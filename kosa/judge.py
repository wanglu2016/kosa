"""判定：給一個命題，用命題庫判斷它，並給出理由。三值：

  證成  命題庫推得出它。附「最簡前提」（極小的一組條目）。
  證否  命題庫推得出它的否定。附推出否定的極小前提。
  未決  兩者都推不出：庫不知道。附一個它成立的世界（實例）、一個它不成立的世界（反例）。

「證成」「證否」是有界的結論：求解器只窮盡至多若干個法、若干個有情的世界。重要的「證成」要再由 Lean 證明。

存在命題的處理：有界世界只有幾個元素，庫中全部存在命題一起考就裝不下。所以庫分兩部分：
全稱的底子 U（本體結構、全稱命題、「通」之類命題的全稱部分），以及存在部分 E（逐條考）。
  證成：U 推得出它；或 U 加上某一條存在部分推得出它（待判命題的各部分分別考）。
  證否：U 加上它沒有模型；或 U、某一條存在部分、它三者沒有模型。
  未決：以上都不成立。實例取自 U 加上它的模型，反例取自 U 加上它的否定的模型——
        這兩個世界只滿足 U，未必同時滿足全部存在部分，所以「未決」不是確定的結論。

題庫中「答」寫書中的答案：成立、有、可能 → 應證成；不成立、無、不可能 → 應證否。
比對結果三種：一致、未決（庫沒覆蓋到，不算錯）、相違（庫的結論與書相反，必須處理）。
"""
from __future__ import annotations
from dataclasses import dataclass, field
from pathlib import Path

from .kb import Ontology, Module
from .engine import Engine

ROOT = Path(__file__).resolve().parent.parent

EXPECT = {"成立": "證成", "有": "證成", "可能": "證成", "證成": "證成",
          "不成立": "證否", "無": "證否", "不可能": "證否", "證否": "證否"}


@dataclass
class Verdict:
    sid: str
    verdict: str                  # 證成 / 證否 / 未決 / 矛盾（庫本身不相容）
    premises: list = field(default_factory=list)   # 證成、證否時：極小前提
    example: object = None        # 未決時：它成立的世界
    counter: object = None        # 未決時：它不成立的世界
    expected: str = ""            # 書中答案（原文）
    vacuous: str = ""             # 未決且只能空真地成立時：主語（如「身表」）——缺的是「有身表」這類存在命題
    pending: list = field(default_factory=list)    # 前提中「待核」者

    @property
    def want(self):
        return EXPECT.get(self.expected, "")

    @property
    def match(self):
        """一致 / 未決 / 相違 / （無答案時）空"""
        if not self.want:
            return ""
        if self.verdict == self.want:
            return "一致"
        if self.verdict == "未決":
            return "未決"
        return "相違"

    @property
    def ok(self):
        return self.match in ("", "一致", "未決")


class Judge:
    """一個命題庫（連同若干待判命題）的判定器。"""
    TOP = 20     # 每次只試最相關的若干條存在部分（只影響完備性；見 skill〈坑〉「速度」）

    def __init__(self, module: Module):
        self.m = module
        self.e = Engine(module)
        self.U = module.universal_base()
        self.E = module.existence_facts()
        self.base = self.U + self.E     # 供消融檢驗、統計用

    def _shrink(self, items, pred):
        return self.e.minimize(items, pred)

    def _candidates(self, sid):
        """與 sid 相關的存在部分（有共用的詞），共用詞多的排在前面。
        只影響完備性，不影響可靠性：不相關的存在部分不拿來試。"""
        mine = self.m.content_names(sid) - {"法類"}
        scored = [(len(self.m.content_names(x) & mine), i, x) for i, x in enumerate(self.E) if x != sid]
        return [x for k, i, x in sorted(scored, key=lambda t: (-t[0], t[1])) if k][:self.TOP]

    def _prove(self, part):
        """一個部分：U 推得出它，或 U 加一條（相關的）存在部分推得出它。回傳所用的前提（極小），推不出回傳 None。
        全稱部分只用 U：一條存在命題幫不了全稱的結論（除非庫自相矛盾）。"""
        e, U = self.e, self.U
        st = self.m.statements[part]
        extras = [[]] + ([[x] for x in self._candidates(part)] if st.formula[0] == "有" else [])
        for extra in extras:
            if e.entails(U + extra, part, world=False).ok:
                return self.e.minimize(U + extra, lambda S: e.entails(list(S), part, world=False).ok)
        return None

    def _refute(self, sid):
        """U（或 U 加一條存在部分）與它不相容。回傳極小前提，相容回傳 None。"""
        e, U = self.e, self.U
        for extra in [[]] + [[x] for x in self._candidates(sid)]:
            if not e.consistent(U + extra + [sid]).ok:
                return self.e.minimize(U + extra, lambda S: not e.consistent(list(S) + [sid]).ok)
        return None

    def judge(self, sid, expected=""):
        e, m = self.e, self.m
        parts = m.parts(sid)
        # 先看全稱底子是否已推出它的否定：若是，它不可能由 U 加一條存在部分證成
        #（每條存在部分都已檢驗與 U 相容，見〈驗證〉），不必再逐條試。
        if not e.consistent(self.U + [sid]).ok:
            prem = self.e.minimize(self.U, lambda S: not e.consistent(list(S) + [sid]).ok)
            return Verdict(sid, "證否", prem, expected=expected, pending=self._pending(prem))
        proofs = [self._prove(p) for p in parts]
        pos = all(x is not None for x in proofs)
        # 證成了就不再逐條找反駁：U 加某條存在部分若與它不相容，那是兩條存在部分彼此不相容，屬於全庫的問題，不在這裡查
        refut = None if pos else self._refute(sid)
        if pos and refut is not None:
            return Verdict(sid, "矛盾", expected=expected)
        if pos:
            prem = list(dict.fromkeys(x for pr in proofs for x in pr))
            return Verdict(sid, "證成", prem, expected=expected, pending=self._pending(prem))
        if refut is not None:
            return Verdict(sid, "證否", refut, expected=expected, pending=self._pending(refut))
        ex, vac = None, ""
        if f"{sid}・例" in m.statements:
            r = e.consistent(self.U + [sid, f"{sid}・例"], world=True)
            if r.ok:
                ex = r.world
            else:
                from .lang import show_class
                vac = show_class(m.statements[sid].formula[2][1][1])
        if ex is None:
            ex = e.consistent(self.U + [sid], world=True).world
        cx = e.entails(self.U, sid).world
        return Verdict(sid, "未決", example=ex, counter=cx, expected=expected, vacuous=vac)

    def verdict_only(self, sid, base):
        e = self.e
        pos = e.entails(list(base), sid, world=False).ok
        neg = not e.consistent(list(base) + [sid]).ok
        return "矛盾" if pos and neg else "證成" if pos else "證否" if neg else "未決"

    def ablation(self, verdicts, assumptions):
        """逐條去掉條目，看哪些題的結論變了：回傳 {條目: [變了的題]}。
        去掉前提只會使「證成／證否」變為「未決」；前提中不含它的題不必重算。"""
        out = {}
        for a in assumptions:
            base = [b for b in self.base if b != a]
            out[a] = [v.sid for v in verdicts
                      if v.verdict in ("證成", "證否") and a in v.premises
                      and self.verdict_only(v.sid, base) != v.verdict]
        return out

    def _pending(self, ids):
        own = lambda s: self.m.statements[s].meta.get("_屬", s)
        return list(dict.fromkeys(own(s) for s in ids if self.m.statements[own(s)].meta.get("狀態") == "待核"))


def load_bank(path: Path):
    """讀一個題庫文件（它自己「引」入命題庫）。"""
    onto = Ontology.load(ROOT / "本體")
    return Module.load(path, onto)


def run_bank(path: Path):
    """判定題庫中的全部題目。回傳 (模組, 判定器, [Verdict], {題: [Verdict]})。"""
    m = load_bank(path)
    J = Judge(m)
    qs = [s for s, st in m.statements.items() if st.meta.get("答")]
    out, groups = [], {}
    for sid in qs:
        st = m.statements[sid]
        if st.meta["答"] not in EXPECT:
            raise ValueError(f"【{sid}】的答案「{st.meta['答']}」不是 成立、不成立、有、無、可能、不可能 之一")
        v = J.judge(sid, st.meta["答"])
        out.append(v)
        groups.setdefault(st.meta.get("題", sid), []).append(v)
    return m, J, out, groups


def all_banks():
    return sorted((ROOT / "題庫").glob("*.kosa"))


def judge_text(text):
    """判定一條臨時寫下的命題。論域（法、有情）由句中的詞推出。"""
    tmp = ROOT / ".判定.kosa"
    body = f"題庫 臨時\n引 庫\n\n【待判】{text}\n"
    tmp.write_text(body, encoding="utf-8")
    try:
        m = load_bank(tmp)
    finally:
        tmp.unlink()
    J = Judge(m)
    return m, J, J.judge("待判")
