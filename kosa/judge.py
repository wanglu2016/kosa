"""判定：給一個命題，用命題庫判斷它，並給出理由。三值：

  證成  命題庫推得出它。附「最簡前提」（極小的一組條目）。
  證否  命題庫推得出它的否定。附推出否定的極小前提。
  未決  兩者都推不出：庫不知道。附一個它成立的世界（實例）、一個它不成立的世界（反例）。

「證成」「證否」是有界的結論：求解器只窮盡至多若干個法、若干個有情的世界。
「未決」反而是確定的：實例和反例都是真的模型。重要的「證成」要再由 Lean 證明。

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

    def __init__(self, module: Module):
        self.m = module
        self.e = Engine(module)
        self.base = module.structure_ids() + module.entry_ids()

    def _shrink(self, items, pred):
        return self.e.minimize(items, pred)

    def judge(self, sid, expected=""):
        e = self.e
        pos = e.entails(self.base, sid, world=False).ok
        neg = not e.consistent(self.base + [sid]).ok
        if pos and neg:
            return Verdict(sid, "矛盾", expected=expected)
        if pos:
            prem = self._shrink(self.base, lambda S: e.entails(S, sid, world=False).ok)
            return Verdict(sid, "證成", prem, expected=expected, pending=self._pending(prem))
        if neg:
            prem = self._shrink(self.base, lambda S: not e.consistent(list(S) + [sid]).ok)
            return Verdict(sid, "證否", prem, expected=expected, pending=self._pending(prem))
        ex = e.consistent(self.base + [sid], world=True).world
        cx = e.entails(self.base, sid).world
        return Verdict(sid, "未決", example=ex, counter=cx, expected=expected)

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
        return [s for s in ids if self.m.statements[s].meta.get("狀態") == "待核"]


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
