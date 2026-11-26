"""判定：給一個命題，用命題庫判斷它成立與否，並給出理由。

四種結論：
  全稱命題（唯、非、即……）
    成立    命題庫推得出它。附「最簡前提」（可用庫中定理，前提最少）與「拆到底」（只用假定、約定）。
    不成立  命題庫推不出它：有一個滿足庫中全部條目、卻違反它的世界（附反例）。
            庫若不完整，反例可能是庫還沒排除的荒謬情形——反例要人看。
  存在命題（有……、容、容有）
    可能    與命題庫相容（附一個實例世界）。
    不可能  命題庫推得出它的否定（附推出否定的極小前提集）。
"""
from __future__ import annotations
import re
from dataclasses import dataclass, field
from pathlib import Path

from .kb import Ontology, Module
from .engine import Engine
from .tree import nodes

ROOT = Path(__file__).resolve().parent.parent


@dataclass
class Verdict:
    sid: str
    kind: str                     # 全稱 / 存在
    verdict: str                  # 成立 / 不成立 / 可能 / 不可能
    short: list = field(default_factory=list)    # 最簡前提（可含定理）
    deep: list = field(default_factory=list)     # 拆到底（只含假定、約定）
    world: object = None          # 反例或實例
    expected: str = ""
    pending: list = field(default_factory=list)  # 所依前提中待核者（就「拆到底」說）

    @property
    def ok(self):
        return not self.expected or self.verdict == self.expected


def is_existential(f):
    return f[0] == "有"


class Judge:
    """一個命題庫（連同若干待判命題）的判定器。"""

    def __init__(self, module: Module):
        self.m = module
        self.e = Engine(module)
        N = nodes(module)
        self.base = [s for s, n in N.items() if n.layer in ("約定", "假定")]
        self.lemmas = [s for s, n in N.items() if n.layer == "定理"]
        self.N = N

    def _shrink(self, items, pred):
        cur = list(items)
        for s in list(cur):
            trial = [x for x in cur if x != s]
            if pred(trial):
                cur = trial
        return cur

    def judge(self, sid, expected=""):
        e, m = self.e, self.m
        st = m.statements[sid]
        if is_existential(st.formula):
            r = e.consistent(self.base + [sid], world=True)
            if r.ok:
                return Verdict(sid, "存在", "可能", world=r.world, expected=expected)
            incons = lambda S: not e.consistent(list(S) + [sid]).ok
            short = self._shrink(self.base + self.lemmas, incons)
            deep = self._shrink(self.base, incons)
            return Verdict(sid, "存在", "不可能", short, deep, expected=expected, pending=self._pending(deep))
        r = e.entails(self.base, sid)
        if not r.ok:
            return Verdict(sid, "全稱", "不成立", world=r.world, expected=expected)
        ent = lambda S: e.entails(list(S), sid, world=False).ok
        short = self._shrink(self.base + self.lemmas, ent)
        deep = self._shrink(self.base, ent)
        return Verdict(sid, "全稱", "成立", short, deep, expected=expected, pending=self._pending(deep))

    def verdict_only(self, sid, base):
        """只求結論，不求理由（供消融檢驗用）。"""
        e = self.e
        st = self.m.statements[sid]
        if is_existential(st.formula):
            return "可能" if e.consistent(list(base) + [sid]).ok else "不可能"
        return "成立" if e.entails(list(base), sid, world=False).ok else "不成立"

    def ablation(self, verdicts, assumptions):
        """逐條去掉假定，看哪些題的結論變了：回傳 {假定: [變了的題]}。"""
        # 去掉前提只會讓「成立／不可能」變弱；且「拆到底」不含它的題，剩下的前提仍推得出，不必重算。
        out = {}
        for a in assumptions:
            base = [b for b in self.base if b != a]
            out[a] = [v.sid for v in verdicts
                      if v.verdict in ("成立", "不可能") and a in v.deep
                      and self.verdict_only(v.sid, base) != v.verdict]
        return out

    def _pending(self, ids):
        return [s for s in ids if self.m.statements[s].meta.get("狀態") == "待核"]


def load_bank(path: Path):
    """讀一個題庫文件（它自己「引」入命題庫）。"""
    onto = Ontology.load(ROOT / "本體")
    return Module.load(path, onto)


def run_bank(path: Path):
    """判定題庫中的全部題目。回傳 (模組, [Verdict], {題: [Verdict]})。"""
    m = load_bank(path)
    J = Judge(m)
    qs = [s for s, st in m.statements.items() if st.meta.get("答")]
    out, groups = [], {}
    for sid in qs:
        st = m.statements[sid]
        v = J.judge(sid, st.meta["答"])
        out.append(v)
        groups.setdefault(st.meta.get("題", sid), []).append(v)
    return m, J, out, groups


def all_banks():
    return sorted((ROOT / "題庫").glob("*.kosa"))


def judge_text(text, lib="庫/法"):
    """判定一條臨時寫下的命題。"""
    tmp = ROOT / ".判定.kosa"
    body = f"題庫 臨時\n引 {lib}\n\n【待判】{text}\n　答：\n"
    tmp.write_text(body, encoding="utf-8")
    try:
        m = load_bank(tmp)
    finally:
        tmp.unlink()
    J = Judge(m)
    return m, J, J.judge("待判")
