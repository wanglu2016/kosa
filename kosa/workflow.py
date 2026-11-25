"""形式化工作流程中的幾個標準步驟。"""
from __future__ import annotations
from dataclasses import dataclass, field

from .evaluate import holds


@dataclass
class Round:
    premises: list
    proved: bool
    world: object = None
    violated: list = field(default_factory=list)   # 被反例違反的候選
    added: str | None = None


def violated_by(world, module, sids):
    """回傳在此世界中為假的命題編號。"""
    out = []
    for s in sids:
        f = module.statements[s].formula
        if not holds(f, world, {}, module.onto, module.lex):
            out.append(s)
    return out


def completion_loop(engine, start, pool, target, max_rounds=15):
    """反例驅動的前提補全：
       1. 檢驗「前提 ⊨ 求證」；
       2. 不成立 → 取一個儘量小的反例世界；
       3. 看候選池中哪些前提被這個反例違反——加入其中任一條都能排除它；
       4. 取池中次序最前的一條加入，回到 1。
    """
    module = engine.m
    cur = list(start)
    rounds = []
    for _ in range(max_rounds):
        r = engine.entails(cur, target)
        if r.ok:
            rounds.append(Round(list(cur), True))
            return rounds
        rest = [p for p in pool if p not in cur]
        bad = violated_by(r.world, module, rest)
        rd = Round(list(cur), False, r.world, bad)
        rounds.append(rd)
        if not bad:
            return rounds          # 候選池不足：需要人提出新前提
        rd.added = bad[0]
        cur.append(bad[0])
    return rounds


@dataclass
class PremiseAnalysis:
    premises: list
    minimal_sets: list
    necessary: list
    redundant: list
    witnesses: dict      # 必要前提 → 去掉它之後的反例


def analyze_premises(engine, premises, target, witnesses=True):
    muses, _ = engine.minimal_premise_sets(premises, target)
    used = set().union(*map(set, muses)) if muses else set()
    necessary = [p for p in premises if all(p in m for m in muses)] if muses else []
    redundant = [p for p in premises if p not in used]
    wit = {}
    if witnesses:
        for p in necessary:
            r = engine.entails([x for x in premises if x != p], target)
            wit[p] = r.world
    return PremiseAnalysis(list(premises), muses, necessary, redundant, wit)


@dataclass
class ConflictAnalysis:
    stmts: list
    conflicts: list      # 極小衝突集
    corrections: list    # 極小修正集：放棄其中各條即可相容


def analyze_conflicts(engine, stmts, base=()):
    muses, msses = engine.conflict_sets(stmts, base)
    mcs = [sorted(set(stmts) - set(s), key=stmts.index) for s in msses]
    mcs.sort(key=lambda x: (len(x), [stmts.index(i) for i in x]))
    return ConflictAnalysis(list(stmts), muses, mcs)
