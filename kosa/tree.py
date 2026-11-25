"""前提體系：約定、假定、定理、目標。

每個定理（及目標）列出它所依的條目（「依」）。引擎檢驗：
  · 推得出：所依 ⊨ 定理；
  · 缺一不可：去掉所依中任何一條，就推不出；
  · 假定之間相容，且互不可推（獨立）；
  · 每個定理最終依賴哪些假定、約定（閉包）。
"""
from __future__ import annotations
import re
from dataclasses import dataclass, field

LAYERS = ("約定", "假定", "定理", "目標")


@dataclass
class Node:
    sid: str
    layer: str
    title: str
    deps: list            # 命題編號
    onto_deps: list       # 〔本體：…〕
    meta: dict


def nodes(module):
    out = {}
    for sid, st in module.statements.items():
        layer = st.meta.get("層")
        if layer not in LAYERS:
            continue
        raw = st.meta.get("依", "")
        onto = re.findall(r"〔(.+?)〕", raw)
        raw = re.sub(r"〔.+?〕", "", raw)
        deps = [d.strip() for d in re.split(r"[、，,]", raw) if d.strip()]
        for d in deps:
            if d not in module.statements:
                raise ValueError(f"【{sid}】所依的【{d}】不存在")
        out[sid] = Node(sid, layer, st.meta.get("標題", st.text), deps, onto, st.meta)
    return out


@dataclass
class EdgeCheck:
    sid: str
    ok: bool
    unnecessary: list
    world: object = None


@dataclass
class TreeReport:
    nodes: dict
    edges: dict = field(default_factory=dict)          # 定理 → EdgeCheck
    consistent: bool = False
    dependent_assumptions: dict = field(default_factory=dict)   # 假定 → 是否可由其餘推出
    closure: dict = field(default_factory=dict)        # 節點 → 其最終依賴的約定、假定
    direct: bool = False                               # 全部假定、約定 ⊨ 目標
    goal_minimal: list = field(default_factory=list)   # 目標的極小前提集（在全部假定、約定中）


def verify(engine, goal="目標"):
    m = engine.m
    N = nodes(m)
    R = TreeReport(N)
    base = [s for s, n in N.items() if n.layer in ("約定", "假定")]
    for sid, n in N.items():
        if n.layer not in ("定理", "目標"):
            continue
        r = engine.entails(n.deps, sid)
        unnecessary = []
        if r.ok:
            for d in n.deps:
                if engine.entails([x for x in n.deps if x != d], sid, world=False).ok:
                    unnecessary.append(d)
        R.edges[sid] = EdgeCheck(sid, r.ok, unnecessary, r.world)
    R.consistent = engine.consistent(base).ok
    for a in [s for s in base if N[s].layer == "假定"]:
        R.dependent_assumptions[a] = engine.entails([x for x in base if x != a], a, world=False).ok

    def clos(s, seen=None):
        if s in R.closure:
            return R.closure[s]
        n = N[s]
        if n.layer in ("約定", "假定"):
            res = {s}
        else:
            res = set()
            for d in n.deps:
                res |= clos(d)
        R.closure[s] = res
        return res
    for s in N:
        clos(s)
    R.direct = engine.entails(base, goal, world=False).ok
    R.goal_minimal, _ = engine.minimal_premise_sets(base, goal)
    return R


def depth(N, sid, memo=None):
    memo = {} if memo is None else memo
    if sid in memo:
        return memo[sid]
    n = N[sid]
    d = 0 if not n.deps else 1 + max(depth(N, x, memo) for x in n.deps)
    memo[sid] = d
    return d
