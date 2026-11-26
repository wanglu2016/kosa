"""前提體系：約定、假定、定理、目標。

每個定理（及目標）列出它所依的條目（「依」）。另有兩層：「異讀」是不屬於體系的讀法，
「推論」是由異讀與體系條目推出的結果；異讀不進入相容性、獨立性與極小前提集的檢驗。
引擎檢驗：
  · 推得出：所依 ⊨ 定理；
  · 缺一不可：去掉所依中任何一條，就推不出；
  · 假定之間相容，且互不可推（獨立）；
  · 每個定理最終依賴哪些假定、約定（閉包）。
"""
from __future__ import annotations
import re
from dataclasses import dataclass, field

LAYERS = ("約定", "假定", "定理", "目標", "異讀", "推論")


@dataclass
class Node:
    sid: str
    layer: str
    title: str
    deps: list            # 命題編號
    onto_deps: list       # 〔本體：…〕原文
    meta: dict
    def_deps: list = field(default_factory=list)   # 其中的定義（本體約定），逐條檢驗是否必要


def onto_names(raw_list):
    out = []
    for raw in raw_list:
        raw = raw.split("：", 1)[1] if "：" in raw else raw
        out += [x.strip() for x in re.split(r"[、，,]", raw) if x.strip()]
    return out


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
        defs = [x for x in onto_names(onto) if x in module.onto.defs]
        out[sid] = Node(sid, layer, st.meta.get("標題", st.text), deps, onto, st.meta, defs)
    return out


@dataclass
class EdgeCheck:
    sid: str
    ok: bool
    unnecessary: list
    world: object = None
    needed_defs: list = field(default_factory=list)   # 推不出時：補上哪些定義就推得出（供編者參考）


@dataclass
class TreeReport:
    nodes: dict
    edges: dict = field(default_factory=dict)          # 定理 → EdgeCheck
    consistent: bool = False
    dependent_assumptions: dict = field(default_factory=dict)   # 假定 → 是否可由其餘推出
    closure: dict = field(default_factory=dict)        # 節點 → 其最終依賴的約定、假定
    direct: bool = False                               # 全部假定、約定 ⊨ 目標
    goal_minimal: list = field(default_factory=list)   # 目標的極小前提集（在全部假定、約定中）
    goal: str = "目標"


def goal_of(N, module=None):
    if module is not None and getattr(module, "goal", None):
        if module.goal not in N:
            raise ValueError(f"目標【{module.goal}】不存在")
        return module.goal
    gs = [s for s, n in N.items() if n.layer == "目標"]
    if len(gs) != 1:
        raise ValueError(f"前提體系應恰有一個目標，見到 {gs}")
    return gs[0]


def verify(engine, goal=None):
    m = engine.m
    N = nodes(m)
    goal = goal or goal_of(N, m)
    R = TreeReport(N)
    R.goal = goal
    base = [s for s, n in N.items() if n.layer in ("約定", "假定")]
    for sid, n in N.items():
        if n.layer not in ("定理", "目標", "推論"):
            continue
        # 嚴格模式：只開「依」中列出的本體定義（及其引用的定義、本體結構所需的定義）
        don = engine.defs_on_for(n.def_deps)
        r = engine.entails(n.deps, sid, defs_on=don)
        unnecessary = []
        needed = []
        if r.ok:
            for d in n.deps:
                if engine.entails([x for x in n.deps if x != d], sid, world=False, defs_on=don).ok:
                    unnecessary.append(d)
            for d in n.def_deps:
                rest = engine.defs_on_for([x for x in n.def_deps if x != d])
                if engine.entails(n.deps, sid, world=False, defs_on=rest).ok:
                    unnecessary.append("〔" + d + "〕")
        elif engine.entails(n.deps, sid, world=False).ok:
            # 所依的命題夠了，缺的是本體定義：找一組極小的
            cur = list(m.onto.defs)
            for d in list(cur):
                trial = [x for x in cur if x != d]
                if engine.entails(n.deps, sid, world=False, defs_on=engine.defs_on_for(trial)).ok:
                    cur = trial
            needed = [x for x in cur if x not in engine.defs_on_for(n.def_deps)]
        R.edges[sid] = EdgeCheck(sid, r.ok, unnecessary, r.world, needed)
    R.consistent = engine.consistent(base).ok
    for a in [s for s in base if N[s].layer == "假定"]:
        R.dependent_assumptions[a] = engine.entails([x for x in base if x != a], a, world=False).ok

    def clos(s, seen=None):
        if s in R.closure:
            return R.closure[s]
        n = N[s]
        if n.layer in ("約定", "假定", "異讀"):
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
