"""編者擬的推導（「依」）的檢驗，以及模組的前提樹。

v0.5 起，條目不手標「約定／假定／定理」。有「依」的條目，是編者認為可由所依推出的；
引擎檢驗兩件事：
  · 推得出：所依 ⊨ 此條（只開「依」中列出的本體定義與本體結構條目）；
  · 缺一不可：去掉所依中任何一條（含〔本體：…〕所列），就推不出。
沒有「依」的條目，在前提樹中是葉子（前提）。它們之中哪些其實可由其餘推出，由〈結構〉計算。

「依」的寫法：條目編號用「、」分隔；本體定義與本體結構條目寫在〔本體：…〕裡，
如「依：根品2、根品13、〔本體：惑、染、性・互斥〕」。
"""
from __future__ import annotations
import re
from dataclasses import dataclass, field


@dataclass
class Node:
    sid: str
    kind: str             # 目標 / 推導（有依）/ 前提（無依）/ 本體（結構條目）
    title: str
    deps: list            # 條目編號（含本體結構條目）
    onto_deps: list       # 〔本體：…〕原文
    meta: dict
    def_deps: list = field(default_factory=list)   # 其中的定義（本體約定）


def onto_names(raw_list):
    out = []
    for raw in raw_list:
        raw = raw.split("：", 1)[1] if "：" in raw else raw
        out += [x.strip() for x in re.split(r"[、，,]", raw) if x.strip()]
    return out


def parse_deps(module, sid, raw):
    onto = re.findall(r"〔(.+?)〕", raw)
    rest = re.sub(r"〔.+?〕", "", raw)
    deps = [d.strip() for d in re.split(r"[、，,]", rest) if d.strip()]
    defs = []
    for name in onto_names(onto):
        if name in module.onto.defs:
            defs.append(name)
        elif name in module.statements and module.statements[name].meta.get("_結構"):
            deps.append(name)
        elif name in module.onto.dims or name in module.onto.rels:
            # 簡寫：門名、關係名代表它的全部結構條目（互斥、窮盡……；類型、對稱、傳遞）
            deps += [x for x in module.structure_ids()
                     if x.split("・")[0] == name and x.split("・")[1] in
                     ("互斥", "窮盡", "適用", "類型", "對稱", "傳遞")]
        else:
            raise ValueError(f"【{sid}】〔本體：{name}〕既不是本體定義，也不是本體結構條目（如「性・互斥」）")
    for d in deps:
        if d not in module.statements:
            raise ValueError(f"【{sid}】所依的【{d}】不存在")
    return deps, onto, defs


def nodes(module):
    out = {}
    goal = getattr(module, "goal", None)
    for sid, st in module.statements.items():
        if st.meta.get("答") or st.meta.get("_屬"):
            continue
        if st.meta.get("_結構"):
            out[sid] = Node(sid, "本體", st.text, [], [], st.meta)
            continue
        raw = st.meta.get("依", "")
        deps, onto, defs = parse_deps(module, sid, raw) if raw else ([], [], [])
        kind = "目標" if sid == goal else ("推導" if raw else "前提")
        out[sid] = Node(sid, kind, st.meta.get("標題", st.text), deps, onto, st.meta, defs)
    return out


@dataclass
class EdgeCheck:
    sid: str
    ok: bool
    unnecessary: list
    world: object = None
    needed: list = field(default_factory=list)   # 推不出時：再補哪些本體條目（定義、結構）就推得出


@dataclass
class TreeReport:
    nodes: dict
    edges: dict = field(default_factory=dict)          # 有依的條目 → EdgeCheck
    consistent: bool = False
    closure: dict = field(default_factory=dict)        # 節點 → 其最終依賴的前提（葉子）
    direct: bool = False                               # 全部前提 ⊨ 目標
    goal_minimal: list = field(default_factory=list)   # 目標在全部條目中的極小前提集
    goal: str = ""


def _split(m, deps):
    """把所依拆成全稱部分與存在部分（庫模式）。"""
    U, E = [], []
    for d in deps:
        for p in (m.parts(d) if m.explicit else [d]):
            (E if m.statements[p].meta.get("_部") == "有" else U).append(p)
    return U, E


def _edge_ok(engine, n, deps, defs_on):
    """所依（deps）推得出條目 n 嗎？
    庫模式：條目與所依都拆成全稱、存在兩部分。條目的每一部分，要由所依的全稱部分、
    或全稱部分加一條相關的存在部分推出——有界世界裝不下許多存在部分，不能全放進去，
    否則所依本身無模型，甚麼都「推得出」。回傳 (成立?, 反例世界)。"""
    m = engine.m
    if not m.explicit:
        r = engine.entails(deps, n.sid, defs_on=defs_on)
        return r.ok, r.world
    U, E = _split(m, deps)
    for q in m.parts(n.sid):
        cands = [[]] + [[e] for e in E if m.relevant(e, q)]
        if not any(engine.entails(U + c, q, world=False, defs_on=defs_on).ok for c in cands):
            return False, engine.entails(U, q, defs_on=defs_on).world
    return True, None


def check_edge(engine, n):
    """檢驗一條有「依」的條目。"""
    m = engine.m
    don = engine.defs_on_for(n.def_deps)
    ok, world = _edge_ok(engine, n, n.deps, don)
    unnecessary, needed = [], []
    if ok:
        for d in n.deps:
            if _edge_ok(engine, n, [x for x in n.deps if x != d], don)[0]:
                unnecessary.append(d)
        for d in n.def_deps:
            rest = engine.defs_on_for([x for x in n.def_deps if x != d])
            if _edge_ok(engine, n, n.deps, rest)[0]:
                unnecessary.append("〔" + d + "〕")
    else:
        # 只補本體（定義、結構條目）能不能推得出？能的話，給出一組極小的補充
        struct = [s for s in m.structure_ids() if s not in n.deps]
        alldefs = list(m.onto.defs)
        if _edge_ok(engine, n, n.deps + struct, None)[0]:
            need_s = engine.minimize(struct, lambda S: _edge_ok(engine, n, n.deps + list(S), None)[0])
            need_d = engine.minimize(alldefs, lambda D: _edge_ok(
                engine, n, n.deps + need_s, engine.defs_on_for(list(D) + n.def_deps))[0])
            needed = need_s + [d for d in need_d if d not in engine.defs_on_for(n.def_deps)]
    return EdgeCheck(n.sid, ok, unnecessary, world, needed)


def verify(engine, goal=None):
    m = engine.m
    N = nodes(m)
    goal = goal or getattr(m, "goal", None)
    R = TreeReport(N, goal=goal or "")
    for sid, n in N.items():
        if n.kind in ("推導", "目標") and (n.deps or n.def_deps or n.meta.get("依")):
            # 「依」只列本體定義的（如「依：〔本體：意業〕」）也要檢驗——v0.5 漏了這種
            R.edges[sid] = check_edge(engine, n)
    U = m.universal_base()
    R.consistent = engine.consistent(U).ok and all(engine.consistent(U + [e]).ok for e in m.existence_facts())
    base = m.structure_ids() + m.entry_ids()

    def clos(s):
        if s in R.closure:
            return R.closure[s]
        n = N[s]
        res = {s} if not n.deps else set().union(*(clos(d) for d in n.deps))
        R.closure[s] = res
        return res
    for s in N:
        clos(s)
    if goal:
        leaves = [s for s in base if not N[s].deps]
        R.direct = engine.entails(leaves, goal, world=False).ok
        R.goal_minimal, _ = engine.minimal_premise_sets([s for s in leaves if not N[s].kind == "本體"], goal,
                                                        base=m.structure_ids(), limit=GOAL_LIMIT)
    return R


def depth(N, sid, memo=None):
    memo = {} if memo is None else memo
    if sid in memo:
        return memo[sid]
    n = N[sid]
    d = 0 if not n.deps else 1 + max(depth(N, x, memo) for x in n.deps)
    memo[sid] = d
    return d
