"""驗證引擎：把模組編譯為回答集程序（ASP），用 clingo 求解。

在有界世界中，引擎能回答：
  · 一組前提是否相容（有無模型）；
  · 一組前提是否蘊涵某命題（「前提 ∧ 非命題」無模型 ⇒ 蘊涵）；
  · 不蘊涵時給出反例世界（儘量小）；
  · 極小前提集、極小衝突集、極小修正集（MARCO 枚舉）；
  · 在唯一（或最大）模型中計數。
"""
from __future__ import annotations
import itertools
import re
from dataclasses import dataclass

import clingo

from .lang import free_vars, parse_class, show
from .evaluate import World, Ent, LABELS


def q(s):
    return '"' + s.replace('"', '\\"') + '"'


class Compiler:
    def __init__(self, module):
        self.m = module
        self.onto = module.onto
        self.lex = module.lex
        self.rules: list[str] = []
        self.n = 0
        self.sort_index = {name: i for i, name in enumerate(module.sorts)}
        self.stmt_index = {}
        self.target_index = {}

    def new(self, p="a"):
        self.n += 1
        return f"{p}{self.n}"

    def dom(self, v, env):
        s = env[v]
        return f"ent(V{v})" if s == "*" else f"d{self.sort_index[s]}(V{v})"

    @staticmethod
    def atom(pred, vs):
        return f"{pred}({','.join('V' + v for v in vs)})" if vs else pred

    # 類
    def comp_class(self, ce, x, env):
        k = ce[0]
        if k == "名":
            return f"is(V{x},{q(ce[1])})"
        p = self.new("c")
        d = self.dom(x, env)
        if k == "且":
            body = [self.comp_class(c, x, env) for c in ce[1]]
            self.rules.append(f"{p}(V{x}) :- {d}, {', '.join(body)}.")
        elif k == "或":
            for c in ce[1]:
                self.rules.append(f"{p}(V{x}) :- {d}, {self.comp_class(c, x, env)}.")
        elif k == "非":
            self.rules.append(f"{p}(V{x}) :- {d}, not {self.comp_class(ce[1], x, env)}.")
        return f"{p}(V{x})"

    # 公式（Lloyd–Topor 變換）
    def comp(self, f, env):
        k = f[0]
        fv = sorted(free_vars(f))
        doms = [self.dom(v, env) for v in fv]
        if k == "屬":
            return self.comp_class(f[1], f[2], env)
        if k == "係":
            return f"r({q(f[1])},V{f[2][0]},V{f[2][1]})"
        p = self.new()
        head = self.atom(p, fv)
        if k == "同門":
            w = f"W{self.n}"
            self.rules.append(f"{head} :- {', '.join(doms)}, v(V{f[2]},{q(f[1])},{w}), v(V{f[3]},{q(f[1])},{w}).")
        elif k == "同":
            if f[1] == f[2]:
                self.rules.append(f"{head} :- {', '.join(doms)}.")
            else:
                self.rules.append(f"{head} :- {', '.join(doms)}, V{f[1]} == V{f[2]}.")
        elif k == "真":
            self.rules.append(f"{head}.")
        elif k == "非":
            a = self.comp(f[1], env)
            self.rules.append(f"{head} :- {', '.join(doms + ['not ' + a])}.")
        elif k == "且":
            parts = [self.comp(g, env) for g in f[1]]
            self.rules.append(f"{head} :- {', '.join(doms + parts)}.")
        elif k == "或":
            for g in f[1]:
                a = self.comp(g, env)
                self.rules.append(f"{head} :- {', '.join(doms + [a])}.")
        elif k == "⇒":
            return self.comp(("或", [("非", f[1]), f[2]]), env)
        elif k == "⇔":
            return self.comp(("且", [("⇒", f[1], f[2]), ("⇒", f[2], f[1])]), env)
        elif k == "有":
            env2 = dict(env)
            for v, s in f[1]:
                env2[v] = s
            a = self.comp(f[2], env2)
            bd = [self.dom(v, env2) for v, _ in f[1]]
            self.rules.append(f"{head} :- {', '.join(doms + bd + [a])}.")
        elif k == "凡":
            return self.comp(("非", ("有", f[1], ("非", f[2]))), env)
        else:
            raise ValueError(f)
        return head

    def world(self):
        m, onto, R = self.m, self.onto, self.rules
        for name, s in m.sorts.items():
            j = self.sort_index[name]
            if s.kind == "開放":
                for i in range(1, s.size + 1):
                    R.append(f"slot({j},e({j},{i})).")
                R.append(f"{{ act(E) }} :- slot({j},E).")
                R.append(f"d{j}(E) :- act(E), slot({j},E).")
                # 對稱破缺：前面的槽位先啟用，減少等價模型
                R.append(f":- slot({j},e({j},I)), I > 1, act(e({j},I)), not act(e({j},I-1)).")
            elif s.kind == "固定":
                for el in s.elements:
                    R.append(f"d{j}(e({j},{q(el)})).")
            elif s.kind == "積":
                for i, attrs in enumerate(s.elements, 1):
                    R.append(f"d{j}(e({j},{i})).")
                    for dn, v in attrs.items():
                        R.append(f"v(e({j},{i}),{q(dn)},{q(v)}).")
            R.append(f"ent(E) :- d{j}(E).")
            if s.kind == "開放":
                for dn in s.dims:
                    d = onto.dims[dn]
                    vals = "; ".join(f"v(E,{q(dn)},{q(v)})" for v in d.values)
                    if d.applies:
                        ce = parse_class(d.applies, self.lex)
                        app = self.comp_class(ce, "e", {"e": name})
                        app = app.replace("Ve", "E")
                        R.append(f"1 {{ {vals} }} 1 :- d{j}(E), {app}.")
                        R.append(f"v(E,{q(dn)},\"—\") :- d{j}(E), not {app}.")
                    else:
                        R.append(f"1 {{ {vals} }} 1 :- d{j}(E).")
                    for val, vap in d.value_applies.items():
                        app = self.comp_class(parse_class(vap, self.lex), "e", {"e": name}).replace("Ve", "E")
                        R.append(f":- d{j}(E), v(E,{q(dn)},{q(val)}), not {app}.")
        R.append('is(E,V) :- v(E,D,V), V != "—".')
        for dn, text in onto.defs.items():
            ce = parse_class(text, self.lex)
            a = self.comp_class(ce, "e", {"e": "*"})
            R.append(f"is(Ve,{q(dn)}) :- ent(Ve), {a}.")
        for pn, p in m.preds.items():
            j = self.sort_index[p.sort]
            if p.kind == "待定":
                R.append(f"{{ is(E,{q(pn)}) }} :- d{j}(E).")
            else:
                for el in p.extension:
                    R.append(f"is(e({j},{q(el)}),{q(pn)}).")
        for rn in m.rels_used:
            r = onto.rels[rn]
            ds = self.sort_index[m.default_sort]
            a1 = self.comp_class(parse_class(r.sig[0], self.lex), "x", {"x": m.default_sort})
            a2 = self.comp_class(parse_class(r.sig[1], self.lex), "y", {"y": m.default_sort})
            R.append(f"{{ r({q(rn)},Vx,Vy) }} :- d{ds}(Vx), d{ds}(Vy), Vx != Vy, {a1}, {a2}.")
            if r.symmetric:
                R.append(f":- r({q(rn)},X,Y), not r({q(rn)},Y,X).")
        for rn, sname in m.order_rels.items():
            s = m.sorts[sname]
            j = self.sort_index[sname]
            for a, b in itertools.combinations(s.elements, 2):
                R.append(f"r({q(rn)},e({j},{q(a)}),e({j},{q(b)})).")

    def statement(self, sid, f, as_target=False):
        idx = len(self.stmt_index) + len(self.target_index)
        h = self.comp(f, {})
        if as_target:
            self.target_index[sid] = idx
            self.rules.append(f"#external q({idx}).")
            self.rules.append(f":- q({idx}), {h}.")
        else:
            self.stmt_index[sid] = idx
            self.rules.append(f"#external on({idx}).")
            self.rules.append(f":- on({idx}), not {h}.")


@dataclass
class Result:
    ok: bool                 # 蘊涵／相容 的結論
    world: World | None = None


class Engine:
    """一個模組的求解器。所有命題一次編譯；每次查詢只切換假設。"""

    def __init__(self, module, extra_targets: dict | None = None):
        self.m = module
        c = Compiler(module)
        c.world()
        for sid, st in module.statements.items():
            c.statement(sid, st.formula)
            c.statement(sid, st.formula, as_target=True)
        for sid, f in (extra_targets or {}).items():
            c.statement(sid, f, as_target=True)
        self.c = c
        self.program = "\n".join(c.rules)
        self._ctl = self._control(minimize=False)
        self._opt = None
        self.calls = 0

    def _control(self, minimize):
        ctl = clingo.Control(["--warn=none"])
        prog = self.program
        if minimize:
            prog += "\n#minimize { 1@3,E : act(E) }.\n#minimize { 1@2,R,X,Y : r(R,X,Y) }.\n"
            prog += "#minimize { 1@1,E,P : is(E,P), open(P) }.\n"
            prog += "\n".join(f"open({q(p)})." for p, pr in self.m.preds.items() if pr.kind == "待定") + "\n"
        ctl.add("base", [], prog)
        ctl.ground([("base", [])])
        self._release(ctl)
        return ctl

    def _release(self, ctl):
        # 外部原子預設為假；釋放後才能由假設決定真假
        for i in self.c.stmt_index.values():
            ctl.assign_external(clingo.Function("on", [clingo.Number(i)]), None)
        for i in self.c.target_index.values():
            ctl.assign_external(clingo.Function("q", [clingo.Number(i)]), None)

    def _assumptions(self, ctl, on, target=None):
        A = []
        for sid, i in self.c.stmt_index.items():
            A.append((clingo.Function("on", [clingo.Number(i)]), sid in on))
        for sid, i in self.c.target_index.items():
            A.append((clingo.Function("q", [clingo.Number(i)]), sid == target))
        return A

    def sat(self, on, target=None, want_world=False, minimize=True):
        """有無模型？target 給定時，求「前提 ∧ 非 target」的模型。"""
        self.calls += 1
        if not want_world:
            res = self._ctl.solve(assumptions=self._assumptions(self._ctl, set(on), target))
            return res.satisfiable, None
        if minimize:
            if self._opt is None:
                self._opt = self._control(minimize=True)
            ctl = self._opt
            ctl.configuration.solve.opt_mode = "opt"
        else:
            ctl = self._ctl
        last = None
        with ctl.solve(assumptions=self._assumptions(ctl, set(on), target), yield_=True) as h:
            for mdl in h:
                last = mdl.symbols(atoms=True)
            sat = h.get().satisfiable
        return sat, (self._world(last) if last is not None else None)

    def entails(self, on, target, world=True) -> Result:
        sat, w = self.sat(on, target, want_world=world)
        return Result(not sat, w)

    def consistent(self, on, world=False) -> Result:
        sat, w = self.sat(on, None, want_world=world)
        return Result(sat, w)

    def _world(self, symbols) -> World:
        m = self.m
        inv = {i: n for n, i in self.c.sort_index.items()}
        ents = {}
        rels = set()
        acts = set()
        for s in symbols:
            if s.name == "act":
                acts.add(str(s.arguments[0]))
        for s in symbols:
            if s.name in ("d0", "d1", "d2", "d3", "d4") or re.match(r"d\d+$", s.name):
                key = str(s.arguments[0])
                j = s.arguments[0].arguments[0].number
                ents.setdefault(key, Ent(key, inv[j], {}, set()))
        for s in symbols:
            if s.name == "v":
                key = str(s.arguments[0])
                if key in ents:
                    ents[key].attrs[s.arguments[1].string] = s.arguments[2].string
            elif s.name == "is":
                key = str(s.arguments[0])
                p = s.arguments[1].string
                if key in ents and p in m.preds:
                    ents[key].preds.add(p)
            elif s.name == "r":
                rels.add((s.arguments[0].string, str(s.arguments[1]), str(s.arguments[2])))
        ordered = sorted(ents.values(), key=lambda e: e.key)
        # 給開放類別的實體起名：甲乙丙……
        n = 0
        for e in ordered:
            if m.sorts[e.sort].kind == "開放":
                e.label = LABELS[n]
                n += 1
            else:
                e.label = e.key.split(",", 1)[1].rstrip(")").strip('"')
        return World(ordered, rels)

    # ── 極小集枚舉（MARCO）──
    def marco(self, universe, pred, base=()):
        """枚舉 universe 中使 pred 為真的極小子集（MUS），以及使其為假的極大子集（MSS）。
        pred 必須單調：子集為真則超集亦真。base 中的命題始終開啟。"""
        U = list(universe)
        idx = {s: i for i, s in enumerate(U)}
        blocks = []
        muses, msses = [], []
        while True:
            ctl = clingo.Control(["--warn=none"])
            prog = [f"{{ sel(0..{len(U) - 1}) }}." if U else ""]
            prog += blocks
            prog.append("#maximize { 1,K : sel(K) }.")
            ctl.add("base", [], "\n".join(prog))
            ctl.ground([("base", [])])
            ctl.configuration.solve.opt_mode = "opt"
            seed = None
            with ctl.solve(yield_=True) as h:
                for mdl in h:
                    seed = {U[s.arguments[0].number] for s in mdl.symbols(atoms=True) if s.name == "sel"}
                if not h.get().satisfiable:
                    seed = None
            if seed is None:
                break
            if pred(set(base) | seed):
                mus = self._shrink(seed, pred, base)
                muses.append(mus)
                blocks.append(":- " + ", ".join(f"sel({idx[s]})" for s in sorted(mus, key=idx.get)) + ".")
            else:
                msses.append(seed)
                outside = [s for s in U if s not in seed]
                if not outside:
                    break
                blocks.append(":- " + ", ".join(f"not sel({idx[s]})" for s in outside) + ".")
        order = {s: i for i, s in enumerate(U)}
        muses = [sorted(x, key=order.get) for x in muses]
        msses = [sorted(x, key=order.get) for x in msses]
        return muses, msses

    def _shrink(self, S, pred, base):
        cur = list(S)
        for s in list(cur):
            trial = [x for x in cur if x != s]
            if pred(set(base) | set(trial)):
                cur = trial
        return set(cur)

    def minimal_premise_sets(self, premises, target, base=()):
        return self.marco(premises, lambda S: self.entails(S, target, world=False).ok, base)

    def conflict_sets(self, stmts, base=()):
        return self.marco(stmts, lambda S: not self.consistent(S).ok, base)

    # ── 計數 ──
    def maximal_world(self, on, closure_preds):
        """在前提下，令 closure_preds 的外延極大（「凡未被排除者皆是」）。回傳世界及是否唯一。"""
        ctl = clingo.Control(["--warn=none", "--opt-mode=optN"])
        prog = self.program + "\n" + "\n".join(
            f"#maximize {{ 1,E : is(E,{q(p)}) }}." for p in closure_preds)
        ctl.add("base", [], prog)
        ctl.ground([("base", [])])
        self._release(ctl)
        ctl.configuration.solve.models = 0
        optimal = []
        with ctl.solve(assumptions=self._assumptions(ctl, set(on)), yield_=True) as h:
            for mdl in h:
                if mdl.optimality_proven:
                    optimal.append(mdl.symbols(atoms=True))
                    if len(optimal) > 1:
                        break
        if not optimal:
            return None, False
        return self._world(optimal[0]), len(optimal) == 1
