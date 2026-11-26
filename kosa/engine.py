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
            if ce[1] in self.sort_index:          # 類別名作類：該論域的一切元素
                return f"d{self.sort_index[ce[1]]}(V{x})"
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
            if self.m.explicit:
                # 兩者於此門都無值（不適用），亦算相同——與 Lean 中「—」＝「—」一致
                self.rules.append(f"{head} :- {', '.join(doms)}, not hv(V{f[2]},{q(f[1])}), not hv(V{f[3]},{q(f[1])}).")
        elif k == "同":
            if f[1] == f[2]:
                self.rules.append(f"{head} :- {', '.join(doms)}.")
            else:
                self.rules.append(f"{head} :- {', '.join(doms)}, V{f[1]} == V{f[2]}.")
        elif k == "真":
            self.rules.append(f"{head}.")
        elif k == "結構":
            return self.comp_structure(f)
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

    def comp_structure(self, f):
        """本體結構條目（門的互斥、窮盡、適用；關係的類型、對稱、傳遞）：回傳「此條成立」的原子。"""
        _, kind, name, _ = f
        R, onto = self.rules, self.onto
        p = self.new("st")
        bad = p + "_bad"
        if kind in ("互斥", "窮盡", "適用"):
            d = onto.dims[name]
            j = self.sort_index[d.sort]
            app = None
            if d.applies:
                app = self.comp_class(parse_class(d.applies, self.lex), "e", {"e": d.sort})
            if kind == "互斥":
                R.append(f"{bad} :- v(Ve,{q(name)},V1), v(Ve,{q(name)},V2), V1 < V2.")
            elif kind == "窮盡":
                R.append(f"{bad} :- d{j}(Ve), {app + ', ' if app else ''}not hv(Ve,{q(name)}).")
            else:
                R.append(f"{bad} :- d{j}(Ve), hv(Ve,{q(name)}), not {app}.")
        elif kind == "值適用":
            dn, val = name
            d = onto.dims[dn]
            j = self.sort_index[d.sort]
            app = self.comp_class(parse_class(d.value_applies[val], self.lex), "e", {"e": d.sort})
            R.append(f"{bad} :- d{j}(Ve), v(Ve,{q(dn)},{q(val)}), not {app}.")
        else:
            r = onto.rels[name]
            s1, s2 = self.lex.rel_sorts[name]
            if kind == "類型":
                a1 = self.comp_class(parse_class(r.sig[0], self.lex), "x", {"x": s1})
                a2 = self.comp_class(parse_class(r.sig[1], self.lex), "y", {"y": s2})
                R.append(f"{bad} :- r({q(name)},Vx,Vy), not {a1}.")
                R.append(f"{bad} :- r({q(name)},Vx,Vy), not {a2}.")
                R.append(f"{bad} :- r({q(name)},Vx,Vx).")
            elif kind == "對稱":
                R.append(f"{bad} :- r({q(name)},X,Y), not r({q(name)},Y,X).")
            elif kind == "傳遞":
                R.append(f"{bad} :- r({q(name)},X,Y), r({q(name)},Y,Z), X != Z, not r({q(name)},X,Z).")
        R.append(f"{p} :- not {bad}.")
        return p

    def world_explicit(self):
        """庫模式的世界：門值、關係都自由選取，結構約束由各結構條目（可開關）施加。"""
        m, onto, R = self.m, self.onto, self.rules
        for name, s in m.sorts.items():
            j = self.sort_index[name]
            if s.kind != "開放":
                raise ValueError("庫模式只支持開放類別")
            for i in range(1, s.size + 1):
                R.append(f"slot({j},e({j},{i})).")
            R.append(f"{{ act(E) }} :- slot({j},E).")
            R.append(f"d{j}(E) :- act(E), slot({j},E).")
            R.append(f":- slot({j},e({j},I)), I > 1, act(e({j},I)), not act(e({j},I-1)).")
            R.append(f"ent(E) :- d{j}(E).")
            for dn in s.dims:
                d = onto.dims[dn]
                for v in d.values:
                    R.append(f"val({q(dn)},{q(v)}).")
                R.append(f"{{ v(E,{q(dn)},V) : val({q(dn)},V) }} :- d{j}(E).")
                R.append(f"hv(E,{q(dn)}) :- v(E,{q(dn)},_).")
        R.append("is(E,V) :- v(E,D,V).")
        self._defs()
        self._preds()
        for rn in m.rels_used:
            s1, s2 = self.lex.rel_sorts[rn]
            R.append(f"{{ r({q(rn)},X,Y) }} :- d{self.sort_index[s1]}(X), d{self.sort_index[s2]}(Y).")

    def _defs(self):
        R = self.rules
        self.def_index = {}
        for k, (dn, text) in enumerate(self.onto.defs.items()):
            self.def_index[dn] = k
            ce = parse_class(text, self.lex)
            srt = self.lex.sort.get(dn)
            a = self.comp_class(ce, "e", {"e": srt if (self.m.explicit and srt in self.sort_index) else "*"})
            R.append(f"#external od({k}).")
            R.append(f"is(Ve,{q(dn)}) :- ent(Ve), {a}, od({k}).")
            R.append(f"{{ is(Ve,{q(dn)}) }} :- ent(Ve), not od({k}).")

    def _preds(self):
        R, m = self.rules, self.m
        for pn, p in m.preds.items():
            j = self.sort_index[p.sort]
            if p.kind == "待定":
                R.append(f"{{ is(E,{q(pn)}) }} :- d{j}(E).")
            else:
                for el in p.extension:
                    R.append(f"is(e({j},{q(el)}),{q(pn)}).")

    def world(self):
        if self.m.explicit:
            return self.world_explicit()
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
        # 定義是本體約定。每個定義有一個開關 od(k)：開著時，定義項恰等於定義式；
        # 關著時，定義項成為一個未解釋的類（可真可假）。前提樹檢驗時，只開「依」中列出的定義，
        # 這樣每一步用到的約定都必須寫出來。
        self._defs()
        self._preds()
        for rn in m.rels_used:
            r = onto.rels[rn]
            ds = self.sort_index[m.default_sort]
            a1 = self.comp_class(parse_class(r.sig[0], self.lex), "x", {"x": m.default_sort})
            a2 = self.comp_class(parse_class(r.sig[1], self.lex), "y", {"y": m.default_sort})
            R.append(f"{{ r({q(rn)},Vx,Vy) }} :- d{ds}(Vx), d{ds}(Vy), Vx != Vy, {a1}, {a2}.")
            if r.symmetric:
                R.append(f":- r({q(rn)},X,Y), not r({q(rn)},Y,X).")
            if r.transitive:
                R.append(f":- r({q(rn)},X,Y), r({q(rn)},Y,Z), X != Z, not r({q(rn)},X,Z).")
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
        self._structural = module.onto.structural_defs()
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
        for i in self.c.def_index.values():
            ctl.assign_external(clingo.Function("od", [clingo.Number(i)]), None)

    def defs_on_for(self, listed):
        """只開列出的定義（連同它們引用的定義、本體結構所需的定義）。"""
        onto = self.m.onto
        return onto.def_closure(listed) | self._structural

    def _assumptions(self, ctl, on, target=None, defs_on=None):
        A = []
        for sid, i in self.c.stmt_index.items():
            A.append((clingo.Function("on", [clingo.Number(i)]), sid in on))
        for sid, i in self.c.target_index.items():
            A.append((clingo.Function("q", [clingo.Number(i)]), sid == target))
        for dn, i in self.c.def_index.items():
            A.append((clingo.Function("od", [clingo.Number(i)]), defs_on is None or dn in defs_on))
        return A

    def sat(self, on, target=None, want_world=False, minimize=True, defs_on=None):
        """有無模型？target 給定時，求「前提 ∧ 非 target」的模型。
        defs_on 給定時，只有其中的定義生效（其餘定義項當作未解釋的類）。"""
        self.calls += 1
        if not want_world:
            res = self._ctl.solve(assumptions=self._assumptions(self._ctl, set(on), target, defs_on))
            return res.satisfiable, None
        if minimize:
            if self._opt is None:
                self._opt = self._control(minimize=True)
            ctl = self._opt
            ctl.configuration.solve.opt_mode = "opt"
        else:
            ctl = self._ctl
        last = None
        with ctl.solve(assumptions=self._assumptions(ctl, set(on), target, defs_on), yield_=True) as h:
            for mdl in h:
                last = mdl.symbols(atoms=True)
            sat = h.get().satisfiable
        return sat, (self._world(last) if last is not None else None)

    def entails(self, on, target, world=True, defs_on=None) -> Result:
        sat, w = self.sat(on, target, want_world=world, defs_on=defs_on)
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
        for e in ents.values():
            e.attrs["_論域"] = e.sort
        for s in symbols:
            if s.name == "v":
                key = str(s.arguments[0])
                if key in ents:
                    dn, val = s.arguments[1].string, s.arguments[2].string
                    old = ents[key].attrs.get(dn)
                    if old is None or old == "—":
                        ents[key].attrs[dn] = val
                    elif val != "—":       # 互斥關掉時，一門可取多值
                        ents[key].attrs[dn] = tuple(sorted(set((old if isinstance(old, tuple) else (old,)) + (val,))))
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

    @staticmethod
    def minimize(items, pred):
        """在 items 中取一個極小子集 S，使 pred(S) 為真（pred 須單調：子集真則超集亦真）。
        用 QuickXplain 式的二分：極小集小時，呼叫次數約為 k·log(n/k)，遠少於逐條試刪。"""
        items = list(items)
        if not pred(items):
            raise ValueError("全集不滿足條件，無極小子集")

        def rec(background, cands, has_delta):
            if has_delta and pred(background):
                return []
            if len(cands) == 1:
                return list(cands)
            half = len(cands) // 2
            a, b = cands[:half], cands[half:]
            sb = rec(background + a, b, True)
            sa = rec(background + sb, a, bool(sb))
            return sa + sb
        if pred([]):
            return []
        out = rec([], items, False)
        order = {x: i for i, x in enumerate(items)}
        return sorted(out, key=order.get)

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
