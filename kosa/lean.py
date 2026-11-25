"""把模組（開放類別）導出為 Lean 4。

導出的內容：
  · 每一門 → 一個歸納類型（值為構造子）；
  · 「世界」結構：論域 E、各門的取值函數、各關係；
  · 本體公理：適用條件、關係的類型約束、對稱；
  · 每條命題 → 一個 Prop 定義。
證明本身另寫（見 lean/ 目錄），由 Lean 內核檢查。
"""
from __future__ import annotations

from .lang import parse_class


def g(s):
    return f"«{s}»"


class LeanExport:
    def __init__(self, module):
        self.m = module
        self.onto = module.onto
        self.lex = module.lex
        self.sort = module.sorts[module.default_sort]
        self.dims = self.sort.dims

    def dim_has_dash(self, d):
        return self.onto.dims[d].applies is not None

    def cls(self, ce, x):
        k = ce[0]
        if k == "名":
            n = ce[1]
            info = self.lex.kind[n]
            if info[0] == "值":
                return f"W.{g(info[1])} {x} = .{g(n)}"
            if info[0] == "定義":
                return f"{g(n)} W {x}"
            if info[0] == "謂詞":
                return f"W.{g(n)} {x}"
            raise ValueError(n)
        if k == "且":
            return "(" + " ∧ ".join(self.cls(c, x) for c in ce[1]) + ")"
        if k == "或":
            return "(" + " ∨ ".join(self.cls(c, x) for c in ce[1]) + ")"
        if k == "非":
            return f"¬({self.cls(ce[1], x)})"
        raise ValueError(ce)

    def f(self, f):
        k = f[0]
        if k == "屬":
            return self.cls(f[1], f[2])
        if k == "係":
            return f"W.{g(f[1])} {f[2][0]} {f[2][1]}"
        if k == "同門":
            return f"W.{g(f[1])} {f[2]} = W.{g(f[1])} {f[3]}"
        if k == "同":
            return f"{f[1]} = {f[2]}"
        if k == "非":
            return f"¬({self.f(f[1])})"
        if k == "且":
            return "(" + " ∧ ".join(self.f(x) for x in f[1]) + ")"
        if k == "或":
            return "(" + " ∨ ".join(self.f(x) for x in f[1]) + ")"
        if k == "⇒":
            return f"({self.f(f[1])} → {self.f(f[2])})"
        if k == "⇔":
            return f"({self.f(f[1])} ↔ {self.f(f[2])})"
        if k in ("凡", "有"):
            q = "∀" if k == "凡" else "∃"
            vs = " ".join(v for v, _ in f[1])
            return f"({q} {vs} : W.E, {self.f(f[2])})"
        if k == "真":
            return "True"
        raise ValueError(f)

    def header(self, ns="Kosa"):
        L = ["-- 本文件由 Kosa 自動生成（kosa/lean.py），請勿手改。",
             f"-- 模組：{self.m.title}",
             "",
             f"namespace {ns}", ""]
        for d in self.dims:
            dim = self.onto.dims[d]
            vals = list(dim.values) + (["—"] if self.dim_has_dash(d) else [])
            L.append(f"/-- 門：{d}（{'、'.join(dim.values)}） -/")
            L.append(f"inductive {g(d + '值')} where")
            L.append("  | " + " | ".join(g(v) for v in vals))
            L.append("  deriving DecidableEq, Repr")
            L.append("")
        L.append("/-- 一個「世界」：論域 E，以及每個法在各門的取值、各關係。 -/")
        L.append(f"structure {g('世界')} where")
        L.append("  E : Type")
        for d in self.dims:
            L.append(f"  {g(d)} : E → {g(d + '值')}")
        for pn, pr in self.m.preds.items():
            if pr.sort == self.m.default_sort:
                L.append(f"  {g(pn)} : E → Prop")
        for r in self.m.rels_used:
            L.append(f"  {g(r)} : E → E → Prop")
        L.append("")
        exported = set()
        for n, text in self.onto.defs.items():
            ce = parse_class(text, self.lex)
            try:
                body = self.cls(ce, "x")
            except KeyError:
                continue
            # 只導出本模組用得到的門所構成的定義（所引用的定義也須已導出）
            if any(f"W.{g(d)}" in body for d in self.onto.dims if d not in self.dims):
                continue
            if any(f"{g(d)} W" in body for d in self.onto.defs if d not in exported):
                continue
            exported.add(n)
            L.append(f"/-- 定義：{n}＝{text} -/")
            L.append(f"def {g(n)} (W : {g('世界')}) (x : W.E) : Prop := {body}")
            L.append("")
        # 本體公理
        ax = []
        for d in self.dims:
            dim = self.onto.dims[d]
            if dim.applies:
                cond = self.cls(parse_class(dim.applies, self.lex), "x")
                ax.append((f"適用_{d}", f"∀ x : W.E, W.{g(d)} x = .{g('—')} ↔ ¬({cond})"))
            for val, vap in dim.value_applies.items():
                cond = self.cls(parse_class(vap, self.lex), "x")
                ax.append((f"適用_{val}", f"∀ x : W.E, W.{g(d)} x = .{g(val)} → {cond}"))
        for r in self.m.rels_used:
            rel = self.onto.rels[r]
            a = self.cls(parse_class(rel.sig[0], self.lex), "x")
            b = self.cls(parse_class(rel.sig[1], self.lex), "y")
            ax.append((f"類型_{r}", f"∀ x y : W.E, W.{g(r)} x y → ({a}) ∧ ({b}) ∧ x ≠ y"))
            if rel.symmetric:
                ax.append((f"對稱_{r}", f"∀ x y : W.E, W.{g(r)} x y → W.{g(r)} y x"))
            if rel.transitive:
                ax.append((f"傳遞_{r}", f"∀ x y z : W.E, W.{g(r)} x y → W.{g(r)} y z → x ≠ z → W.{g(r)} x z"))
        L.append("/-- 本體公理：適用條件、關係的類型約束、對稱。 -/")
        L.append(f"structure {g('本體公理')} (W : {g('世界')}) : Prop where")
        for n, body in ax:
            L.append(f"  {g(n)} : {body}")
        L.append("")
        return L

    def statements(self, sids):
        L = []
        for sid in sids:
            st = self.m.statements[sid]
            L.append(f"/-- 【{sid}】{st.text} -/")
            L.append(f"def {g(sid)} (W : {g('世界')}) : Prop :=")
            L.append(f"  {self.f(st.formula)}")
            L.append("")
        return L

    def build(self, sids, ns="Kosa"):
        return "\n".join(self.header(ns) + self.statements(sids) + [f"end {ns}", ""])
