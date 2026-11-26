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


def statement_sorts(f, acc=None):
    """公式中各量化變元的論域。"""
    acc = set() if acc is None else acc
    k = f[0]
    if k in ("凡", "有"):
        acc |= {s for _, s in f[1]}
        statement_sorts(f[2], acc)
    elif k in ("且", "或"):
        for g in f[1]:
            statement_sorts(g, acc)
    elif k == "非":
        statement_sorts(f[1], acc)
    elif k in ("⇒", "⇔"):
        statement_sorts(f[1], acc)
        statement_sorts(f[2], acc)
    return acc


class LeanExport:
    """導出一個論域（法或有情）的 Lean 定義。跨論域的命題（同時講法與有情）暫不導出。"""

    def __init__(self, module, sort=None):
        self.m = module
        self.onto = module.onto
        self.lex = module.lex
        self.sort_name = sort or module.default_sort
        self.sort = module.sorts[self.sort_name]
        self.dims = self.sort.dims
        self.rels = [r for r in module.rels_used
                     if module.lex.rel_sorts.get(r, (self.sort_name, self.sort_name)) == (self.sort_name, self.sort_name)]

    def exportable(self, sid):
        st = self.m.statements[sid]
        if st.meta.get("_結構"):
            return False          # 本體結構在 Lean 中由「世界」的定義本身保證（門是函數）
        return statement_sorts(st.formula) <= {self.sort_name}

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
            if info[0] == "類別":
                return "True"
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
            if pr.sort == self.sort_name:
                L.append(f"  {g(pn)} : E → Prop")
        for r in self.rels:
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
        for r in self.rels:
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
        sids = [s for s in sids if self.exportable(s)]
        return "\n".join(self.header(ns) + self.statements(sids) + [f"end {ns}", ""])


def proved_in_lean(proof_dir):
    """Proof*.lean 中已證的條目：定理名為「«編號成立»」者。回傳 {編號: 文件名}。"""
    import re
    out = {}
    for p in sorted(proof_dir.glob("Proof*.lean")):
        for m in re.finditer(r"^theorem «(.+?)成立»", p.read_text(encoding="utf-8"), re.M):
            out[m.group(1)] = p.stem
    return out


def check_file(module, proof_dir, namespaces):
    """生成 Check.lean：每條寫了「依」又有 Lean 證明的條目，檢驗其 Lean 證明只用「依」所列的條目。
    （本體定義、本體結構在 Lean 中是內建的，不算在內。）namespaces：論域 → Lean 命名空間。"""
    from .tree import nodes
    proved = proved_in_lean(proof_dir)
    N = nodes(module)
    imports = sorted(set(proved.values()))
    L = ["-- 本文件由 Kosa 自動生成（kosa/lean.py），請勿手改。",
         "-- 每一段 example 檢驗：某條目的 Lean 證明，只用到它的「依」所列的條目。",
         "-- 若證明用了「依」以外的條目，assumption 找不到它，這裡就會報錯。", ""]
    L += [f"import Kosa.{p}" for p in imports] + [""]
    by_ns = {}
    for sid, n in N.items():
        if sid not in proved or n.kind == "本體":
            continue
        deps = [d for d in n.deps if not module.statements[d].meta.get("_結構")]
        srt = statement_sorts(module.statements[sid].formula)
        if len(srt) != 1:
            continue
        by_ns.setdefault(namespaces[srt.pop()], []).append((sid, deps))
    for ns, items in by_ns.items():
        L += [f"namespace {ns}", ""]
        for sid, deps in items:
            hyps = " ".join(f"(h{i} : {g(d)} W)" for i, d in enumerate(deps, 1))
            L.append(f"example (W : {g('世界')}) (O : {g('本體公理')} W) {hyps} : {g(sid)} W := by")
            L.append(f"  apply {g(sid + '成立')} W <;> assumption")
            L.append("")
        L += [f"end {ns}", ""]
    return "\n".join(L), proved
