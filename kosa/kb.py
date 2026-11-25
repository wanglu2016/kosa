"""知識庫：讀取本體（門、定義、關係）與模組（類別、謂詞、命題）。"""
from __future__ import annotations
import re
from dataclasses import dataclass, field
from pathlib import Path

from .lang import Lexicon, KosaSyntaxError, parse_statement, parse_class, show, normalize

INDENT = ("　", " ", "\t")


def read_blocks(path: Path):
    """把檔案讀成若干塊：(首行, {鍵: 值}, 行號)。以 # 開頭的行是註釋。"""
    blocks = []
    cur = None
    for no, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        if raw.startswith(INDENT):
            if cur is None:
                raise KosaSyntaxError(f"{path}:{no} 縮進行之前沒有條目")
            line = raw.strip()
            if "：" in line:
                k, v = line.split("：", 1)
                k = k.strip()
                if k in cur[1]:
                    cur[1][k] += "\n" + v.strip()
                else:
                    cur[1][k] = v.strip()
                cur[1].setdefault("_order", []).append(k)
            else:
                cur[1]["說明"] = (cur[1].get("說明", "") + line)
            continue
        cur = (raw.strip(), {}, no)
        blocks.append(cur)
    return blocks


def split_names(s: str):
    return [p.strip() for p in re.split(r"[、，,]", s) if p.strip()]


@dataclass
class Dim:
    name: str
    values: list
    applies: str | None
    notes: dict
    value_applies: dict = field(default_factory=dict)   # 值 → 此值的適用類（如「身表〔色處〕」）


@dataclass
class Relation:
    name: str
    sig: tuple
    symmetric: bool
    notes: dict
    fixed_order_sort: str | None = None   # 由次序生成的關係（如「先於」）
    transitive: bool = False


@dataclass
class Ontology:
    dims: dict = field(default_factory=dict)
    defs: dict = field(default_factory=dict)       # 名 → 類表達式字串
    def_notes: dict = field(default_factory=dict)
    rels: dict = field(default_factory=dict)
    aliases: dict = field(default_factory=dict)

    @classmethod
    def load(cls, root: Path):
        o = cls()
        for head, kv, no in read_blocks(root / "門.kosa"):
            m = re.match(r"門\s+(\S+?)(?:〔(.+?)〕)?：(.+)$", head)
            if not m:
                raise KosaSyntaxError(f"門.kosa:{no} 無法解析：{head}")
            vals, vapp = [], {}
            for raw in split_names(m.group(3)):
                mv = re.match(r"(.+?)〔(.+?)〕$", raw)
                if mv:
                    vals.append(mv.group(1))
                    vapp[mv.group(1)] = mv.group(2)
                else:
                    vals.append(raw)
            o.dims[m.group(1)] = Dim(m.group(1), vals, m.group(2), kv, vapp)
        for head, kv, no in read_blocks(root / "定義.kosa"):
            if head.startswith("別名"):
                a, b = head[2:].strip().split("＝")
                o.aliases[a.strip()] = b.strip()
                continue
            m = re.match(r"定義\s+(\S+?)：(.+)$", head)
            if not m:
                raise KosaSyntaxError(f"定義.kosa:{no} 無法解析：{head}")
            o.defs[m.group(1)] = m.group(2).strip()
            o.def_notes[m.group(1)] = kv
        for head, kv, no in read_blocks(root / "關係.kosa"):
            m = re.match(r"關係\s+(\S+?)（(.+?)，(.+?)）(?:〔(.+?)〕)?$", head)
            if not m:
                raise KosaSyntaxError(f"關係.kosa:{no} 無法解析：{head}")
            props = m.group(4) or ""
            o.rels[m.group(1)] = Relation(m.group(1), (m.group(2), m.group(3)), "對稱" in props, kv,
                                          transitive="傳遞" in props)
        return o

    def lexicon(self) -> Lexicon:
        lex = Lexicon()
        for d in self.dims.values():
            lex.add(d.name, ("門",))
            for v in d.values:
                lex.add(v, ("值", d.name))
        for n in self.defs:
            lex.add(n, ("定義",))
        for r in self.rels:
            lex.add(r, ("關係",))
        for a, b in self.aliases.items():
            lex.add_alias(a, b)
        return lex

    def def_refs(self, text):
        """類表達式中直接引用的定義名。"""
        from .lang import tokenize
        lex = self.lexicon()
        return {t.text for t in tokenize(text, lex) if t.kind == "NAME" and lex.kind.get(t.text, ("",))[0] == "定義"}

    def def_closure(self, names):
        """定義及其所引用的定義（遞歸）。"""
        out, todo = set(), [n for n in names if n in self.defs]
        while todo:
            n = todo.pop()
            if n in out:
                continue
            out.add(n)
            todo += [r for r in self.def_refs(self.defs[n]) if r not in out]
        return out

    def structural_defs(self):
        """出現在門的適用條件、關係的類型中的定義：它們是本體結構的一部分，始終施加。"""
        names = set()
        for d in self.dims.values():
            for ap in [d.applies] + list(d.value_applies.values()):
                if ap:
                    names |= self.def_refs(ap)
        for r in self.rels.values():
            names |= self.def_refs(r.sig[0]) | self.def_refs(r.sig[1])
        return self.def_closure(names)

    def value_dim(self, v):
        for d in self.dims.values():
            if v in d.values:
                return d.name
        return None


@dataclass
class Sort:
    name: str
    kind: str                 # 開放 / 固定 / 積
    size: int = 0
    elements: list = field(default_factory=list)   # 固定：名稱；積：屬性字典
    dims: list = field(default_factory=list)
    ordered: bool = False


@dataclass
class Pred:
    name: str
    sort: str
    kind: str                 # 待定 / 事實
    extension: list = field(default_factory=list)
    notes: dict = field(default_factory=dict)


@dataclass
class Statement:
    sid: str
    text: str
    formula: tuple
    form: str
    meta: dict
    line: int

    @property
    def group(self):
        return self.meta.get("組", "")

    def label(self):
        return f"【{self.sid}】{self.text}"


@dataclass
class Module:
    path: Path
    onto: Ontology
    title: str = ""
    sorts: dict = field(default_factory=dict)
    preds: dict = field(default_factory=dict)
    rels_used: list = field(default_factory=list)
    order_rels: dict = field(default_factory=dict)     # 關係名 → 類別名
    statements: dict = field(default_factory=dict)
    default_sort: str = "法"
    closure: list = field(default_factory=list)
    notes: dict = field(default_factory=dict)
    lex: Lexicon | None = None

    @classmethod
    def load(cls, path: Path, onto: Ontology):
        m = cls(path=path, onto=onto)
        lex = onto.lexicon()
        m.lex = lex
        pending = []
        for head, kv, no in read_blocks(path):
            if head.startswith("模組"):
                m.title = head[2:].strip()
                m.notes = kv
            elif head.startswith("類 "):
                mm = re.match(r"類\s+(\S+?)：(.+)$", head)
                name, rest = mm.group(1), mm.group(2).strip()
                lex.add(name, ("類別",))
                if rest.startswith("開放"):
                    m.sorts[name] = Sort(name, "開放", size=int(re.search(r"\d+", rest).group(0)))
                else:
                    ordered = "（有序）" in rest
                    rest = rest.replace("（有序）", "")
                    m.sorts[name] = Sort(name, "固定", elements=split_names(rest), ordered=ordered)
            elif head.startswith("積 "):
                mm = re.match(r"積\s+(\S+?)：(.+)$", head)
                name = mm.group(1)
                dims = [d.strip() for d in re.split(r"[×xX＊*]", mm.group(2))]
                lex.add(name, ("類別",))
                m.sorts[name] = Sort(name, "積", dims=dims)
            elif head.startswith("用門 "):
                mm = re.match(r"用門\s+(\S+?)：(.+)$", head)
                m.sorts[mm.group(1)].dims = split_names(mm.group(2))
            elif head.startswith("用關係"):
                m.rels_used = split_names(head.split("：", 1)[1] if "：" in head else head[3:])
            elif head.startswith("次序關係 "):
                mm = re.match(r"次序關係\s+(\S+?)〔(.+?)〕", head)
                lex.add(mm.group(1), ("關係",))
                m.order_rels[mm.group(1)] = mm.group(2)
            elif head.startswith("謂詞 "):
                mm = re.match(r"謂詞\s+(\S+?)〔(.+?)〕：(.+)$", head)
                name, sort, rest = mm.group(1), mm.group(2), mm.group(3).strip()
                lex.add(name, ("謂詞", sort))
                if rest == "待定":
                    m.preds[name] = Pred(name, sort, "待定", notes=kv)
                else:
                    ext = [] if rest in ("（無）", "無") else split_names(rest)
                    m.preds[name] = Pred(name, sort, "事實", ext, notes=kv)
            elif head.startswith("預設類"):
                m.default_sort = head.split()[-1]
            elif head.startswith("閉包"):
                m.closure = split_names(head[2:])
            elif head.startswith("【"):
                mm = re.match(r"【(.+?)】(.+)$", head)
                pending.append((mm.group(1), mm.group(2).strip(), kv, no))
            else:
                raise KosaSyntaxError(f"{path.name}:{no} 無法識別：{head}")
        # 積類別：生成元素
        for s in m.sorts.values():
            if s.kind == "積":
                s.elements = m._product(s)
        for sid, text, kv, no in pending:
            try:
                f, form = parse_statement(text, lex, m.default_sort)
            except KosaSyntaxError as e:
                raise KosaSyntaxError(f"{path.name}:{no}【{sid}】{e}") from None
            if sid in m.statements:
                raise KosaSyntaxError(f"{path.name}:{no} 編號重複：{sid}")
            m.statements[sid] = Statement(sid, text, f, form, kv, no)
        m._check_dims()
        return m

    def _product(self, s: Sort):
        """積類別的元素。因子可以是一門（取其全部值），也可以是一個定義——
        定義須展開為若干門值之「或」（如「惑」＝貪或瞋或……或五見），每個門值連同它的適用條件
        所蘊含的上位門值一起寫入（如「身見」→ 見種＝身見、心所自性＝慧、法類＝心所）。"""
        onto = self.onto
        out = [dict()]
        dims = []
        for factor in s.dims:
            if factor in onto.dims:
                d = onto.dims[factor]
                dims.append(factor)
                new = []
                for partial in out:
                    appl = True
                    if d.applies:
                        appl = self._applies_partial(d.applies, partial)
                    vals = d.values if appl else ["—"]
                    for v in vals:
                        if v in d.value_applies and not self._applies_partial(d.value_applies[v], partial):
                            continue
                        q = dict(partial)
                        q[factor] = v
                        new.append(q)
                out = new
            elif factor in onto.defs:
                atoms = self._expand_values(factor)
                new = []
                for partial in out:
                    for v in atoms:
                        q = dict(partial)
                        q.update(self._value_closure(v))
                        new.append(q)
                out = new
                for v in atoms:
                    for dn in self._value_closure(v):
                        if dn not in dims:
                            dims.append(dn)
            else:
                raise KosaSyntaxError(f"積類別「{s.name}」的因子「{factor}」既不是門，也不是定義")
        # 因子展開出的門，未取值者記為「—」
        for q in out:
            for dn in dims:
                q.setdefault(dn, "—")
        s.dims = dims
        return out

    def _expand_values(self, name):
        """把定義展開為門值的列表；定義須是門值或定義之「或」。"""
        info = self.lex.kind.get(name)
        if info and info[0] == "值":
            return [name]
        if info and info[0] == "定義":
            ce = parse_class(self.onto.defs[name], self.lex)
            alts = ce[1] if ce[0] == "或" else [ce]
            out = []
            for a in alts:
                if a[0] != "名":
                    raise KosaSyntaxError(f"定義「{name}」不是單純的列舉，不能作積的因子")
                out += self._expand_values(a[1])
            return out
        raise KosaSyntaxError(f"「{name}」不能展開為門值")

    def _value_closure(self, v):
        """門值 v，及其適用條件所要求的上位門值（適用條件須是單一門值）。"""
        out = {}
        while v is not None:
            dn = self.onto.value_dim(v)
            out[dn] = v
            ap = self.onto.dims[dn].value_applies.get(v) or self.onto.dims[dn].applies
            if not ap:
                break
            ce = parse_class(ap, self.lex)
            if ce[0] == "名" and self.lex.kind.get(ce[1], ("",))[0] == "值":
                v = ce[1]
            else:
                break
        return out

    def formula_dims(self, f):
        """命題中出現的門（含定義、謂詞以外的類所涉及的門）。"""
        k = f[0]
        if k in ("凡", "有"):
            return self.formula_dims(f[2])
        if k in ("且", "或"):
            out = set()
            for g in f[1]:
                out |= self.formula_dims(g)
            return out
        if k == "非":
            return self.formula_dims(f[1])
        if k in ("⇒", "⇔"):
            return self.formula_dims(f[1]) | self.formula_dims(f[2])
        if k == "屬":
            return self.class_dims(f[1])
        if k == "同門":
            return {f[1]}
        return set()

    def _check_dims(self):
        """防呆：命題、定義、適用條件所涉及的門，必須是本模組用到的門。
        否則那些門值在世界中永遠不成立，命題會被靜默地誤讀。"""
        used = set()
        for s in self.sorts.values():
            used |= set(s.dims)
        for s in self.sorts.values():
            if s.kind != "開放":
                continue
            for dn in s.dims:
                d = self.onto.dims[dn]
                for ap in [d.applies] + list(d.value_applies.values()):
                    if not ap:
                        continue
                    miss = self.class_dims(parse_class(ap, self.lex)) - set(s.dims)
                    if miss:
                        raise KosaSyntaxError(
                            f"{self.path.name}：類別「{s.name}」用了門「{dn}」，它的適用條件涉及門「{'、'.join(sorted(miss))}」，請一併列入「用門」")
        for sid, st in self.statements.items():
            miss = self.formula_dims(st.formula) - used
            if miss:
                raise KosaSyntaxError(
                    f"{self.path.name}【{sid}】用到門「{'、'.join(sorted(miss))}」，但本模組沒有用這些門（見「用門」）")

    def _applies_partial(self, cls_text, partial):
        ce = parse_class(cls_text, self.lex)
        # 適用條件涉及積類別之外的門時（如「界〔有漏〕」而積中無「有漏無漏」），視為適用
        if not self.class_dims(ce) <= set(partial):
            return True
        from .evaluate import class_holds_attrs
        return class_holds_attrs(ce, partial, self.onto, self.lex, {})

    def class_dims(self, ce):
        k = ce[0]
        if k == "名":
            info = self.lex.kind[ce[1]]
            if info[0] == "值":
                return {info[1]}
            if info[0] == "定義":
                return self.class_dims(parse_class(self.onto.defs[ce[1]], self.lex))
            return set()
        if k == "非":
            return self.class_dims(ce[1])
        out = set()
        for c in ce[1]:
            out |= self.class_dims(c)
        return out

    def ids(self, group=None):
        return [k for k, s in self.statements.items() if group is None or s.group == group]

    def get(self, sid):
        return self.statements[sid]
