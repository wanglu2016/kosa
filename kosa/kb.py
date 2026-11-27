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
            # 縮進兩格以上：上一欄的續行（即使行中有「：」也不另起一欄）
            if raw.startswith("　　") and cur[1].get("_order"):
                last = cur[1]["_order"][-1]
                cur[1][last] += "\n" + line
                continue
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
    sort: str = "法"                                     # 此門用於哪個論域（法、有情）


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
        cur_sort = "法"
        for head, kv, no in read_blocks(root / "門.kosa"):
            if head.startswith("論域"):
                # 「論域 有情」：以下各門用於有情
                cur_sort = head[2:].strip()
                continue
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
            o.dims[m.group(1)] = Dim(m.group(1), vals, m.group(2), kv, vapp, cur_sort)
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
        sorts = {d.sort for d in self.dims.values()}
        for srt in sorts:
            lex.add(srt, ("類別",))
            lex.sort[srt] = srt
        for d in self.dims.values():
            lex.add(d.name, ("門",))
            lex.dim_sort[d.name] = d.sort
            for v in d.values:
                lex.add(v, ("值", d.name))
                lex.sort[v] = d.sort
        for n in self.defs:
            lex.add(n, ("定義",))
        for r in self.rels:
            lex.add(r, ("關係",))
        for a, b in self.aliases.items():
            lex.add_alias(a, b)
        # 定義的論域：由定義式中的詞推出（定義可引用定義，故反覆推到不再變）
        if getattr(self, "_def_sorts", None) is None:
            from .lang import class_sort
            ds = {}
            changed = True
            while changed:
                changed = False
                for n, text in self.defs.items():
                    if n in ds:
                        continue
                    for k, v in ds.items():
                        lex.sort[k] = v
                    srt = class_sort(parse_class(text, lex), lex, f"定義「{n}」")
                    if srt:
                        ds[n] = srt
                        changed = True
            for n in self.defs:
                if n not in ds:
                    raise KosaSyntaxError(f"定義「{n}」推不出論域")
            self._def_sorts = ds
        lex.sort.update(self._def_sorts)
        from .lang import class_sort
        for r in self.rels.values():
            lex.rel_sorts[r.name] = tuple(class_sort(parse_class(c, lex), lex, f"關係「{r.name}」") or "法"
                                          for c in r.sig)
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
    def load(cls, path: Path, onto: Ontology, extra_files=()):
        """讀一個模組文件。文件中「引 庫/某」一行把命題庫的那一部分併入本模組；
        「目標 某」指定前提體系的目標。extra_files 是另外要併入的文件（如題庫）。"""
        m = cls(path=path, onto=onto)
        lex = onto.lexicon()
        m.lex = lex
        m.goal = None
        m.side = []
        m.libraries = []
        m.auto_dims = False
        m.explicit = False      # 庫模式：門與關係的結構（互斥、窮盡、適用、類型……）是可開關的顯性條目
        pending = []
        m._read(path, pending)
        for f in extra_files:
            m._read(Path(f), pending)
        # 積類別：生成元素
        for s in m.sorts.values():
            if s.kind == "積":
                s.elements = m._product(s)
        for sid, text, kv, no, src in pending:
            sort = kv.get("_論域") or m.default_sort
            try:
                f, form = parse_statement(text, lex, sort, infer=m.explicit)
            except KosaSyntaxError as e:
                raise KosaSyntaxError(f"{src}:{no}【{sid}】{e}") from None
            if sid in m.statements:
                raise KosaSyntaxError(f"{src}:{no} 編號重複：{sid}")
            m.statements[sid] = Statement(sid, text, f, form, kv, no)
        if m.explicit:
            m._library_dims()
            m._structure()
            m._split_existential()
            m._example_witness()
        elif m.auto_dims:
            m._auto_dims()
        m._check_dims()
        return m

    # ── 庫模式 ──
    def _library_dims(self):
        """庫模式：每個開放類別用本體中屬於該論域的全部門；用本體的全部關係。"""
        for s in self.sorts.values():
            if s.kind == "開放":
                s.dims = [d for d, dim in self.onto.dims.items() if dim.sort == s.name]
        self.rels_used = [r for r in self.onto.rels
                          if all(x in self.sorts for x in self.lex.rel_sorts.get(r, ("法", "法")))]

    def _structure(self):
        """把本體中隱含的命題寫成顯性條目（編號如「性・互斥」），放在全部條目之前。
        門：互斥（一法於此門至多一值）、窮盡（適用者必有一值）、適用（取值者必屬適用類）、
        值的適用（如身表唯在色處）。關係：類型（兩項各屬其類，且不自反）、對稱、傳遞。"""
        out = {}
        onto = self.onto

        def add(sid, kind, name, text, extra=None):
            meta = {"品": "本體", "_結構": kind, "標題": text}
            if extra:
                meta.update(extra)
            out[sid] = Statement(sid, text, ("結構", kind, name, text), "結構", meta, 0)

        for s in self.sorts.values():
            if s.kind != "開放":
                continue
            for dn in s.dims:
                d = onto.dims[dn]
                add(f"{dn}・互斥", "互斥", dn, f"一{s.name}於「{dn}」門至多取一值")
                if d.applies:
                    add(f"{dn}・窮盡", "窮盡", dn, f"凡{d.applies}，於「{dn}」門必取一值")
                    add(f"{dn}・適用", "適用", dn, f"於「{dn}」門取值者，唯是{d.applies}")
                else:
                    add(f"{dn}・窮盡", "窮盡", dn, f"一切{s.name}於「{dn}」門必取一值")
                for val, vap in d.value_applies.items():
                    add(f"{val}・適用", "值適用", (dn, val), f"{val}唯是{vap}")
        for rn in self.rels_used:
            r = onto.rels[rn]
            add(f"{rn}・類型", "類型", rn, f"{rn}（x，y）：x 是{r.sig[0]}，y 是{r.sig[1]}，x、y 不同")
            if r.symmetric:
                add(f"{rn}・對稱", "對稱", rn, f"{rn}（x，y）則{rn}（y，x）")
            if r.transitive:
                add(f"{rn}・傳遞", "傳遞", rn, f"{rn}（x，y）且{rn}（y，z），x、z 不同，則{rn}（x，z）")
        for sid in out:
            if sid in self.statements:
                raise KosaSyntaxError(f"條目編號「{sid}」與本體結構條目重名")
        self.statements = {**out, **self.statements}

    def _split_existential(self):
        """把含存在部分的命題拆開：全稱部分「編號・全」、各存在部分「編號・有1」「編號・有2」……
        有界世界只有幾個元素，全部存在命題一起考就裝不下；所以全稱部分合考，存在部分逐條與全稱部分合考。
        （「A 通 B、C」＝ 凡 A 皆 B 或 C，且有 A 是 B、有 A 是 C：全稱一部分、存在兩部分。）"""
        add = {}
        for sid, st in self.statements.items():
            if st.meta.get("_結構"):
                continue
            f = st.formula
            conj = f[1] if f[0] == "且" else [f]
            ex = [g for g in conj if g[0] == "有"]
            if not ex:
                continue
            un = [g for g in conj if g[0] != "有"]
            st.meta["_部分"] = []
            if un:
                pid = f"{sid}・全"
                g = un[0] if len(un) == 1 else ("且", un)
                add[pid] = Statement(pid, show(g), g, "全稱部分", {"_屬": sid, "_部": "全"}, st.line)
                st.meta["_部分"].append(pid)
            for i, g in enumerate(ex, 1):
                pid = f"{sid}・有{i}" if len(ex) > 1 else f"{sid}・有"
                add[pid] = Statement(pid, show(g), g, "存在部分", {"_屬": sid, "_部": "有"}, st.line)
                st.meta["_部分"].append(pid)
        self.statements.update(add)

    def _example_witness(self):
        """題目（有「答」的條目、臨時判定的命題）若是「凡 A 皆……」，另立「編號・例」＝有 A，
        供判定「未決」時給一個不空的實例世界（否則最小的實例常是空世界，看不出甚麼）。"""
        add = {}
        for sid, st in self.statements.items():
            if not (st.meta.get("答") or sid == "待判"):
                continue
            f = st.formula
            if f[0] == "凡" and len(f[1]) == 1 and f[2][0] in ("⇒", "⇔") and f[2][1][0] == "屬":
                pid = f"{sid}・例"
                g = ("有", f[1], f[2][1])
                add[pid] = Statement(pid, show(g), g, "實例", {"_屬": sid, "_部": "例"}, st.line)
        self.statements.update(add)

    def structure_ids(self):
        return [s for s, st in self.statements.items() if st.meta.get("_結構")]

    def entry_ids(self):
        """命題庫的條目（不含本體結構條目、題目、拆出的部分）。"""
        return [s for s, st in self.statements.items()
                if not st.meta.get("_結構") and st.meta.get("_庫") and not st.meta.get("答")]

    def parts(self, sid):
        """一條命題拆成的部分；沒有存在部分的，就是它自己。"""
        return self.statements[sid].meta.get("_部分") or [sid]

    def universal_base(self):
        """全稱的底子：本體結構條目、無存在部分的條目、有存在部分者的全稱部分。"""
        out = self.structure_ids()
        for s in self.entry_ids():
            out += [p for p in self.parts(s) if self.statements[p].meta.get("_部") != "有"]
        return out

    def content_names(self, sid):
        """一條命題涉及的詞（定義展開到門值；門值連同其門）：用來判斷兩條命題是否相關。"""
        cache = self.__dict__.setdefault("_names", {})
        if sid in cache:
            return cache[sid]
        out = set()

        def cls(ce):
            k = ce[0]
            if k == "名":
                n = ce[1]
                info = self.lex.kind.get(n, ("",))
                if info[0] == "定義":
                    if n not in out:
                        out.add(n)
                        cls(parse_class(self.onto.defs[n], self.lex))
                elif info[0] == "值":
                    out.add(n)
                    out.add(info[1])
                elif info[0] == "謂詞":
                    out.add(n)
                return
            for c in (ce[1] if k in ("且", "或") else [ce[1]]):
                cls(c)

        def walk(f):
            k = f[0]
            if k in ("凡", "有"):
                walk(f[2])
            elif k in ("且", "或"):
                for g in f[1]:
                    walk(g)
            elif k == "非":
                walk(f[1])
            elif k in ("⇒", "⇔"):
                walk(f[1])
                walk(f[2])
            elif k == "屬":
                cls(f[1])
            elif k == "係":
                out.add(f[1])
            elif k == "同門":
                out.add(f[1])
        walk(self.statements[sid].formula)
        cache[sid] = out
        return out

    def relevant(self, a, b):
        """兩條命題有沒有共用的詞（不計「法類」這類幾乎處處出現的門）。"""
        common = self.content_names(a) & self.content_names(b)
        return bool(common - {"法類"})

    def existence_facts(self):
        """命題庫中的存在部分（逐條與全稱底子合考）。"""
        return [p for s in self.entry_ids() for p in self.parts(s) if self.statements[p].meta.get("_部") == "有"]

    def _read(self, path: Path, pending, lib_meta=None):
        m, lex = self, self.lex
        for head, kv, no in read_blocks(path):
            if head.startswith("模組") or head.startswith("題庫"):
                m.title = head[2:].strip()
                m.notes = kv
            elif head.startswith("次序："):
                pass
            elif head.startswith("論域"):
                if lib_meta is None:
                    raise KosaSyntaxError(f"{path.name}:{no} 「論域」只能出現在命題庫中")
            elif head.startswith("引 ") or head.startswith("引　"):
                self._import(head[1:].strip(), pending)
            elif head.startswith("目標 "):
                m.goal = head[2:].strip()
            elif head.startswith("旁證 "):
                m.side += split_names(head[2:].strip())
            elif head.startswith("類 "):
                mm = re.match(r"類\s+(\S+?)：(.+)$", head)
                name, rest = mm.group(1), mm.group(2).strip()
                if name in m.sorts:
                    continue
                lex.add(name, ("類別",))
                lex.sort[name] = name
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
                lex.sort[name] = name
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
                if name in m.preds:
                    continue
                lex.add(name, ("謂詞", sort))
                lex.sort[name] = sort
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
                meta = dict(kv)
                if lib_meta:
                    meta.update(lib_meta)
                pending.append((mm.group(1), mm.group(2).strip(), meta, no, path.name))
            else:
                raise KosaSyntaxError(f"{path.name}:{no} 無法識別：{head}")

    def _import(self, rel, pending):
        """併入命題庫的一部分：先讀「論域.kosa」（類別、謂詞），再按其中「次序」讀各品。"""
        root = Path(__file__).resolve().parent.parent / rel
        if not root.is_dir():
            raise KosaSyntaxError(f"沒有命題庫「{rel}」")
        self.libraries.append(rel)
        self.explicit = True
        head_file = root / "論域.kosa"
        order = []
        for head, kv, no in read_blocks(head_file):
            if head.startswith("次序："):
                order = split_names(head.split("：", 1)[1])
        self._read(head_file, pending, lib_meta={})
        sort = self.default_sort
        files = [root / f"{n}.kosa" for n in order] + sorted(
            f for f in root.glob("*.kosa") if f.stem not in order and f.name != "論域.kosa")
        for f in files:
            if f.exists():
                self._read(f, pending, lib_meta={"品": f.stem, "_論域": sort or self.default_sort, "_庫": rel})

    def _auto_dims(self):
        """自動推算預設類別要用的門與關係：命題、定義、關係類型、適用條件所涉及的門，取其閉包。"""
        onto = self.onto
        s = self.sorts[self.default_sort]
        need = set(s.dims)
        rels = set(self.rels_used)
        for st in self.statements.values():
            need |= self.formula_dims(st.formula)
            rels |= self._formula_rels(st.formula)
        for rn in rels:
            if rn in onto.rels:
                r = onto.rels[rn]
                need |= self.class_dims(parse_class(r.sig[0], self.lex)) | self.class_dims(parse_class(r.sig[1], self.lex))
        changed = True
        while changed:
            changed = False
            for dn in list(need):
                d = onto.dims[dn]
                for ap in [d.applies] + list(d.value_applies.values()):
                    if ap:
                        extra = self.class_dims(parse_class(ap, self.lex)) - need
                        if extra:
                            need |= extra
                            changed = True
        s.dims = [d for d in onto.dims if d in need]
        self.rels_used = [r for r in onto.rels if r in rels]

    def _formula_rels(self, f):
        k = f[0]
        if k == "係":
            return {f[1]} if f[1] in self.onto.rels else set()
        if k in ("凡", "有"):
            return self._formula_rels(f[2])
        if k in ("且", "或"):
            out = set()
            for g in f[1]:
                out |= self._formula_rels(g)
            return out
        if k == "非":
            return self._formula_rels(f[1])
        if k in ("⇒", "⇔"):
            return self._formula_rels(f[1]) | self._formula_rels(f[2])
        return set()

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
