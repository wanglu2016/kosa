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


@dataclass
class Relation:
    name: str
    sig: tuple
    symmetric: bool
    notes: dict
    fixed_order_sort: str | None = None   # 由次序生成的關係（如「先於」）


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
            o.dims[m.group(1)] = Dim(m.group(1), split_names(m.group(3)), m.group(2), kv)
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
            o.rels[m.group(1)] = Relation(m.group(1), (m.group(2), m.group(3)), "對稱" in (m.group(4) or ""), kv)
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
        return m

    def _product(self, s: Sort):
        onto = self.onto
        out = [dict()]
        for dname in s.dims:
            d = onto.dims[dname]
            new = []
            for partial in out:
                appl = True
                if d.applies:
                    appl = self._applies_partial(d.applies, partial)
                vals = d.values if appl else ["—"]
                for v in vals:
                    q = dict(partial)
                    q[dname] = v
                    new.append(q)
            out = new
        return out

    def _applies_partial(self, cls_text, partial):
        ce = parse_class(cls_text, self.lex)
        # 適用條件涉及積類別之外的門時（如「惑種〔惑〕」而積中無「心所類」），視為適用
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
