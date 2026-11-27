"""Kosa 命題語言：詞法與語法。

兩層語法：
  1. 句式（毘曇自己的論式）：
       A 唯 B     凡 A 皆 B              （A、B 是類表達式）
       A 皆 B / A 是 B / A 定 B   同「唯」
       A 非 B     凡 A 皆非 B
       A 即 B     A 與 B 外延相同
       A 通 B、C  凡 A 或 B 或 C，且 A 容 B、A 容 C
       A 容 B     有 A 是 B
       A 容有     有 A
       A 無       無有 A
       A：B、C    A 即「B 或 C」（《俱舍萬字》的寫法）
  2. 公式（一階邏輯，關鍵詞用漢字）：
       凡 x、y：……   有 z：……   且 或 非  ⇒ ⇔  ＝ ≠
       類(x)  關係(x，y)  門(x)＝門(y)  門(x)＝值  ［類表達式］(x)

類表達式：「・」連接的項（且）；每項是「或」連接的原子；原子前可加「非」。
"""
from __future__ import annotations
import re
from dataclasses import dataclass, field

# ───────────── 抽象語法 ─────────────
# 類表達式： ('名', 名) | ('且', [..]) | ('或', [..]) | ('非', ce)
# 公式：
#   ('凡', [(變元, 類別)], f)  ('有', [(變元, 類別)], f)
#   ('且', [f..])  ('或', [f..])  ('非', f)  ('⇒', a, b)  ('⇔', a, b)
#   ('屬', ce, x)            x 屬於類 ce
#   ('係', 關係名, [x, y])   x 與 y 有此關係
#   ('同門', 門名, x, y)      門(x)＝門(y)
#   ('同', x, y)             x＝y
#   ('真',)

PUNCT_MAP = {
    "(": "（", ")": "）", ",": "，", ":": "：", "[": "［", "]": "］",
    "=": "＝", "≠": "≠",
}
MULTI = [("<=>", "⇔"), ("=>", "⇒"), ("!=", "≠"), ("→", "⇒"), ("↔", "⇔")]
KEYWORDS = ["凡", "有", "且", "或", "非", "⇒", "⇔"]
SENT_OPS = {"唯", "皆", "是", "定", "非", "即", "通", "容", "容有", "無", "不容"}


class KosaSyntaxError(Exception):
    pass


@dataclass
class Tok:
    kind: str   # NAME / KW / VAR / P
    text: str


def normalize(s: str) -> str:
    for a, b in MULTI:
        s = s.replace(a, b)
    out = []
    for ch in s:
        out.append(PUNCT_MAP.get(ch, ch))
    return "".join(out)


class Lexicon:
    """已知詞表：門值、定義、門名、關係、謂詞、類別。由本體與模組共同提供。"""

    def __init__(self):
        self.kind: dict[str, tuple] = {}
        self.alias: dict[str, str] = {}
        self._sorted: list[str] | None = None
        # 論域資訊：詞（門值、定義、謂詞、類別）→ 所屬論域；門 → 論域；關係 → (第一項論域, 第二項論域)
        self.sort: dict[str, str] = {}
        self.dim_sort: dict[str, str] = {}
        self.rel_sorts: dict[str, tuple] = {}

    def add(self, name, info):
        if name in self.kind and self.kind[name] != info:
            raise KosaSyntaxError(f"詞「{name}」重複定義：{self.kind[name]} 與 {info}")
        self.kind[name] = info
        self._sorted = None

    def add_alias(self, a, b):
        self.alias[a] = b
        self._sorted = None

    def names(self):
        if self._sorted is None:
            self._sorted = sorted(list(self.kind) + list(self.alias), key=len, reverse=True)
        return self._sorted

    def canon(self, n):
        return self.alias.get(n, n)


def tokenize(s: str, lex: Lexicon) -> list[Tok]:
    s = normalize(s)
    toks, i = [], 0
    names = lex.names()
    while i < len(s):
        c = s[i]
        if c.isspace():
            i += 1
            continue
        if c in "（），：、［］＝≠・":
            toks.append(Tok("P", c))
            i += 1
            continue
        m = None
        for n in names:
            if s.startswith(n, i):
                m = n
                break
        if m is not None:
            toks.append(Tok("NAME", lex.canon(m)))
            i += len(m)
            continue
        if c in "凡有且或非":
            toks.append(Tok("KW", c))
            i += 1
            continue
        if c in "⇒⇔":
            toks.append(Tok("KW", c))
            i += 1
            continue
        mv = re.match(r"[a-zA-Z][a-zA-Z0-9_']*", s[i:])
        if mv:
            toks.append(Tok("VAR", mv.group(0)))
            i += len(mv.group(0))
            continue
        # 未知詞：取出連續漢字報錯——封閉詞彙
        mu = re.match(r"[㐀-鿿\U00020000-\U0002ffff]+", s[i:])
        bad = mu.group(0) if mu else c
        raise KosaSyntaxError(f"未知詞「{bad}」：不在本體詞表中。若是新概念，請先在本體中定義。")
    return toks


class Parser:
    def __init__(self, toks: list[Tok], lex: Lexicon, default_sort: str):
        self.t, self.i, self.lex, self.ds = toks, 0, lex, default_sort

    def peek(self, k=0):
        j = self.i + k
        return self.t[j] if j < len(self.t) else None

    def eat(self, kind=None, text=None):
        tk = self.peek()
        if tk is None:
            raise KosaSyntaxError("句子意外結束")
        if (kind and tk.kind != kind) or (text and tk.text != text):
            raise KosaSyntaxError(f"此處應為「{text or kind}」，見到「{tk.text}」")
        self.i += 1
        return tk

    def at(self, kind=None, text=None):
        tk = self.peek()
        return tk is not None and (kind is None or tk.kind == kind) and (text is None or tk.text == text)

    # 類表達式
    def class_expr(self):
        terms = [self.class_term()]
        while self.at("P", "・"):
            self.eat()
            terms.append(self.class_term())
        return terms[0] if len(terms) == 1 else ("且", terms)

    def class_term(self):
        alts = [self.class_atom()]
        while self.at("KW", "或"):
            self.eat()
            alts.append(self.class_atom())
        return alts[0] if len(alts) == 1 else ("或", alts)

    def class_atom(self):
        if self.at("KW", "非"):
            self.eat()
            return ("非", self.class_atom())
        tk = self.eat("NAME")
        info = self.lex.kind.get(tk.text)
        if info is None or info[0] not in ("值", "定義", "謂詞", "類別"):
            raise KosaSyntaxError(f"「{tk.text}」不是可作為類的詞（它是{info[0] if info else '未知詞'}）")
        return ("名", tk.text)

    # 公式
    def formula(self):
        if self.at("KW", "凡") or self.at("KW", "有"):
            q = self.eat().text
            vs = self.varlist()
            self.eat("P", "：")
            body = self.formula()
            return (q, vs, body)
        return self.iff()

    def varlist(self):
        vs = []
        while True:
            v = self.eat("VAR").text
            sort = self.ds
            if self.at("NAME") and self.lex.kind.get(self.peek().text, ("",))[0] == "類別":
                # 允許「t∈道位」寫作「t 道位」
                sort = self.eat().text
            vs.append((v, sort))
            if self.at("P", "、") or self.at("P", "，"):
                self.eat()
                continue
            break
        return vs

    def iff(self):
        a = self.imp()
        if self.at("KW", "⇔"):
            self.eat()
            b = self.imp()
            return ("⇔", a, b)
        return a

    def imp(self):
        a = self.disj()
        if self.at("KW", "⇒"):
            self.eat()
            b = self.imp()
            return ("⇒", a, b)
        return a

    def disj(self):
        xs = [self.conj()]
        while self.at("KW", "或"):
            self.eat()
            xs.append(self.conj())
        return xs[0] if len(xs) == 1 else ("或", xs)

    def conj(self):
        xs = [self.unary()]
        while self.at("KW", "且"):
            self.eat()
            xs.append(self.unary())
        return xs[0] if len(xs) == 1 else ("且", xs)

    def unary(self):
        if self.at("KW", "非"):
            self.eat()
            return ("非", self.unary())
        if self.at("KW", "凡") or self.at("KW", "有"):
            return self.formula()
        if self.at("P", "（"):
            self.eat()
            f = self.formula()
            self.eat("P", "）")
            return f
        return self.atom()

    def atom(self):
        if self.at("P", "［"):
            self.eat()
            ce = self.class_expr()
            self.eat("P", "］")
            self.eat("P", "（")
            x = self.eat("VAR").text
            self.eat("P", "）")
            return ("屬", ce, x)
        if self.at("VAR"):
            x = self.eat().text
            op = self.eat("P").text
            y = self.eat("VAR").text
            if op == "＝":
                return ("同", x, y)
            if op == "≠":
                return ("非", ("同", x, y))
            raise KosaSyntaxError(f"變元之間只能用＝或≠，見到「{op}」")
        tk = self.eat("NAME")
        info = self.lex.kind.get(tk.text)
        self.eat("P", "（")
        args = [self.eat("VAR").text]
        while self.at("P", "，") or self.at("P", "、"):
            self.eat()
            args.append(self.eat("VAR").text)
        self.eat("P", "）")
        kind = info[0]
        if kind == "關係":
            if len(args) != 2:
                raise KosaSyntaxError(f"關係「{tk.text}」需要兩項")
            return ("係", tk.text, args)
        if len(args) != 1:
            raise KosaSyntaxError(f"「{tk.text}」只接受一項")
        if kind == "門":
            # 門(x)＝門(y) / 門(x)≠門(y) / 門(x)＝值
            op = self.eat("P").text
            if op not in ("＝", "≠"):
                raise KosaSyntaxError("門之後應接＝或≠")
            rhs = self.eat("NAME")
            rinfo = self.lex.kind.get(rhs.text)
            if rinfo[0] == "門":
                if rhs.text != tk.text:
                    raise KosaSyntaxError("只能比較同一門的值")
                self.eat("P", "（")
                y = self.eat("VAR").text
                self.eat("P", "）")
                f = ("同門", tk.text, args[0], y)
            elif rinfo[0] == "值" and rinfo[1] == tk.text:
                f = ("屬", ("名", rhs.text), args[0])
            else:
                raise KosaSyntaxError(f"「{rhs.text}」不是門「{tk.text}」的值")
            return f if op == "＝" else ("非", f)
        if kind in ("值", "定義", "謂詞", "類別"):
            return ("屬", ("名", tk.text), args[0])
        raise KosaSyntaxError(f"「{tk.text}」不能這樣用")


def _split_list(s: str) -> list[str]:
    return [p for p in re.split(r"[、，,]", s) if p.strip()]


def class_names(ce):
    k = ce[0]
    if k == "名":
        return {ce[1]}
    if k == "非":
        return class_names(ce[1])
    out = set()
    for c in ce[1]:
        out |= class_names(c)
    return out


def class_sort(ce, lex: Lexicon, what=""):
    """類表達式所屬的論域（法、有情……）。不涉及任何有論域的詞時回傳 None。"""
    sorts = {lex.sort[n] for n in class_names(ce) if n in lex.sort}
    if len(sorts) > 1:
        raise KosaSyntaxError(f"{what}混用了不同論域的詞：{'、'.join(sorted(sorts))}")
    return sorts.pop() if sorts else None


def resolve_sorts(f, lex: Lexicon, default: str):
    """為公式中未標論域的變元推出論域：看它出現在哪些類、關係、門中。推不出的取預設論域。"""
    def walk(g, scope, acc):
        k = g[0]
        if k in ("凡", "有"):
            inner = dict(scope)
            for v, srt in g[1]:
                key = (v, id(g))
                inner[v] = key
                acc.setdefault(key, set())
                if srt:
                    acc[key].add(srt)
            walk(g[2], inner, acc)
        elif k in ("且", "或"):
            for h in g[1]:
                walk(h, scope, acc)
        elif k == "非":
            walk(g[1], scope, acc)
        elif k in ("⇒", "⇔"):
            walk(g[1], scope, acc)
            walk(g[2], scope, acc)
        elif k == "屬":
            srt = class_sort(g[1], lex, "類表達式")
            if srt and g[2] in scope:
                acc[scope[g[2]]].add(srt)
        elif k == "係":
            sig = lex.rel_sorts.get(g[1])
            if sig:
                for v, srt in zip(g[2], sig):
                    if v in scope and srt:
                        acc[scope[v]].add(srt)
        elif k == "同門":
            srt = lex.dim_sort.get(g[1])
            for v in (g[2], g[3]):
                if v in scope and srt:
                    acc[scope[v]].add(srt)

    acc = {}
    walk(f, {}, acc)
    for key, ss in acc.items():
        if len(ss) > 1:
            raise KosaSyntaxError(f"變元「{key[0]}」同時被當作{'、'.join(sorted(ss))}")

    def rebuild(g):
        k = g[0]
        if k in ("凡", "有"):
            vs = []
            for v, srt in g[1]:
                ss = acc.get((v, id(g)), set())
                vs.append((v, srt or (next(iter(ss)) if ss else default)))
            return (k, vs, rebuild(g[2]))
        if k in ("且", "或"):
            return (k, [rebuild(h) for h in g[1]])
        if k == "非":
            return (k, rebuild(g[1]))
        if k in ("⇒", "⇔"):
            return (k, rebuild(g[1]), rebuild(g[2]))
        return g
    return rebuild(f)


def parse_statement(src: str, lex: Lexicon, default_sort: str, infer: bool = True):
    """把一句命題解析為公式。回傳 (公式, 句式名)。
    infer 時，變元的論域（法、有情）由句中的詞推出，推不出時取 default_sort；
    否則（舊模組，如積類別）一律取 default_sort。"""
    s = normalize(src.strip()).rstrip("。")
    head = s.lstrip()[:1]

    def as_formula():
        toks = tokenize(s, lex)
        p = Parser(toks, lex, None if infer else default_sort)
        f = p.formula()
        if p.peek() is not None:
            raise KosaSyntaxError(f"多餘的內容：「{p.peek().text}」")
        return resolve_sorts(f, lex, default_sort) if infer else f

    if head in ("凡", "有") and len(s) > 1 and (s[1].isspace() or re.match(r"[a-zA-Z]", s[1])):
        return as_formula(), "公式"

    def srt(*ces):
        if not infer:
            return default_sort
        found = {class_sort(c, lex, "這句命題") for c in ces} - {None}
        if len(found) > 1:
            raise KosaSyntaxError(f"這句命題混用了不同論域的詞：{'、'.join(sorted(found))}")
        return found.pop() if found else default_sort

    parts = s.split()
    x = "x"
    if len(parts) == 1 and "：" in s:
        a, b = s.split("：", 1)
        A = _class(a, lex, default_sort)
        Bs = [_class(y, lex, default_sort) for y in _split_list(b)]
        d = srt(A, *Bs)
        rhs = Bs[0] if len(Bs) == 1 else ("或", Bs)
        return ("凡", [(x, d)], ("⇔", ("屬", A, x), ("屬", rhs, x))), "列舉"
    if len(parts) == 2 and parts[1] in ("無", "容有"):
        A = _class(parts[0], lex, default_sort)
        d = srt(A)
        if parts[1] == "無":
            return ("非", ("有", [(x, d)], ("屬", A, x))), "無"
        return ("有", [(x, d)], ("屬", A, x)), "容有"
    if len(parts) == 2 and parts[1] == "各容有":
        Cs = [_class(y, lex, default_sort) for y in _split_list(parts[0])]
        d = srt(*Cs)
        exs = [("有", [(x, d)], ("屬", C, x)) for C in Cs]
        return (exs[0] if len(exs) == 1 else ("且", exs)), "各容有"
    if len(parts) == 2 and parts[1] == "互斥":
        Cs = [_class(y, lex, default_sort) for y in _split_list(parts[0])]
        if len(Cs) < 2:
            raise KosaSyntaxError("「互斥」前至少要列兩類")
        d = srt(*Cs)
        pairs = [("非", ("屬", ("且", [Cs[i], Cs[j]]), x))
                 for i in range(len(Cs)) for j in range(i + 1, len(Cs))]
        body = pairs[0] if len(pairs) == 1 else ("且", pairs)
        return ("凡", [(x, d)], body), "互斥"
    if len(parts) == 3 and parts[1] in SENT_OPS:
        op = parts[1]
        A = _class(parts[0], lex, default_sort)
        if op == "通":
            Bs = [_class(b, lex, default_sort) for b in _split_list(parts[2])]
            d = srt(A, *Bs)
            uni = ("凡", [(x, d)], ("⇒", ("屬", A, x), ("屬", ("或", Bs) if len(Bs) > 1 else Bs[0], x)))
            exs = [("有", [(x, d)], ("屬", ("且", [A, B]), x)) for B in Bs]
            return ("且", [uni] + exs), "通"
        B = _class(parts[2], lex, default_sort)
        d = srt(A, B)
        if op in ("唯", "皆", "是", "定"):
            return ("凡", [(x, d)], ("⇒", ("屬", A, x), ("屬", B, x))), "唯"
        if op in ("非", "不容"):
            return ("凡", [(x, d)], ("⇒", ("屬", A, x), ("非", ("屬", B, x)))), "非"
        if op == "即":
            return ("凡", [(x, d)], ("⇔", ("屬", A, x), ("屬", B, x))), "即"
        if op == "容":
            return ("有", [(x, d)], ("屬", ("且", [A, B]), x)), "容"
    # 退而求其次：當作公式解析
    try:
        return as_formula(), "公式"
    except KosaSyntaxError:
        raise KosaSyntaxError(f"無法識別的句式：「{src}」") from None


def _class(s: str, lex: Lexicon, ds: str):
    toks = tokenize(s, lex)
    p = Parser(toks, lex, ds)
    ce = p.class_expr()
    if p.peek() is not None:
        raise KosaSyntaxError(f"類表達式「{s}」有多餘內容「{p.peek().text}」")
    return ce


def parse_class(s: str, lex: Lexicon, ds: str = "法"):
    return _class(normalize(s), lex, ds)


# ───────────── 把公式寫回可讀的形式 ─────────────

def show_class(ce) -> str:
    k = ce[0]
    if k == "名":
        return ce[1]
    if k == "非":
        return "非" + show_class(ce[1])
    if k == "且":
        return "・".join(show_class(c) for c in ce[1])
    if k == "或":
        return "或".join(show_class(c) for c in ce[1])
    raise ValueError(ce)


def show(f, top=True) -> str:
    k = f[0]
    if k in ("凡", "有"):
        vs = "、".join(v for v, _ in f[1])
        return f"{k} {vs}：{show(f[2], False)}"
    if k == "且":
        return " 且 ".join(_paren(g) for g in f[1])
    if k == "或":
        return " 或 ".join(_paren(g) for g in f[1])
    if k == "非":
        return "非 " + _paren(f[1])
    if k in ("⇒", "⇔"):
        return f"{_paren(f[1])} {k} {_paren(f[2])}"
    if k == "屬":
        ce = f[1]
        if ce[0] == "名":
            return f"{ce[1]}({f[2]})"
        return f"［{show_class(ce)}］({f[2]})"
    if k == "係":
        return f"{f[1]}({f[2][0]}，{f[2][1]})"
    if k == "同門":
        return f"{f[1]}({f[2]})＝{f[1]}({f[3]})"
    if k == "同":
        return f"{f[1]}＝{f[2]}"
    if k == "真":
        return "真"
    if k == "結構":
        return f[3]
    raise ValueError(f)


def _paren(g):
    s = show(g, False)
    if g[0] in ("且", "或", "⇒", "⇔", "凡", "有"):
        return f"（{s}）"
    return s


def free_vars(f, bound=frozenset()):
    k = f[0]
    if k in ("凡", "有"):
        nb = bound | {v for v, _ in f[1]}
        return free_vars(f[2], nb)
    if k in ("且", "或"):
        out = set()
        for g in f[1]:
            out |= free_vars(g, bound)
        return out
    if k == "非":
        return free_vars(f[1], bound)
    if k in ("⇒", "⇔"):
        return free_vars(f[1], bound) | free_vars(f[2], bound)
    if k == "屬":
        return {f[2]} - bound
    if k == "係":
        return set(f[2]) - bound
    if k == "同門":
        return {f[2], f[3]} - bound
    if k == "同":
        return {f[1], f[2]} - bound
    return set()   # 真、結構：無自由變元
