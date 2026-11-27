"""在一個具體的「世界」（模型）裡計算類與公式的真假。

用途：反例渲染、自動診斷（某條候選前提是否被反例違反）、計數。
"""
from __future__ import annotations
from dataclasses import dataclass, field

from .lang import parse_class

LABELS = "甲乙丙丁戊己庚辛壬癸子丑寅卯辰巳午未申酉戌亥"

_def_cache: dict = {}


def _def_ce(name, onto, lex):
    key = (id(onto), name)
    if key not in _def_cache:
        _def_cache[key] = parse_class(onto.defs[name], lex)
    return _def_cache[key]


def class_holds_attrs(ce, attrs, onto, lex, preds):
    k = ce[0]
    if k == "名":
        n = ce[1]
        info = lex.kind[n]
        if info[0] == "值":
            a = attrs.get(info[1])
            return a == n or (isinstance(a, tuple) and n in a)
        if info[0] == "類別":
            return attrs.get("_論域") == n
        if info[0] == "定義":
            return class_holds_attrs(_def_ce(n, onto, lex), attrs, onto, lex, preds)
        if info[0] == "謂詞":
            return n in preds
        return False
    if k == "且":
        return all(class_holds_attrs(c, attrs, onto, lex, preds) for c in ce[1])
    if k == "或":
        return any(class_holds_attrs(c, attrs, onto, lex, preds) for c in ce[1])
    if k == "非":
        return not class_holds_attrs(ce[1], attrs, onto, lex, preds)
    raise ValueError(ce)


@dataclass
class Ent:
    key: str            # ASP 項，如 e(0,3)
    sort: str
    attrs: dict
    preds: set
    label: str = ""


@dataclass
class World:
    ents: list = field(default_factory=list)
    rels: set = field(default_factory=set)      # (關係, key1, key2)

    def by_key(self, k):
        for e in self.ents:
            if e.key == k:
                return e
        raise KeyError(k)

    def of_sort(self, s):
        return [e for e in self.ents if e.sort == s]


def holds(f, world: World, env: dict, onto, lex) -> bool:
    k = f[0]
    if k == "屬":
        e = env[f[2]]
        return class_holds_attrs(f[1], e.attrs, onto, lex, e.preds)
    if k == "係":
        a, b = env[f[2][0]], env[f[2][1]]
        return (f[1], a.key, b.key) in world.rels
    if k == "同門":
        a, b = env[f[2]], env[f[3]]
        return _vals(a.attrs.get(f[1])) == _vals(b.attrs.get(f[1]))
    if k == "同":
        return env[f[1]].key == env[f[2]].key
    if k == "非":
        return not holds(f[1], world, env, onto, lex)
    if k == "且":
        return all(holds(g, world, env, onto, lex) for g in f[1])
    if k == "或":
        return any(holds(g, world, env, onto, lex) for g in f[1])
    if k == "⇒":
        return (not holds(f[1], world, env, onto, lex)) or holds(f[2], world, env, onto, lex)
    if k == "⇔":
        return holds(f[1], world, env, onto, lex) == holds(f[2], world, env, onto, lex)
    if k in ("凡", "有"):
        vs = f[1]

        def rec(i, env2):
            if i == len(vs):
                return holds(f[2], world, env2, onto, lex)
            v, s = vs[i]
            dom = world.of_sort(s)
            if k == "凡":
                return all(rec(i + 1, {**env2, v: e}) for e in dom)
            return any(rec(i + 1, {**env2, v: e}) for e in dom)
        return rec(0, env)
    if k == "真":
        return True
    if k == "結構":
        return structure_holds(f, world, onto, lex)
    raise ValueError(f)


def _vals(a):
    if a is None or a == "—":
        return frozenset()
    return frozenset(a) if isinstance(a, tuple) else frozenset([a])


def structure_holds(f, world, onto, lex):
    """本體結構條目在一個世界中是否成立。"""
    _, kind, name, _ = f
    if kind in ("互斥", "窮盡", "適用"):
        d = onto.dims[name]
        ce = parse_class(d.applies, lex) if d.applies else None
        for e in world.of_sort(d.sort):
            vs = _vals(e.attrs.get(name))
            app = class_holds_attrs(ce, e.attrs, onto, lex, e.preds) if ce else True
            if kind == "互斥" and len(vs) > 1:
                return False
            if kind == "窮盡" and app and not vs:
                return False
            if kind == "適用" and vs and not app:
                return False
        return True
    if kind == "值適用":
        dn, val = name
        d = onto.dims[dn]
        ce = parse_class(d.value_applies[val], lex)
        return all(class_holds_attrs(ce, e.attrs, onto, lex, e.preds)
                   for e in world.of_sort(d.sort) if val in _vals(e.attrs.get(dn)))
    r = onto.rels[name]
    pairs = {(a, b) for rn, a, b in world.rels if rn == name}
    if kind == "類型":
        c1, c2 = parse_class(r.sig[0], lex), parse_class(r.sig[1], lex)
        for a, b in pairs:
            ea, eb = world.by_key(a), world.by_key(b)
            if a == b or not class_holds_attrs(c1, ea.attrs, onto, lex, ea.preds) \
                    or not class_holds_attrs(c2, eb.attrs, onto, lex, eb.preds):
                return False
        return True
    if kind == "對稱":
        return all((b, a) in pairs for a, b in pairs)
    if kind == "傳遞":
        return all((a, c) in pairs for a, b in pairs for b2, c in pairs if b == b2 and a != c)
    return True
