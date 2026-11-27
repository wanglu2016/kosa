"""命題庫的結構：哪些條目是施設，哪些可由其餘推出。

做法（見 skill〈施設〉一節）：
  1. 獨立性：每條條目，看它能否由其餘全部條目推出。推不出的，求解器給一個反例世界——
     這是確定的證據：在任何一種施設中，它都必須被施設（「核心」）。
  2. 施設的選擇：按「偏好」從低到高逐條試：若它可由目前剩下的條目推出，就把它列為「推出」，
     從施設中拿掉。這樣得到一組互不可推的施設（不唯一；偏好決定選哪一組）。
  3. 每條「推出」的條目，求一組由施設中取的極小前提。

偏好（越高越應留作施設）：本體結構＞有頌或屬約定＞有出處（萬字、論文）＞無出處；
編者擬了「依」的、標「待核」的，偏好最低（先試著由別的推出）。

存在部分：含「有……」的命題拆成全稱部分與存在部分（見 kb.Module._split_existential）。
全稱部分之間照上面計算；一條存在部分，看它能否由全稱施設、或全稱施設加另一條存在部分推出。

注意：「推得出」是有界的結論（求解器只窮盡有限大小的世界）；全稱部分的「推不出」附有反例，是確定的。
"""
from __future__ import annotations
from dataclasses import dataclass, field

from .engine import Engine


@dataclass
class EntryStatus:
    sid: str
    rank: int
    independent: bool = False      # 不能由其餘推出（全稱部分附反例）
    counter: object = None
    role: str = "施設"             # 施設 / 推出
    premises: list = field(default_factory=list)


@dataclass
class Structure:
    entries: dict                  # 項目（本體結構條目、條目、條目的部分）→ EntryStatus
    module: object = None
    consistent: bool = True
    bad_existence: list = field(default_factory=list)   # 與全稱底子不相容的存在部分
    counts: dict = field(default_factory=dict)

    def ids(self, role=None, independent=None):
        """按條目（不按部分）列出。"""
        out = []
        for s in self.module.structure_ids() + self.module.entry_ids():
            x = self.entry(s)
            if (role is None or x.role == role) and (independent is None or x.independent == independent):
                out.append(s)
        return out

    def entry(self, sid):
        """條目的身分：各部分中有一部分是施設，條目就是施設；全部推出，條目才是推出。"""
        if sid in self.entries:
            return self.entries[sid]
        parts = [self.entries[p] for p in self.module.parts(sid)]
        x = EntryStatus(sid, parts[0].rank)
        x.independent = any(p.independent for p in parts)
        x.counter = next((p.counter for p in parts if p.counter is not None), None)
        if all(p.role == "推出" for p in parts):
            x.role = "推出"
            x.premises = list(dict.fromkeys(q for p in parts for q in p.premises))
        return x


def preference(st):
    meta = st.meta
    if meta.get("_結構"):
        r = 50
    elif meta.get("頌") or meta.get("性質") == "約定":
        r = 40
    elif meta.get("出處") or meta.get("依據"):
        r = 30
    else:
        r = 20
    if meta.get("依"):
        r -= 15
    if meta.get("狀態") == "待核":
        r -= 10
    return r


def analyze(module, engine: Engine | None = None, worlds: bool = True) -> Structure:
    e = engine or Engine(module)
    st = module.statements
    U = module.universal_base()
    E = module.existence_facts()
    rank = lambda p: preference(st[st[p].meta.get("_屬", p)])
    S = Structure({p: EntryStatus(p, rank(p)) for p in U + E}, module)
    S.consistent = e.consistent(U).ok
    if not S.consistent:
        return S
    S.bad_existence = [x for x in E if not e.consistent(U + [x]).ok]
    if S.bad_existence:
        S.consistent = False
        return S
    # 1. 獨立性
    for s in U:
        r = e.entails([x for x in U if x != s], s, world=worlds)
        if not r.ok:
            S.entries[s].independent = True
            S.entries[s].counter = r.world

    def ex_derivable(x, basis, others):
        for extra in [[]] + [[y] for y in others if y != x and module.relevant(x, y)]:
            if e.entails(basis + extra, x, world=False).ok:
                return extra
        return None
    for x in E:
        if ex_derivable(x, U, E) is None:
            S.entries[x].independent = True
    # 2. 施設的選擇（全稱部分）：偏好低者先試；同偏好者，後出現的先試
    basis = list(U)
    for s in sorted(U, key=lambda s: (S.entries[s].rank, -U.index(s))):
        if S.entries[s].independent:
            continue
        rest = [x for x in basis if x != s]
        if e.entails(rest, s, world=False).ok:
            basis = rest
            S.entries[s].role = "推出"
    # 存在部分
    ebasis = list(E)
    support = {}
    for x in sorted(E, key=lambda s: (S.entries[s].rank, -E.index(s))):
        if S.entries[x].independent:
            continue
        extra = ex_derivable(x, basis, [y for y in ebasis if y != x])
        if extra is not None:
            ebasis = [y for y in ebasis if y != x]
            S.entries[x].role = "推出"
            support[x] = extra
    # 3. 推出者的極小前提（取自施設）
    for s in U:
        if S.entries[s].role == "推出":
            S.entries[s].premises = e.minimize(basis, lambda P: e.entails(list(P), s, world=False).ok)
    for x in E:
        if S.entries[x].role == "推出":
            # 所依的存在部分若後來也被推出，順著鏈找到仍在施設中的那一條（推出具傳遞性）
            extra = support[x]
            seen = {x}
            while extra and extra[0] not in ebasis and extra[0] not in seen:
                seen.add(extra[0])
                extra = support.get(extra[0], [])
            S.entries[x].premises = e.minimize(basis + extra, lambda P: e.entails(list(P), x, world=False).ok)
    onto = module.onto
    S.counts = {
        "門": len(onto.dims), "門值": sum(len(d.values) for d in onto.dims.values()),
        "定義": len(onto.defs), "關係": len(onto.rels),
        "本體結構條目": len(module.structure_ids()), "命題條目": len(module.entry_ids()),
        "存在部分": len(E),
        "施設": len(S.ids("施設")), "其中核心": len(S.ids("施設", True)), "推出": len(S.ids("推出")),
    }
    return S
