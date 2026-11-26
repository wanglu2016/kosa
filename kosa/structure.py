"""命題庫的結構：哪些條目是施設，哪些可由其餘推出。

做法（見 skill〈施設〉一節）：
  1. 獨立性：每條條目，看它能否由其餘全部條目推出。推不出的，求解器給一個反例世界——
     這是確定的證據：在任何一種施設中，它都必須被施設（「核心」）。
  2. 施設的選擇：按「偏好」從低到高逐條試：若它可由目前剩下的條目推出，就把它列為「推出」，
     從施設中拿掉。這樣得到一組互不可推的施設（不唯一；偏好決定選哪一組）。
  3. 每條「推出」的條目，求一組由施設中取的極小前提。

偏好（越高越應留作施設）：本體結構＞有頌或屬約定＞有出處（萬字、論文）＞無出處；
編者擬了「依」的、標「待核」的，偏好最低（先試著由別的推出）。

注意：「推得出」是有界的結論（求解器只窮盡有限大小的世界）；「推不出」附有反例，是確定的。
"""
from __future__ import annotations
from dataclasses import dataclass, field

from .engine import Engine


@dataclass
class EntryStatus:
    sid: str
    rank: int
    independent: bool = False      # 不能由其餘全部條目推出（附反例）
    counter: object = None
    role: str = "施設"             # 施設 / 推出
    premises: list = field(default_factory=list)


@dataclass
class Structure:
    entries: dict                  # 編號 → EntryStatus（按條目次序）
    consistent: bool = True
    counts: dict = field(default_factory=dict)

    def ids(self, role=None, independent=None):
        return [s for s, x in self.entries.items()
                if (role is None or x.role == role) and (independent is None or x.independent == independent)]


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
    order = module.structure_ids() + module.entry_ids()
    S = Structure({s: EntryStatus(s, preference(module.statements[s])) for s in order})
    S.consistent = e.consistent(order).ok
    if not S.consistent:
        return S
    # 1. 獨立性
    for s in order:
        rest = [x for x in order if x != s]
        r = e.entails(rest, s, world=worlds)
        if not r.ok:
            S.entries[s].independent = True
            S.entries[s].counter = r.world
    # 2. 施設的選擇：偏好低者先試；同偏好者，後出現的先試
    basis = list(order)
    trial = sorted(order, key=lambda s: (S.entries[s].rank, -order.index(s)))
    for s in trial:
        if S.entries[s].independent:
            continue
        rest = [x for x in basis if x != s]
        if e.entails(rest, s, world=False).ok:
            basis = rest
            S.entries[s].role = "推出"
    # 3. 推出者的極小前提（取自施設）
    for s in order:
        if S.entries[s].role == "推出":
            S.entries[s].premises = e.minimize(basis, lambda P: e.entails(list(P), s, world=False).ok)
    onto = module.onto
    S.counts = {
        "門": len(onto.dims), "門值": sum(len(d.values) for d in onto.dims.values()),
        "定義": len(onto.defs), "關係": len(onto.rels),
        "本體結構條目": len(module.structure_ids()), "命題條目": len(module.entry_ids()),
        "施設": len(S.ids("施設")), "其中核心": len(S.ids("施設", True)), "推出": len(S.ids("推出")),
    }
    return S
