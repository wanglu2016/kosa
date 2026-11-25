"""三個演示模組的完整工作流程。每個函數回傳一個結果字典，供報告使用。"""
from __future__ import annotations
import time
from pathlib import Path

from .kb import Ontology, Module
from .engine import Engine
from .lang import parse_class, show
from .evaluate import class_holds_attrs
from .workflow import completion_loop, analyze_premises, analyze_conflicts, violated_by
from .corpus import Verses

ROOT = Path(__file__).resolve().parent.parent


def load(name):
    onto = Ontology.load(ROOT / "本體")
    return onto, Module.load(ROOT / "模組" / name / "命題.kosa", onto)


def verses():
    return Verses(ROOT / "語料" / "俱舍論頌.json")


def module_one():
    t0 = time.time()
    onto, m = load("一_有覆無記色")
    e = Engine(m)
    R = {"module": m, "engine": e}
    P = m.ids("二〇二二")
    pool = m.ids("補出候選")
    R["start"] = P
    R["pool"] = pool
    # ① 反例驅動補前提
    rounds = completion_loop(e, P, pool, "求證")
    R["rounds"] = rounds
    final = rounds[-1].premises
    R["final"] = final
    # ② 極小前提集、必要性見證
    R["analysis"] = analyze_premises(e, final, "求證", witnesses=True)
    # ③ 擴大的前提庫：全部候選 + 頌文
    # 存在命題（如頌一乙）不放入證明搜索：在有界世界裡，它們會佔用元素，造成虛假的「蘊涵」
    universal = [s for s in m.ids("頌文") if m.statements[s].formula[0] != "有"]
    R["excluded_existential"] = [s for s in m.ids("頌文") if s not in universal]
    big = final + [p for p in pool if p not in final] + universal
    R["big"] = big
    R["big_analysis"] = analyze_premises(e, big, "求證", witnesses=False)
    # ④ 頌文作為定理
    R["song3"] = analyze_premises(e, final, "頌三", witnesses=False)
    r = e.entails(final, "頌二")
    R["song2_from_final"] = r
    R["song2_violated"] = violated_by(r.world, m, [p for p in pool if p not in final]) if r.world else []
    R["song2"] = analyze_premises(e, final + ["補九"], "頌二", witnesses=False)
    # ⑤ 詮釋分歧：等起＝因等起
    alt = [p if p != "前提10甲" else "異讀10甲" for p in final]
    R["alt"] = alt
    R["alt_result"] = e.entails(alt, "求證")
    R["alt_song3"] = e.entails(alt, "頌三")
    # 為看清要點：再令轉與表同地，看頌三的反例
    R["alt_song3_same"] = e.entails(alt + ["異讀補四"], "頌三")
    T = ["異讀8", "異讀補四", "異讀補五"]
    R["transposed"] = T
    R["alt_transposed"] = e.entails(alt + T, "求證", world=False)
    lib = [s for s in m.statements if s not in ("求證", "異讀10甲") and s not in T]
    R["lib"] = lib
    R["lib_consistent"] = e.consistent(lib).ok
    L2 = [x for x in lib if x != "前提10甲"] + ["異讀10甲"] + T
    R["lib_alt_consistent"] = e.consistent(L2).ok
    R["lib_alt_conflicts"] = analyze_conflicts(e, L2)
    R["verse_checks"] = verses().check_module(m)
    R["calls"] = e.calls
    R["seconds"] = time.time() - t0
    return R


def module_two():
    t0 = time.time()
    onto, m = load("二_九十八隨眠")
    e = Engine(m)
    R = {"module": m, "engine": e}
    rules = m.ids("規則")
    R["rules"] = rules
    R["candidates"] = len(m.sorts["隨眠位"].elements)
    w, uniq = e.maximal_world(rules, m.closure)
    R["world"], R["unique"] = w, uniq

    def count(world, expr):
        ce = parse_class(expr, m.lex, "隨眠位")
        return [en for en in world.ents if class_holds_attrs(ce, en.attrs, onto, m.lex, en.preds)]

    R["count"] = lambda expr, world=w: len(count(world, expr))
    R["members"] = lambda expr, world=w: count(world, expr)
    # 預期數字：頌「十七七八四」「九十八」；《萬字》2.2「欲界36、色界31、無色界31」
    expected = [
        ("立", 98, "頌「故成九十八」"),
        ("立・欲界", 36, "《萬字》2.2「欲界 36」"),
        ("立・色界", 31, "《萬字》2.2「色界 31」"),
        ("立・無色界", 31, "《萬字》2.2「無色界 31」"),
        ("立・欲界・見苦所斷", 10, "頌「十七七八四」"),
        ("立・欲界・見集所斷", 7, "頌「十七七八四」"),
        ("立・欲界・見滅所斷", 7, "頌「十七七八四」"),
        ("立・欲界・見道所斷", 8, "頌「十七七八四」"),
        ("立・欲界・修所斷", 4, "頌「十七七八四」"),
    ]
    R["tests"] = [(x, n, src, R["count"](x)) for x, n, src in expected]
    # 每條規則的貢獻：去掉它，總數變成多少
    drop = []
    for r in rules:
        w2, u2 = e.maximal_world([x for x in rules if x != r], m.closure)
        drop.append((r, len(count(w2, "立")), u2))
    R["drop"] = drop
    # 沒有閉包：只要求滿足規則，「立」的外延可大可小
    R["no_closure_min"] = e.consistent(rules + ["驗證一"]).ok
    R["empty_ok"] = True
    # 模組一的前提2在此是定理
    R["v1"] = e.entails(rules, "驗證一", world=False).ok
    R["v2"] = e.entails(rules, "驗證二", world=False).ok
    R["v2_min"] = analyze_premises(e, rules, "驗證二", witnesses=False).minimal_sets
    R["verse_checks"] = verses().check_module(m)
    R["seconds"] = time.time() - t0
    return R


def module_three():
    t0 = time.time()
    onto, m = load("三_眾賢之矛盾")
    e = Engine(m)
    R = {"module": m, "engine": e}
    S = m.ids("陳述")
    R["stmts"] = S
    R["all_consistent"] = e.consistent(S).ok
    R["base"] = analyze_conflicts(e, S)
    variants = [
        ("方案一", "眾賢：「斷染時許依下修上」", [s if s != "壬" else "方案一" for s in S], "以【方案一】替換【壬】"),
        ("方案二", "眾賢：「許得離道而修」", [s for s in S if s != "己"], "放棄橋接原則【己】：有漏離繫得可不由修上邊世俗道而起"),
        ("方案三", "作者：以「退」會通【甲】", [s if s != "甲" else "方案三" for s in S], "以【方案三】替換【甲】"),
        ("方案二＋三", "兩者並用", [s if s != "甲" else "方案三" for s in S if s != "己"], "放棄【己】，並以【方案三】替換【甲】"),
    ]
    R["variants"] = []
    for name, who, stmts, how in variants:
        ca = analyze_conflicts(e, stmts)
        R["variants"].append((name, who, how, stmts, e.consistent(stmts).ok, ca))
    # 代表性的相容世界
    reps = [
        ("立場 A：前八品已修上地有漏", [s for s in S if s not in ("乙", "庚", "壬")]),
        ("立場 B：方案二＋三，再放棄辛、丁", [s if s != "甲" else "方案三" for s in S if s not in ("己", "辛", "丁")]),
        ("立場 C：第九無間道修", [s for s in S if s not in ("乙", "壬", "丁", "己")]),
    ]
    R["reps"] = []
    for label, stmts in reps:
        r = e.consistent(stmts, world=True)
        R["reps"].append((label, stmts, r.ok, r.world))
    R["verse_checks"] = verses().check_module(m)
    R["seconds"] = time.time() - t0
    return R


def module_four():
    t0 = time.time()
    from .tree import verify
    onto, m = load("四_前提體系")
    e = Engine(m)
    R = {"module": m, "engine": e}
    R["tree"] = verify(e)
    R["verse_checks"] = verses().check_module(m)
    rows = []
    tsv = ROOT / "模組" / "四_前提體系" / "精確化對照.tsv"
    for line in tsv.read_text(encoding="utf-8").splitlines():
        if line.startswith("#") or not line.strip():
            continue
        rows.append(line.split("\t"))
    R["precision"] = rows[1:]
    link = ROOT / "lean" / "網頁版" / "連結.txt"
    R["web_link"] = link.read_text(encoding="utf-8").strip() if link.exists() else ""
    R["seconds"] = time.time() - t0
    R["calls"] = e.calls
    return R


def tree_module(name, extra=None):
    """以前提體系組織的模組（五、六）：逐條檢驗，並計算目標的極小前提集。"""
    t0 = time.time()
    from .tree import verify
    onto, m = load(name)
    e = Engine(m)
    R = {"module": m, "engine": e}
    T = verify(e)
    R["tree"] = T
    R["verse_checks"] = verses().check_module(m)
    base = [s for s, n in T.nodes.items() if n.layer in ("約定", "假定")]
    R["base"] = base
    # 每條假定、約定：去掉它，目標還成立嗎？（不成立者，附反例）
    R["drop"] = {}
    for a in base:
        r = e.entails([b for b in base if b != a], T.goal)
        R["drop"][a] = r
    if extra:
        extra(R, e, m, T)
    R["seconds"] = time.time() - t0
    R["calls"] = e.calls
    return R


def module_five():
    def extra(R, e, m, T):
        # 異讀：若「集」讀成「能生後心」
        R["misread"] = e.entails(["異讀甲", "目標甲", "甲假五", "約甲二"], "推論甲", world=False).ok
        R["misread_consistent_empty"] = e.consistent(["異讀甲"] + R["base"]).ok
    return tree_module("五_阿羅漢最後心", extra)


def module_six():
    return tree_module("六_阿那含成就初靜慮")
