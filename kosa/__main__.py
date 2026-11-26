"""命令行：python3 -m kosa 〈命令〉 …

  報告                         重跑全部模組，生成 報告/index.html
  檢驗 〈模組〉 〈命題〉 〈前提…〉   這些前提是否蘊涵該命題；不蘊涵則列出反例
  相容 〈模組〉 〈命題…〉          這些命題是否相容；不相容則列出極小衝突集
  核對                         核對全部頌文引用
  驗證                         頌文核對＋前提體系逐條檢驗；有任何一處不通過即以非零狀態退出（供 GitHub 自動運行）
  題庫                         判定題庫（題庫/*.kosa）中的全部題目，與書中答案比對
  判定 〈命題〉 [〈論域〉]        用命題庫判定一條命題：成立／不成立／可能／不可能，附理由
  lean                         重新導出 lean/Kosa/Module1.lean、Lib.lean、LibP.lean 與網頁版
〈模組〉可寫「一」至「六」或目錄名。前提可寫「組:二〇二二」表示整組。
"""
from __future__ import annotations
import sys
from pathlib import Path

from .demos import ROOT, load, verses
from .engine import Engine
from .render import world_lines
from .workflow import analyze_conflicts

MODS = {"一": "一_有覆無記色", "二": "二_九十八隨眠", "三": "三_眾賢之矛盾", "四": "四_前提體系",
        "五": "五_阿羅漢最後心", "六": "六_阿那含成就初靜慮"}
TREES = ("四", "五", "六")          # 以前提體系（約定、假定、定理、目標）組織的模組
# Lean 導出：模組一自成一體；命題庫各論域各導出一個文件（經由引用它的模組讀入）。
LEAN = (("一", "Module1.lean", "Kosa.M1"), ("四", "Lib.lean", "Kosa.Lib"), ("六", "LibP.lean", "Kosa.LibP"))
# 網頁版單文件：(名稱, 定義文件, 證明文件…)
WEB = (("模組四", "Lib.lean", ["Proof5.lean", "Proof4.lean"]),
       ("模組五", "Lib.lean", ["Proof5.lean"]),
       ("模組六", "LibP.lean", ["Proof6.lean"]))


def mod(name):
    return load(MODS.get(name, name))


def expand(m, items):
    out = []
    for it in items:
        if it.startswith("組:"):
            out += m.ids(it[2:])
        else:
            if it not in m.statements:
                sys.exit(f"沒有命題【{it}】")
            out.append(it)
    return out


def web_lean():
    """生成可貼進 live.lean-lang.org 的單文件版（定義＋證明），以及直接打開它的鏈接。"""
    web = ROOT / "lean" / "網頁版"
    web.mkdir(exist_ok=True)
    try:
        import lzstring
        lz = lzstring.LZString()
    except ImportError:
        lz = None
    for name, defs, proofs in WEB:
        parts = [(ROOT / "lean" / "Kosa" / defs).read_text(encoding="utf-8")]
        for pf in proofs:
            src = (ROOT / "lean" / "Kosa" / pf).read_text(encoding="utf-8")
            parts.append("\n".join(l for l in src.splitlines() if not l.startswith("import ")))
        src = (f"-- Kosa {name}（單文件版，可直接貼進 https://live.lean-lang.org 檢查）\n"
               "-- 前半是由 Kosa 自動生成的本體與命題庫定義；後半是證明。\n\n" + "\n".join(parts) + "\n")
        (web / f"{name}.lean").write_text(src, encoding="utf-8")
        if lz:
            link = "https://live.lean-lang.org/#codez=" + lz.compressToEncodedURIComponent(src)
            fn = "連結.txt" if name == "模組四" else f"連結{name[-1]}.txt"
            (web / fn).write_text(link + "\n", encoding="utf-8")
    print(f"已生成網頁版單文件 {web}" + ("" if lz else "（未安裝 lzstring，未生成鏈接）"))


def main(argv):
    if not argv or argv[0] in ("-h", "--help", "幫助"):
        print(__doc__)
        return
    cmd = argv[0]
    if cmd == "報告":
        from .report import build
        out = build(ROOT / "報告" / "index.html")
        print(f"已生成 {out}")
    elif cmd == "檢驗":
        onto, m = mod(argv[1])
        e = Engine(m)
        target, prem = argv[2], expand(m, argv[3:])
        r = e.entails(prem, target)
        if r.ok:
            print(f"成立：{len(prem)} 條前提蘊涵【{target}】（至多 {m.sorts[m.default_sort].size or '固定'} 個元素的一切世界）")
        else:
            print(f"不成立。反例：")
            for l in world_lines(r.world, m):
                print("  " + l)
    elif cmd == "相容":
        onto, m = mod(argv[1])
        e = Engine(m)
        S = expand(m, argv[2:])
        if e.consistent(S).ok:
            print("相容。")
        else:
            ca = analyze_conflicts(e, S)
            print("不相容。極小衝突集：")
            for c in ca.conflicts:
                print("  " + "、".join(c))
            print("極小修正集：")
            for c in ca.corrections:
                print("  放棄 " + "、".join(c))
    elif cmd == "核對":
        v = verses()
        bad = 0
        for k, name in MODS.items():
            onto, m = load(name)
            for sid, field, quote, hits in v.check_module(m):
                mark = f"✓ {hits[0][0]} 第{hits[0][1]}行" if hits else "✗ 未找到"
                bad += 0 if hits else 1
                print(f"模組{k}【{sid}】{field}「{quote}」 {mark}")
        onto = load(MODS["一"])[0]
        for sid, field, quote, hits in v.check_ontology(onto):
            mark = f"✓ {hits[0][0]} 第{hits[0][1]}行" if hits else "✗ 未找到"
            bad += 0 if hits else 1
            print(f"本體【{sid}】{field}「{quote}」 {mark}")
        print("全部一致。" if not bad else f"{bad} 句未找到。")
        if bad:
            sys.exit(1)
    elif cmd == "驗證":
        from .tree import verify
        v = verses()
        bad = 0
        for k, name in MODS.items():
            onto, m = load(name)
            for sid, field, quote, hits in v.check_module(m):
                if not hits:
                    bad += 1
                    print(f"✗ 模組{k}【{sid}】頌「{quote}」未在 CBETA 找到")
        for k in TREES:
            onto, m = mod(k)
            R = verify(Engine(m))
            print(f"── 模組{k}：{m.title}")
            for sid, ec in R.edges.items():
                mark = "✓" if ec.ok and not ec.unnecessary else "✗"
                bad += 0 if mark == "✓" else 1
                extra = "" if ec.ok else "（推不出）"
                if ec.unnecessary:
                    extra += "（多餘：" + "、".join(ec.unnecessary) + "）"
                print(f"{mark}【{sid}】{R.nodes[sid].title}{extra}")
            dep = [a for a, v2 in R.dependent_assumptions.items() if v2]
            print("假定相容：", "✓" if R.consistent else "✗")
            print("假定互不可推：", "✓" if not dep else "✗ " + "、".join(dep))
            pend = sorted({a for a in R.closure[R.goal] if R.nodes[a].meta.get("狀態") == "待核"},
                          key=list(R.nodes).index)
            print("目標所依的待核假定：", "、".join(pend) if pend else "無")
            bad += (0 if R.consistent else 1) + len(dep)
        for sid, field, quote, hits in v.check_ontology(onto):
            if not hits:
                bad += 1
                print(f"✗ 本體【{sid}】頌「{quote}」未在 CBETA 找到")
        from .judge import run_bank, all_banks
        for p in all_banks():
            m, J, out, groups = run_bank(p)
            npass = sum(1 for g in groups.values() if all(v.ok for v in g))
            wrong = [v for v in out if not v.ok]
            print(f"── 題庫 {m.title}：{npass}/{len(groups)} 題答對")
            for v in wrong:
                print(f"✗【{v.sid}】判定為「{v.verdict}」，書中為「{v.expected}」")
            bad += len(wrong)
        print("全部通過。" if not bad else f"{bad} 處不通過。")
        if bad:
            sys.exit(1)
    elif cmd == "題庫":
        from .judge import run_bank, all_banks
        bad = 0
        for p in all_banks():
            m, J, out, groups = run_bank(p)
            npass = sum(1 for g in groups.values() if all(v.ok for v in g))
            print(f"── {m.title}：{npass}/{len(groups)} 題答對（原子問題 {sum(v.ok for v in out)}/{len(out)}）")
            for title, vs in groups.items():
                mark = "✓" if all(v.ok for v in vs) else "✗"
                print(f"{mark} {title}")
                for v in vs:
                    if not v.ok:
                        bad += 1
                        print(f"    ✗【{v.sid}】判定為「{v.verdict}」，書中為「{v.expected}」")
        print("全部答對。" if not bad else f"{bad} 個原子問題答錯。")
        if bad:
            sys.exit(1)
    elif cmd == "判定":
        from .judge import judge_text
        from .lang import KosaSyntaxError
        lib = "庫/" + argv[2] if len(argv) > 2 else "庫/法"
        try:
            m, J, v = judge_text(argv[1], lib)
        except KosaSyntaxError as e:
            sys.exit("命題寫不進 Kosa 語言：" + str(e).split("】", 1)[-1])
        print(f"判定：{v.verdict}")
        if v.verdict in ("成立", "不可能"):
            print("最簡前提：" + ("、".join(v.short) if v.short else "（由本體定義直接得出）"))
            print("拆到底：" + ("、".join(v.deep) if v.deep else "（由本體定義直接得出）"))
            for s in v.deep:
                st = m.statements[s]
                print(f"  【{s}】{st.text}  —— {st.meta.get('標題', '')}" + ("（待核）" if st.meta.get("狀態") == "待核" else ""))
        elif v.world is not None:
            print("反例：" if v.verdict == "不成立" else "實例：")
            for l in world_lines(v.world, m):
                print("  " + l)
    elif cmd == "lean":
        from .lean import LeanExport
        for key, fname, ns in LEAN:
            onto, m = mod(key)
            out = ROOT / "lean" / "Kosa" / fname
            out.write_text(LeanExport(m).build(list(m.statements), ns), encoding="utf-8")
            print(f"已導出 {out}")
        web_lean()
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
