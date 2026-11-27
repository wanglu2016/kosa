"""命令行：python3 -m kosa 〈命令〉 …

  驗證                         頌文核對＋推導（「依」）檢驗＋全庫相容＋題庫；有不通過即以非零狀態退出（GitHub 自動運行用）
  結構                         計算命題庫的施設與推出（核心條目附反例）
  題庫                         判定題庫中的全部題目，與書中答案比對：一致／未決／相違
  判定 〈命題〉                 用命題庫判定一條命題：證成／證否／未決，附理由。論域（法、有情）由句中的詞推出
  報告                         生成 報告/index.html
  案例                         生成案例頁「三道題」（報告/three-questions.html，本機預覽版）
  lean                         重新導出 lean/Kosa/Lib.lean（法）、LibP.lean（有情）、Module1.lean、Check.lean 與網頁版
  檢驗 〈模組〉 〈命題〉 〈前提…〉   （舊模組一、二、三）這些前提是否蘊涵該命題
  相容 〈模組〉 〈命題…〉          （舊模組一、二、三）這些命題是否相容；不相容則列出極小衝突集
  核對                         核對全部頌文引用
〈模組〉可寫「一」至「六」或目錄名。前提可寫「組:二〇二二」表示整組。
"""
from __future__ import annotations
import sys
from pathlib import Path

from .demos import ROOT, load, verses, load_library
from .engine import Engine
from .render import world_lines
from .workflow import analyze_conflicts

MODS = {"一": "一_有覆無記色", "二": "二_九十八隨眠", "三": "三_眾賢之矛盾", "四": "四_前提體系",
        "五": "五_阿羅漢最後心", "六": "六_阿那含成就初靜慮"}
OLD = ("一", "二", "三")             # 自帶前提的舊演示模組
# 網頁版單文件：(名稱, 定義文件, 證明文件…)
WEB = (("模組四", "Lib.lean", ["Proof5.lean", "Proof4.lean"]),
       ("模組五", "Lib.lean", ["Proof5.lean"]),
       ("模組六", "Lib.lean", ["Proof6.lean"]),
       ("三道題", "Lib.lean", ["Proof5.lean", "Proof4.lean", "Proof7.lean"]))
LINKS = {"模組四": "連結.txt", "模組五": "連結五.txt", "模組六": "連結六.txt"}


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
            fn = LINKS.get(name, f"連結・{name}.txt")
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
        for k in OLD:
            onto, m = load(MODS[k])
            for sid, field, quote, hits in v.check_module(m):
                mark = f"✓ {hits[0][0]} 第{hits[0][1]}行" if hits else "✗ 未找到"
                bad += 0 if hits else 1
                print(f"模組{k}【{sid}】{field}「{quote}」 {mark}")
        lib = load_library()
        for sid, field, quote, hits in v.check_module(lib) + v.check_ontology(lib.onto):
            mark = f"✓ {hits[0][0]} 第{hits[0][1]}行" if hits else "✗ 未找到"
            bad += 0 if hits else 1
            print(f"【{sid}】{field}「{quote}」 {mark}")
        print("全部一致。" if not bad else f"{bad} 句未找到。")
        if bad:
            sys.exit(1)
    elif cmd == "驗證":
        from .tree import verify
        v = verses()
        bad = 0
        lib = load_library()
        for k in OLD:
            onto, m = load(MODS[k])
            for sid, field, quote, hits in v.check_module(m):
                if not hits:
                    bad += 1
                    print(f"✗ 模組{k}【{sid}】頌「{quote}」未在 CBETA 找到")
        for sid, field, quote, hits in v.check_module(lib) + v.check_ontology(lib.onto):
            if not hits:
                bad += 1
                print(f"✗【{sid}】頌「{quote}」未在 CBETA 找到")
        R = verify(Engine(lib))
        print(f"── 命題庫：{len(lib.entry_ids())} 條，本體結構條目 {len(lib.structure_ids())} 條")
        print("全庫相容：", "✓" if R.consistent else "✗")
        bad += 0 if R.consistent else 1
        for sid, ec in R.edges.items():
            mark = "✓" if ec.ok and not ec.unnecessary else "✗"
            bad += 0 if mark == "✓" else 1
            extra = "" if ec.ok else "（推不出" + ("；再補 " + "、".join(ec.needed) + " 就推得出" if ec.needed else "") + "）"
            if ec.unnecessary:
                extra += "（多餘：" + "、".join(ec.unnecessary) + "）"
            print(f"{mark}【{sid}】{R.nodes[sid].title}{extra}")
        for k in ("四", "五", "六"):
            onto, m = mod(k)
            if m.goal not in m.statements:
                bad += 1
                print(f"✗ 模組{k}的目標【{m.goal}】不在命題庫中")
        from .judge import run_bank, all_banks
        for p in all_banks():
            m, J, out, groups = run_bank(p)
            from collections import Counter
            c = Counter(x.match for x in out)
            print(f"── 題庫 {m.title}：一致 {c['一致']}、未決 {c['未決']}、相違 {c['相違']}")
            for x in out:
                if x.match == "相違":
                    bad += 1
                    print(f"✗【{x.sid}】判定為「{x.verdict}」，書中為「{x.expected}」")
        print("全部通過。" if not bad else f"{bad} 處不通過。")
        if bad:
            sys.exit(1)
    elif cmd == "結構":
        from .structure import analyze
        lib = load_library()
        S = analyze(lib, worlds=False)
        c = S.counts
        print(f"命題條目 {c['命題條目']}，本體結構條目 {c['本體結構條目']}；門 {c['門']}、門值 {c['門值']}、定義 {c['定義']}、關係 {c['關係']}")
        if not S.consistent:
            if S.bad_existence:
                sys.exit("這些存在部分與全稱部分不相容：" + "、".join(S.bad_existence))
            sys.exit("命題庫的全稱部分自相矛盾。")
        print(f"施設 {c['施設']}（其中核心 {c['其中核心']}），推出 {c['推出']}")
        for s in S.ids("推出"):
            print(f"  推出【{s}】{lib.statements[s].meta.get('標題', lib.statements[s].text)} ← {'、'.join(S.entry(s).premises) or '本體定義'}")
        print("非核心的施設（可與別的條目互推，選它作施設是一種選擇）：" + "、".join(S.ids("施設", False)))
    elif cmd == "題庫":
        from .judge import run_bank, all_banks
        from collections import Counter
        bad = 0
        for p in all_banks():
            m, J, out, groups = run_bank(p)
            c = Counter(x.match for x in out)
            print(f"── {m.title}：一致 {c['一致']}、未決 {c['未決']}、相違 {c['相違']}")
            for title, vs in groups.items():
                mark = "✗" if any(x.match == "相違" for x in vs) else ("？" if any(x.match == "未決" for x in vs) else "✓")
                print(f"{mark} {title}")
                for x in vs:
                    if x.match != "一致":
                        bad += x.match == "相違"
                        print(f"    {'✗' if x.match == '相違' else '？'}【{x.sid}】判定為「{x.verdict}」，書中為「{x.expected}」")
        print("沒有相違。" if not bad else f"{bad} 個原子問題與書相違。")
        if bad:
            sys.exit(1)
    elif cmd == "判定":
        from .judge import judge_text
        from .lang import KosaSyntaxError
        try:
            m, J, x = judge_text(argv[1])
        except KosaSyntaxError as e:
            sys.exit("命題寫不進 Kosa 語言：" + str(e).split("】", 1)[-1])
        print(f"判定：{x.verdict}")
        if x.verdict in ("證成", "證否"):
            print("極小前提：" + ("、".join(x.premises) if x.premises else "（由本體定義直接得出）"))
            for s in x.premises:
                st = m.statements[s]
                print(f"  【{s}】{st.text}  —— {st.meta.get('標題', '')}" + ("（待核）" if st.meta.get("狀態") == "待核" else ""))
        elif x.verdict == "未決":
            if x.vacuous:
                print(f"命題庫推不出它，也推不出它的否定。它只在沒有「{x.vacuous}」的世界裡成立："
                      f"若「{x.vacuous}」存在，它就不成立。庫中缺「{x.vacuous} 容有」這類存在命題，所以判不出。")
            else:
                print("命題庫推不出它，也推不出它的否定。它成立的世界：")
                for l in world_lines(x.example, m):
                    print("  " + l)
            print("它不成立的世界：")
            for l in world_lines(x.counter, m):
                print("  " + l)
    elif cmd == "案例":
        from .case import build_case, PAGE
        out = ROOT / "報告" / PAGE
        build_case(out=out)
        print(f"已生成案例頁 {out}（本機預覽版，未附結構計算；字體見報告的 assets）")
    elif cmd == "lean":
        from .lean import LeanExport, LibExport, check_file
        onto, m1 = mod("一")
        (ROOT / "lean" / "Kosa" / "Module1.lean").write_text(LeanExport(m1).build(list(m1.statements), "Kosa.M1"), encoding="utf-8")
        lib = load_library()
        out = ROOT / "lean" / "Kosa" / "Lib.lean"
        out.write_text(LibExport(lib).build(lib.entry_ids(), "Kosa.Lib"), encoding="utf-8")
        print(f"已導出 {out}")
        src, proved = check_file(lib, ROOT / "lean" / "Kosa", "Kosa.Lib")
        (ROOT / "lean" / "Kosa" / "Check.lean").write_text(src, encoding="utf-8")
        print(f"已導出 Check.lean（{len(proved)} 條有 Lean 證明）")
        web_lean()
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
