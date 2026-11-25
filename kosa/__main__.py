"""命令行：python3 -m kosa 〈命令〉 …

  報告                         重跑全部模組，生成 報告/index.html
  檢驗 〈模組〉 〈命題〉 〈前提…〉   這些前提是否蘊涵該命題；不蘊涵則列出反例
  相容 〈模組〉 〈命題…〉          這些命題是否相容；不相容則列出極小衝突集
  核對                         核對全部頌文引用
  驗證                         頌文核對＋前提體系逐條檢驗；有任何一處不通過即以非零狀態退出（供 GitHub 自動運行）
  lean                         重新導出 lean/Kosa/Module1.lean
〈模組〉可寫「一」「二」「三」或目錄名。前提可寫「組:二〇二二」表示整組。
"""
from __future__ import annotations
import sys
from pathlib import Path

from .demos import ROOT, load, verses
from .engine import Engine
from .render import world_lines
from .workflow import analyze_conflicts

MODS = {"一": "一_有覆無記色", "二": "二_九十八隨眠", "三": "三_眾賢之矛盾", "四": "四_前提體系"}


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
        onto, m = mod("四")
        R = verify(Engine(m))
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
        bad += (0 if R.consistent else 1) + len(dep)
        print("全部通過。" if not bad else f"{bad} 處不通過。")
        if bad:
            sys.exit(1)
    elif cmd == "lean":
        from .lean import LeanExport
        for key, fname, ns in (("一", "Module1.lean", "Kosa.M1"), ("四", "Module4.lean", "Kosa.M4")):
            onto, m = mod(key)
            out = ROOT / "lean" / "Kosa" / fname
            out.write_text(LeanExport(m).build(list(m.statements), ns), encoding="utf-8")
            print(f"已導出 {out}")
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
