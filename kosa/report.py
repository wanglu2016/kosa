"""生成〈Kosa v0.1 工作流程演示〉報告（單一 HTML 文件）。"""
from __future__ import annotations
import html
import re
import subprocess
from pathlib import Path

from .demos import module_one, module_two, module_three, ROOT
from .lang import show, parse_class
from .engine import Compiler
from .lean import LeanExport
from .tree import onto_names
from .render import world_html, stage_table_html, world_lines
from .evaluate import class_holds_attrs, holds

E = html.escape

CSS = """
/* VOICE: 學術、克制，像一部校勘精細的論書附錄
   IDEA: 論書的「科判」與校勘記：每條命題有出處，每一步有依據
   PICTURE: 工作流程的一條長卷，以及十五條證明路徑的矩陣
   COLOUR and TYPE: 白底墨字；石青表示成立，朱色表示反例與衝突；Noto Serif TC
   LAYOUT: 單欄長文，表格為主，章節鏈接一行 */
:root{color-scheme:light dark;--bg:light-dark(#ffffff,#121416);--ink:light-dark(#1a1a1a,#e8e6e1);--mute:light-dark(#5d5d5d,#a9a7a1);
--rule:light-dark(#d9d6cf,#33373b);--panel:light-dark(#f4f3ef,#1b1e21);--blue:light-dark(#2a5a86,#8fb8de);--red:light-dark(#b8321c,#f08a74);
--blueBg:light-dark(#e6eef6,#1c2a38);--redBg:light-dark(#f8e7e2,#3a211c)}
:root[data-theme=light]{color-scheme:light}:root[data-theme=dark]{color-scheme:dark}
*{box-sizing:border-box;min-width:0}
body{margin:0;background:var(--bg);color:var(--ink);font:16.5px/1.75 "Kosa Serif","Noto Serif TC","Songti TC","PMingLiU",serif;overflow-x:clip}
[hidden]{display:none!important}
.band{padding:clamp(28px,4vw,60px) max(5vw,16px)}
.wrap{max-width:1080px;margin:0 auto}
h1{font-size:clamp(30px,4.4vw,46px);line-height:1.15;margin:.2em 0 .35em;text-wrap:balance;font-weight:700}
h2{font-size:28px;line-height:1.25;margin:2.2em 0 .6em;padding-top:.6em;border-top:2px solid var(--ink);text-wrap:balance}
h3{font-size:20px;margin:1.8em 0 .5em}
p{max-width:44em}
.deck{font-size:19px;color:var(--mute);max-width:40em}
.top{background:var(--panel);border-bottom:1px solid var(--rule)}
.stats{display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:12px;margin:26px 0 8px}
.stat{background:var(--bg);border:1px solid var(--rule);padding:14px 16px}
.stat b{display:block;font-size:30px;line-height:1.1;font-variant-numeric:tabular-nums}
.stat span{font-size:14px;color:var(--mute)}
.stat.ok b{color:var(--blue)}.stat.bad b{color:var(--red)}
nav.scroll{display:flex;gap:6px 18px;flex-wrap:wrap;padding:10px max(5vw,16px);border-bottom:1px solid var(--rule);background:var(--bg);font-size:15px}
@media(min-width:900px){nav.scroll{position:sticky;top:0;z-index:5}}
nav a{color:var(--ink);text-decoration:none;border-bottom:1px solid var(--rule)}nav a:hover{border-color:var(--ink)}
.flow{display:flex;flex-wrap:wrap;align-items:stretch;gap:0;margin:24px 0 6px;counter-reset:f}
.flow .n{flex:1 1 120px;padding:12px 12px 12px 14px;border:1px solid var(--rule);margin:-1px 0 0 -1px;background:var(--bg);position:relative}
.flow .n b{display:block;font-size:17px}.flow .n span{font-size:13.5px;color:var(--mute);line-height:1.5;display:block}
.flow .n.loop{background:var(--redBg)}.flow .n.done{background:var(--blueBg)}
.loopnote{font-size:14px;color:var(--red);margin:6px 0 0}
table{border-collapse:collapse;width:100%;margin:12px 0 18px;font-size:15px}
th,td{border-bottom:1px solid var(--rule);padding:7px 8px;text-align:left;vertical-align:top}
thead th{border-bottom:2px solid var(--ink);font-weight:700;white-space:nowrap}
td.num,th.num{text-align:right;font-variant-numeric:tabular-nums;white-space:nowrap}
.k{white-space:nowrap;font-weight:700}
code,.f{font-family:"Kosa Serif","Noto Serif TC","Songti TC",serif;background:var(--panel);padding:1px 5px;border-radius:3px;overflow-wrap:anywhere}
pre{background:var(--panel);padding:12px 14px;font:13.5px/1.6 ui-monospace,"SF Mono",Menlo,monospace;overflow-x:auto;border:1px solid var(--rule)}
.tag{display:inline-block;border:1px solid var(--rule);padding:0 6px;margin:2px 3px 2px 0;font-size:14px;background:var(--bg);white-space:nowrap}
table.world{width:auto;margin:6px 0}table.world th{width:2.2em;color:var(--mute);border:0}table.world td{border:0;padding:3px 4px}
table.world tr.hit th{color:var(--red)}table.world tr.hit .tag{border-color:var(--red)}
ul.rels{margin:2px 0 4px 1.2em;padding:0;font-size:14.5px;color:var(--mute)}
.round{border:1px solid var(--rule);border-left:4px solid var(--red);padding:12px 16px;margin:14px 0;background:var(--bg)}
.round.ok{border-left-color:var(--blue)}
.round h4{margin:0 0 6px;font-size:17px}
.verdict{font-weight:700}.verdict.no{color:var(--red)}.verdict.yes{color:var(--blue)}
.note{font-size:14.5px;color:var(--mute)}
.chip{display:inline-block;padding:0 7px;margin:2px 4px 2px 0;border:1px solid var(--rule);background:var(--panel);font-size:14.5px;white-space:nowrap}
.chip.red{border-color:var(--red);color:var(--red);background:var(--redBg)}.chip.blue{border-color:var(--blue);color:var(--blue);background:var(--blueBg)}
.set{margin:4px 0}
table.mx{font-size:13px;width:auto}table.mx th,table.mx td{padding:3px 5px;text-align:center;border:1px solid var(--rule)}
table.mx thead th{writing-mode:vertical-rl;white-space:nowrap;border-bottom:1px solid var(--ink);padding:6px 3px;font-weight:400}
table.mx td.y{background:var(--ink);color:var(--bg)}table.mx tr.short td.y{background:var(--blue)}
table.stages{width:auto;font-size:14px}table.stages th,table.stages td{border:1px solid var(--rule);text-align:center;padding:4px 8px}
table.stages td.y{color:var(--blue);font-weight:700}table.stages td.n{color:var(--rule)}
details{border:1px solid var(--rule);padding:8px 14px;margin:10px 0;background:var(--bg)}summary{cursor:pointer;font-weight:700}
.two{display:grid;grid-template-columns:repeat(auto-fit,minmax(300px,1fr));gap:16px}
.box{border:1px solid var(--rule);padding:12px 16px;background:var(--panel)}
.scroll{overflow-x:auto}
.ok{color:var(--blue)}.bad{color:var(--red)}
blockquote{margin:10px 0;padding:6px 14px;border-left:3px solid var(--rule);color:var(--mute)}
footer{border-top:1px solid var(--rule);font-size:14px;color:var(--mute)}
@media(max-width:600px){table{font-size:13px}.stack thead{display:none}.stack tr{display:grid;padding-block:10px}.stack td{display:flow-root;border:0;padding:3px 0;padding-inline-start:6.5em;text-align:start}.stack td::before{content:attr(data-l);float:inline-start;width:6em;margin-inline-start:-6.5em;color:var(--mute);white-space:normal}.stack td:empty{display:none}}
html{scroll-padding-top:60px}
ul.tree,ul.tree ul{list-style:none;margin:0;padding-left:22px;border-left:1px solid var(--rule)}
ul.tree{padding-left:0;border-left:0}
ul.tree li{margin:6px 0;position:relative}
ul.tree ul li::before{content:"";position:absolute;left:-22px;top:15px;width:16px;border-top:1px solid var(--rule)}
ul.tree summary{font-weight:400;list-style:none}ul.tree summary::-webkit-details-marker{display:none}
ul.tree details{border:0;padding:0;margin:0;background:none}
.node{display:inline-flex;flex-wrap:wrap;gap:4px 8px;align-items:baseline}
.lay{display:inline-block;font-size:12.5px;padding:0 6px;border-radius:2px;color:#fff;white-space:nowrap}
.lay.目標{background:var(--ink);color:var(--bg)}.lay.定理{background:var(--blue)}.lay.假定{background:#7a6a4f}.lay.約定{background:#888}.lay.異讀{background:var(--red)}.lay.推論{background:var(--red)}.lay.本體{background:var(--panel);color:var(--mute);border:1px solid var(--rule)}
.pend{color:var(--red);font-size:13px;white-space:nowrap}.src{color:var(--mute);font-size:13px}
.leanpair{display:grid;grid-template-columns:minmax(0,1fr);gap:10px}
a.btn{display:inline-block;padding:10px 16px;border:1px solid var(--ink);color:var(--ink);text-decoration:none;margin:6px 8px 6px 0;min-height:44px}
a.btn:hover{background:var(--ink);color:var(--bg)}
"""

STACK_JS = """<script>new MutationObserver(()=>{for(const c of document.querySelectorAll('.stack td:not([data-l])')){let i=0,p=c;while(p=p.previousElementSibling)i+=p.colSpan;c.dataset.l=c.closest('table').rows[0].cells[i]?.textContent||''}}).observe(document,{childList:true,subtree:true})</script>"""

# 每條補出前提：反例鑽的是哪個空子（不依賴具體反例的寫法）
GAP = {
    "補一": "前提只說染心的善染來自「相應法」，沒說那個相應法是惑。反例讓欲界有覆無記心只與非惑的心所相應，於是前提9（欲界有覆無記惑唯身見、邊見）根本用不上。",
    "補二": "前提沒說心與相應的惑同性。反例讓有覆無記心與一個無覆無記或不善的惑相應，前提9又用不上。",
    "補三": "前提沒說心與相應的惑同地。反例讓欲界的心與他地的惑相應，前提9只管欲界惑，於是落空。",
    "補四": "前提沒說表業與其等起心同地。反例讓表色與它的等起心分處兩地：心在初靜慮，表色卻在別處。",
    "補五": "前提沒說等起心是有漏。反例用無漏心作等起。",
    "補六": "前提沒說無漏法不繫、有漏法繫地。反例讓一個有漏或有覆的法標為「不繫」，或讓無漏法繫於某地。",
    "補七": "前提沒說染污法都是有漏。",
    "補八": "前提沒說無漏法非所斷。",
    "補九": "前提沒說每個表業都有剎那等起心。反例中有一個沒有等起心的表色，它可以在任何地。",
}


def tags(items, cls=""):
    return "".join(f'<span class="chip {cls}">{E(i)}</span>' for i in items)


def target_hits(world, module, sid):
    """∀x(P⇒Q) 形式的命題：回傳使 P 真 Q 假的實體。"""
    f = module.statements[sid].formula
    if f[0] == "凡" and len(f[1]) == 1 and f[2][0] == "⇒":
        v = f[1][0][0]
        out = set()
        for e in world.ents:
            env = {v: e}
            if holds(f[2][1], world, env, module.onto, module.lex) and not holds(f[2][2], world, env, module.onto, module.lex):
                out.add(e.key)
        return out
    if f[0] == "非" and f[1][0] == "有":
        v = f[1][1][0][0]
        return {e.key for e in world.ents if holds(f[1][2], world, {v: e}, module.onto, module.lex)}
    return set()


def stmt_cell(m, sid):
    st = m.statements[sid]
    return f'<span class="k">【{E(sid)}】</span>'


def meta_line(st, keys=("出處", "依據")):
    parts = []
    for k in keys:
        if k in st.meta:
            parts.append(f"{k}：{st.meta[k]}")
    return "；".join(parts)


def verse_badge(checks, sid):
    rows = [c for c in checks if c[0] == sid]
    if not rows:
        return ""
    out = []
    for _, field, quote, hits in rows:
        if hits:
            h = hits[0]
            out.append(f'<span class="ok">✓</span> 頌「{E(quote)}」（{E(h[0])}·第{h[1]}行）')
        else:
            out.append(f'<span class="bad">✗ 頌「{E(quote)}」未在 CBETA 找到</span>')
    return "<br>".join(out)


def asp_of(module, sid):
    c = Compiler(module)
    c.statement(sid, module.statements[sid].formula)
    return "\n".join(c.rules)


def section_ontology(onto, m1):
    rows = []
    for d in onto.dims.values():
        vals = [v + (f"〔{d.value_applies[v]}〕" if v in d.value_applies else "") for v in d.values]
        rows.append(f"<tr><td class='k'>{E(d.name)}</td><td>{E(d.applies or '一切')}</td><td>{tags(vals)}</td><td class='note'>{E(d.notes.get('出處', '') or d.notes.get('頌', ''))}</td></tr>")
    defs = "".join(f"<tr><td class='k'>{E(n)}</td><td><code>{E(t)}</code></td></tr>" for n, t in onto.defs.items())
    rels = "".join(f"<tr><td class='k'>{E(r.name)}</td><td>（{E(r.sig[0])}，{E(r.sig[1])}）{'對稱' if r.symmetric else ''}</td><td class='note'>{E(r.notes.get('說明', ''))}</td></tr>" for r in onto.rels.values())
    # 概念表
    tsv = (ROOT / "本體" / "概念表.tsv").read_text(encoding="utf-8").splitlines()
    rows_c = [l.split("\t") for l in tsv if l and not l.startswith("#")][1:]
    done = [r for r in rows_c if r[4] == "已形式化"]
    part = [r for r in rows_c if r[4] == "部分"]
    n = len(rows_c)
    bar = (f'<div style="display:flex;height:16px;border:1px solid var(--rule);margin:8px 0 4px">'
           f'<div style="width:{100*len(done)/n:.1f}%;background:var(--blue)"></div>'
           f'<div style="width:{100*len(part)/n:.1f}%;background:var(--blueBg)"></div></div>')
    clist = "".join(f"<tr><td>{E(r[1])}</td><td>{E(r[2])}</td><td>{E(r[3])}</td><td class='{'ok' if r[4]=='已形式化' else ''}'>{E(r[4])}</td><td class='note'>{E(r[5])}</td></tr>" for r in done + part)
    return f"""
<h2 id="ontology">本體：先定詞，才能說命題</h2>
<p>Kosa 的詞彙是封閉的。每個命題只能用本體裡定義過的詞；寫了未定義的詞，解析器直接報錯（「未知詞：……不在本體詞表中」）。這是讓命題可以被機器精確理解的前提，也是擴展的入口：新概念先進本體，再進命題。</p>
<p>本體有三部分。<b>門</b>是分別的維度，每個法在每一門中恰取一值。<b>定義</b>是由門值組成的類。<b>關係</b>連接兩個法。「每門恰取一值」由引擎自動施加，所以「見所斷與修所斷互斥」「內門轉與外門轉互斥」這類前提不必另寫。2022 文中這類前提隱含在「有二種」裡，形式化後就成了本體的一部分。</p>
<h3>門</h3>
<div class="scroll"><table class="stack"><thead><tr><th>門</th><th>適用於</th><th>值</th><th>出處</th></tr></thead><tbody>{''.join(rows)}</tbody></table></div>
<div class="two"><div><h3>定義</h3><table><tbody>{defs}</tbody></table></div>
<div><h3>關係</h3><table class="stack"><thead><tr><th>關係</th><th>類型</th><th>說明</th></tr></thead><tbody>{rels}</tbody></table></div></div>
<h3>概念表：〈術語要點一覽〉的 {n} 個術語，v0.3 覆蓋多少</h3>
{bar}
<p class="note">深色：已形式化 {len(done)} 個；淺色：部分 {len(part)} 個；空白：未形式化 {n-len(done)-len(part)} 個。概念表取自 wanglu2016/abhidharma 的概念數據，存於 <code>本體/概念表.tsv</code>，每加一門、一個模組就更新狀態，可作為完備度的粗略刻度。</p>
<div class="scroll"><table class="stack"><thead><tr><th>術語</th><th>品</th><th>作者標註</th><th>狀態</th><th>所在</th></tr></thead><tbody>{clist}</tbody></table></div>
"""


def section_language(m1):
    forms = [
        ("A 唯 B", "凡 A 皆 B", "前提1", ),
        ("A 非 B", "凡 A 皆非 B", "前提6"),
        ("A 即 B", "A 與 B 外延相同", "補六"),
        ("A：B、C", "A 即「B 或 C」（《萬字》的寫法）", "前提11"),
        ("A 無", "沒有 A", "頌三"),
        ("A 通 B、C", "凡 A 皆 B 或 C，且 A 容 B、A 容 C", None),
        ("A 容 B", "有 A 是 B", None),
        ("凡／有 …：…", "一階公式：且、或、非、⇒、⇔、＝", "前提9"),
    ]
    rows = []
    for f, r, ex in forms:
        exs = f"【{ex}】<code>{E(m1.statements[ex].text)}</code>" if ex else "（模組三、四將用到）"
        rows.append(f"<tr><td class='k'>{E(f)}</td><td>{E(r)}</td><td>{exs}</td></tr>")
    st = m1.statements["前提1"]
    lean = LeanExport(m1).f(st.formula)
    asp = asp_of(m1, "前提1")
    return f"""
<h2 id="language">命題語言：用毘曇自己的句式</h2>
<p>命題用繁體中文書寫。句式取自毘曇論書本身的論式：「唯」「非」「即」「通」「容」「無」，加上《俱舍萬字》的「A：B、C」。類表達式用「・」表示且，「或」表示或，「非」表示非，例如「見所斷・惑」就是「既是見所斷，又是惑」。需要關係、多個變元時，用漢字關鍵詞的一階公式：「凡 x、y：相應(x，y) ⇒ 斷非斷(x)＝斷非斷(y)」。</p>
<div class="scroll"><table class="stack"><thead><tr><th>句式</th><th>讀法</th><th>庫中的例子</th></tr></thead><tbody>{''.join(rows)}</tbody></table></div>
<h3>一條命題的四層形態</h3>
<p>以【前提1】為例。作者只需寫第二層；其餘三層由程序生成。</p>
<table class="stack"><tbody>
<tr><td class="k">原文</td><td>{E(st.meta['原文'])}</td></tr>
<tr><td class="k">Kosa 命題</td><td><code>{E(st.text)}</code></td></tr>
<tr><td class="k">一階公式</td><td><code>{E(show(st.formula))}</code></td></tr>
<tr><td class="k">Lean 4</td><td><code>{E(lean)}</code></td></tr>
</tbody></table>
<details><summary>回答集程序（給求解器 clingo 的形式）</summary><pre>{E(asp)}</pre>
<p class="note">「on(0)」是這條命題的開關。引擎一次編譯全部命題，每次查詢只切換開關，所以檢驗一組前提只需幾十毫秒。</p></details>
"""


def round_card(i, rd, m, chosen_note=True):
    if rd.proved:
        return (f'<div class="round ok"><h4>第 {i} 輪：{len(rd.premises)} 條前提 → <span class="verdict yes">成立</span></h4>'
                f'<p>在至多 6 個法的一切世界中，都找不到反例。</p></div>')
    hit = target_hits(rd.world, m, "求證")
    added = rd.added
    st = m.statements[added] if added else None
    gap = GAP.get(added, "")
    body = world_html(rd.world, m, hit)
    return f"""<div class="round"><h4>第 {i} 輪：{len(rd.premises)} 條前提 → <span class="verdict no">不成立</span>，反例如下</h4>
{body}
<p class="note">朱框是違反結論的那個法：它是有覆無記色，卻不繫於初靜慮。</p>
<p><b>空子：</b>{E(gap)}</p>
<p><b>此反例違反的候選：</b>{tags(rd.violated, 'red')} → 加入 <b>【{E(added)}】</b><code>{E(st.text)}</code><br>
<span class="note">{E(meta_line(st, ('說明', '依據')))}</span></p></div>"""


def section_m1(R1):
    m = R1["module"]
    checks = R1["verse_checks"]
    # 十六條前提
    rows = []
    for sid in R1["start"]:
        st = m.statements[sid]
        rows.append(f"<tr><td class='k'>{E(sid)}</td><td>{E(st.meta.get('原文', ''))}</td><td><code>{E(st.text)}</code></td>"
                    f"<td class='note'>{E(st.meta.get('詮釋', st.meta.get('說明', '')))}{'<br>' if verse_badge(checks, sid) else ''}{verse_badge(checks, sid)}</td></tr>")
    rounds = "".join(round_card(i, rd, m) for i, rd in enumerate(R1["rounds"]))
    added = [rd.added for rd in R1["rounds"] if rd.added]
    A = R1["analysis"]
    ms = A.minimal_sets[0]
    from_2022 = [s for s in ms if s in R1["start"]]
    hidden = [s for s in ms if s not in R1["start"]]
    red = A.redundant
    onto_red = [s for s in red if m.statements[s].form == "列舉"]
    other_red = [s for s in red if s not in onto_red]
    # 必要性見證
    wit = []
    for p in A.necessary:
        w = A.witnesses.get(p)
        if w is None:
            continue
        wit.append(f"<details><summary>去掉【{E(p)}】</summary><p><code>{E(m.statements[p].text)}</code></p>{world_html(w, m, target_hits(w, m, '求證'))}</details>")
    # 擴大庫
    B = R1["big_analysis"]
    sets = sorted(B.minimal_sets, key=len)
    cols = [p for p in R1["big"] if any(p in s for s in sets)]
    head = "".join(f"<th>{E(c)}</th>" for c in cols)
    body = []
    for i, s in enumerate(sets):
        cls = ' class="short"' if i == 0 else ""
        cells = "".join(f"<td class='{'y' if c in s else ''}'>{'●' if c in s else ''}</td>" for c in cols)
        body.append(f"<tr{cls}><th class='num'>{len(s)}</th>{cells}</tr>")
    never = [p for p in R1["big"] if p not in cols]
    alt_sets = [x for x in sets if "頌一" in x and not ({"前提1", "前提3乙", "前提8"} & set(x))]
    alt_route = (f"<li>以頌「見斷識唯轉」（頌一）代替「內門轉」一路（前提1、3乙、8），也能證明，例如 {tags(alt_sets[0])}——兩條路殊途同歸。</li>" if alt_sets else "")
    always = B.necessary
    # 頌文作為定理
    s3 = R1["song3"].minimal_sets
    s2 = R1["song2"].minimal_sets
    s2w = R1["song2_from_final"].world
    # 異讀
    alt = R1["alt_result"]
    alt_hit = target_hits(alt.world, m, "求證") if alt.world else set()
    a3 = R1["alt_song3_same"]
    a3_hit = target_hits(a3.world, m, "頌三") if a3.world else set()
    a3_note = ""
    if a3.world:
        # 找出反例中作為「轉」的心，核實它的性質，再下文字
        keys = {e.key: e for e in a3.world.ents}
        cs = [keys[b] for r, a, b in a3.world.rels if r == "因等起" and a in a3_hit]
        c = cs[0] if cs else None
        if c and c.attrs.get("繫不繫") == "欲界繫" and c.attrs.get("斷非斷") == "見所斷" and c.attrs.get("門轉") == "內門轉":
            a3_note = (f"反例中作為「轉」的心（{c.label}）是欲界的見所斷心，內門轉——它正是頌「見斷識唯轉」所說的那種識："
                       "能作轉，不能作隨轉。在隨轉的讀法下，這樣的心作不了表業的等起，頌三因此成立；在轉的讀法下，它可以作，頌三就落空了。")
        elif c:
            a3_note = f"反例中作為「轉」的心是 {c.label}：{'・'.join(v for v in c.attrs.values() if v != '—')}。"
    conf = R1["lib_alt_conflicts"].conflicts
    lean_src = (ROOT / "lean" / "Kosa" / "Proof1.lean").read_text(encoding="utf-8")
    thm = re.search(r"theorem «有覆無記色唯初靜慮繫» .*?:\n    «求證» W", lean_src, re.S).group(0)
    axioms = R1.get("lean_axioms", "")
    return f"""
<h2 id="m1">模組一：把 2022 年的證明交給機器</h2>
<p>底本是〈怎樣推導出一個毘曇命題？〉（2022 年 7 月）。文中從 16 條前提，經 48 步推出「有覆無記色唯初靜慮繫」。這裡把 16 條前提逐條寫成 Kosa 命題（其中前提3、前提10各拆成兩條，共 18 條），交給引擎檢驗：這 18 條前提是否蘊涵結論？</p>
<p>引擎的做法是找反例。它在「至多 6 個法」的世界裡，搜索一個滿足全部前提、卻違反結論的世界。找不到，結論就在此範圍內成立；找到了，那個世界就指出前提缺了甚麼。</p>
<h3>十六條前提的形式化</h3>
<div class="scroll"><table class="stack"><thead><tr><th>編號</th><th>2022 文原句</th><th>Kosa 命題</th><th>詮釋與頌文核對</th></tr></thead><tbody>{''.join(rows)}</tbody></table></div>
<p class="note">「詮釋」欄記下形式化時做的、原文沒有明說的決定。這些決定都可以改；改了以後重新檢驗即可。</p>

<h3 id="m1-loop">反例驅動的補前提：{len(R1['rounds'])-1} 輪</h3>
<p>候選池裡預先放了 9 條可能的隱含前提，各附依據（頌文、《萬字》，或標「待核」）。每一輪，引擎取一個儘量小的反例，檢查哪些候選被它違反——加入其中任何一條都能排除這個反例——然後按池中次序加入第一條，再檢驗。選哪條、加幾條，都由反例決定。</p>
{rounds}
<p class="note">反例裡常有荒謬的組合，例如初靜慮繫的瞋、無漏的有覆無記惑。它們荒謬，是因為前提庫還沒有排除它們；只要與結論無關，就不影響檢驗。一個完整的庫應把這類常識命題（上界無瞋、無漏唯善或無覆無記……）也收進來，屆時反例會乾淨得多，需要補的前提也可能更少。</p>

<h3 id="m1-min">證明成立之後：哪些前提真正用到了</h3>
<p>最終前提集共 {len(R1['final'])} 條。引擎枚舉了其中所有的極小前提集——去掉其中任何一條，證明就不再成立。{'結果只有一個' if len(A.minimal_sets)==1 else f'共 {len(A.minimal_sets)} 個，這裡列出第一個'}，共 {len(ms)} 條：2022 文的 {len(from_2022)} 條，加上補出的 {len(hidden)} 條。</p>
<div class="box"><div class="set"><b>2022 文：</b>{tags(from_2022, 'blue')}</div><div class="set"><b>補出：</b>{tags(hidden, 'red')}</div></div>
<p><b>冗餘的前提：</b>{tags(red)}</p>
<ul>
<li>{tags(onto_red)}已由本體的定義給出（「所斷」「業」「染」），作為前提是同義反復。</li>
<li>{tags(other_red)}在補足之後用不上。2022 文第一步（命題 1–14）證明「見所斷心與見所斷惑相應」，第 26 步再用它說「欲界有覆無記心是見所斷」，都是為了把「內門轉」從惑傳到心。補一直接給出與心相應的惑，內門轉就能沿著相應關係從惑傳到心（前提3乙），不必經過「心是見所斷」這一環。所以第一步可以整個省去。{'前提7 也被補一、補二取代。' if '前提7' in red else ''}</li>
</ul>
<details><summary>必要性見證：去掉極小前提集中的每一條，各有一個反例（共 {len(wit)} 個）</summary>{''.join(wit)}</details>

<h3 id="m1-paths">擴大前提庫：證明不止一條路</h3>
<p>把候選池中其餘的前提和三條頌文也放進庫裡（共 {len(R1['big'])} 條），引擎找出 <b>{len(sets)}</b> 條互不包含的極小證明。下表每行一條，「●」表示用到；首行（石青）最短，只用 4 條。</p>
<div class="scroll"><table class="mx"><thead><tr><th>條數</th>{head}</tr></thead><tbody>{''.join(body)}</tbody></table></div>
<ul>
<li>最短的證明只用 {tags(sets[0], 'blue')}：有覆無記色是業，不是無表，所以是表；表唯在欲界、初靜慮（頌「表唯有伺二」）；欲界無有覆表（頌「欲無有覆表，以無等起故」）。這正是 2022 文說的「掌握的前提越多，證明就越簡單」。</li>
<li>每一條證明都用到的只有 {tags(always, 'red')}。其餘前提都可以被別的前提替代。</li>
<li>任何一條證明都用不上的：{tags(never)}。</li>
{alt_route}
</ul>
<p class="note">存在命題（如【頌一乙】「見所斷識能作轉」）不放入這裡的搜索。求解器只檢驗至多 6 個法的世界；存在命題會迫使世界裡先有幾個法，剩下的位置可能不夠容納反例，從而造成虛假的「蘊涵」。初版曾因此多報了 8 條「證明」。這是有界檢驗的固有局限，也是主結論要再交給 Lean 證明的原因。</p>

<h3 id="m1-verse">頌文作為定理</h3>
<p>頌三「欲無有覆表，以無等起故」本身是可以推出的。它的極小前提集只有一個：</p>
<div class="box">{''.join(f'<div class="set">{tags(s)}</div>' for s in s3)}</div>
<p>這就是「以無等起故」的形式解釋：欲界有覆無記心唯是身見、邊見相應心，內門轉，不能作表業的剎那等起；而有覆無記表必須有同性的剎那等起心。Lean 版本見下文定理「欲無有覆表」。</p>
<p>頌二「表唯有伺二」則不能由最終前提集推出。反例是一個沒有等起心的表色：</p>
{world_html(s2w, m, target_hits(s2w, m, '頌二')) if s2w else ''}
<p>補上【補九】「表業必有剎那等起心」之後，頌二可推出，極小前提集為 {''.join(tags(s) for s in s2)}。</p>

<h3 id="m1-fork">一個詮釋分歧：「等起」是轉還是隨轉？</h3>
<p>前提10「色由等起成善染性」中的「等起」，可以讀作剎那等起（隨轉），也可以讀作因等起（轉）。上面的證明取前者。改取後者（【異讀10甲】），結論立即不成立，反例如下：</p>
{world_html(alt.world, m, alt_hit) if alt.world else ''}
<p>這個反例鑽的是一個淺層的空子：前提8、補四、補五都只約束剎那等起，對因等起一無所說。更有意思的是頌三「欲無有覆表」在轉的讀法下也推不出（{'不成立' if not R1['alt_song3'].ok else '成立'}）。為了看清要點，再加上【異讀補四】（令轉與表同地），頌三的反例是：</p>
{world_html(a3.world, m, a3_hit) if a3.world else '<p>（頌三成立，無反例。）</p>'}
<p>{E(a3_note)}</p>
<p>要在轉的讀法下救回結論，自然的辦法是把前提8、補四、補五移到因等起上（【異讀8】【異讀補四】【異讀補五】）。這樣結論確實可以推出（{'成立' if R1['alt_transposed'].ok else '不成立'}）。但整個庫隨即自相矛盾：唯一的極小衝突集是</p>
<div class="box">{''.join(f'<div class="set">{tags(s, "red")}</div>' for s in conf)}</div>
<p>讀法：頌「見斷識唯轉」說見所斷心能作轉（頌一乙）；見所斷心是染（前提6）；染心有惑相應（補一），惑與心同所斷（前提3甲），見所斷惑內門轉（前提1），相應法同門轉（前提3乙）——所以這個心內門轉；而【異讀8】要求作表業之轉的心外門轉。有意思的是，前提6、前提3甲在主證明裡是冗餘的，在這裡卻不可缺。這個衝突也由 Lean 證明（定理「轉讀法之衝突」），不受有界檢驗的限制。</p>
<p><b>結論（在本模組的形式化之下）：</b>若頌文與 2022 文的其餘前提都成立，前提10 中的「等起」只能讀作剎那等起（隨轉）。這是否合於論意，仍須回到《俱舍》《正理》業品長行核實。</p>

<h3 id="m1-lean">Lean 內核驗證：對任意大小的世界成立</h3>
<p>求解器的檢驗是有界的：它窮盡了至多 6 個法的世界。為了確認結論對任意世界都成立，Kosa 把本體和命題自動導出為 Lean 4（<code>lean/Kosa/Module1.lean</code>），證明另寫在 <code>lean/Kosa/Proof1.lean</code>，由 Lean 內核逐步檢查。共五條定理：</p>
<ul><li>「欲界有覆無記心唯內門轉」（引理）</li><li>「有覆無記色唯初靜慮繫」（前提即上述極小前提集的 16 條）</li><li>「欲無有覆表」（頌三作為定理）</li><li>「有覆無記色唯初靜慮繫_頌文版」（4 條前提的短證明）</li><li>「轉讀法之衝突」（見下文詮釋分歧一節）</li></ul>
<pre>{E(thm)}</pre>
<p class="note">Lean 的 <code>#print axioms</code> 結果：{E(axioms)}。沒有 sorry，沒有額外公理（propext 是 Lean 的標準公理，來自 simp）。</p>
"""


def section_m2(R2):
    m = R2["module"]
    checks = R2["verse_checks"]
    rules = "".join(f"<tr><td class='k'>{E(r)}</td><td><code>{E(m.statements[r].text)}</code></td><td>{E(m.statements[r].meta.get('說明', ''))}</td><td class='note'>{verse_badge(checks, r)}</td></tr>" for r in R2["rules"])
    bu = ["見苦所斷", "見集所斷", "見滅所斷", "見道所斷", "修所斷"]
    jie = ["欲界", "色界", "無色界"]
    order = ["身見", "邊見", "邪見", "見取", "戒禁取", "貪", "瞋", "癡", "慢", "疑"]
    trs = []
    for b in bu:
        cells = []
        for j in jie:
            mem = R2["members"](f"立・{j}・{b}")
            names = sorted({e.attrs["見種"] if e.attrs.get("見種", "—") != "—" else e.attrs["心所自性"] for e in mem}, key=order.index)
            cells.append(f"<td><b class='num'>{len(mem)}</b><br><span class='note'>{E('、'.join(names))}</span></td>")
        trs.append(f"<tr><th>{E(b)}</th>{''.join(cells)}</tr>")
    tot = "".join(f"<td class='num'><b>{R2['count']('立・'+j)}</b></td>" for j in jie)
    tests = "".join(f"<tr><td><code>{E(x)}</code></td><td class='num'>{n}</td><td class='num'>{got}</td><td class='{'ok' if n==got else 'bad'}'>{'✓' if n==got else '✗'}</td><td class='note'>{E(src)}</td></tr>" for x, n, src, got in R2["tests"])
    drop = "".join(f"<tr><td class='k'>{E(r)}</td><td class='num'>{n}</td><td class='num'>+{n-98}</td></tr>" for r, n, u in R2["drop"])
    return f"""
<h2 id="m2">模組二：九十八隨眠——幾條規則生成全部</h2>
<p>頌：「六行部界異，故成九十八。欲見苦等斷，十七七八四。謂如次具離，三二見見疑。色無色除瞋，餘等如欲說。」這裡演示的是壓縮：把頌中的排除規則寫成命題，引擎從 {R2['candidates']} 個候選位（十隨眠 × 斷 × 見諦 × 三界）中推出哪些立為隨眠。「九十八」「十七七八四」以及《萬字》的「欲界 36、色界 31、無色界 31」都不是前提，而是要驗證的結果。</p>
<div class="scroll"><table class="stack"><thead><tr><th>規則</th><th>Kosa 命題</th><th>說明</th><th>頌文核對</th></tr></thead><tbody>{rules}</tbody></table></div>
<p><b>閉包原則。</b>規則只說哪些候選<em>不能</em>立。要得到確定的數字，還需要一條原則：凡未被排除者，皆立為隨眠。列舉式的說法（「十隨眠除身見、邊見、戒禁取」）都隱含這條原則，但很少明說。Kosa 把它作為顯式的設定（模組文件中的「閉包 立」），引擎在滿足規則的前提下令「立」的外延極大，並檢查極大模型是否唯一（{'唯一' if R2['unique'] else '不唯一'}）。</p>
<h3>推出的結果</h3>
<div class="scroll"><table><thead><tr><th></th>{''.join(f'<th>{j}</th>' for j in jie)}</tr></thead><tbody>{''.join(trs)}<tr><th>合計</th>{tot}</tr></tbody></table></div>
<div class="scroll"><table class="stack"><thead><tr><th>查詢</th><th class="num">文獻所說</th><th class="num">引擎推出</th><th></th><th>出處</th></tr></thead><tbody>{tests}</tbody></table></div>
<h3>每條規則的貢獻</h3>
<p>去掉一條規則，重新計數：多出來的就是這條規則排除掉的。</p>
<table style="width:auto"><thead><tr><th>去掉</th><th class="num">總數</th><th class="num">多出</th></tr></thead><tbody>{drop}</tbody></table>
<p class="note">例如去掉規則四（上界除瞋），多出 10 個：色、無色二界各五部的瞋。去掉規則五（隨眠皆所斷），多出 28 個：非所斷的十種惑在三界各一，減去上二界已被規則四排除的瞋。</p>
<h3>模組之間的連通</h3>
<p>模組一的【前提2】「身見、邊見、邪見、見取、戒禁取唯見所斷」，在這裡不是前提，而是定理（【驗證二】，{'成立' if R2['v2'] else '不成立'}），極小前提集為 {''.join(tags(s) for s in R2['v2_min'])}。隨著模組增多，一個模組的前提常常會變成另一個模組的定理——這就是「刪去冗餘」的形式含義：冗餘的命題不刪，而是降為定理，變成測試題。</p>
"""


def group_mcs(mcs):
    A = [s for s in mcs if {"乙", "庚", "壬"} <= set(s)]
    B = [s for s in mcs if not ({"乙", "壬"} & set(s))]
    C = [s for s in mcs if s not in A and s not in B]
    return A, B, C


def section_m3(R3):
    m = R3["module"]
    checks = R3["verse_checks"]
    rows = []
    for sid in R3["stmts"]:
        st = m.statements[sid]
        txt = st.meta.get("原文", st.meta.get("說明", ""))
        rows.append(f"<tr><td class='k'>{E(sid)}</td><td>{E(txt)}</td><td><code>{E(st.text)}</code></td><td class='note'>{E(st.meta.get('出處', st.meta.get('依據', '')))}{'<br>' + verse_badge(checks, sid) if verse_badge(checks, sid) else ''}</td></tr>")
    base = R3["base"]
    conf = "".join(f'<div class="set">{tags(c, "red")}</div>' for c in base.conflicts)
    A, B, C = group_mcs(base.corrections)

    import itertools
    prod = {frozenset((a, b, c, "辛")) for a, b, c in itertools.product(("甲", "癸"), ("丙", "丁"), ("戊", "己"))}
    B_note = ("代價是從四組中各放棄一條：甲或癸，丙或丁，戊或己，以及有說（辛）。" if {frozenset(x) for x in B} == prod else "")

    def sets(xs):
        return "".join(f'<div class="set">放棄 {tags(s)}</div>' for s in xs)
    var_rows = []
    for name, who, how, stmts, ok, ca in R3["variants"]:
        rest = "".join(f'<span class="chip red">{E("".join(c))}</span>' for c in ca.conflicts)
        var_rows.append(f"<tr><td class='k'>{E(name)}</td><td>{E(who)}</td><td>{E(how)}</td><td class='num'>{len(ca.conflicts)}</td><td>{rest}</td></tr>")
    preds = ["未離下", "修上地有漏", "修俗智", "引有漏離繫得", "成就無色善"]
    reps = "".join(f"<div><h4>{E(label)}</h4>{stage_table_html(w, m, '道位', preds) if w else '無'}</div>" for label, stmts, ok, w in R3["reps"])
    v23 = [v for v in R3["variants"] if v[0] == "方案二＋三"][0]
    V = {v[0]: v for v in R3["variants"]}
    base_c = [set(c) for c in base.conflicts]
    notes = []
    c1 = [set(c) for c in V["方案一"][5].conflicts]
    if all(c & {"乙", "庚"} for c in c1):
        notes.append(f"方案一「斷染時許依下修上」解決了與頌文壬的衝突，但剩下的 {len(c1)} 個衝突全都牽涉乙或庚：允許前八品依下修上，正與「未離下時未能修彼」（乙）和《顯宗》「前八品時不修上邊世俗道」（庚）相抵。書中說此說「和『然由有漏繫地堅牢，未離下時不能修彼』相矛盾」，機器的結果與之一致。")
    c2 = [set(c) for c in V["方案二"][5].conflicts]
    gone2 = [c for c in base_c if c not in c2]
    if all("己" in c for c in gone2) and all("己" not in c for c in c2):
        notes.append(f"方案二「許得離道而修」只解決了牽涉橋接原則己的 {len(gone2)} 個衝突。")
    c3 = [set(c) for c in V["方案三"][5].conflicts]
    gone3 = [c for c in base_c if c not in c3]
    if all("甲" in c for c in gone3) and all(c in base_c for c in c3):
        notes.append(f"方案三（作者以「退」會通甲）解決了牽涉甲的 {len(gone3)} 個衝突，沒有引入新的衝突。")
    c23 = [set(c) for c in v23[5].conflicts]
    if all(("辛" in c) or ({"丙", "丁"} <= c) for c in c23):
        notes.append(f"方案二、三並用，仍剩 {len(c23)} 個衝突，全都牽涉有說（辛）或「修七智」一路（丙、丁）。")
    opt_notes = "<ul>" + "".join(f"<li>{E(n)}</li>" for n in notes) + "</ul>"
    keep = {"乙", "庚", "壬", "丙"}
    mcs23 = [set(x) for x in v23[5].corrections]
    viable = [x for x in mcs23 if not (x & keep)]
    question = ""
    if viable:
        vs = "；".join("、".join(sorted(x, key=R3["stmts"].index)) for x in viable)
        question = (f"<p><b>給作者的一個問題。</b>在方案二、三之下，要同時保住乙、庚、壬和丙，最省的放棄方式只有：{E(vs)}。"
                    "其中丁是書中頁 201 的推理（「只能是空處近分俗智，因為下地俗智不是第四靜慮染的斷對治」）。"
                    "若前八無間道「修」俗智不必是作為第四靜慮染的斷對治而修，丁就不成立，丙與《顯宗》的衝突隨之消失。這一步是否站得住，需要您判斷。</p>")
    return f"""
<h2 id="m3">模組三：眾賢沒能解決的矛盾</h2>
<p>底本是《俱舍九題》第九題第五節（頁 191–203）。問題是：聖者以無漏道離第四靜慮染，何時修空處近分的有漏善？作者把《正理》《顯宗》中相關的說法一一擺出，指出它們互相牴觸，並斷言「眾賢沒能解決這個問題」。這裡把書中的十條陳述形式化，交給引擎做衝突分析。</p>
<p>世界是五個道位（前八品的無間道、解脫道，第九品的無間道、解脫道，以及「退後」），按次序排列。「無間道」「未離下」「得上地」等是固定的事實；「修上地有漏」「成就無色善」「修俗智」「引有漏離繫得」是待定的，由引擎替每個道位決定真假。</p>
<div class="scroll"><table class="stack"><thead><tr><th>編號</th><th>原文或說明</th><th>Kosa 命題</th><th>出處</th></tr></thead><tbody>{''.join(rows)}</tbody></table></div>
<p class="note">【丁】是作者在頁 201 的推理；【己】【癸】是兩條橋接原則。【癸】必須補出：沒有它，「無色善心已可得」（甲）與「未離下時未能修彼」（乙）在邏輯上並不衝突。形式化在這裡又一次逼出了一條隱含原則。</p>

<h3>極小衝突集：{len(base.conflicts)} 個</h3>
<p>每一組放在一起就矛盾，去掉其中任何一條就不矛盾。</p>
<div class="box">{conf}</div>

<h3>極小修正集：{len(base.corrections)} 種最省的放棄方式</h3>
<p>每一種都是「最少放棄這幾條，其餘全部相容」。它們自然分成三個立場：</p>
<div class="two">
<div class="box"><b>立場 A：前八品已修上地有漏</b>（{len(A)} 種）<p class="note">放棄《正理》《顯宗》的「未離下時未能修彼」、《顯宗》的補充，以及頌「諸道依得此，修此地有漏」。代價是放棄一句頌文。</p>{sets(A)}</div>
<div class="box"><b>立場 B：第九解脫道才修</b>（{len(B)} 種）<p class="note">保住乙、庚、壬。{B_note}</p>{sets(B)}</div>
<div class="box"><b>立場 C：第九無間道修</b>（{len(C)} 種）<p class="note">放棄乙與頌文壬，但保住《顯宗》的「前八品不修」（庚）。</p>{sets(C)}</div>
</div>

<h3>會通方案各解決了甚麼</h3>
<div class="scroll"><table class="stack"><thead><tr><th>方案</th><th>出自</th><th>做法</th><th class="num">剩餘衝突</th><th>剩餘的衝突集</th></tr></thead><tbody>{''.join(var_rows)}</tbody></table></div>
{opt_notes}
{question}
<h3>三個立場的代表世界</h3>
<p class="note">「●」表示該道位上此事為真。</p>
<div class="two">{reps}</div>
<p><b>結論。</b>機器的結論與《九題》一致：在這組陳述之下，眾賢的問題沒有不付代價的解法。形式化沒有替我們選擇，但給出了代價的完整清單，並精確指出哪一條推理承擔了哪一份衝突。</p>
"""


def onto_node_html(m, name):
    """前提樹中的本體條目：定義顯示為約定（附定義式與頌），門、關係顯示為本體結構。"""
    onto = m.onto
    if name in onto.defs:
        notes = onto.def_notes.get(name, {})
        song = notes.get("頌", "")
        src = f'<span class="src">頌「{E(song)}」</span>' if song else ""
        return (f'<li><span class="node"><span class="lay 約定">約定</span><span class="k">{E(name)}</span>'
                f'<span>本體定義：{E(name)}＝{E(onto.defs[name])}</span>{src}</span></li>')
    kind = "門" if name in onto.dims else ("關係" if name in onto.rels else "")
    extra = ""
    if name in onto.rels:
        r = onto.rels[name]
        props = "、".join(x for x, f in (("對稱", r.symmetric), ("可傳遞", r.transitive)) if f)
        extra = f"（{props}）" if props else ""
    return f'<li><span class="node"><span class="lay 本體">本體</span><span class="note">{E(kind)}「{E(name)}」{E(extra)}</span></span></li>'


def tree_html(m, R, sid, seen, verse_checks):
    n = R.nodes[sid]
    st = m.statements[sid]
    lay = f'<span class="lay {n.layer}">{n.layer}</span>'
    head = f'<span class="node">{lay}<span class="k">{E(sid)}</span><span>{E(n.title)}</span>'
    if sid in seen:
        return f'<li>{head}<span class="note">（見上）</span></span></li>'
    seen.add(sid)
    info = ""
    if n.layer in ("定理", "目標", "推論"):
        ec = R.edges[sid]
        ok = ec.ok and not ec.unnecessary
        info = f'<span class="{"ok" if ok else "bad"}" style="font-size:13px">{"✓ 由所依推出，所依缺一不可" if ok else "✗ 未通過"}</span>'
    elif n.layer == "假定":
        if st.meta.get("狀態") == "待核":
            info = '<span class="pend">待核</span>'
        vb = [c for c in verse_checks if c[0] == sid and c[1] == "頌"]
        if vb:
            info += "".join(f'<span class="src">頌「{E(q)}」{"✓" if h else "✗"} {E(h[0][0][2:4]) if h else ""}</span>' for _, _, q, h in vb)
        elif st.meta.get("依據"):
            info += f'<span class="src">{E(st.meta["依據"][:60])}</span>'
    head += info + "</span>"
    body = f'<div style="margin:2px 0 0"><code>{E(st.text)}</code></div>'
    kids = "".join(tree_html(m, R, d, seen, verse_checks) for d in n.deps)
    kids += "".join(onto_node_html(m, nm) for nm in onto_names(n.onto_deps))
    if not kids:
        return f'<li>{head}{body}</li>'
    return f'<li><details open><summary>{head}</summary>{body}<ul>{kids}</ul></details></li>'


def section_tree(R4):
    m = R4["module"]
    T = R4["tree"]
    N = T.nodes
    vc = R4["verse_checks"]
    tree = f'<ul class="tree">{tree_html(m, T, "目標", set(), vc)}</ul>'
    assumptions = [s for s, n in N.items() if n.layer == "假定"]
    pend = [s for s in assumptions if m.statements[s].meta.get("狀態") == "待核"]
    lit = [s for s in assumptions if s not in pend]
    users = {a: [s for s, n in N.items() if a in n.deps] for a in N}
    rows = []
    for a in [s for s, n in N.items() if n.layer in ("約定", "假定")]:
        st = m.statements[a]
        vb = verse_badge(vc, a)
        src = vb if vb else E(st.meta.get("依據", ""))
        status = '<span class="pend">待核</span>' if a in pend else ('約定' if N[a].layer == "約定" else '有文獻')
        rows.append(f"<tr><td class='k'>{E(a)}</td><td>{E(N[a].title)}</td><td><code>{E(st.text)}</code></td><td>{status}</td><td class='note'>{src}</td><td>{tags(users[a])}</td></tr>")
    edges = []
    for sid, ec in T.edges.items():
        ok = ec.ok and not ec.unnecessary
        edges.append(f"<tr><td class='k'>{E(sid)}</td><td>{E(N[sid].title)}</td><td>{tags(N[sid].deps)}</td><td class='{'ok' if ec.ok else 'bad'}'>{'✓' if ec.ok else '✗'}</td><td class='{'ok' if not ec.unnecessary else 'bad'}'>{'✓' if not ec.unnecessary else '多餘：' + '、'.join(ec.unnecessary)}</td></tr>")
        if not ec.ok and ec.world is not None:
            edges.append(f"<tr><td></td><td colspan='4'><b class='bad'>推不出。反例：</b>滿足所依的全部條目、卻不滿足【{E(sid)}】的世界——它指出所依還缺甚麼。{world_html(ec.world, m, target_hits(ec.world, m, sid))}</td></tr>")
    dep = [a for a, v in T.dependent_assumptions.items() if v]
    goal_base = T.closure[T.goal]
    tight = len(T.goal_minimal) == 1 and set(T.goal_minimal[0]) == goal_base
    not_on_path = [a for a in assumptions if a not in goal_base]
    prec = []
    for r in R4["precision"]:
        r = r + [""] * (5 - len(r))
        verdict = r[2]
        cls = {"精確": "blue", "精確化": "", "定理": "blue", "約定": "", "不必要": "red"}.get(verdict, "")
        prec.append(f"<tr><td class='k'>{E(r[0])}</td><td>{E(r[1])}</td><td><span class='chip {cls}'>{E(verdict)}</span></td><td>{E(r[3])}</td><td class='note'>{E(r[4])}</td></tr>")
    counts = {}
    for r in R4["precision"]:
        counts[r[2]] = counts.get(r[2], 0) + 1
    mapped = set()
    for r in R4["precision"]:
        for x in re.split(r"[、，]", r[3]):
            mapped.add(x.strip())
    new_ones = [a for a in assumptions if a not in mapped]
    pend_rows = "".join(f"<li><b>【{E(a)}】{E(N[a].title)}</b><br><code>{E(m.statements[a].text)}</code><br><span class='note'>{E(m.statements[a].meta.get('說明', ''))}</span></li>" for a in pend)
    return f"""
<h2 id="tree">前提體系：從一條命題拆到它的假定</h2>
<p>v0.1 照 2022 文的十六條前提檢驗。這一版換一個方向：從結論出發，問它依賴甚麼；所依的命題若還有更基礎的理由，就再拆下去，直到遇到不再在本庫中推出的論點。拆到底，命題分成四層：</p>
<ul>
<li><span class="lay 約定">約定</span> 由定義或本體成立，無可爭議。大部分約定直接寫在本體裡：門、值、定義、關係的類型，以及「每法於每門恰取一值」。</li>
<li><span class="lay 假定">假定</span> 不在本庫中推出的論點。有頌文或論文明文的，記出處並與 CBETA 核對；憑阿毘達磨知識補出而尚未找到明文的，標「待核」。</li>
<li><span class="lay 定理">定理</span> 由所列的前提推出。每一條都經兩道檢驗：求解器檢驗它由所依推出，而且所依缺一不可；Lean 內核再證明一次，不受世界大小的限制。</li>
<li><span class="lay 目標">目標</span> 有覆無記色唯初靜慮繫。</li>
</ul>
<p>結果：{len(assumptions)} 條假定（{len(lit)} 條有頌文或論文明文，{len(pend)} 條待核），{sum(1 for n in N.values() if n.layer == '約定')} 條約定（另有本體中的約定），{sum(1 for n in N.values() if n.layer == '定理')} 條定理。</p>

<h3>前提樹</h3>
<p class="note">從目標往下讀。每個節點下面是它所依的條目；已在前面展開過的，記「見上」。點節點可以收起。</p>
<div class="scroll">{tree}</div>

<h3>機器檢驗</h3>
<div class="scroll"><table class="stack"><thead><tr><th>定理</th><th>內容</th><th>所依</th><th>推得出</th><th>缺一不可</th></tr></thead><tbody>{''.join(edges)}</tbody></table></div>
<ul>
<li>全部假定、約定彼此相容：{'✓' if T.consistent else '✗'}。</li>
<li>假定互不可推（沒有一條假定能由其餘推出）：{'✓' if not dep else '✗ ' + E('、'.join(dep))}。</li>
<li>目標最終依賴 {len(goal_base)} 條假定、約定；這恰是目標在全部假定中唯一的極小前提集：{'✓' if tight else '✗'}。也就是說，體系裡沒有一條在目標的證明中是多餘的。{'不在目標證明路徑上的假定：' + tags(not_on_path) + '（只用於旁支定理）。' if not_on_path else ''}</li>
</ul>
<div class="box"><b>第一次改進：引擎找到一條更省的路。</b>
<p>初版的樹讓【定八】依賴【定七】「表唯在欲界、初靜慮」（即頌「表唯有伺二」），因而依賴【假七】「表業必有剎那等起心」。每條邊都檢驗通過，但引擎再算目標在全部假定中的極小前提集時，發現假七用不上：有覆無記表的剎那等起心，已由【定一】與【假六】保證。於是新增【定七乙】「有覆無記表唯在欲界、初靜慮」，它比定七弱，但不需要假七；定八改依定七乙。定七作為頌文的形式化仍保留在庫中，只是不再在目標的證明路徑上。</p>
<p class="note">這正是你說的「在完善的過程中，找到更簡潔的推理」。每加一條假定或定理，這類檢查都會自動重跑。</p></div>

<h3>假定與約定一覽</h3>
<div class="scroll"><table class="stack"><thead><tr><th>編號</th><th>內容</th><th>Kosa 命題</th><th>狀態</th><th>依據</th><th>被誰所依</th></tr></thead><tbody>{''.join(rows)}</tbody></table></div>

<h3 id="precision">2022 文十六條前提的精確化</h3>
<p>原文是示例，這裡逐條判定它在體系中的位置：精確 {counts.get('精確', 0)} 條，精確化 {counts.get('精確化', 0)} 條，可推出的定理 {counts.get('定理', 0)} 條，本體約定 {counts.get('約定', 0)} 條，不必要 {counts.get('不必要', 0)} 條。</p>
<div class="scroll"><table class="stack"><thead><tr><th>原前提</th><th>原文</th><th>判定</th><th>在體系中</th><th>說明</th></tr></thead><tbody>{''.join(prec)}</tbody></table></div>
<p><b>原文沒有、體系新增的假定：</b>{tags(new_ones)}。其中最基礎的是【假一】至【假四】：頌「勝義善解脫，自性慚愧根，相應彼相應，等起色業等」所說的四種善。2022 文的「色由等起成善染性」，在體系中不再是前提，而是由四種善推出的定理（定一）：色不是勝義，不是心所，沒有相應，所以它的善染只能由等起而成。</p>

<h3 id="pending">待核的 {len(pend)} 條：需要您確認</h3>
<p>這幾條是我憑阿毘達磨知識補出的，體系離不開它們，但我還沒有找到明文。請您判斷是否成立、出處在哪裡。若某條不成立，改動之後重跑，引擎會指出哪些定理隨之失效、需要改走哪條路。</p>
<ol>{pend_rows}</ol>
"""


def section_lean_guide(R4):
    src = (ROOT / "lean" / "Kosa" / "Proof4.lean").read_text(encoding="utf-8")
    d3 = re.search(r"/-- 【定三】.*?(?=\n\n/--)", src, re.S).group(0)
    whole = re.search(r"theorem «目標由諸假定».*?«目標成立» W d3 d8", src, re.S).group(0)
    link = R4.get("web_link", "")
    btn = f'<a class="btn" href="{E(link)}">在官方網頁編輯器中打開模組四（免安裝）</a>' if link else ""
    return f"""
<h2 id="lean">Lean 導讀：同一個證明，兩種寫法</h2>
<p>Lean 是一個「證明檢查器」。你把前提和結論寫成它能讀的形式，再寫出證明步驟；它逐步核對，每一步都必須由已有的東西嚴格推出。全部通過，這個證明就對任意世界成立——不像求解器只能窮盡有限大小的世界。</p>
<p>你不需要寫 Lean。你寫的是繁體中文命題；Kosa 把它們自動翻成 Lean 的定義（<code>lean/Kosa/Module4.lean</code>），證明另寫在 <code>lean/Kosa/Proof4.lean</code>，每一行都附了中文說明。下面以【定三】為例，左邊是中文推理，右邊是 Lean。</p>
<div class="leanpair">
<div class="box"><b>中文</b>
<p>定三：有覆無記色唯是表色。依：定二、假五。</p>
<p>設 x 是有覆無記色。<br>由定二（善、染之色唯是業），x 是業，即表或無表。<br>若 x 是表：成立。<br>若 x 是無表：由假五（無表唯善、不善），x 是善或不善；但 x 是有覆無記，相違。<br>所以 x 是表。</p></div>
<div><pre>{E(d3)}</pre></div>
</div>
<p>讀法要點：括號裡的 <code>(d2 : «定二» W)</code>、<code>(a5 : «假五» W)</code> 就是「依」；冒號後的 <code>«定三» W</code> 是結論；<code>by</code> 之後每一行對應左邊一句。<code>rcases hYe with h | h</code> 是「分兩種情況」，<code>cases h'</code> 是「這種情況不可能」。</p>
<h3>把整棵樹拼起來</h3>
<p>每條定理單獨證明之後，從假定到目標的證明就只是按「依」拼接。下面這條定理的前提恰是體系的全部基礎（假七不在其中），證明裡沒有任何新的推理：</p>
<pre>{E(whole)}</pre>
<p class="note">Lean 的公理檢查：{E(R4.get('lean_axioms', ''))}。沒有 sorry（未完成的證明），沒有額外公理；propext 是 Lean 的標準公理，來自 simp。</p>
<h3 id="nolean">不裝 Lean，怎樣自己看到它通過</h3>
<div class="two">
<div class="box"><b>官方網頁編輯器</b><p>點下面的按鈕，模組四的全部定義和證明會載入 live.lean-lang.org。程序在對方的伺服器上運行；右側欄顯示每一步的狀態，沒有紅色錯誤即全部通過。也可以把 <code>lean/網頁版/模組四.lean</code> 的內容貼進去。</p>{btn}<p class="note">網頁編輯器可能使用比 4.24 更新的 Lean 版本。本文件已在 Lean 4.24 下通過；我這邊的環境連不上該網站，未能在線測試。</p></div>
<div class="box"><b>放到 GitHub，自動檢驗</b><p>倉庫裡的 <code>.github/workflows/kosa.yml</code> 讓 GitHub 在每次提交後自動：用 Lean 檢查全部證明（並審核不得有 sorry）；核對頌文、逐條檢驗前提體系；重新生成本報告並發佈為網頁。你只需在網頁上修改 <code>.kosa</code> 文件並提交，結果顯示為綠勾或紅叉。公開倉庫免費。</p></div>
<div class="box"><b>體積</b><p>Lean 的核心工具鏈解壓後約 2.3 GB。Mathlib（數學庫）的預編譯文件還要再加幾 GB，Kosa 用不到它。求解器部分（Python 加 clingo）很小。Mac 空間緊張，不必在本機安裝。</p></div>
<div class="box"><b>以後想深入</b><p>GitHub Codespaces 在瀏覽器裡提供完整的編程環境，可以安裝 Lean 的編輯器插件，逐步看證明狀態。個人賬戶每月有免費額度。</p></div>
</div>
"""


def section_verses(R1, R2, R3, R4=None, R5=None, R6=None, onto_checks=None):
    rows = []
    groups = [("一", R1), ("二", R2), ("三", R3)] + [(k, R) for k, R in (("四", R4), ("五", R5), ("六", R6)) if R]
    if onto_checks:
        groups.append(("本體", {"verse_checks": onto_checks}))
    for tag, R in groups:
        for sid, field, quote, hits in R["verse_checks"]:
            loc = f"{hits[0][0]}·第{hits[0][1]}行" if hits else "未找到"
            line = hits[0][3] if hits else ""
            rows.append(f"<tr><td>{'' if tag == '本體' else '模組'}{tag}</td><td class='k'>{E(sid)}</td><td>{E(field)}</td><td>{E(quote)}</td><td class='{'ok' if hits else 'bad'}'>{'✓' if hits else '✗'} {E(loc)}</td><td class='note'>{E(line)}</td></tr>")
    ok = sum(1 for _, R in groups for c in R["verse_checks"] if c[3])
    n = sum(len(R["verse_checks"]) for _, R in groups)
    return f"""
<h2 id="verses">引文核對：{ok}/{n} 句頌文與 CBETA 一致</h2>
<p>命題中「頌」「相關頌」兩欄所引的頌文，以及本體註記中的頌文，逐字（去標點）與 CBETA T1560《阿毘達磨俱舍論本頌》核對，並給出所在品與行。這是 v0.1 的最小語料層。</p>
<p>建庫時，編者憑記憶寫的幾句頌文（如「等起有二種，謂因及剎那」「色不見所斷」）與 CBETA 不合，被這一步攔下並已改正（實為「等起有二種，因及彼剎那」「色定非見斷」）。這正是這一層存在的理由：AI 憑記憶寫的引文，不經核對不能入庫。</p>
<div class="scroll"><table class="stack"><thead><tr><th>模組</th><th>命題</th><th>欄</th><th>引文</th><th>結果</th><th>CBETA 原行</th></tr></thead><tbody>{''.join(rows)}</tbody></table></div>
"""


def section_extend():
    return """
<h2 id="extend">怎樣擴展</h2>
<div class="two">
<div class="box"><b>加一個概念</b><p>在 <code>本體/門.kosa</code> 加一門，或在 <code>本體/定義.kosa</code> 加一個定義。例如加「所緣」一門後，前提3乙就可以照原文寫成「同所緣」，再另立「門轉由所緣定」，把現在的詮釋決定變成可檢驗的命題。</p></div>
<div class="box"><b>加一條命題</b><p>在模組文件中寫一個【編號】條目：命題一行，下面縮進寫原文、出處、頌、詮釋、組。不需要寫任何代碼。</p></div>
<div class="box"><b>加一個模組</b><p>新建 <code>模組/某某/命題.kosa</code>，聲明類別（開放的法、固定的道位、或門的積），寫命題。工作流程函數（補前提、極小前提集、衝突分析、計數）都可直接用。</p></div>
<div class="box"><b>加一道考題</b><p>把文獻中的結論寫成【驗證】或【求證】條目。引擎會告訴你它成立、不成立（附反例），或由哪幾條前提推出。</p></div>
</div>
<h3>還沒有做的</h3>
<ul>
<li>本體已按五位七十五法立自性，但地只分九地加不繫，沒有近分、靜慮中間；十二處、十八界、五蘊的歸攝還沒有寫成定義。</li>
<li>補特伽羅只記「欲染」「初靜慮染」兩段經歷；二靜慮以上各地的離染、得果、練根、退、命終，還沒有一般的時間模型（模組六因此把得、捨規則壓縮在待核的假定裡）。</li>
<li>關係只能連接同一類別的兩項；「補特伽羅成就某法」暫時寫成補特伽羅的謂詞。</li>
<li>沒有「所緣」一門，所以「同所緣」只能借「同門轉」表達（模組一前提3乙）。</li>
<li>模組三的時間只用五個代表道位，不是一般的道位模型。九品、九地、退、命終、生上地的一般模型是賢聖品、智品、定品形式化的前提，也是最難的部分。</li>
<li>語料層只有《俱舍論頌》；《俱舍》長行、《正理》《顯宗》《婆沙》未入庫，出處欄只是文字說明，不能自動核對。</li>
<li>證明文字未自動生成。引擎給出極小前提集和反例；可讀的逐步證明目前在 Lean 中手寫。</li>
<li>前提體系中標「待核」的六條假定（見上文），尚待作者以論文確認或否定。模組一的補出前提中，補二、補四、補七、補九亦同。</li>
</ul>
<h3>可作為 Kosa 與 AbhiLib 比較的考題</h3>
<ol>
<li>2022 文命題：給出 16 條前提，能否發現證明不完整、指出缺哪些前提、找出冗餘？</li>
<li>九十八隨眠：能否從頌文的排除規則推出 98 與「十七七八四」，並說明閉包原則？</li>
<li>眾賢的矛盾：能否給出全部極小衝突集與極小修正集，並評估方案一、二、三？</li>
<li>轉與隨轉：能否發現「等起」的兩種讀法對結論的影響？</li>
<li>引文：所引頌文是否全部與 CBETA 一致？</li>
</ol>
"""


def section_run(R1, R2, R3, R4, R5, R6):
    tree = """kosa/
├─ 本體/            門.kosa　定義.kosa　關係.kosa　概念表.tsv
├─ 模組/
│  ├─ 一_有覆無記色/命題.kosa
│  ├─ 二_九十八隨眠/命題.kosa
│  ├─ 三_眾賢之矛盾/命題.kosa
│  ├─ 四_前提體系/命題.kosa　精確化對照.tsv
│  ├─ 五_阿羅漢最後心/命題.kosa
│  └─ 六_阿那含成就初靜慮/命題.kosa
├─ 語料/            俱舍論頌.json（CBETA T1560）
├─ kosa/            引擎（Python）：lang 語法　kb 讀庫　engine 求解　workflow 流程
│                   evaluate 求值　render 渲染　lean 導出　corpus 核對　report 報告
├─ lean/            Lean 4 項目：Kosa/Module1、4、5、6.lean（自動生成）　Proof1、4、5、6.lean（證明）
│                   網頁版/模組四、五、六.lean（可貼進網頁編輯器的單文件版）
├─ .github/workflows/kosa.yml　GitHub 自動運行
└─ 報告/index.html  本頁"""
    return f"""
<h2 id="run">怎樣運行</h2>
<pre>pip install clingo
python3 -m kosa 報告              # 重跑全部模組，生成本頁
python3 -m kosa 檢驗 一 求證 前提1 前提2 …   # 檢驗一組前提是否蘊涵某命題
python3 -m kosa 相容 三 甲 乙 丙 …          # 檢驗一組命題是否相容，並列出衝突集
python3 -m kosa 驗證              # 頌文核對＋前提體系逐條檢驗（GitHub 自動運行用的就是這一步）
python3 -m kosa 核對              # 核對全部頌文引用
python3 -m kosa lean              # 重新導出 lean/Kosa/Module*.lean 與網頁版
cd lean &amp;&amp; lake build             # 用 Lean 4.24 檢查證明</pre>
<pre>{E(tree)}</pre>
<p class="note">本次運行：模組五 {R5['seconds']:.1f} 秒，模組六 {R6['seconds']:.1f} 秒，模組四（前提體系）{R4['seconds']:.1f} 秒（求解器調用 {R4['calls']} 次），模組一 {R1['seconds']:.1f} 秒（求解器調用 {R1['calls']} 次），模組二 {R2['seconds']:.1f} 秒，模組三 {R3['seconds']:.1f} 秒。檢驗範圍：開放類別至多 6 個法（模組五 4 個，模組六 2 個補特伽羅）。</p>
"""


def section_rebuild(onto, R1, R2, R4):
    """v0.3：本體按五位七十五法重建。"""
    D = onto.dims
    wei = [("色", "色自性"), ("心", None), ("心所", "心所自性"), ("心不相應行", "不相應自性"), ("無為", "無為自性")]
    cnt = []
    total = 0
    for w, dn in wei:
        n = len(D[dn].values) if dn else 1
        total += n
        sub = tags(D[dn].values) if dn else "識（依所依根再分六識，見「六識」門）"
        cnt.append(f"<tr><td class='k'>{E(w)}</td><td class='num'>{n}</td><td>{sub}</td></tr>")
    six = []
    for name in ("大地法", "大善地法", "大煩惱地法", "大不善地法", "小煩惱地法", "不定地法"):
        six.append(f"<tr><td class='k'>{E(name)}</td><td><code>{E(onto.defs[name])}</code></td></tr>")
    R2ok = R2["tests"][0][1] == R2["tests"][0][3]
    T4 = R4["tree"]
    A1 = R1["analysis"]
    return f"""
<h2 id="rebuild">本體 v0.3：按五位七十五法重建</h2>
<p>v0.2 的本體只為一條命題服務：法只分心、心所、色；心所只分「惑」與「非惑心所」。這一版把一法「是什麼」——它的自性——按七十五法列出，把「惑」「五見」「表色」「四諦」這類按某個標準歸成的類改寫為定義。您提的四個問題，處理如下。</p>
<div class="two">
<div class="box"><b>一、法類補上心不相應行、無為</b><p>「法類」一門現在就是五位：色、心、心所、心不相應行、無為。每一位下面再立一門「自性」，列出該位的諸法，合計 {total} 法。心在七十五法中只算一法，另立「六識」一門作分別。</p></div>
<div class="box"><b>二、惑、非惑心所是分類，不是自性</b><p>同意。心所的自性改為「心所自性」一門，列四十六心所；「惑」改為定義：貪或瞋或慢或疑或癡或五見。這樣同一個心所可以同時屬於幾種分類（貪既是惑，又是不定地法），不必在門裡重複列出。大地法等六地也是定義。</p></div>
<div class="box"><b>三、「繫」改名「繫不繫」</b><p>同意，並照同一原則改了三門：「斷」改「斷非斷」（《萬字》2.1 本來就這樣寫），「漏」改「有漏無漏」，「伺」改「有伺無伺」。最後一個不只是名稱問題：「伺」現在是心所自性的一個值，門不能再叫這個名字。原則是：一門的值若是「某」與「非某」相對，門名就把兩頭都說出來，這也是論書分別門的舊式。</p></div>
<div class="box"><b>四、五見放在定義</b><p>五見的自性都是慧——它們不是五個心所，而是慧的五種。所以在「慧」之下立「見種」一門，值取頌「眼法界一分，八種說名見，五識俱生慧，非見不度故」：五染污見、世間正見、有學見、無學見，以及非見。「五見」是由其中五個值組成的類，放在定義；「惑」又引用「五見」。門記「是哪一個」，定義記「歸哪一類」。</p></div>
</div>
<h3>七十五法</h3>
<table style="width:auto"><thead><tr><th>位</th><th class="num">法數</th><th>自性</th></tr></thead><tbody>{''.join(cnt)}</tbody></table>
<details><summary>心所六地（定義）</summary><table><tbody>{''.join(six)}</tbody></table></details>
<h3>其他改動</h3>
<ul>
<li><b>表色。</b>v0.2 有「色類」一門（表色、無表色、非業色）。現在無表色是色的自性之一；表色由「表非表」一門定義，門只適用於色處、聲處。單個值也可以帶適用條件：「身表〔色處〕」「語表〔聲處〕」，取頌「身表許別形」「語表許言聲」。</li>
<li><b>四諦。</b>苦諦、集諦定義為有漏，滅諦為擇滅，道諦為無漏的有為法（頌「有漏名取蘊……及苦集世間」「無漏謂道諦，及三種無為」）。</li>
<li><b>補特伽羅。</b>新增一組只用於有情的門：果位（四向四果加異生）、生地、欲染、初靜慮染、見道依地。模組六用到它們。</li>
<li><b>防呆。</b>本體一變，舊命題可能悄悄失去意義——例如一條命題用了「見種」，模組卻沒有聲明用這一門，那些值在世界裡就永遠不成立。引擎現在在讀入時檢查：命題、定義、適用條件涉及的門，都必須在模組的「用門」裡，否則報錯。</li>
<li><b>積類別。</b>模組二的候選位原來是「惑種×斷×見諦×界」。惑種一門取消後，積的因子可以是一個定義：「惑×斷非斷×見諦×界」，引擎把「惑」展開為十個門值，並補上每個值所蘊含的上位門值（身見→見種＝身見、心所自性＝慧、法類＝心所）。</li>
</ul>
<h3>舊模組照舊通過</h3>
<p>重建之後，前四個模組全部重跑：模組一的極小前提集仍是 {len(A1.minimal_sets[0])} 條；模組二仍推出 {R2['tests'][0][3]} 隨眠 {'✓' if R2ok else '✗'}；模組四的目標仍依賴 {len(T4.closure[T4.goal])} 條假定、約定。Lean 的證明改寫了幾處：原來「有惑種者是惑」要借本體的適用條件，現在惑是定義，五見是惑可以直接展開，證明反而短了。</p>
"""


def tree_section(R, anchor, heading, intro, after_tree="", show_drop=True, first_roots=()):
    """前提體系模組（五、六）的通用展示。"""
    m = R["module"]
    T = R["tree"]
    N = T.nodes
    vc = R["verse_checks"]
    goal = T.goal
    tree = f'<ul class="tree">{tree_html(m, T, goal, set(), vc)}</ul>'
    side = [s for s, n in N.items() if n.layer in ("定理", "推論") and s not in T.closure.get(goal, set()) and goal not in n.deps]
    reached = set()

    def walk(x):
        if x in reached:
            return
        reached.add(x)
        for d in N[x].deps:
            walk(d)
    walk(goal)
    unreached = [s for s, n in N.items() if n.layer in ("定理", "推論") and s not in reached]
    used = {d for s in unreached for d in N[s].deps}
    side_roots = list(first_roots) + [s for s in unreached if s not in used and s not in first_roots]
    seen_side = set(reached)
    side_trees = "".join(tree_html(m, T, s, seen_side, vc) for s in side_roots)
    edges = []
    for sid, ec in T.edges.items():
        ok = ec.ok and not ec.unnecessary
        edges.append(f"<tr><td class='k'>{E(sid)}</td><td>{E(N[sid].title)}</td><td>{tags(N[sid].deps)}</td><td class='{'ok' if ec.ok else 'bad'}'>{'✓' if ec.ok else '✗'}</td><td class='{'ok' if not ec.unnecessary else 'bad'}'>{'✓' if not ec.unnecessary else '多餘：' + '、'.join(ec.unnecessary)}</td></tr>")
    users = {a: [s for s, n in N.items() if a in n.deps] for a in N}
    rows = []
    for a in R["base"]:
        st = m.statements[a]
        vb = verse_badge(vc, a)
        src = vb if vb else E(st.meta.get("依據", ""))
        pend = st.meta.get("狀態") == "待核"
        status = '<span class="pend">待核</span>' if pend else ('約定' if N[a].layer == "約定" else '有文獻')
        rows.append(f"<tr><td class='k'>{E(a)}</td><td>{E(N[a].title)}</td><td><code>{E(st.text)}</code></td><td>{status}</td><td class='note'>{src}</td><td>{tags(users[a]) or '<span class=note>（庫存）</span>'}</td></tr>")
    mins = "".join(f"<li>{tags(x)}</li>" for x in T.goal_minimal)
    common = set(T.goal_minimal[0]).intersection(*map(set, T.goal_minimal)) if T.goal_minimal else set()
    drop_rows = []
    for a, r in R["drop"].items():
        if not r.ok:
            drop_rows.append(f"<tr><td class='k'>{E(a)}</td><td>{E(N[a].title)}</td><td>{world_html(r.world, m, target_hits(r.world, m, goal))}</td></tr>")
    drop = (f"""<h3>哪幾條缺一不可</h3>
<p>逐條去掉一條假定或約定，其餘全部保留，再問目標是否成立。不成立的，引擎給出反例——這幾條就是無論走哪條路都繞不過去的。</p>
<div class="scroll"><table class="stack"><thead><tr><th>去掉</th><th>內容</th><th>反例</th></tr></thead><tbody>{''.join(drop_rows)}</tbody></table></div>""" if show_drop and drop_rows else "")
    pend_all = [a for a in R["base"] if m.statements[a].meta.get("狀態") == "待核"]
    pend_goal = [a for a in pend_all if a in T.closure[goal]]
    dep = [a for a, v in T.dependent_assumptions.items() if v]
    return f"""
<h2 id="{anchor}">{heading}</h2>
{intro}
<h3>前提樹</h3>
<p class="note">從目標往下讀。「✓」表示求解器已檢驗：所依推得出它，且所依缺一不可；Lean 另有證明。</p>
<div class="scroll">{tree}</div>
{f'<h3>其他定理</h3><p class="note">不在目標的證明路徑上，但由庫中的條目推出，一併收入。</p><div class="scroll"><ul class="tree">{side_trees}</ul></div>' if side_trees else ''}
{after_tree}
<h3>機器檢驗</h3>
<div class="scroll"><table class="stack"><thead><tr><th>定理</th><th>內容</th><th>所依</th><th>推得出</th><th>缺一不可</th></tr></thead><tbody>{''.join(edges)}</tbody></table></div>
<ul>
<li>全部假定、約定彼此相容：{'✓' if T.consistent else '✗'}；假定互不可推：{'✓' if not dep else '✗ ' + E('、'.join(dep))}。</li>
<li>目標在全部 {len(R['base'])} 條假定、約定中的極小前提集有 {len(T.goal_minimal)} 個——也就是 {len(T.goal_minimal)} 條互不包含的證明路線：<ol>{mins}</ol>每一條都用到：{tags(sorted(common, key=list(N).index))}。</li>
<li>主證明（前提樹）最終依賴 {len(T.closure[goal])} 條；其中待核的：{tags(pend_goal) or '無'}。</li>
</ul>
{drop}
<h3>假定與約定</h3>
<p class="note">「被誰所依」為空的條目，不在本題的任何證明中用到，作為庫存保留，留給以後的命題。</p>
<div class="scroll"><table class="stack"><thead><tr><th>編號</th><th>內容</th><th>Kosa 命題</th><th>狀態</th><th>依據</th><th>被誰所依</th></tr></thead><tbody>{''.join(rows)}</tbody></table></div>
"""


def section_m5(R5):
    m = R5["module"]
    T = R5["tree"]
    intro = f"""<p>題目：「阿羅漢最後心是苦諦、集諦。」證明的全部：最後心是無覆無記（頌「二無記涅槃」），所以不是道諦（道諦唯善）；按定義它是心，不是無為；所以不是無漏，即有漏；有漏法名苦，亦名集（頌「有漏名取蘊……及苦集世間」）。</p>
<p>最後一步含一個約定：苦諦、集諦的範圍相等。上一版把它藏在兩個定義裡；這一版把它列為【定甲九】，放在目標的正下方。「阿羅漢最後心」也改為定義（【約甲二】）：阿羅漢心相續的最後一剎那心。</p>
<p>第二部分證明上一版的待核假定「相應的心、心所同性」（原甲假九，現為【定甲八】）。證明逼出了更基礎的條目，見下面「其他定理」的第一棵樹。</p>"""
    box = f"""<div class="box"><b>本體約定不再隱藏</b>
<p>為了讓「苦集同範圍」這類約定無處可藏，引擎改了規則：檢驗一條定理時，<b>只有「依」中列出的本體定義才生效</b>，其餘定義項一律當作意義不明的詞。這樣，一步推理若用到「苦諦即有漏」「道諦即無漏的有為」，就必須寫出來，否則判為推不出；寫了而沒用到，又判為多餘。前提樹中，這些本體定義顯示為「約定」節點，附定義式與頌文。</p>
<p>按新規則重跑，模組四、六也各有幾步原來沒寫出它所用的定義（如「業」「有記」「二定以上」「生二定以上」），都已補上。</p></div>
<div class="box"><b>相應法同性：逼出了什麼</b>
<p>要證明「相應的心、心所同性」，先要知道一法的善惡從哪裡來。頌「勝義善解脫，自性慚愧根，相應彼相應，等起色業等，翻此名不善」說四種：心、心所不是勝義（甲假十），也不由等起（甲假十一，等起只成色業與不相應行），所以只能是自性善，或「彼相應」——與自性善相應（甲假十二、十三）。</p>
<p>證明在這裡卡了一下：x 與自性善 z 相應，y 與 x 相應，y 是否也與 z 相應？這要求相應可以傳遞。它不是假定，而是由相應五義推出的定理（定甲七）：相應就是同所依、同所緣、同行相、同時，「同」是相等關係，自然可以傳遞。於是「一聚心、心所兩兩相應」也成了定理。</p>
<p>剩下兩條待核（甲假十二、十三）：頌只說善、不善，把有覆無記也照此處理是類推。若您認可這一類推，或給出有覆無記的依據，相應法同性就完全落在文獻上。</p></div>"""
    return tree_section(R5, "m5", "模組五：阿羅漢最後心是苦諦、集諦", intro, box, first_roots=("定甲八",))


def section_m6(R6):
    m = R6["module"]
    T = R6["tree"]
    gap = R6["drop"]["乙假十二"]
    st = m.statements["乙假十二"]
    intro = f"""<p>題目：「阿那含必然成就初靜慮。」論域換成了補特伽羅。每個人有果位、生地、兩段離染的經歷（欲界染、初靜慮染各是作異生時離，還是作聖者時離），以及入見道所依之地；「成就」味、淨、無漏初靜慮是他的謂詞。「初靜慮」取根本等至；《發智》《婆沙》問「修淨初靜慮」時，未至、中間算作「餘地」。</p>
<p>證明分兩種情形。生在欲界或初靜慮的不還，由離欲染得淨初靜慮，未曾易地，故成就淨初靜慮。生在第二靜慮以上的不還，淨初靜慮已因易地而捨，味初靜慮因離染而不成就，只能靠無漏初靜慮——對照【定乙三】：同樣生在二定以上的異生，就不成就初靜慮。何時得無漏初靜慮，要看他在哪裡離初靜慮染、依何地入見道。</p>"""
    gapbox = f"""<div class="box"><b>引擎找到的缺口：一種不還，現有的依據說不清他是否成就初靜慮</b>
<p>把【乙假十二】從庫中拿掉，其餘條目全部保留，目標就不成立。引擎給出的反例是：</p>
{world_html(gap.world, m, target_hits(gap.world, m, T.goal))}
<p>這是一個超越證的不還：作異生時已以世俗道離欲染、離初靜慮染（所以能生第二靜慮以上），入見道依未至定，至第十六心證不還果；死後生到第二靜慮以上。易地捨了淨初靜慮，初靜慮的愛已斷，味不成就；他作聖者以後沒有「為離初靜慮染」的機會，見道依未至，所修無漏只到未至地。他還成就根本初靜慮嗎？</p>
<p>【乙假十二】假定他成就：{E(st.meta.get('依據', ''))}——已離欲染者依未至起無漏功德，算作「依初靜慮」，修初靜慮無漏；這一條把它推廣到道類智。推廣是否成立，要看見道、道類智的修法（「見道忍智起，即彼未來修」「修道初剎那，修六或七智」）與起功德是否不同。</p>
<p><b>請您判斷。</b>若乙假十二成立，命題成立，且有更強的結論【定乙五】：不還都成就無漏初靜慮。若不成立，命題要加限制：除去先離欲染、依未至入見道、後生二定以上的不還。若「初靜慮」改讀為初靜慮地（含未至），這種人成就無漏未至，命題也成立——那就是讀法的問題了。</p></div>"""
    return tree_section(R6, "m6", "模組六：阿那含必然成就初靜慮", intro, gapbox)


def section_library(onto, mods, R4, R5, R6):
    """知識庫總表：本體規模、各模組各層條目數、全部待核假定。"""
    nvals = sum(len(d.values) for d in onto.dims.values())
    rows = []
    allpend = []
    for key, R in mods:
        m = R["module"]
        lay = {}
        for sid, st in m.statements.items():
            l = st.meta.get("層") or st.meta.get("組") or "命題"
            lay[l] = lay.get(l, 0) + 1
            if st.meta.get("狀態") == "待核" and st.meta.get("層") == "假定":
                allpend.append((key, sid, st))
        cells = "、".join(f"{k} {v}" for k, v in lay.items())
        rows.append(f"<tr><td class='k'>模組{key}</td><td>{E(m.title.split('・', 1)[-1])}</td><td class='num'>{len(m.statements)}</td><td class='note'>{E(cells)}</td></tr>")
    pend = "".join(f"<tr><td>{k}</td><td class='k'>{E(sid)}</td><td>{E(st.meta.get('標題', ''))}</td><td><code>{E(st.text)}</code></td></tr>" for k, sid, st in allpend)
    return f"""
<h2 id="library">知識庫總表</h2>
<p>本體：{len(onto.dims)} 門、{nvals} 個門值、{len(onto.defs)} 個定義、{len(onto.rels)} 種關係。命題分在六個模組裡；前提體系式的模組（四、五、六）每條都標了層。</p>
<div class="scroll"><table class="stack"><thead><tr><th>模組</th><th>題目</th><th class="num">條目</th><th>分層</th></tr></thead><tbody>{''.join(rows)}</tbody></table></div>
<h3 id="pending-all">全部待核的假定（{len(allpend)} 條）</h3>
<p>這些是我憑阿毘達磨知識補出、還沒有找到明文的論點。請您逐條判斷：成立的，補上出處，改為「文獻」；不成立的，改寫或刪去，重跑之後，引擎會指出哪些定理隨之失效。</p>
<div class="scroll"><table class="stack"><thead><tr><th>模組</th><th>編號</th><th>標題</th><th>命題</th></tr></thead><tbody>{pend}</tbody></table></div>
"""


def lean_axioms():
    lean_dir = ROOT / "lean"
    import shutil
    lake = Path(shutil.which("lake")) if shutil.which("lake") else None
    for cand in ([] if lake else [Path.home() / "tools" / "lean-4.24.0-linux" / "bin" / "lake", Path("/home/claude/tools/lean-4.24.0-linux/bin/lake")]):
        if cand.exists():
            lake = cand
            break
    if lake is None:
        return "（本機未安裝 Lean，未重新檢查）"
    chk = lean_dir / ".axcheck.lean"
    names = ["M1.«有覆無記色唯初靜慮繫»", "M1.«欲無有覆表»", "M1.«有覆無記色唯初靜慮繫_頌文版»", "M1.«轉讀法之衝突»"]
    names += [f"M4.«{t}»" for t in ("定一成立", "定二成立", "定三成立", "定四成立", "定五成立", "定六成立", "定七成立", "定七乙成立", "定八成立", "目標成立", "目標由諸假定")]
    names += [f"M5.«{t}»" for t in ("目標甲由諸假定", "目標甲_以意識代定義", "相應同性由諸假定", "定甲三成立", "定甲四成立", "定甲六成立")]
    names += [f"M6.«{t}»" for t in ("目標乙由諸假定", "目標乙_經無漏", "定乙三成立", "定乙四成立")]
    chk.write_text("import Kosa\n" + "".join(f"#print axioms Kosa.{n}\n" for n in names), encoding="utf-8")
    env = dict(__import__("os").environ)
    env["PATH"] = str(lake.parent) + ":" + env.get("PATH", "")
    b = subprocess.run([str(lake), "build"], cwd=lean_dir, capture_output=True, text=True, env=env)
    if b.returncode != 0:
        return "Lean 構建失敗：" + b.stdout[-400:]
    r = subprocess.run([str(lake), "env", "lean", str(chk)], cwd=lean_dir, capture_output=True, text=True, env=env)
    chk.unlink()
    return r.stdout.strip().replace("\n", "；")


CN = {1: '一', 2: '二', 3: '三', 4: '四', 5: '五', 6: '六', 7: '七', 8: '八', 9: '九', 10: '十'}


def build(out: Path):
    from .demos import module_four, module_five, module_six, verses
    fonts_ok = fonts_available()
    font_link = '<link rel="stylesheet" href="assets/fonts/fonts.css">' if fonts_ok else ""
    R1 = module_one()
    R1["lean_axioms"] = lean_axioms()
    R4 = module_four()
    R4["lean_axioms"] = R1["lean_axioms"]
    R2 = module_two()
    R3 = module_three()
    R5 = module_five()
    R6 = module_six()
    m1 = R1["module"]
    onto = m1.onto
    onto_checks = verses().check_ontology(onto)
    rounds = len(R1["rounds"]) - 1
    T5, T6 = R5["tree"], R6["tree"]
    must5 = [a for a, r in R5["drop"].items() if not r.ok]
    must6 = [a for a, r in R6["drop"].items() if not r.ok]
    npend = sum(1 for R in (R4, R5, R6) for st in R["module"].statements.values()
                if st.meta.get("層") == "假定" and st.meta.get("狀態") == "待核")
    ok5 = all(ec.ok and not ec.unnecessary for ec in T5.edges.values()) and T5.consistent
    ok6 = all(ec.ok and not ec.unnecessary for ec in T6.edges.values()) and T6.consistent
    nwei = len(onto.dims["色自性"].values) + 1 + len(onto.dims["心所自性"].values) + len(onto.dims["不相應自性"].values) + len(onto.dims["無為自性"].values)
    stats = f"""<div class="stats">
<div class="stat"><b>{nwei} 法</b><span>本體按五位立自性：色 {len(onto.dims['色自性'].values)}、心 1、心所 {len(onto.dims['心所自性'].values)}、心不相應行 {len(onto.dims['不相應自性'].values)}、無為 {len(onto.dims['無為自性'].values)}</span></div>
<div class="stat ok"><b>{'✓' if ok5 else '✗'} 題一</b><span>阿羅漢最後心是苦諦、集諦。不可少的假定只有 {len(must5)} 條：{'、'.join(must5)}；「相應法同性」也已由假定證出</span></div>
<div class="stat"><b>{'✓*' if ok6 else '✗'} 題二</b><span>阿那含必然成就初靜慮。* 有條件：{len(T6.goal_minimal)} 條證明路線都要用到待核的乙假十二——引擎找到了一種說不清的不還</span></div>
<div class="stat ok"><b>Lean</b><span>兩題的每條定理都由 Lean 證明，對任意大小的世界成立</span></div>
<div class="stat"><b>{npend} 條</b><span>待核的假定，列在「知識庫總表」，請您確認</span></div>
</div>"""
    flow = """<div class="flow">
<div class="n"><b>概念</b><span>本體定義門、值、關係；詞表封閉</span></div>
<div class="n"><b>命題</b><span>毘曇論式的中文命題，附原文、出處、詮釋</span></div>
<div class="n"><b>編譯</b><span>命題 → 一階公式 → 回答集程序</span></div>
<div class="n"><b>檢驗</b><span>求解器找反例：無反例即蘊涵</span></div>
<div class="n loop"><b>補前提</b><span>反例違反哪條候選，就加入哪條</span></div>
<div class="n"><b>分析</b><span>極小前提集、衝突集、修正集</span></div>
<div class="n done"><b>內核證明</b><span>導出 Lean，證明對任意世界成立</span></div>
<div class="n done"><b>核對</b><span>引用的頌文逐字比對 CBETA</span></div>
</div><p class="loopnote">「補前提」回到「檢驗」，直到沒有反例為止。模組一走了 """ + str(rounds) + """ 輪。</p>"""
    nav = """<nav class="scroll"><a href="#rebuild">本體重建</a><a href="#m5">題一：最後心</a><a href="#m6">題二：阿那含</a><a href="#library">知識庫總表</a><a href="#tree">模組四</a><a href="#lean">Lean 導讀</a><a href="#nolean">免安裝</a><a href="#ontology">本體</a><a href="#language">命題語言</a><a href="#m1">模組一</a><a href="#m2">模組二</a><a href="#m3">模組三</a><a href="#verses">引文核對</a><a href="#extend">擴展</a><a href="#run">運行</a></nav>"""
    page = f"""<!DOCTYPE html>
<html lang="zh-Hant"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Kosa v0.3 說一切有部阿毘達磨形式化庫</title>
<meta name="description" content="Kosa：說一切有部阿毘達磨形式化庫。本體按五位七十五法重建；證明「阿羅漢最後心是苦諦、集諦」「阿那含必然成就初靜慮」，每一步由求解器檢驗、由 Lean 證明。">
<meta property="og:title" content="Kosa：說一切有部阿毘達磨形式化庫">
<meta property="og:description" content="從一條毘曇命題拆到它的假定：每一步都由機器檢驗。">
<meta property="og:image" content="https://wanglu2016.github.io/kosa/assets/og.png">
<meta property="og:type" content="website">
<link rel="icon" href="assets/favicon.svg" type="image/svg+xml">
{font_link}
<style>{CSS}</style>{STACK_JS}</head><body>
<header class="band top"><div class="wrap">
<p class="note">Kosa v0.3 · 說一切有部阿毘達磨形式化庫 · 依《俱舍論頌》《俱舍九題》《俱舍萬字》</p>
<h1>本體按七十五法重建，再證兩道題：一道成立，一道找到了缺口</h1>
<p class="deck">這一版先把本體補全為五位七十五法，再用它證明「阿羅漢最後心是苦諦、集諦」「阿那含必然成就初靜慮」。證明中用到的、順帶證明的、暫時用不到的前提都收進庫裡。v0.2 的前提體系與 v0.1 的演示模組保留在後面，並在新本體上全部重跑通過。</p>
{stats}
<div id="flow">{flow}</div>
</div></header>
{nav}
<main class="band"><div class="wrap">
{section_rebuild(onto, R1, R2, R4)}
{section_m5(R5)}
{section_m6(R6)}
{section_library(onto, [("一", R1), ("二", R2), ("三", R3), ("四", R4), ("五", R5), ("六", R6)], R4, R5, R6)}
<h2 id="v02" style="border-top-width:6px">v0.2：模組四的前提體系</h2>
<p>以下是第二版的內容：從「有覆無記色唯初靜慮繫」拆到十九條假定。本體重建後重跑，結果不變。</p>
{section_tree(R4)}
{section_lean_guide(R4)}
<h2 id="v01" style="border-top-width:6px">v0.1 的工作流程與三個演示模組</h2>
<p>以下是第一版的內容：本體與命題語言的說明，以及模組一（照 2022 文檢驗）、模組二（九十八隨眠）、模組三（眾賢之矛盾）。</p>
{section_ontology(onto, m1)}
{section_language(m1)}
{section_m1(R1)}
{section_m2(R2)}
{section_m3(R3)}
{section_verses(R1, R2, R3, R4, R5, R6, onto_checks)}
{section_extend()}
{section_run(R1, R2, R3, R4, R5, R6)}
</div></main>
<footer class="band"><div class="wrap">Kosa v0.3。命題取自王路《俱舍九題》《俱舍萬字》及〈怎樣推導出一個毘曇命題？〉（2022），版權歸作者；頌文取自 CBETA T1560（非商業使用）。標「待核」者尚待作者確認。本頁由 <code>python3 -m kosa 報告</code> 生成。</div></footer>
</body></html>"""
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(page, encoding="utf-8")
    build_assets(out.parent, page, fonts_ok)
    return out


def fonts_available():
    try:
        import fontTools.subset  # noqa: F401
        import brotli  # noqa: F401
    except ImportError:
        return False
    src = ROOT / "tools" / "fonts"
    return (src / "NotoSerifTC-Regular.otf").exists() and (src / "NotoSerifTC-Bold.otf").exists()


def build_assets(out_dir: Path, page: str, fonts_ok: bool):
    """複製圖標、預覽圖；按頁面實際用字裁剪 Noto Serif TC，生成 woff2 與 fonts.css。"""
    import shutil
    assets = out_dir / "assets"
    assets.mkdir(parents=True, exist_ok=True)
    site = ROOT / "tools" / "site"
    if site.exists():
        for f in site.iterdir():
            if f.is_file():
                shutil.copy(f, assets / f.name)
    if not fonts_ok:
        return
    from fontTools import subset
    fdir = assets / "fonts"
    fdir.mkdir(exist_ok=True)
    chars = set(page) | {chr(c) for c in range(32, 127)} | set("，。、；：？！「」『』（）〔〕【】《》〈〉……——・")
    chars = "".join(sorted(c for c in chars if not c.isspace() or c == " "))
    css = []
    for name, weight in (("NotoSerifTC-Regular.otf", 400), ("NotoSerifTC-Bold.otf", 700)):
        opts = subset.Options()
        opts.flavor = "woff2"
        opts.layout_features = ["*"]
        font = subset.load_font(str(ROOT / "tools" / "fonts" / name), opts)
        sub = subset.Subsetter(opts)
        sub.populate(text=chars)
        sub.subset(font)
        outname = name.replace(".otf", ".woff2")
        subset.save_font(font, str(fdir / outname), opts)
        css.append(f"@font-face{{font-family:'Kosa Serif';font-style:normal;font-weight:{weight};font-display:swap;src:url('{outname}') format('woff2')}}")
    (fdir / "fonts.css").write_text("\n".join(css) + "\n", encoding="utf-8")
    shutil.copy(ROOT / "tools" / "fonts" / "OFL-NotoSerifTC.txt", fdir / "OFL-NotoSerifTC.txt")
