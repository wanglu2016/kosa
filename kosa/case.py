"""案例頁「三道題」：從不用庫的解答，到題網、補庫、推導檢驗與 Lean 證明。

報告（python3 -m kosa 報告）生成 報告/three-questions.html，附結構計算的結果；
python3 -m kosa 案例 單獨生成同一頁（不算結構，幾十秒），供本機預覽。
頁中的命題、頌、依、題網結果、判定示例與 Lean 代碼，都在生成時從庫中讀出或當場計算，
所以庫改了，頁面跟著改；只有解答與說明的文字寫在本文件裡。
"""
from __future__ import annotations

import html
import re
from contextlib import suppress
from pathlib import Path
from urllib.parse import quote

from .demos import ROOT

E = html.escape
PAGE = "three-questions.html"
BANK = ROOT / "題庫" / "三道題.kosa"
PROOF = ROOT / "lean" / "Kosa" / "Proof7.lean"
WEBLINK = ROOT / "lean" / "網頁版" / "連結・三道題.txt"
GH = "https://github.com/wanglu2016/kosa/blob/main/"

# 每道題：本輪補進本體的條目（文件, 首行開頭）與命題庫條目；答案條目（有 Lean 證明）
Q = {
    "一": dict(onto=[("定義.kosa", "定義 意業")], base=["根品24"], ans=["業品26", "業品27"]),
    "二": dict(onto=[("門.kosa", "門 律儀種"), ("門.kosa", "門 律儀類"), ("門.kosa", "門 根律儀"),
                    ("定義.kosa", "定義 諸律儀")],
              base=["業品28", "業品29", "業品30"], ans=["業品31", "業品32", "業品33", "業品34"]),
    "三甲": dict(onto=[("門.kosa", "門 依地"), ("定義.kosa", "定義 初靜慮地"), ("定義.kosa", "定義 第三靜慮地"),
                      ("定義.kosa", "定義 非想非非想處地"), ("定義.kosa", "定義 樂根")],
                base=["界品57", "界品58", "根品25", "根品26", "定品13"], ans=["根品27", "根品28"]),
    "三乙": dict(onto=[("關係.kosa", "關係 成就")],
                base=["賢聖品7", "賢聖品8", "賢聖品9", "賢聖品10", "賢聖品11"], ans=["賢聖品12"]),
}
NEW_DIMS, NEW_RELS = 4, 1          # 本輪新立的門、關係（律儀種、律儀類、根律儀、依地；成就）

YUN = ["色蘊", "受蘊", "想蘊", "行蘊", "識蘊"]
CHU = ["眼處", "耳處", "鼻處", "舌處", "身處", "意處", "色處", "聲處", "香處", "味處", "觸處", "法處"]
JIE = ["眼界", "耳界", "鼻界", "舌界", "身界", "意界", "色界（十八界）", "聲界", "香界", "味界", "觸界", "法界",
       "眼識界", "耳識界", "鼻識界", "舌識界", "身識界", "意識界"]
DI = ["欲界地", "初靜慮地", "第二靜慮地", "第三靜慮地", "第四靜慮地", "空無邊處地", "識無邊處地", "無所有處地", "非想非非想處地"]
SHENG = ["生欲界", "生初靜慮", "生第二靜慮", "生第三靜慮", "生第四靜慮", "生空無邊處", "生識無邊處", "生無所有處", "生非想非非想處"]

DEMOS = [
    ("受蘊・諸律儀 容有", "受蘊裡有沒有律儀？只用本體（門的適用條件）就判為證否。"),
    ("凡 x：樂受(x) ⇒ 欲界地(x) 或 初靜慮地(x)", "一個常見的錯答：漏了第三靜慮。引擎判為證否，並指出用的是定品13（第三靜慮地有樂受）。"),
    ("有 p、x：生空無邊處(p) 且 異生(p) 且 樂根(x) 且 成就(p，x)", "生無色界的異生成就樂根嗎？證否，依據是賢聖品11（頌「愚生無色界，成善命意捨」）。"),
    ("有 p、x：生第二靜慮(p) 且 異生(p) 且 樂根(x) 且 成就(p，x)",
     "庫還答不了的題。引擎如實判為未決，並給出一個它成立的世界——那個異生成就的是無漏第三靜慮的樂受。"
     "異生不可能成就無漏有為法，這個荒唐的實例正好說明庫還缺「異生不成就道諦」一類命題：下一步補甚麼，由此可見。"),
]


def gh(path):
    return GH + quote(path)


def onto_entry(fname, head):
    """本體文件中以 head 開頭的條目：(首行, {欄: 值})。"""
    lines = (ROOT / "本體" / fname).read_text(encoding="utf-8").splitlines()
    for i, l in enumerate(lines):
        if l.startswith(head):
            meta, last = {}, None
            for l2 in lines[i + 1:]:
                if not l2.startswith("　"):
                    break
                if l2.startswith("　　") and last:
                    meta[last] += l2.strip()
                    continue
                k, _, v = l2[1:].partition("：")
                meta[k], last = v, k
            return l, meta
    raise KeyError(head)


def verses(s):
    return "".join(f"「{E(v.strip())}」" for v in s.split("；") if v.strip())


def lean_block(src, name):
    """Proof7.lean 中定理（或引理）name 的整段，連同它上面的文檔註釋。"""
    i = src.index(f"theorem «{name}»")
    j = src.rfind("/--", 0, i)
    start = j if j != -1 and "theorem «" not in src[j:i] else i
    ends = [k for k in (src.find(p, i + 1) for p in ("\n/--", "\n/-!", "\nend Kosa", "\ntheorem ")) if k != -1]
    return src[start:min(ends)].rstrip()


def lean_names(src):
    return re.findall(r"^theorem «(.+?)»", src, re.M)


def entry_card(lib, sid, S=None, show_deps=True):
    st = lib.statements[sid]
    meta = st.meta
    kind = ""
    if S is not None:
        with suppress(Exception):
            x = S.entry(sid)
            kind = x.role
    cls = "round ok" if kind == "推出" else "round base"
    bits = []
    if meta.get("頌"):
        bits.append("頌：" + verses(meta["頌"]))
    if meta.get("出處"):
        bits.append("出處：" + E(meta["出處"]))
    if show_deps and meta.get("依"):
        bits.append("依：" + E(meta["依"]))
    if kind:
        role = ("機器計算：<b class='ok'>推出</b>" if kind == "推出"
                else "機器計算：<b>施設</b>（不能由庫中其餘條目推出）")
        bits.append(role)
    expl = f"<p class='note'>詮釋：{E(meta['詮釋'])}</p>" if meta.get("詮釋") else ""
    return (f"<div class='{cls}'><h4>【{E(sid)}】{E(meta.get('標題', ''))}</h4>"
            f"<p><code>{E(st.text)}</code></p><p class='note'>{'　·　'.join(bits)}</p>{expl}</div>")


def onto_card(fname, head):
    first, meta = onto_entry(fname, head)
    bits = []
    if meta.get("頌"):
        bits.append("頌：" + verses(meta["頌"]))
    if meta.get("出處"):
        bits.append("出處：" + E(meta["出處"]))
    say = f"<p class='note'>{E(meta['說明'])}</p>" if meta.get("說明") else ""
    return (f"<div class='round base'><h4>本體 · <a href='{gh('本體/' + fname)}'>{E(fname)}</a></h4>"
            f"<p><code>{E(first)}</code></p>{say}<p class='note'>{'　·　'.join(bits)}</p></div>")


def chips(V, sids, names):
    out = []
    for sid, name in zip(sids, names):
        v = V[sid]
        ans = v.expected
        mark = "✓" if v.match == "一致" else ("？" if v.match == "未決" else "✗")
        cls = "chip blue" if ans in ("有", "成立") else "chip"
        out.append(f"<span class='{cls}' title='{E(sid)}：判定 {E(v.verdict)}'>{E(name)}　{E(ans)} {mark}</span>")
    return "".join(out)


def bank_table(V, sids, lib_m):
    rows = []
    for sid in sids:
        v = V[sid]
        st = lib_m.statements[sid]
        rows.append(f"<tr><td><code>{E(st.text)}</code></td><td>{E(v.expected)}</td><td>{E(v.verdict)}</td>"
                    f"<td class='{'ok' if v.match == '一致' else 'bad'}'>{E(v.match)}</td></tr>")
    return ("<table class='stack'><thead><tr><th>題網中的命題</th><th>答</th><th>庫的判定</th><th>比對</th></tr></thead>"
            f"<tbody>{''.join(rows)}</tbody></table>")


def demo_html(text, comment):
    from .judge import judge_text
    from .render import world_lines
    m, J, x = judge_text(text)
    body = [f"<p><code>python3 -m kosa 判定 \"{E(text)}\"</code></p>", f"<p class='note'>{E(comment)}</p>"]
    out = [f"判定：{x.verdict}"]
    if x.verdict in ("證成", "證否"):
        out.append("極小前提：" + ("、".join(x.premises) if x.premises else "（由本體定義直接得出）"))
        for s in x.premises:
            st = m.statements[s]
            out.append(f"  【{s}】{st.text}")
    elif x.verdict == "未決":
        out.append("命題庫推不出它，也推不出它的否定。它成立的世界：")
        out += ["  " + l for l in world_lines(x.example, m)]
    body.append("<pre>" + E("\n".join(out)) + "</pre>")
    cls = "round ok" if x.verdict != "未決" else "round"
    return f"<div class='{cls}'>{''.join(body)}</div>"


CSS_EXTRA = """
.round.base{border-left-color:var(--ink)}
.answer{border:1px solid var(--rule);background:var(--panel);padding:4px 20px 12px;margin:16px 0}
.answer h3{margin-top:1em}
.qa{font-size:19px;font-weight:700;color:var(--blue)}
.verse{font-weight:700}
ol.steps>li{margin:8px 0}
.lede{font-size:18px}
pre code{background:none;padding:0}
.toc a{white-space:nowrap}
"""

PART1 = """
<p class="note">以下是 Claude 在<b>不查命題庫</b>的情況下，只憑阿毘達磨知識給出的解答，引頌按《俱舍論頌》（CBETA T1560）。這一步與一位研習者自己作答無異：先找頌，再把散在各品的背景拼起來。</p>

<div class="answer">
<h3>一、五識俱思是意業嗎？</h3>
<p class="qa">答：是。</p>
<ol class="steps">
<li><b>意業的自性就是思。</b>頌：<span class="verse">「世別由業生，思及思所作，思即是意業，所作謂身語」</span>。業分兩種：思，與思所作。思就是意業；思所作的，是身業、語業。所以判斷一法是不是意業，只看它的自性是不是思。</li>
<li><b>五識起時必有思相應。</b>思是大地法，頌：<span class="verse">「受想思觸欲，慧念與作意，勝解三摩地，遍於一切心」</span>。眼等五識也是心，所以五識起時，必有思與之相應。這個思，按上一條，就是意業。</li>
<li><b>不看與哪一識相應。</b>「意業」的界定只問自性是不是思，不問這個思與第六意識相應，還是與前五識相應。《俱舍九題》頁 47–49 也明說：不論與意識相應還是與前五識相應，思都是意業。</li>
<li><b>容易混淆的一點。</b>頌：<span class="verse">「見斷識唯轉，唯隨轉五識，修斷意通二」</span>：五識只作剎那等起（隨轉），不能作因等起（轉）去發動身語表業。但這說的是五識能不能「發起」身語業；五識俱思「是不是」意業，是另一個問題。五識俱思不發動身語表業，它自身仍是意業。</li>
</ol>

<h3>二、哪些蘊處界中沒有任何律儀？</h3>
<p class="qa">答：受、想、識三蘊；十二處中除法處以外的十一處；十八界中除法界以外的十七界。<br>有律儀的是：色蘊、行蘊、法處、法界。</p>
<ol class="steps">
<li><b>「律儀」有兩類。</b>
<ul>
<li>無表的律儀。頌：<span class="verse">「無表三律儀，不律儀非二」「律儀別解脫，靜慮及道生」</span>。無表分律儀、不律儀、非律儀非不律儀三種；律儀又分別解脫、靜慮、道生三種。這一類的體是無表色。</li>
<li>意根律儀。頌：<span class="verse">「正知正念合，名意根律儀」</span>。經中守護根門的根律儀，有部以正知、正念為體：正知是慧，正念是念，都是心所。</li>
</ul>
題目問「任何律儀」，兩類都要算。</li>
<li><b>兩類各屬何蘊處界。</b>無表色是色，屬色蘊；它不是五根、五境，在十二處、十八界中屬法處、法界。慧、念是心所，受、想以外的心所屬行蘊；在處、界中也屬法處、法界。</li>
<li><b>逐一看。</b>
<ul>
<li>五蘊：色蘊有（無表律儀），行蘊有（意根律儀）；受蘊、想蘊沒有（正知、正念不是受、想），識蘊沒有（心王既不是心所，也不是色）。</li>
<li>十二處：只有法處有；眼等五根處、色等五境處、意處都沒有。</li>
<li>十八界：只有法界有；五根界、五境界、意界、六識界，共十七界都沒有。</li>
</ul></li>
<li><b>另一種讀法。</b>若「律儀」只指無表的律儀，行蘊就也沒有律儀，答案成了「受、想、行、識四蘊」，處、界不變。兩種讀法只在行蘊上有分歧；題說「任何」，取前一種。</li>
</ol>

<h3>三、幾地有樂受？生幾地容成就樂根？</h3>
<p class="qa">答：三地有樂受：欲界、初靜慮、第三靜慮。生九地都容成就樂根。</p>
<p><b>（甲）幾地有樂受</b></p>
<ol class="steps">
<li><b>樂受是甚麼。</b>頌：<span class="verse">「身不悅名苦，即此悅名樂，及三定心悅，餘處此名喜」</span>。樂受有兩種：身受之悅（與身識相應），以及第三靜慮的心悅（與意識相應）。其餘地方的心悅不名樂，名喜。</li>
<li><b>身識只在欲界、初靜慮。</b>頌：<span class="verse">「五識唯尋伺，後三三餘無」</span>：五識唯有尋伺，而第二靜慮以上無尋無伺，所以五識只在欲界與初靜慮。與身識相應的樂受也就只在這兩地。</li>
<li><b>加上第三靜慮的心悅，</b>有樂受的是欲界、初靜慮、第三靜慮三地。印證：<span class="verse">「生靜慮從初，有喜樂捨受，及喜捨樂捨，唯捨受如次」</span>——初靜慮有喜、樂、捨，第二靜慮有喜、捨，第三靜慮有樂、捨，第四靜慮唯捨；無色界唯捨。</li>
<li><b>無漏的樂受也不出這三地。</b>五識唯有漏（頌<span class="verse">「意法意識通，所餘唯有漏」</span>），身識不起無漏受；無漏的樂受只有依第三靜慮的意識之悅。</li>
<li><b>「地」指受所繫屬（無漏則所依）的地，不是有情所生的地。</b>生在第二靜慮的有情，可以起初靜慮繫的眼、耳、身識；這時若有樂受，屬初靜慮地。</li>
</ol>
<p><b>（乙）生幾地容成就樂根</b></p>
<ol class="steps">
<li><b>成就不同於現起、繫屬。</b>頌：<span class="verse">「得謂獲成就，非得此相違」</span>。成就是有其得而未捨，不必現前，也不必是所生之地繫屬的法。所以「生某地成就樂根」和「某地有樂受」是兩個問題。</li>
<li><b>欲界：</b>生欲界的有情必成就樂根。頌：<span class="verse">「極少八無善，成受身命意」</span>——連斷了善根、成就根最少的欲界有情，也成就五受根（其中有樂根）與身、命、意，共八根。</li>
<li><b>上八地：</b>聖者必成就樂根。頌：<span class="verse">「二無漏十一，初無漏十三」</span>——成就已知根或具知根的，至少成就十一根；成就未知當知根的，至少十三根；兩種都含樂根。三無漏根依意、樂、喜、捨、信、勤、念、定、慧九根而立（頌<span class="verse">「見修無學道，依九立三根」</span>），聖者成就無漏的樂根。而色界四地、無色界四地都有聖者受生：頌<span class="verse">「上流若雜修，能往色究竟，超半超遍歿，餘能往有頂，行無色有四，住此般涅槃」</span>。</li>
<li><b>所以生九地都容有成就樂根的有情：</b>答九地。</li>
<li><b>但不是生九地的一切有情都成就。</b>頌：<span class="verse">「愚生無色界，成善命意捨」</span>——生無色界的異生只成就信等五根、命、意、捨，不成就樂根。生無色界而成就樂根的，唯是聖者。</li>
</ol>
<p><b>兩問合看。</b>樂受只在三地，成就樂根卻遍九地。差別正在「繫屬、現起」與「成就」之分：無色界的聖者沒有一剎那樂受現起，卻成就無漏的樂根。</p>
</div>
"""

LESSONS = """
<ol class="steps">
<li><b>難在讀法，不在證明。</b>三道題各有一個讀法上的陷阱：第一題要防空真（「凡五識俱思皆是意業」在沒有五識俱思的世界裡也成立，所以要另證「有五識俱思」）；第二題「任何律儀」要收進意根律儀，否則行蘊的答案相反；第三題「有樂受」與「成就樂根」是兩回事。讀對以後，九條 Lean 證明一次通過。這些讀法寫進了 skill 的讀法凡例（讀十六至十九），以後的題照它讀。</li>
<li><b>庫缺的主要是框架，不是命題。</b>本輪補了 4 個門、1 個關係、十餘條定義，命題倒是其次。第二題的 35 格，補上律儀的門和「只有甚麼法在此門取值」的適用條件以後，「沒有律儀」的 31 格完全由本體推出，不需要一條命題。門分得好、適用條件寫全，大批門分別命題就不必再逐條寫：這是把庫建成基礎設施最省力的方向。</li>
<li><b>題網是對的單位。</b>一個問題拆成對每一項「有沒有」，既是答案的嚴格形式，又永久留在題庫裡做回歸檢驗。以後無論誰改庫，只要哪一格不再一致，CI 就會標紅。</li>
<li><b>求解器與 Lean 分工。</b>求解器快，能給反例和「還缺甚麼」，但它只窮盡有限世界（5 個法、2 個有情）。第三題乙要 9 個有情，求解器的世界裝不下，本輪還因此發現並修好一個「前提整體不可滿足、推導空真通過」的漏洞。Lean 沒有這個界限，所以重要的推出都要有 Lean 證明。</li>
<li><b>機器核對頌文。</b>Claude 憑記憶引頌，本輪又錯了兩處（「應知諸無表，律不律俱非」實為「無表三律儀，不律儀非二」；另一處把「唯隨轉五識，修斷意通二」記成了別的句子）。入庫時與 CBETA 逐字核對，當場發現。</li>
<li><b>不為一題特設。</b>每補一條都問：別的題也會用到它嗎？本輪補的律儀三門、九地定義、成就關係，都是以後二十二根、諸心、得捨會反復用到的背景。有兩條眼下是按頌的粒度寫的施設（「聖者必成就樂根」「樂受或在第三靜慮、或與身識相應」），等做完二十二根，應能變成推出。</li>
</ol>
"""


def build_case(lib=None, S=None, out: Path | None = None):
    from .demos import load_library
    from .judge import run_bank
    from .report import CSS, STACK_JS
    lib = lib or load_library()
    bm, J, results, groups = run_bank(BANK)
    V = {v.sid: v for v in results}
    n_ok = sum(v.match == "一致" for v in results)
    src = PROOF.read_text(encoding="utf-8")
    names = lean_names(src)
    main_thms = [n for n in names if n.endswith("成立")]
    lemmas = [n for n in names if not n.endswith("成立")]
    weblink = WEBLINK.read_text(encoding="utf-8").strip() if WEBLINK.exists() else ""
    n_base = sum(len(q["base"]) + len(q["ans"]) for q in Q.values())

    def lean(nm):
        return f"<pre><code>{E(lean_block(src, nm))}</code></pre>"

    def part(key):
        q = Q[key]
        return ("".join(onto_card(f, h) for f, h in q["onto"]) + "".join(entry_card(lib, s, S) for s in q["base"]))

    def answers(key):
        return "".join(entry_card(lib, s, S) for s in Q[key]["ans"])

    stats = f"""<div class="stats">
<div class="stat ok"><b>{n_ok}／{len(results)}</b><span>題網的格子，命題庫逐格判定，全部與解答一致</span></div>
<div class="stat ok"><b>{len(main_thms)} 條</b><span>答案命題的 Lean 定理（另有 {len(lemmas)} 條小引理），GitHub 上自動編譯通過</span></div>
<div class="stat"><b>{NEW_DIMS} 門 · {NEW_RELS} 關係</b><span>為這三道題新立的本體；另有十餘條定義</span></div>
<div class="stat"><b>{n_base} 條</b><span>新入庫的命題，每條引頌、記出處</span></div>
</div>"""
    nav = """<nav class="scroll toc"><a href="index.html">← 報告首頁</a><a href="#flow">做法</a><a href="#part1">第一部分：解答</a><a href="#q1">第一題</a><a href="#q2">第二題</a><a href="#q3">第三題</a><a href="#demo">試一試</a><a href="#lessons">經驗</a><a href="#files">文件</a></nav>"""
    flow = """<div class="flow">
<div class="n"><b>出題</b><span>作者給三道題</span></div>
<div class="n"><b>解答</b><span>不用庫，按阿毘達磨作答、引頌</span></div>
<div class="n"><b>讀法</b><span>把題讀成嚴格命題，定量詞與範圍</span></div>
<div class="n"><b>題網</b><span>拆成逐項「有沒有」的格子，入題庫</span></div>
<div class="n loop"><b>補庫</b><span>判不出的格子告訴你缺甚麼：補門、定義、命題</span></div>
<div class="n"><b>推導</b><span>答案條目寫「依」，機器檢驗推得出、缺一不可</span></div>
<div class="n done"><b>Lean</b><span>寫證明，GitHub 上自動編譯；檢驗只用了「依」</span></div>
</div>
<p class="loopnote">「補庫」一步反復做，直到每一格都判得出、與解答一致。</p>"""

    V2 = lambda grp, lst: [f"二·{grp}·{x}" for x in lst]  # noqa: E731
    q2grid = f"""<table class="stack"><tbody>
<tr><th class="k">五蘊</th><td>{chips(V, V2('蘊', YUN), YUN)}</td></tr>
<tr><th class="k">十二處</th><td>{chips(V, V2('處', CHU), CHU)}</td></tr>
<tr><th class="k">十八界</th><td>{chips(V, V2('界', JIE), JIE)}</td></tr>
</tbody></table>
<p class="note">每格是一條命題「X・諸律儀 容有」。藍色為「有」；✓ 表示命題庫的判定與解答一致。</p>"""
    q3a = chips(V, [f"三甲·{d}" for d in DI], DI)
    q3b = chips(V, [f"三乙·{s}" for s in SHENG], SHENG)
    q1t = bank_table(V, ["一·五識俱思是意業", "一·有五識俱思"], bm)
    q3bx = bank_table(V, ["三乙·無色異生不成就"], bm)

    lean_web = (f"<p>想親手跑一遍：<a href='{E(weblink)}'>在瀏覽器裡打開 Lean（live.lean-lang.org）</a>，"
                "頁面會載入庫的全部定義與本頁的證明，在對方伺服器上編譯，不必安裝任何軟件。</p>") if weblink else ""
    demos = "".join(demo_html(t, c) for t, c in DEMOS)
    files = [("題庫/三道題.kosa", "三道題的題網（56 格）"), ("lean/Kosa/Proof7.lean", "三道題的 Lean 證明"),
             ("本體/門.kosa", "門：律儀種、律儀類、根律儀、依地"), ("本體/定義.kosa", "定義：諸律儀、九地、五受根"),
             ("本體/關係.kosa", "關係：成就（有情，法）"), ("庫/業品.kosa", "業品26–34"), ("庫/根品.kosa", "根品24–28"),
             ("庫/界品.kosa", "界品57–58"), ("庫/定品.kosa", "定品13"), ("庫/賢聖品.kosa", "賢聖品7–12"),
             (".claude/skills/kosa-formalize/references/讀法凡例.md", "讀法凡例（讀十六至十九是本輪新增）")]
    filelist = "".join(f"<li><a href='{gh(p)}'><code>{E(p)}</code></a>　{E(d)}</li>" for p, d in files)
    note_s = ("" if S is not None else
              "<p class='note'>（本機預覽版：未附結構計算。線上版在每條命題下注明它是施設還是推出。）</p>")

    page = f"""<!DOCTYPE html>
<html lang="zh-Hant"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>案例：三道題——從解答到機器證明 · Kosa</title>
<meta name="description" content="Kosa 案例：三道阿毘達磨題，先不用庫作答，再寫成嚴格命題、補庫，直到求解器逐格判定一致、Lean 證明通過。">
<meta property="og:title" content="Kosa 案例：三道題——從解答到機器證明">
<meta property="og:description" content="五識俱思是意業嗎？哪些蘊處界中沒有任何律儀？幾地有樂受，生幾地容成就樂根？">
<meta property="og:image" content="https://wanglu2016.github.io/kosa/assets/og.png">
<link rel="icon" href="assets/favicon.svg" type="image/svg+xml">
<link rel="stylesheet" href="assets/fonts/fonts.css">
<style>{CSS}{CSS_EXTRA}</style>{STACK_JS}</head><body>
<header class="band top"><div class="wrap">
<p class="note">Kosa · 說一切有部阿毘達磨形式化庫 · 案例</p>
<h1>三道題：從解答到機器證明</h1>
<p class="deck">作者出了三道題。Claude 先不用庫，按阿毘達磨作答；再把答案寫成嚴格命題，庫判不出就補庫，直到命題庫逐格判定與解答一致、Lean 證明通過。本頁記錄全過程，也示範 Kosa 怎樣用。</p>
<ol class="lede">
<li>五識俱思是意業嗎？</li>
<li>哪些蘊處界中沒有任何律儀？</li>
<li>幾地有樂受？生幾地容成就樂根？</li>
</ol>
{stats}
</div></header>
{nav}
<main class="band"><div class="wrap">
{note_s}
<h2 id="flow">做法：以題養庫</h2>
<p>Kosa 的命題庫是一個不斷生長的基礎設施。拿一道題來，先照研習者的辦法解答；再看庫能不能獨立判出同樣的答案。判不出，說明庫缺了背景，就補——補的應是以後別的題也用得著的框架（門、定義、按論書粒度寫的命題），不是為這一題特設的捷徑。</p>
{flow}

<h2 id="part1">第一部分：不用庫，先按阿毘達磨解答</h2>
{PART1}

<h2 id="part2">第二部分：形式化與機器證明</h2>
<p>每道題走同樣幾步：<b>讀法</b>（把題讀成嚴格命題）、<b>題網</b>（拆成逐項的格子，入題庫）、<b>補庫</b>（庫判不出就補）、<b>推導</b>（答案條目寫明所依，機器檢驗）、<b>Lean 證明</b>。下面的命題、頌文、所依與判定結果，都是生成本頁時從庫中讀出、當場計算的。</p>
<p class="note">怎樣讀 Kosa 命題：<code>凡 x：A(x) ⇒ B(x)</code> 讀作「凡是 A 的法都是 B」；<code>有 x：…</code> 讀作「有一法……」；<code>A 唯 B</code> 即「A 都是 B」，<code>A 非 B</code> 即「A 都不是 B」，<code>A・B 容有</code> 即「有既是 A 又是 B 的」；<code>相應(x，y)</code>、<code>成就(p，x)</code> 是關係。<code>p</code> 一類變元指有情，<code>x、y</code> 指法。</p>

<h3 id="q1">第一題　五識俱思是意業嗎？</h3>
<p><b>讀法。</b>「是不是」要寫成兩條：全稱的「凡與五識相應的思都是意業」，和存在的「確有與五識相應的思」。只寫前一條，它在一個沒有五識俱思的世界裡也空洞地成立，等於甚麼也沒說。（讀法凡例讀十九）</p>
<p><b>題網</b>只有兩格：</p>
{q1t}
<p><b>補庫。</b>「意業：思」的定義庫中早有（取自《俱舍九題》）。缺的是「凡心皆有思相應」。大地法有十個，這裡只寫了思：求解器的世界只有 5 個法，一個心連十個大地法就有 11 個法，裝不下。其餘九個等用到時逐條加。</p>
{part('一')}
<p><b>推導與證明。</b>業品26 只依「意業」的定義，一步得出；業品27 依「凡心皆有思相應」與「六識各容有」，再用相應關係的對稱性。</p>
{answers('一')}
{lean('業品26成立')}
{lean('業品27成立')}

<h3 id="q2">第二題　哪些蘊處界中沒有任何律儀？</h3>
<p><b>讀法。</b>「任何律儀」取最廣的意義：無表的律儀，加上以正知、正念為體的意根律儀。庫中為此立一條定義「諸律儀：律儀或意根律儀」。若只取無表律儀，行蘊的答案就反過來了（讀法凡例讀十六）。</p>
<p><b>題網：</b>五蘊、十二處、十八界逐一問「其中有沒有律儀」，共 35 格。</p>
{q2grid}
<p><b>補庫。</b>庫裡原來沒有「律儀」這個詞。立三個門：律儀種（無表的三種）、律儀類（律儀的三種）、根律儀；關鍵是它們的<b>適用類</b>：律儀種只對無表色取值，根律儀只對慧、念取值。再立三條存在命題（三種律儀各有、意根律儀有）。</p>
{part('二')}
<p><b>推導與證明。</b>這一題最能說明「框架比命題重要」：業品31–33（31 格「沒有」）的「依」裡<b>只有本體</b>——門的互斥與適用條件，沒有一條命題。一法若有律儀，它要麼是無表色（色），要麼是慧、念（心所）；受、想、識、五根、五境、意處、六識界都不是這兩種。Lean 中先證這條「諸律儀之體」，四條定理都由它推出。</p>
{answers('二')}
{lean('諸律儀之體')}
{lean('業品31成立')}
{lean('業品34成立')}

<h3 id="q3">第三題　幾地有樂受？生幾地容成就樂根？</h3>
<p><b>讀法。</b>兩問要分開讀。「某地有樂受」問的是樂受<b>繫屬</b>（無漏則<b>依</b>）哪一地，與有情生在哪裡無關；「生某地容成就樂根」問的是有沒有一個生在該地的有情<b>成就</b>某個樂根，是有情與法之間的關係（讀法凡例讀十七、十八）。若把「成就」讀成「現起」或「繫屬」，第二問就會錯答三地。</p>
<p><b>題網（甲）：</b>九地逐一問「X地・樂受 容有」。</p>
<p>{q3a}</p>
<p><b>補庫（甲）。</b>庫中原來只有「繫」，無漏法不繫，問「某地有沒有」時會被漏掉。於是立「依地」門（只對無漏有為法取值），九地各定義為「X繫或無漏X」。命題補了五識唯有伺、唯有漏，以及按頌寫的「樂受或在第三靜慮，或與身識相應」。</p>
{part('三甲')}
<p><b>推導與證明（甲）。</b>樂受若不在第三靜慮，就與身識相應；身識是五識，唯有伺、唯有漏，所以只在欲界或初靜慮；相應的心、心所同地，於是樂受也在欲界或初靜慮。其餘六地沒有樂受，則由九地定義兩兩相違得出：同是繫屬的地，地不同；一是繫屬、一是無漏所依，無漏者不繫，與有繫相違。</p>
{answers('三甲')}
{lean('根品27成立')}
{lean('根品28成立')}
<p><b>題網（乙）：</b>九個生地逐一問「有沒有生在此地、成就樂根的有情」，另加一格「生無色界的異生不成就樂根」。</p>
<p>{q3b}</p>
{q3bx}
<p><b>補庫（乙）。</b>立「成就（有情，法）」關係，讓有情與法在同一個世界裡；按頌補五條命題：生欲界者必成就樂根、聖者必成就樂根、有生欲界者、上八地各有聖者、無色界異生不成就樂根。</p>
{part('三乙')}
<p><b>推導與證明（乙）。</b>這一條要九個有情，求解器只有兩個有情的位置，裝不下；引擎把前提中的存在命題拆開逐條考，才判得出。Lean 沒有這個界限，直接證出。</p>
{answers('三乙')}
{lean('賢聖品12成立')}
{lean_web}

<h2 id="demo">試一試：判定一條命題</h2>
<p>任何一條用庫中詞彙寫成的命題，都可以交給引擎判定。結果有三種：<b>證成</b>（附極小前提），<b>證否</b>（附推出其否定的極小前提），<b>未決</b>（庫推不出它，也推不出它的否定；附一個它成立的世界）。下面四條是當場計算的結果。</p>
{demos}

<h2 id="lessons">經驗：怎樣讓後面的證明越來越容易</h2>
{LESSONS}

<h2 id="files">文件</h2>
<ul>{filelist}</ul>
<p>自己運行：</p>
<pre><code>git clone https://github.com/wanglu2016/kosa && cd kosa
pip install clingo fonttools brotli lzstring
python3 -m kosa 題庫        # 判定全部題庫，含本頁的 56 格
python3 -m kosa 判定 "受蘊・諸律儀 容有"
python3 -m kosa 驗證        # 頌文核對、推導檢驗、全庫相容、題庫</code></pre>
</div></main>
<footer class="band"><div class="wrap">Kosa · 案例頁。命題取自王路《俱舍九題》《俱舍萬字》，版權歸作者；頌文取自 CBETA T1560（非商業使用）。形式化與證明由 Claude（Anthropic）完成。本頁由 <code>python3 -m kosa 報告</code> 生成。</div></footer>
</body></html>"""
    if out is not None:
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(page, encoding="utf-8")
    return page
