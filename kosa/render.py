"""把世界（模型）寫成中文。"""
from __future__ import annotations
import html

REL_READ = {
    "相應": "{a} 與 {b} 相應",
    "剎那等起": "{a} 以 {b} 為剎那等起（隨轉）",
    "因等起": "{a} 以 {b} 為因等起（轉）",
    "先於": "{a} 先於 {b}",
}

# 展示次序：先說是甚麼法，再說分別
ORDER = ["果位", "生地", "欲染", "初靜慮染", "見道依地",
         "法類", "色自性", "表非表", "六識", "心所自性", "見種", "五受", "不相應自性", "無為自性",
         "繫不繫", "界", "性", "斷非斷", "見諦", "有漏無漏", "門轉", "有伺無伺", "定散"]


def ent_desc(e, module):
    if module.sorts[e.sort].kind == "固定":
        parts = [e.label]
        if e.preds:
            parts.append("・".join(sorted(e.preds, key=lambda p: list(module.preds).index(p))))
        return parts
    vals = []
    for d in ORDER + [k for k in e.attrs if k not in ORDER]:
        v = e.attrs.get(d)
        if v and v != "—":
            vals.append(v)
    for p in module.preds:
        if p in e.preds:
            vals.append(p)
    return vals


def world_lines(world, module, only_sort=None):
    out = []
    for e in world.ents:
        if only_sort and e.sort != only_sort:
            continue
        if module.sorts[e.sort].kind == "開放":
            out.append(f"{e.label}：" + "・".join(ent_desc(e, module)))
    seen = set()
    label = {e.key: e.label for e in world.ents}
    for r, a, b in sorted(world.rels):
        if r in module.order_rels:
            continue
        sym = r in module.onto.rels and module.onto.rels[r].symmetric
        key = (r, frozenset((a, b))) if sym else (r, a, b)
        if key in seen:
            continue
        seen.add(key)
        out.append(REL_READ.get(r, "{r}({a}，{b})").format(a=label[a], b=label[b], r=r))
    return out


def world_html(world, module, highlight=()):
    rows = []
    for e in world.ents:
        if module.sorts[e.sort].kind != "開放":
            continue
        cls = ' class="hit"' if e.key in highlight else ""
        cells = "".join(f'<span class="tag">{html.escape(v)}</span>' for v in ent_desc(e, module))
        rows.append(f'<tr{cls}><th>{e.label}</th><td>{cells}</td></tr>')
    rels = [l for l in world_lines(world, module) if "：" not in l]
    rel_html = "".join(f"<li>{html.escape(l)}</li>" for l in rels)
    return (f'<table class="world">{"".join(rows)}</table>'
            + (f'<ul class="rels">{rel_html}</ul>' if rel_html else ""))


def stage_table_html(world, module, sort, preds):
    """固定類別（如道位）的世界：行＝元素，列＝謂詞。"""
    ents = world.of_sort(sort)
    head = "".join(f"<th>{html.escape(p)}</th>" for p in preds)
    body = []
    for e in ents:
        cells = "".join(f'<td class="{"y" if p in e.preds else "n"}">{"●" if p in e.preds else "·"}</td>' for p in preds)
        body.append(f"<tr><th>{html.escape(e.label)}</th>{cells}</tr>")
    return f'<table class="stages"><tr><th></th>{head}</tr>{"".join(body)}</table>'
