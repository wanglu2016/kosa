"""語料層（v0.1 最小版）：《俱舍論頌》CBETA T1560。

用途：命題中「頌」「相關頌」欄所引的頌文，逐字與 CBETA 核對，並給出所在品與行。
"""
from __future__ import annotations
import json
import re
from pathlib import Path

_PUNCT = re.compile(r"[，。、；：！？「」『』（）\s|]")


def strip(s: str) -> str:
    return _PUNCT.sub("", s)


class Verses:
    def __init__(self, path: Path):
        data = json.loads(path.read_text(encoding="utf-8"))
        self.chapters = []
        for ch in data:
            lines = [l.replace("|", "") for l in ch["lines"]]
            flat, index = "", []
            for i, l in enumerate(lines):
                s = strip(l)
                index.extend([i] * len(s))
                flat += s
            self.chapters.append((ch["head"], lines, flat, index))

    def find(self, quote: str):
        """回傳 [(品名, 起行, 止行, 原行文字)]；找不到回傳 []。"""
        key = strip(quote)
        hits = []
        if not key:
            return hits
        for head, lines, flat, index in self.chapters:
            start = 0
            while True:
                k = flat.find(key, start)
                if k < 0:
                    break
                a, b = index[k], index[k + len(key) - 1]
                hits.append((head, a + 1, b + 1, "".join(lines[a:b + 1])))
                start = k + 1
        return hits

    def check_module(self, module):
        """核對模組中所有頌文引用。回傳 [(命題編號, 欄位, 引文, 命中)]。"""
        out = []
        for sid, st in module.statements.items():
            for field in ("頌", "相關頌"):
                if field in st.meta:
                    for quote in re.split(r"[；;]", st.meta[field]):
                        quote = quote.strip()
                        if quote:
                            out.append((sid, field, quote, self.find(quote)))
        return out
