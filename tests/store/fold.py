#!/usr/bin/env python3
"""独立的 fold：log.jsonl → 快照 JSON（键有序）。后端的 --cubical-store-dump 必须打印逐字节相同的东西（验收 B5）。
规则：只有 set 落盘；最后一行没有换行 = 撕裂行，丢弃；中间有解析不了的行 = 损坏，报错；
大值行 {"h": sha256} 在快照里记成 {"h": ...}，小值行 {"v": ...} 记成字符串。
打印格式照 aeson：键按码点排序、无空格、非 ASCII 原样、控制字符只有 \\n \\r \\t 用短写，其余写 \\u00xx。"""
import json, sys

def fold(path):
    board = {}
    with open(path, "rb") as f:
        for raw in f:
            if not raw.endswith(b"\n"):
                break                                  # 撕裂的最后一行：没写完 = 没写
            r = json.loads(raw)                        # 中间坏行：抛错，不能悄悄当成结尾
            if r["op"] == "set":
                board[r["k"]] = {"h": r["h"]} if "h" in r else r["v"]
    return board

def esc(s):                                            # aeson 的字符串转义
    out = []
    for c in s:
        if c == '"':      out.append('\\"')
        elif c == "\\":   out.append("\\\\")
        elif c == "\n":   out.append("\\n")
        elif c == "\r":   out.append("\\r")
        elif c == "\t":   out.append("\\t")
        elif ord(c) < 32: out.append("\\u%04x" % ord(c))
        else:             out.append(c)
    return '"' + "".join(out) + '"'

def dumps(board):
    items = []
    for k in sorted(board):
        v = board[k]
        items.append(esc(k) + ":" + ('{"h":' + esc(v["h"]) + "}" if isinstance(v, dict) else esc(v)))
    return "{" + ",".join(items) + "}"

if __name__ == "__main__":
    print(dumps(fold(sys.argv[1])))
