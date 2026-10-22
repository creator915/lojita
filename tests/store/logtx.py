#!/usr/bin/env python3
"""把 log.jsonl 转写成 Agda（验收 B8 / E8，后端写、Agda 查）：
tx : S.Tx 是日志里的 set 序列；对快照里的每个键生成一条 refl：S.runTx tx empty k ≡ just v。
日志里的键 "a/x" 按 "/" 拆成路径 "a" ∷ "x" ∷ []（Path.agda），S = Store Path String。
大值行用哈希串当值。用法：logtx.py DIR/log.jsonl > tests/gen/LogTx.agda；agda -i src -i tests/gen tests/gen/LogTx.agda"""
import json, sys
sys.path.insert(0, __file__.rsplit("/", 1)[0] if "/" in __file__ else ".")
from fold import fold

def esc(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\r", "\\r").replace("\t", "\\t") + '"'

def val(r):
    return r["h"] if "h" in r else r["v"]

def pathKey(k):                                    # "a/x" → ("a" ∷ "x" ∷ [])
    return "(" + " ∷ ".join(esc(seg) for seg in k.split("/")) + " ∷ [])"

def main(path):
    ops = []
    with open(path, "rb") as f:
        for raw in f:
            if not raw.endswith(b"\n"):
                break
            r = json.loads(raw)
            if r["op"] == "set":
                ops.append("S.set %s %s" % (pathKey(r["k"]), esc(val(r))))
    board = fold(path)
    out = ["{-# OPTIONS --safe --cubical #-}",
           "-- 由 tests/store/logtx.py 从 log.jsonl 生成：后端写的日志，Agda 用 S.runTx 复算（验收 B8 / E8）；键按 / 拆成路径",
           "module LogTx where",
           "open import Cubical.Foundations.Prelude using (_≡_; refl)",
           "open import Cubical.Data.List.Base using ([]; _∷_)",
           "open import Cubical.Data.Maybe.Base using (nothing; just)",
           "open import Agda.Builtin.String using (String)",
           "open import Keys using (discreteString)",
           "open import Path using (Path; discretePath)",
           "import Store",
           "module S = Store Path String discretePath discreteString",
           "",
           "emptyBoard : S.Board",
           "emptyBoard _ = nothing",
           "",
           "tx : S.Tx",
           "tx = " + (" ∷ ".join(ops) + " ∷ []" if ops else "[]"),
           ""]
    for k in sorted(board):
        v = board[k]["h"] if isinstance(board[k], dict) else board[k]
        out += ["_ : S.runTx tx emptyBoard %s ≡ just %s" % (pathKey(k), esc(v)), "_ = refl", ""]
    sys.stdout.write("\n".join(out))

main(sys.argv[1])
