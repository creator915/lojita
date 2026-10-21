#!/bin/sh
# 不用 LLM 的演练：信箱里预先放好三份答卷（围栏+错定义、postulate、正确），看回路是否走通、提示词长什么样
cd "$(dirname "$0")" || exit 1
export LC_ALL=C.UTF-8
AGDA=${AGDA:-/usr/local/bin/agda-cubical-run.v6}
BOX=${BOX:-runs/task1-dry}
rm -rf "$BOX" && mkdir -p "$BOX"
cat > "$BOX/0.answer" <<'A'
```agda
{-# OPTIONS --safe --cubical #-}
module Twice where
open import Cubical.Data.Nat

twice : ℕ → ℕ
twice n = n + 1
```
A
cat > "$BOX/1.answer" <<'A'
{-# OPTIONS --safe --cubical #-}
module Twice where
open import Cubical.Data.Nat

postulate
  twice : ℕ → ℕ
A
cat > "$BOX/2.answer" <<'A'
{-# OPTIONS --safe --cubical #-}
module Twice where
open import Cubical.Data.Nat

twice : ℕ → ℕ
twice n = n + n
A
timeout 600 "$AGDA" -v0 --cubical-drive=task1 --cubical-handler=ask:mailbox:"$BOX" src/Solve.agda
