#!/bin/sh
# 真后端跑 DriveToy（先 ./check.sh）；需要 agda-cubical-run.v7（kid 用的 enter 带 realm，v6 不认）
cd "$(dirname "$0")" || exit 1
export LC_ALL=C.UTF-8
AGDA=${AGDA:-/usr/local/bin/agda-cubical-run.v7}
run() { echo "--- $1"; timeout 300 "$AGDA" -v0 --cubical-drive="$1" --cubical-handler=ask:fixed:yes src/DriveToy.agda 2>/dev/null; }
run prog        # value (Lit (LitNat (pos 6)))         parse → check → eval twice 3
run bad         # error "…UnequalTypes…"                check 驳回，报错原文
run kid         # "yes"                                 enter → ask → leave
run showIface   # ok (iface ("M1" ∷ []) (("twice" , ℕ → ℕ) ∷ []) …)
run undeclared  # fail [] "imports not in the header: Cubical.Data.Bool"
run chain       # value (Lit (LitNat (pos 4)))         M2 import 虚拟模块 M1，eval four
run coinf       # fail … CoInfectiveImport              Agda 自己的规则兜底
run comments    # 4                                     注释挂成声明序列里的节点
run showGoals   # holes ((goal 0 … ℕ) ∷ [])            洞的表
run fillHole    # value (Lit (LitNat (pos 6)))         give 填洞 → check → eval
run splitN      # holes (两个)                          split 分情况
run splitLam    # holes (两个)                          扩展 λ 里的洞分情况
