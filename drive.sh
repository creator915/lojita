#!/bin/sh
# 用后端 v5 的驱动器跑 ToyCode 的策略：装四条声明（Agda 真的检查、真的扩展签名），再调 twice 5
# 库名：Agda 侧只说了个数（Code 1 2 …），这里说它们是谁
cd "$(dirname "$0")" || exit 1
export LC_ALL=C.UTF-8
agda-cubical-run.v5 -v0 --cubical-drive=strat --cubical-lib-defs=ℕ --cubical-lib-cons=zero,suc src/ToyCode.agda
