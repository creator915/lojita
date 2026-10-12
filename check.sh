#!/bin/sh
# 检查全部模块：ToyStore 依赖 Game / PathCat / Harness / Store / Replay
cd "$(dirname "$0")" && LC_ALL=C.UTF-8 agda src/ToyStore.agda
