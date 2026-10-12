#!/bin/sh
# 检查全部模块：ToyStore 依赖 Game / PathCat / Harness / Store / Replay；ToyCode 依赖 Later / Code / Load
cd "$(dirname "$0")" && export LC_ALL=C.UTF-8 && agda src/ToyStore.agda && agda src/ToyCode.agda
