#!/bin/sh
# 检查全部模块：ToyStore 依赖 Game / PathCat / Harness / Store / Replay；Later 单独检查
cd "$(dirname "$0")" && export LC_ALL=C.UTF-8 && agda src/ToyStore.agda && agda src/Later.agda
