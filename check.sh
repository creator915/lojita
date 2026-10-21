#!/bin/sh
# 检查全部模块：ToyStore 依赖 Game / PathCat / Harness / Store / Replay；
# ToyEnv 依赖 Later / Syntax（生成）/ FlagTable（生成）/ Env / Keys；StoreToy = Store 程序在纯对手上全 refl；DriveToy 给 drive.sh
cd "$(dirname "$0")" && export LC_ALL=C.UTF-8 && agda src/ToyStore.agda && agda src/ToyEnv.agda && agda src/StoreToy.agda && agda src/DriveToy.agda
