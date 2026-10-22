#!/bin/sh
# 检查全部模块：ToyStore 依赖 Game / PathCat / Harness / Store / Replay；
# Path（路径键与引理）→ Env（依赖 Later / Syntax（生成）/ FlagTable（生成）/ Path）→ ToyEnv（脚本余模型，五条 refl）；
# StoreToy = Store 程序在纯对手上全 refl；DriveToy 给 drive.sh；Node = 文件 agent 的程序；ToyNode = 六局全 refl
cd "$(dirname "$0")" && export LC_ALL=C.UTF-8 && agda src/ToyStore.agda && agda src/Path.agda && agda src/ToyEnv.agda && agda src/StoreToy.agda && agda src/DriveToy.agda && agda src/Node.agda && agda src/ToyNode.agda
