#!/bin/sh
# 检查全部模块（2026-10-22 复位后）：
#   Path（路径键与引理）→ Env（依赖 Later / Syntax（生成）/ FlagTable（生成）/ Path / Keys → Store → Game；Later → PathCat）
#   → ToyEnv（脚本余模型，五条 refl）；StoreToy = Store 程序在纯对手上全 refl；DriveToy 给 drive.sh。
# Harness / Replay / ToyStore / Node / ToyNode 已归档到 archive/2026-10-22-subagent-tree/（见 docs/reset-2026-10-22.md）。
cd "$(dirname "$0")" && export LC_ALL=C.UTF-8 && agda src/Path.agda && agda src/ToyEnv.agda && agda src/StoreToy.agda && agda src/DriveToy.agda
