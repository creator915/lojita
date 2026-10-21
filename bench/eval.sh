#!/bin/sh
# 评测一次运行：bench/eval.sh runs/bench/<题目>/<时间>  （镜像 = 官方镜像 + 解释器那层，题目与测试没变）
cd "$(dirname "$0")/.." || exit 1
RUN=${1:?run dir}
PB=${PB:-/root/pb-venv/bin/programbench}
"$PB" eval "$RUN/sub" --image-tag "${TAG:-task_cleanroom_v6_lojita}" --docker-cpus "${CPUS:-4}" -w 1 -b 1 2>&1 | tee "$RUN/eval.log"
"$PB" info "$RUN/sub" 2>&1 | tee "$RUN/info.log"
