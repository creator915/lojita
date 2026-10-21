#!/bin/sh
# 第一个任务真跑：DeepSeek 写 twice，Agda 查，最多五轮；跑 N 次，每次的 stdout / stderr 存在 runs/task1/
# 密钥只从环境变量来：LOJITA_API_KEY=… ./task1.sh 10
cd "$(dirname "$0")" || exit 1
export LC_ALL=C.UTF-8
: "${LOJITA_API_KEY:?LOJITA_API_KEY 没设}"
export LOJITA_MODEL=${LOJITA_MODEL:-deepseek-flash}
AGDA=${AGDA:-/usr/local/bin/agda-cubical-run.v6}
URL=${URL:-https://api.deepseek.com/chat/completions}
N=${1:-1}
OUT=${OUT:-runs/task1}
mkdir -p "$OUT"
i=1
while [ "$i" -le "$N" ]; do
  timeout 900 "$AGDA" -v0 --cubical-drive=task1 --cubical-handler=ask:http:"$URL" src/Solve.agda > "$OUT/$i.out" 2> "$OUT/$i.log"
  rounds=$(grep -c '^\[drive\] step [0-9]* ask' "$OUT/$i.log")
  if grep -q '^passed' "$OUT/$i.out"; then r=passed; elif grep -q '^gaveUp' "$OUT/$i.out"; then r=gaveUp; else r=ERROR; fi
  echo "trial $i: $r after $rounds round(s)"
  i=$((i + 1))
done
