#!/bin/sh
# 给一个题目的官方镜像叠一层解释器：bench/build-image.sh junegunn__fzf.b56d614
# 结果：programbench/<题目>:task_cleanroom_v6_lojita（评测时 --image-tag task_cleanroom_v6_lojita）
set -e
cd "$(dirname "$0")" || exit 1
TASK=${1:?task id, e.g. junegunn__fzf.b56d614}
BASE="programbench/$(echo "$TASK" | sed 's/__/_1776_/'):task_cleanroom_v6"
AGDA=${AGDA:-/usr/local/bin/agda-cubical-run.v6}
DATA=$("$AGDA" --print-agda-data-dir)
rm -rf ctx && mkdir -p ctx/lojita
cp "$AGDA" ctx/agda
cp -r "$DATA" ctx/agda-data
cp -r /root/agda-backend/cubical-upstream ctx/cubical
tar -C .. --exclude=./.git --exclude=./runs --exclude=./archive --exclude=./_lojita_virtual --exclude=./bench -cf - . | tar -C ctx/lojita -xf -
docker image inspect "$BASE" >/dev/null 2>&1 || docker pull "$BASE"
docker build --build-arg BASE="$BASE" -t "${BASE}_lojita" .
rm -rf ctx
echo "built ${BASE}_lojita"
