#!/bin/sh
# 回放一局：把某次运行 box 里的 n.answer 原样放进新信箱，不问 LLM，重跑 Bench.agda；同时每 2 秒记一次 agda 进程的内存
# 用法：bench/replay.sh runs/bench/<题目>/<时间> [内存上限，默认 16g]
cd "$(dirname "$0")/.." || exit 1
SRC=${1:?run dir}; MEM=${2:-16g}
TASK=$(basename "$(dirname "$SRC")")
IMG="programbench/$(echo "$TASK" | sed 's/__/_1776_/'):task_cleanroom_v6_lojita"
RUN=$SRC/replay; rm -rf "$RUN"; BOX=$RUN/box; mkdir -p "$BOX"; chmod 777 "$BOX"
cp "$SRC"/box/*.answer "$BOX"/
NAME=lojita-replay
docker rm -f "$NAME" >/dev/null 2>&1
docker run -d --name "$NAME" --network none --memory "$MEM" --memory-swap "$MEM" --user agent --cap-drop SYS_PTRACE \
  -v "$(realpath "$BOX"):/box" -w /workspace "$IMG" sleep infinity >/dev/null || exit 1
docker exec -u agent "$NAME" git config user.name lojita; docker exec -u agent "$NAME" git config user.email lojita@example.com
( while docker exec "$NAME" true 2>/dev/null; do
    printf '%s rss_kb=%s step=%s prompt=%s\n' "$(date -u +%H:%M:%S)" \
      "$(docker exec "$NAME" sh -c 'ps -o rss= -C agda | sort -n | tail -1')" \
      "$(grep -c '^\[drive\] step' "$RUN/drive.log" 2>/dev/null)" \
      "$(ls "$BOX"/*.prompt 2>/dev/null | wc -l)"; sleep 2; done ) > "$RUN/mem.log" 2>/dev/null &
SAMPLER=$!
timeout "${WALL:-1800}" docker exec -u agent -w /opt/lojita/lojita -e LC_ALL=C.UTF-8 -e LOJITA_SH_TIMEOUT=180 "$NAME" \
  /opt/lojita/bin/agda -v0 --library-file=/opt/lojita/libraries \
  --cubical-drive=agent --cubical-handler=ask:mailbox:/box --cubical-handler=sh:/workspace \
  src/Bench.agda > "$RUN/drive.out" 2> "$RUN/drive.log"
echo "drive exit=$?"
kill $SAMPLER 2>/dev/null; docker rm -f "$NAME" >/dev/null
