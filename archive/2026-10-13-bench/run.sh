#!/bin/sh
# 在题目镜像（叠了解释器那层）里跑 Bench.agda 的 agent：bench/run.sh junegunn__fzf.b56d614
# 产物：runs/bench/<题目>/<时间>/{box/（全部提示词与回答 = 轨迹）, drive.log, drive.out, relay.log, sub/<题目>/submission.tar.gz}
# 之后：bench/eval.sh runs/bench/<题目>/<时间>
cd "$(dirname "$0")/.." || exit 1
TASK=${1:?task id}
: "${LOJITA_API_KEY:?LOJITA_API_KEY 没设}"
IMG="programbench/$(echo "$TASK" | sed 's/__/_1776_/'):task_cleanroom_v6_lojita"
TS=$(date -u +%Y%m%dT%H%M%SZ)
RUN=runs/bench/$TASK/$TS
BOX=$RUN/box
mkdir -p "$BOX" && chmod 777 "$BOX"
NAME=lojita-$TS
echo "start $TS task=$TASK image=$IMG container=$NAME" | tee "$RUN/run.log"
docker run -d --name "$NAME" --network none --cpus "${CPUS:-4}" --memory 16g --memory-swap 16g \
  --user agent --cap-drop SYS_PTRACE -v "$(realpath "$BOX"):/box" -w /workspace \
  -e PAGER=cat -e MANPAGER=cat -e LESS=-R -e PIP_PROGRESS_BAR=off -e TQDM_DISABLE=1 \
  "$IMG" sleep infinity >/dev/null || exit 1
docker exec -u agent "$NAME" git config user.name lojita
docker exec -u agent "$NAME" git config user.email lojita@example.com
python3 bench/relay.py "$BOX" > "$RUN/relay.log" 2>&1 &
RELAY=$!
timeout "${WALL:-10800}" docker exec -u agent -w /opt/lojita/lojita -e LC_ALL=C.UTF-8 -e LOJITA_SH_TIMEOUT=180 "$NAME" \
  /opt/lojita/bin/agda -v0 --library-file=/opt/lojita/libraries \
  --cubical-drive=agent --cubical-handler=ask:mailbox:/box --cubical-handler=sh:/workspace \
  src/Bench.agda > "$RUN/drive.out" 2> "$RUN/drive.log"
echo "drive exit=$? $(date -u +%Y%m%dT%H%M%SZ)" | tee -a "$RUN/run.log"
touch "$BOX/stop"; kill $RELAY 2>/dev/null
# 提交包 = /workspace（题目给的 executable 对 agent 不可读，跳过它）
docker exec -u agent "$NAME" sh -c 'tar --ignore-failed-read -czf /box/submission.tar.gz -C /workspace .' 2>>"$RUN/run.log"
mkdir -p "$RUN/sub/$TASK" && mv "$BOX/submission.tar.gz" "$RUN/sub/$TASK/"
docker rm -f "$NAME" >/dev/null
echo "done; submission at $RUN/sub/$TASK/submission.tar.gz" | tee -a "$RUN/run.log"
