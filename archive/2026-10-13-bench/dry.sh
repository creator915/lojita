#!/bin/sh
# 不用 LLM 的演练：信箱里预放三份答卷（一条命令、一次没围栏的回复、提交），看容器里整条回路是否走通
cd "$(dirname "$0")/.." || exit 1
TASK=${1:-junegunn__fzf.b56d614}
IMG="programbench/$(echo "$TASK" | sed 's/__/_1776_/'):task_cleanroom_v6_lojita"
RUN=runs/bench/dry; rm -rf "$RUN"; BOX=$RUN/box; mkdir -p "$BOX" && chmod 777 "$BOX"
printf 'Let me look around.\n\n```bash\nls -la && ./executable --version && git status | head -3\n```\n' > "$BOX/0.answer"
printf 'I forgot the fence.\n' > "$BOX/1.answer"
printf 'Done.\n\n```bash\necho COMPLETE_TASK_AND_SUBMIT_FINAL_OUTPUT\n```\n' > "$BOX/2.answer"
NAME=lojita-dry
docker rm -f "$NAME" >/dev/null 2>&1
docker run -d --name "$NAME" --network none --user agent --cap-drop SYS_PTRACE -v "$(realpath "$BOX"):/box" -w /workspace "$IMG" sleep infinity >/dev/null || exit 1
docker exec -u agent "$NAME" git config user.name lojita && docker exec -u agent "$NAME" git config user.email lojita@example.com
timeout 300 docker exec -u agent -w /opt/lojita/lojita -e LC_ALL=C.UTF-8 -e LOJITA_SH_TIMEOUT=180 "$NAME" \
  /opt/lojita/bin/agda -v0 --library-file=/opt/lojita/libraries \
  --cubical-drive=agent --cubical-handler=ask:mailbox:/box --cubical-handler=sh:/workspace \
  src/Bench.agda > "$RUN/drive.out" 2> "$RUN/drive.log"
echo "drive exit=$?"
docker exec -u agent "$NAME" sh -c 'tar --ignore-failed-read -czf /box/submission.tar.gz -C /workspace .'; echo "tar exit=$?"
docker rm -f "$NAME" >/dev/null
