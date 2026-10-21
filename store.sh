#!/bin/sh
# 验收：Store 的硬盘余模型（docs/store-backend.md 第三节）
#   F 组：不要后端。fold.py / logtx.py 对样例日志；LogTx 由 Agda 用 refl 复算。
#   B 组：要 agda-cubical-run.v7（--cubical-handler=store:DIR、--cubical-store-dump=DIR）。每条用独立目录。
cd "$(dirname "$0")" || exit 1
export LC_ALL=C.UTF-8
AGDA=${AGDA:-/usr/local/bin/agda-cubical-run.v7}
T=${T:-runs/store-test}
FX=tests/store/fixtures
pass=0; fail=0
ok()  { echo "PASS $1"; pass=$((pass+1)); }
bad() { echo "FAIL $1: $2"; fail=$((fail+1)); }
norm() { python3 -c 'import json,sys; sys.path.insert(0,"tests/store"); from fold import dumps; print(dumps(json.load(sys.stdin)))'; }   # aeson 的写法
fold() { python3 tests/store/fold.py "$1"; }
has() { case "$1" in *"$2"*) return 0;; *) return 1;; esac; }

# ---------- F 组 ----------
for fx in basic torn blob; do
  if [ "$(fold $FX/$fx/log.jsonl)" = "$(norm < $FX/$fx/expected.json)" ]; then ok "F-fold-$fx"; else bad "F-fold-$fx" "$(fold $FX/$fx/log.jsonl)"; fi
done
python3 tests/store/logtx.py $FX/basic/log.jsonl > tests/gen/LogTx.agda
if agda -i src -i tests/gen tests/gen/LogTx.agda > /dev/null 2>&1; then ok "F-logtx-basic（Agda refl）"; else bad "F-logtx-basic" "agda rejected tests/gen/LogTx.agda"; fi

# ---------- B 组 ----------
if [ ! -x "$AGDA" ]; then echo "SKIP B 组：$AGDA 不存在（先构建 v7）"; echo "F 组：$pass 过 $fail 败"; exit 2; fi
rm -rf "$T"; mkdir -p "$T"
drive() { timeout "${TIMEOUT:-300}" "$AGDA" -v0 --cubical-drive="$1" --cubical-handler=store:"$2" src/StoreToy.agda 2>/dev/null; }
dump()  { "$AGDA" -v0 --cubical-store-dump="$1" src/StoreToy.agda 2>/dev/null | norm; }

# B1 回环
o=$(drive roundtrip "$T/b1a"); has "$o" 'just "1"' && ok B1-roundtrip || bad B1-roundtrip "$o"
o=$(drive missing "$T/b1b");   has "$o" 'nothing'  && ok B1-missing   || bad B1-missing "$o"
o=$(drive overwrite "$T/b1c"); has "$o" 'just "2"' && ok B1-overwrite || bad B1-overwrite "$o"

# B2 子实例
o=$(drive kidSees "$T/b2a");   has "$o" 'just "1"' && has "$o" 'nothing' && ok B2-kidSees || bad B2-kidSees "$o"
o=$(drive kidWrites "$T/b2b"); has "$o" 'just "9"' && ok B2-kidWrites || bad B2-kidWrites "$o"

# B3 重启：同一目录换进程
drive persist1 "$T/b3" > /dev/null
o=$(drive persist2 "$T/b3")
has "$o" 'just "one"' && has "$o" 'just "two"' && has "$o" 'just "three"' && ok B3-restart || bad B3-restart "$o"
[ "$(wc -l < "$T/b3/log.jsonl")" = 3 ] && ok "B3-log=3行（get 不落盘）" || bad B3-lines "$(wc -l < "$T/b3/log.jsonl")"

# B4 撕裂：砍掉最后一行的尾巴，再跑；文件要被截回完整行
drive persist1 "$T/b4" > /dev/null
truncate -s -7 "$T/b4/log.jsonl"
o=$(drive persist2 "$T/b4")
has "$o" 'just "one"' && has "$o" 'just "two"' && has "$o" 'nothing' && ok B4-torn || bad B4-torn "$o"
[ "$(wc -l < "$T/b4/log.jsonl")" = 2 ] && [ "$(tail -c1 "$T/b4/log.jsonl" | od -An -c | tr -d ' ')" = '\n' ] && ok B4-truncated-back || bad B4-truncated-back "$(tail -c 60 "$T/b4/log.jsonl")"
# B4 被杀：stress 跑到一半 kill -9，重启后 dump = 完整行的 fold，再追加也正常
"$AGDA" -v0 --cubical-drive=stress --cubical-handler=store:"$T/b4k" src/StoreToy.agda > /dev/null 2>&1 &
kp=$!; sleep 8; kill -9 $kp 2>/dev/null; wait $kp 2>/dev/null
[ "$(dump "$T/b4k")" = "$(fold "$T/b4k/log.jsonl")" ] && ok B4-kill9-dump=fold || bad B4-kill9 "dump ≠ fold"
drive roundtrip "$T/b4k" > /dev/null
[ "$(dump "$T/b4k")" = "$(fold "$T/b4k/log.jsonl")" ] && ok B4-kill9-append-ok || bad B4-kill9-append "dump ≠ fold after append"

# B5 方块：dump = 独立 fold；两种写序快照相等
drive commuteXY "$T/b5x" > /dev/null; drive commuteYX "$T/b5y" > /dev/null
[ "$(dump "$T/b5x")" = "$(fold "$T/b5x/log.jsonl")" ] && ok B5-dump=fold || bad B5-dump=fold "$(dump "$T/b5x") vs $(fold "$T/b5x/log.jsonl")"
[ "$(dump "$T/b5x")" = "$(dump "$T/b5y")" ] && ok B5-commute || bad B5-commute "$(dump "$T/b5x") vs $(dump "$T/b5y")"

# B6 大字段
o=$(drive big "$T/b6")
has "$o" 'true' && ok B6-big-roundtrip || bad B6-big-roundtrip "$o"
[ "$(ls "$T/b6/blob" | wc -l)" = 1 ] && [ "$(wc -c < "$T/b6/blob/$(ls "$T/b6/blob")")" = 102400 ] && ok B6-one-blob-102400 || bad B6-blob "$(ls -l "$T/b6/blob")"
[ "$(grep -c '"h":' "$T/b6/log.jsonl")" = 2 ] && ! grep -q '"v":' "$T/b6/log.jsonl" && ok B6-log-hash-only || bad B6-log "$(cut -c1-120 "$T/b6/log.jsonl")"

# B7 性能：一万次 set+get；RSS 每秒采样
start=$(date +%s)
"$AGDA" -v0 --cubical-drive=stress --cubical-handler=store:"$T/b7" src/StoreToy.agda > "$T/b7.out" 2>/dev/null &
sp=$!; : > "$T/b7.rss"
while kill -0 $sp 2>/dev/null; do awk '/VmRSS/{print $2}' /proc/$sp/status >> "$T/b7.rss" 2>/dev/null; sleep 1; done
wait $sp; el=$(( $(date +%s) - start ))
has "$(cat "$T/b7.out")" '0' && ok B7-stress-0-mismatch || bad B7-stress "$(cat "$T/b7.out")"
[ $el -lt 120 ] && ok "B7-time ${el}s<120s" || bad B7-time "${el}s"
r10=$(sed -n 10p "$T/b7.rss"); rl=$(tail -1 "$T/b7.rss")
if [ -n "$r10" ] && [ -n "$rl" ] && [ $(( rl - r10 )) -lt 51200 ]; then ok "B7-rss-flat $((rl/1024))MB-$((r10/1024))MB"; else bad B7-rss "10s:${r10}kB last:${rl}kB"; fi
[ "$(wc -l < "$T/b7/log.jsonl")" = 10000 ] && ok B7-log-10000-lines || bad B7-log "$(wc -l < "$T/b7/log.jsonl")"

# B8 日志是棋谱：转写成 Agda，refl 复算
python3 tests/store/logtx.py "$T/b5x/log.jsonl" > tests/gen/LogTx.agda
agda -i src -i tests/gen tests/gen/LogTx.agda > /dev/null 2>&1 && ok "B8-log→Agda-refl" || bad B8 "agda rejected LogTx"

echo "$pass 过 $fail 败"; [ $fail = 0 ]
