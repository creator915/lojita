#!/bin/sh
# 后端驱动器的反例：前四段该 fail（nothing），最后一段该过（just 0）。原因看 [drive] 日志
cd "$(dirname "$0")" || exit 1
export LC_ALL=C.UTF-8
for e in badType loop negData useUndefined sigOk; do
  echo "--- $e"
  agda-cubical-run.v5 -v0 --cubical-drive="$e" --cubical-lib-defs=ℕ --cubical-lib-cons=zero,suc src/DriveTests.agda 2>&1 | grep -v "^\[drive\] step\|^\[drive\] library\|^\[drive\] environment\|^\[drive\] names\|^\[drive\]   ok"
done
