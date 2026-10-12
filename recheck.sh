#!/bin/sh
# 真实文件走 parse → toV → fromV → 当虚拟模块检查：解码和合成范围在真实代码上也站得住
# 用法：./recheck.sh [FILE...]；不给参数就跑 src/ 里的全部模块和几个 cubical 模块
cd "$(dirname "$0")" || exit 1
export LC_ALL=C.UTF-8
AGDA=${AGDA:-/usr/local/bin/agda-cubical-run.v6}
C=/root/agda-backend/cubical-upstream/Cubical
if [ $# -eq 0 ]; then
  set -- src/Game.agda src/PathCat.agda src/Later.agda src/Store.agda src/Env.agda src/ToyEnv.agda \
         $C/Data/Nat/Properties.agda $C/Data/List/Properties.agda $C/HITs/S1/Base.agda $C/Foundations/Univalence.agda
fi
status=0
for f in "$@"; do
  out=$("$AGDA" -v0 --cubical-recheck="$f" src/Env.agda 2>/dev/null | tail -1)
  echo "$out" | cut -c1-200
  case "$out" in OK*) ;; *) status=1 ;; esac
done
exit $status
