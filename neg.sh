#!/bin/sh
# 反例：这些文件必须编译失败（权限、flag、配额、根上 leave 都是类型错）
cd "$(dirname "$0")" || exit 1
export LC_ALL=C.UTF-8
status=0
for f in tests/neg/*.agda; do
  if agda -i src -i tests/neg "$f" > /dev/null 2>&1; then echo "UNEXPECTED PASS: $f"; status=1; else echo "rejected as expected: $f"; fi
done
exit $status
