#!/bin/sh
# Rebuilder = Agda 自己的接口缓存：check 过的模块把接口写进 _build（带源码哈希与 import 哈希），
# 再 check 同一个模块、哈希都没变，就直接装接口，不重查。看 Agda 的 "Checking M1" 变成 "Loading M1"
cd "$(dirname "$0")" || exit 1
export LC_ALL=C.UTF-8
AGDA=${AGDA:-/usr/local/bin/agda-cubical-run.v6}
rm -rf _build/2.9.0/agda/_lojita_virtual
echo "--- 第一次：要查"
"$AGDA" --cubical-drive=prog src/DriveToy.agda 2>&1 | grep "Checking M1\|Loading M1\|interface\|^value"
echo "--- 第二次：直接装接口"
"$AGDA" --cubical-drive=prog src/DriveToy.agda 2>&1 | grep "Checking M1\|Loading M1\|interface\|^value"
