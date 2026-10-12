#!/bin/sh
# 用新后端 agda-cubical-run 把 ToyStore 里的项算到规范形（先跑 ./check.sh）
# 注意：被 open 的模块里的名字在这里要带前缀，例如 D.board
cd "$(dirname "$0")" || exit 1
export LC_ALL=C.UTF-8
run() { echo "--- $1"; agda -v0 --cubical-run="$1" src/ToyStore.agda; }
run 'theTrace'                                   # §7  真对手跑出的棋谱
run 'finalBoard kx'                              #     终局 x
run 'finalBoard ky'                              #     终局 y
run 'fst inc-tx'                                 #     一步 run 在对象层的事务
run 'fst result′ ky'                             # §11 换运输：叶子只看见 y
run 'moved kx′'                                  # §10 沿 ua 搬运后的数据库
run 'moved ky′'
run 'fst (fst (fst (snd replayed)))'             # §12 回放：脚本一条没消费
run 'length (snd (snd replayed))'                #     回放棋谱长度
run 'D.board (fst (fst (snd diverged))) kx'      #     录音失效后的终局 x
run 'length (snd (snd diverged))'                #     录音 7 条 + 重问 2 条
