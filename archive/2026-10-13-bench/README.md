# 2026-10-13 归档：任务一回路与 ProgramBench 的临时件

归档原因见 docs/store-plan.md（三份记忆 → 一个 Store）与 docs/bench.md（fzf 第一局 OOM 的记录）。
- Solve.agda、Bench.agda、Str.agda：在 Agda 项里抱历史、拼提示词、拆大字符串，是 OOM 的来源；策略部分在阶段 5 作为纯策略重写。
- task1.sh、task1-dry.sh、run.sh、relay.py、dry.sh、replay.sh：信箱拓扑，由"后端写 Store、中继读 Store"取代。
留在 bench/ 的 Dockerfile、build-image.sh、eval.sh 是函子层与官方评测，仍在用。
