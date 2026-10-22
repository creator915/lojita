# Lojita：给 Claude Code 的工作规矩

- **冻结（2026-10-22 晚）**：不要再在这里提交。后续在 /root/logita1（github.com/creator915/logita1）。

- **2026-10-22 晚复位**：先读 `docs/reset-2026-10-22.md`。subagent 递归（Harness / Replay / ToyStore / Node / ToyNode、04-node、harness-plan）已归档到 `archive/2026-10-22-subagent-tree/`；新基础 = 文件库 + 触发器（一切皆文件，agent 之间只有行，没有调用）。`docs/harness/` 各页顶上一行写着哪些段作废；README 里有速查表。
- 下一步是 D0（讨论，拍板 reset §4.8 七条）→ D1（Σ 目录化：新 Env）→ D2（Agent 一轮 + 玩具调度器）→ D3（后端 v8 + 触发循环）→ D4（真跑）。不要再在 `Env.agda` §3 的栈帧（配额、realm 继承）上搭东西；`enter` / `leave` 以后只管检查器会话。
- 动手前先跑基线：`./check.sh`、`./neg.sh`、`./store.sh`、`./drive.sh`，记下现在哪些过；改完每一步再跑，只许变好。
- 永不手改生成的文件：`src/Syntax.agda`、`src/FlagTable.agda`。
- 跑 agda 必须 `LC_ALL=C.UTF-8`。默认 `agda` 是 `/usr/local/bin/agda-cubical-run.v7`；M1 做出 v8 后再换链接。
- 改了行为就改 `docs/harness/` 对应那一页；脚本注释里的期望输出和文档里的验收表必须一致。
- 用户不读代码。汇报用验收编号说话（例：M0-1 过；E6 没过，报错首行是 …），不贴大段代码；卡住时说清卡在哪一页哪一条。
- 提交：docs 和 src 一起进 git，`git push -u origin main`（SSH 部署密钥已可用）。不要提交 `runs/`、`_build/`、`*.agdai`。
