# Lojita：给 Claude Code 的工作规矩

- 规格在 `docs/harness/`：`README.md` 是索引，`07-milestones.md` 是当前要做的事。改任何文件前先读对应的那一页；每条验收标准是一条命令加一行期望输出，照着跑。
- 当前里程碑：M0（Agda 侧）。顺序：`src/Path.agda` → `src/Env.agda` → 改键（ToyEnv / StoreToy / DriveToy / tests/neg）→ `./check.sh` 过 → `src/Node.agda` → `src/ToyNode.agda` S1 … S6。M0 不碰后端。
- 动手前先跑基线：`./check.sh`、`./neg.sh`、`./store.sh`、`./drive.sh`，记下现在哪些过；改完每一步再跑，只许变好。
- 永不手改生成的文件：`src/Syntax.agda`、`src/FlagTable.agda`。
- 跑 agda 必须 `LC_ALL=C.UTF-8`。默认 `agda` 是 `/usr/local/bin/agda-cubical-run.v7`；M1 做出 v8 后再换链接。
- 改了行为就改 `docs/harness/` 对应那一页；脚本注释里的期望输出和文档里的验收表必须一致。
- 用户不读代码。汇报用验收编号说话（例：M0-1 过；E6 没过，报错首行是 …），不贴大段代码；卡住时说清卡在哪一页哪一条。
- 提交：docs 和 src 一起进 git，`git push -u origin main`（SSH 部署密钥已可用）。不要提交 `runs/`、`_build/`、`*.agdai`。
