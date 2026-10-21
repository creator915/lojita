# 07 里程碑：每一步做什么、怎么验、怎么退

一句话：六步，顺序不能换。每步列改哪些文件、按什么顺序动手、验收命令与期望、完成标志、回滚。M2 之前不接真 LLM。

```
 M0 Agda 侧 ──▶ M1 后端 v8 ──▶ M2 单节点（twice）──▶ M3 两层树（pow / mul）──▶ M3′ 反驳 ──▶ M3″ 改设计 ──▶ M4 keep ──▶ M5 以后
 全 refl         drive.sh         真 LLM                 dry 再真 LLM             dry        dry             dry 再真 LLM
```

## M0 Agda 侧：类型先对

**目标**：`Env` 的四处改动、两条引理、`Node.agda`、`ToyNode.agda` 六局全 refl、十个反例全被拒。不碰后端。

**改哪些文件**

| 文件 | 动作 | 看哪页 |
| --- | --- | --- |
| `src/Path.agda` | 新：Path、isPrefix、prefix-++、≤ᵇ-refl、half、half-≤ | 03 §1 |
| `src/Env.agda` | 改：路径键；Query / Item；ask；Move / Filled / transport；audit；`checkAt`；`_▸_` 只记接口 | 03 §1–5 |
| `src/ToyEnv.agda` | 改：Script、步号、respS 三个分支、键改路径 | 06 §1 |
| `src/StoreToy.agda` | 改：键改路径 | 06 §2 |
| `src/DriveToy.agda` | 改：`kid` 的 realm 改路径（新程序留到 M1） | 06 §3 |
| `src/Node.agda` | 新：§1–§7 | 04 |
| `src/ToyNode.agda` | 新：六局 | 04 §9 |
| `tests/neg/NegRealm.agda`、`NegWiden.agda` | 改：路径 | 06 §8 |
| `tests/neg/NegTransport.agda`、`NegNote.agda`、`NegPeek.agda` | 新 | 06 §8 |
| `tests/store/logtx.py`、`tests/gen/LogTx.agda` | 改：键按 `/` 拆 | 03 §6 |
| `check.sh` | 改：加新文件 | 06 §9 |

**顺序**：Path → Env（先只改类型，让 check.sh 报出所有要改键的地方）→ ToyEnv / StoreToy / DriveToy / neg 改键 → check.sh 过 → Node（§1–§5 先，再 §6–§7）→ ToyNode S1 → S2 → … → S6。

**验收**

| 编号 | 命令 | 期望 |
| --- | --- | --- |
| M0-1 | `./check.sh` | 无 error，退出码 0（含 ToyNode 六局 refl） |
| M0-2 | `./neg.sh` | 十行 `rejected as expected` |
| M0-3 | `./store.sh` | F 组四条过；B 组若后端仍是 v7 会因为键是列表而 SKIP 或失败——允许，M1 恢复 |
| M0-4 | `grep -c prefixOf src/*.agda` | `0`（旧名字全没了） |
| M0-5 | `grep -n "sh\|eval\|goals" src/Node.agda` | 没有这些构造子出现在 NodeOp 里 |

**完成标志**：M0-1、M0-2、M0-4、M0-5 全过。

**回滚**：`git -C /root/lojita checkout -- src tests check.sh`。

**风险与判断**：`checkAll` 的索引写法最容易卡；卡住时先把 `keys` 定成长度 2 的具体列表写通，再推广到列表递归。`prefix-++` 若证不出，看 `isPrefix` 是否真的用了 `discreteString`（用 `primStringEquality` 就证不出）。

## M1 后端 v8：手跟上

**目标**：`05-backend.md` 的六处改动；`drive.sh` 九个新程序过；`store.sh` 28 过；`schema.py`、`report.py` 能跑。

**改哪些文件**

| 文件 | 动作 | 看哪页 |
| --- | --- | --- |
| `/root/agda-backend/v8/Drive.hs`（及 agda-source 里的同一文件） | 改：join、ask、transport、checkAt、audit、by、接口缓存、script 分隔 | 05 §1–7 |
| `Agda.cabal` | 不改（regex 若要用 `regex-tdfa`，先确认 cabal store 里有；否则手写行首匹配） | 05 §9 |
| `src/DriveToy.agda` | 改：九个新程序 | 06 §3 |
| `tests/node/scripts/drive-split.txt` | 新 | 06 §5 |
| `tests/store/schema.py`、`tests/node/report.py` | 新 | 06 §6、§7 |
| `drive.sh`、`store.sh` | 改 | 06 §9 |

**顺序**：join（跑 store.sh B 组回到 25 过）→ by 字段 → ask → transport whole → transport fill → audit → 接口缓存 → script 分隔 → DriveToy 九个程序 → schema.py → report.py。每一步构建、安装、跑一遍 `./drive.sh` 看旧程序没坏。

**验收**：`05-backend.md` §10 的 B1–B13 全过，外加：

| 编号 | 命令 | 期望 |
| --- | --- | --- |
| M1-1 | `./store.sh` | `28 passed, 0 failed` |
| M1-2 | `./drive.sh` | 二十三个程序每个下一行等于注释 |
| M1-3 | `/root/agda-backend/agda-source/test/CubicalRuntime/run-tests.sh` | 通过 |
| M1-4 | `python3 tests/store/schema.py runs/drive-fillOne` | `OK` |
| M1-5 | `ls -la /usr/local/bin/agda*` | `agda → agda-cubical-run.v8`；v7 还在 |

**完成标志**：M1-1 到 M1-5 全过。

**回滚**：`ln -sf /usr/local/bin/agda-cubical-run.v7 /usr/local/bin/agda`；Lojita 侧 `git checkout -- src/DriveToy.agda drive.sh store.sh`。

**风险与判断**：fill 拼出来的文本 `prettyModule` 打印后 Agda 读不回去（mixfix 回成前缀应用是已知的）——用 `fillOne` 的 check 结果判断；若 check 报 parse 类错误，看 `code/M1.agda` 的文本。

## M2 单节点：任务一重做

**目标**：`Boot.agda` 的 `twice`；dry 用预置答卷过；真 LLM 十局。

**改哪些文件**

| 文件 | 动作 | 看哪页 |
| --- | --- | --- |
| `src/Boot.agda` | 新：E₀、配额、树深、三个任务的 spec 常量、`main` 三个 | 08 §2 |
| `tests/node/scripts/twice-*.txt` | 新 | 06 §5 |
| `node.sh` | 新 | 06 §9 |
| `check.sh` | 加 Boot | |

**验收**

| 编号 | 命令 | 期望 |
| --- | --- | --- |
| M2-1 | `./node.sh dry tests/node/scripts/twice-pass.txt` | `result: solved 2 twice/code/Twice.agda twice/code/TwiceTest.agda`；`schema.py` OK；report 显示 `twice rounds=1` |
| M2-2 | `./node.sh dry tests/node/scripts/twice-fail-once.txt` | `solved`；report `rounds=2`；`--prompt` 第二条提示词含第一轮的报错原文 |
| M2-3 | `./node.sh dry tests/node/scripts/twice-fail-only.txt` 然后 `./node.sh dry tests/node/scripts/twice-pass.txt --same-dir <上一局目录>` | 第一局 `exhausted`；第二局 `solved`，且第二局第一条提示词含第一局的 verdict（A5） |
| M2-4 | dump 里 `twice/code/Twice.agda` 的文本 | `twice : ℕ → ℕ` 后面跟着 LLM 给的子句；没有 `postulate` |
| M2-5 | `LOJITA_API_KEY=… ./node.sh run twice 10` | `solved ≥ 9/10`；每局 `schema.py` OK |
| M2-6 | 每局结束时后端进程的最大 RSS（`/usr/bin/time -v` 包一层） | < 500 MB，十局之间不增长 |

**完成标志**：M2-1 到 M2-5 全过。

**回滚**：删 `runs/twice-*`；`git checkout -- src/Boot.agda node.sh`。

## M3 两层树：pow 要 mul

**目标**：根的 stub 已 import `Mul`，所以第一轮必然是分解；dry 过；真 LLM 跑。

**验收**

| 编号 | 命令 | 期望 |
| --- | --- | --- |
| M3-1 | `./node.sh dry tests/node/scripts/pow-design.txt` | `result: solved 4 …kids/mul/code/Mul.agda …MulTest.agda pow/code/Pow.agda pow/code/PowTest.agda`（孩子在前） |
| M3-2 | report | `pow rounds=1 result=solved 4`，`kids/mul rounds=1 result=solved 2` |
| M3-3 | dump：`pow/verdict/1` | 含洞阶段留下的 postulate 数（`deferred=<k>`） |
| M3-4 | `schema.py` | OK（I4：mul 的 spec 先于它的第一条 trace） |
| M3-5 | `report.py --check-isolation` | `isolation OK` |
| M3-6 | `LOJITA_API_KEY=… ./node.sh run pow 5` | `solved ≥ 3/5`（分解对 LLM 更难；记下失败局的 verdict 作为改提示词的依据） |

**完成标志**：M3-1 到 M3-5 全过，M3-6 至少 1 局 solved。

## M3′ 反驳：矛盾的根

**目标**：根的 spec 自相矛盾（`test1 : f 0 ≡ 1`、`test2 : f 0 ≡ 2`），agent 交反驳。

| 编号 | 命令 | 期望 |
| --- | --- | --- |
| M3′-1 | `./node.sh dry tests/node/scripts/contra-refute.txt` | `result: refuted contra/code/ContraRefute.agda` |
| M3′-2 | dump：`contra/code/ContraRefute.agda` | 含 `absurd : ⊥`，不含 `postulate` |
| M3′-3 | 把脚本里的反驳改成含 `postulate` 的版本再跑 | `exhausted`，`verdict/1` 含 `unsafe` |
| M3′-4 | `LOJITA_API_KEY=… ./node.sh run contra 3` | 至少 1 局 refuted |

## M3″ 改设计：孩子反驳，父重来

| 编号 | 命令 | 期望 |
| --- | --- | --- |
| M3″-1 | `./node.sh dry tests/node/scripts/pow-redesign.txt` | `solved 4` |
| M3″-2 | report | `pow rounds=2 memos=2`；`kids/mul rounds=2`（第一次 refuted，第二次 solved） |
| M3″-3 | dump：`pow/memo/1` | 含孩子反驳的键 |
| M3″-4 | dump：`pow/kids/mul/spec/stub` | 最后一次写入的是第二版（log 里两条，后者胜） |

## M4 keep：一个孩子不受影响

| 编号 | 命令 | 期望 |
| --- | --- | --- |
| M4-1 | `./node.sh dry tests/node/scripts/two-kids-keep.txt` | `solved` |
| M4-2 | report | `kids/a rounds=1`（只跑了一次）；`kids/b rounds=2` |
| M4-3 | log：`twokids/kids/a/trace/` 的行 | 全部早于根第二次 ask 的步号 |
| M4-4 | `schema.py` | OK |
| M4-5 | 真 LLM：设计一个两孩子的任务跑 3 局 | 记录；不设通过线 |

## M5 以后（另开计划）

- Rebuilder 读 Store：`Replay.wrap` 的录音 = `trace/`；`iface/p` 两个哈希由后端写；keep 用哈希不用逐字比。
- 并发孩子：Σ 加"未就绪"，`Exec` 换成 restarting；"B 中途被杀"才真的出现。
- Code 换 abstract 语法：unit 级的 M（改名、拆分、闭包沿 `Export.deps` 传）。
- 压缩工具：剔掉不可达前缀。
- IO 根与 mock、内核 + 壳 + 协议文件：`08-root-session.md` §4。
- Σ 重排成"目录 × 四类操作"的 record；restarting 版里对 spec 文件的 write 触发孩子 agent 的 open：`10-files-resources.md`。
- 文件更新接 GitHub（write = commit）：记一笔，不做。

## 判断"搞乱了"的速查

| 症状 | 多半是 | 看哪页 |
| --- | --- | --- |
| `check.sh` 报 `String != List String` | 某个键没改成路径 | 03 §6 |
| `check.sh` 在 Node 的 `set…` 处 unsolved meta | 少给了 `prefix-++` 的证明 | 03 §1、04 §3 |
| `drive.sh` 打 `unknown step transport` | 后端没装 v8，或分派表少行 | 05 §9 |
| `store.sh` B 组 dump 不等 | join 的 `/` 多了少了 | 05 §1 |
| 一局跑完 `schema.py` 报 I2 | 某处用 set 写了 code/ | 04 §2、05 §5 |
| 一局跑完 `schema.py` 报 I4 | design 里 transport 与 enter 顺序反了 | 04 §7.2 |
| Agda 无限 "Checking" | 接口缓存策略 | 05 §6 |
| LLM 总被驳回 "imports not in the header" | E₀ 名单与提示词不一致 | 08 §3 |
