# Harness v8 开发文档（2026-10-21）

这一夹文档把 `../harness-plan.md` 的方案展开到能照着做、照着验的程度。每一页对应系统的一个部件：
它是什么、长什么样、和谁相连、怎么验收、搞乱了怎么退回。**不读代码也能照着验收**：每条验收标准都是一条命令加一行期望输出。

比 harness-plan.md 多出的设计，来自 10-21 后半段与 10-22 的讨论：

1. 底层是**关系式的文件库**：文件是一行带属性的记录，文件之间的依赖是一等公民的表（持有 / 引用两种），文件夹是查询。见 `01-objects.md`。
2. agent 分**两类**：挂在一个文件上的文件 agent（memory 和权限都挂在那个文件上），和挂在根上的根会话。见 `02-agents.md`。
3. **一切皆文件**：Σ 是一个目录，每个抽象文件有 open / close / read / write 四类操作；进程、硬件也是文件；权限 = 文件 × 操作类型。见 `10-files-resources.md`。
4. **每个文件配一个抽象 agent**：memory + 权限；1.agent 能读写 1.agda、能 open / read / write 2Test.agda、能 open 2.agent；树内固定、树外开放。见 `02-agents.md` §2.3、§2.8。
5. **内核 + 壳 + 协议文件**：微服务 = Agda 内核 + IO 壳；同一环境里两个内核交互，写一个 Agda 协议文件把两棵树拼成一棵，再给它一个壳；多个壳可以调同一个内核。见 `08-root-session.md` §4。
6. 文件更新接 GitHub（write = commit）：记一笔，不做。见 `10-files-resources.md` §11。

一处随之改动：父 agent 不再 `get` 孩子的正文交给 check，而是 `checkAt` 让检查器读；agent 对孩子的 code 只有 open 没有 read。

两处小改名：测试模块叫 `XTest`、反驳模块叫 `XRefute`，不用带点的 `X.Test`（虚拟模块按名字落文件，带点要建目录）；
stub 可以含具体定义（规约里用到的谓词、类型），洞只是其中的 `postulate` 块。

## 阅读顺序

```
 README（本页）──▶ 01 对象 ──▶ 02 agent ──▶ 10 一切皆文件 ──▶ 07 里程碑（先看要做什么、怎么验）
                                                                │
                 ┌──────────────┬──────────────┬────────────────┼──────────────┐
                 ▼              ▼              ▼                ▼              ▼
              03 Env.agda    04 Node.agda   05 后端 v8      06 玩具与测试   08 根会话
                                                                               ▼
                                                                           09 术语表
```

| 文件 | 讲什么 | 什么时候看 |
| --- | --- | --- |
| `01-objects.md` | 文件、关系、持有与引用、搬运的一条原则、删除、Store 键表 | 开工前；写任何一行 Store 代码前 |
| `02-agents.md` | 文件 agent 与根会话：memory、权限、能做什么、生命周期 | 开工前 |
| `03-env.md` | `Env.agda` 的改动逐条：路径键、Query、transport、audit，两条引理 | M0 |
| `04-node.md` | `Node.agda` 逐段：NodeSig、node 主循环的每个分支、沙箱与粘合 | M0 |
| `05-backend.md` | 后端 v8 逐条：join、ask 渲染与拆文件、transport、audit、接口缓存 | M1 |
| `06-toys-tests.md` | ToyNode、改键的 ToyEnv / StoreToy、DriveToy 新程序、新反例、脚本、检查器 | M0、M1 |
| `07-milestones.md` | M0–M5 每步：改哪些文件、按什么顺序、验收命令与期望输出、完成标志、回滚 | 全程 |
| `08-root-session.md` | 根会话、Boot.agda、E₀ 怎么定、IO 根与 mock、多根 | M2 起 |
| `09-glossary.md` | 符号与术语 | 随时 |
| `10-files-resources.md` | 一切皆文件：抽象文件与四类操作、Σ 是一个目录、open / close 的线性纪律、权限 = Σ、agent 文件的生命周期、硬件与挂载表、能验什么 | 开工前；M5 前再读 |

## 全景一：harness 操作的对象

```
 E₀（任务开工定死的包与 flag；任务中唯一能被多个文件 import 的东西）
   ▲ 引用（reference：只读内容，不管存在）
   │
 <R>/              根文件 R.agda + RTest.agda          根会话写它的 spec；根的文件 agent 填它
   ├── kids/A/     A.agda + ATest.agda                 R 持有 A（holding：A 因 R 的洞而存在；R 丢弃 A，A 整个到 1）
   │    └── kids/A1/ …                                 A 持有 A1
   └── kids/B/     B.agda + BTest.agda

 一条原则：被依赖的接口动了，依赖它的跟着动；接口没动，链到此终止
   A1 的正文变  →  A 不动（A 只看 A1 的接口 = A 写给 A1 的 spec）
   A1 反驳 spec →  A 必须改设计 → A 的正文变 → R 不动，除非 A 也反驳
```

## 全景二：仓库里的源文件

```
 生成（agda-code-gen，永不手改）    Syntax.agda   FlagTable.agda
                                         │             │
 骨架（不动）    Game ─▶ PathCat ─▶ Harness ─▶ Replay   │   Later ◀── PathCat
                  │                                     │     │
                  └─────▶ Store ─▶ Keys                 ▼     ▼
 环境（改）                        Path.agda(新) ─▶ Env.agda(改)
                                                      │
 节点（新）                                           ├─▶ Node.agda(新) ─▶ ToyNode.agda(新)
                                                      │        └────────▶ Boot.agda(新，M2)
 玩具（改）                                           ├─▶ ToyEnv.agda(改) ─▶ StoreToy.agda(改)
                                                      └─▶ DriveToy.agda(改)
 反例            tests/neg/*.agda：7 个 → 10 个
 检查器          tests/store/fold.py（有） schema.py（新）   tests/node/report.py（新） tests/node/scripts/*.txt（新，预置答卷）
 脚本            check.sh  neg.sh  drive.sh  store.sh  node.sh（新）
 后端 v8         /root/agda-backend/v8/：Drive.hs（改） Runtime.hs（不动） Code.hs（不动） → /usr/local/bin/agda-cubical-run.v8
```

箭头是 import。每个文件的状态（不动 / 改 / 新 / 生成）和它的验收，在 `06-toys-tests.md` 与 `07-milestones.md` 的表里逐个列。

## 全景三：一个文件 agent 的一轮

```
 spec（父写在我的前缀里）
   │ ask：后端把 Query 渲染成提示词，问 LLM，答卷按 "-- file:" 拆进 draft/，回文件名
   ▼
 draft/n/*.agda ──分类──┬─ 解答：transport fill → 沙箱 check（E₀⁻）→ 粘合 check（E₀，--safe）→ result = solved
                        ├─ 分解：写孩子 spec、transport whole 根正文 → 洞阶段 check → 逐个 enter 孩子 → 粘合 → solved
                        └─ 反驳：transport whole、audit → 沙箱 check → result = refuted
 没过 ──▶ verdict/n、memo/n ──▶ 下一轮（配额 −1）；配额 0 ──▶ result = exhausted
```

## 验收总表

每个脚本检查什么、过了长什么样。细则在各页。

| 命令 | 检查什么 | 过了 |
| --- | --- | --- |
| `./check.sh` | 全部 Agda 模块在 `--safe --cubical` 下通过，含 ToyNode 的 refl | 没有任何输出以 `error` 开头；退出码 0 |
| `./neg.sh` | 十个反例全部编译失败 | 十行 `rejected as expected`，没有 `UNEXPECTED PASS` |
| `./store.sh` | Store 后端 F 组 + B 组 | 最后一行 `25 passed, 0 failed`（M1 后是 `28 passed`，加三条） |
| `./drive.sh` | 真后端跑 DriveToy 全部程序 | 每个 `--- 名字` 下面一行等于 drive.sh 注释里写的期望 |
| `python3 tests/store/schema.py runs/<局>` | 一局日志满足键表的全部不变量 | 一行 `OK` |
| `python3 tests/node/report.py runs/<局>` | 打印这一局的树：每个节点几轮、结局 | 一棵树；根的结局是 `solved` |
| `./node.sh dry <脚本>` | 用预置答卷跑一局（不接 LLM） | 最后一行 `result: solved …` |
| `LOJITA_API_KEY=… ./node.sh run <任务> N` | 真 LLM 跑 N 局 | 每局一行结局；汇总 `solved k/N` |

## 搞乱了怎么办

- Agda 侧全在 git 里。看改了什么：`git -C /root/lojita status`、`git -C /root/lojita diff src/Env.agda`。退回一个文件：`git -C /root/lojita checkout -- src/Env.agda`。
- `Syntax.agda`、`FlagTable.agda` 永不手改；若被改了，`git checkout` 回来。
- 后端退回 v7：`ln -sf /usr/local/bin/agda-cubical-run.v7 /usr/local/bin/agda`。v8 源码在 `/root/agda-backend/v8/`，二进制在 `/usr/local/bin/agda-cubical-run.v8`。
- 一局的 Store 在 `runs/<局>/`，整个目录可以删，不影响系统；永远不要手改 `log.jsonl`。
- 哪一条验收没过，就翻那一页的"验收"小节，每条验收标准旁边写着它对应哪个文件的哪一段。

## 文档之间的关系

```
 01 对象 ──定义键表──▶ 03 Env（键是 Path）、05 后端（谁写哪些键）、06 schema.py（检查键表不变量）
 02 agent ──定义两类──▶ 04 Node（文件 agent 的程序）、08 根会话（Boot）
 10 一切皆文件 ──把 Σ 读成目录──▶ 02 的权限表、03 的前置条件、05 的挂载表
 07 里程碑 ──引用──▶ 其余每一页的"验收"小节
```
