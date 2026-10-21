# Store 的硬盘余模型：计划、验收标准与结果（阶段 1，2026-10-13 → 10-14，已完成）

一句话：后端在硬盘上实现 `WSig = {get, set}` 的余模型。一局一个目录，`log.jsonl` 只追加，`blob/` 放大字段，
内存里一张有序表是日志的 fold。Agda 这边 `AgdaSig` 用 `get` / `set` 换掉 `readF` / `writeF`，realm 进栈帧。
验收只认一个方块：后端 dump 出来的快照 = 日志的 fold = `Store.world` 算出来的 Board。

已定：不接 SQLite / Postgres，手写；硬盘可以就地改，因为它被线性地调用（点不变）。
三条拍板：realm 进类型；阶段 0 归档到 `archive/2026-10-13-bench/`；阈值 2 KB、sha256、二进制叫 v7。

```
  Agda（纯，--safe --cubical）                 后端（就地改，被线性地调用）
  ─────────────────────────────                ───────────────────────────────────
  Keys.agda  S = Store String String           runs/<局>/
    S.world : Board → WOp → Res × Board          log.jsonl      一行一条 set（get 不落盘）
    S.runTx / S.realm                            blob/<sha256>  大于 2 KB 的值
  Env.agda   AgdaSig：get k / set k v           内存 Map String Val = 启动时 fold 日志
    Ix 栈帧 = (Env , 配额 , realm 前缀)         --cubical-handler=store:DIR
    enter h q p 压 realm，leave 弹               enter 压前缀、leave 弹前缀
```

验收的方块：

```
        目录 ────── 一步 get / set ──────▶ 目录
         │                                  │
       dump                               dump        dump = --cubical-store-dump=DIR（新）
         ▼                                  ▼
       Board ────────── world ───────────▶ Board      两条路相等；回应也相等
```

## 一、日志格式

```
{"n":12,"step":34,"op":"set","k":"a/x","v":"1","r":""}            小值内联
{"n":13,"step":35,"op":"set","k":"trace/3/reply","h":"3f2a…","r":"a/"}   大值：sha256，正文在 blob/3f2a…
```

- `n` 行号（跨重启单调，就是事务里的位置），`step` 驱动器这一局的步号，`k` 键，`v` 值或 `h` 哈希，`r` 写入时生效的 realm 前缀。
- 只记 set。读不造版本，所以读不落盘，直接查内存表。
- 每写一行：`hFlush`（进程被杀也不丢）再 `fsync`（机器断电也不丢，1.3 ms）。
- 开局恢复：逐行读；最后一行没有换行或解析失败 = 撕裂行，丢弃并把文件截回上一完整行；fold 成 Map；校验每个哈希的 blob 文件都在；步号接着记。
- 值 > 2 KB 进 `blob/<sha256>`：先写临时文件再改名；已存在就跳过（同内容自动去重）。

## 二、改哪里

### Agda 侧（Lojita）

| 文件 | 改动 |
| --- | --- |
| `src/Keys.agda`（新，约 40 行） | `discreteString`：由内建引理 `primStringToListInjective`、`primCharToNatInjective` 加 `discreteℕ`、`discreteList` 推出，零 postulate；`prefixOf : String → String → Bool`；`module S = Store String String discreteString discreteString`，就是后端要实现的那个 Store |
| `src/Env.agda` | `Frame = Env × ℕ × String`，第三项 = realm 前缀，`""` 是 whole；`enter h q p`，前置条件 `prefixOf (realmOf ix) p`（子只能更窄）；`get k` 回 `Maybe String`，无前置条件，realm 外由余模型答 `nothing`（这是 `restrictL`）；`set k v` 回 `Unit`，前置条件 `prefixOf (realmOf ix) k`（越界写是类型错，比 `mergeL` 的"丢掉"更严，结果一致）；删 `readF` / `writeF`；`next` 对 get / set 不变环境 |
| `src/ToyEnv.agda` | `W ix = List Verdict × S.Board`；get / set 用 `S.world` 回答，realm 外的 get 回 `nothing`；`ix₀` 多一项 `""` |
| `src/StoreToy.agda`（新） | 真后端跑的程序：`roundtrip` `missing` `overwrite` `kidSees` `kidWrites` `persist1` `persist2` `commuteXY` `commuteYX` `big` `stress` |
| `tests/neg/NegRealm.agda`、`NegWiden.agda` | 子实例写 realm 外的键；子实例要一个比父宽的 realm。都必须编译失败 |
| `src/DriveToy.agda` | 写出来的索引里 Frame 多一项，机械改（约 6 处） |
| `check.sh`、`neg.sh`、`store.sh`（新） | check 加 Keys / StoreToy；store.sh 跑下面 B1–B8 |

已知限制：`set` 的前置条件要在类型检查时算出 `true`，所以子实例里的键要写成字面量；根上 realm 是 `""`，任何键都算得出。

### 后端侧（agda-backend）

只动 `Drive.hs` 和 `Runtime.hs`；fsync 用 `unix` 包，若 `Agda.cabal` 没列它就加一行（GHC 自带库，不用下载）。

| 处 | 改动 |
| --- | --- |
| `Handlers` | 删 `hRead` / `hWrite` / `allowed`；加 `hStore`：目录、日志句柄、`IORef (Map String Val)`、步号、realm 栈 |
| `store:DIR` | 开局：建目录和 `blob/`；按 §一 恢复；没配 store 时 get / set 拒答停机 |
| `get` | realm 外 → `nothing`；查 Map；`Blob h` → 读 `blob/h` |
| `set` | realm 外 → 拒答停机（类型上到不了，兜底）；> 2 KB 写 blob；追加一行；flush + fsync；更新 Map |
| `enter` / `leave` | `enter` 多一个显式参数 p，压 realm 栈；`leave` 弹 |
| `--cubical-store-dump=DIR` | 不跑程序，打印 Map 为 JSON（大值打哈希）。就是上图的 snapshot 箭头 |
| 构建 | `cabal build agda-cubical-run` → `/usr/local/bin/agda-cubical-run.v7`，`agda` 指过去；源码存 `/root/agda-backend/v7/`；v6 二进制留着，回退一条 `ln -sf` |

## 三、验收标准

### A 组：Agda（`./check.sh`、`./neg.sh`）

- A1 全部模块 `--safe --cubical` 通过，零 postulate。
- A2 ToyEnv 四个 refl：写后读 `just`；读缺席 `nothing`；同键两次写后写赢；子实例读 realm 外 `nothing`。
- A3 两个反例必须编译失败。

### B 组：真后端（`./store.sh`，每条用独立目录）

- B1 回环：`roundtrip` → `just "1"`；`missing` → `nothing`；`overwrite` → `just "2"`。
- B2 子实例：`kidSees` → `(just "1" , nothing)`；`kidWrites` 之后父读 → `just "9"`。
- B3 重启：`persist1` 跑完换进程跑 `persist2`，读到全部值；日志行数 = set 的次数，不多不少。
- B4 撕裂与被杀：`persist1` 后用 `truncate` 砍掉最后一行的一半，再跑 `persist2`：撕裂行被丢弃，文件截回完整行，被砍那一步读到 `nothing`，之后追加正常。`stress` 跑到一半 `kill -9`，重启后 dump 可读且等于完整行的 fold。
- B5 方块：`dump` 与一个独立的十行 python fold 相等；`commuteXY` / `commuteYX` 两局的 dump 相等（不同键可换）。
- B6 大字段：`big` 写 100 KB，日志行只有哈希，`blob/` 恰一个文件，get 回原文 `wc -c` 相等；同值写两次不重复。
- B7 性能：`stress` 一万次 set + get。总时 < 2 分钟（含 Agda 归约，平均 < 10 ms/步）；每秒采样 RSS，首尾差 < 50 MB；日志大小随步数线性。
- B8 日志是棋谱：脚本把 `log.jsonl` 转写成 `tx : S.Tx`，Agda 用 refl 验证 `S.runTx tx (λ _ → nothing)` 在每个键上等于 dump 的值。后端写、Agda 查。

## 四、顺序

0. 阶段 0：`Solve` `Bench` `Str` `task1*.sh` 和 `bench/` 的临时脚本移到 `archive/2026-10-13-bench/`；`check.sh` 去掉 Solve、Bench。它们写死了 `(E₀ , n) , []`，Frame 一变就坏，正好先走。
1. Keys、Env、ToyEnv、neg、DriveToy → A1–A3 过。
2. Drive.hs、Runtime.hs → 构建 v7 → StoreToy + store.sh → B1–B8 过。
3. 本文改名 `store-backend.md` 记录结果；README 的架构图加 Store 一层。

## 五、待拍板

1. realm 进类型（推荐）还是只在后端拦。
2. 阶段 0 是归档（推荐）还是直接删。
3. 阈值 2 KB、哈希 sha256、二进制叫 v7：没有异议就这么定。

## 六、进度：测试数据已出（2026-10-13 夜）

先于后端写好的东西，全部通过 `./check.sh`、`./neg.sh`、`./store.sh` 的 F 组：

| 东西 | 状态 |
| --- | --- |
| 阶段 0 | Solve / Bench / Str / task1*.sh / bench 的 run.sh relay.py dry.sh replay.sh → `archive/2026-10-13-bench/`，附 README |
| `src/Keys.agda` | `discreteString`、`module S = Store String String …`。`prefixOf` 放在 Env.agda（Env 不必依赖 Store） |
| `src/Env.agda` | 栈帧 `Env × ℕ × String`、`realmOf`、`enter h q p`、`get` / `set`（§二的类型原样） |
| `src/ToyEnv.agda` | `W ix = List Verdict × S.Board`，`emptyBoard`（`empty` 与 cubical 的 isOneEmpty 撞名），get 按 realm 答、set 用 `S.upd` |
| `src/StoreToy.agda` | 十一个程序 + §7 九条 refl（A2 全过，含"换进程 = 把跑完 persist1 的盘交给 persist2"） |
| `tests/neg/NegRealm.agda`、`NegWiden.agda` | 都以 UnsolvedMetaVariables 在 set / enter 处失败：前置条件算成 ⊥，解不出 |
| `tests/store/` | 三组样例日志（basic / torn / blob）+ `expected.json`；`fold.py`（独立 fold）；`logtx.py`（日志 → Agda refl）；README |
| `store.sh` | F 组四条已过（fold 三组样例、LogTx 由 Agda refl 复算）；B 组等 v7，没有二进制时 SKIP 退出码 2 |
| `drive.sh` | v6 上除 `kid` 外照跑；`kid` 要等 v7（`enter` 从 3 个参数变成 5 个） |

B8 已经在样例上验证：`S.runTx` 经 `discreteString` 在 Agda 里按 refl 归约，后端写、Agda 查这条路通。

给后端实现的几个定数（从测试数据反推）：
- `enter` 的参数在 Drive.hs 里是 `[h, q, p, _, _]`：第三个显式参数是 realm 前缀，后两个是证明，不解码。
- `set` 的参数是 `[k, v, _]`。`get` 是 `[k]`。回应 `VMaybe (Just (VStr v))` / `VMaybe Nothing` / `VUnit`。
- `--cubical-store-dump=DIR` 仍带一个 .agda 文件参数（Agda 的命令行要求），打印与 `fold.py` 逐字节相同的 JSON：键有序、无空格、大值 `{"h":…}`。
- 日志行字段顺序不限，fold 只看 `op` / `k` / `v` / `h`；撕裂行 = 没有换行的最后一行；中间坏行是损坏，开局报错。

## 七、验收结果（2026-10-14）

后端 v7：`/root/agda-backend/V7-STORE.md`，只动 Drive.hs、Runtime.hs，cabal 加 crypton（sha256）。默认 `agda` 已指向 v7。

| 项 | 结果 |
| --- | --- |
| `./store.sh` | 25 过 0 败（F 组 4、B1–B8 共 21） |
| `./drive.sh` | 十二个程序全过，含 `kid`（enter 带 realm） |
| `./check.sh`、`./neg.sh` | 过；七个反例都被拒 |
| 后端 v2 回归 `run-tests.sh` | 过 |
| B7：一万次 set + get | 15 s，CPU 1.6 s，其余是一万次 fsync（约 1.3 ms 一次） |
| B7：RSS | 221 MB 平直；GHC 最大驻留 117 MB |
| B7：日志 | 10000 行，线性 |

一个坑，记下来当规矩：`stress` 第一版写成 `loop n (if … then bad else suc bad)`，归约器不会先算那个 if，
一万步后累加器积成一万层的项：124 s、RSS 涨 146 MB。改成先按比较结果分支再递归（控制流依赖它，归约器就得算）之后 15 s、RSS 平直。
**Run 程序里传给下一步的参数要先算出来**；这和"大内容不进 Agda"是同一条性能主线。
