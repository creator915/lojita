# 归档：Code 的核心子集版（2026-10-13，当天归档）

这里是提交 `4671cae` 里的 `src/Code.agda`、`src/Load.agda`、`src/ToyCode.agda`、`src/DriveTests.agda`、`docs/code-type.md`、`drive.sh`、`drive-tests.sh`。
配套的后端 v5（`Runtime.v5.hs`、`V5-DRIVE.md`、二进制 `agda-cubical-run.v5`）在服务器 `/root/lojita-discarded/backend-v5/`。

## 为什么归档（用户定）

- Code 只做了 Agda 的核心子集：名字按层号、没有糖（where / with / let / 模块）、没有 import 和 flag、unsafe 被排除。要的是**完整的 Agda 宇宙**，糖和 unsafe 都在，import / flag 是作用在语境 / 余语境上的模态算子，必须有。
- 后端接在反射 API（unquoteDecl 背后的 declareDef / defineFun / declareData / defineData）上，所以只能覆盖那一块。应当像 IO 例子那样直接接 agda 程序的入口（parser / createInterface / normalise / 交互命令）。

新方案见 `docs/code-plan.md`。

## 还有用的

- `src/Later.agda` 留在主线：▷ 作为环境索引上的算子、带索引的 `Run`、路 `Walk`、余模型与 `play`，一字不改。
- 这里的 `Load.agda` 的形状（步 → 判决 → `next`；`loadThen`；`accepted`；脚本后端）可以照搬，把 `Decl Γ` 换成完整模块、`Verdict` 带回接口。
- 后端 v5 的三样机制可作 v6 参考：WHNF 循环喂续体、失败时 `putTC` 回滚、每拍补做 mutual 块末检查并把错误类警告当错误。
- 反例集（类型错、不停机、负性、引用未定义名）值得保留为新后端的验收。
