# tests/store —— Store 硬盘余模型的测试数据（验收见 docs/store-backend.md）

| 东西 | 作用 |
| --- | --- |
| `fixtures/basic/` | 三行日志，同键后写赢；`expected.json` 是快照 |
| `fixtures/torn/` | 第三行写到一半没有换行：快照只算前两行；后端开局必须把文件截回 `expected-recovered.jsonl` |
| `fixtures/blob/` | 一行大值（哈希在 `h`，正文在 `blob/<sha256>`）加一行小值 |
| `fold.py` | 独立的 fold：日志 → 快照 JSON。后端 `--cubical-store-dump=DIR` 必须打印同样的东西 |
| `logtx.py` | 日志 → Agda：`tx : S.Tx` 与每个键的 refl，后端写、Agda 查；键按 `/` 拆成路径，`S = Store Path String`（验收 E8） |
| `../../store.sh` | F 组（不要后端：fold / logtx 对样例）+ B 组（要 v7 后端：B1–B8） |

日志一行一条 set，字段：`n` 行号（跨重启单调）、`step` 驱动器的步号、`k` 键、`v` 小值或 `h` 大值的 sha256、`r` 写入时的 realm 前缀。get 不落盘。fold 只看 `op` / `k` / `v` / `h`。
