# chrono-harness-inputs

从固定版本读取检查输入。

运行 `./check.sh` 验证独立组件。证明使用 Verus 0.2026.04.24.f8e1704，通过环境变量 `VERUS` 指定可执行文件。

[固定来源](https://github.com/ChronoAIProject/chrono-harness/tree/5f6892dfa2f73675a84e4ebdc3b06eb83b824d6e/crates/inputs)

有执行单元的宿主执行 compose 时，inputs 将两端固定登记文档和 FILEMAP 给出的测试 ID 交给已安装的 chrono-judge-routes global-selection。本仓 mise 清单按平台校验路由工具 v0.1.0-alpha.1。查询只读标准输入，退役错误通过 compose 返回。capture、pair 以及没有执行单元的 compose 可单独运行。
