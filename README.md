# chrono-harness-inputs

从固定版本读取检查输入。

运行 `./check.sh` 验证独立组件。证明使用 Verus 0.2026.04.24.f8e1704，通过环境变量 `VERUS` 指定可执行文件。

[固定来源](https://github.com/ChronoAIProject/chrono-harness/tree/5f6892dfa2f73675a84e4ebdc3b06eb83b824d6e/crates/inputs)

有执行单元的宿主运行 `compose` 时，在 PATH 中安装本仓 mise 清单校验的两个命令。inputs 将固定的 base 和 candidate 提交交给 `chrono-judge-filemap endpoint-tests`，再把它返回的测试和退役测试交给 `chrono-judge-routes global-selection`。登记错误或无法退役的测试会使 compose 失败。capture、pair 和没有执行单元的 compose 可单独运行。
