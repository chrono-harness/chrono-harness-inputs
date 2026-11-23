# chrono-harness-inputs

从固定版本读取检查输入。

运行 `./check.sh` 验证独立组件。证明使用 Verus 0.2026.04.24.f8e1704，通过环境变量 `VERUS` 指定可执行文件。

[固定来源](https://github.com/ChronoAIProject/chrono-harness/tree/5f6892dfa2f73675a84e4ebdc3b06eb83b824d6e/crates/inputs)

有执行单元的宿主运行 `compose` 时，在 PATH 中安装本仓 mise 清单固定的命令。inputs 将固定的 base 和 candidate 提交交给 `chrono-judge-filemap endpoint-tests`，再把它返回的测试和退役测试交给 `chrono-judge-routes global-selection`。再由 `chrono-judge-registration collection-inputs-v1` 返回两端所需输入。登记错误或无法退役的测试会使 compose 失败。capture 通过宿主 PATH 中的 chrono-judge-registration capture-plan-v1 核对配置选择和需要捕获的输入 ID。inputs 自己从固定 Git 提交取得登记，并读取所选环境及文件形成快照。pair 和没有执行单元的 compose 可单独运行。

离线传输直接读取 `chrono-input-snapshot/v1` 至 `v3` 数据，核对端点、选择器、文件地址与内容身份。没有执行单元时，compose 仅按两端有效配置中的环境和文件声明核对覆盖。带执行单元时仍由上述判官解释完整登记。
