# chrono-harness-inputs

从固定版本读取检查输入。

在集成工作树运行 `mise exec -- ./check.sh`，按固定 Git 变更和本仓 FILEMAP 验证快照。选中快照单元时，CI 执行产品与独立边界两个 Verus 根和原生测试，汇总读取该单元原报告。未登记证明根的其他代码保留未知覆盖。

[固定来源](https://github.com/ChronoAIProject/chrono-harness/tree/5f6892dfa2f73675a84e4ebdc3b06eb83b824d6e/crates/inputs)

有执行单元的宿主运行 `compose` 时，在 PATH 中安装本仓 mise 清单固定的命令。inputs 将固定的 base 和 candidate 提交交给 `chrono-judge-filemap endpoint-tests`，再把它返回的测试和退役测试交给 `chrono-judge-routes global-selection`。再由 `chrono-judge-registration collection-inputs-v1` 返回两端所需输入。登记错误或无法退役的测试会使 compose 失败。capture 通过宿主 PATH 中的 chrono-judge-registration capture-plan-v1 核对配置选择和需要捕获的输入 ID。inputs 由同一个已绑定的 chrono-harness git-facts-v1 会话读取固定提交中的登记，按选择捕获环境和文件。已登记的外部查询由 chrono-harness run-command-v1 限制执行时间、输入与输出。采用宿主保管策略时，通过 chrono-harness retained-artifacts-v1 写入、保留原件并交接报告消费者。未启用保管或日志的宿主可以在空 PATH 离线运行 pair。启用滚动日志时使用安装的 chrono-diagnostics cli-events-v1 记录业务进程和实际退出状态。

离线传输直接读取 `chrono-input-snapshot/v1` 至 `v3` 数据，核对端点、选择器、文件地址与内容身份。没有执行单元时，compose 仅按两端有效配置中的环境和文件声明核对覆盖。带执行单元时仍由上述判官解释完整登记。

采集已安装工具时，固定配置须把 `.chrono-harness/bin/` 中的同一个程序登记为工具和带 SHA-256 的 present 输入。注册判官可在捕获计划中返回该输入 ID 对应的外部安装文件绝对路径。采集器从该文件读取原字节，核对登记摘要，再发布快照。普通文件输入沿用其登记的位置。

## 本地检查的保留窗口

本仓的本地完整检查在 `.chrono-harness/state/collection/check.json` 发布报告。需要保留的结果应在 24 小时内将报告及其引用的原件转存至检出外，并从接收位置读回。各 Verus 操作的编译库和依赖文件由项目判官读取，成功后由当前操作释放。

在长期开发检出上，按实际仓库和 mise 路径在用户 crontab 安装下列条目。每小时调用同一个模板任务；到期报告在读取和交付义务结束后释放，后续维护回收已无引用的原件。机器在线并启用该定时任务时，维护会在没有后续业务命令的情况下运行。

```cron
0 * * * * cd '/absolute/path/to/repository' && '/absolute/path/to/mise' run harness-maintain-checks >/dev/null
```
