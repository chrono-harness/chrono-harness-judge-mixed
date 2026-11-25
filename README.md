# chrono-harness-judge-mixed

识别规则和产品的混合变更。

在任务工作树中运行 `./check.sh`。检查汇总读取本轮原件，Verus 的编译库和 dep-info 在成功核验后立即释放。需要长期保存的报告请在 24 小时内转存到工作树之外。

主检出负责登记和回收任务工作树。安装所选工具后，开发机可将下列条目加入用户 crontab，替换为本机主检出和 mise 的绝对路径。每小时的维护会检查实际租约、源码与提交的保全状况，回收到期工作树及其中的 `.chrono-harness/state/`、工具链接与构建目录。

```cron
0 * * * * cd '/absolute/path/to/chrono-harness-judge-mixed' && '/absolute/path/to/mise' exec -- chrono-worktree maintain --host-root . --config .chrono-harness/worktree.json >/dev/null
```

长期主检出的原生编译使用专属的 `.chrono-harness/native-check/`。整次标准检查持有工作树租约。同一项每小时维护在取得排他租约后批量回收已登记的临时目录，包括检查中断后遗留的 Cargo 文件。需要跨期使用的报告应在下一次维护前转存。外置 `CARGO_TARGET_DIR` 由调用方维护。迁移前遗留的 `target/check.*` 需先确认所有者和使用情况，再转存或移除。

[固定来源](https://github.com/ChronoAIProject/chrono-harness/tree/5f6892dfa2f73675a84e4ebdc3b06eb83b824d6e/crates/judge-mixed)

供 FILEMAP 使用的 `chrono-judge-mixed classify-v1` 从 stdin 读取 JSON。调用者给出 `base`、`candidate`、`delta`、`before` 和 `after`。两个端点分别包含工作流路径 `workflow`、本次各路径的 `surfaces` 映射及配置中的 `semantic_fields`。后两个对象按路径提供已声明语义字段所需的 JSON。调用者负责从固定端点取得这些数据。命令复用本仓判官的分类，成功向 stdout 返回规则路径、产品路径和具体变化，退出 0；输入无效时向 stderr 写出原因，退出 2。

需要从 Git 读取语义文档时，先向 `chrono-judge-mixed document-paths-v1` 提交 `base`、`candidate` 两组 semantic_fields 和 `delta`。返回的两个同名路径数组分别列出该端点存在且分类需要的文件。两个数据命令的 stdin 上限均为 64 MiB。

宿主调用原生 `--protocol chrono-judge/v1` 时，需要已安装的 `chrono-harness judge-pipeline` 和 `chrono-judge-registration classification-inputs-v1`。runner 核对封存请求和进程限额。mixed 核对 FILEMAP 和成本前置结果，按语义声明选择路径。registration 解释两端登记、读取所选提交中的文档，并在响应中保留绑定的 Git 读取记录。单独运行 `classify-v1` 和 `document-paths-v1` 只需 mixed 本身。

主检出的一次完整检查会产生 `.chrono-harness/state/preparation/` 和 `collection/` 中的报告。单独运行本仓单元时，报告写入 `mixed/`。三个目录位于同一个 `.chrono-harness/state/` 下，按上方每小时维护批次回收。需要跨期使用的原件请在下一批次前转存；持有已登记读者租约时会保全。首次启用前已有的报告，由持有者核对、转存后显式接管。
