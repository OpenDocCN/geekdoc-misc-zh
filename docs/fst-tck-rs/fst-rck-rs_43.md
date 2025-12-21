# 并发

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/concurrency.html`](https://freddiehaddad.github.io/fast-track-to-rust/concurrency.html)

我们即将结束这门课程，没有比并发更好的方式来总结内容了！Rust，像许多其他语言一样，包含一个用于创建线程和并行执行任务的本地[线程](https://doc.rust-lang.org/std/thread/)模块。然而，许多 crate 建立在 Rust 的本地多线程能力之上，简化了过程并提供各种线程模式。

例如，如果你在 Go 中编程，你可能会熟悉用于在`goroutines`之间移动数据的通道。同样，如果你与 JavaScript 合作过，你可能知道`async`和`await`。这两种范式，以及许多其他范式，在 Rust 中都可以作为 crate 使用。

这里有一些值得探索的例子：

+   **[crossbeam](https://crates.io/crates/crossbeam)**：一套用于并发编程的工具

+   **[rayon](https://crates.io/crates/rayon)**：一个用于 Rust 的数据并行库。

+   **[tokio](https://crates.io/crates/tokio)**：一个用于编写异步 I/O 后端应用程序的事件驱动、非阻塞 I/O 平台。

让我们深入探讨多线程！
