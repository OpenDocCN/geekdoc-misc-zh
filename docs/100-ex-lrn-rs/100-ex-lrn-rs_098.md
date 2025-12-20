# 结语

> 原文：[`rust-exercises.com/100-exercises/08_futures/08_outro.html`](https://rust-exercises.com/100-exercises/08_futures/08_outro.html)

Rust 的异步模型非常强大，但它确实引入了额外的复杂性。花时间了解你的工具：深入研究`tokio`的文档，并熟悉其原语，以充分利用它。

请记住，在语言和`std`级别上，目前正在对 Rust 的异步故事进行精简和“完善”的工作。由于这些缺失的部分，你可能会在日常工作中遇到一些粗糙的边缘。

对于一个基本无痛苦的异步体验，这里有一些推荐：

+   **选择一个运行时并坚持下去。**

    一些原语（例如计时器、I/O）不能跨运行时移植。尝试混合运行时可能会让你感到痛苦。尝试编写与运行时无关的代码可能会显著增加你的代码库的复杂性。如果可能的话，避免这样做。

+   **目前还没有稳定的`Stream`/`AsyncIterator`接口。**

    `AsyncIterator`在概念上是一个异步产生新项目的迭代器。正在进行设计工作，但尚未达成共识（目前）。如果你使用`tokio`，请以`tokio_stream`（[`docs.rs/tokio-stream/latest/tokio_stream/`](https://docs.rs/tokio-stream/latest/tokio_stream/)）作为你的首选接口。

+   **小心缓冲区。**

    它往往是微妙错误的根源。查看["芭芭拉与缓冲流战斗"](https://rust-lang.github.io/wg-async/vision/submitted_stories/status_quo/barbara_battles_buffered_streams.html)以获取更多详细信息。

+   **异步任务没有范围线程的等价物。**

    查看["范围任务三难问题"](https://without.boats/blog/the-scoped-task-trilemma/)以获取更多详细信息。

不要让这些注意事项吓到你：异步 Rust 正在大规模（例如 AWS、Meta）上被有效地使用，以支持基础服务。

如果你计划在 Rust 中构建网络应用程序，你必须掌握它。

## 练习

本节的练习位于[`08_futures/08_outro`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/08_futures/08_outro)
