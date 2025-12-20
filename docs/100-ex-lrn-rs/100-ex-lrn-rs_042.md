# 模拟票务，第二部分

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/00_intro.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/00_intro.html)

在前几章中我们工作的`Ticket`结构体是一个良好的起点，但它仍然在呼喊“我是一个初学的 Rustacean！”。

我们将利用本章来提升我们的 Rust 领域建模技能。在过程中，我们需要引入一些更多概念：

+   `enum`s，Rust 在数据建模中最强大的功能之一

+   `Option` 类型，用于建模可空值

+   `Result` 类型，用于建模可恢复的错误

+   `Debug` 和 `Display` 特性，用于打印

+   `Error` 特性，用于标记错误类型

+   `TryFrom` 和 `TryInto` 特性，用于可错误转换

+   Rust 的包系统，解释什么是库，什么是二进制文件，如何使用第三方 crates

## 练习

本节练习位于[`05_ticket_v2/00_intro`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/00_intro)
