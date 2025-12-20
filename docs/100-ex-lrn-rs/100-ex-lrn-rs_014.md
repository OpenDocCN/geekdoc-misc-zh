# 建模一个工单

> 原文：[`rust-exercises.com/100-exercises/03_ticket_v1/00_intro.html`](https://rust-exercises.com/100-exercises/03_ticket_v1/00_intro.html)

第一章应该已经让你对 Rust 的一些原始类型、运算符和基本控制流结构有了很好的掌握。

在本章中，我们将进一步探讨使 Rust 真正独特的东西：**所有权**。

所有权是使 Rust 既内存安全又高效，且无需垃圾回收器的原因。

作为我们的运行示例，我们将使用一个（类似 JIRA 的）工单，这种工单通常用于跟踪软件项目中的错误、功能或任务。

我们将尝试用 Rust 来建模它。这将是我们第一次迭代——到章节结束时，它可能不会完美，也不会非常符合 Rust 的惯用风格。但这将是一个足够的挑战！

要继续前进，你必须掌握几个新的 Rust 概念，例如：

+   `struct`s，Rust 定义自定义类型的一种方式

+   所有权、引用和借用

+   内存管理：栈、堆、指针、数据布局、析构函数

+   模块和可见性

+   字符串

## 练习

本节练习位于[`03_ticket_v1/00_intro`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/03_ticket_v1/00_intro)
