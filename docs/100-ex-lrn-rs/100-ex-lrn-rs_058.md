# 简介

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/00_intro.html`](https://rust-exercises.com/100-exercises/06_ticket_management/00_intro.html)

在上一章中，我们在真空中对 `Ticket` 进行了建模：我们定义了其字段及其约束，我们学习了如何在 Rust 中最佳地表示它们，但我们没有考虑 `Ticket` 如何适应更大的系统。我们将利用本章来围绕 `Ticket` 建立一个简单的流程，引入一个（原始的）管理系统来存储和检索票据。

本任务将为我们提供一个探索新的 Rust 概念的机会，例如：

+   栈分配的数组

+   `Vec`，一种可增长的数组类型

+   `Iterator` 和 `IntoIterator`，用于遍历集合

+   切片 (`&[T]`)，用于处理集合的部分

+   生命周期，用于描述引用的有效时长

+   `HashMap` 和 `BTreeMap`，两种键值数据结构

+   `Eq` 和 `Hash`，用于比较 `HashMap` 中的键

+   `Ord` 和 `PartialOrd`，用于处理 `BTreeMap`

+   `Index` 和 `IndexMut`，用于访问集合中的元素

## 练习

本节练习位于[`06_ticket_management/00_intro`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/00_intro)
