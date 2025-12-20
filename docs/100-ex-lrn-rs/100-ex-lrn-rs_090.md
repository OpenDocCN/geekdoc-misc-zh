# 异步 Rust

> 原文：[`rust-exercises.com/100-exercises/08_futures/00_intro.html`](https://rust-exercises.com/100-exercises/08_futures/00_intro.html)

在 Rust 中编写并发程序的方式不仅仅是线程。

在本章中，我们将探讨另一种方法：**异步编程**。

尤其是以下内容的介绍：

+   使用 `async`/`.await` 关键字，轻松编写异步代码

+   `Future` 特性，用于表示可能尚未完成的计算

+   `tokio`，运行异步代码最流行的运行时

+   Rust 异步模型的协作特性，以及这对你的代码有何影响

## 练习

本节练习位于[`08_futures/00_intro`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/08_futures/00_intro)
