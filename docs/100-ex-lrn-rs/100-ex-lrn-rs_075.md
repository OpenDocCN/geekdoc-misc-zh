# 简介

> [`rust-exercises.com/100-exercises/07_threads/00_intro.html`](https://rust-exercises.com/100-exercises/07_threads/00_intro.html)

Rust 的一个重大承诺是*无畏并发*：使编写安全、并发的程序更加容易。我们至今还没有看到很多这方面的内容。我们迄今为止所做的工作都是单线程的。是时候改变这一点了！

在本章中，我们将使我们的票务存储多线程化。

我们将有机会接触 Rust 的核心并发特性，包括：

+   线程，使用`std::thread`模块

+   消息传递，使用通道

+   共享状态，使用`Arc`、`Mutex`和`RwLock`

+   `Send`和`Sync`，这些特性编码了 Rust 的并发保证

我们还将讨论多线程系统的各种设计模式及其权衡。

## 练习

本节练习位于[`07_threads/00_intro`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/07_threads/00_intro)
