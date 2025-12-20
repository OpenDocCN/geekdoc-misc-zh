# Sync

> 原文：[`rust-exercises.com/100-exercises/07_threads/14_sync.html`](https://rust-exercises.com/100-exercises/07_threads/14_sync.html)

在我们结束这一章之前，让我们谈谈 Rust 标准库中的另一个关键特性：`Sync`。

`Sync` 是一个自动特性，就像 `Send` 一样。

它被所有可以在线程之间安全**共享**的类型自动实现。

换句话说：如果 `&T` 是 `Send`，则 `T` 是 `Sync`。

## `T: Sync` 不意味着 `T: Send`

重要的是要注意，`T` 可以是 `Sync` 而不是 `Send`。

例如：`MutexGuard` 不是 `Send`，但它确实是 `Sync`。

它不是 `Send`，因为锁必须在获取它的同一个线程上释放，所以我们不希望 `MutexGuard` 在不同的线程上被丢弃。

但它是 `Sync`，因为将 `&MutexGuard` 传递给另一个线程不会影响锁释放的位置。

## `T: Send` 不意味着 `T: Sync`

反过来也是真的：`T` 可以是 `Send` 而不是 `Sync`。

例如：`RefCell<T>` 是 `Send`（如果 `T` 是 `Send`），但它不是 `Sync`。

`RefCell<T>` 执行运行时借用检查，但它用来跟踪借用的计数器不是线程安全的。因此，多个线程持有 `&RefCell` 会导致数据竞争，可能多个线程会获得对同一数据的可变引用。因此 `RefCell` 不是 `Sync`。

`Send` 是可以的，相反，因为当我们将一个 `RefCell` 发送到另一个线程时，我们没有留下对它包含的数据的任何引用，因此没有并发可变访问的风险。

## 练习

本节的练习位于 [07_threads/14_sync](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/07_threads/14_sync)
