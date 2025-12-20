# 读取者和写入者

> 原文：[`rust-exercises.com/100-exercises/07_threads/12_rw_lock.html`](https://rust-exercises.com/100-exercises/07_threads/12_rw_lock.html)

我们的新`TicketStore`可以工作，但它的读取性能并不出色：一次只能有一个客户端读取特定的票据，因为`Mutex<T>`无法区分读取者和写入者。

我们可以通过使用不同的锁定原语来解决这个问题：`RwLock<T>`。

`RwLock<T>`代表**读写锁**。它允许**多个读取者**同时访问数据，但一次只能有一个写入者。

`RwLock<T>`有两种获取锁的方法：`read`和`write`。

`read`返回一个保护器，允许你读取数据，而`write`返回一个保护器，允许你修改它。

```rs
use std::sync::RwLock;

// An integer protected by a read-write lock
let lock = RwLock::new(0);

// Acquire a read lock on the RwLock
let guard1 = lock.read().unwrap();

// Acquire a **second** read lock
// while the first one is still active
let guard2 = lock.read().unwrap();
```

## 权衡

表面上看，`RwLock<T>`似乎是一个不费脑力的选择：它提供了`Mutex<T>`功能集的超集。为什么你还要使用`Mutex<T>`，而不是`RwLock<T>`呢？

有两个关键原因：

+   锁定`RwLock<T>`比锁定`Mutex<T>`更昂贵。

    这是因为`RwLock<T>`必须跟踪活动读取者和写入者的数量，而`Mutex<T>`只需要跟踪锁是否被持有。如果读取者多于写入者，这种性能开销不是问题，但如果工作负载是写入密集型，`Mutex<T>`可能是一个更好的选择。

+   `RwLock<T>`可能会导致**写入者饥饿**。

    如果总是有读取者等待获取锁，那么写入者可能永远没有机会运行。

    `RwLock<T>`不提供关于读取者和写入者被授予访问锁的顺序的任何保证。这取决于底层操作系统实现的策略，这可能对写入者不公平。

在我们的情况下，我们可以预期工作负载将是读取密集型（因为大多数客户端将读取票据，而不是修改它们），所以`RwLock<T>`是一个不错的选择。

## 练习

本节的练习位于[`07_threads/12_rw_lock`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/07_threads/12_rw_lock)
