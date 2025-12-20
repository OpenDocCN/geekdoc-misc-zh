# 异步感知原语

> 原文：[`rust-exercises.com/100-exercises/08_futures/06_async_aware_primitives.html`](https://rust-exercises.com/100-exercises/08_futures/06_async_aware_primitives.html)

如果您浏览 `tokio` 的文档，您会注意到它提供了许多与标准库中的类型“镜像”的类型，但具有异步特性：锁、通道、定时器等。

在异步上下文中工作时应优先考虑这些异步替代方案，而不是它们的同步对应方案。

为了理解原因，让我们看看 `Mutex`，这是我们在上一章中探讨的互斥锁。

## 案例研究：`Mutex`

让我们看看一个简单的例子：

```rs
use std::sync::{Arc, Mutex};

async fn run(m: Arc<Mutex<Vec<u64>>>) {
    let guard = m.lock().unwrap();
    http_call(&guard).await;
    println!("Sent {:?} to the server", &guard);
    // `guard` is dropped here
}

/// Use `v` as the body of an HTTP call.
async fn http_call(v: &[u64]) {
  // [...]
}
```

### `std::sync::MutexGuard` 和让点

这段代码可以编译，但很危险。

我们尝试在异步上下文中从 `std` 的 `Mutex` 获取锁。然后我们在让点（`http_call` 上的 `.await`）上保持对生成的 `MutexGuard`。

让我们想象有两个任务在一个单线程运行时并发执行 `run`。我们观察到以下调度事件序列：

```rs
 Task A          Task B
        | 
  Acquire lock
Yields to runtime
        | 
        +--------------+
                       |
             Tries to acquire lock 
```

我们有一个死锁。任务 B 将永远无法获取锁，因为锁目前被任务 A 持有，任务 A 在释放锁之前已经让步给运行时，并且由于运行时无法抢占任务 B，因此不会再次被调度。

### `tokio::sync::Mutex`

您可以通过切换到 `tokio::sync::Mutex` 来解决问题：

```rs
use std::sync::Arc;
use tokio::sync::Mutex;

async fn run(m: Arc<Mutex<Vec<u64>>>) {
    let guard = m.lock().await;
    http_call(&guard).await;
    println!("Sent {:?} to the server", &guard);
    // `guard` is dropped here
}
```

获取锁现在是一个异步操作，如果无法取得进展，则会返回到运行时。

回到先前的场景，以下会发生：

```rs
 Task A          Task B
          | 
  Acquires the lock
  Starts `http_call`
  Yields to runtime
          | 
          +--------------+
                         |
             Tries to acquire the lock
              Cannot acquire the lock
                 Yields to runtime
                         |
          +--------------+
          |
`http_call` completes      
  Releases the lock
   Yield to runtime
          |
          +--------------+
                         |
                 Acquires the lock
                       [...] 
```

所有都很好！

### 多线程无法拯救你

我们在先前的例子中使用了单线程运行时作为执行上下文，但即使在使用多线程运行时，同样的风险仍然存在。

唯一的区别在于创建死锁所需的并发任务数量：在单线程运行时，2 个就足够了；在多线程运行时，我们需要 `N+1` 个任务，其中 `N` 是运行时线程的数量。

### 缺点

拥有一个异步感知的 `Mutex` 会带来性能损失。

如果您确信锁没有受到重大竞争，并且您小心地确保永远不会在让点（`http_call` 上的 `.await`）持有它，您仍然可以在异步上下文中使用 `std::sync::Mutex`。

但要权衡性能收益与您将承担的活跃风险。

## 其他原语

我们以 `Mutex` 为例，但同样适用于 `RwLock`、信号量等。

在异步上下文中工作时，优先选择异步感知版本以最大限度地减少问题风险。

## 练习

本节练习位于 `08_futures/06_async_aware_primitives` 中（[`github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/08_futures/06_async_aware_primitives`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/08_futures/06_async_aware_primitives)）。
