# 不要阻塞运行时

> 原文：[`rust-exercises.com/100-exercises/08_futures/05_blocking.html`](https://rust-exercises.com/100-exercises/08_futures/05_blocking.html)

让我们回到释放点。

与线程不同，**Rust 任务不能被抢占**。

`tokio`本身无法决定暂停一个任务并运行另一个任务来替代它。当任务释放资源时——即`Future::poll`返回`Poll::Pending`，或者在`async fn`的情况下，当你`.await`一个未来时——控制权才会完全回到执行器。

这使得运行时面临风险：如果一个任务从不释放资源，运行时将永远无法运行另一个任务。这被称为**阻塞运行时**。

## 什么是阻塞？

多长时间算太长？一个任务在没有释放资源之前可以花费多少时间才成为问题？

这取决于运行时、应用程序、正在执行的任务数量以及许多其他因素。但作为一个一般规则，尽量在释放点之间花费少于 100 微秒。 

## 后果

阻塞运行时可能导致：

+   **死锁**：如果一个任务没有释放资源，却在等待另一个任务完成，而那个任务又在等待第一个任务释放资源，那么你就遇到了死锁。除非运行时能够将其他任务调度到不同的线程上，否则无法取得任何进展。

+   **饥饿**：其他任务可能无法运行，或者可能经过长时间的延迟后才能运行，这可能导致性能下降（例如，高尾部延迟）。

## 阻塞并不总是显而易见

在异步代码中，一些类型的操作通常应该避免，例如：

+   同步 I/O。你无法预测它将花费多长时间，而且它很可能超过 100 微秒。

+   耗时的 CPU 密集型计算。

后者类别并不总是显而易见。例如，对包含少量元素的向量进行排序不是问题；但如果向量有数十亿条记录，情况就不同了。

## 如何避免阻塞

好吧，那么在必须执行一个可能或风险成为阻塞的操作的情况下，你如何避免阻塞运行时？

你需要将工作移动到不同的线程。你不想使用所谓的运行时线程，即`tokio`用来运行任务的那些线程。

`tokio`为此提供了一个专门的线程池，称为**阻塞池**。你可以使用`tokio::task::spawn_blocking`函数在阻塞池上启动一个同步操作。`spawn_blocking`返回一个在操作完成时解析为操作结果的未来。

```rs
use tokio::task;

fn expensive_computation() -> u64 {
    // [...]
}

async fn run() {
    let handle = task::spawn_blocking(expensive_computation);
    // Do other stuff in the meantime
    let result = handle.await.unwrap();
}
```

阻塞池是长期存在的。`spawn_blocking`应该比直接通过`std::thread::spawn`创建新线程更快，因为线程初始化的成本被分摊到多次调用中。

## 进一步阅读

+   查看 Alice Ryhl 关于这个主题的博客文章[（https://ryhl.io/blog/async-what-is-blocking/）](https://ryhl.io/blog/async-what-is-blocking/)。

## 练习

本节练习位于[`08_futures/05_blocking`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/08_futures/05_blocking)
