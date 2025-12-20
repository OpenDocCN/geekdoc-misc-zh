# 运行时架构

> 原文：[`rust-exercises.com/100-exercises/08_futures/03_runtime.html`](https://rust-exercises.com/100-exercises/08_futures/03_runtime.html)

到目前为止，我们一直在谈论异步运行时作为一个抽象概念。让我们更深入地了解一下它们的实现方式——正如你很快就会看到的，它对我们的代码有影响。

## 风味

`tokio`提供了两种不同的运行时**风味**。

您可以通过`tokio::runtime::Builder`配置您的运行时：

+   `Builder::new_multi_thread`为您提供一个**多线程`tokio`运行时**

+   `Builder::new_current_thread`将依赖于**当前线程**进行执行。

`#[tokio::main]`默认返回一个多线程运行时，而`#[tokio::test]`则使用当前线程运行时。

### 当前线程运行时

当前线程运行时，正如其名所示，完全依赖于它启动的操作系统线程来调度和执行任务。

当使用当前线程运行时，您有**并发性**但没有**并行性**：异步任务将被交错，但在任何给定时间最多只有一个任务在运行。

### 多线程运行时

当使用多线程运行时，在任何给定时间可以有最多`N`个任务**并行**运行，其中`N`是运行时使用的线程数。默认情况下，`N`与可用的 CPU 核心数相匹配。

还有更多：`tokio`执行**工作窃取**。

如果一个线程处于空闲状态，它不会等待：它会尝试找到一个准备就绪的新任务，无论是来自全局队列还是从另一个线程的本地队列中窃取。

工作窃取可以带来显著的性能优势，尤其是在尾部延迟方面，当您的应用程序处理的工作负载在各个线程之间不平衡时。

## 影响

`tokio::spawn`对风味不敏感：无论您是在多线程还是当前线程运行时上运行，它都会工作。缺点是签名假设了最坏的情况（即多线程）并相应地进行了约束：

```rs
pub fn spawn<F>(future: F) -> JoinHandle<F::Output>
where
    F: Future + Send + 'static,
    F::Output: Send + 'static,
{ /* */ }
```

让我们暂时忽略`Future`特质，专注于其他部分。

`spawn`要求所有输入都是`Send`并且具有`'static`生命周期。

`'static`约束遵循与`std::thread::spawn`上的`'static`约束相同的理由：生成的任务可能会比生成它的上下文存活得更久，因此它不应该依赖于任何可能在生成上下文被销毁后释放的本地数据。

```rs
fn spawner() {
    let v = vec![1, 2, 3];
    // This won't work, since `&v` doesn't
    // live long enough.
    tokio::spawn(async { 
        for x in &v {
            println!("{x}")
        }
    })
}
```

另一方面，`Send`是`tokio`的工作窃取策略的直接后果：如果线程`A`上生成的任务最终会被移动到空闲的线程`B`，那么它需要一个`Send`约束，因为我们正在跨越线程边界。

```rs
fn spawner(input: Rc<u64>) {
    // This won't work either, because
    // `Rc` isn't `Send`.
    tokio::spawn(async move {
        println!("{}", input);
    })
}
```

## 练习

本节练习位于[`08_futures/03_runtime`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/08_futures/03_runtime)
