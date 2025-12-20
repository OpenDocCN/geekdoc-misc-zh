# 异步函数

> 原文：[`rust-exercises.com/100-exercises/08_futures/01_async_fn.html`](https://rust-exercises.com/100-exercises/08_futures/01_async_fn.html)

你迄今为止编写的所有函数和方法都是**急切的**。

除非你调用它们，否则什么都不会发生。但一旦你调用，它们就会运行到完成：它们完成了**所有**工作，然后返回它们的输出。

有时候这并不理想。

例如，如果你正在编写一个 HTTP 服务器，可能会有很多**等待**：等待请求体到达，等待数据库响应，等待下游服务回复等。

你在等待的时候，如果能做些别的事情会怎么样呢？

如果你可以在计算中途放弃会怎么样？

如果你可以选择优先处理另一个任务而不是当前任务会怎么样？

这就是**异步函数**的用武之地。

## `async fn`

你使用 `async` 关键字来定义一个异步函数：

```rs
use tokio::net::TcpListener;

// This function is asynchronous
async fn bind_random() -> TcpListener {
    // [...]
}
```

如果你像调用常规函数一样调用 `bind_random` 会发生什么？

```rs
fn run() {
    // Invoke `bind_random`
    let listener = bind_random();
    // Now what?
}
```

没有发生任何事情！

Rust 不会在你调用它时开始执行 `bind_random`，甚至不是作为一个后台任务（根据你使用其他语言的经验，你可能会有这样的预期）。Rust 中的异步函数是**懒加载的**：它们不会在你明确要求之前做任何工作。使用 Rust 的术语，我们说 `bind_random` 返回一个**未来**，这是一个表示可能稍后完成的计算的类型。它们被称为未来，因为它们实现了 `Future` 特性，这是一个我们将在本章后面详细探讨的接口。

## `.await`

向异步函数请求执行一些工作的最常见方法是使用 `.await` 关键字：

```rs
use tokio::net::TcpListener;

async fn bind_random() -> TcpListener {
    // [...]
}

async fn run() {
    // Invoke `bind_random` and wait for it to complete
    let listener = bind_random().await;
    // Now `listener` is ready
}
```

`.await` 不会将控制权返回给调用者，直到异步函数运行完成——例如，在上面的例子中，直到 `TcpListener` 被创建。

## `Runtimes`

如果你感到困惑，你是对的！

我们刚刚说过，异步函数的优点是它们不会一次性完成所有工作。然后我们介绍了 `.await`，它不会返回直到异步函数运行完成。我们不是刚刚重新引入了我们试图解决的问题吗？这有什么意义？

不完全是！当你调用 `.await` 时，幕后会发生很多事情！

你正在将控制权交给一个**异步运行时**，也称为**异步执行器**。执行器是魔法发生的地方：它们负责管理你所有的正在进行中的异步**任务**。特别是，它们平衡两个不同的目标：

+   **进度**：它们确保任务在可能的情况下取得进展。

+   **效率**：如果一个任务正在等待某件事，它们会尽力确保在此期间另一个任务可以运行，充分利用可用资源。

### `No default runtime`

Rust 在其异步编程方法上相当独特：它没有默认的运行时。标准库没有提供。你需要自己提供！

在大多数情况下，你会在生态系统提供的选项中选择一个。一些运行时被设计为广泛适用，对于大多数应用程序来说是一个不错的选择。`tokio` 和 `async-std` 属于这一类别。其他运行时针对特定用例进行了优化——例如，`embassy` 用于嵌入式系统。

在本课程中，我们将依赖 `tokio`，这是 Rust 中用于通用异步编程最流行的运行时。

### [`#[tokio::main]`](#tokiomain)

可执行文件的入口点，即 `main` 函数，必须是一个同步函数。这就是你设置并启动所选异步运行时的位置。

大多数运行时都提供了一个宏来简化这个过程。对于 `tokio`，它是 `tokio::main`：

```rs
#[tokio::main]
async fn main() {
    // Your async code goes here
}
```

它扩展为：

```rs
fn main() {
    let rt = tokio::runtime::Runtime::new().unwrap();
    rt.block_on(
        // Your async function goes here
        // [...]
    );
}
```

### [`#[tokio::test]`](#tokiotest)

对于测试也是如此：它们必须是同步函数。

每个测试函数都在自己的线程中运行，如果你需要在测试中运行异步代码，你需要负责设置和启动异步运行时。

`tokio` 提供了一个 `#[tokio::test]` 宏来简化这个过程：

```rs
#[tokio::test]
async fn my_test() {
    // Your async test code goes here
}
```

## 练习

本节练习位于 `08_futures/01_async_fn`（[`github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/08_futures/01_async_fn`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/08_futures/01_async_fn)）
