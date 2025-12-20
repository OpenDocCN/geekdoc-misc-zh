# Future 特性

> [`rust-exercises.com/100-exercises/08_futures/04_future.html`](https://rust-exercises.com/100-exercises/08_futures/04_future.html)

## 局部 `Rc` 问题

让我们回到 `tokio::spawn` 的签名：

```rs
pub fn spawn<F>(future: F) -> JoinHandle<F::Output>
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
{ /* */ }
```

`F` 为 `Send` 究竟意味着什么？

如前所述，这意味着它从启动环境捕获的任何值都必须是 `Send`。但它不仅仅如此。

任何跨越 `.await` 点持有的值都必须是 `Send`。

让我们看看一个例子：

```rs
use std::rc::Rc;
use tokio::task::yield_now;

fn spawner() {
    tokio::spawn(example());
}

async fn example() {
    // A value that's not `Send`,
    // created _inside_ the async function
    let non_send = Rc::new(1);

    // A `.await` point that does nothing
    yield_now().await;

    // The local non-`Send` value is still needed
    // after the `.await`
    println!("{}", non_send);
}
```

编译器会拒绝这段代码：

```rs
error: future cannot be sent between threads safely
    |
5   |     tokio::spawn(example());
    |                  ^^^^^^^^^ 
    | future returned by `example` is not `Send`
    |
note: future is not `Send` as this value is used across an await
    |
11  |     let non_send = Rc::new(1);
    |         -------- has type `Rc<i32>` which is not `Send`
12  |     // A `.await` point
13  |     yield_now().await;
    |                 ^^^^^ 
    |   await occurs here, with `non_send` maybe used later
note: required by a bound in `tokio::spawn`
    |
164 |     pub fn spawn<F>(future: F) -> JoinHandle<F::Output>
    |            ----- required by a bound in this function
165 |     where
166 |         F: Future + Send + 'static,
    |                     ^^^^ required by this bound in `spawn` 
```

要理解为什么是这样，我们需要深化对 Rust 异步模型的理解。

## Future 特性

我们一开始就声明了 `async` 函数返回 **futures**，即实现了 `Future` 特性的类型。你可以将未来视为 **状态机**。它处于两种状态之一：

+   **pending**：计算尚未完成。

+   **ready**：计算已完成，这里是输出。

这在特性定义中有所体现：

```rs
trait Future {
    type Output;

    // Ignore `Pin` and `Context` for now
    fn poll(
      self: Pin<&mut Self>, 
      cx: &mut Context<'_>
    ) -> Poll<Self::Output>;
}
```

### `poll`

`poll` 方法是 `Future` 特性的核心。

一个未来本身不做什么。它需要被 **轮询** 才能取得进展。

当你调用 `poll` 时，你是在要求未来执行一些工作。`poll` 尝试取得进展，然后返回以下之一：

+   `Poll::Pending`：未来尚未准备好。你需要稍后再次调用 `poll`。

+   `Poll::Ready(value)`：未来已完成。`value` 是计算的结果，类型为 `Self::Output`。

一旦 `Future::poll` 返回 `Poll::Ready`，它就不应该再次被轮询：未来已完成，没有剩下要做的。

### 运行时的作用

你很少，如果不是永远，会直接调用 `poll`。

这就是你的异步运行时的工作：它拥有所有必要的信息（`poll` 签名中的 `Context`），以确保你的未来可以在可能的时候取得进展。

## `async fn` 和 futures

我们已经使用高级接口，异步函数进行了工作。

我们现在已经看到了低级原语，即 `Future` 特性。

它们是如何相关的？

每次你将一个函数标记为异步时，该函数将返回一个未来。编译器会将你的异步函数的主体转换为 **状态机**：每个 `.await` 点对应一个状态。

回到我们之前的 `Rc` 例子：

```rs
use std::rc::Rc;
use tokio::task::yield_now;

async fn example() {
    let non_send = Rc::new(1);
    yield_now().await;
    println!("{}", non_send);
}
```

编译器会将其转换为类似以下的枚举：

```rs
pub enum ExampleFuture {
    NotStarted,
    YieldNow(Rc<i32>),
    Terminated,
}
```

当调用 `example` 时，它返回 `ExampleFuture::NotStarted`。未来尚未被轮询，因此没有任何事情发生。

当运行时第一次轮询它时，`ExampleFuture` 将推进到下一个 `.await` 点：它会在状态机的 `ExampleFuture::YieldNow(Rc<i32>)` 阶段停止，返回 `Poll::Pending`。

当它再次被轮询时，它将执行剩余的代码（`println!`）并返回 `Poll::Ready(())`。

当你查看其状态机表示，`ExampleFuture`，现在就很清楚为什么`example`不是`Send`：因为它持有`Rc`，因此不能是`Send`。

## 让步点

正如你刚才在`example`中看到的，每一个`.await`点都会在未来的生命周期中创建一个新的中间状态。

正因如此，`.await`点也被称为**让步点**：你的未来让步将控制权交回正在轮询它的运行时，允许运行时暂停它，并在必要时安排另一个任务执行，从而在多个方面同时取得进展。

我们将在后面的章节中再次讨论让步的重要性。

## 练习

本章节的练习位于[`08_futures/04_future`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/08_futures/04_future)
