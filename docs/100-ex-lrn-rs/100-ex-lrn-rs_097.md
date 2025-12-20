# 取消

> 原文：[`rust-exercises.com/100-exercises/08_futures/07_cancellation.html`](https://rust-exercises.com/100-exercises/08_futures/07_cancellation.html)

当挂起的未来被丢弃时会发生什么？

运行时将不再轮询它，因此它不会取得任何进一步的进展。换句话说，它的执行已被**取消**。

在野外，这通常发生在处理超时的情况下。例如：

```rs
use tokio::time::timeout;
use tokio::sync::oneshot;
use std::time::Duration;

async fn http_call() {
    // [...]
}

async fn run() {
    // Wrap the future with a `Timeout` set to expire in 10 milliseconds.
    let duration = Duration::from_millis(10);
    if let Err(_) = timeout(duration, http_call()).await {
        println!("Didn't receive a value within 10 ms");
    }
}
```

当超时到期时，`http_call`返回的未来将被取消。让我们想象这是`http_call`的主体：

```rs
use std::net::TcpStream;

async fn http_call() {
    let (stream, _) = TcpStream::connect(/* */).await.unwrap();
    let request: Vec<u8> = /* */;
    stream.write_all(&request).await.unwrap();
}
```

每个产出点都成为一个**取消点**。

`http_call`不能被运行时抢占，因此它只能在通过`.await`将控制权交还给执行器后丢弃。这适用于递归情况——例如，`stream.write_all(&request)`在其实现中可能有多处产出点。完全有可能看到`http_call`在取消之前推送一个**部分**请求，从而断开连接并从未完成传输主体。

## 清理

Rust 的取消机制非常强大——它允许调用者取消一个正在进行的任务，而无需任务本身的任何形式的合作。

同时，这也可能相当危险。可能需要执行一个**优雅的取消**，以确保在终止操作之前执行一些清理任务。

例如，考虑这个虚构的 SQL 事务 API：

```rs
async fn transfer_money(
    connection: SqlConnection,
    payer_id: u64,
    payee_id: u64,
    amount: u64
) -> Result<(), anyhow::Error> {
    let transaction = connection.begin_transaction().await?;
    update_balance(payer_id, amount, &transaction).await?;
    decrease_balance(payee_id, amount, &transaction).await?;
    transaction.commit().await?;
}
```

在取消时，最好显式地中止挂起的交易，而不是让它悬而未决。不幸的是，Rust 没有提供一种针对此类**异步**清理操作的万无一失的机制。

最常见的策略是依赖于`Drop`特质来安排所需的清理工作。这可以通过以下方式实现：

+   在运行时上启动一个新任务

+   在通道上入队一条消息

+   启动一个后台线程

最佳选择是情境相关的。

## 取消已启动的任务

当你使用`tokio::spawn`启动一个任务时，你不能再将其丢弃；它属于运行时。

尽管如此，如果需要，你可以使用它的`JoinHandle`来取消它：

```rs
async fn run() {
    let handle = tokio::spawn(/* some async task */);
    // Cancel the spawned task
    handle.abort();
}
```

## 进一步阅读

+   当使用`tokio`的`select!`宏来“竞速”两个不同的未来时，请务必非常小心。除非你能确保**取消安全性**，否则在循环中重试相同的任务是非常危险的。查看`[`select!`的文档](https://tokio.rs/tokio/tutorial/select)以获取更多详细信息。

    如果你需要混合两个异步数据流（例如，一个套接字和一个通道），建议使用`[`StreamExt::merge](https://docs.rs/tokio-stream/latest/tokio_stream/trait.StreamExt.html#method.merge)`。

+   在某些情况下，`[`CancellationToken`](https://docs.rs/tokio-util/latest/tokio_util/sync/struct.CancellationToken.html)`可能比`JoinHandle::abort`更可取。

## 练习

本节练习位于[`08_futures/07_cancellation`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/08_futures/07_cancellation)
