# 任务创建

> 原文：[`rust-exercises.com/100-exercises/08_futures/02_spawn.html`](https://rust-exercises.com/100-exercises/08_futures/02_spawn.html)

你对上一个练习的解决方案应该看起来像这样：

```rs
pub async fn echo(listener: TcpListener) -> Result<(), anyhow::Error> {
    loop {
        let (mut socket, _) = listener.accept().await?;
        let (mut reader, mut writer) = socket.split();
        tokio::io::copy(&mut reader, &mut writer).await?;
    }
}
```

这并不坏！

如果两个传入连接之间有很长时间的间隔，`echo` 函数将处于空闲状态（因为 `TcpListener::accept` 是一个异步函数），从而允许执行器在此期间运行其他任务。

但我们如何实际上让多个任务并发运行呢？

如果我们总是运行我们的异步函数直到完成（通过使用 `.await`），我们一次将不会有超过一个任务在运行。

这就是 `tokio::spawn` 函数发挥作用的地方。

## `tokio::spawn`

`tokio::spawn` 允许你将任务交给执行器，**而不需要等待它完成**。

每次你调用 `tokio::spawn` 时，你都在告诉 `tokio` 在后台继续运行创建的任务，**与创建它的任务并发**。

这里是如何使用它来同时处理多个连接的：

```rs
use tokio::net::TcpListener;

pub async fn echo(listener: TcpListener) -> Result<(), anyhow::Error> {
    loop {
        let (mut socket, _) = listener.accept().await?;
        // Spawn a background task to handle the connection
        // thus allowing the main task to immediately start 
        // accepting new connections
        tokio::spawn(async move {
            let (mut reader, mut writer) = socket.split();
            tokio::io::copy(&mut reader, &mut writer).await?;
        });
    }
}
```

### 异步块

在这个例子中，我们向 `tokio::spawn` 传递了一个 **异步块**：`async move { /* */ }`。异步块是标记代码区域为异步的一种快捷方式，而无需定义单独的异步函数。

### `JoinHandle`

`tokio::spawn` 返回一个 `JoinHandle`。

你可以使用 `JoinHandle` 来 `.await` 背景任务，就像我们使用 `join` 为创建的线程做的那样。

```rs
pub async fn run() {
    // Spawn a background task to ship telemetry data
    // to a remote server
    let handle = tokio::spawn(emit_telemetry());
    // In the meantime, do some other useful work
    do_work().await;
    // But don't return to the caller until 
    // the telemetry data has been successfully delivered
    handle.await;
}

pub async fn emit_telemetry() {
    // [...]
}

pub async fn do_work() {
    // [...]
}
```

### 恐慌边界

如果使用 `tokio::spawn` 创建的任务发生恐慌，恐慌将被执行器捕获。

如果你没有 `.await` 对应的 `JoinHandle`，恐慌不会传播到创建者。即使你 `.await` 了 `JoinHandle`，恐慌也不会自动传播。等待 `JoinHandle` 返回一个 `Result`，其错误类型为 `JoinError`。然后你可以通过调用 `JoinError::is_panic` 来检查任务是否发生恐慌，并决定如何处理恐慌——要么记录它，要么忽略它，要么传播它。

```rs
use tokio::task::JoinError;

pub async fn run() {
    let handle = tokio::spawn(work());
    if let Err(e) = handle.await {
        if let Ok(reason) = e.try_into_panic() {
            // The task has panicked
            // We resume unwinding the panic,
            // thus propagating it to the current task
            panic::resume_unwind(reason);
        }
    }
}

pub async fn work() {
    // [...]
}
```

### `std::thread::spawn` 与 `tokio::spawn`

你可以将 `tokio::spawn` 视为 `std::thread::spawn` 的异步兄弟。

注意一个关键区别：使用 `std::thread::spawn`，你是在将控制权委托给操作系统调度器。你无法控制线程的调度方式。

使用 `tokio::spawn`，你是在委托给一个完全在用户空间运行的异步执行器。底层的操作系统调度器不参与决定下一个运行哪个任务。现在，我们通过选择的执行器来负责这个决定。

## 练习

本节练习位于 `[08_futures/02_spawn](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/08_futures/02_spawn)`。
