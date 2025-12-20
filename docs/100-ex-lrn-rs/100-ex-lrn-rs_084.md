# 有界与无界通道

> 原文：[`rust-exercises.com/100-exercises/07_threads/09_bounded.html`](https://rust-exercises.com/100-exercises/07_threads/09_bounded.html)

到目前为止，我们一直在使用无界通道。

您可以发送尽可能多的消息，通道将增长以容纳它们。

在多生产者单消费者场景中，这可能会出现问题：如果生产者以比消费者处理消息更快的速度排队消息，通道将不断增长，可能会消耗所有可用内存。

我们的建议是**永远**不要在生产系统中使用无界通道。

您应该始终使用有界通道强制限制可以排队的消息数量。

## 有界通道

有界通道具有固定容量。

您可以通过调用 `sync_channel` 并传入大于零的容量来创建一个：

```rs
use std::sync::mpsc::sync_channel;

let (sender, receiver) = sync_channel(10);
```

`receiver` 与之前相同，类型为 `Receiver<T>`。

`sender`，而是一个 `SyncSender<T>` 的实例。

### 发送消息

您有两种不同的方法通过 `SyncSender` 发送消息：

+   `send`：如果通道中有空间，它将排队消息并返回 `Ok(())`。

    如果通道已满，它将阻塞并等待直到有空间可用。

+   `try_send`：如果通道中有空间，它将排队消息并返回 `Ok(())`。

    如果通道已满，它将返回 `Err(TrySendError::Full(value))`，其中 `value` 是无法发送的消息。

根据您的用例，您可能希望使用其中一个。

### 背压

使用有界通道的主要优势是它们提供了一种形式的**背压**。

它们迫使生产者在消费者跟不上的情况下减速。然后，背压可以传播到整个系统，可能影响整个架构，并防止最终用户通过请求压倒系统。

## 练习

本节的练习位于 `07_threads/09_bounded` 中[`07_threads/09_bounded`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/07_threads/09_bounded)
