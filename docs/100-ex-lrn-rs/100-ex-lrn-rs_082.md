# 双向通信

> 原文：[`rust-exercises.com/100-exercises/07_threads/07_ack.html`](https://rust-exercises.com/100-exercises/07_threads/07_ack.html)

在我们当前的客户端-服务器实现中，通信是单向的：从客户端到服务器。

客户端无法知道服务器是否收到了消息、是否成功执行，或者是否失败。这并不理想。

为了解决这个问题，我们可以引入一个双向通信系统。

## 响应通道

我们需要一种方式让服务器能够向客户端发送响应。

有多种方法可以做到这一点，但最简单的方法是在客户端发送给服务器的消息中包含一个`Sender`通道。在处理完消息后，服务器可以使用这个通道向客户端发送响应。

这是在基于消息传递原语构建的 Rust 应用程序中相当常见的一种模式。

## 练习

本节练习位于[`07_threads/07_ack`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/07_threads/07_ack)
