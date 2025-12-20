# 专门的客户端类型

> 原文：[`rust-exercises.com/100-exercises/07_threads/08_client.html`](https://rust-exercises.com/100-exercises/07_threads/08_client.html)

客户端的所有交互都相当底层：你必须手动创建响应通道，构建命令，将其发送到服务器，然后在对响应通道调用`recv`以获取响应。

这是一大堆可以抽象出来的样板代码，这正是我们将在本练习中要做的。

## 练习

本节练习位于[`07_threads/08_client`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/07_threads/08_client)
