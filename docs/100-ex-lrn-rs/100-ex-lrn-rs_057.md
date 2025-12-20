# 总结

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/15_outro.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/15_outro.html)

当涉及到领域建模时，魔鬼藏在细节中。

Rust 提供了广泛的工具来帮助您直接在类型系统中表示您领域的约束，但这需要一些练习才能做到正确，并编写出符合习惯的代码。

让我们以对 `Ticket` 模型的最后一次精炼来结束这一章。

我们将为 `Ticket` 中的每个字段引入一个新的类型，以封装相应的约束。

每次有人访问 `Ticket` 字段时，他们都会得到一个保证有效的值——即 `TicketTitle` 而不是 `String`。他们不必担心标题在代码的其他地方为空：只要他们有一个 `TicketTitle`，他们就知道它是通过构造有效 **的**。

这只是一个例子，展示了您如何使用 Rust 的类型系统来使您的代码更安全、更具表现力。

## 进一步阅读

+   [解析，而不是验证](https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/)

+   [使用类型来保证领域不变性](https://www.lpalmieri.com/posts/2020-12-11-zero-to-production-6-domain-modelling/)

## 练习

本节的练习位于[`05_ticket_v2/15_outro`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/15_outro)
