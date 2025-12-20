# 验证

> 原文：[`rust-exercises.com/100-exercises/03_ticket_v1/02_validation.html`](https://rust-exercises.com/100-exercises/03_ticket_v1/02_validation.html)

让我们回到我们的票据定义：

```rs
struct Ticket {
    title: String,
    description: String,
    status: String,
}
```

我们正在为`Ticket`结构体的字段使用“原始”类型。这意味着用户可以创建一个标题为空、描述超级长或状态不合逻辑（例如“有趣”）的票据。

我们可以做得更好！

## 进一步阅读

+   查看关于`String`的文档（[`doc.rust-lang.org/std/string/struct.String.html`](https://doc.rust-lang.org/std/string/struct.String.html)），以全面了解它提供的方法。你将需要在练习中使用它！

## 练习

本节的练习位于[03_ticket_v1/02_validation](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/03_ticket_v1/02_validation)
