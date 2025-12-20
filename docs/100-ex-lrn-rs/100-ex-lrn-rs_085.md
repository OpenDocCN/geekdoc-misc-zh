# 更新操作

> 原文：[`rust-exercises.com/100-exercises/07_threads/10_patch.html`](https://rust-exercises.com/100-exercises/07_threads/10_patch.html)

到目前为止，我们只实现了插入和检索操作。

让我们看看我们如何扩展系统以提供更新操作。

## 遗留更新

在系统的非线程版本中，更新操作相当直接：`TicketStore`公开了一个`get_mut`方法，允许调用者获取一个对票证的可变引用，然后对其进行修改。

## 多线程更新

在当前的多线程版本中，相同的策略将不起作用。借用检查器会阻止我们：`SyncSender<&mut Ticket>`不是`'static`，因为`&mut Ticket`不满足`'static`生命周期，因此它们不能被传递给`std::thread::spawn`的闭包捕获。

有几种方法可以绕过这个限制。我们将在接下来的练习中探讨其中的一些。

### 修补

我们不能通过通道发送一个`&mut Ticket`，因此我们无法在客户端进行修改。

我们能否在服务器端进行修改？

如果我们告诉服务器需要更改的内容，我们就可以这样做。换句话说，如果我们向服务器发送一个**补丁**：

```rs
struct TicketPatch {
    id: TicketId,
    title: Option<TicketTitle>,
    description: Option<TicketDescription>,
    status: Option<TicketStatus>,
}
```

`id`字段是必需的，因为它需要用来识别需要更新的票证。

所有其他字段都是可选的：

+   如果一个字段是`None`，这意味着该字段不应被更改。

+   如果一个字段是`Some(value)`，这意味着该字段应更改为`value`。

## 练习

本节的练习位于[`07_threads/10_patch`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/07_threads/10_patch)
