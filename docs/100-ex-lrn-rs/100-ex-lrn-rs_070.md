# 票据 id

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/12_two_states.html`](https://rust-exercises.com/100-exercises/06_ticket_management/12_two_states.html)

让我们再次思考我们的票据管理系统。

我们现在的票据模型看起来是这样的：

```rs
pub struct Ticket {
    pub title: TicketTitle,
    pub description: TicketDescription,
    pub status: Status
}
```

这里缺少一件事：一个**标识符**来唯一标识一个票据。

该标识符对于每个票据应该是唯一的。这可以通过在创建新票据时自动生成来保证。

## 细化模型

id 应该存储在哪里？

我们可以在`Ticket`结构体中添加一个新的字段：

```rs
pub struct Ticket {
    pub id: TicketId,
    pub title: TicketTitle,
    pub description: TicketDescription,
    pub status: Status
}
```

但在创建票据之前我们并不知道 id。所以它不能从一开始就存在。

它必须是可选的：

```rs
pub struct Ticket {
    pub id: Option<TicketId>,
    pub title: TicketTitle,
    pub description: TicketDescription,
    pub status: Status
}
```

这也不是理想的——我们每次从存储中检索票据时都必须处理`None`情况，尽管我们知道一旦票据被创建，id 应该始终存在。

最佳方案是拥有两种不同的票据**状态**，分别由两种不同的类型表示：一个`TicketDraft`和一个`Ticket`：

```rs
pub struct TicketDraft {
    pub title: TicketTitle,
    pub description: TicketDescription
}

pub struct Ticket {
    pub id: TicketId,
    pub title: TicketTitle,
    pub description: TicketDescription,
    pub status: Status
}
```

`TicketDraft`是一个尚未创建的票据。它没有 id，也没有状态。

`Ticket`是一个已经创建的票据。它有一个 id 和一个状态。

由于`TicketDraft`和`Ticket`字段各自嵌入了自己的约束，我们不需要在两种类型之间重复逻辑。

## 练习

本节练习位于[`06_ticket_management/12_two_states`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/12_two_states)
