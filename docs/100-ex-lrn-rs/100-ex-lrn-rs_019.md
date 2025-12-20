# 封装

> 原文：[`rust-exercises.com/100-exercises/03_ticket_v1/05_encapsulation.html`](https://rust-exercises.com/100-exercises/03_ticket_v1/05_encapsulation.html)

现在我们对模块和可见性有了基本理解，让我们回到**封装**。

封装是将对象的内部表示隐藏起来的实践。它最常用于强制执行对象状态的一些**不变性**。

回到我们的 `Ticket` 结构体：

```rs
struct Ticket {
    title: String,
    description: String,
    status: String,
}
```

如果所有字段都是公开的，就没有封装。

你必须假设字段可以在任何时候被修改，设置为它们类型允许的任何值。你不能排除票可能有一个空标题或状态不合理的情况。

为了强制执行更严格的规则，我们必须保持字段私有^(1)。然后我们可以提供公共方法来与 `Ticket` 实例交互。这些公共方法将负责维护我们的不变性（例如，标题不能为空）。

如果至少有一个字段是私有的，就不再可能直接使用结构体实例化语法创建 `Ticket` 实例：

```rs
// This won't work!
let ticket = Ticket {
    title: "Build a ticket system".into(),
    description: "A Kanban board".into(),
    status: "Open".into()
};
```

你在之前的可见性练习中已经看到了这个操作。

我们现在需要提供一个或多个公共**构造函数**——即可以从模块外部使用的静态方法或函数，用于创建结构体的新实例。

幸运的是，我们已经有了一个：`Ticket::new`，如在前一个练习中实现的那样一个之前的练习。

## 访问器方法

总结来说：

+   所有 `Ticket` 字段都是私有的

+   我们提供了一个公共构造函数，`Ticket::new`，在创建时强制执行我们的验证规则

这是个不错的开始，但还不够：除了创建 `Ticket`，我们还需要与之交互。但如果字段是私有的，我们如何访问它们？

我们需要提供**访问器方法**。

访问器方法是允许你读取结构体（或多个字段）的私有字段值的公共方法。

Rust 没有内置的方式为你生成访问器方法，就像一些其他语言所做的那样。你必须自己编写它们——它们只是普通的方法。

## 练习

本节练习位于[`03_ticket_v1/05_encapsulation`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/03_ticket_v1/05_encapsulation)

* * *

1.  或者改进它们的类型，这是一种我们将在稍后探讨的技术。↩
