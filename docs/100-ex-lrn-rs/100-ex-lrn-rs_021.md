# 可变引用

> 原文：[`rust-exercises.com/100-exercises/03_ticket_v1/07_setters.html`](https://rust-exercises.com/100-exercises/03_ticket_v1/07_setters.html)

你的访问器方法现在应该看起来像这样：

```rs
impl Ticket {
    pub fn title(&self) -> &String {
        &self.title
    }

    pub fn description(&self) -> &String {
        &self.description
    }

    pub fn status(&self) -> &String {
        &self.status
    }
}
```

在这里和那里撒一点`&`就完成了！

现在我们有了一种方法可以在不消耗它的过程中访问`Ticket`实例的字段。接下来，让我们看看我们如何通过**设置器方法**来增强我们的`Ticket`结构体。

## 设置器

设置器方法允许用户更改`Ticket`的私有字段值，同时确保其不变性得到尊重（即你不能将`Ticket`的标题设置为空字符串）。

在 Rust 中实现设置器有两种常见的方法：

+   以`self`作为输入。

+   以`&mut self`作为输入。

### 以`self`作为输入

第一种方法看起来是这样的：

```rs
impl Ticket {
    pub fn set_title(mut self, new_title: String) -> Self {
        // Validate the new title [...]
        self.title = new_title;
        self
    }
}
```

它获取了`self`的所有权，更改了标题，并返回修改后的`Ticket`实例。

这就是它的用法：

```rs
let ticket = Ticket::new(
    "Title".into(), 
    "Description".into(), 
    "To-Do".into()
);
let ticket = ticket.set_title("New title".into());
```

由于`set_title`获取了`self`的所有权（即它**消耗了它**），我们需要将结果重新分配给一个变量。在上面的例子中，我们利用**变量遮蔽**来重用相同的变量名：当你用与现有变量相同的名称声明一个新变量时，新变量**遮蔽**了旧变量。这是 Rust 代码中的常见模式。

当你需要一次性更改多个字段时，`self`-设置器工作得相当好：你可以将多个调用链接在一起！

```rs
let ticket = ticket
    .set_title("New title".into())
    .set_description("New description".into())
    .set_status("In Progress".into());
```

### 以`&mut self`作为输入

设置器的第二种方法，使用`&mut self`，看起来是这样的：

```rs
impl Ticket {
    pub fn set_title(&mut self, new_title: String) {
        // Validate the new title [...]

        self.title = new_title;
    }
}
```

这次方法以可变引用`self`作为输入，更改标题，然后就没有其他操作了。不返回任何内容。

你可以这样使用它：

```rs
let mut ticket = Ticket::new(
    "Title".into(),
    "Description".into(),
    "To-Do".into()
);
ticket.set_title("New title".into());

// Use the modified ticket
```

所有权保留在调用者那里，因此原始的`ticket`变量仍然有效。我们不需要重新分配结果。但是，我们需要将`ticket`标记为可变的，因为我们正在获取它的可变引用。

`&mut`-设置器有一个缺点：你不能将多个调用链接在一起。由于它们不返回修改后的`Ticket`实例，你不能在第一个设置器的结果上调用另一个设置器。你必须单独调用每个设置器：

```rs
ticket.set_title("New title".into());
ticket.set_description("New description".into());
ticket.set_status("In Progress".into());
```

## 练习

本节练习位于[`03_ticket_v1/07_setters`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/03_ticket_v1/07_setters)
