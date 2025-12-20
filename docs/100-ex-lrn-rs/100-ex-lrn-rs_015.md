# 结构体

> 原文：[`rust-exercises.com/100-exercises/03_ticket_v1/01_struct.html`](https://rust-exercises.com/100-exercises/03_ticket_v1/01_struct.html)

对于每张票，我们需要跟踪三块信息：

+   一个标题

+   一个描述

+   一个状态

我们可以开始使用一个[`String`](https://doc.rust-lang.org/std/string/struct.String.html)来表示它们。`String`是 Rust 标准库中定义的类型，用于表示[UTF-8 编码](https://en.wikipedia.org/wiki/UTF-8)的文本。

但我们如何**结合**这三块信息成为一个单一实体呢？

## 定义结构体

结构体定义了一个**新的 Rust 类型**。

```rs
struct Ticket {
    title: String,
    description: String,
    status: String
}
```

结构体在其他编程语言中相当类似于你所说的类或对象。

## 定义字段

新类型是通过将其他类型作为**字段**组合而成的。

每个字段都必须有一个名称和一个类型，由冒号`:`分隔。如果有多个字段，它们由逗号`,`分隔。

字段不必是相同的类型，就像下面`Configuration`结构体中可以看到的那样：

```rs
struct Configuration {
   version: u32,
   active: bool
}
```

## 实例化

你可以通过指定每个字段的值来创建结构体的实例：

```rs
// Syntax: <StructName> { <field_name>: <value>, ... }
let ticket = Ticket {
    title: "Build a ticket system".into(),
    description: "A Kanban board".into(),
    status: "Open".into()
};
```

## 访问字段

你可以使用`.`运算符来访问结构体的字段：

```rs
// Field access
let x = ticket.description;
```

## 方法

我们可以通过定义**方法**来给我们的结构体附加行为。

以`Ticket`结构体为例：

```rs
impl Ticket {
    fn is_open(self) -> bool {
        self.status == "Open"
    }
}

// Syntax:
// impl <StructName> {
//    fn <method_name>(<parameters>) -> <return_type> {
//        // Method body
//    }
// }
```

方法与函数非常相似，有两个关键区别：

1.  方法必须在**`impl`块**内定义

1.  方法可以使用`self`作为它们的第一个参数。`self`是一个关键字，代表被调用的结构体实例。

### self

如果一个方法以`self`作为第一个参数，它可以使用**方法调用语法**来调用：

```rs
// Method call syntax: <instance>.<method_name>(<parameters>)
let is_open = ticket.is_open();
```

这与你在上一章中用于对`u32`值执行饱和算术运算的调用语法相同。

### 静态方法

如果一个方法不以`self`作为其第一个参数，它就是一个**静态方法**。

```rs
struct Configuration {
    version: u32,
    active: bool
}

impl Configuration {
    // `default` is a static method on `Configuration`
    fn default() -> Configuration {
        Configuration { version: 0, active: false }
    }
}
```

调用静态方法的唯一方法是使用**函数调用语法**：

```rs
// Function call syntax: <StructName>::<method_name>(<parameters>)
let default_config = Configuration::default();
```

### 等价性

即使对于以`self`作为第一个参数的方法，你也可以使用函数调用语法：

```rs
// Function call syntax:
//   <StructName>::<method_name>(<instance>, <parameters>)
let is_open = Ticket::is_open(ticket);
```

函数调用语法清楚地表明`ticket`被用作`self`，方法的第一个参数，但它确实更冗长。尽可能使用方法调用语法。

## 练习

本节练习位于[`03_ticket_v1/01_struct`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/03_ticket_v1/01_struct)
