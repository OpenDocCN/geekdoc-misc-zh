# 推导宏

> 原文：[`rust-exercises.com/100-exercises/04_traits/04_derive.html`](https://rust-exercises.com/100-exercises/04_traits/04_derive.html)

实现`Ticket`的`PartialEq`有点繁琐，不是吗？你必须手动比较结构体的每个字段。

## 解构语法

此外，实现是脆弱的：如果结构体定义发生变化（例如添加了新字段），你必须记得更新`PartialEq`的实现。

你可以通过将结构体解构为其字段来降低风险：

```rs
impl PartialEq for Ticket {
    fn eq(&self, other: &Self) -> bool {
        let Ticket {
            title,
            description,
            status,
        } = self;
        // [...]
    }
}
```

如果`Ticket`的定义发生变化，编译器将报错，抱怨你的解构不再详尽。

你也可以重命名结构体字段，以避免变量遮蔽：

```rs
impl PartialEq for Ticket {
    fn eq(&self, other: &Self) -> bool {
        let Ticket {
            title,
            description,
            status,
        } = self;
        let Ticket {
            title: other_title,
            description: other_description,
            status: other_status,
        } = other;
        // [...]
    }
}
```

解构是工具箱中的一个有用模式，但还有更方便的方法来做这件事：**推导宏**。

## 宏

你已经在过去的练习中遇到了几个宏：

+   `assert_eq!`和`assert!`，在测试用例中

+   `println!`，用于打印到控制台

Rust 宏是**代码生成器**。

它们根据你提供的输入生成新的 Rust 代码，然后该生成的代码将与你的程序的其他部分一起编译。一些宏是内置在 Rust 的标准库中的，但你也可以编写自己的宏。我们不会在本课程中创建自己的宏，但你可以在"进一步阅读"部分中找到一些有用的提示。

### 检查

一些 IDE 允许你展开宏来检查生成的代码。如果不行，你可以使用`cargo-expand`。

### 推导宏

**推导宏**是 Rust 宏的一种特定类型。它被指定为结构体顶部的**属性**。

```rs
#[derive(PartialEq)]
struct Ticket {
    title: String,
    description: String,
    status: String
}
```

推导宏用于自动为自定义类型实现常见（且“明显”）的特质。在上面的例子中，`PartialEq`特质自动应用于`Ticket`。如果你展开宏，你会看到生成的代码在功能上等同于你手动编写的代码，尽管阅读起来稍微有些繁琐：

```rs
#[automatically_derived]
impl ::core::cmp::PartialEq for Ticket {
    #[inline]
    fn eq(&self, other: &Ticket) -> bool {
        self.title == other.title 
            && self.description == other.description
            && self.status == other.status
    }
}
```

编译器会建议你在可能的情况下推导特质。

## 进一步阅读

+   [Rust 宏小书](https://veykril.github.io/tlborm/)

+   [进程宏研讨会](https://github.com/dtolnay/proc-macro-workshop)

## 练习

本节练习位于[`04_traits/04_derive`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/04_derive)
