# 生命周期

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/06_lifetimes.html`](https://rust-exercises.com/100-exercises/06_ticket_management/06_lifetimes.html)

让我们通过为 `&TicketStore` 添加 `IntoIterator` 的实现来尝试完成之前的练习，以在 `for` 循环中获得最大便利。

让我们从填写实现中最“明显”的部分开始：

```rs
impl IntoIterator for &TicketStore {
    type Item = &Ticket;
    type IntoIter = // What goes here?

    fn into_iter(self) -> Self::IntoIter {
        self.tickets.iter()
    }
}
```

`type IntoIter` 应该设置为哪种类型？

直观地看，它应该是 `self.tickets.iter()` 返回的类型，即 `Vec::iter()` 返回的类型。

如果你检查标准库文档，你会发现 `Vec::iter()` 返回一个 `std::slice::Iter`。`Iter` 的定义如下：

```rs
pub struct Iter<'a, T> { /* fields omitted */ }
```

`'a` 是一个**生命周期参数**。

## 生命周期参数

生命周期是 Rust 编译器用来跟踪一个引用（无论是可变还是不可变）有效期的**标签**。

引用的生命周期受其所引用的值的范围约束。Rust 总是在编译时确保引用在它们所引用的值被丢弃后不会使用，以避免悬垂指针和使用后释放的漏洞。

这听起来应该很熟悉：当我们讨论所有权和借用时，我们已经看到了这些概念的实际应用。生命周期只是命名一个特定引用有效期的**方式**。

当你有多个引用并且需要明确它们如何**相互关联**时，命名变得很重要。让我们看看 `Vec::iter()` 的签名：

```rs
impl <T> Vec<T> {
    // Slightly simplified
    pub fn iter<'a>(&'a self) -> Iter<'a, T> {
        // [...]
    }
}
```

`Vec::iter()` 是一个名为 `'a` 的生命周期参数的泛型。

`'a` 用于**绑定** `Vec` 的生命周期和由 `iter()` 返回的 `Iter` 的生命周期。用简单的话来说：由 `iter()` 返回的 `Iter` 不能比它从其中创建的 `Vec` 引用 (`&self`) 活得更久。

这很重要，因为，如我们所讨论的，`Vec::iter` 返回一个遍历 `Vec` 元素引用的迭代器。如果 `Vec` 被丢弃，迭代器返回的引用将变得无效。Rust 必须确保这种情况不会发生，生命周期是它用来强制执行此规则的工具。

## 生命周期省略

Rust 有一些称为**生命周期省略规则**的规则，允许你在许多情况下省略显式的生命周期注解。例如，`Vec::iter` 在 `std` 的源代码中的定义如下：

```rs
impl <T> Vec<T> {
    pub fn iter(&self) -> Iter<'_, T> {
        // [...]
    }
}
```

`Vec::iter()` 的签名中没有显式的生命周期参数。省略规则意味着由 `iter()` 返回的 `Iter` 的生命周期绑定到 `&self` 引用的生命周期。你可以将 `'_` 视为生命周期引用的**占位符**。

请参阅 参考文献 部分，以获取有关生命周期省略的官方文档链接。

在大多数情况下，你可以依赖编译器告诉你何时需要添加显式的生命周期注解。

## 参考文献

+   [std::vec::Vec::iter](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.iter)

+   [std::slice::Iter](https://doc.rust-lang.org/std/slice/struct.Iter.html)

+   [生命周期省略规则](https://doc.rust-lang.org/reference/lifetime-elision.html)

## 练习

本节练习位于[`06_ticket_management/06_lifetimes`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/06_lifetimes)
