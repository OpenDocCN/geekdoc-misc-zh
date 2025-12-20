# impl Trait

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/08_impl_trait.html`](https://rust-exercises.com/100-exercises/06_ticket_management/08_impl_trait.html)

`TicketStore::to_dos` 返回一个 `Vec<&Ticket>`。

这个签名在每次调用 `to_dos` 时都会引入一个新的堆分配，这可能是不必要的，取决于调用者需要用结果做什么。如果 `to_dos` 返回一个迭代器而不是 `Vec`，那就更好了，这样调用者就可以决定是将结果收集到一个 `Vec` 中，还是只是迭代它们。

然而，这很棘手！下面实现的 `to_dos` 的返回类型是什么？

```rs
impl TicketStore {
    pub fn to_dos(&self) -> ??? {
        self.tickets.iter().filter(|t| t.status == Status::ToDo)
    }
}
```

## 不可命名类型

`filter` 方法返回一个 `std::iter::Filter` 的实例，其定义如下：

```rs
pub struct Filter<I, P> { /* fields omitted */ }
```

其中 `I` 是正在过滤的迭代器的类型，而 `P` 是用于过滤元素的谓词。

我们知道在这种情况下 `I` 是 `std::slice::Iter<'_, Ticket>`，但 `P` 呢？

`P` 是一个闭包，一个 **匿名函数**。正如其名所示，闭包没有名称，所以我们不能在代码中将其写下来。

Rust 有一个解决方案：**impl Trait**。

## `impl Trait`

`impl Trait` 是一个允许你返回一个类型而不指定其名称的特性。你只需声明该类型实现了哪些特质，Rust 就会自动推断其余部分。

在这种情况下，我们想要返回一个指向 `Ticket` 的引用迭代器：

```rs
impl TicketStore {
    pub fn to_dos(&self) -> impl Iterator<Item = &Ticket> {
        self.tickets.iter().filter(|t| t.status == Status::ToDo)
    }
}
```

就这样！

## 泛型？

返回位置上的 `impl Trait` **不是**一个泛型参数。

泛型是用于类型的占位符，这些类型由函数的调用者填充。具有泛型参数的函数是 **多态的**：它可以使用不同的类型调用，编译器将为每种类型生成不同的实现。

对于 `impl Trait` 来说情况并非如此。具有 `impl Trait` 的函数的返回类型在编译时是 **固定的**，编译器将为其生成单个实现。这就是为什么 `impl Trait` 也被称为 **不可见返回类型**：调用者不知道返回值的确切类型，只知道它实现了指定的特质（s）。但是编译器知道确切的类型，没有涉及多态。

## RPIT

如果你阅读了关于 Rust 的 RFC 或深入研究，你可能会遇到缩写 **RPIT**。

它代表 **"Return Position Impl Trait"**，指的是在返回位置使用 `impl Trait`。

## 练习

本节的练习位于 `06_ticket_management/08_impl_trait` 中（[`github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/08_impl_trait`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/08_impl_trait)）
