# TryFrom 和 TryInto

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/13_try_from.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/13_try_from.html)

在上一章中，我们探讨了 `From` 和 `Into` 特性（From 和 Into 特性），这是 Rust 中用于**不可靠**类型转换的惯用接口。

但如果转换不能保证成功怎么办？

我们现在对错误有了足够的了解，可以讨论 `From` 和 `Into` 的**可失败**对应物：`TryFrom` 和 `TryInto`。

## TryFrom 和 TryInto

`TryFrom` 和 `TryInto` 都定义在 `std::convert` 模块中，就像 `From` 和 `Into` 一样。

```rs
pub trait TryFrom<T>: Sized {
    type Error;
    fn try_from(value: T) -> Result<Self, Self::Error>;
}

pub trait TryInto<T>: Sized {
    type Error;
    fn try_into(self) -> Result<T, Self::Error>;
}
```

`From`/`Into` 和 `TryFrom`/`TryInto` 之间的主要区别在于后者返回一个 `Result` 类型。

这允许转换失败，返回错误而不是恐慌。

## Self::Error

`TryFrom` 和 `TryInto` 都有一个关联的 `Error` 类型。这允许每个实现指定自己的错误类型，理想情况下是最适合尝试的转换。

`Self::Error` 是引用在特性本身中定义的 `Error` 关联类型的一种方式。

## 对偶性

就像 `From` 和 `Into` 一样，`TryFrom` 和 `TryInto` 是成对出现的特性。

如果你为某个类型实现了 `TryFrom`，你将免费获得 `TryInto`。

## 练习

本节的练习位于（[05_ticket_v2/13_try_from](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/13_try_from)）
