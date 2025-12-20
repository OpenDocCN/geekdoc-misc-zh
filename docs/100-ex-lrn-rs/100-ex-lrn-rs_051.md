# 错误特性

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/09_error_trait.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/09_error_trait.html)

## 错误报告

在之前的练习中，你必须解构`TitleError`变体来提取错误信息并将其传递给`panic!`宏。

这是一个（基础的）错误报告示例：将错误类型转换为可以展示给用户、服务操作员或开发者的表示形式。

对于每个 Rust 开发者来说，提出自己的错误报告策略并不实际：这将浪费时间和精力，并且不会很好地在不同项目间组合。这就是为什么 Rust 提供了`std::error::Error`特性。

## `Error`特性

在`Result`中的`Err`变体类型没有限制，但使用实现`Error`特性的类型是一种良好的实践。`Error`是 Rust 错误处理故事的核心：

```rs
// Slightly simplified definition of the `Error` trait
pub trait Error: Debug + Display {}
```

你可能还记得来自`From`特性的`:`语法——它用于指定**超特性**。对于`Error`，有两个超特性：`Debug`和`Display`。如果一个类型想要实现`Error`，它必须也实现`Debug`和`Display`。

## `Display`和`Debug`

我们已经在之前的练习中遇到了`Debug`特性（/100-exercises/04_traits/04_derive）——它是`assert_eq!`在断言失败时用来显示变量值的特性。

从“机械”的角度来看，`Display`和`Debug`是相同的——它们编码了类型应该如何转换为类似字符串的表示形式：

```rs
// `Debug`
pub trait Debug {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}

// `Display`
pub trait Display {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}
```

它们的区别在于其*目的*：`Display`返回一个针对“最终用户”的表示形式，而`Debug`提供的是一个更适合开发者和服务操作员的低级表示形式。

这就是为什么`Debug`可以使用`#[derive(Debug)]`属性自动实现，而`Display`**需要**手动实现。

## 练习

本节练习位于[`05_ticket_v2/09_error_trait`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/09_error_trait)
