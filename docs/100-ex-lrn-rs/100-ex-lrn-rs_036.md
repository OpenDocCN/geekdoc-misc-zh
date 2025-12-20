# From 和 Into

> 原文：[`rust-exercises.com/100-exercises/04_traits/09_from.html`](https://rust-exercises.com/100-exercises/04_traits/09_from.html)

让我们回到我们的字符串之旅开始的地方：

```rs
let ticket = Ticket::new(
    "A title".into(), 
    "A description".into(), 
    "To-Do".into()
);
```

我们现在已经足够了解，可以开始解析 `.into()` 在这里做了什么。

## 问题

这就是 `new` 方法的签名：

```rs
impl Ticket {
    pub fn new(
        title: String, 
        description: String, 
        status: String
    ) -> Self {
        // [...]
    }
}
```

我们还看到字符串字面量（如 `"A title"`) 的类型是 `&str`。

我们在这里有一个类型不匹配：期望 `String`，但我们有 `&str`。这次不会有魔法转换来救我们；我们需要 **执行转换**。

## `From` 和 `Into`

Rust 标准库在 `std::convert` 模块中定义了两个用于 **不可失败转换** 的 trait：`From` 和 `Into`。

```rs
pub trait From<T>: Sized {
    fn from(value: T) -> Self;
}

pub trait Into<T>: Sized {
    fn into(self) -> T;
}
```

这些 trait 定义展示了我们之前没有见过的几个概念：**超 trait** 和 **隐式 trait 约束**。让我们首先解析这些概念。

### 超 trait / 子 trait

`From: Sized` 语法意味着 `From` 是 `Sized` 的 **子 trait**：任何实现了 `From` 的类型也必须实现 `Sized`。或者，你也可以说 `Sized` 是 `From` 的 **超 trait**。

### 隐式 trait 约束

每次你有泛型类型参数时，编译器都会隐式地假设它是 `Sized`。

例如：

```rs
pub struct Foo<T> {
    inner: T,
}
```

实际上等价于：

```rs
pub struct Foo<T: Sized> 
{
    inner: T,
}
```

在 `From<T>` 的情况下，trait 定义等价于：

```rs
pub trait From<T: Sized>: Sized {
    fn from(value: T) -> Self;
}
```

换句话说，**T** 和实现 `From<T>` 的类型都必须是 `Sized`，尽管前者约束是隐式的。

### 负 trait 约束

你可以通过 **负 trait 约束** 来放弃隐式的 `Sized` 约束：

```rs
pub struct Foo<T: ?Sized> {
    //            ^^^^^^^
    //            This is a negative trait bound
    inner: T,
}
```

这个语法读作 "`T` 可能或可能不是 `Sized`"，它允许你将 `T` 绑定到一个 DST（例如 `Foo<str>`）。这是一个特殊情况：负 trait 约束仅限于 `Sized`，你不能与其他 trait 一起使用它们。

## 从 `&str` 到 `String`

在 [std 的文档](https://doc.rust-lang.org/std/convert/trait.From.html#implementors) 中，你可以看到哪些 `std` 类型实现了 `From` trait。

你会发现 `String` 实现了 `From<&str> for String`。因此，我们可以写出：

```rs
let title = String::from("A title");
```

尽管如此，我们主要使用的是 `.into()`。

如果你查看 `Into` 的实现者 [implementors of `Into`](https://doc.rust-lang.org/std/convert/trait.Into.html#implementors)，你不会找到 `Into<String> for &str`。这是怎么回事？

`From` 和 `Into` 是 **对偶 trait**。

特别是，`Into` 为任何实现了 `From` 的类型使用 **泛型实现**：

```rs
impl<T, U> Into<U> for T
where
    U: From<T>,
{
    fn into(self) -> U {
        U::from(self)
    }
}
```

如果类型 `U` 实现了 `From<T>`，则自动实现了 `Into<U> for T`。这就是为什么我们可以写出 `let title = "A title".into();`。

## `.into()`

每次你看到 `.into()`，你都在见证类型之间的转换。

那么目标类型是什么呢？

在大多数情况下，目标类型是以下之一：

+   由函数/方法的签名指定（例如，我们上面的例子中的 `Ticket::new`）

+   在变量声明中指定类型注解（例如 `let title: String = "A title".into();`）

`.into()` 将会自动工作，只要编译器可以从上下文中无歧义地推断出目标类型。

## 练习

本节的练习位于 [04_traits/09_from](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/09_from)
