# 可空性

> [原文链接](https://rust-exercises.com/100-exercises/05_ticket_v2/05_nullability.html)

我们对`assigned`方法的实现相当直接：对于待办和已完成票据的恐慌处理远非理想。

我们可以使用**Rust 的`Option`类型**做得更好。

## `Option`

`Option`是 Rust 类型，表示**可空值**。

它是一个枚举，定义在 Rust 的标准库中：

```rs
enum Option<T> {
    Some(T),
    None,
}
```

`Option`编码了值可能存在（`Some(T)`）或不存在（`None`）的想法。

它还强制你**显式处理两种情况**。如果你在处理可空值时忘记了处理`None`情况，你会得到编译器错误。

这在其他语言的“隐式”可空性方面是一个显著的改进，在其他语言中，你可能忘记检查`null`，从而触发运行时错误。

## `Option`的定义

`Option`的定义使用了你之前没有见过的 Rust 构造：**类似元组的变体**。

### 类似元组的变体

`Option`有两个变体：`Some(T)`和`None`。

`Some`是一个**类似元组的变体**：它是一个包含**未命名字段**的变体。

类似元组的变体通常在只有一个字段要存储时使用，尤其是在我们查看类似`Option`的“包装”类型时。

### 类似元组的结构体

它们不仅限于枚举——你也可以定义类似元组的结构体：

```rs
struct Point(i32, i32);
```

你可以使用位置索引来访问`Point`实例的两个字段：

```rs
let point = Point(3, 4);
let x = point.0;
let y = point.1;
```

### 元组

当我们还没有看到元组时，说某物是类似元组的有点奇怪！

元组是 Rust 原始类型的另一个例子。它们将固定数量的值（可能具有不同的类型）组合在一起：

```rs
// Two values, same type
let first: (i32, i32) = (3, 4);
// Three values, different types
let second: (i32, u32, u8) = (-42, 3, 8);
```

语法很简单：你在括号内列出值的类型，用逗号分隔。你可以使用点符号和字段索引来访问元组的字段：

```rs
assert_eq!(second.0, -42);
assert_eq!(second.1, 3);
assert_eq!(second.2, 8);
```

当你懒得定义一个专门的`struct`类型来组合值时，元组是一个方便的组合值的方式。

## 练习

本节练习位于[`05_ticket_v2/05_nullability`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/05_nullability)
