# 控制流，第一部分

> 原文：[`rust-exercises.com/100-exercises/02_basic_calculator/03_if_else.html`](https://rust-exercises.com/100-exercises/02_basic_calculator/03_if_else.html)

到目前为止，我们编写的所有程序都很直接。

一系列指令从上到下执行，就是这样。

是时候介绍一些**分支**了。

## `if`子句

`if`关键字用于在条件为真时执行一个代码块。

这里有一个简单的例子：

```rs
let number = 3;
if number < 5 {
    println!("`number` is smaller than 5");
}
```

这个程序将打印`number is smaller than 5`，因为条件`number < 5`为真。

### `else`子句

和大多数编程语言一样，Rust 支持可选的`else`分支，当`if`表达式的条件为假时执行一个代码块。

例如：

```rs
let number = 3;

if number < 5 {
    println!("`number` is smaller than 5");
} else {
    println!("`number` is greater than or equal to 5");
}
```

### `else if`子句

当你有多个`if`表达式，一个嵌套在另一个内部时，你的代码会越来越向右偏移。

```rs
let number = 3;

if number < 5 {
    println!("`number` is smaller than 5");
} else {
    if number >= 3 {
        println!("`number` is greater than or equal to 3, but smaller than 5");
    } else {
        println!("`number` is smaller than 3");
    }
}
```

你可以使用`else if`关键字将多个`if`表达式合并为一个：

```rs
let number = 3;

if number < 5 {
    println!("`number` is smaller than 5");
} else if number >= 3 {
    println!("`number` is greater than or equal to 3, but smaller than 5");
} else {
    println!("`number` is smaller than 3");
}
```

## 布尔值

`if`表达式中的条件必须是类型`bool`，即**布尔**类型。

布尔值，就像整数一样，是 Rust 中的原始类型。

布尔值有两种可能的值：`true`或`false`。

### 没有真值或假值

如果`if`表达式的条件不是布尔类型，你将得到一个编译错误。

例如，以下代码将无法编译：

```rs
let number = 3;
if number {
    println!("`number` is not zero");
}
```

你将得到以下编译错误：

```rs
error[E0308]: mismatched types
 --> src/main.rs:3:8
  |
3 |     if number {
  |        ^^^^^^ expected `bool`, found integer 
```

这遵循 Rust 关于类型转换的哲学：没有从非布尔类型到布尔类型的自动转换。Rust 没有 JavaScript 或 Python 中的**真值**或**假值**的概念。

你必须明确你想要检查的条件。

### 比较运算符

使用比较运算符为`if`表达式构建条件是很常见的。

在 Rust 中处理整数时，可用的比较运算符如下：

+   `==`: 等于

+   `!=`: 不等于

+   `<`: 小于

+   `>`: 大于

+   `<=`: 小于或等于

+   `>=`: 大于或等于

## `if/else`是一个表达式

在 Rust 中，`if`表达式是**表达式**，而不是**语句**：它们返回一个值。

那个值可以被分配给一个变量或用于其他表达式。例如：

```rs
let number = 3;
let message = if number < 5 {
    "smaller than 5"
} else {
    "greater than or equal to 5"
};
```

在上面的例子中，`if`语句的每个分支都评估为字符串字面量，然后被分配给`message`变量。

唯一的要求是`if`的两个分支返回相同类型。

## 练习

本节练习位于[`02_basic_calculator/03_if_else`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/02_basic_calculator/03_if_else)
