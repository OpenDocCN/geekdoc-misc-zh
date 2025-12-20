# 循环，第一部分：while

> 原文：[`rust-exercises.com/100-exercises/02_basic_calculator/06_while.html`](https://rust-exercises.com/100-exercises/02_basic_calculator/06_while.html)

您对`factorial`的实现已被强制使用递归。

这可能对您来说很自然，尤其是如果您来自函数式编程背景。或者，如果您习惯了像 C 或 Python 这样的更命令式语言，可能会觉得有些奇怪。

让我们看看您如何使用`loop`来实现相同的功能。

## `while`循环

`while`循环是一种在条件为真时执行代码块的方式。

这里是通用语法：

```rs
while <condition> {
    // code to execute
}
```

例如，我们可能想要计算从 1 到 5 的数字之和：

```rs
let sum = 0;
let i = 1;
// "while i is less than or equal to 5"
while i <= 5 {
    // `+=` is a shorthand for `sum = sum + i`
    sum += i;
    i += 1;
}
```

这将不断将 1 加到`i`上，并将`i`加到`sum`上，直到`i`不再小于或等于 5。

## `mut`关键字

上述示例将无法编译。您将得到类似以下错误：

```rs
error[E0384]: cannot assign twice to immutable variable `sum`
 --> src/main.rs:7:9
  |
2 |     let sum = 0;
  |         ---
  |         |
  |         first assignment to `sum`
  |         help: consider making this binding mutable: `mut sum`
...
7 |         sum += i;
  |         ^^^^^^^^ cannot assign twice to immutable variable

error[E0384]: cannot assign twice to immutable variable `i`
 --> src/main.rs:8:9
  |
3 |     let i = 1;
  |         -
  |         |
  |         first assignment to `i`
  |         help: consider making this binding mutable: `mut i`
...
8 |         i += 1;
  |         ^^^^^^ cannot assign twice to immutable variable 
```

这是因为 Rust 中的变量默认是**不可变的**。

一旦赋值，您就不能更改它们的值。

如果您想要允许修改，必须使用`mut`关键字将变量声明为**可变的**：

```rs
// `sum` and `i` are mutable now!
let mut sum = 0;
let mut i = 1;

while i <= 5 {
    sum += i;
    i += 1;
}
```

这将编译并运行而不会出现错误。

## 进一步阅读

+   [`while`循环文档](https://doc.rust-lang.org/std/keyword.while.html)

## 练习

本节练习位于[`02_basic_calculator/06_while`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/02_basic_calculator/06_while)
