# 循环，第二部分：for

> 原文：[`rust-exercises.com/100-exercises/02_basic_calculator/07_for.html`](https://rust-exercises.com/100-exercises/02_basic_calculator/07_for.html)

手动增加计数器变量有些繁琐。这种模式也非常常见！

为了使这个过程更简单，Rust 提供了一种更简洁的方式来遍历一系列值：`for` 循环。

## `for` 循环

`for` 循环是一种执行代码块的方式，每次迭代器^(1)中的每个元素。

这里是通用的语法：

```rs
for <element> in <iterator> {
    // code to execute
}
```

## 范围

Rust 的标准库提供了一个 **range** 类型，可以用来遍历一系列数字^(2)。

例如，如果我们想计算从 1 到 5 的数字之和：

```rs
let mut sum = 0;
for i in 1..=5 {
    sum += i;
}
```

每次循环运行时，`i` 将被分配范围中的下一个值，然后执行代码块。

Rust 中有五种类型的范围：

+   `1..5`：一个（半开）范围。它包括从 1 到 4 的所有数字。它不包括最后一个值，5。

+   `1..=5`：一个包含范围。它包括从 1 到 5 的所有数字。它包括最后一个值，5。

+   `1..`：一个开放范围。它包括从 1 到无穷大（好吧，直到整型类型的最大值）的所有数字。

+   `..5`：一个从整型类型的最低值开始，到 4 结束的范围。它不包括最后一个值，5。

+   `..=5`：一个从整型类型的最低值开始，到 5 结束的范围。它包括最后一个值，5。

你可以使用 `for` 循环与前三种类型的范围一起使用，其中起始点是明确指定的。最后两种范围类型在其他上下文中使用，我们将在后面介绍。

范围的极值不一定是整型字面量——它们也可以是变量或表达式！

例如：

```rs
let end = 5;
let mut sum = 0;

for i in 1..(end + 1) {
    sum += i;
}
```

## 进一步阅读

+   [`for` 循环文档](https://doc.rust-lang.org/std/keyword.for.html)

## 练习

本节的练习位于[`02_basic_calculator/07_for`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/02_basic_calculator/07_for)

* * *

1.  在本课程的后期，我们将给出“迭代器”的确切定义。现在，你可以将其视为可以循环遍历的一系列值。↩

1.  你还可以使用范围与其他类型一起使用（例如字符和 IP 地址），但在日常 Rust 编程中，整数无疑是最常见的用例。↩
