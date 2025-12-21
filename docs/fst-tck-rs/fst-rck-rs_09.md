# 变量

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/variables.html`](https://freddiehaddad.github.io/fast-track-to-rust/variables.html)

Rust 是一种静态类型语言，这意味着所有变量都有类型，并且这种类型必须在编译时已知。`let`关键字用于声明变量，或者更准确地说，用于变量绑定。

`let`语句的结构^(1) ^(2)：

```rs
let identifier: type = expression;
```

## 类型推断

由于`y`作为参数传递给需要 32 位有符号整数的`print_value`函数，编译器推断出其类型。因此，可以省略`x`的显式类型声明。

```rs
fn print_value(value: i32) {
    println!("{value}");
}

fn main() {
    let x: i32 = 10;
    let y = 20;

    print_value(x);
    print_value(y);
}
```

## Rustle 变量

要开始我们的 rustle 程序，我们目前将避免通过命令行参数处理用户输入。相反，我们将硬编码一些字符串并执行一些简单的*rustling*。让我们使用诗人罗伯特·路易斯·斯蒂文森的著名诗作《我的影子》作为我们的输入。

```rs
fn main() {
    let pattern = "him";
    let poem = "I have a little shadow that goes in and out with me,
                And what can be the use of him is more than I can see.
                He is very, very like me from the heels up to the head;
                And I see him jump before me, when I jump into my bed.

                The funniest thing about him is the way he likes to grow -
                Not at all like proper children, which is always very slow;
                For he sometimes shoots up taller like an india-rubber ball,
                And he sometimes gets so little that there's none of him at all.";
}
```

下一步是搜索诗中该模式的出现并打印结果。为了实现这一点，我们需要学习一些关于控制流的知识。

# 总结

在本节中，我们：

+   学习了如何声明变量。

+   探索了 Rust 的类型推断。

# 下一步

接下来是控制流。

* * *

1.  [`let`语句](https://doc.rust-lang.org/reference/statements.html#let-statements)支持尚未涵盖的更高级功能。↩

1.  在许多情况下，编译器可以推断类型，允许你省略它。↩
