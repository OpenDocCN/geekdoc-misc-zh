# 闭包

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/closures.html`](https://freddiehaddad.github.io/fast-track-to-rust/closures.html)

在 Rust 中，[闭包](https://doc.rust-lang.org/book/ch13-01-closures.html) 是可以捕获其周围环境的函数，可以清晰地表达程序员的意图，并以低级性能实现这一点。它们在函数式编程语言中相当常见。

Rust 中的闭包有一些独特的特性：

+   参数用 `||` 而不是 `()` 括起来。

+   函数体周围的括号 `{}` 对于单行表达式是可选的。

## 回到我们的循环

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

    for (line_no, line) in
        poem.lines()
            .enumerate()
            .filter_map(|(i, line)| match line.contains(pattern) {
                true => Some((i + 1, line)),
                false => None,
            })
    {
        println!("{line_no}: {line}");
    }
}
```

在代码片段中，闭包是：

```rs
|(i, line)| match line.contains(pattern) {
    true => Some((i + 1, line)),
    false => None,
}
```

## filter_map

`filter_map` 函数 (1) 创建了一个同时过滤和映射的迭代器。它调用一个闭包，并过滤掉结果中的 `None`，留下包含所有匹配模式行号和行的元组的迭代器。当 `for` 循环消耗迭代器时，我们只需要打印结果，因为我们只剩下包含模式的行！

> 回想一下，`enumerate` 返回一个元组的迭代器。`filter_map` 接收元组作为闭包的参数。

# 练习

+   将 `filter_map` 替换为 `map` 和 `filter` 以实现相同的结果。注意 `filter_map` 如何产生更高效和简洁的代码。

<details><summary>解决方案</summary>

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

    for (line_no, line) in poem
        .lines()
        .enumerate()
        .map(|(i, line)| (i + 1, line))
        .filter(|(_line_no, line)| line.contains(pattern))
    {
        println!("{line_no}: {line}");
    }
}
```

> `_line_no` 中的下划线 `_` 前缀是我们告诉 Rust 编译器我们有意忽略第一个参数的方式。如果没有它，编译器将会报错。</details>

# 总结

在本节中我们：

+   引入了 `Option` 枚举

+   学习了闭包

+   使用了迭代器

+   学习了 `mut` 关键字

# 下一页

接下来是集合！

* * *

1.  存在独立的 `filter` 和 `map` 迭代器。 ↩
