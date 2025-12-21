# 迭代器

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/iterators.html`](https://freddiehaddad.github.io/fast-track-to-rust/iterators.html)

迭代器在 Rust 中无处不在，要全面深入地探讨它们，可能需要将这门课程更名为 **慢速 Rust 进阶之路**。我们将介绍基础知识，并指导您查阅关于 [迭代器](https://doc.rust-lang.org/book/ch13-02-iterators.html#processing-a-series-of-items-with-iterators) 的所有复杂细节的文档。

控制流 部分解释说，在 `for` 循环中对 `lines()` 的调用返回一个迭代器。我们说 `for` 循环 *消费* 迭代器。然而，在 Rust 中，我们可以做比仅仅消费迭代器更多的事情！

## 迭代器适配器

可以使用 [迭代器适配器](https://doc.rust-lang.org/book/ch13-02-iterators.html?search=#methods-that-produce-other-iterators) 创建新的迭代器。这些适配器生成新的迭代器，修改原始迭代器的某些方面。让我们使用一个来打印行号。

`enumerate` 函数创建一个迭代器，它返回当前迭代计数以及前一个迭代器的值，以 `(index, value)` 的元组形式。在循环中，`i` 的类型是 `usize`，而 `line` 的类型是 `&str`。

```rs
fn main() {
 let pattern = "him"; let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";      for (i, line) in poem.lines().enumerate() {
        if line.contains(pattern) {
            println!("{}: {line}", i + 1);
        }
    }
}
```

## 高级迭代器

我们可以通过使用 `filter_map` 迭代器适配器来进一步操作，返回只包含我们想要的项目的迭代器！

```rs
fn main() {
 let pattern = "him"; let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";      for (line_no, line) in
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

哇！刚才发生了什么？我们正在快速学习 Rust，所以我们要加快速度！让我们来分解一下，因为这段代码需要一些解释。

* * *

1.  一个 [元组](https://doc.rust-lang.org/rust-by-example/primitives/tuples.html#tuples) 是由不同类型的值组成的集合，它使用括号 `()` 构建而成。↩
