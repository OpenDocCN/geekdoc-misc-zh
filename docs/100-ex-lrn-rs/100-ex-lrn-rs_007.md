# 潘克

> 原文：[`rust-exercises.com/100-exercises/02_basic_calculator/04_panics.html`](https://rust-exercises.com/100-exercises/02_basic_calculator/04_panics.html)

让我们回到您为 "变量" 部分 编写的 `speed` 函数。它可能看起来像这样：

```rs
fn speed(start: u32, end: u32, time_elapsed: u32) -> u32 {
    let distance = end - start;
    distance / time_elapsed
}
```

如果您有敏锐的观察力，您可能已经发现了一个问题^(1)：如果 `time_elapsed` 为零会发生什么？

您可以在 [Rust playground](https://play.rust-lang.org/?version=stable&mode=debug&edition=2021&gist=36e5ddbe3b3f741dfa9f74c956622bac) 上尝试它！

程序将以以下错误信息退出：

```rs
thread 'main' panicked at src/main.rs:3:5:
attempt to divide by zero 
```

这被称为**恐慌**。

潘克是 Rust 用来表示程序遇到严重错误，无法继续执行的一种方式，它是一个**不可恢复的错误**^(2)。除以零就属于这类错误。

## panic! 宏

您可以通过调用 `panic!` 宏来有意地触发恐慌^(3):

```rs
fn main() {
    panic!("This is a panic!");
    // The line below will never be executed
    let x = 1 + 2;
}
```

Rust 中还有其他机制可以处理可恢复的错误，我们将在稍后的课程中介绍。我们将在稍后 覆盖这些内容。目前，我们将坚持使用恐慌作为粗暴但简单的临时解决方案。

## 进一步阅读

+   [panic! 宏文档](https://doc.rust-lang.org/std/macro.panic.html)

## 练习

本节练习位于 `02_basic_calculator/04_panics` 中[`github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/02_basic_calculator/04_panics`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/02_basic_calculator/04_panics)

* * *

1.  关于 `speed` 的问题我们很快就会解决。你能发现它吗？↩

1.  您可以尝试捕获一个恐慌，但这应该是一种最后的手段，仅限于非常特定的情况。↩

1.  如果它后面跟着一个 `!`，则表示宏调用。现在，我们可以将宏视为带有香料的函数。我们将在课程中稍后更详细地介绍它们。↩
