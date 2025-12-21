# 可变性

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/mutability.html`](https://freddiehaddad.github.io/fast-track-to-rust/mutability.html)

在我们的 rustle 程序的第 13 行和第 18 行添加了两行代码。变量`i`将在每次循环迭代时递增，我们将用它来打印行号。请运行代码。

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

    let i = 1;
    for line in poem.lines() {
        if line.contains(pattern) {
            println!("{i}: {line}");
        }
        i += 1;
    }
}
```

哎呀！出错了。幸运的是，编译器（`rustc`）会发出非常有帮助的错误信息.^(1) 变量`i`是不可变的！

## 变量和可变性

Rust 中的变量默认是不可变的。这个设计选择有助于你编写利用 Rust 的内存安全和无恐惧并发特性的代码。更多详情，你可以参考 Rust 文档中关于[变量和可变性](https://doc.rust-lang.org/book/ch03-01-variables-and-mutability.html)的部分。虽然语言鼓励不可变性，但在某些情况下，修改值是必要的。在这种情况下，我们使用`mut`关键字。

```rs
let mut i = 1;
```

好的，请在第 13 行添加`mut`关键字，然后再次运行程序。

我们将探讨需要和适合使用不可变性的情况。然而，让我们看看迭代器如何被用来避免需要可变计数器的需求。

* * *

1.  已经投入了大量努力使`rustc`具有出色的错误信息。为了帮助理解如何解释它们，请参考文档中的[诊断结构](https://rustc-dev-guide.rust-lang.org/diagnostics.html#diagnostic-structure)。↩
