# 只能有一个

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/there_can_be_only_one.html`](https://freddiehaddad.github.io/fast-track-to-rust/there_can_be_only_one.html)

目前，我们的整个 rustle 程序都包含在`main`函数中。这种做法是为了以逻辑顺序和易于理解的方式介绍重要概念来应对课程教学中的挑战。然而，现在是时候将`main`函数中的某些代码重构为单独的函数了。

让我们先创建一个函数来处理查找输入中包含指定模式的所有行的任务。以下是函数签名：

```rs
fn find_matching_lines(lines: Vec<&str>, pattern: &str) -> Vec<usize>
```

这是我们将转移到新函数中的代码：

```rs
// store the 0-based line number for any matched line
let match_lines: Vec<_> = lines
    .iter()
    .enumerate()
    .filter_map(|(i, line)| match line.contains(pattern) {
        true => Some(i),
        false => None,
    })
    .collect(); // turns anything iterable into a collection
```

这是经过更改后实现的修订代码。请审查它并运行代码。

```rs
use std::iter::FromIterator; // this line addresses a rust playground bug   fn find_matching_lines(lines: Vec<&str>, pattern: &str) -> Vec<usize> {
    lines
        .iter()
        .enumerate()
        .filter_map(|(i, line)| match line.contains(pattern) {
            true => Some(i),
            false => None,
        })
        .collect() // turns anything iterable into a collection
        // The return keyword is unnecessary when the returned value is the
        // final expression in a function. In this scenario, the semicolon (;)
        // is omitted.
}

fn main() {
    let poem = "I have a little shadow that goes in and out with me,
                And what can be the use of him is more than I can see.
                He is very, very like me from the heels up to the head;
                And I see him jump before me, when I jump into my bed.

                The funniest thing about him is the way he likes to grow -
                Not at all like proper children, which is always very slow;
                For he sometimes shoots up taller like an india-rubber ball,
                And he sometimes gets so little that there's none of him at all.";

    // command line arguments
    let pattern = "all";
    let before_context = 1;
    let after_context = 1;

    // convert the poem into lines
    let lines = Vec::from_iter(poem.lines());

    // store the 0-based line number for any matched line
    let match_lines = find_matching_lines(lines, pattern);

    // create intervals of the form [a,b] with the before/after context
    let mut intervals: Vec<_> = match_lines
        .iter()
        .map(|line| {
            (
                line.saturating_sub(before_context),
                line.saturating_add(after_context),
            )
        })
        .collect();

    // merge overlapping intervals
    intervals.dedup_by(|next, prev| {
        if prev.1 < next.0 {
            false
        } else {
            prev.1 = next.1;
            true
        }
    });

    // print the lines
    for (start, end) in intervals {
        for (line_no, line) in
            lines.iter().enumerate().take(end + 1).skip(start)
        {
            println!("{}: {}", line_no + 1, line)
        }
    }
}
```

## 哎呀！

一处微小的代码更改导致程序出现问题。幸运的是，Rust 编译器提供了有用的信息来诊断问题。然而，如果你不熟悉 Rust 的所有权规则，理解这个错误可能会很具挑战性。让我们分解错误并了解出了什么问题。以下是错误消息中的关键细节，经过整理以提高可读性：

```rs
error[E0382]: borrow of moved value: `lines`
    --> src/main.rs:63:13
     |
34   |     let lines = Vec::from_iter(poem.lines());
     |         ----- move occurs because `lines` has type `Vec<&str>`, which
     |               does not implement the `Copy` trait
...
37   |     let match_lines = find_matching_lines(lines, pattern);
     |                                           ----- value moved here
...
63   |             lines.iter().enumerate().take(end + 1).skip(start)
     |             ^^^^^^^^^^^^ value borrowed here after move
     | 
```

### 错误解包

复制特质，值移动，值借用。这一切究竟是什么意思？

#### 复制特质

我们将在课程的后半部分更详细地探讨[特质](https://doc.rust-lang.org/book/ch10-02-traits.html)。现在，只需知道当一个类型实现了`[`Copy`](https://doc.rust-lang.org/std/marker/trait.Copy.html)`特质时，其值在赋值给新变量时会被复制。这意味着赋值之后，原始变量和新变量都可以独立使用。

我们传递给`find_matching_lines`函数的`lines`向量*没有*实现`[`Copy`](https://doc.rust-lang.org/std/marker/trait.Copy.html)`特质。

#### 值移动

默认情况下，Rust 中的变量绑定遵循*移动语义*。1 当一个值被*移动*时，其所有权转移到新变量，使原始变量无效且不可用。

由于`lines`向量没有实现`[`Copy`](https://doc.rust-lang.org/std/marker/trait.Copy.html)`特质，其值被*移动*，导致`main`中的原始值无效。

#### 值借用

由于`main`中的`lines`变量因*移动*而变得无效，因此任何尝试[*借用*](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html#references-and-borrowing)或引用其值的尝试都是无效的。这就是为什么编译器会生成“移动后在此处借用值”的消息。

> 移动语义
> 
> Rust 的移动语义在编译时检测常见的内存相关错误，如空指针解引用、缓冲区溢出和使用后释放，从而在确保内存安全方面发挥着重要作用。因此，它防止这些错误在运行时发生。

* * *

1.  在 Rust 中有一些例外。例如，大多数原始类型实现了 `Copy` ↩ 特性。
