# 控制流程

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/control_flow.html`](https://freddiehaddad.github.io/fast-track-to-rust/control_flow.html)

Rust 中用于控制程序流程的一些常见方法包括：

+   [`if`](https://doc.rust-lang.org/reference/expressions/if-expr.html#if-expressions) 和 [`if let`](https://doc.rust-lang.org/reference/expressions/if-expr.html#if-let-expressions) 表达式

+   [循环表达式](https://doc.rust-lang.org/reference/expressions/loop-expr.html)

+   [`match` 表达式](https://doc.rust-lang.org/reference/expressions/match-expr.html)

这些方法帮助你管理执行流程，使你的代码更高效、更易读。

我们将使用`for`循环遍历诗中的所有行，检查每一行是否包含由`pattern`指定的子串。每一行将使用`match`表达式进行评估。

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

    for line in poem.lines() {
        match line.contains(pattern) {
            true => println!("{line}"),
            false => (),
        }
    }
}
```

## `for` 循环

`for`循环的语法应该看起来很熟悉。然而，在这一行发生了一些有趣的事情。注意方法调用`poem.lines()`。你可能认为诗是一个字符串字面量。它怎么能有方法呢？好吧，正如你所猜测的，以及之前提到的，字符串切片不仅仅是字符串字面量。我们将更详细地探讨它们，所以请记住这一点。

循环的目的非常明确：它遍历诗中的每一行。

## `match` 表达式

你可能已经猜到了，但`match`表达式与`if`表达式类似，因为它在代码执行中引入了一个分支。然而，它有一个非常强大的功能：当使用时，编译器确保所有可能的[*scrutinee*](https://doc.rust-lang.org/reference/glossary.html#scrutinee)结果都被覆盖。这个方面保证了[`match`表达式](https://doc.rust-lang.org/reference/expressions/match-expr.html)中所有情况都被处理。

让我们确保我们完全理解这一点。在代码片段中，通过在行 16 前加上`//`来注释掉它，然后运行代码。

> 友好的编译器错误
> 
> 抽时间来欣赏一下这个编译器错误是多么的有帮助。Rust 编译器真的是你的朋友！

```rs
 Compiling playground v0.0.1 (/playground)
error[E0004]: non-exhaustive patterns: `false` not covered
  --> src/main.rs:14:15
   |
14 |         match line.contains(pattern) {
   |               ^^^^^^^^^^^^^^^^^^^^^^ pattern `false` not covered
   |
   = note: the matched value is of type `bool`
help: ensure that all possible cases are being handled by adding a match arm with a
   |  wildcard pattern or an explicit pattern as shown
   |
15 ~             true => println!("{line}"),
16 ~             false => todo!(),
   |

For more information about this error, try `rustc --explain E0004`.
error: could not compile `playground` (bin "playground") due to 1 previous error 
```

编译器错误信息正在通知你：

+   `contains`方法返回一个布尔值。

+   没有涵盖`false`情况。

+   Rust 编译器可以通过`rustc --explain E0004`提供更多信息。

让我们看看 Rust 编译器会说什么：

```rs
$ rustc --explain E0004
This error indicates that the compiler cannot guarantee a matching pattern for
one or more possible inputs to a match expression. Guaranteed matches are
required in order to assign values to match expressions, or alternatively,
determine the flow of execution.

Erroneous code example:

enum Terminator {
    HastaLaVistaBaby,
    TalkToMyHand,
}

let x = Terminator::HastaLaVistaBaby;

match x { // error: non-exhaustive patterns: `HastaLaVistaBaby` not covered
    Terminator::TalkToMyHand => {}
}

If you encounter this error you must alter your patterns so that every possible
value of the input type is matched. For types with a small number of variants
(like enums) you should probably cover all cases explicitly. Alternatively, the
underscore `_` wildcard pattern can be added after all other patterns to match
"anything else". Example:

enum Terminator {
    HastaLaVistaBaby,
    TalkToMyHand,
}

let x = Terminator::HastaLaVistaBaby;

match x {
    Terminator::TalkToMyHand => {}
    Terminator::HastaLaVistaBaby => {}
}

// or:

match x {
    Terminator::TalkToMyHand => {}
    _ => {}
}
```

`match`分支具有以下结构：

```rs
match VALUE {
    PATTERN => EXPRESSION,
    PATTERN => EXPRESSION,
    PATTERN => EXPRESSION,
} 
```

## ()` 单元类型

在我们不想执行任何操作的情况下，例如在`false`分支中，我们可以使用空单元类型`()`。随着课程的进行，我们将进一步探讨这一点。

# 摘要

在本节中，我们：

+   探索了`for`循环表达式。

+   检查了`match`表达式。

+   学习了 Rust 编译器如何提供有用的错误信息。

+   介绍了空单元类型`()`。

# 练习

+   将 `match` 表达式替换为 `if` 表达式。

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

    for line in poem.lines() {
        if line.contains(pattern) {
            println!("{line}");
        }
    }
}
```</details>

# 下一页

如果需要，请休息一下，然后我们继续！
