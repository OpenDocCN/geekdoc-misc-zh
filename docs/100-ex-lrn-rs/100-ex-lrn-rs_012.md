# 情况化行为

> 原文：[`rust-exercises.com/100-exercises/02_basic_calculator/09_saturating.html`](https://rust-exercises.com/100-exercises/02_basic_calculator/09_saturating.html)

`overflow-checks` 是一个粗糙的工具：它是一个全局设置，影响整个程序。

通常情况下，你可能希望根据上下文以不同的方式处理整数溢出：有时环绕是正确的选择，而其他时候恐慌更可取。

## 环绕方法

你可以通过使用 `wrapping_` 方法来逐个操作选择进入环绕算术^(1)。

例如，你可以使用 `wrapping_add` 来进行带环绕的整数加法：

```rs
let x = 255u8;
let y = 1u8;
let sum = x.wrapping_add(y);
assert_eq!(sum, 0);
```

## 饱和方法

或者，你可以通过使用 `saturating_` 方法选择进入**饱和算术**。

与环绕不同，饱和算术将返回整数类型的最大或最小值。例如：

```rs
let x = 255u8;
let y = 1u8;
let sum = x.saturating_add(y);
assert_eq!(sum, 255);
```

由于 `255 + 1` 是 `256`，这比 `u8::MAX` 大，所以结果是 `u8::MAX`（255）。

对于下溢，情况相反：`0 - 1` 是 `-1`，这比 `u8::MIN` 小，所以结果是 `u8::MIN`（0）。

你不能通过 `overflow-checks` 配置文件设置获得饱和算术——你必须在进行算术操作时明确选择进入。

## 练习

本节练习位于 `02_basic_calculator/09_saturating`。[链接](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/02_basic_calculator/09_saturating)

* * *

1.  你可以将方法视为“附加”到特定类型上的函数。我们将在下一章中介绍方法（以及如何定义它们）。↩
