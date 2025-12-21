# 选项

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/option.html`](https://freddiehaddad.github.io/fast-track-to-rust/option.html)

`Option` 类型表示一个可选值，它可以是一个带有值的 `Some`，或者是一个 `None`。在 Rust 中它们很常见，并且服务于各种目的。选项通常与模式匹配（即 `match` 表达式）一起使用。`Option` 的文档（[`Option`](https://doc.rust-lang.org/std/option/)）提供了关于其使用的详细信息。

`Some(T)` 和 `None` 是 `Option<T>` 枚举的两种变体。^([1)]

```rs
pub enum Option<T> {
    None,
    Some(T),
}
```

> 我们还没有讨论 [泛型](https://doc.rust-lang.org/rust-by-example/generics.html#generics)。现在，只需注意 `enum` 中的 `T` 代表任何类型。

## 回到我们的循环

在代码片段中，我们检查模式是否是当前行的子串。如果是，我们返回一个包含行号（`i+1`）和 `line` 的元组，这些内容被封装在 `Option` 枚举的 `Some` 变体中。如果不是，我们返回 `None` 变体。

```rs
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
```

* * *

1.  Rust 中的 `[enum](https://doc.rust-lang.org/std/keyword.enum.html)` 与其他编译语言（如 C）中的类似，但它们有重要的区别，这使得它们更加强大。↩

1.  回想一下，grep 使用基于 1 的行编号。`enumerate` 从 0 开始。↩
