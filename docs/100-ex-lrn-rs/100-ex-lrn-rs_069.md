# 可变切片

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/11_mutable_slices.html`](https://rust-exercises.com/100-exercises/06_ticket_management/11_mutable_slices.html)

每当我们讨论切片类型（如 `str` 和 `[T]`）时，我们都使用了它们的不可变借用形式（`&str` 和 `&[T]`）。

但切片也可以是可变的！

下面是如何创建一个可变切片的方法：

```rs
let mut numbers = vec![1, 2, 3];
let slice: &mut [i32] = &mut numbers;
```

然后，你可以修改切片中的元素：

```rs
slice[0] = 42;
```

这将改变 `Vec` 的第一个元素为 `42`。

## 限制

当处理不可变借用时，建议是明确的：优先选择切片引用而不是对拥有类型的引用（例如，`&[T]` 而不是 `&Vec<T>`）。

对于可变借用来说，情况并非如此。

考虑以下场景：

```rs
let mut numbers = Vec::with_capacity(2);
let mut slice: &mut [i32] = &mut numbers;
slice.push(1);
```

这将无法编译！

`push` 是 `Vec` 的一个方法，而不是切片的方法。这是更普遍原则的体现：Rust 不允许你从切片中添加或删除元素。你只能修改/替换已经存在的元素。

在这方面，`&mut Vec` 或 `&mut String` 与 `&mut [T]` 或 `&mut str` 相比，功能上更为强大。

根据你需要执行的操作选择最合适的类型。

## 练习

本节练习位于[`06_ticket_management/11_mutable_slices`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/11_mutable_slices)
