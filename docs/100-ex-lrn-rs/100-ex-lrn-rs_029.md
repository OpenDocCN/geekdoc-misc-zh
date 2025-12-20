# 实现特性

> 原文：[`rust-exercises.com/100-exercises/04_traits/02_orphan_rule.html`](https://rust-exercises.com/100-exercises/04_traits/02_orphan_rule.html)

当类型定义在另一个包中（例如，`u32` 来自 Rust 的标准库）时，你无法直接为其定义新方法。如果你尝试：

```rs
impl u32 {
    fn is_even(&self) -> bool {
        self % 2 == 0
    }
}
```

编译器将报错：

```rs
error[E0390]: cannot define inherent `impl` for primitive types
  |
1 | impl u32 {
  | ^^^^^^^^
  |
  = help: consider using an extension trait instead 
```

## 扩展特性

**扩展特性** 是一个主要目的是为外部类型附加新方法的特性，例如 `u32`。这正是你在上一个练习中采用的模式，通过定义 `IsEven` 特性并为其实现 `i32` 和 `u32`，然后只要 `IsEven` 在作用域内，你就可以自由地调用这些类型上的 `is_even` 方法。

```rs
// Bring the trait in scope
use my_library::IsEven;

fn main() {
    // Invoke its method on a type that implements it
    if 4.is_even() {
        // [...]
    }
}
```

## 单一实现

你可以编写的特性实现有限制。

最简单、最直接的一个：你无法在一个包中为同一类型实现相同的特性两次。

例如：

```rs
trait IsEven {
    fn is_even(&self) -> bool;
}

impl IsEven for u32 {
    fn is_even(&self) -> bool {
        true
    }
}

impl IsEven for u32 {
    fn is_even(&self) -> bool {
        false
    }
}
```

编译器将拒绝它：

```rs
error[E0119]: conflicting implementations of trait `IsEven` for type `u32`
   |
5  | impl IsEven for u32 {
   | ------------------- first implementation here
...
11 | impl IsEven for u32 {
   | ^^^^^^^^^^^^^^^^^^^ conflicting implementation for `u32` 
```

当在 `u32` 值上调用 `IsEven::is_even` 时，不能对应该使用哪个特性实现产生歧义，因此只能有一个。

## 孤儿规则

当涉及多个包时，情况会更加复杂。特别是，以下至少有一个必须是真实的：

+   特性定义在当前包中

+   实现类型定义在当前包中

这被称为 Rust 的 **孤儿规则**。其目标是使方法解析过程无歧义。

想象以下情况：

+   `A` 包定义了 `IsEven` 特性

+   包 `B` 为 `u32` 实现 `IsEven`

+   包 `C` 为 `u32` 提供了 `IsEven` 特性的（不同）实现

+   包 `D` 依赖于 `B` 和 `C` 并调用 `1.is_even()`

应该使用哪个实现？`B` 中定义的？还是 `C` 中定义的？

没有好的答案，因此定义了孤儿规则来防止这种情况。多亏了孤儿规则，包 `B` 和包 `C` 都无法编译。

## 进一步阅读

+   如上所述，孤儿规则有一些注意事项和例外。如果你想了解其细微差别，请查看[参考](https://doc.rust-lang.org/reference/items/implementations.html#trait-implementation-coherence)。

## 练习

本节练习位于[`04_traits/02_orphan_rule`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/02_orphan_rule)
