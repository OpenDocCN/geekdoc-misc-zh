# 转换，第一部分

> 原文：[`rust-exercises.com/100-exercises/02_basic_calculator/10_as_casting.html`](https://rust-exercises.com/100-exercises/02_basic_calculator/10_as_casting.html)

我们反复强调，Rust 不会为整数执行隐式类型转换。

你如何执行**显式**转换呢？

## as

你可以使用`as`运算符在整数类型之间进行转换。

`as`转换是**不可失败的**。

例如：

```rs
let a: u32 = 10;

// Cast `a` into the `u64` type
let b = a as u64;

// You can use `_` as the target type
// if it can be correctly inferred 
// by the compiler. For example:
let c: u64 = a as _;
```

这个转换的语义是你所期望的：所有`u32`值都是有效的`u64`值。

### 截断

如果我们朝相反的方向进行，事情会更有趣：

```rs
// A number that's too big 
// to fit into a `u8`
let a: u16 = 255 + 1;
let b = a as u8;
```

这个程序将正常运行，因为没有问题的，因为`as`转换是**不可失败的**。但`b`的值是多少？当从较大的整数类型转换为较小的类型时，Rust 编译器将执行**截断**。

为了理解发生了什么，让我们首先看看`256u16`在内存中是如何表示的，作为一个位序列：

```rs
 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0
|               |               |
+---------------+---------------+
  First 8 bits    Last 8 bits 
```

当转换为`u8`时，Rust 编译器将保留`u16`内存表示的最后 8 位。

```rs
 0 0 0 0 0 0 0 0 
|               |
+---------------+
  Last 8 bits 
```

因此`256 as u8`等于`0`。这在大多数情况下都不是理想的。

事实上，如果 Rust 编译器看到你尝试将字面量值转换为会导致截断的类型，它会主动尝试阻止你：

```rs
error: literal out of range for `i8`
  |
4 |     let a = 255 as i8;
  |             ^^^
  |
  = note: the literal `255` does not fit into the type `i8` 
          whose range is `-128..=127`
  = help: consider using the type `u8` instead
  = note: `#[deny(overflowing_literals)]` on by default 
```

### 推荐

作为一项经验法则，对`as`转换要非常小心。

仅**专门**用于从较小的类型转换为较大的类型。要从较大的整数类型转换为较小的类型，请依赖我们将在课程后面探索的*可失败*转换机制。

### 限制

令人惊讶的行为并不是`as`转换的唯一缺点。它也相当有限：你只能依赖`as`转换进行原始类型和一些其他特殊情况的转换。

当处理复合类型时，你必须依赖不同的转换机制（可失败和不可失败），我们将在后面探讨。

## 进一步阅读

+   查阅[Rust 的官方参考](https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast)以了解`as`转换对每个源/目标组合的精确行为，以及允许转换的详尽列表。

## 练习

本节的练习位于[`02_basic_calculator/10_as_casting`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/02_basic_calculator/10_as_casting)
