# 运算符重载

> 原文：[`rust-exercises.com/100-exercises/04_traits/03_operator_overloading.html`](https://rust-exercises.com/100-exercises/04_traits/03_operator_overloading.html)

现在我们对特质有了基本了解，让我们回到**运算符重载**。运算符重载是定义像`+`、`-`、`*`、`/`、`==`、`!=`等运算符自定义行为的特性。

## 运算符是特质

在 Rust 中，运算符是特质。

对于每个运算符，都有一个对应的特质定义了该运算符的行为。通过为你的类型实现该特质，你可以**解锁**使用相应的运算符。

例如，`[`PartialEq` trait](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html)`定义了`==`和`!=`运算符的行为：

```rs
// The `PartialEq` trait definition, from Rust's standard library
// (It is *slightly* simplified, for now)
pub trait PartialEq {
    // Required method
    //
    // `Self` is a Rust keyword that stands for 
    // "the type that is implementing the trait"
    fn eq(&self, other: &Self) -> bool;

    // Provided method
    fn ne(&self, other: &Self) -> bool { ... }
}
```

当你写`x == y`时，编译器会寻找`x`和`y`类型的`PartialEq`特质的实现，并将`x == y`替换为`x.eq(y)`。这是一种语法糖！

这是主要运算符的对应关系：

| 运算符 | 特质 |
| --- | --- |
| `+` | [`Add`](https://doc.rust-lang.org/std/ops/trait.Add.html) |
| `-` | [`Sub`](https://doc.rust-lang.org/std/ops/trait.Sub.html) |
| `*` | [`Mul`](https://doc.rust-lang.org/std/ops/trait.Mul.html) |
| `/` | [`Div`](https://doc.rust-lang.org/std/ops/trait.Div.html) |
| `%` | [`Rem`](https://doc.rust-lang.org/std/ops/trait.Rem.html) |
| `==`和`!=` | [`PartialEq`](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html) |
| `<`, `>`, `<=`, 和 `>=` | [`PartialOrd`](https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html) |

算术运算符位于`[`std::ops`](https://doc.rust-lang.org/std/ops/index.html)模块中，而比较运算符位于`[`std::cmp`](https://doc.rust-lang.org/std/cmp/index.html)模块中。

## 默认实现

`PartialEq::ne`的注释说明"`ne`是一个提供的方法"。

这意味着`PartialEq`在特质定义中为`ne`提供了**默认实现**——定义片段中的省略的`{ ... }`块。

如果你展开省略的块，它看起来像这样：

```rs
pub trait PartialEq {
    fn eq(&self, other: &Self) -> bool;

    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}
```

这正是你所期望的：`ne`是`eq`的否定。

由于提供了默认实现，当你为你的类型实现`PartialEq`时，可以跳过实现`ne`。只需要实现`eq`即可。

```rs
struct WrappingU8 {
    inner: u8,
}

impl PartialEq for WrappingU8 {
    fn eq(&self, other: &WrappingU8) -> bool {
        self.inner == other.inner
    }

    // No `ne` implementation here
}
```

虽然你不必使用默认实现，但你可以选择在实现特质时覆盖它：

```rs
struct MyType;

impl PartialEq for MyType {
    fn eq(&self, other: &MyType) -> bool {
        // Custom implementation
    }

    fn ne(&self, other: &MyType) -> bool {
        // Custom implementation
    }
}
```

## 练习

本节练习位于`[`04_traits/03_operator_overloading`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/03_operator_overloading)
