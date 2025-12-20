# 泛型和关联类型

> 原文：[`rust-exercises.com/100-exercises/04_traits/10_assoc_vs_generic.html`](https://rust-exercises.com/100-exercises/04_traits/10_assoc_vs_generic.html)

让我们重新审视我们之前研究的两个特性的定义，`From` 和 `Deref`：

```rs
pub trait From<T> {
    fn from(value: T) -> Self;
}

pub trait Deref {
    type Target;

    fn deref(&self) -> &Self::Target;
}
```

它们都具有类型参数。

在 `From` 的情况下，它是一个泛型参数，`T`。

在 `Deref` 的情况下，它是一个关联类型，`Target`。

它们有什么区别？为什么使用一个而不是另一个？

## 最多一个实现

由于解引用强制转换的工作方式，给定类型只能有一个“目标”类型。例如，`String` 只能解引用到 `str`。这是为了避免歧义：如果你可以为类型实现多次 `Deref`，当你调用一个 `&self` 方法时，编译器应该选择哪个 `Target` 类型？

正因如此，`Deref` 使用了一个关联类型，`Target`。

关联类型是由 **特性实现** 唯一确定的。由于你不能为 `Deref` 实现多次，因此你只能为给定类型指定一个 `Target`，并且不会存在任何歧义。

## 泛型特性

另一方面，你可以为一个类型实现多次 `From`，**只要输入类型 `T` 是不同的**。例如，你可以使用 `u32` 和 `u16` 作为输入类型为 `WrappingU32` 实现 `From`：

```rs
impl From<u32> for WrappingU32 {
    fn from(value: u32) -> Self {
        WrappingU32 { inner: value }
    }
}

impl From<u16> for WrappingU32 {
    fn from(value: u16) -> Self {
        WrappingU32 { inner: value.into() }
    }
}
```

这之所以有效，是因为 `From<u16>` 和 `From<u32>` 被视为 **不同的特性**。

没有歧义：编译器可以根据要转换的值的类型确定使用哪个实现。

## 案例研究：`Add`

作为结束示例，考虑标准库中的 `Add` 特性：

```rs
pub trait Add<RHS = Self> {
    type Output;

    fn add(self, rhs: RHS) -> Self::Output;
}
```

它使用了两种机制：

+   它有一个泛型参数，`RHS`（右侧），默认为 `Self`

+   它有一个关联类型，`Output`，表示加法的结果类型

### `RHS`

`RHS` 是一个泛型参数，允许添加不同类型的值。

例如，你将在标准库中找到以下两个实现：

```rs
impl Add<u32> for u32 {
    type Output = u32;

    fn add(self, rhs: u32) -> u32 {
      //                      ^^^
      // This could be written as `Self::Output` instead.
      // The compiler doesn't care, as long as the type you
      // specify here matches the type you assigned to `Output` 
      // right above.
      // [...]
    }
}

impl Add<&u32> for u32 {
    type Output = u32;

    fn add(self, rhs: &u32) -> u32 {
        // [...]
    }
}
```

这允许以下代码编译：

```rs
let x = 5u32 + &5u32 + 6u32;
```

因为 `u32` 实现了 `Add<&u32>` 以及 `Add<u32>`。

### `输出`

`Output` 表示加法的结果类型。

我们为什么需要 `Output`？我们不能只使用 `Self` 作为输出，即实现 `Add` 的类型吗？我们可以，但这将限制特性的灵活性。例如，在标准库中，你会找到以下实现：

```rs
impl Add<&u32> for &u32 {
    type Output = u32;

    fn add(self, rhs: &u32) -> u32 {
        // [...]
    }
}
```

它们实现特性的是 `&u32` 类型，但加法的结果是 `u32`。

如果 `add` 必须返回 `Self`，即在这种情况下返回 `&u32`，则提供此实现将是不可能的^(1)。`Output` 允许 `std` 将实现者与返回类型解耦，从而支持这种情况。

另一方面，`Output`不能是一个泛型参数。一旦知道了操作数的类型，操作的结果类型**必须**是唯一确定的。这就是为什么它是关联类型的原因：对于给定的实现者和泛型参数的组合，只有一个`Output`类型。

## 结论

总结一下：

+   当必须为特定的特性实现唯一确定类型时，使用**关联类型**。

+   当你想允许对同一类型的不同输入类型有多个特性实现时，使用**泛型参数**。

## 练习

本节的练习位于[`04_traits/10_assoc_vs_generic`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/10_assoc_vs_generic)

* * *

1.  灵活性通常不是免费的：由于`Output`的存在，特性定义变得更加复杂，实现者必须思考他们想要返回的内容。只有在真正需要这种灵活性时，这种权衡才是合理的。在设计自己的特性时，请记住这一点。↩
