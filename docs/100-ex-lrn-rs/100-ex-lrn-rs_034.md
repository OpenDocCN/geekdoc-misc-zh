# Deref 特质

> 原文：[`rust-exercises.com/100-exercises/04_traits/07_deref.html`](https://rust-exercises.com/100-exercises/04_traits/07_deref.html)

在上一个练习中，你不需要做太多，对吧？

改变

```rs
impl Ticket {
    pub fn title(&self) -> &String {
        &self.title
    }
}
```

to

```rs
impl Ticket {
    pub fn title(&self) -> &str {
        &self.title
    }
}
```

是你为了让代码编译并通过测试所需要做的全部。不过，你心里可能应该响起一些警钟。

## 它不应该工作，但它确实工作了

让我们回顾一下事实：

+   `self.title` 是一个 `String`

+   因此，`&self.title` 是一个 `&String`

+   （修改后的）`title` 方法的输出是 `&str`

你会期望编译器错误，不是吗？`Expected &String, found &str` 或类似的内容。然而，它只是正常工作。**为什么**？

## `Deref` to the rescue

`Deref` 特质是语言特性 [**deref coercion**](https://doc.rust-lang.org/std/ops/trait.Deref.html#deref-coercion) 背后的机制。

特质是在标准库中定义的，位于 `std::ops` 模块中：

```rs
// I've slightly simplified the definition for now.
// We'll see the full definition later on.
pub trait Deref {
    type Target;

    fn deref(&self) -> &Self::Target;
}
```

`type Target` 是一个 **关联类型**。

它是一个占位符，用于在实现特质时必须指定的具体类型。

## Deref coercion

通过为类型 `T` 实现 `Deref<Target = U>`，你告诉编译器 `&T` 和 `&U` 在某种程度上是可以互换的。

尤其是你将获得以下行为：

+   对 `T` 的引用会隐式转换为对 `U` 的引用（即 `&T` 变为 `&U`）

+   你可以调用 `&T` 上定义的所有接受 `&self` 作为输入的方法。

关于解引用运算符 `*`，还有一件事，但我们现在还不需要它（如果你好奇，请参阅 `std` 的文档）。

## `String` 实现 `Deref`

`String` 使用 `Target = str` 实现 `Deref`。

```rs
impl Deref for String {
    type Target = str;

    fn deref(&self) -> &str {
        // [...]
    }
}
```

多亏了这个实现和 deref coercion，当需要时，`&String` 会自动转换为 `&str`。

## 不要滥用 deref coercion

Deref coercion 是一个强大的功能，但它可能导致混淆。

自动转换类型可能会使代码更难阅读和理解。如果 `T` 和 `U` 上都定义了具有相同名称的方法，哪个会被调用？

我们将在课程中稍后探讨 deref coercion 的“最安全”的使用案例：智能指针。

## 练习

本节的练习位于[`04_traits/07_deref`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/07_deref)
