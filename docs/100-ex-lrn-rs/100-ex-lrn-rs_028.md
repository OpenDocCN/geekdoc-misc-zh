# 特性

> 原文：[`rust-exercises.com/100-exercises/04_traits/01_trait.html`](https://rust-exercises.com/100-exercises/04_traits/01_trait.html)

让我们再次看看我们的 `Ticket` 类型：

```rs
pub struct Ticket {
    title: String,
    description: String,
    status: String,
}
```

到目前为止，我们所有的测试都使用了 `Ticket` 的字段进行断言。

```rs
assert_eq!(ticket.title(), "A new title");
```

如果我们想直接比较两个 `Ticket` 实例呢？

```rs
let ticket1 = Ticket::new(/* ... */);
let ticket2 = Ticket::new(/* ... */);
ticket1 == ticket2
```

编译器会阻止我们：

```rs
error[E0369]: binary operation `==` cannot be applied to type `Ticket`
  --> src/main.rs:18:13
   |
18 |     ticket1 == ticket2
   |     ------- ^^ ------- Ticket
   |     |
   |     Ticket
   |
note: an implementation of `PartialEq` might be missing for `Ticket` 
```

`Ticket` 是一个新类型。默认情况下，它 **没有任何行为附加**。

Rust 并不会神奇地推断如何比较两个包含 `String` 的 `Ticket` 实例。

尽管如此，Rust 编译器正在引导我们走向正确的方向：它建议我们可能遗漏了 `PartialEq` 的实现。`PartialEq` 是一个 **特性**！

## 特性是什么？

特性是 Rust 定义 **接口** 的方式。

特性定义了一组方法，类型必须实现这些方法以满足特性的契约。

### 定义特性

特性定义的语法如下所示：

```rs
trait <TraitName> {
    fn <method_name>(<parameters>) -> <return_type>;
}
```

例如，我们可以定义一个名为 `MaybeZero` 的特性，要求其实现者定义一个 `is_zero` 方法：

```rs
trait MaybeZero {
    fn is_zero(self) -> bool;
}
```

### 实现特性

要为类型实现特性，我们使用 `impl` 关键字，就像我们为常规方法做的那样，但语法略有不同：

```rs
impl <TraitName> for <TypeName> {
    fn <method_name>(<parameters>) -> <return_type> {
        // Method body
    }
}
```

例如，为了为自定义数字类型 `WrappingU32` 实现 `MaybeZero` 特性：

```rs
pub struct WrappingU32 {
    inner: u32,
}

impl MaybeZero for WrappingU32 {
    fn is_zero(self) -> bool {
        self.inner == 0
    }
}
```

### 调用特性方法

要调用特性方法，我们使用 `.` 操作符，就像我们使用常规方法一样：

```rs
let x = WrappingU32 { inner: 5 };
assert!(!x.is_zero());
```

要调用特性方法，必须满足两个条件：

+   类型必须实现该特性。

+   特性必须在作用域内。

为了满足后者，你可能需要添加一个 `use` 语句来引用特性：

```rs
use crate::MaybeZero;
```

如果以下条件之一成立，则不需要这样做：

+   该特性定义在调用发生时的相同模块中。

+   特性定义在标准库的 **预置** 中。预置是一组特性类型，它们被自动导入到每个 Rust 程序中。这就像在每个 Rust 模块的开头添加了 `use std::prelude::*;`。

你可以在 [Rust 文档](https://doc.rust-lang.org/std/prelude/index.html) 中找到特性和类型的列表。

## 练习

本节练习位于 `04_traits/01_trait` 中 [练习](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/01_trait)

* * *

1.  直接在类型上定义的方法，而不使用特性，也称为 **固有方法**。 ↩
