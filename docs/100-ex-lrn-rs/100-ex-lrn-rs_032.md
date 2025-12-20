# 特性界限

> 原文：[`rust-exercises.com/100-exercises/04_traits/05_trait_bounds.html`](https://rust-exercises.com/100-exercises/04_traits/05_trait_bounds.html)

到目前为止，我们已经看到了特性的两种用法：

+   解锁“内置”行为（例如，运算符重载）

+   向现有类型添加新行为（即扩展特性）

还有一个第三种用法：**泛型编程**。

## 问题

我们到目前为止的所有函数和方法，都是与**具体类型**一起工作的。

操作具体类型的代码通常易于编写和理解。但它也限制了其可重用性。

让我们假设，例如，我们想要编写一个函数，如果整数是偶数则返回`true`。使用具体类型，我们必须为每个我们想要支持的整数类型编写一个单独的函数：

```rs
fn is_even_i32(n: i32) -> bool {
    n % 2 == 0
}

fn is_even_i64(n: i64) -> bool {
    n % 2 == 0
}

// Etc.
```

或者，我们也可以编写一个单一的扩展特性，然后为每个整数类型编写不同的实现：

```rs
trait IsEven {
    fn is_even(&self) -> bool;
}

impl IsEven for i32 {
    fn is_even(&self) -> bool {
        self % 2 == 0
    }
}

impl IsEven for i64 {
    fn is_even(&self) -> bool {
        self % 2 == 0
    }
}

// Etc.
```

重复仍然存在。

## 泛型编程

我们可以使用**泛型**做得更好。

泛型允许我们编写与**类型参数**一起工作的代码，而不是具体类型：

```rs
fn print_if_even<T>(n: T)
where
    T: IsEven + Debug
{
    if n.is_even() {
        println!("{n:?} is even");
    }
}
```

`print_if_even`是一个**泛型函数**。

它与特定输入类型无关。相反，它与任何类型`T`一起工作，该类型：

+   实现`IsEven`特性。

+   实现`Debug`特性。

此合同用**特性界限**表示：`T: IsEven + Debug`。

`+`符号用于要求`T`实现多个特性。`T: IsEven + Debug`等价于“`T`实现`IsEven`**并且**`Debug`”。

## 特性界限

特性界限在`print_if_even`中有什么作用？

为了找出原因，让我们尝试移除它们：

```rs
fn print_if_even<T>(n: T) {
    if n.is_even() {
        println!("{n:?} is even");
    }
}
```

以下代码无法编译：

```rs
error[E0599]: no method named `is_even` found for type parameter `T` 
              in the current scope
 --> src/lib.rs:2:10
  |
1 | fn print_if_even<T>(n: T) {
  |                  - method `is_even` not found 
  |                    for this type parameter
2 |     if n.is_even() {
  |          ^^^^^^^ method not found in `T`

error[E0277]: `T` doesn't implement `Debug`
 --> src/lib.rs:3:19
  |
3 |         println!("{n:?} is even");
  |                   ^^^^^ 
  |   `T` cannot be formatted using `{:?}` because 
  |         it doesn't implement `Debug`
  |
help: consider restricting type parameter `T`
  |
1 | fn print_if_even<T: std::fmt::Debug>(n: T) {
  |                   +++++++++++++++++ 
```

没有特性界限，编译器不知道`T`**能做什么**。

它不知道`T`有一个`is_even`方法，也不知道如何格式化`T`以进行打印。从编译器的角度来看，裸`T`没有任何行为。

特性界限通过确保函数体所需的行为存在来限制可以使用的类型集。

## 语法：内联特性界限

上述所有示例都使用了**`where`子句**来指定特性界限：

```rs
fn print_if_even<T>(n: T)
where
    T: IsEven + Debug
//  ^^^^^^^^^^^^^^^^^
//  This is a `where` clause
{
    // [...]
}
```

如果特性界限简单，可以直接在类型参数旁边**内联**它们：

```rs
fn print_if_even<T: IsEven + Debug>(n: T) {
    //           ^^^^^^^^^^^^^^^^^
    //           This is an inline trait bound
    // [...]
}
```

## 语法：有意义的名称

在上述示例中，我们使用了`T`作为类型参数名称。当一个函数只有一个类型参数时，这是一个常见的约定。

虽然没有阻止你使用更有意义的名称：

```rs
fn print_if_even<Number: IsEven + Debug>(n: Number) {
    // [...]
}
```

实际上，当存在多个类型参数或名称`T`不足以传达类型在函数中的作用时，**使用有意义的名称**是**可取的**。在命名类型参数时，确保清晰和可读性，就像命名变量或函数参数一样。尽管如此，请遵循 Rust 的约定：使用[大驼峰命名法为类型参数命名](https://rust-lang.github.io/api-guidelines/naming.html#casing-conforms-to-rfc-430-c-case)。

## 函数签名是王

你可能会想知道为什么我们真的需要特性界限。编译器不能从函数体中推断出所需的特性吗？

它可以，但不会。

理由与函数参数上的显式类型注解相同：每个函数签名都是调用者和被调用者之间的合同，条款必须明确声明。这允许提供更好的错误信息、更好的文档、减少版本间的意外破坏，并加快编译时间。

## 练习

本节的练习位于[`04_traits/05_trait_bounds`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/05_trait_bounds)
