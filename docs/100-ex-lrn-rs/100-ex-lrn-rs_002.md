# 语法

> 原文：[`rust-exercises.com/100-exercises/01_intro/01_syntax.html`](https://rust-exercises.com/100-exercises/01_intro/01_syntax.html)

不要急于求成！

在开始这一部分之前，请完成上一部分的练习。

它位于 `exercises/01_intro/00_welcome`，在 [课程 GitHub 仓库](https://github.com/mainmatter/100-exercises-to-learn-rust) 中。

使用 `wr`（/100-exercises/01_intro/00_welcome#wr-the-workshop-runner）开始课程并验证你的解决方案。

之前的任务甚至不算是练习，但它已经让你接触到了相当多的 Rust **语法**。我们不会涵盖之前练习中使用的 Rust 语法的每一个细节。相反，我们将只涵盖 *足够多* 的内容，以便在不陷入细节的情况下继续前进。

一步一步来！

## 注释

你可以使用 `//` 进行单行注释：

```rs
// This is a single-line comment
// Followed by another single-line comment
```

## 函数

Rust 中的函数使用 `fn` 关键字定义，后跟函数名称、输入参数和返回类型。函数体被大括号 `{}` 包围。

在之前的练习中，你看到了 `greeting` 函数：

```rs
// `fn` <function_name> ( <input params> ) -> <return_type> { <body> }
fn greeting() -> &'static str {
    // TODO: fix me 👇
    "I'm ready to __!"
}
```

`greeting` 没有输入参数，并返回一个字符串切片的引用 (`&'static str`)。

### 返回类型

如果函数不返回任何内容（即返回 Rust 的单元类型 `()`），则可以省略返回类型。这就是 `test_welcome` 函数的情况：

```rs
fn test_welcome() {
    assert_eq!(greeting(), "I'm ready to learn Rust!");
}
```

上面的代码等同于：

```rs
// Spelling out the unit return type explicitly
//                   👇
fn test_welcome() -> () {
    assert_eq!(greeting(), "I'm ready to learn Rust!");
}
```

### 返回值

函数中的最后一个表达式会隐式返回：

```rs
fn greeting() -> &'static str {
    // This is the last expression in the function
    // Therefore its value is returned by `greeting`
    "I'm ready to learn Rust!"
}
```

你也可以使用 `return` 关键字来提前返回一个值：

```rs
fn greeting() -> &'static str {
    // Notice the semicolon at the end of the line!
    return "I'm ready to learn Rust!";
}
```

在可能的情况下省略 `return` 关键字被认为是惯用的。

### 输入参数

输入参数在函数名称后面的圆括号 `()` 内声明。

每个参数都通过其名称、冒号 `:` 和其类型来声明。

例如，下面的 `greet` 函数接受一个类型为 `&str`（“字符串切片”）的 `name` 参数：

```rs
// An input parameter
//        👇
fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}
```

如果有多个输入参数，它们必须用逗号分隔。

### 类型注解

由于我们已经多次提到“类型”，让我们明确指出：Rust 是一种 **静态类型语言**。

Rust 中的每个值都有一个类型，并且这个类型必须在编译时为编译器所知。

类型是一种 **静态分析** 的形式。

你可以将类型视为编译器附加到程序中每个值的 **标签**。根据标签，编译器可以强制执行不同的规则——例如，你不能将字符串加到数字上，但你可以将两个数字相加。如果正确利用，类型可以防止整个类别的运行时错误。

## 练习

本节的练习位于 [01_intro/01_syntax](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/01_intro/01_syntax)
