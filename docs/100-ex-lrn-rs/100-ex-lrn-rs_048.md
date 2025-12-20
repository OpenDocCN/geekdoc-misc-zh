# 可靠性

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/06_fallibility.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/06_fallibility.html)

让我们回顾一下之前练习中的`Ticket::new`函数：

```rs
impl Ticket {
    pub fn new(
        title: String, 
        description: String, 
        status: Status
    ) -> Ticket {
        if title.is_empty() {
            panic!("Title cannot be empty");
        }
        if title.len() > 50 {
            panic!("Title cannot be longer than 50 bytes");
        }
        if description.is_empty() {
            panic!("Description cannot be empty");
        }
        if description.len() > 500 {
            panic!("Description cannot be longer than 500 bytes");
        }

        Ticket {
            title,
            description,
            status,
        }
    }
}
```

一旦其中一个检查失败，函数就会恐慌。这并不理想，因为它没有给调用者处理错误的机会。

是时候介绍`Result`类型了，这是 Rust 处理错误的主要机制。

## `Result`类型

`Result`类型是在标准库中定义的一个枚举：

```rs
enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

它有两个变体：

+   `Ok(T)`: 表示一个成功的运算。它包含`T`，即运算的输出。

+   `Err(E)`: 表示一个失败的运算。它包含`E`，即发生的错误。

`Ok`和`Err`都是泛型，允许你为成功和错误情况指定自己的类型。

## 无异常

Rust 中的可恢复错误**表示为值**。

它们只是类型的一个实例，像任何其他值一样被传递和处理。这与 Python 或 C#等其他语言不同，在这些语言中，**异常**用于表示错误。

异常创建了一个单独的控制流路径，这可能很难理解。

仅通过查看函数的签名，你不知道它是否会抛出异常。你也不知道，仅通过查看函数的签名，**它**可以抛出哪些异常类型。

你必须阅读函数的文档或查看其实现，才能找出答案。

异常处理逻辑的局部性非常差：抛出异常的代码与捕获它的代码相距甚远，两者之间没有直接的联系。

## 可靠性编码在类型系统中

Rust 通过`Result`强制你在函数的签名中**编码可靠性**。

如果一个函数可能会失败（并且你希望调用者有机会处理错误），它必须返回一个`Result`。

```rs
// Just by looking at the signature, you know that this function 
// can fail. You can also inspect `ParseIntError` to see what 
// kind of failures to expect.
fn parse_int(s: &str) -> Result<i32, ParseIntError> {
    // ...
}
```

这就是`Result`的大优点：它使可靠性明确。

请记住，恐慌确实存在。它们不像其他语言中的异常那样由类型系统跟踪。但它们是为了**不可恢复的错误**而设计的，应该谨慎使用。

## 练习

本节练习位于[`05_ticket_v2/06_fallibility`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/06_fallibility)
