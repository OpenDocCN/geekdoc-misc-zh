# 错误枚举

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/08_error_enums.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/08_error_enums.html)

你对上一个练习的解决方案可能感觉有些别扭：基于字符串的匹配并不是最佳选择！

同事可能会重新设计`Ticket::new`返回的错误信息（例如，以提高可读性），突然之间，你的调用代码就会崩溃。

你已经知道修复这个问题的工具了：枚举！

## 对错误做出反应

当你想让调用者根据发生的特定错误以不同的方式行为时，你可以使用枚举来表示不同的错误情况：

```rs
// An error enum to represent the different error cases
// that may occur when parsing a `u32` from a string.
enum U32ParseError {
    NotANumber,
    TooLarge,
    Negative,
}
```

使用错误枚举，你将不同的错误情况编码到类型系统中——它们成为易出错函数签名的一部分。

这简化了调用者的错误处理，因为他们可以使用`match`表达式来对不同的错误情况进行响应：

```rs
match s.parse_u32() {
    Ok(n) => n,
    Err(U32ParseError::Negative) => 0,
    Err(U32ParseError::TooLarge) => u32::MAX,
    Err(U32ParseError::NotANumber) => {
        panic!("Not a number: {}", s);
    }
}
```

## 练习

本节的练习位于[`05_ticket_v2/08_error_enums`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/08_error_enums)
