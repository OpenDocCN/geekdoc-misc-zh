# 解包

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/07_unwrap.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/07_unwrap.html)

`Ticket::new`现在返回一个`Result`而不是在无效输入时恐慌。

这对调用者意味着什么？

## 失败不能（隐式地）被忽视

与异常不同，Rust 的`Result`强制你在**调用位置处理错误**。

如果你调用一个返回`Result`的函数，Rust 不会允许你隐式忽略错误情况。

```rs
fn parse_int(s: &str) -> Result<i32, ParseIntError> {
    // ...
}

// This won't compile: we're not handling the error case.
// We must either use `match` or one of the combinators provided by 
// `Result` to "unwrap" the success value or handle the error.
let number = parse_int("42") + 2;
```

## 你得到了一个`结果`. 现在怎么办？

当你调用一个返回`Result`的函数时，你有两个关键选项：

+   如果操作失败，则恐慌。这可以通过使用`unwrap`或`expect`方法来完成。

    ```rs
    // Panics if `parse_int` returns an `Err`.
    let number = parse_int("42").unwrap();
    // `expect` lets you specify a custom panic message.
    let number = parse_int("42").expect("Failed to parse integer");
    ```

+   使用`match`表达式解构`结果`以显式处理错误情况。

    ```rs
    match parse_int("42") {
        Ok(number) => println!("Parsed number: {}", number),
        Err(err) => eprintln!("Error: {}", err),
    }
    ```

## 练习

本节练习位于[`05_ticket_v2/07_unwrap`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/07_unwrap)
