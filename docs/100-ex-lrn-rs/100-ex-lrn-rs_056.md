# Error::source

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/14_source.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/14_source.html)

为了完成对 `Error` 特质的覆盖，我们还需要讨论一件事：`source` 方法。

```rs
// Full definition this time!
pub trait Error: Debug + Display {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}
```

`source` 方法是一种访问**错误原因**的方式，如果有的话。

错误通常链式传递，意味着一个错误是另一个错误的原因：您有一个高级错误（例如，无法连接到数据库），它是由一个低级错误（例如，无法解析数据库主机名）引起的。`source` 方法允许您“遍历”完整的错误链，通常用于在日志中捕获错误上下文。

## 实现 `source`

`Error` 特质提供了一个默认实现，该实现始终返回 `None`（即没有底层原因）。这就是为什么在前面的练习中您不必关心 `source`。

您可以覆盖此默认实现，为您的错误类型提供一个原因。

```rs
use std::error::Error;

#[derive(Debug)]
struct DatabaseError {
    source: std::io::Error
}

impl std::fmt::Display for DatabaseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Failed to connect to the database")
    }
}

impl std::error::Error for DatabaseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.source)
    }
}
```

在这个例子中，`DatabaseError` 将 `std::io::Error` 作为其来源包装起来。然后我们覆盖 `source` 方法，在调用时返回此来源。

## `(dyn Error + 'static)`

这 `&(dyn Error + 'static)` 类型是什么？

让我们分解它：

+   `dyn Error` 是一个**特质对象**。它是一种引用实现 `Error` 特质的任何类型的方式。

+   `'static` 是一个特殊的**生命周期指定符**。`'static` 意味着引用在“我们需要它的时候”有效，即整个程序执行期间。

结合：`&(dyn Error + 'static)` 是一个指向实现 `Error` 特质且在整个程序执行期间有效的特质对象的引用。

目前不必过分担心这些概念。我们将在未来的章节中更详细地介绍它们。

## 使用 `thiserror` 实现 `source`

`thiserror` 为您的错误类型提供了三种自动实现 `source` 的方式：

+   命名为 `source` 的字段将自动用作错误的来源。

    ```rs
    use thiserror::Error;

    #[derive(Error, Debug)]
    pub enum MyError {
        #[error("Failed to connect to the database")]
        DatabaseError {
            source: std::io::Error
        }
    }
    ```

+   带有 `#[source]` 属性的字段将自动用作错误的来源。

    ```rs
    use thiserror::Error;

    #[derive(Error, Debug)]
    pub enum MyError {
        #[error("Failed to connect to the database")]
        DatabaseError {
            #[source]
            inner: std::io::Error
        }
    }
    ```

+   带有 `#[from]` 属性的字段将自动用作错误的来源，并且 `thiserror` 将自动生成一个 `From` 实现来将注解类型转换为您的错误类型。

    ```rs
    use thiserror::Error;

    #[derive(Error, Debug)]
    pub enum MyError {
        #[error("Failed to connect to the database")]
        DatabaseError {
            #[from]
            inner: std::io::Error
        }
    }
    ```

## `?` 操作符

`?` 操作符是传播错误的简写。

当用于返回 `Result` 的函数时，如果 `Result` 是 `Err`，它将提前返回错误。

例如：

```rs
use std::fs::File;

fn read_file() -> Result<String, std::io::Error> {
    let mut file = File::open("file.txt")?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}
```

等价于：

```rs
use std::fs::File;

fn read_file() -> Result<String, std::io::Error> {
    let mut file = match File::open("file.txt") {
        Ok(file) => file,
        Err(e) => {
            return Err(e);
        }
    };
    let mut contents = String::new();
    match file.read_to_string(&mut contents) {
        Ok(_) => (),
        Err(e) => {
            return Err(e);
        }
    }
    Ok(contents)
}
```

您可以使用 `?` 操作符显著缩短错误处理代码。

特别是，`?` 操作符将自动将可疑操作的错误类型转换为函数的错误类型，如果可能进行转换（即如果存在合适的 `From` 实现）。

## 练习

本节练习位于[`05_ticket_v2/14_source`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/14_source)
