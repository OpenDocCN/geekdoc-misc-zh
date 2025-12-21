# 作用域线程

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/scoped_threads.html`](https://freddiehaddad.github.io/fast-track-to-rust/scoped_threads.html)

在前一个章节中，我们探讨了`thread`模块中的`spawn`方法，并指出其局限性：它不能借用非`'static`数据，因为编译器无法保证在所有借用值的生命周期之前，所有线程都将被连接。为了解决这个问题，`thread`模块还提供了`[`scope`函数](https://doc.rust-lang.org/stable/std/thread/fn.scope.html)`，它与`[`Scope`](https://doc.rust-lang.org/stable/std/thread/struct.Scope.html)`一起工作。这种组合通过确保在作用域内创建的所有线程在它们创建的函数返回之前自动连接，除非它们之前已被手动连接，从而允许借用非`'static`数据。

## `scope`函数

这里是`[`scope`函数](https://doc.rust-lang.org/stable/std/thread/fn.scope.html)的签名：

```rs
pub fn scope<'env, F, T>(f: F) -> T
where
    F: for<'scope> FnOnce(&'scope Scope<'scope, 'env>) -> T,
```

`scope`函数接受一个闭包（`f`）作为参数，该闭包接收一个`Scope`对象（由`scope`创建）。这个`Scope`对象允许使用`[`spawn`](https://doc.rust-lang.org/stable/std/thread/struct.Scope.html#method.spawn)方法来创建线程。`spawn`方法返回一个`[`ScopedJoinHandle`](https://doc.rust-lang.org/stable/std/thread/struct.ScopedJoinHandle.html)，正如其名称所暗示的，提供了一个`[`join`](https://doc.rust-lang.org/stable/std/thread/struct.ScopedJoinHandle.html#method.join)方法来等待创建的线程完成。

作用域线程涉及两个生命周期：`'scope`和`'env`：

+   `'env`：这是一个生命周期参数，表示`Scope`可以借用（即作用域外部的数据）的环境数据的生命周期。它确保任何对环境数据的引用都超出作用域的生命周期。

+   `'scope`：这是另一个生命周期参数，表示作用域本身的生命周期。这是在此期间可以创建和运行新的作用域线程的时期。它确保在生命周期结束时，任何正在运行的线程都被连接。

用简单的话说，`scope`函数接受一个闭包`f`，它可以借用具有特定生命周期`'env`的数据，并确保在函数返回之前，作用域内创建的所有线程都被连接。

让我们回顾一下前一个章节中未能编译的一个示例，以更好地理解这些概念。请审查以下代码片段，然后运行程序。

```rs
fn main() {
    use std::thread;

    let error = String::from("E0373"); // Compiler error E0373

    thread::scope(|s| {
        let handler = s.spawn(|| {
            println!("{error}");
        });

        s.spawn(|| {
            println!("{error}");
        });

        handler.join().unwrap(); // Manually join the first thread

        // Second thread is automatically joined when the closure returns.
    });
}
```

通过这些所有权和类型系统工具，可以保证在`scope`内创建的所有线程在它们的生命周期结束时都会被连接。这允许 Rust 编译器确定所有借用数据（在这种情况下，是`error` `String`）在线程的生命周期内保持有效。这就是 Rust 将许多运行时错误转换为编译时错误的方式。这样的概念有助于在 Rust 中实现无畏的并发！
