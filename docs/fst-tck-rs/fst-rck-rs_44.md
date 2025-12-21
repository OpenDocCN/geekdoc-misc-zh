# 非作用域线程

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/non-scoped_threads.html`](https://freddiehaddad.github.io/fast-track-to-rust/non-scoped_threads.html)

在我们的 rustle 程序中启用多线程支持的最简单方法是为每个指定的文件启动一个线程，执行我们开发的模式匹配步骤，并使用 fork/join 模式打印结果。如果你有 C++ 背景，你可能首先从探索 [thread](https://doc.rust-lang.org/std/thread/) 模块中的函数开始，发现 [spawn](https://doc.rust-lang.org/stable/std/thread/fn.spawn.html) 函数，然后直接深入。

然而，这种方法是有缺陷的！虽然这可能是一个有价值的学习经验，但它可能会很耗时、令人沮丧且令人困惑。让我们来探讨一下这种方法的一些陷阱，然后探索一个更有效的解决方案。

## `spawn` 函数

这是 `spawn` 函数的签名：

```rs
pub fn spawn<F, T>(f: F) -> JoinHandle<T>
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
```

`spawn` 函数接受一个闭包（`f`）作为参数，为运行闭包启动一个新线程，并返回一个 `JoinHandle`。正如其名所示，`JoinHandle` 提供了一个 `join` 方法来等待派生线程完成。到目前为止，一切顺利。然而，`F` 和返回值 `T` 上的 `'static`^(1) 约束，正如诗人所说，是问题的关键所在。

`'static` 约束要求闭包及其返回值必须在整个程序执行期间存活。这是必要的，因为线程可能会比创建它们的上下文存活得更久。

如果一个线程及其返回值可以比调用者存活得更久，我们需要确保它们在之后仍然有效。由于我们 *无法* 预测线程何时完成，它们必须一直有效到程序结束。因此，需要 `'static` 生命周期。

> 如果这个概念仍然不清楚，不要担心；这是 Rust 中最具挑战性的方面之一，许多开发者一开始都发现很难理解。

让我们通过一个简单的程序来更好地理解这些概念。审查以下代码片段，然后运行程序。

```rs
fn main() {
    use std::thread;

    let error = 0373; // Compiler error E0373

    let handler = thread::spawn(|| {
        println!("{error}");
    });

    handler.join().unwrap();
}
```

这个简单的程序看起来完全有效。那么为什么 Rust 编译器会抱怨那些在其他大多数语言中运行无问题的代码？即使在这个例子中不是这样，从更一般的角度来看，`main` 中创建的派生线程可能会比创建它的线程存活得更久。因为闭包借用了 `error` 值，父线程可能会超出作用域，导致 `error` 值被丢弃，使引用无效。因为编译器 *无法* 知道这会不会发生，所以我们看到了错误：

> error[E0373](https://doc.rust-lang.org/stable/error_codes/E0373.html): 闭包可能超出当前函数的生命周期，但它借用 `error`，而 `error` 是当前函数所拥有的

编译器确实提供了一个在某些情况下可能有效的解决方案：

> help: 要强制闭包获取 `error`（以及任何其他引用的变量）的所有权，请使用 `[`move`](https://doc.rust-lang.org/std/keyword.move.html) ^(2) 关键字

让我们看看这样做会发生什么：

```rs
fn main() {
    use std::thread;

    let error = 0373; // Compiler error E0373

    let handler = thread::spawn(move || {
        println!("{error}");
    });

    handler.join().unwrap();
}
```

回顾我们关于 *拷贝语义* 的讨论，这可能就是为什么它有效的原因。值被 *拷贝* 到新线程的作用域中，使其独立于原始值并解决了生命周期问题。变量现在保证与线程的寿命相同。这对于原始类型和实现了 `Copy` 特质的类型来说工作得很好。但如果拷贝是一个昂贵的操作，或者对象不能被拷贝怎么办？这导致开发者学习 Rust 时经常面临的下一个挑战：如果我们需要启动额外的线程，而这些线程也需要访问相同的变量，会发生什么？

例如，考虑以下情况：

```rs
fn main() {
    use std::thread;

    let error = String::from("E0373"); // Compiler error E0373

    let handler1 = thread::spawn(move || {
        println!("{error}");
    });

    let handler2 = thread::spawn(move || {
        println!("{error}");
    });

    handler1.join().unwrap();
    handler2.join().unwrap();
}
```

虽然这些严格的规则可能看起来令人畏惧，尤其是在较大的程序中，但它们是 Rust 的 [无惧并发](https://doc.rust-lang.org/book/ch16-00-concurrency.html#fearless-concurrency) 目标的基础。这些规则确保了程序中的并发既安全又高效。

现在我们已经了解了为什么在许多其他语言中工作得很好的传统 fork/join 模型在 Rust 中很可能会失败，让我们来探讨如何正确实现这种方法！

* * *

1.  生命周期是另一种泛型。然而，它们不是确保类型具有期望的行为，而是确保引用在期望的持续时间内保持有效。 ↩

1.  `move` 将任何通过引用或可变引用捕获的变量转换为通过值捕获的变量。 ↩
