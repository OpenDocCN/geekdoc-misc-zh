# 作用域线程

> 原文：[`rust-exercises.com/100-exercises/07_threads/04_scoped_threads.html`](https://rust-exercises.com/100-exercises/07_threads/04_scoped_threads.html)

我们迄今为止讨论的所有生命周期问题都有一个共同的原因：派生线程可能会比其父线程存活得更久。

我们可以通过使用**作用域线程**来规避这个问题。

```rs
let v = vec![1, 2, 3];
let midpoint = v.len() / 2;

std::thread::scope(|scope| {
    scope.spawn(|| {
        let first = &v[..midpoint];
        println!("Here's the first half of v: {first:?}");
    });
    scope.spawn(|| {
        let second = &v[midpoint..];
        println!("Here's the second half of v: {second:?}");
    });
});

println!("Here's v: {v:?}");
```

让我们分析一下正在发生的事情。

## `scope`

`std::thread::scope`函数创建一个新的**作用域**。

`std::thread::scope`接受一个闭包作为输入，它有一个单一参数：一个`Scope`实例。

## 作用域派生

`Scope`暴露了一个`spawn`方法。

与`std::thread::spawn`不同，使用`Scope`派生的所有线程在作用域结束时都会**自动连接**。

如果我们要将前面的示例“翻译”成`std::thread::spawn`，它看起来会是这样：

```rs
let v = vec![1, 2, 3];
let midpoint = v.len() / 2;

let handle1 = std::thread::spawn(|| {
    let first = &v[..midpoint];
    println!("Here's the first half of v: {first:?}");
});
let handle2 = std::thread::spawn(|| {
    let second = &v[midpoint..];
    println!("Here's the second half of v: {second:?}");
});

handle1.join().unwrap();
handle2.join().unwrap();

println!("Here's v: {v:?}");
```

## 从环境中借用

尽管翻译后的示例无法编译：编译器会抱怨`&v`不能从我们的派生线程中使用，因为它的生命周期不是`'static'`。

这不是`std::thread::scope`的问题——你可以**安全地从环境中借用**。

在我们的例子中，`v`是在派生点之前创建的。它只会在`scope`返回后才会被丢弃。同时，`scope`内部派生的所有线程都保证在`scope`返回之前完成，因此不存在悬垂引用的风险。

编译器不会抱怨！

## 练习

本节练习位于[`07_threads/04_scoped_threads`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/07_threads/04_scoped_threads)
