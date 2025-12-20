# 线程

> 原文：[`rust-exercises.com/100-exercises/07_threads/01_threads.html`](https://rust-exercises.com/100-exercises/07_threads/01_threads.html)

在我们开始编写多线程代码之前，让我们退一步，谈谈线程是什么以及为什么我们可能想要使用它们。

## 什么是线程？

**线程**是由底层操作系统管理的执行上下文。

每个线程都有自己的栈和指令指针。

一个**进程**可以管理多个线程。这些线程共享相同的内存空间，这意味着它们可以访问相同的数据。

线程是一个**逻辑**结构。最终，你只能在 CPU 核心上同时运行一组指令，这是**物理**执行单元。

由于线程的数量可能比 CPU 核心的数量多得多，因此操作系统的**调度器**负责在任何给定时间决定运行哪个线程，在它们之间分配 CPU 时间以最大化吞吐量和响应性。

## `main`

当 Rust 程序启动时，它在一个单独的线程上运行，即**主线程**。

这个线程是由操作系统创建的，负责运行`main`函数。

```rs
use std::thread;
use std::time::Duration;

fn main() {
    loop {
        thread::sleep(Duration::from_secs(2));
        println!("Hello from the main thread!");
    }
}
```

## `std::thread`

Rust 的标准库提供了一个模块，`std::thread`，允许你创建和管理线程。

### `spawn`

你可以使用`std::thread::spawn`来创建新线程并在它们上执行代码。

例如：

```rs
use std::thread;
use std::time::Duration;

fn main() {
    let handle = thread::spawn(|| {
        loop {
            thread::sleep(Duration::from_secs(1));
            println!("Hello from a thread!");
        }
    });

    loop {
        thread::sleep(Duration::from_secs(2));
        println!("Hello from the main thread!");
    }
}
```

如果你在这个程序上执行[Rust playground](https://play.rust-lang.org/?version=stable&mode=debug&edition=2021&gist=afedf7062298ca8f5a248bc551062eaa)中，你会看到主线程和生成的线程是并发运行的。

每个线程独立于其他线程进行进度。

### 进程终止

当主线程完成时，整个进程将退出。

生成的线程将继续运行，直到完成或主线程完成。

```rs
use std::thread;
use std::time::Duration;

fn main() {
    let handle = thread::spawn(|| {
        loop {
            thread::sleep(Duration::from_secs(1));
            println!("Hello from a thread!");
        }
    });

    thread::sleep(Duration::from_secs(5));
}
```

在上面的例子中，你可以预期看到“Hello from a thread!”的消息大约打印五次。

然后，主线程将完成（当`sleep`调用返回时），生成的线程将被终止，因为整个进程退出。

### `join`

你也可以通过在`spawn`返回的`JoinHandle`上调用`join`方法来等待生成的线程完成。

```rs
use std::thread;
fn main() {
    let handle = thread::spawn(|| {
        println!("Hello from a thread!");
    });

    handle.join().unwrap();
}
```

在这个例子中，主线程将在退出之前等待生成的线程完成。

这在两个线程之间引入了一种**同步**形式：你保证在程序退出之前会看到“Hello from a thread!”的消息打印出来，因为主线程不会退出，直到生成的线程完成。

## 练习

本节练习位于[`07_threads/01_threads`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/07_threads/01_threads)
