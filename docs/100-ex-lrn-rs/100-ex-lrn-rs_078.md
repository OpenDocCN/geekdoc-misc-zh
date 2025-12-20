# 泄露数据

> 原文：[`rust-exercises.com/100-exercises/07_threads/03_leak.html`](https://rust-exercises.com/100-exercises/07_threads/03_leak.html)

关于向生成的线程传递引用的主要担忧是使用后释放（use-after-free）错误：使用指向已释放/已重新分配的内存区域的指针访问数据。

如果你正在处理堆分配的数据，你可以通过告诉 Rust 你永远不会回收该内存来避免这个问题：你选择**泄露内存**，故意为之。

这可以通过使用 Rust 标准库中的 `Box::leak` 方法来完成：

```rs
// Allocate a `u32` on the heap, by wrapping it in a `Box`.
let x = Box::new(41u32);
// Tell Rust that you'll never free that heap allocation
// using `Box::leak`. You can thus get back a 'static reference.
let static_ref: &'static mut u32 = Box::leak(x);
```

## 数据泄露是进程范围内的

泄露数据是危险的：如果你持续泄露内存，最终你会耗尽内存并因内存不足错误而崩溃。

```rs
// If you leave this running for a while, 
// it'll eventually use all the available memory.
fn oom_trigger() {
    loop {
        let v: Vec<usize> = Vec::with_capacity(1024);
        v.leak();
    }
}
```

同时，通过 `leak` 方法泄露的内存并不是真正被遗忘的。

操作系统可以将每个内存区域映射到负责它的进程。当进程退出时，操作系统将回收该内存。

考虑到这一点，当以下情况发生时，泄露内存可能是可以接受的：

+   你需要泄露的内存量是有限的/事先已知的，或者

+   你的进程是短暂的，并且你确信在它退出之前不会耗尽所有可用内存

如果你的用例允许，"让操作系统处理它"是一个完全有效的内存管理策略。

## 练习

本节的练习位于[`07_threads/03_leak`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/07_threads/03_leak)
