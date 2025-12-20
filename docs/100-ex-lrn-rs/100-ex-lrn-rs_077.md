# 'static

> 原文：[`rust-exercises.com/100-exercises/07_threads/02_static.html`](https://rust-exercises.com/100-exercises/07_threads/02_static.html)

如果您尝试从上一个练习中的向量借用切片，您可能会得到一个类似以下内容的编译器错误：

```rs
error[E0597]: `v` does not live long enough
   |
11 | pub fn sum(v: Vec<i32>) -> i32 {
   |            - binding `v` declared here
...
15 |     let right = &v[split_point..];
   |                  ^ borrowed value does not live long enough
16 |     let left_handle = spawn(move || left.iter().sum::<i32>());
   |                             -------------------------------- 
                     argument requires that `v` is borrowed for `'static`
19 | }
   |  - `v` dropped here while still borrowed 
```

`argument requires that v is borrowed for 'static'，这是什么意思？

`'static` 生命周期是 Rust 中的一个特殊生命周期。

这意味着该值将在整个程序运行期间有效。

## 分离的线程

通过 `thread::spawn` 启动的线程可以**生存期超过**创建它的线程。

例如：

```rs
use std::thread;

fn f() {
    thread::spawn(|| {
        thread::spawn(|| {
            loop {
                thread::sleep(std::time::Duration::from_secs(1));
                println!("Hello from the detached thread!");
            }
        });
    });
}
```

在这个例子中，第一个创建的线程将转而创建一个子线程，该子线程每秒打印一条消息。

然后，第一个线程将完成并退出。当发生这种情况时，其子线程将**继续运行**，直到整个进程运行。

在 Rust 的术语中，我们说子线程已经**生存期超过**了其父线程。

## 静态生命周期

由于创建的线程可以：

+   生存期超过创建它的线程（其父线程）

+   运行直到程序退出

它不得借用任何可能在程序退出之前被丢弃的值；违反此约束会导致使用后释放的漏洞。

这也是为什么 `std::thread::spawn` 的签名要求传递给它的闭包具有 `'static` 生命周期：

```rs
pub fn spawn<F, T>(f: F) -> JoinHandle<T> 
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static
{
    // [..]
}
```

## 静态不仅仅是关于引用

Rust 中的所有值都有生命周期，不仅仅是引用。

特别是，一个拥有其数据类型的类型（如 `Vec` 或 `String`）满足 `'static` 约束：如果您拥有它，您可以在返回创建它的函数后继续使用它，即使您想要的时间更长。

因此，您可以解释 `'static` 为一种表达方式：

+   给我一个拥有值的引用

+   给我一个在整个程序运行期间有效的引用

第一种方法是你在上一个练习中解决问题的方法：通过分配新的向量来保存原始向量的左右部分，然后将它们移动到创建的线程中。

## 静态引用

让我们谈谈第二种情况，在整个程序运行期间有效的引用。

### 静态数据

最常见的情况是引用**静态数据**，例如字符串字面量：

```rs
let s: &'static str = "Hello world!";
```

由于字符串字面量在编译时已知，Rust 将它们存储在可执行文件中，称为**只读数据段**。因此，指向该区域的引用在程序运行期间始终有效；它们满足 `'static` 合同。

## 进一步阅读

+   [数据段](https://en.wikipedia.org/wiki/Data_segment)

## 练习

本节练习位于[07_threads/02_static](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/07_threads/02_static)
