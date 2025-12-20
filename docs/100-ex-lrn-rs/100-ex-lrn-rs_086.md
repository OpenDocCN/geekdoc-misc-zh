# 锁、Send 和 Arc

> 原文：[`rust-exercises.com/100-exercises/07_threads/11_locks.html`](https://rust-exercises.com/100-exercises/07_threads/11_locks.html)

你刚才实现的补丁策略有一个主要的缺点：它是竞态的。

如果两个客户端几乎同时为同一票据发送补丁，服务器将按任意顺序应用它们。最后入队的补丁将覆盖其他客户端所做的更改。

## 版本号

我们可以通过使用**版本号**来尝试解决这个问题。

每个票据在创建时都会分配一个版本号，设置为`0`。

每当客户端发送一个补丁时，他们必须包括票据的当前版本号以及期望的更改。服务器只有在版本号匹配它存储的版本号时才会应用补丁。

在上述场景中，服务器将拒绝第二个补丁，因为版本号已经被第一个补丁递增，因此不会与第二个客户端发送的版本号匹配。

这种方法在分布式系统中相当常见（例如，当客户端和服务器不共享内存时），并且被称为**乐观并发控制**。

理念是，大多数时候不会发生冲突，因此我们可以针对常见情况进行优化。现在你对 Rust 已经足够了解，如果你愿意，可以将这种策略作为附加练习自己实现。

## 锁定

我们也可以通过引入一个**锁**来修复竞争条件。

每当客户端想要更新一个票据时，他们必须首先获取对该票据的锁。在锁处于活动状态时，其他客户端无法修改票据。

Rust 的标准库提供了两种不同的锁定原语：`Mutex<T>`和`RwLock<T>`。

让我们从`Mutex<T>`开始。它代表**mut**ual **ex**clusion，并且是最简单的锁类型：它只允许一个线程访问数据，无论它是读取还是写入。

`Mutex<T>`包裹它所保护的数据，因此它对数据类型是泛型的。

你不能直接访问数据：类型系统强制你首先使用`Mutex::lock`或`Mutex::try_lock`获取锁。前者在获取锁之前会阻塞，后者如果无法获取锁，会立即返回错误。

这两种方法都返回一个保护对象，该对象可以解引用到数据，允许你修改它。当保护对象被丢弃时，锁被释放。

```rs
use std::sync::Mutex;

// An integer protected by a mutex lock
let lock = Mutex::new(0);

// Acquire a lock on the mutex
let mut guard = lock.lock().unwrap();

// Modify the data through the guard,
// leveraging its `Deref` implementation
*guard += 1;

// The lock is released when `data` goes out of scope
// This can be done explicitly by dropping the guard
// or happen implicitly when the guard goes out of scope
drop(guard)
```

## 锁定粒度

我们应该将`Mutex`包裹什么？

最简单的方法是将整个`TicketStore`包裹在一个单独的`Mutex`中。

这将有效，但会严重限制系统的性能：你将无法并行读取票据，因为每次读取都必须等待锁被释放。

这被称为**粗粒度锁定**。

使用**细粒度锁定**会更好，其中每个票据都由其自己的锁保护。这样，只要客户端没有尝试访问相同的票据，他们就可以并行地使用票据。

```rs
// The new structure, with a lock for each ticket
struct TicketStore {
    tickets: BTreeMap<TicketId, Mutex<Ticket>>,
}
```

这种方法更高效，但有一个缺点：`TicketStore`必须意识到系统的多线程特性；到目前为止，`TicketStore`一直幸福地忽略了线程的存在。

让我们无论如何尝试一下。

## 谁持有锁？

为了使整个方案工作，锁必须传递给想要修改票据的客户端。

客户端可以直接修改票据（就像他们有一个`&mut Ticket`一样），并在完成后释放锁。

这有点棘手。

我们不能通过通道发送一个`Mutex<Ticket>`，因为`Mutex`不是`Clone`的，而且我们不能将它从`TicketStore`中移出。我们能否发送`MutexGuard`代替？

让我们用一个小的例子来测试这个想法：

```rs
use std::thread::spawn;
use std::sync::Mutex;
use std::sync::mpsc::sync_channel;

fn main() {
    let lock = Mutex::new(0);
    let (sender, receiver) = sync_channel(1);
    let guard = lock.lock().unwrap();

    spawn(move || {
        receiver.recv().unwrap();
    });

    // Try to send the guard over the channel
    // to another thread
    sender.send(guard);
}
```

编译器对这个代码不满意：

```rs
error[E0277]: `MutexGuard<'_, i32>` cannot be sent between 
              threads safely
   --> src/main.rs:10:7
    |
10  |   spawn(move || {
    |  _-----_^
    | | |
    | | required by a bound introduced by this call
11  | |     receiver.recv().unwrap();
12  | | });
    | |_^ `MutexGuard<'_, i32>` cannot be sent between threads safely
    |
    = help: the trait `Send` is not implemented for 
            `MutexGuard<'_, i32>`, which is required by 
            `{closure@src/main.rs:10:7: 10:14}: Send`
    = note: required for `Receiver<MutexGuard<'_, i32>>` 
            to implement `Send`
note: required because it's used within this closure 
```

`MutexGuard<'_, i32>`不是`Send`：这意味着什么？

## `Send`

`Send`是一个标记特质，表示一个类型可以安全地从一条线程转移到另一条线程。

`Send`也是一个自动特质，就像`Sized`一样；编译器根据其定义自动实现（或不实现）你的类型的`Send`。

你也可以为你的类型手动实现`Send`，但这需要`unsafe`，因为你必须保证类型确实可以在线程之间安全地发送，这是编译器无法自动验证的原因。

### 通道要求

`Sender<T>`, `SyncSender<T>`和`Receiver<T>`只有在`T`是`Send`时才是`Send`。

这是因为它们被用来在线程之间发送值，如果值本身不是`Send`，那么在线程之间发送它是不安全的。

### `MutexGuard`

`MutexGuard`不是`Send`，因为`Mutex`使用的底层操作系统原语来实现锁（在某些平台上）要求锁必须由获取它的同一个线程释放。

如果我们将`MutexGuard`发送到另一个线程，锁将由不同的线程释放，这会导致未定义的行为。

## 我们的挑战

总结一下：

+   我们不能通过通道发送一个`MutexGuard`。因此，我们不能在服务器端加锁，然后在客户端修改票据。

+   我们可以发送一个`Mutex`通过通道，因为只要它保护的数据是`Send`，它就是`Send`，对于`Ticket`来说就是这样。同时，我们既不能将`Mutex`从`TicketStore`中移出，也不能克隆它。

我们如何解决这个问题？

我们需要从不同的角度看待这个问题。要锁定`Mutex`，我们不需要拥有值。共享引用就足够了，因为`Mutex`使用内部可变性：

```rs
impl<T> Mutex<T> {
    // `&self`, not `self`!
    pub fn lock(&self) -> LockResult<MutexGuard<'_, T>> {
        // Implementation details
    }
}
```

因此，发送给客户端的共享引用就足够了。

我们不能直接这样做，因为引用必须是`'static`的，而这并不是情况。

从某种意义上说，我们需要一个“所有者共享引用”。结果发现，Rust 有一个符合这个要求的类型：`Arc`。

## 救命之`Arc`

`Arc`代表**原子引用计数**。

`Arc`围绕一个值并跟踪该值存在的引用数量。当最后一个引用被丢弃时，该值将被释放。

被`Arc`包裹的值是不可变的：你只能获取对其的共享引用。

```rs
use std::sync::Arc;

let data: Arc<u32> = Arc::new(0);
let data_clone = Arc::clone(&data);

// `Arc<T>` implements `Deref<T>`, so can convert 
// a `&Arc<T>` to a `&T` using deref coercion
let data_ref: &u32 = &data;
```

如果你感到似曾相识，你是对的：`Arc`听起来非常类似于我们在讨论内部可变性时引入的引用计数指针`Rc`。区别在于线程安全性：`Rc`不是`Send`，而`Arc`是。这归结于引用计数实现的方式：`Rc`使用一个“普通”整数，而`Arc`使用一个**原子**整数，它可以在线程之间安全地共享和修改。

## Arc<Mutex<T>>

如果我们将`Arc`与`Mutex`搭配使用，我们最终得到一个类型：

+   可以在线程之间传递，因为：

    +   如果`T`是`Send`，则`Arc`是`Send`，

    +   `Mutex`是`Send`如果`T`是`Send`。

    +   `T`是`Ticket`，它是`Send`。

+   可以被克隆，因为无论`T`是什么，`Arc`都是`Clone`。克隆一个`Arc`会增加引用计数，数据不会被复制。

+   可以用来修改它所包裹的数据，因为`Arc`允许你获取对`Mutex<T>`的共享引用，这反过来又可以用来获取锁。

我们已经拥有了实现票务存储锁定策略所需的所有组件。

## 进一步阅读

+   在本课程中，我们不会涵盖原子操作的细节，但你可以在[std 文档](https://doc.rust-lang.org/std/sync/atomic/index.html)以及["Rust 原子操作与锁"书籍](https://marabos.nl/atomics/)中找到更多信息。

## 练习

本节练习位于[07_threads/11_locks](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/07_threads/11_locks)
