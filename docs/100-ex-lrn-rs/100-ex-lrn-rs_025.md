# 析构函数

> 原文：[`rust-exercises.com/100-exercises/03_ticket_v1/11_destructor.html`](https://rust-exercises.com/100-exercises/03_ticket_v1/11_destructor.html)

当引入堆时，我们提到你需要释放你分配的内存。

当引入借用检查器时，我们也指出在 Rust 中你很少需要直接管理内存。

这两个陈述一开始可能看起来有些矛盾。让我们通过引入**作用域**和**析构函数**来了解它们是如何结合在一起的。

## 作用域

变量的**作用域**是 Rust 代码中该变量有效或**存活**的区域。

变量的作用域从其声明开始。它结束于以下情况之一：

1.  声明变量的块（即 `{}` 之间的代码）结束

    ```rs
    fn main() {
       // `x` is not yet in scope here
       let y = "Hello".to_string();
       let x = "World".to_string(); // <-- x's scope starts here...
       let h = "!".to_string(); //   |
    } //  <-------------- ...and ends here
    ```

1.  变量的所有权被转移给其他人（例如一个函数或另一个变量）

    ```rs
    fn compute(t: String) {
       // Do something [...]
    }

    fn main() {
        let s = "Hello".to_string(); // <-- s's scope starts here...
                    //                    | 
        compute(s); // <------------------- ..and ends here
                    //   because `s` is moved into `compute`
    }
    ```

## 析构函数

当值的所有者超出作用域时，Rust 会调用其**析构函数**。

析构函数试图清理该值使用的资源——特别是它分配的任何内存。

你可以通过将其传递给 `std::mem::drop` 来手动调用值的析构函数。

那就是为什么你经常会听到 Rust 开发者说“那个值已经被**释放**”作为一种方式来表明一个值已经超出作用域并且其析构函数已被调用。

### 可视化掉落点

我们可以插入显式的 `drop` 调用来“说明”编译器为我们做的事情。回到之前的例子：

```rs
fn main() {
   let y = "Hello".to_string();
   let x = "World".to_string();
   let h = "!".to_string();
}
```

它相当于：

```rs
fn main() {
   let y = "Hello".to_string();
   let x = "World".to_string();
   let h = "!".to_string();
   // Variables are dropped in reverse order of declaration
   drop(h);
   drop(x);
   drop(y);
}
```

让我们看看第二个例子，其中 `s` 的所有权被传递给 `compute`：

```rs
fn compute(s: String) {
   // Do something [...]
}

fn main() {
   let s = "Hello".to_string();
   compute(s);
}
```

它相当于这样：

```rs
fn compute(t: String) {
    // Do something [...]
    drop(t); // <-- Assuming `t` wasn't dropped or moved 
             //     before this point, the compiler will call 
             //     `drop` here, when it goes out of scope
}

fn main() {
    let s = "Hello".to_string();
    compute(s);
}
```

注意区别：尽管在 `main` 中调用 `compute` 之后 `s` 就不再有效，但在 `main` 中没有 `drop(s)`。当你将一个值的所有权传递给一个函数时，你也在**转移清理它的责任**。

这确保了值的析构函数最多被调用一次，通过设计防止了[双重释放漏洞](https://owasp.org/www-community/vulnerabilities/Doubly_freeing_memory)。

### 使用释放后

如果你尝试在释放之后使用一个值会发生什么？

```rs
let x = "Hello".to_string();
drop(x);
println!("{}", x);
```

如果你尝试编译此代码，你会得到一个错误：

```rs
error[E0382]: use of moved value: `x`
 --> src/main.rs:4:20
  |
3 |     drop(x);
  |          - value moved here
4 |     println!("{}", x);
  |                    ^ value used here after move
```

Drop **消耗** 被调用时的值，这意味着调用之后该值就不再有效。

编译器将因此阻止你使用它，避免[使用已释放内存的漏洞](https://owasp.org/www-community/vulnerabilities/Using_freed_memory)。

### 释放引用

如果一个变量包含一个引用怎么办？

例如：

```rs
let x = 42i32;
let y = &x;
drop(y);
```

当你调用 `drop(y)`... 没有发生任何事情。

如果你实际上尝试编译此代码，你会得到一个警告：

```rs
warning: calls to `std::mem::drop` with a reference 
         instead of an owned value does nothing
 --> src/main.rs:4:5
  |
4 |     drop(y);
  |     ^^^^^-^
  |          |
  |          argument has type `&i32`
  | 
```

这回到了我们之前所说的：我们只想调用析构函数一次。

你可以对同一个值有多个引用——如果我们在一个引用超出作用域时调用它们指向的值的析构函数，会发生什么？它们会引用一个不再有效的内存位置：所谓的[**悬垂指针**](https://en.wikipedia.org/wiki/Dangling_pointer)，它是[**使用后释放漏洞**](https://owasp.org/www-community/vulnerabilities/Using_freed_memory)的近亲。Rust 的所有权系统通过设计排除了这类漏洞。

## 练习

本节的练习位于[`03_ticket_v1/11_destructor`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/03_ticket_v1/11_destructor)

* * *

1.  Rust 不保证析构函数会运行。例如，如果你明确选择泄露内存，它们就不会运行。↩
