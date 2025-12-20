# 迭代

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/04_iterators.html`](https://rust-exercises.com/100-exercises/06_ticket_management/04_iterators.html)

在最初的练习中，你学习了 Rust 允许你使用 `for` 循环遍历集合。那时我们正在查看范围（例如 `0..5`），但对于数组、向量等集合也同样适用。

```rs
// It works for `Vec`s
let v = vec![1, 2, 3];
for n in v {
    println!("{}", n);
}

// It also works for arrays
let a: [u32; 3] = [1, 2, 3];
for n in a {
    println!("{}", n);
}
```

是时候了解这是如何在底层工作的了。

## `for` desugaring

每次你在 Rust 中编写一个 `for` 循环时，编译器都会将其 `desugar` 成以下代码：

```rs
let mut iter = IntoIterator::into_iter(v);
loop {
    match iter.next() {
        Some(n) => {
            println!("{}", n);
        }
        None => break,
    }
}
```

`loop` 是另一种循环结构，位于 `for` 和 `while` 之上。

一个 `loop` 块将无限运行，除非你显式地 `break` 出来。

## `Iterator` 特性

上一段代码片段中的 `next` 方法来自 `Iterator` 特性。`Iterator` 特性在 Rust 的标准库中定义，并为可以产生一系列值的类型提供了一个共享接口：

```rs
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}
```

与 `Item` 关联的类型指定了迭代器产生的值的类型。

`next` 返回序列中的下一个值。

如果有要返回的值，则返回 `Some(value)`，如果没有，则返回 `None`。

小心：当迭代器返回 `None` 时，并不能保证迭代器已经耗尽。只有当迭代器实现了（更严格的）[`FusedIterator`](https://doc.rust-lang.org/std/iter/trait.FusedIterator.html) 特性时，这一点才有保证。

## `IntoIterator` 特性

并非所有类型都实现了 `Iterator`，但许多类型可以被转换为实现了该接口的类型。

正是 `IntoIterator` 特性在这里发挥作用：

```rs
trait IntoIterator {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;
    fn into_iter(self) -> Self::IntoIter;
}
```

`into_iter` 方法会消耗原始值，并返回其元素的迭代器。

一个类型只能有一个 `IntoIterator` 的实现：不能有关于 `for` 应该 `desugar` 到什么的歧义。

一个细节：每个实现了 `Iterator` 的类型也会自动实现 `IntoIterator`，它们只是从 `into_iter` 返回自身！

## 边界检查

遍历迭代器有一个很好的副作用：你无法越界，这是设计上的。

这允许 Rust 从生成的机器代码中移除边界检查，从而加快迭代速度。

换句话说，

```rs
let v = vec![1, 2, 3];
for n in v {
    println!("{}", n);
}
```

通常比

```rs
let v = vec![1, 2, 3];
for i in 0..v.len() {
    println!("{}", v[i]);
}
```

有例外：编译器有时可以证明你即使使用手动索引也不会越界，从而取消边界检查。但通常，在可能的情况下，更喜欢迭代而不是索引。

## 练习

本节练习位于[`06_ticket_management/04_iterators`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/04_iterators)
