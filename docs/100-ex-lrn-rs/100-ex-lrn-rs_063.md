# .iter()

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/05_iter.html`](https://rust-exercises.com/100-exercises/06_ticket_management/05_iter.html)

`IntoIterator`会**消耗**`self`来创建迭代器。

这有其好处：你可以从迭代器中获得**所有者**值。例如：如果你在`Vec<Ticket>`上调用`.into_iter()`，你会得到一个返回`Ticket`值的迭代器。

这也是它的缺点：在调用`.into_iter()`之后，你不能再使用原始集合。很多时候，你想要遍历一个集合而不消耗它，查看**值的引用**。在`Vec<Ticket>`的情况下，你想要遍历`&Ticket`值。

大多数集合都提供了一个名为`.iter()`的方法，它返回一个遍历集合元素引用的迭代器。例如：

```rs
let numbers: Vec<u32> = vec![1, 2];
// `n` has type `&u32` here
for n in numbers.iter() {
    // [...]
}
```

通过为**集合的引用**实现`IntoIterator`，可以简化这种模式。在我们的例子中，那将是`&Vec<Ticket>`。

标准库就是这样做的，这就是为什么以下代码可以工作：

```rs
let numbers: Vec<u32> = vec![1, 2];
// `n` has type `&u32` here
// We didn't have to call `.iter()` explicitly
// It was enough to use `&numbers` in the `for` loop
for n in &numbers {
    // [...]
}
```

提供这两种选项是惯用的：

+   集合引用的`IntoIterator`实现。

+   `.iter()`方法返回一个遍历集合元素的引用迭代器。

前者适用于`for`循环，后者更明确，可以在其他上下文中使用。

## 练习

本节练习位于[`06_ticket_management/05_iter`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/05_iter)
