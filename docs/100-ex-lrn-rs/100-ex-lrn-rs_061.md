# 调整大小

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/03_resizing.html`](https://rust-exercises.com/100-exercises/06_ticket_management/03_resizing.html)

我们说`Vec`是一种“可增长”的向量类型，但这究竟意味着什么？如果你试图向已达到最大容量的`Vec`中插入一个元素会发生什么？

```rs
let mut numbers = Vec::with_capacity(3);
numbers.push(1);
numbers.push(2);
numbers.push(3); // Max capacity reached
numbers.push(4); // What happens here?
```

`Vec`将**自动调整大小**。

它将向分配器请求一个新的（更大的）堆内存块，复制元素，并释放旧内存。

这个操作可能很昂贵，因为它涉及到新的内存分配和复制所有现有元素。

## Vec::with_capacity

如果你有一个大致的元素数量存储在`Vec`中的概念，你可以使用`Vec::with_capacity`方法预先分配足够的内存。

这可以在`Vec`增长时避免新的分配，但如果你高估了实际的使用量，可能会浪费内存。

需要逐个案例进行评估。

## 练习

本节练习位于[`06_ticket_management/03_resizing`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/03_resizing)
