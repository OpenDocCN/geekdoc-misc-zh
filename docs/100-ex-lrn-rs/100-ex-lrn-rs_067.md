# 参数位置的`impl Trait`

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/09_impl_trait_2.html`](https://rust-exercises.com/100-exercises/06_ticket_management/09_impl_trait_2.html)

在上一节中，我们看到了如何使用`impl Trait`来返回一个类型而不指定其名称。

相同的语法也可以用于**参数位置**：

```rs
fn print_iter(iter: impl Iterator<Item = i32>) {
    for i in iter {
        println!("{}", i);
    }
}
```

`print_iter`函数接受一个`i32`类型的迭代器并打印每个元素。

当用于**参数位置**时，`impl Trait`相当于一个带有特质的泛型参数：

```rs
fn print_iter<T>(iter: T) 
where
    T: Iterator<Item = i32>
{
    for i in iter {
        println!("{}", i);
    }
}
```

## 缺点

作为一条经验法则，在参数位置上优先使用泛型而不是`impl Trait`。

泛型允许调用者显式指定参数的类型，使用涡轮鱼语法（`::<>`），这在消除歧义时可能很有用。而`impl Trait`则不是这样。

## 练习

本节的练习位于[`06_ticket_management/09_impl_trait_2`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/09_impl_trait_2)
