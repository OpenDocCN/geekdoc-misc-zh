# 向量

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/02_vec.html`](https://rust-exercises.com/100-exercises/06_ticket_management/02_vec.html)

数组的优点也是其缺点：它们的尺寸必须在编译时预先知道。如果您尝试创建一个在运行时才知道大小的数组，您将得到编译错误：

```rs
let n = 10;
let numbers: [u32; n];
```

```rs
error[E0435]: attempt to use a non-constant value in a constant
 --> src/main.rs:3:20
  |
2 | let n = 10;
3 | let numbers: [u32; n];
  |                    ^ non-constant value 
```

对于我们的票务管理系统，数组不起作用——我们在编译时不知道需要存储多少张票。这就是`Vec`发挥作用的地方。

## `Vec`

`Vec`是由标准库提供的一个可增长数组类型。

您可以使用`Vec::new`函数创建一个空数组：

```rs
let mut numbers: Vec<u32> = Vec::new();
```

然后您可以使用`push`方法将元素推入向量：

```rs
numbers.push(1);
numbers.push(2);
numbers.push(3);
```

向量末尾添加新值。

如果您在创建时知道值，您还可以使用`vec!`宏创建一个初始化的向量：

```rs
let numbers = vec![1, 2, 3];
```

## 访问元素

访问元素的语法与数组相同：

```rs
let numbers = vec![1, 2, 3];
let first = numbers[0];
let second = numbers[1];
let third = numbers[2];
```

索引必须是`usize`类型。

您还可以使用`get`方法，它返回一个`Option<&T>`：

```rs
let numbers = vec![1, 2, 3];
assert_eq!(numbers.get(0), Some(&1));
// You get a `None` if you try to access an out-of-bounds index
// rather than a panic.
assert_eq!(numbers.get(3), None);
```

访问是边界检查的，就像使用数组访问元素一样。它具有 O(1)的复杂度。

## 内存布局

`Vec`是一个堆分配的数据结构。

当您创建一个`Vec`时，它会在堆上分配内存以存储元素。

如果您运行以下代码：

```rs
let mut numbers = Vec::with_capacity(3);
numbers.push(1);
numbers.push(2);
```

您将得到以下内存布局：

```rs
 +---------+--------+----------+
Stack | pointer | length | capacity | 
      |  |      |   2    |    3     |
      +--|------+--------+----------+
         |
         |
         v
       +---+---+---+
Heap:  | 1 | 2 | ? |
       +---+---+---+ 
```

`Vec`跟踪三件事：

+   您在堆上预留区域的**指针**。

+   向量的**长度**，即向量中有多少个元素。

+   向量的**容量**，即可以放入在堆上预留空间中的元素数量。

这种布局应该很熟悉：它与`String`完全相同！

这不是巧合：`String`在底层被定义为字节的向量，`Vec<u8>`：

```rs
pub struct String {
    vec: Vec<u8>,
}
```

## 练习

本节练习位于[`06_ticket_management/02_vec`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/02_vec)
