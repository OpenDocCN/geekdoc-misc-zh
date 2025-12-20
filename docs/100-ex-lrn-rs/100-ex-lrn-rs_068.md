# 切片

> 原文：[`rust-exercises.com/100-exercises/06_ticket_management/10_slices.html`](https://rust-exercises.com/100-exercises/06_ticket_management/10_slices.html)

让我们回到`Vec`的内存布局：

```rs
let mut numbers = Vec::with_capacity(3);
numbers.push(1);
numbers.push(2);
```

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

我们已经提到过，`String`实际上是一个伪装成`Vec<u8>`的结构。

这种相似性可能会让你问：“`Vec`的`&str`等价物是什么？”

## [`&[T]`](#t)

`[T]`是类型`T`的连续元素序列的**切片**。

它最常见的形式是借用形式，即`&[T]`。

有多种方法可以从`Vec`创建切片引用：

```rs
let numbers = vec![1, 2, 3];
// Via index syntax
let slice: &[i32] = &numbers[..];
// Via a method
let slice: &[i32] = numbers.as_slice();
// Or for a subset of the elements
let slice: &[i32] = &numbers[1..];
```

`Vec`通过使用`[T]`作为目标类型实现了`Deref`特质，因此你可以直接在`Vec`上使用切片方法，这得益于解引用强制转换：

```rs
let numbers = vec![1, 2, 3];
// Surprise, surprise: `iter` is not a method on `Vec`!
// It's a method on `&[T]`, but you can call it on a `Vec` 
// thanks to deref coercion.
let sum: i32 = numbers.iter().sum();
```

### 内存布局

`&[T]`是一个**胖指针**，就像`&str`一样。

它由指向切片第一个元素的指针和切片的长度组成。

如果你有一个包含三个元素的`Vec`：

```rs
let numbers = vec![1, 2, 3];
```

然后创建一个切片引用：

```rs
let slice: &[i32] = &numbers[1..];
```

你将得到这样的内存布局：

```rs
 numbers                          slice
      +---------+--------+----------+      +---------+--------+
Stack | pointer | length | capacity |      | pointer | length |
      |    |    |   3    |    4     |      |    |    |   2    |
      +----|----+--------+----------+      +----|----+--------+
           |                                    |  
           |                                    |
           v                                    | 
         +---+---+---+---+                      |
Heap:    | 1 | 2 | 3 | ? |                      |
         +---+---+---+---+                      |
               ^                                |
               |                                |
               +--------------------------------+ 
```

### [`&Vec<T>` 与 `&[T]`](#vect-vs-t)

当你需要将`Vec`的不可变引用传递给函数时，优先选择`&[T]`而不是`&Vec<T>`。

这使得函数可以接受任何类型的切片，而不仅仅是基于`Vec`的切片。

例如，你可以传递`Vec`中元素的一个子集。但不仅如此——你还可以传递一个**数组的切片**：

```rs
let array = [1, 2, 3];
let slice: &[i32] = &array;
```

数组切片和`Vec`切片是同一类型：它们都是指向连续元素序列的胖指针。在数组的情况下，指针指向栈而不是堆，但在使用切片时这并不重要。

## 练习

本节的练习位于[`06_ticket_management/10_slices`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/06_ticket_management/10_slices)
