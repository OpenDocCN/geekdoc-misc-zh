# 集合

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/collections.html`](https://freddiehaddad.github.io/fast-track-to-rust/collections.html)

Rust 的标准库提供了一些非常强大和有用的数据结构，被称为 [集合](https://doc.rust-lang.org/std/collections/index.html)。虽然我们将在本课程中探索其中之一，但花时间审查整个集合库绝对是值得的。

集合通常分为四个类别：

+   序列：[Vec](https://doc.rust-lang.org/std/vec/struct.Vec.html), [VecDeque](https://doc.rust-lang.org/std/collections/struct.VecDeque.html), [LinkedList](https://doc.rust-lang.org/std/collections/struct.LinkedList.html)

+   映射：[HashMap](https://doc.rust-lang.org/std/collections/hash_map/struct.HashMap.html), [BTreeMap](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html)

+   集合：[HashSet](https://doc.rust-lang.org/std/collections/hash_set/struct.HashSet.html), [BTreeSet](https://doc.rust-lang.org/std/collections/struct.BTreeSet.html)

+   Misc: [二叉堆](https://doc.rust-lang.org/std/collections/struct.BinaryHeap.html)

## Rustle

目前，我们的 rustle 程序仅输出每个模式匹配的行号和匹配行。它还不支持打印匹配前后的行。到目前为止，我们还没有一种直接的方法来实现这一功能，并且我们需要解决几个挑战。

### 处理上下文

`--before-context` 选项要求我们在遇到匹配时打印前面的行。这需要一个机制来引用这些行。然而，我们应该只打印每一行一次，以避免在上下文中连续行包含匹配时重复打印行。

考虑我们代码中的这首诗：

```rs
I have a little shadow that goes in and out with me,
And what can be the use of him is more than I can see.
He is very, very like me from the heels up to the head;
And I see him jump before me, when I jump into my bed.

The funniest thing about him is the way he likes to grow -
Not at all like proper children, which is always very slow;
For he sometimes shoots up taller like an india-rubber ball,
And he sometimes gets so little that there's none of him at all. 
```

如果模式是 "him" 并且设置要打印的每行匹配前前的行数为 2 (`--before-context=2`)，如果没有跟踪打印行的方法，我们最终会得到以下输出：

```rs
1: I have a little shadow that goes in and out with me,
2: And what can be the use of him is more than I can see.
2: And what can be the use of him is more than I can see.
3: He is very, very like me from the heels up to the head;
4: And I see him jump before me, when I jump into my bed.
5:
4: And I see him jump before me, when I jump into my bed.
5:
6: The funniest thing about him is the way he likes to grow -
7: Not at all like proper children, which is always very slow;
8: For he sometimes shoots up taller like an india-rubber ball,
9: And he sometimes gets so little that there's none of him at all. 
```

这不是我们 rustle 程序想要的行为。相反，我们希望得到以下输出：

```rs
1: I have a little shadow that goes in and out with me,
2: And what can be the use of him is more than I can see.
3: He is very, very like me from the heels up to the head;
4: And I see him jump before me, when I jump into my bed.
5:
6: The funniest thing about him is the way he likes to grow -
7: Not at all like proper children, which is always very slow;
8: For he sometimes shoots up taller like an india-rubber ball,
9: And he sometimes gets so little that there's none of him at all. 
```

与 `--after-context` 也有类似的问题。我们的解决方案涉及使用向量以及元组（因为我们现在熟悉它们）来创建我们想要打印的行范围的区间。

### 从输入访问行

上下文问题表明我们需要一种方法来引用每个匹配周围的行范围。我们将通过将行存储在 Rust 标准库中的一个名为向量 `Vec<T>` 的集合中来解决这个问题。

### 跟踪每个匹配周围的行

由于我们熟悉它们，我们可以使用 `tuple` 来表示每个匹配周围的起始和结束区间。我们需要跟踪这些区间并合并重叠的区间，以避免多次打印相同的行。再次强调，向量将非常有用！

# 下一页

让我们开始编码！
