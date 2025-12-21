# Vec

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/vec.html`](https://freddiehaddad.github.io/fast-track-to-rust/vec.html)

`Vec`，即向量，是一种连续可增长的数组类型，写作`Vec<T>`。尽管我们还没有介绍用户自定义类型，但`Vec`是通过一个`struct`实现的。^(1) 它支持许多熟悉的操作，如`push`、`pop`和`len`，但也包括一些你可能不熟悉的操作。

## 将我们的行存储在向量中

让我们在 rustle 程序中迄今为止使用的输入中填充一个向量。创建向量有几种方法，[文档](https://doc.rust-lang.org/std/vec/struct.Vec.html)提供了大量的示例。我们将探索其中的一些。

### 使用`push`

拥有 C++背景的人可能会倾向于使用以下形式的变体来实现这一点：

> 隐藏代码
> 
> 为了使代码更容易阅读，只有新部分是可见的。你可以通过在代码块上悬停并点击“显示隐藏行”按钮来查看之前看到的代码。

```rs
fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";      let mut lines = Vec::new(); // each call to push mutates the vector
    for line in poem.lines() {
        lines.push(line);
    }

    // format text for debugging purposes
    println!("{lines:?}");
}
```

我们还没有讨论特性，所以现在只需知道`:?`指定使用`Debug`^(2)特性来格式化输出。向量类型实现了`fmt::Debug`特性。

### 使用迭代器

虽然使用`push`在功能上是正确的，但它不必要地引入了一个可变变量。一种惯用的解决方案看起来像这样：

```rs
use std::iter::FromIterator; // this line addresses a rust playground bug   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";      // convert poem into lines
    let lines = Vec::from_iter(poem.lines());
  // format text for debugging purposes println!("{lines:?}"); }
```

> 优先考虑不可变性
> 
> 默认不可变的概念是 Rust 鼓励你编写利用其安全特性并支持易于并发的代码的许多方式之一。

## 跟踪所有匹配项

现在我们已经有一个包含我们诗歌中所有行的向量，让我们再创建一个向量来存储找到模式的行号。

```rs
use std::iter::FromIterator; // this line addresses a rust playground bug   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";      let pattern = "all";

 // convert the poem into lines let lines = Vec::from_iter(poem.lines());      // store the 0-based line number for any matched line
    let match_lines: Vec<_> = lines // inferred type (_)
        .iter()
        .enumerate()
        .filter_map(|(i, line)| match line.contains(pattern) {
            true => Some(i),
            false => None,
        })
        .collect(); // turns anything iterable into a collection
  // format text for debugging purposes println!("{match_lines:?}"); }
```

除了使用`from_iter`，你还可以使用`collect`。

> 在`Vec<_>`中的推断类型（`_`）*要求*编译器根据周围环境推断类型（如果可能的话）。^(2)

## 从匹配行创建区间

`map`函数对向量中的每个值调用一次闭包，将`line_no`（行号）传递给函数。我们使用这个来识别我们想要打印的匹配之前和之后的行。为了处理潜在的越界索引，我们使用`saturating_add`和`saturating_sub`。

```rs
use std::iter::FromIterator; // this line addresses a rust playground bug   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let pattern = "all";    let before_context = 1;
    let after_context = 1;

 // convert the poem into lines let lines = Vec::from_iter(poem.lines());   // store the 0-based line number for any matched line let match_lines: Vec<_> = lines .iter() .enumerate() .filter_map(|(i, line)| match line.contains(pattern) { true => Some(i), false => None, }) .collect(); // turns anything iterable into a collection      // create intervals of the form [a,b] with the before/after context
    let intervals: Vec<_> = match_lines
        .iter()
        .map(|line_no| {
            (
                // prevent underflow
                line_no.saturating_sub(before_context),
                // prevent overflow
                line_no.saturating_add(after_context),
            )
        })
        .collect();
  // format text for debugging purposes println!("{intervals:?}"); }
```

## 合并区间

合并重叠的区间很简单，因为它们已经排序，下一个区间的结束值必须大于当前值。我们可以将合并后的区间存储在一个新的 Vector 中，但这将是不高效的。相反，我们将使我们的`intervals`向量可变，并利用`dedup_by`迭代器适配器来执行合并。

```rs
use std::iter::FromIterator; // this line addresses a rust playground bug   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let pattern = "all"; let before_context = 1; let after_context = 1;   // convert the poem into lines let lines = Vec::from_iter(poem.lines());   // store the 0-based line number for any matched line let match_lines: Vec<_> = lines .iter() .enumerate() .filter_map(|(i, line)| match line.contains(pattern) { true => Some(i), false => None, }) .collect(); // turns anything iterable into a collection   // create intervals of the form [a,b] with the before/after context    let mut intervals: Vec<_> = match_lines
 .iter() .map(|line| { ( line.saturating_sub(before_context), line.saturating_add(after_context), ) }) .collect();      // merge overlapping intervals
    intervals.dedup_by(|next, prev| {
        if prev.1 < next.0 {
            false
        } else {
            prev.1 = next.1;
            true
        }
    });
  // format text for debugging purposes println!("{intervals:?}"); }
```

[dedup_by](https://docs.rs/itertools/latest/itertools/trait.Itertools.html#method.dedup_by)迭代器适配器根据提供的闭包移除基于连续相同元素的迭代器。它首先使用集合中的第一个（`prev`）和第二个（`next`）元素调用闭包。如果闭包返回`false`，则`prev`变为`next`，`next`前进，并使用新元素调用闭包。如果闭包返回`true`，则只前进`next`。这种行为允许我们将`prev`更新为合并的区间，从而实现重叠区间的有效合并。

> 元组字段使用基于 0 的索引访问，就像数组元素一样。

## 打印结果

我们的区间合并后，现在可以正确地打印出结果了！

```rs
use std::iter::FromIterator; // this line addresses a rust playground bug   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let pattern = "all"; let before_context = 1; let after_context = 1;   // convert the poem into lines let lines = Vec::from_iter(poem.lines());   // store the 0-based line number for any matched line let match_lines: Vec<_> = lines .iter() .enumerate() .filter_map(|(i, line)| match line.contains(pattern) { true => Some(i), false => None, }) .collect(); // turns anything iterable into a collection   // create intervals of the form [a,b] with the before/after context let mut intervals: Vec<_> = match_lines .iter() .map(|line| { ( line.saturating_sub(before_context), line.saturating_add(after_context), ) }) .collect();   // merge overlapping intervals intervals.dedup_by(|next, prev| { if prev.1 < next.0 { false } else { prev.1 = next.1; true } });      // print the lines
    for (start, end) in intervals {
        for (line_no, line) in lines
                .iter()
                .enumerate()
                .take(end + 1)
                .skip(start) {
            println!("{}: {}", line_no + 1, line)
        }
    }
}
```

## 我们做到了！

我们有一个工作的 rustle 程序！花些时间回顾一下我们到目前为止所涵盖的内容。接下来的课程将会很快地推进。

# 总结

在本节中，我们涵盖了相当多的内容：

+   `collect`可以将任何可迭代对象转换为集合。

+   `saturating_add`和`saturating_sub`可以防止溢出。

+   `skip`创建一个迭代器，它跳过元素，直到跳过了`n`个元素或者到达迭代器的末尾，以先到者为准。

+   `take`创建一个迭代器，它会产生元素，直到产生了`n`个元素或者到达迭代器的末尾，以先到者为准。

+   `println!`宏支持`[?:](https://doc.rust-lang.org/std/fmt/index.html#fmtdisplay-vs-fmtdebug)`格式说明符，该说明符旨在帮助调试 Rust 代码。所有公共类型都应该实现`fmt::Debug trait`。^(3)

# 下一页

让我们深入探讨所有权和借用概念。

* * *

1.  请参考[Vec 源代码](https://doc.rust-lang.org/src/alloc/vec/mod.rs.html)以查看其完整实现。`struct`定义在第[397 行](https://doc.rust-lang.org/src/alloc/vec/mod.rs.html#397)。↩

1.  [推断类型](https://doc.rust-lang.org/reference/types/inferred.html?highlight=Vec%3C_%3E#inferred-type)是 Rust 类型系统的一部分。↩ ↩2

1.  关于`Debug`特质的详细信息可以在[这里](https://doc.rust-lang.org/std/fmt/trait.Debug.html)找到。↩
