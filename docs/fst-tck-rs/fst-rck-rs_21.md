# 借用

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/borrowing.html`](https://freddiehaddad.github.io/fast-track-to-rust/borrowing.html)

在上一节关于在移动值之后借用值的错误中，现在让我们专注于如何 *借用* 一个值。

## 引用

回想一下在 字符串切片 `str` 的部分，我们说它通常以 *借用* 的形式 `&str` 出现。前缀位置中的 `&` 操作符^(1) 表示一个借用。在 `find_matching_lines` 中，`pattern` 是 *借用* 的。

```rs
fn find_matching_lines(lines: Vec<&str>, pattern: &str) -> Vec<usize>
```

## 借用 `lines`

在 `find_matching_lines` 中，我们可以通过在参数类型前加一个 `&`，将其改为 `&Vec<&str>`，并在 `main` 中将变量 `lines` 前加一个 `&` 来 *借用* `lines`。在做出这些更改并重新运行程序后，我们可以看到它现在可以正常工作了。

```rs
use std::iter::FromIterator; // this line addresses a rust playground bug   fn find_matching_lines(lines: &Vec<&str>, pattern: &str) -> Vec<usize> {
    lines
        .iter()
        .enumerate()
        .filter_map(|(i, line)| match line.contains(pattern) {
            true => Some(i),
            false => None,
        })
        .collect() // turns anything iterable into a collection
}

fn main() {
    let poem = "I have a little shadow that goes in and out with me,
                And what can be the use of him is more than I can see.
                He is very, very like me from the heels up to the head;
                And I see him jump before me, when I jump into my bed.

                The funniest thing about him is the way he likes to grow -
                Not at all like proper children, which is always very slow;
                For he sometimes shoots up taller like an india-rubber ball,
                And he sometimes gets so little that there's none of him at all.";

    // command line arguments
    let pattern = "all";
    let before_context = 1;
    let after_context = 1;

    // convert the poem into lines
    let lines = Vec::from_iter(poem.lines());

    // store the 0-based line number for any matched line
    let match_lines = find_matching_lines(&lines, pattern);

    // create intervals of the form [a,b] with the before/after context
    let mut intervals: Vec<_> = match_lines
        .iter()
        .map(|line| {
            (
                line.saturating_sub(before_context),
                line.saturating_add(after_context),
            )
        })
        .collect();

    // merge overlapping intervals
    intervals.dedup_by(|next, prev| {
        if prev.1 < next.0 {
            false
        } else {
            prev.1 = next.1;
            true
        }
    });

    // print the lines
    for (start, end) in intervals {
        for (line_no, line) in
            lines.iter().enumerate().take(end + 1).skip(start)
        {
            println!("{}: {}", line_no + 1, line)
        }
    }
}
```

## 继续重构

让我们创建另一个函数来处理我们区间的创建。以下是函数签名：

```rs
fn create_intervals(
    lines: Vec<usize>,
    before_context: usize,
    after_context: usize,
) -> Vec<(usize, usize)>
```

这是我们将转移到新函数中的代码：

```rs
// create intervals of the form [a,b] with the before/after context
let mut intervals: Vec<_> = match_lines
    .iter()
    .map(|line| {
        (
            line.saturating_sub(before_context),
            line.saturating_add(after_context),
        )
    })
    .collect();
```

这里是实施更改后的修订代码。请审查并运行代码。

```rs
use std::iter::FromIterator; // this line addresses a rust playground bug   fn find_matching_lines(lines: &Vec<&str>, pattern: &str) -> Vec<usize> {
    lines
        .iter()
        .enumerate()
        .filter_map(|(i, line)| match line.contains(pattern) {
            true => Some(i),
            false => None,
        })
        .collect() // turns anything iterable into a collection
}

fn create_intervals(
    lines: Vec<usize>,
    before_context: usize,
    after_context: usize,
) -> Vec<(usize, usize)> {
    lines
        .iter()
        .map(|line| {
            (
                line.saturating_sub(before_context),
                line.saturating_add(after_context),
            )
        })
        .collect()
}

fn main() {
    let poem = "I have a little shadow that goes in and out with me,
                And what can be the use of him is more than I can see.
                He is very, very like me from the heels up to the head;
                And I see him jump before me, when I jump into my bed.

                The funniest thing about him is the way he likes to grow -
                Not at all like proper children, which is always very slow;
                For he sometimes shoots up taller like an india-rubber ball,
                And he sometimes gets so little that there's none of him at all.";

    // command line arguments
    let pattern = "all";
    let before_context = 1;
    let after_context = 1;

    // convert the poem into lines
    let lines = Vec::from_iter(poem.lines());

    // store the 0-based line number for any matched line
    let match_lines = find_matching_lines(&lines, pattern);

    // create intervals of the form [a,b] with the before/after context
    let mut intervals =
        create_intervals(match_lines, before_context, after_context);

    // merge overlapping intervals
    intervals.dedup_by(|next, prev| {
        if prev.1 < next.0 {
            false
        } else {
            prev.1 = next.1;
            true
        }
    });

    // print the lines
    for (start, end) in intervals {
        for (line_no, line) in
            lines.iter().enumerate().take(end + 1).skip(start)
        {
            println!("{}: {}", line_no + 1, line)
        }
    }
}
```

> 移动与借用
> 
> +   为什么可以 *移动* `match_lines` 而不会导致错误？
> +   
> +   考虑堆分配，移动 `match_lines` 而不是 *借用* 它可能有哪些优势？

# 练习

开发一个名为 `merge_intervals` 的函数，并将指定的代码从 `main` 中移动到这个函数中，进行必要的更新。构建另一个名为 `print_results` 的函数，并将指定的代码从 `main` 中移动到这个函数中，根据需要更新。

+   创建一个名为 `merge_intervals` 的函数，并将指定的代码从 `main` 中移动到这个函数中，进行必要的更新。

    ```rs
    // merge overlapping intervals
    intervals.dedup_by(|next, prev| {
        if prev.1 < next.0 {
            false
        } else {
            prev.1 = next.1;
            true
        }
    });
    ```

+   创建另一个名为 `print_results` 的函数，并将指定的代码从 `main` 中移动到这个函数中，根据需要更新它。

    ```rs
    // print the lines
    for (start, end) in intervals {
        for (line_no, line) in
            lines.iter().enumerate().take(end + 1).skip(start)
        {
            println!("{}: {}", line_no + 1, line)
        }
    }
    ```

+   修改 `main` 以利用这些新创建的函数。

> 您可以通过更新上面提供的最新版本代码来完成这些练习。

<details><summary>解决方案</summary>

```rs
use std::iter::FromIterator; // this line addresses a rust playground bug

fn find_matching_lines(lines: &Vec<&str>, pattern: &str) -> Vec<usize> {
    lines
        .iter()
        .enumerate()
        .filter_map(|(i, line)| match line.contains(pattern) {
            true => Some(i),
            false => None,
        })
        .collect() // turns anything iterable into a collection
}

fn create_intervals(
    lines: Vec<usize>,
    before_context: usize,
    after_context: usize,
) -> Vec<(usize, usize)> {
    lines
        .iter()
        .map(|line| {
            (
                line.saturating_sub(before_context),
                line.saturating_add(after_context),
            )
        })
        .collect()
}

fn merge_intervals(intervals: &mut Vec<(usize, usize)>) {
    // merge overlapping intervals
    intervals.dedup_by(|next, prev| {
        if prev.1 < next.0 {
            false
        } else {
            prev.1 = next.1;
            true
        }
    })
}

fn print_results(intervals: Vec<(usize, usize)>, lines: Vec<&str>) {
    for (start, end) in intervals {
        for (line_no, line) in
            lines.iter().enumerate().take(end + 1).skip(start)
        {
            println!("{}: {}", line_no + 1, line)
        }
    }
}

fn main() {
    let poem = "I have a little shadow that goes in and out with me,
                And what can be the use of him is more than I can see.
                He is very, very like me from the heels up to the head;
                And I see him jump before me, when I jump into my bed.

                The funniest thing about him is the way he likes to grow -
                Not at all like proper children, which is always very slow;
                For he sometimes shoots up taller like an india-rubber ball,
                And he sometimes gets so little that there's none of him at all.";

    // command line arguments
    let pattern = "all";
    let before_context = 1;
    let after_context = 1;

    // convert the poem into lines
    let lines = Vec::from_iter(poem.lines());

    // store the 0-based line number for any matched line
    let match_lines = find_matching_lines(&lines, pattern);

    // create intervals of the form [a,b] with the before/after context
    let mut intervals =
        create_intervals(match_lines, before_context, after_context);

    // merge overlapping intervals
    merge_intervals(&mut intervals);

    // print the lines
    print_results(intervals, lines);
}
```</details>

# 总结

虽然所有权和借用的概念相对简单，但在学习 Rust 时可能会令人沮丧。阅读官方文档中的[理解所有权](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)将肯定有助于克服这一挑战。在继续 Rust 之旅时，请记住以下要点：

**所有权规则**

+   在 Rust 中，每个值都有一个所有者。

+   一次只能有一个所有者。

+   当所有者超出作用域时，值将被丢弃。

**借用规则**

+   在任何给定时间，您只能有一个可变引用或任意数量的不可变引用。

+   参考文献必须始终有效。

# 下一节

在我们对所有权和借用有了新的理解之后，让我们将重点转向错误处理。

* * *

1.  `&` 运算符根据上下文可以有不同的含义。例如，当用作中缀运算符时，它变为位与运算。 ↩
