# 正则表达式

> 原文：[`freddiehaddad.github.io/fast-track-to-rust/regular_expression.html`](https://freddiehaddad.github.io/fast-track-to-rust/regular_expression.html)

在我们的项目中添加了`Regex`包后，我们将用正则表达式替换我们一直在使用的`pattern`字符串切片。

## 使用正则表达式

`Regex`模块定义了一个`new`方法，该方法接受一个正则表达式，尝试编译它，并返回一个`Regex`对象.^(1)

```rs
let pattern = "[Ee]xample";
let re = Regex::new(pattern);
```

由于编译正则表达式可能会失败（例如，由于无效的模式），`new`返回一个`Result`。以下是`new`函数的签名^(2)：

```rs
fn new(re: &str) -> Result<Regex, Error>
```

函数签名表明，`Ok`变体返回一个`Regex`，而`Err`变体返回一个`Error`。由于我们的 rustle 程序不能继续使用无效的正则表达式，我们需要捕获这种情况，显示一个有用的错误消息，并退出程序。

让我们把所有这些放在一起：

```rs
extern crate regex; // this is needed for the playground
use regex::Regex;
use std::process::exit;

fn main() {
    let pattern = "(missing the closing parenthesis"; // invalid expression

    // compile the regular expression
    match Regex::new(pattern) {
        // the underscore (_) means we are ignoring the value returned by new
        Ok(_) => println!("{pattern} is a valid regular expression!"),

        // e is the error value returned by new
        Err(e) => {
            eprintln!("{e}"); // eprintln! writes to standard error
            exit(1);          // exit with error code 1
        }
    };
}
```

运行代码以查看错误。然后，通过添加缺失的括号`()`来纠正它，并重新运行代码。

## 更新 Rustle

现在我们有足够的上下文来修改我们的 rustle 程序以包含正则表达式支持。以下是更改内容，其中与程序无关的部分被隐藏：

```rs
#![allow(unused_imports)] use std::fs::File; use std::io::Read; use std::io::{BufRead, BufReader}; use std::process::exit; extern crate regex; // this is needed for the playground use regex::Regex;

fn find_matching_lines(lines: &[String], regex: Regex) -> Vec<usize> {
    lines
        .iter()
        .enumerate()
        .filter_map(|(i, line)| match regex.is_match(line) {
            true => Some(i),
            false => None,
        })
        .collect() // turns anything iterable into a collection
}

fn create_intervals(
 lines: Vec<usize>, before_context: usize, after_context: usize, ) -> Vec<(usize, usize)> {
 lines .iter() .map(|line| { ( line.saturating_sub(before_context), line.saturating_add(after_context), ) }) .collect() }   fn merge_intervals(intervals: &mut Vec<(usize, usize)>) {
 // merge overlapping intervals intervals.dedup_by(|next, prev| { if prev.1 < next.0 { false } else { prev.1 = next.1; true } }) }   fn print_results(intervals: Vec<(usize, usize)>, lines: Vec<String>) {
 for (start, end) in intervals { for (line_no, line) in lines.iter().enumerate().take(end + 1).skip(start) { println!("{}: {}", line_no + 1, line) } } }   fn read_file(file: impl Read) -> Vec<String> {
 BufReader::new(file).lines().map_while(Result::ok).collect() }   fn main() {
 let poem = "I have a little shadow that goes in and out with me, And what can be the use of him is more than I can see. He is very, very like me from the heels up to the head; And I see him jump before me, when I jump into my bed.   The funniest thing about him is the way he likes to grow - Not at all like proper children, which is always very slow; For he sometimes shoots up taller like an india-rubber ball, And he sometimes gets so little that there's none of him at all.";   let mock_file = std::io::Cursor::new(poem);   // command line arguments let pattern = "(all)|(little)"; let before_context = 1; let after_context = 1;   // attempt to open the file let lines = read_file(mock_file); //let lines = match File::open(filename) { //    // convert the poem into lines //    Ok(file) => read_file(file), //    Err(e) => { //        eprintln!("Error opening {filename}: {e}"); //        exit(1); //    } //};      // compile the regular expression
    let regex = match Regex::new(pattern) {
        Ok(re) => re, // bind re to regex
        Err(e) => {
            eprintln!("{e}"); // write to standard error
            exit(1);
        }
    };

    // store the 0-based line number for any matched line
    let match_lines = find_matching_lines(&lines, regex);
  // create intervals of the form [a,b] with the before/after context let mut intervals = create_intervals(match_lines, before_context, after_context);   // merge overlapping intervals merge_intervals(&mut intervals);   // print the lines print_results(intervals, lines); }
```

> 不要忘记，你可以通过点击*显示隐藏行*来揭示隐藏的部分。

`let regex = match Regex::new(pattern)`变量绑定表达式可能看起来有点不寻常。模式在 Rust 文档的[使用 Result 恢复错误](https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html#recoverable-errors-with-result)部分进行了讨论。简要解释一下：当结果是`Ok`时，此代码从`Ok`变体中提取内层的`re`值并将其移动到变量`regex`。

# 下一步

接下来，让我们创建自己的模块！

* * *

1.  `Regex`包包括优秀的[文档](https://docs.rs/regex/latest/regex/)和详细的[示例](https://docs.rs/regex/latest/regex/#examples)供学习。 ↩

1.  `new`的源代码可以在[这里](https://docs.rs/regex/latest/src/regex/regex/string.rs.html#180-182)找到。 ↩
