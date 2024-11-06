# F#语法在 60 秒内

# F#语法在 60 秒内

下面是一个非常快速的概述，介绍如何阅读 F#代码，适用于对语法不熟悉的新手。

显然这并不是非常详细，但应该足以让您能够阅读并理解本系列中即将出现的示例的要点。如果您不明白所有内容，也不必担心，因为当我们到达实际的代码示例时，我会给出更详细的解释。

F#语法与标准的 C 语法之间的两个主要区别是：

+   不使用花括号来界定代码块。相反，使用缩进（Python 在这方面类似）。

+   使用空格而不是逗号来分隔参数。

有些人觉得 F#语法让人反感。如果您是其中之一，请考虑这句话：

> “优化您的记法以避免在看到它的头 10 分钟内使人困惑，但以后降低可读性是一个非常糟糕的错误。”（David MacIver，通过 [有关 Scala 语法的文章](http://rickyclarkson.blogspot.co.uk/2008/01/in-defence-of-0l-in-scala.html)）。

就个人而言，我认为一旦你习惯了，F# 语法就非常清晰和直接。在许多方面，它比 C#语法更简单，关键字和特殊情况更少。

下面的示例代码是一个简单的 F#脚本，演示了您在日常工作中需要的大部分概念。

我鼓励您进行交互式测试并稍微玩弄一下这段代码！要么：

+   将此键入到一个 F#脚本文件中（扩展名为 .fsx），然后将其发送到交互窗口。有关详细信息，请参阅"安装和使用 F#"页面。

+   或者，尝试在交互窗口中运行此代码。记得总是在结尾使用 `;;` 来告诉解释器你输入完毕并且准备好评估了。

```
// single line comments use a double slash
(* multi line comments use (* . . . *) pair

-end of multi line comment- *)

// ======== "Variables" (but not really) ==========
// The "let" keyword defines an (immutable) value
let myInt = 5
let myFloat = 3.14
let myString = "hello"    //note that no types needed

// ======== Lists ============
let twoToFive = [2;3;4;5]        // Square brackets create a list with
                                 // semicolon delimiters.
let oneToFive = 1 :: twoToFive   // :: creates list with new 1st element
// The result is [1;2;3;4;5]
let zeroToFive = [0;1] @ twoToFive   // @ concats two lists

// IMPORTANT: commas are never used as delimiters, only semicolons!

// ======== Functions ========
// The "let" keyword also defines a named function.
let square x = x * x          // Note that no parens are used.
square 3                      // Now run the function. Again, no parens.

let add x y = x + y           // don't use add (x,y)! It means something
                              // completely different.
add 2 3                       // Now run the function.

// to define a multiline function, just use indents. No semicolons needed.
let evens list =
   let isEven x = x%2 = 0     // Define "isEven" as an inner ("nested") function
   List.filter isEven list    // List.filter is a library function
                              // with two parameters: a boolean function
                              // and a list to work on

evens oneToFive               // Now run the function

// You can use parens to clarify precedence. In this example,
// do "map" first, with two args, then do "sum" on the result.
// Without the parens, "List.map" would be passed as an arg to List.sum
let sumOfSquaresTo100 =
   List.sum ( List.map square [1..100] )

// You can pipe the output of one operation to the next using "|>"
// Here is the same sumOfSquares function written using pipes
let sumOfSquaresTo100piped =
   [1..100] |> List.map square |> List.sum  // "square" was defined earlier

// you can define lambdas (anonymous functions) using the "fun" keyword
let sumOfSquaresTo100withFun =
   [1..100] |> List.map (fun x->x*x) |> List.sum

// In F# returns are implicit -- no "return" needed. A function always
// returns the value of the last expression used.

// ======== Pattern Matching ========
// Match..with.. is a supercharged case/switch statement.
let simplePatternMatch =
   let x = "a"
   match x with
    | "a" -> printfn "x is a"
    | "b" -> printfn "x is b"
    | _ -> printfn "x is something else"   // underscore matches anything

// Some(..) and None are roughly analogous to Nullable wrappers
let validValue = Some(99)
let invalidValue = None

// In this example, match..with matches the "Some" and the "None",
// and also unpacks the value in the "Some" at the same time.
let optionPatternMatch input =
   match input with
    | Some i -> printfn "input is an int=%d" i
    | None -> printfn "input is missing"

optionPatternMatch validValue
optionPatternMatch invalidValue

// ========= Complex Data Types =========

// Tuple types are pairs, triples, etc. Tuples use commas.
let twoTuple = 1,2
let threeTuple = "a",2,true

// Record types have named fields. Semicolons are separators.
type Person = {First:string; Last:string}
let person1 = {First="john"; Last="Doe"}

// Union types have choices. Vertical bars are separators.
type Temp = 
    | DegreesC of float
    | DegreesF of float
let temp = DegreesF 98.6

// Types can be combined recursively in complex ways.
// E.g. here is a union type that contains a list of the same type:
type Employee = 
  | Worker of Person
  | Manager of Employee list
let jdoe = {First="John";Last="Doe"}
let worker = Worker jdoe

// ========= Printing =========
// The printf/printfn functions are similar to the
// Console.Write/WriteLine functions in C#.
printfn "Printing an int %i, a float %f, a bool %b" 1 2.0 true
printfn "A string %s, and something generic %A" "hello" [1;2;3;4]

// all complex types have pretty printing built in
printfn "twoTuple=%A,\nPerson=%A,\nTemp=%A,\nEmployee=%A" 
         twoTuple person1 temp worker

// There are also sprintf/sprintfn functions for formatting data
// into a string, similar to String.Format. 
```

有了这个基础，让我们开始比较一些简单的 F#代码与相应的 C#代码。
