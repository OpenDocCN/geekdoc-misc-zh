# 排除 F# 故障

俗话说，“如果能编译通过，就是正确的”，但只是试图让代码编译通过就可以非常令人沮丧！因此，本页致力于帮助您排除 F# 代码的故障。

首先，我将提供一些关于排错的一般建议以及初学者常犯的一些常见错误。之后，我将详细描述每个常见错误消息，并给出它们发生的示例以及如何更正它们的示例。

(跳转至错误编号)

## 排除故障的一般指南

目前你能做的最重要的事情就是花时间和精力来了解 F# 是如何工作的，特别是涉及到函数和类型系统的核心概念。因此，请阅读并反复阅读系列文章"思考函数式"和"理解 F# 类型"，玩弄其中的示例，并在尝试进行严肃编码之前对这些概念感到自在。如果你不理解函数和类型是如何工作的，那么编译器报错将毫无意义。

如果你是从像 C# 这样的命令式语言过来的，你可能已经养成了一些坏习惯，依赖调试器来找出和修复不正确的代码。在 F# 中，你可能根本不会走得那么远，因为编译器在许多方面要严格得多。当然，没有工具可以“调试”编译器并逐步跟踪其处理过程。排错编译器错误的最好工具就是你的大脑，而 F# 强制你使用它！

尽管如此，初学者常常会犯一些极为常见的错误，我将快速地讲解一下它们。

### 在调用函数时不要使用括号

在 F# 中，空白是函数参数的标准分隔符。你很少需要使用括号，尤其是在调用函数时不要使用括号。

```
let add x y = x + y
let result = add (1 2)  //wrong
    // error FS0003: This value is not a function and cannot be applied
let result = add 1 2    //correct 
```

### 不要混淆多参数元组

如果有逗号，那么它就是一个元组。而元组是一个对象而不是两个。因此你会收到关于传递了错误类型的参数或者太少参数的错误。

```
addTwoParams (1,2)  // trying to pass a single tuple rather than two args
   // error FS0001: This expression was expected to have type
   //               int but here has type 'a * 'b 
```

编译器将`(1,2)`视为一个通用的元组，试图将其传递给“`addTwoParams`”。然后它抱怨`addTwoParams`的第一个参数是一个整数，而我们尝试传递一个元组。

如果你尝试向期望一个元组的函数传递*两个*参数，你会得到另一个难以理解的错误。

```
addTuple 1 2   // trying to pass two args rather than one tuple
  // error FS0003: This value is not a function and cannot be applied 
```

### 注意参数过少或过多

如果你向函数传递的参数太少，F# 编译器不会抱怨（事实上，“部分应用”是一个重要特性），但如果你不明白发生了什么，你往往会在后来遇到奇怪的“类型不匹配”错误。

同样，如果参数过多的错误通常是“此值不是函数”，而不是更直接的错误。

“printf”系列函数在这方面非常严格。参数数量必须完全匹配。

这是一个非常重要的主题，你必须了解偏函数的工作原理。请参阅系列文章"函数式思维"以获取更详细的讨论。

### 使用分号作为列表分隔符

在 F# 需要显式分隔符字符的少数地方，如列表和记录中，使用分号。逗号从不使用。（像一个损坏的记录，我会提醒你逗号是用于元组的）。

```
let list1 = [1,2,3]    // wrong! This is a ONE-element list containing 
                       // a three-element tuple
let list1 = [1;2;3]    // correct

type Customer = {Name:string, Address: string}  // wrong
type Customer = {Name:string; Address: string}  // correct 
```

### 不要使用 ! 代表 not 或 != 代表不等于

感叹号符号不是“NOT”运算符。它是可变引用的解引用运算符。如果你误用了它，你将会得到以下错误：

```
let y = true
let z = !y
// => error FS0001: This expression was expected to have 
//    type 'a ref but here has type bool 
```

正确的构造是使用“not”关键字。考虑 SQL 或 VB 语法而不是 C 语法。

```
let y = true
let z = not y       //correct 
```

对于“不等于”，使用“<>”，再次像 SQL 或 VB 一样。

```
let z = 1 <> 2      //correct 
```

### 不要使用 = 进行赋值

如果你使用的是可变值，赋值操作写为“`<-`”。如果你使用等号符号，你可能甚至不会得到错误，只会得到一个意外的结果。

```
let mutable x = 1
x = x + 1          // returns false. x is not equal to x+1 
x <- x + 1         // assigns x+1 to x 
```

### 注意隐藏的制表符

缩进规则非常简单，很容易掌握。但你不被允许使用制表符，只能使用空格。

```
let add x y =     
{tab}x + y   
// => error FS1161: TABs are not allowed in F# code 
```

确保将编辑器设置为将制表符转换为空格。如果你从其他地方粘贴代码，请注意。如果你遇到代码的持续问题，请尝试移除空白并重新添加。

### 不要将简单值误认为函数值

如果你试图创建一个函数指针或委托，请注意不要意外地创建一个已经评估过的简单值。

如果你想要一个可以重复使用的无参数函数，你需要显式传递一个 unit 参数，或者将其定义为 lambda。

```
let reader = new System.IO.StringReader("hello")
let nextLineFn   =  reader.ReadLine()  //wrong
let nextLineFn() =  reader.ReadLine()  //correct
let nextLineFn   =  fun() -> reader.ReadLine()  //correct

let r = new System.Random()
let randomFn   =  r.Next()  //wrong
let randomFn() =  r.Next()  //correct
let randomFn   =  fun () -> r.Next()  //correct 
```

查看系列文章"函数式思维"以获取更多关于无参数函数的讨论。

### 故障排除“信息不足”错误的提示

F# 编译器目前是一种从左到右的单通道编译器，因此如果尚未解析，则编译器无法使用程序中较晚的类型信息。

一些错误可能是由此引起的，比如"FS0072: 对不明确类型的对象进行查找"和"FS0041: 无法确定唯一的重载"。对于每个具体情况的建议修复方法将在下面描述，但如果编译器抱怨缺少类型或信息不足，一些一般原则可能有所帮助。这些指导原则包括：

+   在使用前定义事物（这包括确保文件按正确顺序编译）

+   将具有“已知类型”的事物放在具有“未知类型”的事物之前。特别是，你可以重新排序管道和类似的链式函数，使得类型化对象首先出现。

+   根据需要添加注释。一个常见的技巧是添加注释，直到一切都正常工作，然后逐个删除直到你只保留最少的注释。

如果可能的话，请尽量避免添加注释。不仅美观性不佳，而且会使代码更加脆弱。如果没有对它们的显式依赖，更改类型会更容易。

# F#编译器错误

常见错误列表，按错误编号排序

这是一个我认为值得记录的主要错误列表。我没有记录任何不言自明的错误，只有那些对初学者来说似乎模糊的错误。

我将在未来继续添加到列表中，并欢迎任何关于添加内容的建议。

+   FS0001: 类型'X'与类型'Y'不匹配

+   FS0003: 此值不是函数，无法应用

+   FS0008: 此运行时强制转换或类型测试涉及不确定类型

+   FS0010: 绑定中出现意外标识符

+   FS0010: 不完整的结构构造

+   FS0013: 从类型 X 到 Y 的静态强制转换涉及不确定类型

+   FS0020: 此表达式应为'unit'类型

+   FS0030: 值约束

+   FS0035: 此构造已被弃用

+   FS0039: 字段、构造函数或成员 X 未定义

+   FS0041: 无法确定的唯一重载

+   FS0049: 一般情况下不应在模式中使用大写变量标识符

+   FS0072: 对不确定类型的对象进行查找

+   FS0588: 'let'后面的块未完成

## FS0001: 类型'X'与类型'Y'不匹配

这可能是你遇到的最常见的错误。它可以在各种情况下表现出来，所以我将最常见的问题与示例和修复方法分组在一起。请注意错误消息，因为它通常对问题是非常明确的。

| 错误消息 | 可能的原因 |
| --- | --- |
| 类型'float'与类型'int'不匹配 | A. 不能混合使用浮点数和整数 |
| 类型'int'不支持任何名为'DivideByInt'的运算符 | A. 不能混合使用浮点数和整数。 |
| 类型'X'与任何类型不兼容 | B. 使用了错误的数值类型。 |
| 此类型（函数类型）与类型（简单类型）不匹配。注意：函数类型中有箭头，如`'a -> 'b`。 | C. 向函数传递了太多参数。 |
| 此表达式预期为（函数类型），但这里有（简单类型） | C. 向函数传递了太多参数。 |
| 此表达式预期为（N 部分函数），但这里有（N-1 部分函数） | C. 向函数传递了太多参数。 |
| 此表达式预期为（简单类型），但这里有（函数类型） | D. 向函数传递了太少参数。 |

| 此表达式预期为（类型），但这里有（其他类型） | E. 直接的类型不匹配。 F. 分支或匹配中的返回不一致。

G. 当心隐藏在函数中的类型推断效应。

|

| 类型不匹配。期望一个（简单类型），但给出了一个（元组类型）。注意：元组类型中包含星号，如`'a * 'b`。 | H. 你是不是用逗号代替了空格或分号？ |
| --- | --- |
| 类型不匹配。期望一个（元组类型），但给出了一个（不同的元组类型）。 | I. 元组必须是相同类型才能进行比较。 |
| 预期此表达式类型为'a ref，但此处实际类型为 X | J. 不要将!用作“非”运算符。 |
| 类型（type）与类型（other type）不匹配 | K. 操作符优先级（特别是函数和管道）。 |
| 预期此表达式类型为（monadic type），但此处实际类型为'b * 'c | L. 在计算表达式中出现 let!错误。 |

### A. 不能混合整数和浮点数

与 C#和大多数命令式语言不同，整数和浮点数不能在表达式中混合使用。如果你尝试这样做，你会得到一个类型错误：

```
1 + 2.0  //wrong
   // => error FS0001: The type 'float' does not match the type 'int' 
```

修复方法是先将整数转换为`float`：

```
float 1 + 2.0  //correct 
```

这个问题也会在库函数和其他地方显现出来。例如，你不能对一个整数列表执行“`average`”。

```
[1..10] |> List.average   // wrong
   // => error FS0001: The type 'int' does not support any 
   //    operators named 'DivideByInt' 
```

你必须首先将每个整数转换为浮点数，如下所示：

```
[1..10] |> List.map float |> List.average  //correct 
[1..10] |> List.averageBy float  //correct (uses averageBy) 
```

### B. 使用错误的数字类型

当数值转换失败时，你会得到一个“不兼容”错误。

```
printfn "hello %i" 1.0  // should be a int not a float
  // error FS0001: The type 'float' is not compatible 
  //               with any of the types byte,int16,int32... 
```

一个可能的修复方法是在适当的时候进行转换。

```
printfn "hello %i" (int 1.0) 
```

### C. 向函数传递的参数过多

```
let add x y = x + y
let result = add 1 2 3
// ==> error FS0001: The type ''a -> 'b' does not match the type 'int' 
```

线索就在错误中。

修复方法是删除其中一个参数！

类似的错误是由于向`printf`传递了太多的参数。

```
printfn "hello" 42
// ==> error FS0001: This expression was expected to have type 'a -> 'b    
//                   but here has type unit    

printfn "hello %i" 42 43
// ==> Error FS0001: Type mismatch. Expecting a 'a -> 'b -> 'c    
//                   but given a 'a -> unit    

printfn "hello %i %i" 42 43 44
// ==> Error FS0001: Type mismatch. Expecting a  'a -> 'b -> 'c -> 'd    
//                   but given a 'a -> 'b -> unit 
```

### D. 向函数传递的参数过少

如果向函数传递的参数不足，将会得到一个部分应用。当你之后使用它时，会因为它不是一个简单类型而导致错误。

```
let reader = new System.IO.StringReader("hello");

let line = reader.ReadLine        //wrong but compiler doesn't complain
printfn "The line is %s" line     //compiler error here!
// ==> error FS0001: This expression was expected to have type string    
//                   but here has type unit -> string 
```

对于一些.NET 库函数，特别常见的错误是它们期望一个 unit 参数，比如上面的`ReadLine`。

修复方法是传递正确数量的参数。检查结果值的类型，确保它确实是一个简单类型。在`ReadLine`的情况下，修复方法是传递一个`()`参数。

```
let line = reader.ReadLine()      //correct
printfn "The line is %s" line     //no compiler error 
```

### E. 类型不匹配

最简单的情况是你使用了错误的类型，或者在打印格式字符串中使用了错误的类型。

```
printfn "hello %s" 1.0
// => error FS0001: This expression was expected to have type string    
//                  but here has type float 
```

### F. 分支或匹配中返回类型不一致

一个常见的错误是，如果你有一个分支或匹配表达式，那么每个分支必须返回相同的类型。如果不是，则会得到类型错误。

```
let f x = 
  if x > 1 then "hello"
  else 42
// => error FS0001: This expression was expected to have type string    
//                  but here has type int 
```

```
let g x = 
  match x with
  | 1 -> "hello"
  | _ -> 42
// error FS0001: This expression was expected to have type
//               string but here has type int 
```

显然，最直接的修复方法是使每个分支返回相同的类型。

```
let f x = 
  if x > 1 then "hello"
  else "42"

let g x = 
  match x with
  | 1 -> "hello"
  | _ -> "42" 
```

记住，如果“else”分支丢失，就假设它返回 unit，因此“true”分支也必须返回 unit。

```
let f x = 
  if x > 1 then "hello"
// error FS0001: This expression was expected to have type
//               unit but here has type string 
```

如果两个分支无法返回相同的类型，你可能需要创建一个新的联合类型，可以包含两种类型。

```
type StringOrInt = | S of string | I of int  // new union type
let f x = 
  if x > 1 then S "hello"
  else I 42 
```

### G. 当心隐藏在函数中的类型推断效应

函数可能会导致意外的类型推断在你的代码中波及。例如，在以下代码中，无辜的打印格式字符串意外地导致`doSomething`期望一个字符串。

```
let doSomething x = 
   // do something
   printfn "x is %s" x
   // do something more

doSomething 1
// => error FS0001: This expression was expected to have type string    
//    but here has type int 
```

修复方法是检查函数签名并一直深入到找到有问题的代码为止。此外，尽可能使用最通用的类型，并尽量避免类型注解。

### H. 您是否使用逗号而不是空格或分号？

如果您是 F#的新手，可能会不小心使用逗号而不是空格来分隔函数参数：

```
// define a two parameter function
let add x y = x + 1

add(x,y)   // FS0001: This expression was expected to have 
           // type int but here has type  'a * 'b 
```

修复方法是：不要使用逗号！

```
add x y    // OK 
```

在调用.NET 库函数时，逗号是被使用的一个领域。所有这些都将元组作为参数，因此逗号形式是正确的。实际上，这些调用看起来与从 C#进行的调用完全相同：

```
// correct
System.String.Compare("a","b")

// incorrect
System.String.Compare "a" "b" 
```

### I. 元组必须是相同类型才能进行比较或模式匹配

具有不同类型的元组无法进行比较。尝试将类型为`int * int`的元组与类型为`int * string`的元组进行比较会导致错误：

```
let  t1 = (0, 1)
let  t2 = (0, "hello")
t1 = t2
// => error FS0001: Type mismatch. Expecting a int * int    
//    but given a int * string    
//    The type 'int' does not match the type 'string' 
```

并且长度必须相同：

```
let  t1 = (0, 1)
let  t2 = (0, 1, "hello")
t1 = t2
// => error FS0001: Type mismatch. Expecting a int * int    
//    but given a int * int * string    
//    The tuples have differing lengths of 2 and 3 
```

在绑定期间模式匹配元组时，可能会出现相同的问题：

```
let x,y = 1,2,3
// => error FS0001: Type mismatch. Expecting a 'a * 'b    
//                  but given a 'a * 'b * 'c    
//                  The tuples have differing lengths of 2 and 3

let f (x,y) = x + y
let z = (1,"hello")
let result = f z
// => error FS0001: Type mismatch. Expecting a int * int    
//                  but given a int * string    
//                  The type 'int' does not match the type 'string' 
```

### J. 不要使用!作为“非”运算符

如果您使用`！`作为“非”运算符，您将收到一个包含“ref”一词的类型错误。

```
let y = true
let z = !y     //wrong
// => error FS0001: This expression was expected to have 
//    type 'a ref but here has type bool 
```

修复方法是使用“not”关键字。

```
let y = true
let z = not y   //correct 
```

### K. 运算符优先级（特别是函数和管道）

如果混淆了运算符优先级，可能会出现类型错误。通常，与其他运算符相比，函数应用优先级最高，因此在下面的情况下会出现错误：

```
String.length "hello" + "world"
   // => error FS0001:  The type 'string' does not match the type 'int'

// what is really happening
(String.length "hello") + "world" 
```

修复方法是使用括号。

```
String.length ("hello" + "world")  // corrected 
```

相反，管道运算符与其他运算符相比优先级较低。

```
let result = 42 + [1..10] |> List.sum
 // => => error FS0001:  The type ''a list' does not match the type 'int'

// what is really happening
let result = (42 + [1..10]) |> List.sum 
```

同样，修复方法是使用括号。

```
let result = 42 + ([1..10] |> List.sum) 
```

### L. 在计算表达式（单子）中出现 let!错误

这是一个简单的计算表达式：

```
type Wrapper<'a> = Wrapped of 'a

type wrapBuilder() = 
    member this.Bind (wrapper:Wrapper<'a>) (func:'a->Wrapper<'b>) = 
        match wrapper with
        | Wrapped(innerThing) -> func innerThing

    member this.Return innerThing = 
        Wrapped(innerThing) 

let wrap = new wrapBuilder() 
```

但是，如果您尝试使用它，将会收到错误。

```
wrap {
    let! x1 = Wrapped(1)   // <== error here
    let! y1 = Wrapped(2)
    let z1 = x + y
    return z
    }
// error FS0001: This expression was expected to have type Wrapper<'a>
//               but here has type 'b * 'c 
```

原因是“`Bind`”期望元组`（wrapper，func）`，而不是两个参数。（检查 F#文档中 bind 的签名）。

修复方法是将绑定函数更改为接受元组作为其（唯一）参数。

```
type wrapBuilder() = 
    member this.Bind (wrapper:Wrapper<'a>, func:'a->Wrapper<'b>) = 
        match wrapper with
        | Wrapped(innerThing) -> func innerThing 
```

## FS0003：此值不是函数，无法应用

当向函数传递过多参数时，通常会发生此错误。

```
let add1 x = x + 1
let x = add1 2 3
// ==>   error FS0003: This value is not a function and cannot be applied 
```

当您进行运算符重载但运算符不能用作前缀或中缀时，也可能会发生这种情况。

```
let (!!) x y = x + y
(!!) 1 2              // ok
1 !! 2                // failed !! cannot be used as an infix operator
// error FS0003: This value is not a function and cannot be applied 
```

## FS0008：此运行时强制转换或类型测试涉及不确定类型

当尝试使用“`:?`”运算符对类型进行匹配时，您经常会看到这种情况。

```
let detectType v =
    match v with
        | :? int -> printfn "this is an int"
        | _ -> printfn "something else"
// error FS0008: This runtime coercion or type test from type 'a to int    
// involves an indeterminate type based on information prior to this program point. 
// Runtime type tests are not allowed on some types. Further type annotations are needed. 
```

消息告诉您问题：“某些类型不允许在运行时进行类型测试”。

答案是将值“盒装”，强制其成为引用类型，然后您可以对其进行类型检查：

```
let detectTypeBoxed v =
    match box v with      // used "box v" 
        | :? int -> printfn "this is an int"
        | _ -> printfn "something else"

//test
detectTypeBoxed 1
detectTypeBoxed 3.14 
```

## FS0010：绑定中意外的标识符

通常是由于违反块中表达式对齐的“远离”规则而引起的。

```
//3456789
let f = 
  let x=1     // offside line is at column 3 
   x+1        // oops! don't start at column 4
              // error FS0010: Unexpected identifier in binding 
```

修复方法是正确对齐代码！

另请参见 FS0588：跟随此“let”的块未完成以了解另一个由对齐引起的问题。

## FS0010：结构不完整的结构体

如果您从类构造函数中省略了括号，则经常会发生这种情况：

```
type Something() =
   let field = ()

let x1 = new Something     // Error FS0010 
let x2 = new Something()   // OK! 
```

如果您忘记将运算符括在括号中，也会发生这种情况：

```
// define new operator
let (|+) a = -a

|+ 1    // error FS0010: 
        // Unexpected infix operator

(|+) 1  // with parentheses -- OK! 
```

如果您缺少中缀运算符的一侧，也会发生这种情况：

```
|| true  // error FS0010: Unexpected symbol '||'
false || true  // OK 
```

如果您尝试将命名空间定义发送到 F# 交互式，则也可能会发生。交互式控制台不允许命名空间。

```
namespace Customer  // FS0010: Incomplete structured construct 

// declare a type
type Person= {First:string; Last:string} 
```

## FS0013：从类型 X 到 Y 的静态强制转换涉及不定类型

这通常是由 implic 导致的

## FS0020：此表达式应具有类型'unit'

这个错误通常出现在两种情况下：

+   不是块中的最后一个表达式

+   使用错误的赋值运算符

### FS0020，表达式不是块中的最后一个表达式

块中只有最后一个表达式可以返回一个值。所有其他表达式必须返回单位。因此，当您在不是最后一个函数的位置有一个函数时，通常会发生这种情况。

```
let something = 
  2+2               // => FS0020: This expression should have type 'unit'
  "hello" 
```

简单的解决方法是使用`ignore`。但问问自己为什么要使用一个函数然后丢弃答案？可能是一个 bug。

```
let something = 
  2+2 |> ignore     // ok
  "hello" 
```

如果你以为自己在写 C#，然后不小心使用分号分隔表达式，这种情况也会发生：

```
// wrong
let result = 2+2; "hello";

// fixed
let result = 2+2 |> ignore; "hello"; 
```

### FS0020 与赋值

当分配给属性时，另一种变体的此错误会发生。

```
This expression should have type 'unit', but has type 'Y'. 
```

如果出现这个错误，你很有可能把用于可变值的赋值运算符“`<-`”与相等比较运算符“`=`”混淆了。

```
// '=' versus '<-'
let add() =
    let mutable x = 1
    x = x + 1          // warning FS0020
    printfn "%d" x 
```

修复方法是使用正确的赋值运算符。

```
// fixed
let add() =
    let mutable x = 1
    x <- x + 1
    printfn "%d" x 
```

## FS0030：值限制

这与 F# 的自动泛化到通用类型有关，只要可能的话。

例如，给定：

```
let id x = x
let compose f g x = g (f x)
let opt = None 
```

F# 的类型推断将巧妙地找出通用类型。

```
val id : 'a -> 'a
val compose : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
val opt : 'a option 
```

然而，在某些情况下，F# 编译器感觉到代码是模糊的，即使看起来它猜对了类型，它也需要你更具体：

```
let idMap = List.map id             // error FS0030
let blankConcat = String.concat ""  // error FS0030 
```

几乎总是因为尝试定义部分应用的函数而导致这种情况，并且几乎总是最简单的解决方法是显式添加缺失的参数：

```
let idMap list = List.map id list             // OK
let blankConcat list = String.concat "" list  // OK 
```

更多详情请参阅关于["自动泛化"](http://msdn.microsoft.com/en-us/library/dd233183%28v=VS.100%29.aspx)的 MSDN 文章。

## FS0035：此构造已弃用

在过去几年中，F# 语法已经得到了清理，所以如果你使用的是旧版 F# 书籍或网页上的例子，你可能会遇到这个问题。查看 MSDN 文档以获取正确的语法。

```
let x = 10
let rnd1 = System.Random x         // Good
let rnd2 = new System.Random(x)    // Good
let rnd3 = new System.Random x     // error FS0035 
```

## FS0039：字段、构造函数或成员 X 未定义

这个错误通常在四种情况下发生：

+   显然的情况是某些东西确实没有定义！并确保你没有拼写错误或大小写不匹配。

+   接口

+   递归

+   扩展方法

### FS0039，接口

在 F# 中，所有接口都是“显式”实现而不是“隐式”的。（阅读关于["显式接口实现"](http://msdn.microsoft.com/en-us/library/aa288461%28v=vs.71%29.aspx)的 C# 文档以了解区别的解释）。

关键点是当接口成员被显式实现时，它不能通过普通类实例访问，而只能通过接口实例访问，所以你必须使用`:> `运算符进行类型转换。

下面是一个实现接口的类的示例：

```
type MyResource() = 
   interface System.IDisposable with
       member this.Dispose() = printfn "disposed" 
```

这不起作用：

```
let x = new MyResource()
x.Dispose()  // error FS0039: The field, constructor 
             // or member 'Dispose' is not defined 
```

修复方法是将对象转换为接口，如下所示：

```
// fixed by casting to System.IDisposable 
(x :> System.IDisposable).Dispose()   // OK

let y =  new MyResource() :> System.IDisposable 
y.Dispose()   // OK 
```

### 具有递归的 FS0039

这是一个标准的斐波那契实现：

```
let fib i = 
   match i with
   | 1 -> 1
   | 2 -> 1
   | n -> fib(n-1) + fib(n-2) 
```

不幸的是，这将无法编译：

```
Error FS0039: The value or constructor 'fib' is not defined 
```

原因是当编译器在主体中看到'fib'时，它不知道该函数，因为它尚未完成编译！

修复方法是使用“`rec`”关键字。

```
let rec fib i = 
   match i with
   | 1 -> 1
   | 2 -> 1
   | n -> fib(n-1) + fib(n-2) 
```

请注意，这仅适用于“`let`”函数。成员函数不需要这样做，因为作用域规则略有不同。

```
type FibHelper() =
    member this.fib i = 
       match i with
       | 1 -> 1
       | 2 -> 1
       | n -> fib(n-1) + fib(n-2) 
```

### 具有扩展方法的 FS0039

如果您定义了扩展方法，除非模块在范围内，否则无法使用它。

这里是一个简单的扩展示例：

```
module IntExtensions = 
    type System.Int32 with
        member this.IsEven = this % 2 = 0 
```

如果尝试使用扩展，将会出现 FS0039 错误：

```
let i = 2
let result = i.IsEven  
    // FS0039: The field, constructor or 
    // member 'IsEven' is not defined 
```

修复方法只是打开`IntExtensions`模块。

```
open IntExtensions // bring module into scope
let i = 2
let result = i.IsEven  // fixed! 
```

## FS0041：无法确定唯一的重载

当调用具有多个重载的.NET 库函数时可能会导致这种情况：

```
let streamReader filename = new System.IO.StreamReader(filename) // FS0041 
```

有几种方法可以解决这个问题。一种方法是使用显式类型注释：

```
let streamReader filename = new System.IO.StreamReader(filename:string) // OK 
```

有时您可以使用命名参数来避免类型注释：

```
let streamReader filename = new System.IO.StreamReader(path=filename) // OK 
```

或者您可以尝试创建帮助类型推断的中间对象，而无需使用类型注释：

```
let streamReader filename = 
    let fileInfo = System.IO.FileInfo(filename)
    new System.IO.StreamReader(fileInfo.FullName) // OK 
```

## FS0049：模式中通常不应使用大写变量标识符

在模式匹配时，请注意纯 F#联合类型和仅由标签组成的.NET 枚举类型之间的微妙差异。

纯 F#联合类型：

```
type ColorUnion = Red | Yellow 
let redUnion = Red  

match redUnion with
| Red -> printfn "red"     // no problem
| _ -> printfn "something else" 
```

但对于.NET 枚举，您必须完全限定它们：

```
type ColorEnum = Green=0 | Blue=1      // enum 
let blueEnum = ColorEnum.Blue  

match blueEnum with
| Blue -> printfn "blue"     // warning FS0049
| _ -> printfn "something else" 
```

修复版本：

```
match blueEnum with
| ColorEnum.Blue -> printfn "blue" 
| _ -> printfn "something else" 
```

## FS0072：在不确定类型的对象上查找

当“点”进入一个未知类型的对象时会发生这种情况。

考虑以下示例：

```
let stringLength x = x.Length // Error FS0072 
```

编译器不知道“x”的类型，因此不知道“`Length`”是否是有效的方法。

有几种方法可以解决这个问题。最简单的方法是提供显式类型注释：

```
let stringLength (x:string) = x.Length  // OK 
```

但在某些情况下，对代码进行谨慎的重新排列可能有所帮助。例如，下面的示例看起来应该可以工作。对于人类来说，`List.map`函数应用于字符串列表是显而易见的，那么为什么`x.Length`会导致错误呢？

```
List.map (fun x -> x.Length) ["hello"; "world"] // Error FS0072 
```

原因是 F#编译器目前是一种单通道编译器，因此如果尚未解析，则无法使用程序后面存在的类型信息。

是的，您总是可以明确注释：

```
List.map (fun x:string -> x.Length) ["hello"; "world"] // OK 
```

但另一种更优雅的方法通常可以解决问题，即重新排列已知类型优先，编译器可以在移动到下一个子句之前消化它们。

```
["hello"; "world"] |> List.map (fun x -> x.Length)   // OK 
```

最好避免显式类型注释，因此如果可行，这种方法是最好的。

## FS0588：此“let”后面的块未完成

由于在块中取消缩进表达式，从而违反“离边规则”而引起的。

```
//3456789
let f = 
  let x=1    // offside line is at column 3 
 x+1         // offside! You are ahead of the ball!
             // error FS0588: Block following this 
             // 'let' is unfinished 
```

修复的方法是正确对齐代码。

另请参阅 FS0010：绑定中的意外标识符以了解由对齐引起的另一个问题。
