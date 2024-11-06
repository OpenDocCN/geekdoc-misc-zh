# “为什么使用 F#？”系列

这一系列文章将为您带来对 F# 主要特性的指导之旅，然后向您展示 F# 如何在您的日常开发中帮助您。

+   介绍“为什么使用 F#”系列。F# 的好处概述。

+   60 秒内了解 F# 语法。关于如何阅读 F# 代码的快速概述。

+   比较 F# 与 C#：简单求和。我们尝试在不使用循环的情况下对 1 到 N 的平方进行求和。

+   比较 F# 与 C#：排序。我们看到 F# 比 C# 更具声明性，并且我们介绍了模式匹配。

+   比较 F# 与 C#：下载网页。我们看到 F# 在回调方面表现出色，并且我们介绍了“use”关键字。

+   四个关键概念。区别 F# 与标准命令式语言的概念。

+   简洁性。为什么简洁性很重要？。

+   类型推断。如何避免被复杂的类型语法分散注意力。

+   低开销的类型定义。创建新类型没有代价。

+   使用函数提取样板代码。DRY 原则的函数式方法。

+   使用函数作为构建块。函数组合和迷你语言使代码更易读。

+   简洁的模式匹配。模式匹配可以一步匹配和绑定。

+   便利性。减少编程单调和样板代码的特性。

+   类型的即用即有行为。不需要编码的不可变性和内建相等性。

+   函数作为接口。当函数被使用时，OO 设计模式可以是微不足道的。

+   部分应用。如何固定函数的一些参数。

+   活动模式。强大匹配的动态模式。

+   正确性。如何编写‘编译时单元测试’。

+   不可变性。使您的代码可预测。

+   穷举模式匹配。确保正确性的强大技术。

+   使用类型系统确保正确代码。在 F# 中，类型系统是你的朋友，而不是你的敌人。

+   示例：为正确性设计。如何使非法状态不可表示。

+   并发性。我们编写软件的下一次重大革命？。

+   异步编程。用 Async 类封装后台任务。

+   消息和代理。简化并发思考。

+   函数式响应式编程。将事件转换为流。

+   完整性。F#是整个.NET 生态系统的一部分。

+   与.NET 库无缝互操作。与.NET 库一起工作的一些方便功能。

+   任何 C#可以做到的事情……。F#中面向对象代码的快速浏览。

+   为什么使用 F#：结论。

# 《为什么使用 F#》系列介绍

# 《为什么使用 F#》系列介绍

这一系列的帖子将带你领略 F#的主要特性，然后向你展示 F#如何在你的日常开发中帮助你。

### F# 相对于 C# 的主要优势

如果你已经熟悉 C#或 Java，你可能想知道为什么要学习另一种语言。F#有一些主要优点，我将其归为以下主题：

+   **简洁性**。F#不会被编码“噪音”所淹没，如花括号、分号等等。你几乎从不必指定对象的类型，这要归功于强大的类型推断系统。通常，解决同样的问题所需的代码行数更少。

+   **方便性**。许多常见的编程任务在 F#中要简单得多。这包括创建和使用复杂的类型定义，进行列表处理、比较和相等性、状态机等等。而且，由于函数是一等对象，通过创建将其他函数作为参数的函数，或者组合现有函数来创建新功能，非常容易创建强大且可重用的代码。

+   **正确性**。F#拥有非常强大的类型系统，可以防止许多常见的错误，如空引用异常。此外，通常可以使用类型系统本身对业务逻辑进行编码，因此实际上不可能编写错误的代码，因为它在编译时被检测为类型错误。

+   **并发性**。F#具有许多内置工具和库，可以帮助编写在发生多个事情时的系统。异步编程得到直接支持，同样也支持并行性。F#还有一个消息队列系统，并且对事件处理和响应式编程有很好的支持。由于数据结构默认是不可变的，因此共享状态和避免锁定要容易得多。

+   **完整性**。尽管 F# 本质上是一种函数式语言，但它支持其他不是 100%纯的样式，这使得与非纯净的网站、数据库、其他应用程序等交互变得更容易。特别是，F# 被设计为一种混合功能/面向对象语言，因此它几乎可以做到与 C# 一样的所有事情。当然，F# 与 .NET 生态系统无缝集成，这使您可以访问所有第三方 .NET 库和工具。最后，它是 Visual Studio 的一部分，这意味着您可以获得具有 IntelliSense 支持的良好编辑器、调试器以及用于单元测试、源代码控制和其他开发任务的许多插件。

在本系列的其余文章中，我将尝试演示 F# 的每个优点，使用独立的 F# 代码片段（并经常与 C# 代码进行比较）。我将简要介绍 F# 的所有主要功能，包括模式匹配、函数组合和并发编程。希望在您完成本系列时，您对 F# 的强大和优雅感到印象深刻，并且您将受到鼓舞，使用它进行下一个项目！

### 如何阅读和使用示例代码

这些文章中的所有代码片段都被设计为可交互运行。我强烈建议您在阅读每篇文章时评估代码片段。任何大型代码文件的源代码将链接到文章中。

本系列不是教程，因此我不会过多地解释代码为什么有效。如果您无法理解一些细节，请不要担心；本系列的目标只是向您介绍 F# 并激发您对深入学习的兴趣。

如果您有 C# 和 Java 等语言的经验，您可能已经发现，即使您不熟悉关键字或库，您也可以相当好地理解用其他类似语言编写的源代码。您可能会问“如何分配变量？”或“如何进行循环？”通过这些答案，您可以很快进行一些基本的编程。

这种方法对 F# 不起作用，因为在其纯粹形式中，没有变量、没有循环和没有对象。不要沮丧-它最终会有意义！如果您想更深入地了解 F#，请查看"学习 F#" 页面上的一些有用提示。

# 与 C# 比较 F#: 一个简单的求和

# 与 C# 比较 F#: 一个简单的求和

要看看一些真实的 F# 代码是什么样子，让我们从一个简单的问题开始：“求 1 到 N 的平方和”。

我们将使用 F# 实现与 C# 实现进行比较。首先是 F# 代码：

```
// define the square function
let square x = x * x

// define the sumOfSquares function
let sumOfSquares n = 
   [1..n] |> List.map square |> List.sum

// try it
sumOfSquares 100 
```

神秘的 `|>` 被称为管道操作符。它只是将一个表达式的输出传送到下一个表达式的输入。因此，`sumOfSquares` 的代码如下所示：

1.  创建一个 1 到 n 的列表（方括号构造一个列表）。

1.  将列表传送到名为 `List.map` 的库函数中，使用我们刚刚定义的“square”函数转换输入列表为输出列表。

1.  将结果列表的平方管道传递给名为`List.sum`的库函数。你能猜到它是做什么的吗？

1.  没有明确的“return”语句。`List.sum`的输出是函数的整体结果。

接下来，这是一个使用经典（非函数式）C 语言风格的 C#实现。（稍后将讨论使用 LINQ 的更函数式的版本。）

```
public static class SumOfSquaresHelper
{
   public static int Square(int i) {
      return i * i;
   }

   public static int SumOfSquares(int n) {
      int sum = 0;
      for (int i = 1; i <= n; i++)
      {
         sum += Square(i);
      }
      return sum;
   }
} 
```

有什么不同之处？

+   F#代码更加紧凑

+   F#代码没有任何类型声明

+   F#可以进行交互式开发

让我们逐个来看。

### 更少的代码

最明显的区别是有更多的 C#代码。与 3 行 F#代码（忽略注释）相比，有 13 行 C#代码。C#代码有很多“噪音”，比如大括号、分号等。而且在 C#中，函数不能独立存在，而是需要添加到某个类中（“SumOfSquaresHelper”）。F#使用空白代替括号，不需要行终止符，函数可以独立存在。

在 F#中，通常整个函数都写在一行上，就像“square”函数一样。`sumOfSquares`函数也可以写在一行上。在 C#中，这通常被视为不良做法。

当函数有多行时，F#使用缩进来指示代码块，从而消除了大括号的需要。（如果你曾经使用过 Python，这是相同的思路）。所以`sumOfSquares`函数也可以这样写：

```
let sumOfSquares n = 
   [1..n] 
   |> List.map square 
   |> List.sum 
```

唯一的缺点是你必须仔细缩进代码。就我个人而言，我认为这是值得的。

### 没有类型声明

下一个区别是，C#代码必须明确声明所使用的所有类型。例如，`int i`参数和`int SumOfSquares`返回类型。是的，C#确实允许您在许多地方使用“var”关键字，但不能用于函数的参数和返回类型。

在 F#代码中，我们根本没有声明任何类型。这是一个重要的观点：F#看起来像是一种无类型的语言，但实际上它与 C#一样类型安全，事实上，甚至更安全！F#使用一种称为“类型推断”的技术，从上下文中推断您正在使用的类型。它在大多数情况下工作得非常好，并极大地降低了代码复杂性。

在这种情况下，类型推断算法注意到我们从一个整数列表开始。这反过来意味着平方函数和求和函数也必须取整数，并且最终值必须是一个整数。您可以通过查看交互窗口中编译结果来查看推断出的类型。你会看到类似这样的东西：

```
val square : int -> int 
```

这意味着“square”函数接受一个整数并返回一个整数。

如果原始列表使用浮点数，类型推断系统会推断平方函数使用的是浮点数。试一试看：

```
// define the square function
let squareF x = x * x

// define the sumOfSquares function
let sumOfSquaresF n = 
   [1.0 .. n] |> List.map squareF |> List.sum  // "1.0" is a float

sumOfSquaresF 100.0 
```

类型检查非常严格！如果您尝试在原始的`sumOfSquares`示例中使用一个浮点数列表（`[1.0..n]`），或者在`sumOfSquaresF`示例中使用一个整数列表（`[1 ..n]`），您将从编译器那里收到一个类型错误。

### 交互式开发

最后，F# 有一个交互式窗口，您可以立即测试代码并与其进行交互。而在 C# 中，没有简单的方法可以做到这一点。

例如，我可以编写我的平方函数并立即测试它：

```
// define the square function
let square x = x * x

// test
let s2 = square 2
let s3 = square 3
let s4 = square 4 
```

当我确信它能正常工作时，我可以继续下一个代码片段。

这种交互性鼓励一种渐进式的编码方法，可以让人上瘾！

此外，许多人声称，通过交互式设计代码可以强化良好的设计实践，例如解耦和显式依赖关系，因此，适用于交互式评估的代码也将是易于测试的代码。相反，无法进行交互式测试的代码可能也很难测试。

### 重新审视 C# 代码

我的原始示例是使用“旧式”C#编写的。C# 已经融合了许多函数式特性，可以使用 LINQ 扩展以更简洁的方式重写示例。

这是另一个 C# 版本——F# 代码的逐行翻译。

```
public static class FunctionalSumOfSquaresHelper
{
   public static int SumOfSquares(int n) {
      return Enumerable.Range(1, n)
         .Select(i => i * i)
         .Sum();
   }
} 
```

但是，除了花括号、句点和分号的噪音之外，C# 版本需要声明参数和返回类型，而 F# 版本不需要。

许多 C# 开发者可能会觉得这个例子很琐碎，但当逻辑变得更加复杂时，他们仍然会回到循环中。但在 F# 中，你几乎不会看到像这样的显式循环。例如，参见 [这篇关于消除更复杂循环中样板代码的文章](http://fsharpforfunandprofit.com/posts/conciseness-extracting-boilerplate/)。

# 将 F# 与 C# 进行比较：排序

# 将 F# 与 C# 进行比较：排序

在下一个示例中，我们将实现一个类似快速排序的算法来对列表进行排序，并比较 F# 实现和 C# 实现。

这是一个简化的类似快速排序的算法的逻辑：

```
If the list is empty, there is nothing to do.
Otherwise: 
  1\. Take the first element of the list
  2\. Find all elements in the rest of the list that 
      are less than the first element, and sort them. 
  3\. Find all elements in the rest of the list that 
      are >= than the first element, and sort them
  4\. Combine the three parts together to get the final result: 
      (sorted smaller elements + firstElement + 
       sorted larger elements)

```

注意，这是一个简化的算法，没有进行优化（也不是原地排序，像真正的快速排序一样）；我们现在要关注的是清晰度。

下面是 F# 中的代码：

```
let rec quicksort list =
   match list with
   | [] ->                            // If the list is empty
        []                            // return an empty list
   | firstElem::otherElements ->      // If the list is not empty 
        let smallerElements =         // extract the smaller ones 
            otherElements             
            |> List.filter (fun e -> e < firstElem) 
            |> quicksort              // and sort them
        let largerElements =          // extract the large ones
            otherElements 
            |> List.filter (fun e -> e >= firstElem)
            |> quicksort              // and sort them
        // Combine the 3 parts into a new list and return it
        List.concat [smallerElements; [firstElem]; largerElements]

//test
printfn "%A" (quicksort [1;5;23;18;9;1;3]) 
```

再次注意，这不是一个优化的实现，但是设计得与算法密切相关。

让我们仔细看看这段代码：

+   任何地方都没有类型声明。这个函数将适用于任何具有可比较项的列表（几乎所有 F# 类型，因为它们自动具有默认比较函数）。

+   整个函数都是递归的——这是通过 "`let rec quicksort list =`" 中的 `rec` 关键字向编译器发出的信号。

+   `match..with` 有点像 switch/case 语句。每个要测试的分支都使用竖线表示，如下所示：

```
match x with
| caseA -> something
| caseB -> somethingElse 
```

+   "`match`" 与 `[]` 匹配一个空列表，并返回一个空列表。

+   "`match`" 与 `firstElem::otherElements` 做了两件事。

    +   首先，它只匹配非空列表。

    +   其次，它自动创建两个新值。一个用于第一个元素，称为 "`firstElem`"，另一个用于列表的其余部分，称为 "`otherElements`"。在 C# 方面，这就像有一个 "switch" 语句，不仅分支，而且*同时*进行变量声明和赋值。

+   `->` 在某种程度上类似于 C# 中的 lambda (`=>`)。等效的 C# lambda 将类似于 `(firstElem, otherElements) => 执行某些操作`。

+   "`smallerElements`" 部分获取列表的其余部分，使用内联的 lambda 表达式与第一个元素进行过滤，使用 "`<`" 运算符，然后将结果递归地传递到 quicksort 函数中。

+   "`largerElements`" 行执行相同的操作，只是使用 "`>=`" 运算符

+   最终，使用列表连接函数 "`List.concat`" 构造出结果列表。为了使其工作，第一个元素需要放入一个列表中，这就是方括号的作用。

+   再次注意没有 "return" 关键字；最后一个值将被返回。在 "`[]`" 分支中，返回值是空列表，在主分支中，它是新构造的列表。

为了比较，这里是一个旧式的 C# 实现（不使用 LINQ）。

```
public class QuickSortHelper
{
   public static List<T> QuickSort<T>(List<T> values) 
      where T : IComparable
   {
      if (values.Count == 0)
      {
         return new List<T>();
      }

      //get the first element
      T firstElement = values[0];

      //get the smaller and larger elements
      var smallerElements = new List<T>();
      var largerElements = new List<T>();
      for (int i = 1; i < values.Count; i++)  // i starts at 1
      {                                       // not 0!
         var elem = values[i];
         if (elem.CompareTo(firstElement) < 0)
         {
            smallerElements.Add(elem);
         }
         else
         {
            largerElements.Add(elem);
         }
      }

      //return the result
      var result = new List<T>();
      result.AddRange(QuickSort(smallerElements.ToList()));
      result.Add(firstElement);
      result.AddRange(QuickSort(largerElements.ToList()));
      return result;
   }
} 
```

比较两组代码，我们可以再次看到 F# 代码更加紧凑，噪音更少，无需类型声明。

此外，F# 代码几乎与实际算法完全相同，而 C# 代码不然。这是 F# 的另一个关键优势 -- 代码通常更具声明性（"做什么"）而不是命令性（"如何做"），因此更具自我文档性。

## C# 中的函数式实现

这是一个更现代的 "函数式风格" 实现，使用 LINQ 和一个扩展方法：

```
public static class QuickSortExtension
{
    /// <summary>
    /// Implement as an extension method for IEnumerable
    /// </summary>
    public static IEnumerable<T> QuickSort<T>(
        this IEnumerable<T> values) where T : IComparable
    {
        if (values == null || !values.Any())
        {
            return new List<T>();
        }

        //split the list into the first element and the rest
        var firstElement = values.First();
        var rest = values.Skip(1);

        //get the smaller and larger elements
        var smallerElements = rest
                .Where(i => i.CompareTo(firstElement) < 0)
                .QuickSort();

        var largerElements = rest
                .Where(i => i.CompareTo(firstElement) >= 0)
                .QuickSort();

        //return the result
        return smallerElements
            .Concat(new List<T>{firstElement})
            .Concat(largerElements);
    }
} 
```

这样做更加清晰，几乎与 F# 版本相同。但不幸的是，在函数签名中无法避免额外的噪音。

## 正确性

最后，这种紧凑性的一个有益的副作用是，F# 代码通常第一次就可以工作，而 C# 代码可能需要更多的调试。

实际上，在编写这些示例代码时，旧式的 C# 代码最初是不正确的，需要一些调试才能弄清楚。特别棘手的地方是 `for` 循环（从 1 开始而不是零）和 `CompareTo` 比较（我把它搞反了），而且很容易意外修改传入的列表。第二个 C# 示例中的函数式风格不仅更清晰，而且更容易编写正确。

但是，即使是函数式的 C# 版本与 F# 版本相比也有缺点。例如，因为 F# 使用模式匹配，所以不可能在空列表中分支到 "非空列表" 情况。另一方面，在 C# 代码中，如果我们忘记了测试：

```
if (values == null || !values.Any()) ... 
```

然后提取第一个元素：

```
var firstElement = values.First(); 
```

如果出现异常，程序会失败。编译器无法为您执行此操作。在您自己的代码中，您有多少次使用了 `FirstOrDefault` 而不是 `First`，因为您正在编写 "防御性" 代码。这是一个在 C# 中非常常见但在 F# 中很少见的代码模式示例：

```
var item = values.FirstOrDefault();  // instead of .First()
if (item != null) 
{ 
   // do something if item is valid 
} 
```

在 F# 中，一步到位的 "模式匹配和分支" 允许您在许多情况下避免这种情况。

## 后记

以上的 F# 示例实际上按照 F# 的标准相当冗长！

为了好玩，这是一个更典型简洁版本的例子：

```
let rec quicksort2 = function
   | [] -> []                         
   | first::rest -> 
        let smaller,larger = List.partition ((>=) first) rest 
        List.concat [quicksort2 smaller; [first]; quicksort2 larger]

// test code 
printfn "%A" (quicksort2 [1;5;23;18;9;1;3]) 
```

仅仅 4 行代码而已，而且当你习惯了语法后，仍然非常易读。

# 比较 F# 和 C#: 下载网页

# 比较 F# 和 C#: 下载网页

在此示例中，我们将比较使用回调函数处理文本流的下载网页的 F# 和 C# 代码。

我们将从一个简单的 F# 实现开始。

```
// "open" brings a .NET namespace into visibility
open System.Net
open System
open System.IO

// Fetch the contents of a web page
let fetchUrl callback url =        
    let req = WebRequest.Create(Uri(url)) 
    use resp = req.GetResponse() 
    use stream = resp.GetResponseStream() 
    use reader = new IO.StreamReader(stream) 
    callback reader url 
```

让我们来看看这段代码：

+   在顶部使用 "open" 允许我们写 "WebRequest" 而不是 "System.Net.WebRequest"。这类似于 C# 中的 "`using System.Net`" 头文件。

+   接下来，我们定义 `fetchUrl` 函数，它接受两个参数，一个用于处理流的回调函数，以及要获取的 URL。

+   接下来，我们将 url 字符串封装在一个 Uri 中。F# 具有严格的类型检查，因此如果我们写成了：`let req = WebRequest.Create(url)`，编译器会抱怨它不知道使用哪个版本的 `WebRequest.Create`。

+   在声明 `response`、`stream` 和 `reader` 值时，使用 "`use`" 关键字而不是 "`let`"。这只能与实现了 `IDisposable` 接口的类一起使用。它告诉编译器在资源超出范围时自动处理资源。这相当于 C# 中的 "`using`" 关键字。

+   最后一行调用带有 StreamReader 和 url 作为参数的回调函数。请注意，回调的类型无需在任何地方指定。

现在这里是等效的 C# 实现。

```
class WebPageDownloader
{
    public TResult FetchUrl<TResult>(
        string url,
        Func<string, StreamReader, TResult> callback)
    {
        var req = WebRequest.Create(url);
        using (var resp = req.GetResponse())
        {
            using (var stream = resp.GetResponseStream())
            {
                using (var reader = new StreamReader(stream))
                {
                    return callback(url, reader);
                }
            }
        }
    }
} 
```

像往常一样，C# 版本有更多的 "噪音"。

+   有十行仅仅是大括号，还有五级嵌套的视觉复杂性。

+   所有参数类型都必须显式声明，并且泛型 `TResult` 类型必须重复三次。

[* 在这个特定的例子中，当所有 `using` 语句都相邻时，可以移除[额外的大括号和缩进](https://stackoverflow.com/questions/1329739/nested-using-statements-in-c-sharp)，但在更一般的情况下，它们是必需的。]

## 测试代码

在 F# 领域，我们现在可以交互式地测试代码了。

```
let myCallback (reader:IO.StreamReader) url = 
    let html = reader.ReadToEnd()
    let html1000 = html.Substring(0,1000)
    printfn "Downloaded %s. First 1000 is %s" url html1000
    html      // return all the html

//test
let google = fetchUrl myCallback "http://google.com" 
```

最后，我们不得不为 reader 参数（`reader:IO.StreamReader`）进行类型声明。这是必需的，因为 F# 编译器无法自动确定 "reader" 参数的类型。

F#的一个非常有用的特性是你可以在函数中“固定”参数，这样它们就不必每次都传递。这就是为什么`url`参数被放在*最后*而不是最前面，就像 C#版本一样。回调可以设置一次，而 url 则在每次调用时变化。

```
// build a function with the callback "baked in"
let fetchUrl2 = fetchUrl myCallback 

// test
let google = fetchUrl2 "http://www.google.com"
let bbc    = fetchUrl2 "http://news.bbc.co.uk"

// test with a list of sites
let sites = ["http://www.bing.com";
             "http://www.google.com";
             "http://www.yahoo.com"]

// process each site in the list
sites |> List.map fetchUrl2 
```

最后一行（使用`List.map`）显示了如何将新函数轻松与列表处理函数结合使用，以一次下载整个列表。

这是等价的 C#测试代码：

```
[Test]
public void TestFetchUrlWithCallback() {
    Func<string, StreamReader, string> myCallback = (url, reader) =>
    {
        var html = reader.ReadToEnd();
        var html1000 = html.Substring(0, 1000);
        Console.WriteLine(
            "Downloaded {0}. First 1000 is {1}", url,
            html1000);
        return html;
    };

    var downloader = new WebPageDownloader();
    var google = downloader.FetchUrl("http://www.google.com",
                                      myCallback);

    // test with a list of sites
    var sites = new List<string> {
        "http://www.bing.com",
        "http://www.google.com",
        "http://www.yahoo.com"};

    // process each site in the list
    sites.ForEach(site => downloader.FetchUrl(site, myCallback));
} 
```

同样，代码比 F#代码更加嘈杂，有许多显式类型引用。更重要的是，C#代码不容易允许您在函数中固定一些参数，因此每次都必须显式引用回调。

# 四个关键概念

# 四个关键概念

在接下来的几篇文章中，我们将继续展示本系列的主题：简洁、便利、正确、并发和完备。

但在此之前，让我们先看一些我们将一次又一次遇到的 F#中的关键概念。F#在许多方面与标准的命令式语言（如 C#）不同，但有一些特别重要的差异需要特别理解：

+   **面向函数**而不是面向对象

+   **表达式**而不是语句

+   **代数类型**用于创建领域模型

+   **模式匹配**用于控制流程

在后续的文章中，这些将会被更加深入地讨论——这只是一个开胃菜，帮助你理解本系列的其余内容。

![四个关键概念](img/four-concepts2.png)

### 面向函数而不是面向对象

正如你可能从术语“函数式编程”中预期的那样，函数在 F#中无处不在。

当然，函数是头等实体，可以像任何其他值一样传递：

```
let square x = x * x

// functions as values
let squareclone = square
let result = [1..10] |> List.map squareclone

// functions taking other functions as parameters
let execFunction aFunc aParam = aFunc aParam
let result2 = execFunction square 12 
```

但是 C#也有一流函数，那么函数式编程有什么特别之处呢？

简短的答案是，F#的面向函数的特性渗透到语言和类型系统的每个部分，而在 C#中没有这样的情况，因此在 C#中笨拙或繁琐的事情在 F#中非常优雅。

很难用几段话来解释这一点，但以下是我们将在这一系列文章中看到的一些好处：

+   **使用组合构建**。组合是让我们从小系统构建更大系统的“胶水”。这不是一种可选的技术，而是功能风格的核心。几乎每一行代码都是可组合的表达式（见下文）。组合用于构建基本函数，然后是使用这些函数的函数，依此类推。组合原则不仅适用于函数，还适用于类型（下面讨论的乘积和和类型）。

+   **因式分解和重构**。将问题分解为部分的能力取决于这些部分如何容易地粘合在一起。在函数式设计中，在命令式语言中可能看起来不可分割的方法和类通常可以被分解为令人惊讶的小部分。这些细粒度组件通常包括（a）几个非常通用的函数，这些函数将其他函数作为参数，以及（b）其他帮助函数，这些函数为特定数据结构或应用程序专门化了一般情况。一旦分解出来，通用函数允许很容易地编程许多附加操作，而无需编写新代码。您可以在从循环中提取重复代码的帖子中看到一个很好的通用函数的示例（fold 函数）。

+   **良好的设计**。许多良好设计原则，如“关注点分离”，“单一职责原则”，“针对接口编程，而不是实现”，都是作为函数式方法的自然结果而产生的。而且，函数式代码通常在一般情况下是高级别和声明性的。

本系列中的以下帖子将举例说明函数如何使代码更简洁和方便，然后为了更深入地理解，还有一个关于函数式思维的整个系列。

### 表达式而非语句

在函数式语言中，没有语句，只有表达式。也就是说，每个代码块总是返回一个值，并且较大的代码块是通过组合较小的代码块而不是序列化的语句列表来创建的。

如果您已经使用过 LINQ 或 SQL，您将已经熟悉基于表达式的语言。例如，在纯 SQL 中，您不能进行赋值。相反，您必须在较大的查询中使用子查询。

```
SELECT EmployeeName 
FROM Employees
WHERE EmployeeID IN 
    (SELECT DISTINCT ManagerID FROM Employees)  -- subquery 
```

F#也是以相同的方式工作--每个函数定义都是一个单独的表达式，而不是一组语句。

而且可能并不明显，但是使用表达式构建的代码比使用语句更安全且更紧凑。为了看到这一点，让我们比较一些基于语句的 C#代码与等效的基于表达式的代码。

首先，基于语句的代码。语句不返回值，因此您必须使用从语句主体中分配的临时变量。

```
// statement-based code in C#
int result;     
if (aBool)
{
  result = 42; 
}
Console.WriteLine("result={0}", result); 
```

因为`if-then`块是一个语句，所以`result`变量必须在语句之外被定义，但是从语句内部被分配，这会导致诸如以下问题：

+   `result`应该被设置为什么初始值？

+   如果我忘记给`result`变量赋值会怎么样？

+   在“else”情况下，`result`变量的值是多少？

为了比较，这里是以面向表达式的风格重写的相同代码：

```
// expression-based code in C#
int result = (aBool) ? 42 : 0;
Console.WriteLine("result={0}", result); 
```

在面向表达式的版本中，这些问题都不适用：

+   `result` 变量在赋值的同时声明。不需要在表达式之外设置变量，并且不用担心它们应该被设置为什么初始值。

+   “else”被明确处理。没有忘记在其中一个分支中进行赋值的机会。

+   不可能忘记赋值 `result`，因为那样变量甚至都不存在！

表达式导向的风格在 F# 中不是一个选择，这是从命令式背景转变时需要改变方法的事情之一。

### 代数类型

F# 中的类型系统基于**代数类型**的概念。也就是说，通过两种不同的方式组合现有类型来构建新的复合类型：

+   首先，一组值的组合，每个值从一组类型中选择。这些被称为“积”类型。

+   或者，作为表示一组类型选择的不相交并集。这些被称为“和”类型。

例如，给定现有类型 `int` 和 `bool`，我们可以创建一个必须包含每种类型的新积类型：

```
//declare it
type IntAndBool = {intPart: int; boolPart: bool}

//use it
let x = {intPart=1; boolPart=false} 
```

或者，我们可以创建一个新的联合/和类型，其中每种类型之间有一个选择：

```
//declare it
type IntOrBool = 
    | IntChoice of int
    | BoolChoice of bool

//use it
let y = IntChoice 42
let z = BoolChoice true 
```

这些“选择”类型在 C# 中不可用，但对于建模许多现实情况非常有用，比如状态机中的状态（这在许多领域中是一个令人惊讶地常见的主题）。

通过以这种方式组合“积”和“和”类型，可以轻松创建一个丰富的类型集，准确地模拟任何业务领域。有关此操作的示例，请参见低开销类型定义和使用类型系统确保正确代码的文章。

### 用于控制流的模式匹配

大多数命令式语言提供了各种控制流语句用于分支和循环：

+   `if-then-else`（以及三元版本 `bool ? if-true : if-false`）

+   `case` 或 `switch` 语句

+   `for` 和 `foreach` 循环，带有 `break` 和 `continue`

+   `while` 和 `until` 循环

+   甚至可怕的 `goto`

F# 确实支持其中一些，但 F# 也支持最一般形式的条件表达式，即**模式匹配**。

替换 `if-then-else` 的典型匹配表达式如下：

```
match booleanExpression with
| true -> // true branch
| false -> // false branch 
```

而替代 `switch` 可能看起来像这样：

```
match aDigit with
| 1 -> // Case when digit=1
| 2 -> // Case when digit=2
| _ -> // Case otherwise 
```

最后，循环通常使用递归完成，通常看起来像这样：

```
match aList with
| [] -> 
     // Empty case 
| first::rest -> 
     // Case with at least one element.
     // Process first element, and then call 
     // recursively with the rest of the list 
```

虽然匹配表达式起初看起来不必要复杂，但实际上你会发现它既优雅又强大。

有关模式匹配的好处，请参见穷尽模式匹配的文章，以及一个大量使用模式匹配的示例，请参见罗马数字示例。

### 使用联合类型进行模式匹配

我们上面提到 F# 支持“联合”或“选择”类型。这用于处理底层类型的不同变体，而不是使用继承。模式匹配与这些类型无缝配合，为每个选择创建控制流程。

在以下示例中，我们创建了一个代表四种不同形状的 `Shape` 类型，然后为每种形状定义了一个具有不同行为的 `draw` 函数。这类似于面向对象语言中的多态性，但基于函数。

```
type Shape =        // define a "union" of alternative structures
| Circle of int 
| Rectangle of int * int
| Polygon of (int * int) list
| Point of (int * int) 

let draw shape =    // define a function "draw" with a shape param
  match shape with
  | Circle radius -> 
      printfn "The circle has a radius of %d" radius
  | Rectangle (height,width) -> 
      printfn "The rectangle is %d high by %d wide" height width
  | Polygon points -> 
      printfn "The polygon is made of these points %A" points
  | _ -> printfn "I don't recognize this shape"

let circle = Circle(10)
let rect = Rectangle(4,5)
let polygon = Polygon( [(1,1); (2,2); (3,3)])
let point = Point(2,3)

[circle; rect; polygon; point] |> List.iter draw 
```

一些需要注意的事项：

+   通常情况下，我们不必指定任何类型。编译器正确地确定了“draw”函数的形状参数的类型为 `Shape`。

+   你可以看到 `match..with` 逻辑不仅匹配了形状的内部结构，还根据形状适当地分配值。

+   下划线类似于 switch 语句中的“默认”分支，只是在 F# 中是必需的 -- 必须始终处理每种可能的情况。如果你注释掉这行

    ```
    | _ -> printfn "I don't recognize this shape" 
    ```

看看编译时会发生什么！

这类选择类型在 C# 中可以通过使用子类或接口进行某种程度的模拟，但在 C# 类型系统中没有内置支持这种具有错误检查的穷尽匹配。

# 简洁性

# 简洁性

在看了一些简单的代码之后，我们现在将演示主要主题（简洁性、方便性、正确性、并发性和完整性），通过类型、函数和模式匹配的概念进行过滤。

在接下来的几篇文章中，我们将研究 F# 的特性，这些特性有助于简洁和易读性。

大多数主流编程语言的一个重要目标是良好的可读性和简洁性的平衡。太多的简洁性可能导致难以理解或混淆的代码（APL 任何人？），而太多的冗长可能很容易淹没底层含义。理想情况下，我们希望有一个高信噪比，在代码的每个词和字符都对代码的含义做出贡献，并且有最少的样板代码。

为什么简洁性很重要？以下是一些原因：

+   **简洁的语言往往更具声明性**，它说 *代码应该做什么* 而不是 *如何做*。也就是说，声明性代码更关注高层逻辑，而不是实现的细节。

+   **如果要思考的代码行数较少，那么正确性就更容易理解！**

+   当然，**你可以在屏幕上看到更多的代码**。这可能看起来微不足道，但你能看到的越多，你就能理解的越多。

正如你所见，与 C# 相比，F# 通常更为简洁。这是由于诸如以下特性：

+   **类型推断**和**低开销的类型定义**。F#之所以简洁易读的一个重要原因就是其类型系统。F#使得根据需要创建新类型变得非常容易。它们在定义或使用时都不会造成视觉混乱，并且类型推断系统意味着您可以自由地使用它们，而不会被复杂的类型语法分散注意力。

+   **使用函数提取样板代码**。DRY 原则（“不要重复自己”）是函数式语言以及面向对象语言中良好设计的核心原则。在 F#中，将重复的代码提取到常用实用函数中非常容易，这样可以让您专注于重要的事情。

+   **由简单函数组合复杂代码**和**创建迷你语言**。函数式方法使得创建一组基本操作易如反掌，然后以各种方式组合这些构建块以构建更复杂的行为。通过这种方式，即使是最复杂的代码仍然非常简洁易读。

+   **模式匹配**。我们已经将模式匹配视为一个高级的 switch 语句，但实际上它要通用得多，因为它可以以多种方式比较表达式，匹配值、条件和类型，然后同时赋值或提取值。

# 类型推断

# 类型推断

正如您已经看到的，F#使用一种称为“类型推断”的技术来大大减少需要在普通代码中显式指定的类型注解的数量。即使需要指定类型，与 C#相比，语法也不那么冗长。

要了解这一点，这里有一些包装了两个标准 LINQ 函数的 C#方法。这些实现是微不足道的，但是方法签名非常复杂：

```
public IEnumerable<TSource> Where<TSource>(
    IEnumerable<TSource> source,
    Func<TSource, bool> predicate
    )
{
    //use the standard LINQ implementation
    return source.Where(predicate);
}

public IEnumerable<IGrouping<TKey, TSource>> GroupBy<TSource, TKey>(
    IEnumerable<TSource> source,
    Func<TSource, TKey> keySelector
    )
{
    //use the standard LINQ implementation
    return source.GroupBy(keySelector);
} 
```

而这里是确切的 F#等效代码，显示根本不需要任何类型注解！

```
let Where source predicate = 
    //use the standard F# implementation
    Seq.filter predicate source

let GroupBy source keySelector = 
    //use the standard F# implementation
    Seq.groupBy keySelector source 
```

您可能会注意到，“filter”和“groupBy”的标准 F#实现与 C#中使用的 LINQ 实现完全相反。将“source”参数放在最后，而不是首位。这有一个原因，将在函数式思维系列中解释。

类型推断算法非常擅长从许多来源收集信息以确定类型。在下面的示例中，它正确推断出`list`值是一个字符串列表。

```
let i  = 1
let s = "hello"
let tuple  = s,i      // pack into tuple 
let s2,i2  = tuple    // unpack
let list = [s2]       // type is string list 
```

而在这个示例中，它正确推断出`sumLengths`函数接受一个字符串列表并返回一个整数。

```
let sumLengths strList = 
    strList |> List.map String.length |> List.sum

// function type is: string list -> int 
```

# 低开销的类型定义

# 低开销的类型定义

在 C#中，创建新类型有一个不利因素——缺乏类型推断意味着您需要在大多数地方显式指定类型，导致代码脆弱且视觉混乱更多。因此，总是有诱惑力去创建庞大的类，而不是将它们模块化。

在 F# 中，创建新类型没有任何惩罚，因此拥有数百甚至数千个类型是相当常见的。每次需要定义结构时，您都可以创建一个特殊类型，而不是重用（并重载）现有类型，例如字符串和列表。

这意味着您的程序将更加类型安全，更具自我文档化，并且更易于维护（因为当类型更改时，您将立即获得编译时错误而不是运行时错误）。

以下是 F# 中一行类型的一些示例：

```
open System

// some "record" types
type Person = {FirstName:string; LastName:string; Dob:DateTime}
type Coord = {Lat:float; Long:float}

// some "union" (choice) types
type TimePeriod = Hour | Day | Week | Year
type Temperature = C of int | F of int
type Appointment = OneTime of DateTime 
                   | Recurring of DateTime list 
```

## F# 类型和领域驱动设计

在进行领域驱动设计（DDD）时，F# 类型系统的简洁性尤其有用。在 DDD 中，对于每个真实世界的实体和值对象，您理想情况下希望有一个相应的类型。这可能意味着创建数百个 "小" 类型，在 C# 中可能会很烦琐。

此外，在 DDD 中，"值" 对象应具有结构相等性，这意味着包含相同数据的两个对象应始终相等。在 C# 中，这可能意味着重写 `IEquatable<T>` 更烦琐，但在 F# 中，默认情况下您可以免费获得此功能。

为了展示在 F# 中创建 DDD 类型是多么容易，这里是为一个简单的 "客户" 领域可能创建的一些示例类型。

```
type PersonalName = {FirstName:string; LastName:string}

// Addresses
type StreetAddress = {Line1:string; Line2:string; Line3:string }

type ZipCode =  ZipCode of string   
type StateAbbrev =  StateAbbrev of string
type ZipAndState =  {State:StateAbbrev; Zip:ZipCode }
type USAddress = {Street:StreetAddress; Region:ZipAndState}

type UKPostCode =  PostCode of string
type UKAddress = {Street:StreetAddress; Region:UKPostCode}

type InternationalAddress = {
    Street:StreetAddress; Region:string; CountryName:string}

// choice type  -- must be one of these three specific types
type Address = USAddress | UKAddress | InternationalAddress

// Email
type Email = Email of string

// Phone
type CountryPrefix = Prefix of int
type Phone = {CountryPrefix:CountryPrefix; LocalNumber:string}

type Contact = 
    {
    PersonalName: PersonalName;
    // "option" means it might be missing
    Address: Address option;
    Email: Email option;
    Phone: Phone option;
    }

// Put it all together into a CustomerAccount type
type CustomerAccountId = AccountId of string
type CustomerType = Prospect | Active | Inactive

// override equality and deny comparison
[<CustomEquality; NoComparison>]
type CustomerAccount = 
    {
    CustomerAccountId: CustomerAccountId;
    CustomerType: CustomerType;
    ContactInfo: Contact;
    }

    override this.Equals(other) =
        match other with
        | :? CustomerAccount as otherCust -> 
          (this.CustomerAccountId = otherCust.CustomerAccountId)
        | _ -> false

    override this.GetHashCode() = hash this.CustomerAccountId 
```

这个代码片段仅几行就包含了 17 个类型定义，但复杂度很低。要做同样的事情，您需要多少行 C# 代码？

显然，这只是一个简化版本，只包含基本类型？在一个真实系统中，会添加约束和其他方法。但请注意，创建大量的 DDD 值对象是多么容易，特别是字符串的包装类型，例如"`ZipCode`"和"`Email`"。通过使用这些包装类型，我们可以在创建时强制执行某些约束，并确保这些类型在正常代码中不会与不受约束的字符串混淆。唯一的 "实体" 类型是 `CustomerAccount`，明确指出了对等性和比较的特殊处理。

欲了解更详细的讨论，请参阅名为 "F# 中的领域驱动设计" 的系列。

# 使用函数提取样板代码

# 使用函数提取样板代码

在本系列的第一个示例中，我们看到了一个简单的函数，该函数计算了平方和，分别在 F# 和 C# 中实现。现在让我们假设我们想要一些类似的新函数，例如：

+   计算到 N 的所有数字的乘积

+   计算到 N 的奇数之和

+   到 N 的交替和的数字

显然，所有这些要求都是相似的，但您如何提取任何共同的功能？

让我们首先从一些简单的 C# 实现开始：

```
public static int Product(int n) {
    int product = 1;
    for (int i = 1; i <= n; i++)
    {
        product *= i;
    }
    return product;
}

public static int SumOfOdds(int n) {
    int sum = 0;
    for (int i = 1; i <= n; i++)
    {
        if (i % 2 != 0) { sum += i; }
    }
    return sum;
}

public static int AlternatingSum(int n) {
    int sum = 0;
    bool isNeg = true;
    for (int i = 1; i <= n; i++)
    {
        if (isNeg)
        {
            sum -= i;
            isNeg = false;
        }
        else
        {
            sum += i;
            isNeg = true;
        }
    }
    return sum;
} 
```

所有这些实现有什么共同点？循环逻辑！作为程序员，我们被告知记住 DRY 原则（"不要重复你自己"），然而在这里我们几乎完全重复了每个方法中的相同循环逻辑。让我们看看是否可以仅提取这三种方法之间的差异：

| 函数 | 初始值 | 内部循环逻辑 |
| --- | --- | --- |
| Product | product=1 | 将第 i 个值与运行总和相乘 |
| SumOfOdds | sum=0 | 如果不是偶数，则将第 i 个值加到运行总和上 |
| AlternatingSum | int sum = 0 bool isNeg = true | 使用 isNeg 标志来决定是加还是减，并为下一次循环翻转标志。 |

有没有一种方法可以消除重复的代码，只关注设置和内部循环逻辑？是的，有的。下面是相同的三个函数的 F#版本：

```
let product n = 
    let initialValue = 1
    let action productSoFar x = productSoFar * x
    [1..n] |> List.fold action initialValue

//test
product 10

let sumOfOdds n = 
    let initialValue = 0
    let action sumSoFar x = if x%2=0 then sumSoFar else sumSoFar+x 
    [1..n] |> List.fold action initialValue

//test
sumOfOdds 10

let alternatingSum n = 
    let initialValue = (true,0)
    let action (isNeg,sumSoFar) x = if isNeg then (false,sumSoFar-x)
                                             else (true ,sumSoFar+x)
    [1..n] |> List.fold action initialValue |> snd

//test
alternatingSum 100 
```

这三个函数都具有相同的模式：

1.  设置初始值

1.  设置一个在循环内每个元素上执行的动作函数。

1.  调用库函数`List.fold`。这是一个功能强大的通用函数，它从初始值开始，然后依次对列表中的每个元素运行动作函数。

动作函数始终有两个参数：一个运行总和（或状态）和要操作的列表元素（在上面的示例中称为"x"）。

在最后一个函数`alternatingSum`中，你会注意到它使用了一个元组（一对值）作为初始值和操作的结果。这是因为运行总和和`isNeg`标志都必须传递到循环的下一次迭代中 -- 没有可以使用的"全局"值。折叠的最终结果也是一个元组，所以我们必须使用"snd"（第二个）函数来提取我们想要的最终总和。

通过使用`List.fold`并完全避免任何循环逻辑，F#代码获得了许多好处：

+   **关键的程序逻辑被强调并显式地表达出来**。这些函数之间的重要区别变得非常明显，而共同点则被推到了后台。

+   **繁琐的循环代码已经被消除**，结果代码比 C#版本更加简洁（4-5 行 F#代码 vs. 至少 9 行 C#代码）

+   **循环逻辑中永远不会出现错误**（比如说错位一）因为这个逻辑对我们来说是不可见的。

顺便说一句，平方和的例子也可以使用`fold`来写：

```
let sumOfSquaresWithFold n = 
    let initialValue = 0
    let action sumSoFar x = sumSoFar + (x*x)
    [1..n] |> List.fold action initialValue 

//test
sumOfSquaresWithFold 100 
```

## 在 C#中的"Fold"

你能在 C#中使用"fold"方法吗？可以。LINQ 确实有一个等价于`fold`的方法，叫做`Aggregate`。下面是重写为使用它的 C#代码：

```
public static int ProductWithAggregate(int n) {
    var initialValue = 1;
    Func<int, int, int> action = (productSoFar, x) => 
        productSoFar * x;
    return Enumerable.Range(1, n)
            .Aggregate(initialValue, action);
}

public static int SumOfOddsWithAggregate(int n) {
    var initialValue = 0;
    Func<int, int, int> action = (sumSoFar, x) =>
        (x % 2 == 0) ? sumSoFar : sumSoFar + x;
    return Enumerable.Range(1, n)
        .Aggregate(initialValue, action);
}

public static int AlternatingSumsWithAggregate(int n) {
    var initialValue = Tuple.Create(true, 0);
    Func<Tuple<bool, int>, int, Tuple<bool, int>> action =
        (t, x) => t.Item1
            ? Tuple.Create(false, t.Item2 - x)
            : Tuple.Create(true, t.Item2 + x);
    return Enumerable.Range(1, n)
        .Aggregate(initialValue, action)
        .Item2;
} 
```

嗯，从某种意义上说，这些实现比原始的 C#版本更简单、更安全，但是来自通用类型的所有额外噪音使得这种方法比等效的 F#代码不那么优雅。你可以看到，大多数 C#程序员更喜欢使用显式循环。

## 一个更相关的例子

在现实世界中经常出现的一个稍微更相关的例子是，当元素是类或结构体时，如何获取列表的"最大"元素。LINQ 方法'max'只返回最大值，而不是包含最大值的整个元素。

这是一个使用显式循环的解决方案：

```
public class NameAndSize
{
    public string Name;
    public int Size;
}

public static NameAndSize MaxNameAndSize(IList<NameAndSize> list) {
    if (list.Count() == 0)
    {
        return default(NameAndSize);
    }

    var maxSoFar = list[0];
    foreach (var item in list)
    {
        if (item.Size > maxSoFar.Size)
        {
            maxSoFar = item;
        }
    }
    return maxSoFar;
} 
```

在 LINQ 中这样做似乎很难高效地完成（即，在一次遍历中），并且已经出现了一个[Stack Overflow 问题](http://stackoverflow.com/questions/1101841/linq-how-to-perform-max-on-a-property-of-all-objects-in-a-collection-and-ret)。Jon Skeet 甚至写了一篇[关于此的文章](http://codeblog.jonskeet.uk/2005/10/02/a-short-case-study-in-linq-efficiency/)。

再次，fold 拯救！

这里是使用`Aggregate`的 C#代码：

```
public class NameAndSize
{
    public string Name;
    public int Size;
}

public static NameAndSize MaxNameAndSize(IList<NameAndSize> list) {
    if (!list.Any())
    {
        return default(NameAndSize);
    }

    var initialValue = list[0];
    Func<NameAndSize, NameAndSize, NameAndSize> action =
        (maxSoFar, x) => x.Size > maxSoFar.Size ? x : maxSoFar;
    return list.Aggregate(initialValue, action);
} 
```

请注意，这个 C#版本对于空列表返回 null。这似乎很危险--那么应该发生什么？抛出异常？这似乎也不对。

这是使用 fold 的 F#代码：

```
type NameAndSize= {Name:string;Size:int}

let maxNameAndSize list = 

    let innerMaxNameAndSize initialValue rest = 
        let action maxSoFar x = if maxSoFar.Size < x.Size then x else maxSoFar
        rest |> List.fold action initialValue 

    // handle empty lists
    match list with
    | [] -> 
        None
    | first::rest -> 
        let max = innerMaxNameAndSize first rest
        Some max 
```

F#代码分为两部分：

+   `innerMaxNameAndSize`函数与我们之前看到的类似。

+   第二部分，`match list with`，根据列表是否为空进行分支。对于空列表，它返回`None`，而在非空情况下，它返回`Some`。这样做可以确保函数的调用者必须处理这两种情况。

还有一个测试：

```
//test
let list = [
    {Name="Alice"; Size=10}
    {Name="Bob"; Size=1}
    {Name="Carol"; Size=12}
    {Name="David"; Size=5}
    ]    
maxNameAndSize list
maxNameAndSize [] 
```

实际上，我根本不需要写这个，因为 F#已经有了`maxBy`函数！

```
// use the built in function
list |> List.maxBy (fun item -> item.Size)
[] |> List.maxBy (fun item -> item.Size) 
```

但正如你所看到的，它不能很好地处理空列表。这里有一个包装`maxBy`的安��版本。

```
let maxNameAndSize list = 
    match list with
    | [] -> 
        None
    | _ -> 
        let max = list |> List.maxBy (fun item -> item.Size)
        Some max 
```

# 使用函数作为构建块

# 使用函数作为构建块

一个良好设计的众所周知原则是创建一组基本操作，然后以各种方式组合这些构建块来构建更复杂的行为。在面向对象的语言中，这个目标引发了许多实现方法，如“流畅接口”、“策略模式”、“装饰者模式”等。在 F#中，它们都是通过函数组合完成的。

让我们从使用整数的简单示例开始。假设我们已经创建了一些执行算术运算的基本函数：

```
// building blocks
let add2 x = x + 2
let mult3 x = x * 3
let square x = x * x

// test
[1..10] |> List.map add2 |> printfn "%A"
[1..10] |> List.map mult3 |> printfn "%A"
[1..10] |> List.map square |> printfn "%A" 
```

现在我们想要创建建立在这些基础上的新函数：

```
// new composed functions
let add2ThenMult3 = add2 >> mult3
let mult3ThenSquare = mult3 >> square 
```

“`>>`”运算符是组合运算符。它的意思是：先执行第一个函数，然后执行第二个函数。

注意这种组合函数的简洁性。没有参数、类型或其他无关的噪音。

为了确保，这些示例也可以写得不那么简洁，更加显式：

```
let add2ThenMult3 x = mult3 (add2 x)
let mult3ThenSquare x = square (mult3 x) 
```

但这种更显式的风格也有点混乱：

+   在显式风格中，即使 x 参数和括号并不增加代码的含义，也必须添加它们。

+   在显式风格中，函数是按照它们被应用的顺序从后往前编写的。在我的`add2ThenMult3`示例中，我想先加 2，然后再乘。`add2 >> mult3`的语法比`mult3(add2 x)`在视觉上更清晰。

现在让我们测试这些组合：

```
// test
add2ThenMult3 5
mult3ThenSquare 5
[1..10] |> List.map add2ThenMult3 |> printfn "%A"
[1..10] |> List.map mult3ThenSquare |> printfn "%A" 
```

## 扩展现有函数

现在假设我们想要用一些日志记录行为装饰这些现有函数。我们也可以将它们组合起来，以便创建一个内置日志记录的新函数。

```
// helper functions;
let logMsg msg x = printf "%s%i" msg x; x     //without linefeed 
let logMsgN msg x = printfn "%s%i" msg x; x   //with linefeed

// new composed function with new improved logging!
let mult3ThenSquareLogged = 
   logMsg "before=" 
   >> mult3 
   >> logMsg " after mult3=" 
   >> square
   >> logMsgN " result=" 

// test
mult3ThenSquareLogged 5
[1..10] |> List.map mult3ThenSquareLogged //apply to a whole list 
```

我们的新函数 `mult3ThenSquareLogged` 的名称很难看，但使用起来很容易，并且很好地隐藏了其中涉及的函数的复杂性。你可以看到，如果你将构建块函数定义得很好，那么函数的这种组合方式可以是获得新功能的强大方法。

但等等，这还不止！函数在 F# 中是一等公民实体，并且可以被任何其他 F# 代码所影响。以下是使用组合运算符将函数列表合并为单个操作的示例。

```
let listOfFunctions = [
   mult3; 
   square;
   add2;
   logMsgN "result=";
   ]

// compose all functions in the list into a single one
let allFunctions = List.reduce (>>) listOfFunctions 

//test
allFunctions 5 
```

## 迷你语言

特定领域的语言（DSL）被广泛认可为创建更易读和简洁的代码的技术。函数式方法非常适合这种情况。

如果需要的话，你可以采用完整的"外部"DSL，具有自己的词法分析器、解析器等等，而且有各种适用于 F# 的工具集可以使这一过程变得非常简单。

但在许多情况下，留在 F# 的语法范围内并设计一组"动词"和"名词"来封装我们想要的行为会更容易。

能够简洁地创建新类型，然后针对它们进行匹配，使得快速设置流畅接口变得非常容易。例如，下面是一个使用简单词汇计算日期的小函数。请注意，为了这一个函数，定义了两个新的枚举风格的类型。

```
// set up the vocabulary
type DateScale = Hour | Hours | Day | Days | Week | Weeks
type DateDirection = Ago | Hence

// define a function that matches on the vocabulary
let getDate interval scale direction =
    let absHours = match scale with
                   | Hour | Hours -> 1 * interval
                   | Day | Days -> 24 * interval
                   | Week | Weeks -> 24 * 7 * interval
    let signedHours = match direction with
                      | Ago -> -1 * absHours 
                      | Hence ->  absHours 
    System.DateTime.Now.AddHours(float signedHours)

// test some examples
let example1 = getDate 5 Days Ago
let example2 = getDate 1 Hour Hence

// the C# equivalent would probably be more like this:
// getDate().Interval(5).Days().Ago()
// getDate().Interval(1).Hour().Hence() 
```

上面的示例只有一个"动词"，使用了许多类型作为"名词"。

以下示例演示了如何构建具有许多"动词"的函数式等效的流畅接口。

假设我们正在创建一个具有各种形状的绘图程序。每个形状都有颜色、大小、标签和点击时执行的操作，并且我们希望使用流畅接口来配置每个形状。

这是 C# 中用于流畅接口的简单方法链的示例：

```
FluentShape.Default
   .SetColor("red")
   .SetLabel("box")
   .OnClick( s => Console.Write("clicked") ); 
```

现在，“流畅接口”和“方法链”概念实际上只与面向对象设计相关。在像 F# 这样的函数式语言中，最接近的相当于使用管道运算符将一组函数链接在一起。

让我们从底层的 Shape 类型开始：

```
// create an underlying type
type FluentShape = {
    label : string; 
    color : string; 
    onClick : FluentShape->FluentShape // a function type
    } 
```

我们将添加一些基本的函数：

```
let defaultShape = 
    {label=""; color=""; onClick=fun shape->shape}

let click shape = 
    shape.onClick shape

let display shape = 
    printfn "My label=%s and my color=%s" shape.label shape.color
    shape   //return same shape 
```

要使"方法链"工作，每个函数都应该返回一个可以在链中使用的对象。因此，你会发现"`display`"函数返回形状，而不是什么都不返回。

接下来，我们创建一些辅助函数，将它们公开为"迷你语言"，并将被语言的用户用作构建块。

```
let setLabel label shape = 
   {shape with FluentShape.label = label}

let setColor color shape = 
   {shape with FluentShape.color = color}

//add a click action to what is already there
let appendClickAction action shape = 
   {shape with FluentShape.onClick = shape.onClick >> action} 
```

注意，`appendClickAction`接受一个函数作为参数，并将其与现有的点击操作组合起来。当你开始深入研究函数式的重用方法时，你会看到更多像这样的"高阶函数"，即作用于其他函数的函数。像这样组合函数是理解函数式编程方法的关键之一。

现在作为这个“小语言”的用户，我可以将基础辅助函数组合成自己更复杂的函数，创建自己的函数库。（在 C# 中，这种事情可能使用扩展方法完成。）

```
// Compose two "base" functions to make a compound function.
let setRedBox = setColor "red" >> setLabel "box" 

// Create another function by composing with previous function.
// It overrides the color value but leaves the label alone.
let setBlueBox = setRedBox >> setColor "blue"  

// Make a special case of appendClickAction
let changeColorOnClick color = appendClickAction (setColor color) 
```

然后，我可以将这些函数组合在一起，以创建具有所需行为的对象。

```
//setup some test values
let redBox = defaultShape |> setRedBox
let blueBox = defaultShape |> setBlueBox 

// create a shape that changes color when clicked
redBox 
    |> display
    |> changeColorOnClick "green"
    |> click
    |> display  // new version after the click

// create a shape that changes label and color when clicked
blueBox 
    |> display
    |> appendClickAction (setLabel "box2" >> setColor "green")  
    |> click
    |> display  // new version after the click 
```

在第二种情况下，我实际上将两个函数传递给 `appendClickAction`，但我先将它们组合成一个。这种事情在结构良好的函数库中非常容易做到，但在没有使用嵌套 lambda 的情况下，在 C# 中做到这一点非常困难。

这是一个更复杂的例子。我们将创建一个名为 "`showRainbow`" 的函数，对彩虹中的每种颜色进行设置并显示形状。

```
let rainbow =
    ["red";"orange";"yellow";"green";"blue";"indigo";"violet"]

let showRainbow = 
    let setColorAndDisplay color = setColor color >> display 
    rainbow 
    |> List.map setColorAndDisplay 
    |> List.reduce (>>)

// test the showRainbow function
defaultShape |> showRainbow 
```

请注意，函数变得更加复杂，但代码量仍然相当少。其中一个原因是在进行函数组合时，函数参数通常可以被忽略，这减少了视觉杂乱。例如，"`showRainbow`" 函数确实将形状作为参数，但没有明确显示！这种参数省略称为“无点”风格，并将在 "思考函数式" 系列中进一步讨论

# 简洁性的模式匹配

# 简洁性的模式匹配

到目前为止，我们已经在 `match..with` 表达式中看到了模式匹配逻辑，在那里它似乎只是一个 switch/case 语句。但实际上，模式匹配更加通用，它可以以多种方式比较表达式，匹配值、条件和类型，然后同时分配或提取值。

模式匹配将在后续帖子中深入讨论，但首先，我们来看一看它如何帮助简洁性。我们将研究模式匹配用于将值绑定到表达式（函数等价于分配给变量）的方式。

在以下示例中，我们直接绑定到元组和列表的内部成员：

```
//matching tuples directly
let firstPart, secondPart, _ =  (1,2,3)  // underscore means ignore

//matching lists directly
let elem1::elem2::rest = [1..10]       // ignore the warning for now

//matching lists inside a match..with
let listMatcher aList = 
    match aList with
    | [] -> printfn "the list is empty" 
    | [firstElement] -> printfn "the list has one element %A " firstElement 
    | [first; second] -> printfn "list is %A and %A" first second 
    | _ -> printfn "the list has more than two elements"

listMatcher [1;2;3;4]
listMatcher [1;2]
listMatcher [1]
listMatcher [] 
```

您还可以将值绑定到诸如记录之类的复杂结构的内部。在以下示例中，我们将创建一个 "`Address`" 类型，然后创建一个包含地址的 "`Customer`" 类型。接下来，我们将创建一个客户值，然后匹配各种属性。

```
// create some types
type Address = { Street: string; City: string; }   
type Customer = { ID: int; Name: string; Address: Address}   

// create a customer 
let customer1 = { ID = 1; Name = "Bob"; 
      Address = {Street="123 Main"; City="NY" } }     

// extract name only
let { Name=name1 } =  customer1 
printfn "The customer is called %s" name1

// extract name and id 
let { ID=id2; Name=name2; } =  customer1 
printfn "The customer called %s has id %i" name2 id2

// extract name and address
let { Name=name3;  Address={Street=street3}  } =  customer1   
printfn "The customer is called %s and lives on %s" name3 street3 
```

在最后一个示例中，请注意我们如何可以直接访问 `Address` 子结构并提取出街道以及客户姓名。

处理嵌套结构、仅提取所需字段并将它们分配给值的能力，所有这些都可以在单个步骤中完成，非常有用。它消除了相当多的编码繁琐，也是 F# 代码典型简洁的另一个因素。

# 便利

# 便利

在接下来的一系列帖子中，我们将探讨 F# 的一些更多功能，我将其归为“便利”主题下。这些功能不一定会导致更简洁的代码，但它们确实消除了在 C# 中需要的大量繁琐和样板代码。

+   **类型的有用的“开箱即用”行为**。你创建的大多数类型将立即具有一些有用的行为，例如不可变性和内置相等性 —— 这些功能在 C# 中必须显式编码。

+   **所有函数都是“接口”**，这意味着函数的工作方式隐含地扮演着对象导向设计中接口扮演的许多角色。同样，许多对象导向设计模式在函数式范式中是不必要的或微不足道的。

+   **部分应用**。具有许多参数的复杂函数可以固定或“烘焙”部分参数，但仍然保持其他参数开放。

+   **活动模式**。活动模式是一种特殊的模式，其中模式可以动态匹配或检测，而不是静态的。它们非常适合简化频繁使用的解析和分组行为。

# 类型的开箱即用行为

# 类型的开箱即用行为

F# 的一个好处是，大多数类型立即具有一些有用的“开箱即用”行为，例如不可变性和内置相等性，这些功能在 C# 中通常需要显式编码。

所谓的“大多数”F#类型指的是核心的“结构”类型，例如元组、记录、联合、选项、列表等。类和其他一些类型已经被添加以帮助与.NET 集成，但失去了一些结构类型的功能。

这些核心类型的内置功能包括：

+   不可变性

+   在调试时进行漂亮的打印

+   相等性

+   比较

下面将详细介绍每一个。

## F# 类型具有内置的不可变性

在 C# 和 Java 中，创建不可变类已经成为良好的做法。在 F# 中，你可以免费得到这一点。

这是 F# 中的一个不可变类型：

```
type PersonalName = {FirstName:string; LastName:string} 
```

以下是相同类型在 C# 中通常的编码方式：

```
class ImmutablePersonalName
{
    public ImmutablePersonalName(string firstName, string lastName) {
        this.FirstName = firstName;
        this.LastName = lastName;
    }

    public string FirstName { get; private set; }
    public string LastName { get; private set; }
} 
```

这需要 10 行来完成与 F# 中的 1 行相同的事情。

## 大多数 F# 类型都具有内置的漂亮打印功能

在 F# 中，你不必为大多数类型重写 `ToString()` —— 你可以免费获得漂亮打印！

当运行之前的示例时，你可能已经见过这个了。这里是另一个简单的例子：

```
type USAddress = 
   {Street:string; City:string; State:string; Zip:string}
type UKAddress = 
   {Street:string; Town:string; PostCode:string}
type Address = US of USAddress | UK of UKAddress
type Person = 
   {Name:string; Address:Address}

let alice = {
   Name="Alice"; 
   Address=US {Street="123 Main";City="LA";State="CA";Zip="91201"}}
let bob = {
   Name="Bob"; 
   Address=UK {Street="221b Baker St";Town="London";PostCode="NW1 6XE"}} 

printfn "Alice is %A" alice
printfn "Bob is %A" bob 
```

输出是：

```
Alice is {Name = "Alice";
 Address = US {Street = "123 Main";
               City = "LA";
               State = "CA";
               Zip = "91201";};} 
```

## 大多数 F# 类型都具有内置的结构相等性

在 C# 中，你经常需要实现 `IEquatable` 接口，以便可以在对象之间测试相等性。例如，在使用对象作为字典键时就需要这样做。

在 F# 中，对于大多数 F# 类型，你可以免费获得这个。例如，使用上面的 `PersonalName` 类型，我们可以立即比较两个姓名。

```
type PersonalName = {FirstName:string; LastName:string}
let alice1 = {FirstName="Alice"; LastName="Adams"}
let alice2 = {FirstName="Alice"; LastName="Adams"}
let bob1 = {FirstName="Bob"; LastName="Bishop"}

//test
printfn "alice1=alice2 is %A" (alice1=alice2)
printfn "alice1=bob1 is %A" (alice1=bob1) 
```

## 大多数 F# 类型是自动可比较的

在 C# 中，你经常需要实现 `IComparable` 接口，以便对对象进行排序。

同样，在 F# 中，对于大多数 F# 类型，你可以免费获得这个。例如，这里是一副简单的卡牌的定义。

```
 type Suit = Club | Diamond | Spade | Heart
type Rank = Two | Three | Four | Five | Six | Seven | Eight 
            | Nine | Ten | Jack | Queen | King | Ace 
```

我们可以编写一个函数来测试比较逻辑：

```
let compareCard card1 card2 = 
    if card1 < card2 
    then printfn "%A is greater than %A" card2 card1 
    else printfn "%A is greater than %A" card1 card2 
```

让我们看看它是如何工作的：

```
let aceHearts = Heart, Ace
let twoHearts = Heart, Two
let aceSpades = Spade, Ace

compareCard aceHearts twoHearts 
compareCard twoHearts aceSpades 
```

请注意，红心的 A 自动大于红心的 2，因为“Ace”等级值在“Two”等级值之后。

但也要注意，红心的两对牌自动比黑桃的 A 对牌要大，因为首先比较的是花色部分，而“红心”花色值在“黑桃”值之后。

这是一手扑克牌的例子：

```
let hand = [ Club,Ace; Heart,Three; Heart,Ace; 
             Spade,Jack; Diamond,Two; Diamond,Ace ]

//instant sorting!
List.sort hand |> printfn "sorted hand is (low to high) %A" 
```

而且作为一个附带好处，你还免费获得了 min 和 max！

```
List.max hand |> printfn "high card is %A"
List.min hand |> printfn "low card is %A" 
```

# 函数作为接口

# 函数作为接口

函数式编程的一个重要方面是，在某种程度上，所有函数都是“接口”，这意味着函数在对象导向设计中扮演的许多角色在函数工作方式中是隐含的。

实际上，“针对接口编程，而不是实现”这一关键设计准则是在 F#中免费获得的。

要看看这是如何工作的，让我们比较一下 C#和 F#中相同的设计模式。例如，在 C#中，我们可能想要使用“装饰器模式”来增强一些核心代码。

假设我们有一个计算器接口：

```
interface ICalculator 
{
   int Calculate(int input);
} 
```

然后是一个具体的实现：

```
class AddingCalculator: ICalculator
{
   public int Calculate(int input) { return input + 1; }
} 
```

然后，如果我们想要添加日志记录，我们可以将核心计算器实现包装在一个日志记录包装器中。

```
class LoggingCalculator: ICalculator
{
   ICalculator _innerCalculator;

   LoggingCalculator(ICalculator innerCalculator)
   {
      _innerCalculator = innerCalculator;
   }

   public int Calculate(int input) { 
      Console.WriteLine("input is {0}", input);
      var result  = _innerCalculator.Calculate(input);
      Console.WriteLine("result is {0}", result);
      return result; 
   }
} 
```

到目前为止，一切都很简单。但请注意，为了使这个工作，我们必须为类定义一个接口。如果没有`ICalculator`接口，那么必须对现有代码进行改造。

这就是 F# 的闪亮之处。在 F# 中，你可以做到同样的事情，而不必首先定义接口。只要签名相同，任何函数都可以被透明地替换为任何其他函数。

这是等效的 F# 代码。

```
let addingCalculator input = input + 1

let loggingCalculator innerCalculator input = 
   printfn "input is %A" input
   let result = innerCalculator input
   printfn "result is %A" result
   result 
```

换句话说，函数的签名 *就是* 接口。

## 通用包装器

更好的是，默认情况下，F# 日志记录代码可以完全通用化，以便适用于*任何*函数。以下是一些示例：

```
let add1 input = input + 1
let times2 input = input * 2

let genericLogger anyFunc input = 
   printfn "input is %A" input   //log the input
   let result = anyFunc input    //evaluate the function
   printfn "result is %A" result //log the result
   result                        //return the result

let add1WithLogging = genericLogger add1
let times2WithLogging = genericLogger times2 
```

新的“包装”函数可以在原始函数可以使用的任何地方使用——没人能分辨出区别！

```
// test
add1WithLogging 3
times2WithLogging 3

[1..5] |> List.map add1WithLogging 
```

完全相同的通用包装方法可以用于其他事物。例如，这是一个计时函数的通用包装器。

```
let genericTimer anyFunc input = 
   let stopwatch = System.Diagnostics.Stopwatch()
   stopwatch.Start() 
   let result = anyFunc input  //evaluate the function
   printfn "elapsed ms is %A" stopwatch.ElapsedMilliseconds
   result

let add1WithTimer = genericTimer add1WithLogging 

// test
add1WithTimer 3 
```

这种通用封装的能力是函数式方法的一个很大的便利之处。你可以取任何函数并基于它创建一个类似的函数。只要新函数的输入和输出与原始函数完全相同，新函数就可以在任何地方替代原始函数。还有一些更多的例子：

+   编写一个通用的缓存包装器以使慢函数的值仅计算一次也很容易。

+   编写一个通用的“延迟”包装器以使函数仅在需要结果时被调用也很容易

## 策略模式

我们可以将这种相同的方法应用到另一个常见的设计模式上，即“策略模式”。

让我们使用继承的熟悉例子：一个带有`Cat`和`Dog`子类的`Animal`超类，每个子类都覆盖了一个`MakeNoise()`方法以发出不同的声音。

在真正的函数式设计中，没有子类，而是 `Animal` 类将具有一个通过构造函数传入的 `NoiseMaking` 函数。这种方法与 OO 设计中的 "策略" 模式完全相同。

```
type Animal(noiseMakingStrategy) = 
   member this.MakeNoise = 
      noiseMakingStrategy() |> printfn "Making noise %s" 

// now create a cat 
let meowing() = "Meow"
let cat = Animal(meowing)
cat.MakeNoise

// .. and a dog
let woofOrBark() = if (System.DateTime.Now.Second % 2 = 0) 
                   then "Woof" else "Bark"
let dog = Animal(woofOrBark)
dog.MakeNoise
dog.MakeNoise  //try again a second later 
```

注意，再次强调，我们不必首先定义任何 `INoiseMakingStrategy` 接口。任何具有正确签名的函数都可以工作。因此，在函数模型中，标准的.NET "策略"接口（如 `IComparer`、`IFormatProvider` 和 `IServiceProvider`）变得无关紧要。

许多其他设计模式也可以以同样的方式简化。

# 部分应用

# 部分应用

F# 的一个特别方便的功能是，具有许多参数的复杂函数可以固定或 "烘焙" 其中一些参数，但留下其他参数。在本文中，我们将快速看一下这个在实践中可能如何使用。

让我们从一个非常简单的例子开始说明这是如何工作的。我们将从一个微不足道的函数开始：

```
// define a adding function
let add x y = x + y

// normal use 
let z = add 1 2 
```

但我们也可以做一些奇怪的事情--我们可以只用一个参数调用函数！

```
let add42 = add 42 
```

结果是一个新函数，其中的 "42" 已经固定，并且现在只需要一个参数而不是两个！这种技术称为 "部分应用"，它意味着，对于任何函数，您都可以 "固定" 一些参数，而将其他参数留给稍后填充。

```
// use the new function
add42 2
add42 3 
```

有了这个技能，让我们重新审视一下之前看到的通用记录器：

```
let genericLogger anyFunc input = 
   printfn "input is %A" input   //log the input
   let result = anyFunc input    //evaluate the function
   printfn "result is %A" result //log the result
   result                        //return the result 
```

不幸的是，我已经将日志记录操作硬编码了。理想情况下，我想把这个做得更通用，这样我就可以选择如何进行日志记录。

当然，作为一种函数式编程语言，F# 将通过传递函数来实现这一点。

在这种情况下，我们会将 "before" 和 "after" 回调函数传递给库函数，像这样：

```
let genericLogger before after anyFunc input = 
   before input               //callback for custom behavior
   let result = anyFunc input //evaluate the function
   after result               //callback for custom behavior
   result                     //return the result 
```

您可以看到现在日志记录函数有四个参数。"before"和"after"操作作为显式参数传递，以及函数和它的输入。要在实践中使用这个，我们只需定义函数并将其与最后的 int 参数一起传递给库函数即可：

```
let add1 input = input + 1

// reuse case 1
genericLogger 
    (fun x -> printf "before=%i. " x) // function to call before 
    (fun x -> printfn " after=%i." x) // function to call after
    add1                              // main function
    2                                 // parameter 

// reuse case 2
genericLogger
    (fun x -> printf "started with=%i " x) // different callback 
    (fun x -> printfn " ended with=%i" x) 
    add1                              // main function
    2                                 // parameter 
```

这样更加灵活。我不必每次都创建一个新函数来改变行为--我可以动态定义行为。

但你可能会认为这有点丑陋。一个库函数可能会公开许多回调函数，每次都必须反复传递相同的函数会很不方便。

幸运的是，我们知道这个问题的解决方案。我们可以使用部分应用来修复一些参数。因此，在这种情况下，让我们定义一个新函数，它修复了 `before` 和 `after` 函数，以及 `add1` 函数，但保留了最后一个参数。

```
// define a reusable function with the "callback" functions fixed
let add1WithConsoleLogging = 
    genericLogger
        (fun x -> printf "input=%i. " x) 
        (fun x -> printfn " result=%i" x)
        add1
        // last parameter NOT defined here yet! 
```

现在只需用一个整数调用新的 "wrapper" 函数，所以代码更清晰了。与之前的示例一样，可以在不做任何更改的情况下在任何可以使用原始 `add1` 函数的地方使用它。

```
add1WithConsoleLogging 2
add1WithConsoleLogging 3
add1WithConsoleLogging 4
[1..5] |> List.map add1WithConsoleLogging 
```

## 在 C# 中的函数式方法

在经典的面向对象方法中，我们可能会使用继承来完成这种事情。例如，我们可能有一个抽象的`LoggerBase`类，其中包含"`before`"和"`after`"的虚拟方法以及要执行的函数。然后，为了实现特定的行为，我们会创建一个新的子类，并根据需要重写虚拟方法。

但是，在面向对象设计中，经典的风格继承现在越来越不受欢迎，对象的组合被更加青睐。而且，实际上，在“现代”的 C#中，我们可能会像 F#一样编写代码，无论是使用事件还是通过传递函数来实现。 

下面是将 F#代码翻译为 C#的代码（请注意，我不得不为每个操作指定类型）。

```
public class GenericLoggerHelper<TInput, TResult>
{
    public TResult GenericLogger(
        Action<TInput> before,
        Action<TResult> after,
        Func<TInput, TResult> aFunc,
        TInput input)
    {
        before(input);             //callback for custom behavior
        var result = aFunc(input); //do the function
        after(result);             //callback for custom behavior
        return result;
    }
} 
```

并且这是它的使用方式：

```
[NUnit.Framework.Test]
public void TestGenericLogger() {
    var sut = new GenericLoggerHelper<int, int>();
    sut.GenericLogger(
        x => Console.Write("input={0}. ", x),
        x => Console.WriteLine(" result={0}", x),
        x => x + 1,
        3);
} 
```

在 C#中，当使用 LINQ 库时，这种编程风格是必需的，但许多开发人员并没有完全接受它，以使他们自己的代码更通用和适应性更强。而且，需要的丑陋的`Action<>`和`Func<>`类型声明也没有帮助。但这确实可以使代码更具可重用性。

# 主动模式

# 主动模式

F#有一种特殊类型的模式匹配称为“主动模式”，其中模式可以动态解析或检测。与普通模式一样，从调用者的角度来看，匹配和输出被合并为单个步骤。

这是一个使用主动模式将字符串解析为 int 或 bool 的示例。

```
// create an active pattern
let (|Int|_|) str =
   match System.Int32.TryParse(str) with
   | (true,int) -> Some(int)
   | _ -> None

// create an active pattern
let (|Bool|_|) str =
   match System.Boolean.TryParse(str) with
   | (true,bool) -> Some(bool)
   | _ -> None 
```

你现在不需要担心用于定义主动模式的复杂语法？这只是一个例子，让你看看它们是如何使用的。

一旦这些模式被设置好，它们就可以作为正常的"`match..with`"表达式的一部分使用。

```
// create a function to call the patterns
let testParse str = 
    match str with
    | Int i -> printfn "The value is an int '%i'" i
    | Bool b -> printfn "The value is a bool '%b'" b
    | _ -> printfn "The value '%s' is something else" str

// test
testParse "12"
testParse "true"
testParse "abc" 
```

你可以看到从调用者的角度来看，与`Int`或`Bool`的匹配是透明的，尽管在幕后进行了解析。

一个类似的示例是使用正则表达式的主动模式，以便在单个步骤中匹配正则表达式模式并返回匹配的值。

```
// create an active pattern
open System.Text.RegularExpressions
let (|FirstRegexGroup|_|) pattern input =
   let m = Regex.Match(input,pattern) 
   if (m.Success) then Some m.Groups.[1].Value else None 
```

再次强调，一旦设置了这种模式，它就可以作为正常匹配表达式的一部分透明地使用。

```
// create a function to call the pattern
let testRegex str = 
    match str with
    | FirstRegexGroup "http://(.*?)/(.*)" host -> 
           printfn "The value is a url and the host is %s" host
    | FirstRegexGroup ".*?@(.*)" host -> 
           printfn "The value is an email and the host is %s" host
    | _ -> printfn "The value '%s' is something else" str

// test
testRegex "http://google.com/test"
testRegex "alice@hotmail.com" 
```

并且为了好玩，这里还有一个：著名的[FizzBuzz 挑战](http://www.codinghorror.com/blog/2007/02/why-cant-programmers-program.html)使用主动模式编写。

```
// setup the active patterns
let (|MultOf3|_|) i = if i % 3 = 0 then Some MultOf3 else None
let (|MultOf5|_|) i = if i % 5 = 0 then Some MultOf5 else None

// the main function
let fizzBuzz i = 
  match i with
  | MultOf3 & MultOf5 -> printf "FizzBuzz, " 
  | MultOf3 -> printf "Fizz, " 
  | MultOf5 -> printf "Buzz, " 
  | _ -> printf "%i, " i

// test
[1..20] |> List.iter fizzBuzz 
```

# 正确性

# 正确性

作为一个程序员，你不断地评判着你自己和其他人编写的代码。在理想的情况下，你应该能够看一段代码并轻松地理解它确切地做了什么；当然，简洁、清晰和可读性是其中的一个重要因素。

但更重要的是，你必须能够说服自己代码*确实完成了它应该完成的工作*。当你编写程序时，你不断地思考代码的正确性，你脑海中的小型编译器正在检查代码是否有错误和可能的错误。

如何利用编程语言帮助你实现这一点？

像 C#这样的现代命令式语言提供了许多你已经熟悉的方法：类型检查、作用域和命名规则、访问修饰符等等。而且，在最近的版本中，还有静态代码分析和代码合约。

所有这些技术意味着编译器可以承担大部分检查正确性的负担。如果你犯了一个错误，编译器会提醒你。

但是 F#有一些额外的功能，可以对确保正确性产生巨大的影响。接下来的几篇文章将专注于其中的四个：

+   **不可变性**，使代码的行为更加可预测。

+   **穷尽模式匹配**，可以在编译时捕获许多常见错误。

+   **严格的类型系统**，它是你的朋友，而不是你的敌人。你几乎可以将静态类型检查看作是即时的“编译时单元测试”。

+   **一种富有表现力的类型系统**，可以帮助你“使非法状态不可表示”。我们将看到如何设计一个真实世界的示例来演示这一点。

[* 感谢 Jane Street 的 Yaron Minsky 提供这句话。]

# 不可变性

# 不可变性

要了解为什么不可变性很重要，让我们从一个小例子开始。

这是一些处理数字列表的简单 C#代码。

```
public List<int> MakeList() {
   return new List<int> {1,2,3,4,5,6,7,8,9,10};
}

public List<int> OddNumbers(List<int> list) { 
   // some code
}

public List<int> EvenNumbers(List<int> list) { 
   // some code
} 
```

现在让我来测试一下：

```
public void Test() { 
   var odds = OddNumbers(MakeList()); 
   var evens = EvenNumbers(MakeList());
   // assert odds = 1,3,5,7,9 -- OK!
   // assert evens = 2,4,6,8,10 -- OK!
} 
```

一切都很顺利，测试通过了，但我注意到我两次创建了列表？我肯定应该重构掉这个吧？所以我进行了重构，这是新的改进版本：

```
public void RefactoredTest() { 
   var list = MakeList();
   var odds = OddNumbers(list); 
   var evens = EvenNumbers(list);
   // assert odds = 1,3,5,7,9 -- OK!
   // assert evens = 2,4,6,8,10 -- FAIL!
} 
```

但现在测试突然失败了！为什么重构会导致测试失败？仅仅通过查看代码就能知道吗？

答案当然是列表是可变的，并且很可能`OddNumbers`函数在其过滤逻辑中做出了破坏性的更改。当然，为了确保，我们必须检查`OddNumbers`函数内部的代码。

换句话说，当我调用`OddNumbers`函数时，我无意中创建了不良的副作用。

有没有办法确保这种情况不会发生？有 —— 如果函数使用了`IEnumerable`的话：

```
public IEnumerable<int> MakeList() {}
public List<int> OddNumbers(IEnumerable<int> list) {} 
public List<int> EvenNumbers(IEnumerable <int> list) {} 
```

在这种情况下，我们可以确信调用`OddNumbers`函数不可能对列表产生任何影响，而`EvenNumbers`会正确工作。更重要的是，我们可以仅仅通过查看函数的签名就知道这一点，而不必检查函数的内部。如果你试图通过对列表进行赋值来使其中一个函数出现错误行为，那么编译时会立即报错。

所以在这种情况下`IEnumerable`可以帮助，但如果我使用`IEnumerable<Person>`而不是`IEnumerable<int>`这样的类型会怎样呢？我能像现在这样确信这些函数不会有意外的副作用吗？

## 不可变性的重要性的原因

上面的示例展示了为什么不可变性是有帮助的。实际上，这只是冰山一角。有许多原因说明为什么不可变性很重要：

+   不可变数据使代码更可预测

+   不可变数据更容易处理

+   不可变数据迫使你使用“转换”方法

首先，不可变性使代码**可预测**。如果数据是不可变的，就不会有副作用。如果没有副作用，就更容易推理代码的正确性。

当你有两个作用于不可变数据的函数时，你不必担心调用它们的顺序，或者一个函数是否会干扰另一个函数的输入。在传递数据时，你可以放心（例如，你不必担心在哈希表中使用对象作为键并且其哈希码发生变化）。

实际上，不可变性之所以是一个好主意，原因与全局变量是一个坏主意相同：数据应尽可能保持本地化，应避免副作用。

其次，不可变性更**易于处理**。如果数据是不可变的，许多常见任务变得更加容易。编写代码更容易，维护更容易。需要更少的单元测试（只需检查函数在隔离环境中是否有效），模拟也更容易。并发性更简单，因为你不必担心使用锁来避免更新冲突（因为没有更新）。

最后，默认使用不可变性意味着你开始以不同的方式思考编程。你倾向于考虑**转换**数据而不是就地突变它。

SQL 查询和 LINQ 查询是这种“转换”方法的好例子。在这两种情况下，你总是通过各种函数（选择、过滤、排序）转换原始数据，而不是修改原始数据。

当一个程序使用转换方法设计时，结果往往更加优雅、模块化和可扩展。而恰好，转换方法也与面向函数的范式完美契合。

## F#如何实现不可变性

我们之前看到，不可变值和类型在 F#中是默认的：

```
// immutable list
let list = [1;2;3;4]    

type PersonalName = {FirstName:string; LastName:string}
// immutable person
let john = {FirstName="John"; LastName="Doe"} 
```

由于这个原因，F#有许多技巧可以让生活更轻松，并优化底层代码。

首先，由于无法修改数据结构，当你想要更改它时，必须复制它。F#使得仅使用你想要的更改轻松复制另一个数据结构：

```
let alice = {john with FirstName="Alice"} 
```

复杂数据结构实现为链表或类似结构，以便共享结构的常见部分。

```
// create an immutable list
let list1 = [1;2;3;4]   

// prepend to make a new list
let list2 = 0::list1    

// get the last 4 of the second list 
let list3 = list2.Tail

// the two lists are the identical object in memory!
System.Object.ReferenceEquals(list1,list3) 
```

这种技术确保，虽然你的代码中可能看起来有数百个列表的副本，但它们实际上都在幕后共享同一内存。

## 可变数据

F#对不可变性并不教条；它支持使用`mutable`关键字的可变数据。但打开可变性是一个明确的决定，是与默认值偏离的行为，通常只在特殊情况下才需要，比如优化、缓存等，或者处理.NET 库时。

在实践中，一个严肃的应用程序如果涉及混乱的用户界面、数据库、网络等，就必然会有一些可变状态。但是 F# 鼓励最小化这种可变状态。通常情况下，你仍然可以设计你的核心业务逻辑来使用不可变数据，带来所有相应的好处。

# 详尽的模式匹配

# 详尽的模式匹配

我们之前简要提到，在模式匹配时有一个要求，即匹配所有可能的情况。这实际上是一种确保正确性的非常强大的技术。

让我们再次比较一些 C# 和 F#。这里有一些使用 switch 语句处理不同状态类型的 C# 代码。

```
enum State { New, Draft, Published, Inactive, Discontinued }
void HandleState(State state) {
    switch (state)
    {
        case State.Inactive: // code for Inactive
            break;
        case State.Draft: // code for Draft
            break;
        case State.New: // code for New
            break;
        case State.Discontinued: // code for Discontinued
            break;
    }
} 
```

这段代码会编译，但显然存在一个错误！编译器看不到它？你能看到吗？如果你能看到，并且修复了它，如果我添加了另一个 `State` 到列表中，它会保持修复吗？

这是 F# 的等价代码：

```
type State = New | Draft | Published | Inactive | Discontinued
let handleState state = 
   match state with
   | Inactive -> () // code for Inactive
   | Draft -> () // code for Draft
   | New -> () // code for New
   | Discontinued -> () // code for Discontinued 
```

现在尝试运行这段代码。编译器告诉你什么？

详尽匹配总是会做的事情，这意味着编译器会立即检测到某些常见的错误：

+   一个缺失的情况（通常是由于需求变更或重构而添加了新选择导致的）。

+   一个不可能的情况（当现有选择被移除时）。

+   一个多余的情况，永远不会被触发（该情况已经包含在先前的情况中——有时这可能不明显）。

现在让我们看一些真实例子，看看详尽匹配如何帮助你编写正确的代码。

## 使用 Option 类型避免空值

我们将从一个极其常见的场景开始，即调用者应始终检查无效情况，即测试空值。一个典型的 C# 程序中充斥着这样的代码：

```
if (myObject != null)
{
  // do something
} 
```

不幸的是，编译器不要求进行这个测试。只需有一段代码忘记执行此操作，程序就会崩溃。多年来，大量的编程工作已经致力于处理空值——甚至有人称空值的发明为[十亿美元的错误](http://www.infoq.com/presentations/Null-References-The-Billion-Dollar-Mistake-Tony-Hoare)！

在纯粹的 F# 中，空值不能意外存在。一个字符串或对象在创建时必须始终被分配给某个东西，并且在此后是不可变的。

然而，有许多情况下，*设计意图* 是区分有效值和无效值，并且需要调用者处理这两��情况。

在 C# 中，可以通过使用可空值类型（如 `Nullable<int>`）在某些情况下管理这个问题，以明确设计决策。当遇到可空值时，编译器会强制你意识到它。然后你可以在使用之前测试值的有效性。但是对于标准类（即引用类型），可空值不起作用，而且很容易无意中绕过测试，直接调用 `Value`。

在 F#中，有一个类似但更强大的概念来传达设计意图：名为`Option`的通用包装类型，有两种选择：`Some`或`None`。`Some`选择包装一个有效值，而`None`表示一个缺失的值。

这里有一个例子，如果文件存在，则返回`Some`，但如果文件丢失，则返回`None`。

```
let getFileInfo filePath =
   let fi = new System.IO.FileInfo(filePath)
   if fi.Exists then Some(fi) else None

let goodFileName = "good.txt"
let badFileName = "bad.txt"

let goodFileInfo = getFileInfo goodFileName // Some(fileinfo)
let badFileInfo = getFileInfo badFileName   // None 
```

如果我们想对这些值做任何事情，我们必须始终处理两种可能的情况。

```
match goodFileInfo with
  | Some fileInfo -> 
      printfn "the file %s exists" fileInfo.FullName
  | None -> 
      printfn "the file doesn't exist" 

match badFileInfo with
  | Some fileInfo -> 
      printfn "the file %s exists" fileInfo.FullName
  | None -> 
      printfn "the file doesn't exist" 
```

我们别无选择。不处理某种情况是编译时错误，而不是运行时错误。通过避免空值，并在这种方式中使用`Option`类型，F#完全消除了大量的空引用异常。

[注意：F#确实允许您在不进行测试的情况下访问值，就像 C#一样，但这被认为是极其不良的做法。]

## 边界情况的穷尽模式匹配

这里有一些创建列表的 C#代码，通过对输入列表中的数字进行平均化来创建列表：

```
public IList<float> MovingAverages(IList<int> list) {
    var averages = new List<float>();
    for (int i = 0; i < list.Count; i++)
    {
        var avg = (list[i] + list[i+1]) / 2;
        averages.Add(avg);
    }
    return averages;
} 
```

它可以正确编译，但实际上有一些问题。你能快速找到它们吗？如果你幸运的话，你的单元测试会帮你找到它们，假设你已经考虑到了所有的边界情况。

现在让我们在 F#中尝试同样的事情：

```
let rec movingAverages list = 
    match list with
    // if input is empty, return an empty list
    | [] -> []
    // otherwise process pairs of items from the input 
    | x::y::rest -> 
        let avg = (x+y)/2.0 
        //build the result by recursing the rest of the list
        avg :: movingAverages (y::rest) 
```

这段代码也有一个错误。但与 C#不同，除非我修复它，否则这段代码甚至不会编译。编译器会告诉我，我没有处理当列表中只有一个项目时的情况。它不仅发现了一个错误，还揭示了需求中的一个空白：当只有一个项目时应该发生什么？

这是修复后的版本：

```
let rec movingAverages list = 
    match list with
    // if input is empty, return an empty list
    | [] -> []
    // otherwise process pairs of items from the input 
    | x::y::rest -> 
        let avg = (x+y)/2.0 
        //build the result by recursing the rest of the list
        avg :: movingAverages (y::rest)
    // for one item, return an empty list
    | [_] -> []

// test
movingAverages [1.0]
movingAverages [1.0; 2.0]
movingAverages [1.0; 2.0; 3.0] 
```

作为额外的好处，F#代码也更具自我描述性。它明确描述了每种情况的后果。在 C#代码中，如果列表为空或只有一个项目，发生了什么根本不明显。你必须仔细阅读代码才能找出。

## 穷尽模式匹配作为一种错误处理技术

所有选择必须匹配的事实也可以用作一个有用的替代方案来抛出异常。例如考虑以下常见情况：

+   应用程序的最底层有一个实用函数，它打开一个文件并对其执行任意操作（您将其作为回调函数传入）。

+   然后将结果传递回到顶层的各个层。

+   客户端调用顶层代码，处理结果并进行任何错误处理。

在过程式或面向对象语言中，跨代码层传播和处理异常是一个常见问题。顶层函数很难区分它们应该恢复的异常（比如`FileNotFound`）和不需要处理的异常（比如`OutOfMemory`）。在 Java 中，尝试使用已检查异常来解决这个问题，但效果参差不齐。

在函数式世界中，一个常见的技术是创建一个新的结构来保存好的和坏的可能性，而不是在文件丢失时抛出异常。

```
// define a "union" of two different alternatives
type Result<'a, 'b> = 
    | Success of 'a  // 'a means generic type. The actual type
                     // will be determined when it is used.
    | Failure of 'b  // generic failure type as well

// define all possible errors
type FileErrorReason = 
    | FileNotFound of string
    | UnauthorizedAccess of string * System.Exception

// define a low level function in the bottom layer
let performActionOnFile action filePath =
   try
      //open file, do the action and return the result
      use sr = new System.IO.StreamReader(filePath:string)
      let result = action sr  //do the action to the reader
      sr.Close()
      Success (result)        // return a Success
   with      // catch some exceptions and convert them to errors
      | :? System.IO.FileNotFoundException as ex 
          -> Failure (FileNotFound filePath)      
      | :? System.Security.SecurityException as ex 
          -> Failure (UnauthorizedAccess (filePath,ex))  
      // other exceptions are unhandled 
```

该代码演示了`performActionOnFile`如何返回一个`Result`对象，该对象具有两个替代方案：`Success`和`Failure`。而`Failure`替代方案又有两个替代方案：`FileNotFound`和`UnauthorizedAccess`。

现在中间层可以相互调用，传递结果类型而不担心其结构，只要它们不访问它：

```
// a function in the middle layer
let middleLayerDo action filePath = 
    let fileResult = performActionOnFile action filePath
    // do some stuff
    fileResult //return

// a function in the top layer
let topLayerDo action filePath = 
    let fileResult = middleLayerDo action filePath
    // do some stuff
    fileResult //return 
```

由于类型推断，中间层和顶层不需要指定确切的返回类型。如果底层改变了类型定义，中间层不会受到影响。

显然，在某些时候，顶层的客户端确实想要访问结果。这就是强制要求匹配所有模式的要求。客户端必须处理`Failure`情况，否则编译器会抱怨。而且，当处理`Failure`分支时，还必须处理可能的原因。换句话说，这种特殊情况的处理可以在编译时强制执行，而不是在运行时！此外，通过检查原因类型，可能的原因还得到了明确的文档记录。

下面是一个访问顶层的客户端函数的示例：

```
/// get the first line of the file
let printFirstLineOfFile filePath = 
    let fileResult = topLayerDo (fun fs->fs.ReadLine()) filePath

    match fileResult with
    | Success result -> 
        // note type-safe string printing with %s
        printfn "first line is: '%s'" result   
    | Failure reason -> 
       match reason with  // must match EVERY reason
       | FileNotFound file -> 
           printfn "File not found: %s" file
       | UnauthorizedAccess (file,_) -> 
           printfn "You do not have access to the file: %s" file 
```

您可以看到，此代码必须显式处理`Success`和`Failure`情况，然后对于失败情况，它显式处理了不同的原因。如果您想看看如果不处理其中一个情况会发生什么，请尝试注释掉处理`UnauthorizedAccess`的行，看看编译器会说什么。

现在不需要总是显式处理所有可能的情况。在下面的示例中，该函数使用下划线通配符将所有失败原因视为一个。如果我们想要获得严格性的好处，这可能被认为是不良做法，但至少它明确地完成了。

```
/// get the length of the text in the file
let printLengthOfFile filePath = 
   let fileResult = 
     topLayerDo (fun fs->fs.ReadToEnd().Length) filePath

   match fileResult with
   | Success result -> 
      // note type-safe int printing with %i
      printfn "length is: %i" result       
   | Failure _ -> 
      printfn "An error happened but I don't want to be specific" 
```

现在让我们看看所有这些代码如何在实践中运作，进行一些交互式测试。

首先设置一个好文件和一个坏文件。

```
/// write some text to a file
let writeSomeText filePath someText = 
    use writer = new System.IO.StreamWriter(filePath:string)
    writer.WriteLine(someText:string)
    writer.Close()

let goodFileName = "good.txt"
let badFileName = "bad.txt"

writeSomeText goodFileName "hello" 
```

现在进行交互式测试：

```
printFirstLineOfFile goodFileName 
printLengthOfFile goodFileName 

printFirstLineOfFile badFileName 
printLengthOfFile badFileName 
```

我认为您可以看出，这种方法非常吸引人：

+   函数为每个预期情况返回错误类型（如`FileNotFound`），但处理这些类型不需要使调用代码丑陋。

+   对于意外情况（如`OutOfMemory`），函数继续抛出异常，这些异常通常会在程序的顶层被捕获和记录。

这种技术简单而方便。类似（更通用）的方法在函数式编程中很常见。

在 C#中使用这种方法是可行的，但通常是不切实际的，因为缺乏联合类型和类型推断（我们必须在所有地方指定泛型类型）。

## 详尽的模式匹配作为变更管理工具

最后，详尽的模式匹配是确保代码在需求变化或重构期间保持正确性的有价值工具。

假设需求变化，我们需要处理第三种类型的错误："不定"。为了实现这个新需求，将第一个`Result`类型更改如下，并重新评估所有代码。会发生什么？

```
type Result<'a, 'b> = 
    | Success of 'a 
    | Failure of 'b
    | Indeterminate 
```

或者有时候需求变更会删除一个可能的选择。为了模拟这一点，将第一个`Result`类型更改为仅保留一个选择。

```
type Result<'a> = 
    | Success of 'a 
```

现在重新评估其余的代码。现在会发生什么？

这是非常强大的！当我们调整选择时，我们立即知道所有需要被修复以处理变更的地方。这是静态检查类型错误的另一个示例。关于像 F# 这样的函数式语言经常被说成是"如果它编译通过，那么它必定是正确的"。

# 使用类型系统确保代码正确

# 使用类型系统确保代码正确

你熟悉通过像 C# 和 Java 这样的语言进行静态类型检查。在这些语言中，类型检查是直截了当但相当粗糙的，与像 Python 和 Ruby 这样的动态语言的自由相比，它可以被视为一种烦恼。

但在 F# 中，类型系统是你的朋友，而不是你的敌人。你几乎可以将静态类型检查视为即时单元测试？确保你的代码在编译时正确无误。

在早期的帖子中，我们已经看到了在 F# 中使用类型系统可以做些什么：

+   类型及其相关函数提供了抽象来模拟问题领域。因为创建类型很容易，很少有借口可以避免根据给定问题的需要设计它们，与 C# 类不同，很难创建做"所有事情"的"厨房水槽"类型。

+   定义良好的类型有助于维护。由于 F# 使用类型推断，通常可以轻松地重命名或重新构造类型而无需使用重构工具。如果类型以不兼容的方式更改，这几乎肯定会创建编译时错误，有助于追踪任何问题。

+   良好命名的类型提供了有关程序中其角色的即时文档（而此文档永远不会过时）。

在本文和下一篇文章中，我们将重点介绍使用类型系统来帮助编写正确的代码。我将证明，你可以创建设计，以便如果你的代码实际上编译通过，它几乎肯定会按设计工作。

## 使用标准类型检查

在 C# 中，你使用编译时检查来验证你的代码，甚至都不用考虑它。例如，你会放弃`List<string>`以换取普通的`List`吗？或者放弃`Nullable<int>`并被迫使用带有转换的`object`吗？可能不会。

但是，如果你可以有更精细的类型呢？你可以获得更好的编译时检查。而这正是 F# 所提供的。

F# 类型检查器与 C# 类型检查器并没有太大的不同。但是因为创建新类型是如此容易而不会杂乱，你可以更好地表示领域，并且，作为一个有用的副作用，避免许多常见的错误。

这是一个简单的例子：

```
//define a "safe" email address type
type EmailAddress = EmailAddress of string

//define a function that uses it 
let sendEmail (EmailAddress email) = 
   printfn "sent an email to %s" email

//try to send one
let aliceEmail = EmailAddress "alice@example.com"
sendEmail aliceEmail

//try to send a plain string
sendEmail "bob@example.com"   //error 
```

通过将电子邮件地址包装在特殊类型中，我们确保普通字符串不能作为电子邮件特定函数的参数。（实际上，我们还会隐藏 `EmailAddress` 类型的构造函数，以确保只能在第一次创建时创建有效值。）

这里没有什么是不能在 C# 中完成的，但是为了仅此一目的创建一个新值类型会是相当多的工作，因此在 C# 中，可以很容易地偷懒并传递字符串。

## F# 中的其他类型安全功能

在继续讨论“为正确性设计”的主要主题之前，让我们看看 F# 是类型安全的其他一些次要但很酷的方式。

### 使用 printf 进行类型安全的格式化

这是一个小功能，演示了 F# 比 C# 更类型安全的一种方式，并且 F# 编译器如何能够捕捉到在 C# 中仅在运行时检测到的错误。

尝试评估以下内容并查看生成的错误：

```
let printingExample = 
   printf "an int %i" 2                        // ok
   printf "an int %i" 2.0                      // wrong type
   printf "an int %i" "hello"                  // wrong type
   printf "an int %i"                          // missing param

   printf "a string %s" "hello"                // ok
   printf "a string %s" 2                      // wrong type
   printf "a string %s"                        // missing param
   printf "a string %s" "he" "lo"              // too many params

   printf "an int %i and string %s" 2 "hello"  // ok
   printf "an int %i and string %s" "hello" 2  // wrong type
   printf "an int %i and string %s" 2          // missing param 
```

与 C# 不同，编译器分析格式字符串并确定参数的数量和类型应该是什么。

这可以用来约束参数的类型，而无需明确指定它们。因此，例如，在下面的代码中，编译器可以自动推断参数的类型。

```
let printAString x = printf "%s" x
let printAnInt x = printf "%i" x

// the result is:
// val printAString : string -> unit  //takes a string parameter
// val printAnInt : int -> unit       //takes an int parameter 
```

### 测量单位

F# 有能力定义测量单位并将其与浮点数关联起来。测量单位然后作为类型“附加”到浮点数上，并阻止混合不同类型。如果需要，这是另一个非常方便的功能。

```
// define some measures
[<Measure>] 
type cm

[<Measure>] 
type inches

[<Measure>] 
type feet =
   // add a conversion function
   static member toInches(feet : float<feet>) : float<inches> = 
      feet * 12.0<inches/feet>

// define some values
let meter = 100.0<cm>
let yard = 3.0<feet>

//convert to different measure
let yardInInches = feet.toInches(yard)

// can't mix and match!
yard + meter

// now define some currencies
[<Measure>] 
type GBP

[<Measure>] 
type USD

let gbp10 = 10.0<GBP>
let usd10 = 10.0<USD>
gbp10 + gbp10             // allowed: same currency
gbp10 + usd10             // not allowed: different currency
gbp10 + 1.0               // not allowed: didn't specify a currency
gbp10 + 1.0<_>            // allowed using wildcard 
```

### 类型安全的相等性

最后一个例子。在 C# 中，任何类都可以与任何其他类相等（默认情况下使用引用相等）。总的来说，这是一个坏主意！例如，你根本不应该比较一个字符串和一个人。

这是一些完全有效且编译良好的 C# 代码：

```
using System;
var obj = new Object();
var ex = new Exception();
var b = (obj == ex); 
```

如果我们在 F# 中编写相同的代码，我们会得到一个编译时错误：

```
open System
let obj = new Object()
let ex = new Exception()
let b = (obj = ex) 
```

如果你正在测试两种不同类型之间的相等性，那么你可能做错了什么。

在 F# 中，甚至可以完全停止比较类型！这并不像看起来那么愚蠢。对于某些类型，可能没有有用的默认值，或者您可能希望强制相等性基于特定字段而不是整个对象。

这是一个例子：

```
// deny comparison
[<NoEquality; NoComparison>]
type CustomerAccount = {CustomerAccountId: int}

let x = {CustomerAccountId = 1}

x = x       // error!
x.CustomerAccountId = x.CustomerAccountId // no error 
```

# 工作示例：为正确性设计

# 工作示例：为正确性设计

在这篇文章中，我们将看到如何设计正确性（或者至少是根据目前理解的要求进行设计），我指的是一个良好设计的模型的客户端将无法使系统进入非法状态？即不符合要求的状态。你实际上无法创建不正确的代码，因为编译器不会让你这样做。

为了使其工作，我们必须花一些时间来考虑设计，并努力将要求编码到你使用的类型中。如果你只是为所有数据结构使用字符串或列表，你将无法从类型检查中获得任何好处。

我们将使用一个简单的例子。假设你正在设计一个电子商务网站，其中有一个购物车，并且你得到了以下要求。

+   你只能一次付款一个购物车。

+   一旦购物车付款，就不能更改其中的项目。

+   空购物车不能付款。

## C#中的糟糕设计

在 C#中，我们可能认为这已经足够简单，直接开始编码。以下是一种在 C#中看起来一开始似乎还可以的直接实现。

```
public class NaiveShoppingCart<TItem>
{
   private List<TItem> items;
   private decimal paidAmount;

   public NaiveShoppingCart()
   {
      this.items = new List<TItem>();
      this.paidAmount = 0;
   }

   /// Is cart paid for?
   public bool IsPaidFor { get { return this.paidAmount > 0; } }

   /// Readonly list of items
   public IEnumerable<TItem> Items { get {return this.items; } }

   /// add item only if not paid for
   public void AddItem(TItem item)
   {
      if (!this.IsPaidFor)
      {
         this.items.Add(item);
      }
   }

   /// remove item only if not paid for
   public void RemoveItem(TItem item)
   {
      if (!this.IsPaidFor)
      {
         this.items.Remove(item);
      }
   }

   /// pay for the cart
   public void Pay(decimal amount)
   {
      if (!this.IsPaidFor)
      {
         this.paidAmount = amount;
      }
   }
} 
```

不幸的是，这实际上是一个相当糟糕的设计：

+   其中一个要求甚至都没有被满足。你能看出是哪一个吗？

+   它有一个主要的设计缺陷，以及一些次要的缺陷。你能看出它们是什么吗？

这么短的代码中有这么多问题！

如果我们有更复杂的要求，代码有数千行会发生什么？例如，到处重复的片段：

```
if (!this.IsPaidFor) { do something } 
```

看起来如果一些方法发生变化而其他方法没有变化，它将变得非常脆弱。

在阅读下一节之前，想一分钟，你如何在 C#中更好地实现上述要求，以及以下要求：

+   如果你尝试做一些不符合要求的事情，你将得到一个*编译时错误*，而不是运行时错误。例如，你必须创建一个设计，以便你甚至不能从空购物车调用`RemoveItem`方法。

+   任何状态下购物车的内容都应该是不可变的。这样做的好处是，如果我正在支付购物车，即使其他进程同时添加或删除项目，购物车的内容也不会改变。

## F#中的正确设计

让我们退一步看看是否可以想出一个更好的设计。看着这些要求，很明显我们有一个简单的三状态状态机和一些状态转换： 

+   购物车可以是空的、活动的或已付款的

+   当你向空购物车添加项目时，它变为活动状态

+   当你从活动购物车中移除最后一个项目时，它变为空

+   当你为活动购物车付款时，它变为已付款状态

现在我们可以将业务规则添加到这个模型中：

+   你只能向空或活动的购物车添加项目

+   你只能从活动的购物车中删除项目

+   你只能为处于活动状态的购物车付款

这是状态图：

![购物车](img/ShoppingCart.png)

值得注意的是，这些种类的基于状态的模型在商业系统中非常常见。产品开发、客户关系管理、订单处理和其他工作流程通常可以这样建模。

现在我们有了设计，我们可以在 F#中复制它：

```
type CartItem = string    // placeholder for a more complicated type

type EmptyState = NoItems // don't use empty list! We want to
                          // force clients to handle this as a 
                          // separate case. E.g. "you have no 
                          // items in your cart"

type ActiveState = { UnpaidItems : CartItem list; }
type PaidForState = { PaidItems : CartItem list; 
                      Payment : decimal}

type Cart = 
    | Empty of EmptyState 
    | Active of ActiveState 
    | PaidFor of PaidForState 
```

我们为每个状态创建了一个类型，并创建了一个`Cart`类型，它是所有状态中的任意一个的选择。我为每样东西都取了一个不同的名称（例如`PaidItems`和`UnpaidItems`而不仅仅是`Items`），因为这有助于推理引擎，并使代码更具自解释性。

这是一个比之前的示例要长得多的示例！现在不要太担心 F#语法，但我希望您能理解代码的要领，并看到它如何适应整体设计。

也要将代码片段粘贴到脚本文件中，并在出现时自行评估。

接下来，我们可以为每个状态创建操作。需要注意的主要事项是，每个操作始终将一个状态作为输入，并返回一个新的购物车。也就是说，您从一个特定的已知状态开始，但返回的是一个作为三种可能状态之一的选择的`Cart`。

```
// =============================
// operations on empty state
// =============================

let addToEmptyState item = 
   // returns a new Active Cart
   Cart.Active {UnpaidItems=[item]}

// =============================
// operations on active state
// =============================

let addToActiveState state itemToAdd = 
   let newList = itemToAdd :: state.UnpaidItems
   Cart.Active {state with UnpaidItems=newList }

let removeFromActiveState state itemToRemove = 
   let newList = state.UnpaidItems 
                 |> List.filter (fun i -> i<>itemToRemove)

   match newList with
   | [] -> Cart.Empty NoItems
   | _ -> Cart.Active {state with UnpaidItems=newList} 

let payForActiveState state amount = 
   // returns a new PaidFor Cart
   Cart.PaidFor {PaidItems=state.UnpaidItems; Payment=amount} 
```

接下来，我们将操作作为方法附加到状态上。

```
type EmptyState with
   member this.Add = addToEmptyState 

type ActiveState with
   member this.Add = addToActiveState this 
   member this.Remove = removeFromActiveState this 
   member this.Pay = payForActiveState this 
```

我们还可以创建一些购物车级别的辅助方法。在购物车级别，我们必须使用`match..with`表达式显式处理内部状态的每种可能性。

```
let addItemToCart cart item =  
   match cart with
   | Empty state -> state.Add item
   | Active state -> state.Add item
   | PaidFor state ->  
       printfn "ERROR: The cart is paid for"
       cart   

let removeItemFromCart cart item =  
   match cart with
   | Empty state -> 
      printfn "ERROR: The cart is empty"
      cart   // return the cart 
   | Active state -> 
      state.Remove item
   | PaidFor state ->  
      printfn "ERROR: The cart is paid for"
      cart   // return the cart

let displayCart cart  =  
   match cart with
   | Empty state -> 
      printfn "The cart is empty"   // can't do state.Items
   | Active state -> 
      printfn "The cart contains %A unpaid items"
                                                state.UnpaidItems
   | PaidFor state ->  
      printfn "The cart contains %A paid items. Amount paid: %f"
                                    state.PaidItems state.Payment

type Cart with
   static member NewCart = Cart.Empty NoItems
   member this.Add = addItemToCart this 
   member this.Remove = removeItemFromCart this 
   member this.Display = displayCart this 
```

## 测试设计

现在让我们来练习这段代码：

```
let emptyCart = Cart.NewCart
printf "emptyCart="; emptyCart.Display

let cartA = emptyCart.Add "A"
printf "cartA="; cartA.Display 
```

现在我们有一个包含一个物品的活动购物车。请注意，“`cartA`”与“`emptyCart`”是完全不同的对象，并处于不同的状态。

让我们继续：

```
let cartAB = cartA.Add "B"
printf "cartAB="; cartAB.Display

let cartB = cartAB.Remove "A"
printf "cartB="; cartB.Display

let emptyCart2 = cartB.Remove "B"
printf "emptyCart2="; emptyCart2.Display 
```

到目前为止，一切都很好。再次强调，所有这些都是不同状态的不同对象，

让我们测试一下不能从空购物车中移除物品的要求：

```
let emptyCart3 = emptyCart2.Remove "B"    //error
printf "emptyCart3="; emptyCart3.Display 
```

出错了？这正是我们想要的！

现在假设我们想要支付购物车。我们没有在购物车级别创建此方法，因为我们不想告诉客户如何处理所有情况。此方法仅存在于活动状态，因此客户必须显式处理每种情况，并仅在匹配到活动状态时调用`Pay`方法。

首先，我们将尝试为 cartA 支付。

```
//  try to pay for cartA
let cartAPaid = 
    match cartA with
    | Empty _ | PaidFor _ -> cartA 
    | Active state -> state.Pay 100m
printf "cartAPaid="; cartAPaid.Display 
```

结果是一个已支付的购物车。

现在我们将尝试为 emptyCart 支付款项。

```
//  try to pay for emptyCart
let emptyCartPaid = 
    match emptyCart with
    | Empty _ | PaidFor _ -> emptyCart
    | Active state -> state.Pay 100m
printf "emptyCartPaid="; emptyCartPaid.Display 
```

什么也没发生。购物车是空的，因此未调用 Active 分支。我们可能希望在其他分支中引发错误或记录消息，但无论我们做什么，都不能意外地在空购物车上调用`Pay`方法，因为该状态没有可调用的方法！

如果我们意外地尝试为已经支付的购物车支付款项，结果会是一样的。

```
//  try to pay for cartAB 
let cartABPaid = 
    match cartAB with
    | Empty _ | PaidFor _ -> cartAB // return the same cart
    | Active state -> state.Pay 100m

//  try to pay for cartAB again
let cartABPaidAgain = 
    match cartABPaid with
    | Empty _ | PaidFor _ -> cartABPaid  // return the same cart
    | Active state -> state.Pay 100m 
```

您可能会认为上面的客户端代码可能不代表现实世界中的代码？它是行为良好的，并且已经处理了需求。

那么，如果我们有编写不良或恶意客户端代码试图强制支付会发生什么：

```
match cartABPaid with
| Empty state -> state.Pay 100m
| PaidFor state -> state.Pay 100m
| Active state -> state.Pay 100m 
```

如果我们像这样强行执行，我们将获得编译错误。客户端无法创建不符合要求的代码。

## 总结

我们设计了一个简单的购物车模型，其优点远远超过了 C#设计。

+   它与需求非常清晰地对应。这个 API 的客户端无法调用不符合要求的代码。

+   使用状态意味着可能的代码路径数量要比 C# 版本小得多，因此要编写的单元测试要少得多。

+   每个函数都足够简单，可能第一次就能工作，因为与 C# 版本不同，这里没有任何条件语句。

### 对原始的 C# 代码进行分析

现在你已经看过了 F# 代码，我们可以用新的眼光重新审视原始的 C# 代码。如果你想知道，这是我对设计的 C# 购物车示例有什么问题的看法。

*需求未满足*：一个空购物车仍然可以支付。

*主要设计缺陷*：将支付金额重载为 IsPaidFor 的信号意味着零支付金额永远无法锁定购物车。你确定购物车永远不可能是已支付但免费的吗？要求不明确，但如果以后这成为要求呢？需要改变多少代码？

*次要设计缺陷*：当尝试从空购物车中移除项目时应该发生什么？当尝试为已支付的购物车支付时应该发生什么？在这些情况下，我们应该抛出异常，还是只是静默地忽略它们？客户端能够枚举空购物车中的项目是否有意义？按设计来说这不是线程安全的；那么如果在主线程上进行付款时，辅助线程向购物车添加项目会发生什么？

这是相当多的事情需要担心。

F# 设计的好处是这些问题甚至都不存在。因此，这样设计不仅能确保正确的代码，而且还能真正减少确保设计一开始就是无懈可击的认知工作量。

*编译时检查*：原始的 C# 设计将所有状态和转换混合在一个单一的类中，这使得它非常容易出错。更好的方法是创建单独的状态类（比如说带有一个共同基类），这样可以减少复杂性，但是仍然，缺乏内置的“联合”类型意味着你不能静态验证代码是否正确。在 C# 中有一些实现“联合”类型的方法，但这完全不符合惯例，而在 F# 中却很普遍。

## 附录：正确解决方案的 C# 代码

面对这些要求在 C# 中，你可能会立即想到 -- 只需创建一个接口！

但事情并不像你想象的那么简单。我已经写了一篇后续文章来解释为什么：C# 中的购物车示例。

如果你对看看解决方案的 C# 代码感兴趣，下面是它的代码。这段代码满足上述要求，并且像预期的那样在*编译时*保证了正确性。

关键要注意的是，因为 C# 没有联合类型，所以实现使用了一个"fold" 函数，这个函数有三个函数参数，分别对应每种状态。为了使用购物车，调用者传入一组三个 lambda 函数，而（隐藏的）状态决定了发生了什么。

```
var paidCart = cartA.Do(
    // lambda for Empty state
    state => cartA,  
    // lambda for Active state
    state => state.Pay(100),
    // lambda for Paid state
    state => cartA); 
```

这种方法意味着调用者永远不会调用“错误”的函数，例如对于 Empty 状态调用“Pay”，因为 lambda 的参数不支持它。试一下，看看！

```
using System;
using System.Collections.Generic;
using System.Linq;

namespace WhyUseFsharp
{

    public class ShoppingCart<TItem>
    {

        #region ShoppingCart State classes

        /// <summary>
        /// Represents the Empty state
        /// </summary>
        public class EmptyState
        {
            public ShoppingCart<TItem> Add(TItem item)
            {
                var newItems = new[] { item };
                var newState = new ActiveState(newItems);
                return FromState(newState);
            }
        }

        /// <summary>
        /// Represents the Active state
        /// </summary>
        public class ActiveState
        {
            public ActiveState(IEnumerable<TItem> items)
            {
                Items = items;
            }

            public IEnumerable<TItem> Items { get; private set; }

            public ShoppingCart<TItem> Add(TItem item)
            {
                var newItems = new List<TItem>(Items) {item};
                var newState = new ActiveState(newItems);
                return FromState(newState);
            }

            public ShoppingCart<TItem> Remove(TItem item)
            {
                var newItems = new List<TItem>(Items);
                newItems.Remove(item);
                if (newItems.Count > 0)
                {
                    var newState = new ActiveState(newItems);
                    return FromState(newState);
                }
                else
                {
                    var newState = new EmptyState();
                    return FromState(newState);
                }
            }

            public ShoppingCart<TItem> Pay(decimal amount)
            {
                var newState = new PaidForState(Items, amount);
                return FromState(newState);
            }

        }

        /// <summary>
        /// Represents the Paid state
        /// </summary>
        public class PaidForState
        {
            public PaidForState(IEnumerable<TItem> items, decimal amount)
            {
                Items = items.ToList();
                Amount = amount;
            }

            public IEnumerable<TItem> Items { get; private set; }
            public decimal Amount { get; private set; }
        }

        #endregion ShoppingCart State classes

        //====================================
        // Execute of shopping cart proper
        //====================================

        private enum Tag { Empty, Active, PaidFor }
        private readonly Tag _tag = Tag.Empty;
        private readonly object _state;       //has to be a generic object

        /// <summary>
        /// Private ctor. Use FromState instead
        /// </summary>
        private ShoppingCart(Tag tagValue, object state)
        {
            _state = state;
            _tag = tagValue;
        }

        public static ShoppingCart<TItem> FromState(EmptyState state)
        {
            return new ShoppingCart<TItem>(Tag.Empty, state);
        }

        public static ShoppingCart<TItem> FromState(ActiveState state)
        {
            return new ShoppingCart<TItem>(Tag.Active, state);
        }

        public static ShoppingCart<TItem> FromState(PaidForState state)
        {
            return new ShoppingCart<TItem>(Tag.PaidFor, state);
        }

        /// <summary>
        /// Create a new empty cart
        /// </summary>
        public static ShoppingCart<TItem> NewCart()
        {
            var newState = new EmptyState();
            return FromState(newState);
        }

        /// <summary>
        /// Call a function for each case of the state
        /// </summary>
        /// <remarks>
        /// Forcing the caller to pass a function for each possible case means that all cases are handled at all times.
        /// </remarks>
        public TResult Do<TResult>(
            Func<EmptyState, TResult> emptyFn,
            Func<ActiveState, TResult> activeFn,
            Func<PaidForState, TResult> paidForyFn
            )
        {
            switch (_tag)
            {
                case Tag.Empty:
                    return emptyFn(_state as EmptyState);
                case Tag.Active:
                    return activeFn(_state as ActiveState);
                case Tag.PaidFor:
                    return paidForyFn(_state as PaidForState);
                default:
                    throw new InvalidOperationException(string.Format("Tag {0} not recognized", _tag));
            }
        }

        /// <summary>
        /// Do an action without a return value
        /// </summary>
        public void Do(
            Action<EmptyState> emptyFn,
            Action<ActiveState> activeFn,
            Action<PaidForState> paidForyFn
            )
        {
            //convert the Actions into Funcs by returning a dummy value
            Do(
                state => { emptyFn(state); return 0; },
                state => { activeFn(state); return 0; },
                state => { paidForyFn(state); return 0; }
                );
        }

    }

    /// <summary>
    /// Extension methods for my own personal library
    /// </summary>
    public static class ShoppingCartExtension
    {
        /// <summary>
        /// Helper method to Add
        /// </summary>
        public static ShoppingCart<TItem> Add<TItem>(this ShoppingCart<TItem> cart, TItem item)
        {
            return cart.Do(
                state => state.Add(item), //empty case
                state => state.Add(item), //active case
                state => { Console.WriteLine("ERROR: The cart is paid for and items cannot be added"); return cart; } //paid for case
            );
        }

        /// <summary>
        /// Helper method to Remove
        /// </summary>
        public static ShoppingCart<TItem> Remove<TItem>(this ShoppingCart<TItem> cart, TItem item)
        {
            return cart.Do(
                state => { Console.WriteLine("ERROR: The cart is empty and items cannot be removed"); return cart; }, //empty case
                state => state.Remove(item), //active case
                state => { Console.WriteLine("ERROR: The cart is paid for and items cannot be removed"); return cart; } //paid for case
            );
        }

        /// <summary>
        /// Helper method to Display
        /// </summary>
        public static void Display<TItem>(this ShoppingCart<TItem> cart)
        {
            cart.Do(
                state => Console.WriteLine("The cart is empty"),
                state => Console.WriteLine("The active cart contains {0} items", state.Items.Count()),
                state => Console.WriteLine("The paid cart contains {0} items. Amount paid {1}", state.Items.Count(), state.Amount)
            );
        }
    }

    [NUnit.Framework.TestFixture]
    public class CorrectShoppingCartTest
    {
        [NUnit.Framework.Test]
        public void TestCart()
        {
            var emptyCart = ShoppingCart<string>.NewCart();
            emptyCart.Display();

            var cartA = emptyCart.Add("A");  //one item
            cartA.Display();

            var cartAb = cartA.Add("B");  //two items
            cartAb.Display();

            var cartB = cartAb.Remove("A"); //one item
            cartB.Display();

            var emptyCart2 = cartB.Remove("B"); //empty
            emptyCart2.Display();

            Console.WriteLine("Removing from emptyCart");
            emptyCart.Remove("B"); //error

            //  try to pay for cartA
            Console.WriteLine("paying for cartA");
            var paidCart = cartA.Do(
                state => cartA,
                state => state.Pay(100),
                state => cartA);
            paidCart.Display();

            Console.WriteLine("Adding to paidCart");
            paidCart.Add("C");

            //  try to pay for emptyCart
            Console.WriteLine("paying for emptyCart");
            var emptyCartPaid = emptyCart.Do(
                state => emptyCart,
                state => state.Pay(100),
                state => emptyCart);
            emptyCartPaid.Display();
        }
    }
} 
```

# 并发

# 并发

如今我们经常听到关于并发的话题，它有多么重要，以及它如何是["我们编写软件的下一个主要革命"](http://www.gotw.ca/publications/concurrency-ddj.htm)。

那么我们究竟是什么意思说“并发”，F# 又如何帮助呢？

并发的最简单定义就是“同时发生几件事情，也许彼此相互作用”。这似乎是一个微不足道的定义，但关键点在于大多数计算机程序（和语言）都是设计为串行工作的，一次处理一件事情，并且不适合处理并发。

即使计算机程序被编写以处理并发，也存在一个更严重的问题：我们的大脑在思考并发时表现不佳。普遍认为编写处理并发的代码非常困难。或者我应该说，编写正确的并发代码非常困难！编写出有错误的并发代码非常容易；可能会出现竞争条件，或者操作可能不是原子的，或者任务可能会被无谓地饿死或阻塞，这些问题很难通过查看代码或使用调试器来找到。

在讨论 F# 的具体内容之前，让我们试着对我们作为开发人员必须处理的一些常见并发场景进行分类：

+   **"并发多任务"**。当我们控制一些并发任务（例如进程或线程），并希望它们安全地相互通信和共享数据时，我们就会遇到这种情况。

+   **"异步"编程**。这是当我们启动与我们直接控制之外的另一个系统的对话，然后等待它回复我们时发生的情况。这种情况的常见情况是与文件系统、数据库或网络通信。这些情况通常是 I/O 绑定的，因此在等待期间，您希望做一些其他有用的事情。这些类型的任务通常也是*非确定性*的，这意味着两次运行相同的程序可能会得到不同的结果。

+   **"并行"编程**。当我们有一个单一任务要拆分为独立的子任务，然后并行运行这些子任务时，这就是并行编程，理想情况下利用所有可用的核心或 CPU。这些情况通常是 CPU 绑定的。与异步任务不同，并行性通常是*确定性*的，因此两次运行相同的程序将产生相同的结果。

+   **"响应式"编程**。这是当我们自己不发起任务，而是专注于监听事件并尽快处理这些事件时发生的情况。这种情况发生在设计服务器和处理用户界面时。

当然，这些都是模糊的定义，在实践中会有重叠。然而，总的来说，对于所有这些情况，实际上解决这些场景的实现倾向于使用两种不同的方法：

+   如果有很多需要共享状态或资源而不需要等待的不同任务，则使用"缓冲异步"设计。

+   如果有很多不需要共享状态的相同任务，则使用"fork/join"或"分而治之"方法进行并行任务。

## F#用于并发编程的工具

F#提供了多种编写并发代码的方法：

+   对于多任务和异步问题，F#可以直接使用所有常见的.NET 对象，如`Thread` `AutoResetEvent`、`BackgroundWorker`和`IAsyncResult`。但它也为所有类型的异步 IO 和后台任务管理提供了一个更简单的模型，称为"异步工作流"。我们将在下一篇文章中介绍这些。

+   用于异步问题的另一种替代方法是使用消息队列和["actor 模型"](http://en.wikipedia.org/wiki/Actor_model)（这是上面提到的"缓冲异步"设计）。F#内置了一个称为`MailboxProcessor`的 actor 模型实现。我非常赞成使用 actor 和消息队列进行设计，因为它将各个组件解耦，允许您对每个组件进行串行思考。

+   对于真正的 CPU 并行性，F#有方便的库代码，建立在上述提到的异步工作流之上，并且还可以使用.NET [任务并行库](http://msdn.microsoft.com/en-us/library/dd460717.aspx)。

+   最后，事件处理和响应式编程的函数式方法与传统方法非常不同。函数式方法将事件视为"流"，可以像 LINQ 处理集合一样对其进行过滤、拆分和合并。F#内置支持此模型，以及标准的事件驱动模型。

# 异步编程

# 异步编程

在本文中，我们将看看在 F#中编写异步代码的几种方法，以及一种并行性的简要示例。

## 传统的异步编程

如前所述，F#可以直接使用所有常见的.NET 对象，如`Thread` `AutoResetEvent`、`BackgroundWorker`和`IAsyncResult`。

让我们看一个简单的例子，我们等待一个定时器事件触发：

```
open System

let userTimerWithCallback = 
    // create an event to wait on
    let event = new System.Threading.AutoResetEvent(false)

    // create a timer and add an event handler that will signal the event
    let timer = new System.Timers.Timer(2000.0)
    timer.Elapsed.Add (fun _ -> event.Set() |> ignore )

    //start
    printfn "Waiting for timer at %O" DateTime.Now.TimeOfDay
    timer.Start()

    // keep working
    printfn "Doing something useful while waiting for event"

    // block on the timer via the AutoResetEvent
    event.WaitOne() |> ignore

    //done
    printfn "Timer ticked at %O" DateTime.Now.TimeOfDay 
```

这显示了`AutoResetEvent`作为同步机制的使用。

+   一个 lambda 函数被注册到`Timer.Elapsed`事件中，当事件触发时，AutoResetEvent 被发出信号。

+   主线程启动定时器，在等待时执行其他操作，然后阻塞，直到事件被触发。

+   最后，主线程继续，大约 2 秒后。

上面的代码相当简单，但需要你实例化一个 AutoResetEvent，并且如果 lambda 定义不正确，可能会有错误。

## 引入异步工作流

F# 有一个内置的构造称为“异步工作流”，使得异步代码更容易编写。这些工作流是封装后台任务的对象，并提供许多有用的操作来管理它们。

这是前面的示例重写以使用其中一个：

```
open System
//open Microsoft.FSharp.Control  // Async.* is in this module.

let userTimerWithAsync = 

    // create a timer and associated async event
    let timer = new System.Timers.Timer(2000.0)
    let timerEvent = Async.AwaitEvent (timer.Elapsed) |> Async.Ignore

    // start
    printfn "Waiting for timer at %O" DateTime.Now.TimeOfDay
    timer.Start()

    // keep working
    printfn "Doing something useful while waiting for event"

    // block on the timer event now by waiting for the async to complete
    Async.RunSynchronously timerEvent

    // done
    printfn "Timer ticked at %O" DateTime.Now.TimeOfDay 
```

这些是更改：

+   `AutoResetEvent` 和 lambda 已经消失了，并被`let timerEvent = Control.Async.AwaitEvent (timer.Elapsed)`取代，它直接从事件创建了一个`async`对象，而不需要 lambda。`ignore`被添加以忽略结果。

+   `event.WaitOne()`已被`Async.RunSynchronously timerEvent`替换，它在异步对象上阻塞，直到完成。

就是这样。更简单，更容易理解。

异步工作流也可以与`IAsyncResult`、开始/结束对和其他标准 .NET 方法一起使用。

例如，下面是如何通过包装从`BeginWrite`生成的`IAsyncResult`进行异步文件写入的方法。

```
let fileWriteWithAsync = 

    // create a stream to write to
    use stream = new System.IO.FileStream("test.txt",System.IO.FileMode.Create)

    // start
    printfn "Starting async write"
    let asyncResult = stream.BeginWrite(Array.empty,0,0,null,null)

    // create an async wrapper around an IAsyncResult
    let async = Async.AwaitIAsyncResult(asyncResult) |> Async.Ignore

    // keep working
    printfn "Doing something useful while waiting for write to complete"

    // block on the timer now by waiting for the async to complete
    Async.RunSynchronously async 

    // done
    printfn "Async write completed" 
```

## 创建和嵌套异步工作流

异步工作流也可以手动创建。使用`async`关键字和花括号创建一个新的工作流。花括号包含要在后台执行的一组表达式。

这个简单的工作流只是睡眠 2 秒。

```
let sleepWorkflow  = async{
    printfn "Starting sleep workflow at %O" DateTime.Now.TimeOfDay
    do! Async.Sleep 2000
    printfn "Finished sleep workflow at %O" DateTime.Now.TimeOfDay
    }

Async.RunSynchronously sleepWorkflow 
```

*注意：代码`do! Async.Sleep 2000`类似于`Thread.Sleep`，但设计用于与异步工作流一起工作。*

工作流可以包含*其他*异步工作流嵌套在其中。在大括号内，可以使用`let!`语法阻塞嵌套工作流。

```
let nestedWorkflow  = async{

    printfn "Starting parent"
    let! childWorkflow = Async.StartChild sleepWorkflow

    // give the child a chance and then keep working
    do! Async.Sleep 100
    printfn "Doing something useful while waiting "

    // block on the child
    let! result = childWorkflow

    // done
    printfn "Finished parent" 
    }

// run the whole workflow
Async.RunSynchronously nestedWorkflow 
```

## 取消工作流

关于异步工作流非常方便的一点是它们支持内置的取消机制。不需要特殊的代码。

考虑一个简单的任务，打印从 1 到 100 的数字：

```
let testLoop = async {
    for i in [1..100] do
        // do something
        printf "%i before.." i

        // sleep a bit 
        do! Async.Sleep 10  
        printfn "..after"
    } 
```

我们可以以通常的方式进行测试：

```
Async.RunSynchronously testLoop 
```

现在假设我们想在任务进行到一半时取消它。最好的方法是什么？

在 C# 中，我们必须创建标志来传递，然后频繁地检查它们，但在 F# 中，使用`CancellationToken`类内置了这种技术。

这里是我们如何取消任务的一个例子：

```
open System
open System.Threading

// create a cancellation source
let cancellationSource = new CancellationTokenSource()

// start the task, but this time pass in a cancellation token
Async.Start (testLoop,cancellationSource.Token)

// wait a bit
Thread.Sleep(200)  

// cancel after 200ms
cancellationSource.Cancel() 
```

在 F# 中，任何嵌套的异步调用都会自动检查取消令牌！

在这种情况下，是这一行：

```
do! Async.Sleep(10) 
```

从输出中可以看出，这一行是发生取消的地方。

## 在系列和并行中组合工作流

关于异步工作流的另一个有用之处是它们可以轻松地以各种方式组合：既串联又并行。

让我们再次创建一个简单的工作流，只是在给定的时间内睡眠：

```
// create a workflow to sleep for a time
let sleepWorkflowMs ms = async {
    printfn "%i ms workflow started" ms
    do! Async.Sleep ms
    printfn "%i ms workflow finished" ms
    } 
```

这是一个将两个这样的示例串联起来的版本：

```
let workflowInSeries = async {
    let! sleep1 = sleepWorkflowMs 1000
    printfn "Finished one" 
    let! sleep2 = sleepWorkflowMs 2000
    printfn "Finished two" 
    }

#time
Async.RunSynchronously workflowInSeries 
#time 
```

这是一个将两个这样的示例并行组合在一起的版本：

```
// Create them
let sleep1 = sleepWorkflowMs 1000
let sleep2 = sleepWorkflowMs 2000

// run them in parallel
#time
[sleep1; sleep2] 
    |> Async.Parallel
    |> Async.RunSynchronously 
#time 
```

注意：#time 命令切换定时器的开启和关闭。它仅在交互式窗口中起作用，因此必须将此示例发送到交互式窗口才能正常工作。

我们使用`#time`选项来显示总耗时，因为它们是并行运行的，所以是 2 秒。如果它们是串行运行，那么需要 3 秒。

你可能也会看到输出有时会混乱，因为两个任务同时向控制台写入！

这个最后的示例是一个经典的“分支/合并”方法的例子，其中生成了许多子任务，然后父任务等待它们全部完成。正��你所看到的，F#使这变得非常容易！

## 例子：一个异步网络下载器

在这个更为现实的例子中，我们将看到将一些现有代码从非异步风格转换为异步风格是多么容易，以及可以实现的相应性能提升。

因此，这是一个简单的 URL 下载器，与我们在系列开始时看到的非常相似：

```
open System.Net
open System
open System.IO

let fetchUrl url =        
    let req = WebRequest.Create(Uri(url)) 
    use resp = req.GetResponse() 
    use stream = resp.GetResponseStream() 
    use reader = new IO.StreamReader(stream) 
    let html = reader.ReadToEnd() 
    printfn "finished downloading %s" url 
```

这里是一些用于计时的代码：

```
// a list of sites to fetch
let sites = ["http://www.bing.com";
             "http://www.google.com";
             "http://www.microsoft.com";
             "http://www.amazon.com";
             "http://www.yahoo.com"]

#time                     // turn interactive timer on
sites                     // start with the list of sites
|> List.map fetchUrl      // loop through each site and download
#time                     // turn timer off 
```

记录所用时间，并看看我们是否能改进！

显然上面的例子效率低下--一次只访问一个网站。如果我们能同时访问它们，程序将更快。

那么我们如何将其转换为并发算法呢？逻辑将类似于：

+   为我们正在下载的每个网页创建一个任务，然后对于每个任务，下载逻辑将类似于：

    +   从网站下载页面。在此过程中，暂停并让其他任务有机会。

    +   当下载完成时，唤醒并继续执行任务

+   最后，启动所有任务并让它们开始工作！

不幸的是，在标准的类 C 语言中这样做相当困难。例如，在 C#中，您必须为异步任务完成时创建一个回调。管理这些回调很痛苦，并且会产生许多额外的支持代码，这些代码会妨碍理解逻辑。虽然有一些优雅的解决方案，但总的来说，在 C#中进行并发编程的信号噪比非常高*。

[*截至本文撰写时。未来版本的 C#将具有`await`关键字，类似于 F#现在的情况。]

但正如你所料，F#使这变得容易。以下是下载器代码的并发 F#版本：

```
open Microsoft.FSharp.Control.CommonExtensions   
                                        // adds AsyncGetResponse

// Fetch the contents of a web page asynchronously
let fetchUrlAsync url =        
    async {                             
        let req = WebRequest.Create(Uri(url)) 
        use! resp = req.AsyncGetResponse()  // new keyword "use!" 
        use stream = resp.GetResponseStream() 
        use reader = new IO.StreamReader(stream) 
        let html = reader.ReadToEnd() 
        printfn "finished downloading %s" url 
        } 
```

请注意，新代码几乎与原始代码完全相同。只有一些细微的更改。

+   从"`use resp =`"到"`use! resp =`"的更改正是我们上面讨论的更改--在异步操作进行时，让其他任务有机会。

+   我们还使用了在`CommonExtensions`命名空间中定义的扩展方法`AsyncGetResponse`。这将返回一个我们可以嵌套在主工作流中的异步工作流。

+   此外，整套步骤都包含在"`async {...}`"包装器中，将其转换为可以异步运行的块。

这是使用异步版本进行计时下载的示例。

```
// a list of sites to fetch
let sites = ["http://www.bing.com";
             "http://www.google.com";
             "http://www.microsoft.com";
             "http://www.amazon.com";
             "http://www.yahoo.com"]

#time                      // turn interactive timer on
sites 
|> List.map fetchUrlAsync  // make a list of async tasks
|> Async.Parallel          // set up the tasks to run in parallel
|> Async.RunSynchronously  // start them off
#time                      // turn timer off 
```

这是如何工作的：

+   `fetchUrlAsync`应用于每个站点。它不会立即开始下载，而是返回一个异步工作流以供稍后运行。

+   为了同时设置所有任务运行，我们使用`Async.Parallel`函数

+   最后，我们调用`Async.RunSynchronously`启动所有任务，并等待它们全部停止。

如果您自己尝试这段代码，您会发现异步版本比同步版本快得多。对于一些微小的代码更改来说，这并不算坏事！最重要的是，底层逻辑仍然非常清晰，没有被噪音淹没。

## 示例：一个并行计算

最后，让我们再次快速看一下并行计算。

在开始之前，我应该警告你，下面的示例代码仅用于演示基本原则。像这样的“玩具”版本的并行化基准测试并没有意义，因为任何真正的并发代码都有很多依赖关系。

还要注意，并行化很少是加速代码的最佳方法。你的时间几乎总是更好地花在改进算法上。我随时愿意拿我的串行快速排序版本与你的并行冒泡排序版本比试！（有关如何提高性能的更多详细信息，请参见优化系列）

无论如何，在这个警告的前提下，让我们创建一个消耗一些 CPU 的小任务。我们将串行和并行测试这个任务。

```
let childTask() = 
    // chew up some CPU. 
    for i in [1..1000] do 
        for i in [1..1000] do 
            do "Hello".Contains("H") |> ignore 
            // we don't care about the answer!

// Test the child task on its own.
// Adjust the upper bounds as needed
// to make this run in about 0.2 sec
#time
childTask()
#time 
```

根据需要调整循环的上限，使其在大约 0.2 秒内运行。

现在让我们将一堆这些任务组合成一个单一的串行任务（使用组合），并使用计时器进行测试：

```
let parentTask = 
    childTask
    |> List.replicate 20
    |> List.reduce (>>)

//test
#time
parentTask()
#time 
```

这应该大约需要 4 秒。

现在，为了使`childTask`可并行化，我们必须将其包装在`async`中：

```
let asyncChildTask = async { return childTask() } 
```

要将一堆异步操作组合成一个单一的并行任务，我们使用`Async.Parallel`。

让我们测试一下并比较时间：

```
let asyncParentTask = 
    asyncChildTask
    |> List.replicate 20
    |> Async.Parallel

//test
#time
asyncParentTask 
|> Async.RunSynchronously
#time 
```

在双核机器上，并行版本大约快 50%。当然，它会随着核心或 CPU 数量的增加而变得更快，但是次线性增长。四个核心会比一个核心快，但不会快四倍。

另一方面，就像异步网络下载示例一样，一些微小的代码更改可能会产生很大的差异，同时仍然使代码易于阅读和理解。因此，在真正需要并行处理的情况下，知道很容易安排这一点是很好的。

# 消息和代理

# 消息和代理

在本文中，我们将看一下基于消息（或基于 actor）的并发方法。

在这种方法中，当一个任务想要与另一个任务通信时，它会发送一个消息，而不是直接联系。消息被放在队列中，接收任务（称为“actor”或“代理”）会逐个从队列中取出消息进行处理。

这种基于消息的方法已经应用于许多情况，从低级网络套接字（建立在 TCP/IP 上）到企业范围的应用集成系统（例如 MSMQ 或 IBM WebSphere MQ）。

从软件设计的角度来看，基于消息的方法有许多好处：

+   您可以管理共享数据和资源而无需锁定。

+   您可以轻松遵循“单一职责原则”，因为每个代理可以设计为只做一件事。

+   它鼓励使用“生产者”向解耦的“消费者”发送消息的“管道”模型编程，这有额外的好处：

    +   队列作为缓冲器，消除了客户端等待的情况。

    +   根据需要，很容易扩展队列的一侧或另一侧，以最大化吞吐量。

    +   错误可以得到优雅地处理，因为解耦意味着代理可以创建和销毁而不影响它们的客户端。

从实际开发者的角度来看，我发现基于消息的方法最吸引人的地方是，在编写任何给定角色的代码时，你不必费力去考虑并发性。消息队列强制执行了对操作的“序列化”，否则可能会并发发生。这反过来使得更容易思考（和编写代码）处理消息的逻辑，因为你可以确信你的代码将与可能中断你的流程的其他事件隔离开来。

凭借这些优势，当爱立信内部的一个团队想要设计一个用于编写高度并发的电话应用程序的编程语言时，他们创建了一个采用基于消息的方法的语言，即 Erlang。 Erlang 现在已成为整个领域的典范，并且引起了在其他语言中实现相同方法的浓厚兴趣。

## F# 是如何实现基于消息的方法的

F# 有一个名为 `MailboxProcessor` 的内置代理类。与线程相比，这些代理非常轻量级 - 你可以同时实例化成千上万个。

这些与 Erlang 中的代理类似，但与 Erlang 不同的是，它们 *不* 跨进程边界工作，只在同一进程中工作。而且与像 MSMQ 这样的重量级队列系统不同，消息不是持久化的。如果你的应用程序崩溃，消息将丢失。

但这些只是小问题，可以解决。在未来的系列中，我将介绍消息队列的替代实现。在所有情况下，基本方法都是相同的。

让我们看一个 F# 中的简单代理实现：

```
 #nowarn "40"
let printerAgent = MailboxProcessor.Start(fun inbox-> 

    // the message processing function
    let rec messageLoop = async{

        // read a message
        let! msg = inbox.Receive()

        // process a message
        printfn "message is: %s" msg

        // loop to top
        return! messageLoop  
        }

    // start the loop 
    messageLoop 
    ) 
```

`MailboxProcessor.Start` 函数接受一个简单的函数参数。该函数会无限循环，从队列（或“收件箱”）中读取消息并处理它们。

*注：我已经添加了 `#nowarn "40"` 的指令以避免警告 "FS0040"，在这种情况下可以安全地忽略。*

这是一个使用示例：

```
// test it
printerAgent.Post "hello" 
printerAgent.Post "hello again" 
printerAgent.Post "hello a third time" 
```

在本文的其余部分，我们将看两个略微更有用的示例：

+   在没有锁的情况下管理共享状态

+   对共享 IO 进行序列化和缓冲访问

在这两种情况下，基于消息的并发方法是优雅的、高效的，并且易于编程。

## 管理共享状态

让我们先看看共享状态问题。

一个常见的情景是，你有一些需要被多个并发任务或线程访问和修改的状态。我们将使用一个非常简单的案例，并且说需求是：

+   一个可以由多个任务同时递增的共享"计数器"和"总和"。 

+   对计数器和总和的更改必须是原子的——我们必须保证它们同时被更新。

### 使用锁的共享状态方法

使用锁或互斥锁是满足这些要求的常见方法，因此让我们编写一些使用锁的代码，并查看其性能如何。

首先让我们编写一个静态的`LockedCounter`类，使用锁来保护状态。

```
open System
open System.Threading
open System.Diagnostics

// a utility function
type Utility() = 
    static let rand = new Random()

    static member RandomSleep() = 
        let ms = rand.Next(1,10)
        Thread.Sleep ms

// an implementation of a shared counter using locks
type LockedCounter () = 

    static let _lock = new Object()

    static let mutable count = 0
    static let mutable sum = 0

    static let updateState i = 
        // increment the counters and...
        sum <- sum + i
        count <- count + 1
        printfn "Count is: %i. Sum is: %i" count sum 

        // ...emulate a short delay
        Utility.RandomSleep()

    // public interface to hide the state
    static member Add i = 
        // see how long a client has to wait
        let stopwatch = new Stopwatch()
        stopwatch.Start() 

        // start lock. Same as C# lock{...}
        lock _lock (fun () ->

            // see how long the wait was
            stopwatch.Stop()
            printfn "Client waited %i" stopwatch.ElapsedMilliseconds

            // do the core logic
            updateState i 
            )
        // release lock 
```

对此代码的一些注释：

+   此代码使用非常命令式的方法编写，使用可变变量和锁。

+   公共`Add`方法具有显式的`Monitor.Enter`和`Monitor.Exit`表达式来获取和释放锁。这与 C# 中的`lock{...}`语句相同。

+   我们还添加了一个秒表来测量客户端等待获取锁的时间。

+   核心"业务逻辑"是`updateState`方法，它不仅更新状态，还添加了一个小的随机等待，以模拟执行处理所花费的时间。

让我们在隔离环境中进行测试：

```
// test in isolation
LockedCounter.Add 4
LockedCounter.Add 5 
```

接下来，我们将创建一个任务，该任务将尝试访问计数器：

```
let makeCountingTask addFunction taskId  = async {
    let name = sprintf "Task%i" taskId
    for i in [1..3] do 
        addFunction i
    }

// test in isolation
let task = makeCountingTask LockedCounter.Add 1
Async.RunSynchronously task 
```

在这种情况下，当根本没有争用时，等待时间都为 0。

但是当我们创建 10 个子任务，所有子任务都试图同时访问计数器时会发生什么：

```
let lockedExample5 = 
    [1..10]
        |> List.map (fun i -> makeCountingTask LockedCounter.Add i)
        |> Async.Parallel
        |> Async.RunSynchronously
        |> ignore 
```

哦，亲爱的！现在大部分任务等待了相当长的时间。如果两个任务想要同时更新状态，一个必须等待另一个的工作完成，然后才能执行自己的工作，这会影响性能。

如果我们添加了越来越多的任务，争用将会增加，任务将花费越来越多的时间等待而不是工作。

### 基于消息的共享状态方法

让我们看看消息队列如何帮助我们。这是基于消息的版本：

```
type MessageBasedCounter () = 

    static let updateState (count,sum) msg = 

        // increment the counters and...
        let newSum = sum + msg
        let newCount = count + 1
        printfn "Count is: %i. Sum is: %i" newCount newSum 

        // ...emulate a short delay
        Utility.RandomSleep()

        // return the new state
        (newCount,newSum)

    // create the agent
    static let agent = MailboxProcessor.Start(fun inbox -> 

        // the message processing function
        let rec messageLoop oldState = async{

            // read a message
            let! msg = inbox.Receive()

            // do the core logic
            let newState = updateState oldState msg

            // loop to top
            return! messageLoop newState 
            }

        // start the loop 
        messageLoop (0,0)
        )

    // public interface to hide the implementation
    static member Add i = agent.Post i 
```

对此代码的一些注释：

+   核心"业务逻辑"再次出现在`updateState`方法中，与之前的示例几乎相同的实现，只是状态是不可变的，因此会创建并返回一个新状态到主循环。

+   代理读取消息（在本例中是简单的整数），然后调用`updateState`方法。

+   公共方法`Add`向代理发送消息，而不是直接调用`updateState`方法。

+   这段代码以更函数式的方式编写；没有可变变量，也没有锁。事实上，根本没有处理并发的代码！代码只需要专注于业务逻辑，因此更容易理解。

让我们在隔离环境中进行测试：

```
// test in isolation
MessageBasedCounter.Add 4
MessageBasedCounter.Add 5 
```

接下来，我们将重用之前定义的一个任务，但调用`MessageBasedCounter.Add`：

```
let task = makeCountingTask MessageBasedCounter.Add 1
Async.RunSynchronously task 
```

最后让我们创建 5 个子任务，同时尝试访问计数器。

```
let messageExample5 = 
    [1..5]
        |> List.map (fun i -> makeCountingTask MessageBasedCounter.Add i)
        |> Async.Parallel
        |> Async.RunSynchronously
        |> ignore 
```

我们无法测量客户端的等待时间，因为根本没有！

## 共享 IO

当访问共享 IO 资源（例如文件）时，会出现类似的并发问题：

+   如果 IO 慢，即使没有锁，客户端也可能花费大量时间等待。

+   如果多个线程同时写入资源，可能会导致数据损坏。

这两个问题都可以通过使用异步调用结合缓冲区来解决--这正是消息队列所做的。

在下一个示例中，我们将考虑一个许多客户端将并发写入的日志服务的示例。（在这个简单的情况下，我们将直接写入到控制台。）

我们首先看看一个没有并发控制的实现，然后看看一个使用消息队列来串行化所有请求的实现。

### 无序列化的 IO

为了使损坏非常明显和可重复，让我们首先创建一个"缓慢"控制台，它将每个日志消息中的每个单个字符写入并在每个字符之间暂停一毫秒。在那一毫秒内，另一个线程也可以写入，导致消息不期而遇的交错。

```
let slowConsoleWrite msg = 
    msg |> String.iter (fun ch->
        System.Threading.Thread.Sleep(1)
        System.Console.Write ch
        )

// test in isolation
slowConsoleWrite "abc" 
```

接下来，我们将创建一个简单的任务，循环几次，每次都将其名称写入日志记录器：

```
let makeTask logger taskId = async {
    let name = sprintf "Task%i" taskId
    for i in [1..3] do 
        let msg = sprintf "-%s:Loop%i-" name i
        logger msg 
    }

// test in isolation
let task = makeTask slowConsoleWrite 1
Async.RunSynchronously task 
```

接下来，我们编写一个封装对缓慢控制台访问的日志记录类。它没有锁定或序列化，基本上不是线程安全的：

```
type UnserializedLogger() = 
    // interface
    member this.Log msg = slowConsoleWrite msg

// test in isolation
let unserializedLogger = UnserializedLogger()
unserializedLogger.Log "hello" 
```

现在让我们将所有这些组合成一个真实的示例。我们将创建五个子任务并并行运行它们，所有任务都试图写入缓慢的控制台。

```
let unserializedExample = 
    let logger = new UnserializedLogger()
    [1..5]
        |> List.map (fun i -> makeTask logger.Log i)
        |> Async.Parallel
        |> Async.RunSynchronously
        |> ignore 
```

哎呀！输出的内容乱七八糟的！

### 带消息的序列化 IO

那么，当我们用封装了消息队列的`SerializedLogger`类来替换`UnserializedLogger`时会发生什么呢。

`SerializedLogger`内部的代理简单地从其输入队列中读取消息并将其写入到缓慢的控制台。同样，没有涉及并发的代码，也没有使用锁。

```
type SerializedLogger() = 

    // create the mailbox processor
    let agent = MailboxProcessor.Start(fun inbox -> 

        // the message processing function
        let rec messageLoop () = async{

            // read a message
            let! msg = inbox.Receive()

            // write it to the log
            slowConsoleWrite msg

            // loop to top
            return! messageLoop ()
            }

        // start the loop
        messageLoop ()
        )

    // public interface
    member this.Log msg = agent.Post msg

// test in isolation
let serializedLogger = SerializedLogger()
serializedLogger.Log "hello" 
```

现在我们可以重复之前的未序列化示例，但这次使用`SerializedLogger`。同样，我们创建五个子任务并并行运行它们：

```
let serializedExample = 
    let logger = new SerializedLogger()
    [1..5]
        |> List.map (fun i -> makeTask logger.Log i)
        |> Async.Parallel
        |> Async.RunSynchronously
        |> ignore 
```

有何不同！这次输出完美无缺。

## 总结

这种基于消息的方法还有很多值得探讨的地方。在未来的系列中，我希望能够更详细地讨论，包括诸如：

+   使用 MSMQ 和 TPL Dataflow 的消息队列的替代实现。

+   取消和带外消息。

+   错误处理和重试，以及一般情况下的异常处理。

+   如何通过创建或删除子代来扩展和收缩。

+   避免缓冲区溢出和检测饥饿或不活动。

# 函数响应式编程

# 函数响应式编程

事件无处不在。几乎每个程序都必须处理事件，无论是用户界面中的按钮点击，服务器中的套接字监听，还是系统关闭通知。

事件是最常见的面向对象设计模式之一的基础："观察者"模式。

但是正如我们所知，事件处理，就像一般的并发一样，实现起来可能会很棘手。简单的事件逻辑很直接，但是像"如果连续发生两个事件则执行某些操作，但是如果只有一个事件发生则执行不同的操作"或者"如果两个事件几乎同时发生则执行某些操作"这样的逻辑又该如何呢？以及如何将这些要求以其他更复杂的方式组合起来有多容易？

即使您可以成功地实现这些要求，代码也往往像意大利面一样混乱，即使您怀着最好的意图。

是否有一种方法可以使事件处理更容易？

我们在前一篇关于消息队列的帖子中看到，该方法的一个优点是请求被“序列化”，使得概念上更容易处理。

有一种类似的方法可以用于事件。这个想法是将一系列事件转换成“事件流”。事件流然后就变得很像 IEnumerables，所以下一个明显的步骤就是像 LINQ 处理集合一样处理它们，以便对它们进行过滤、映射、分割和组合。

F#内置支持这种模型，以及更传统的方法。

## 一个简单的事件流

让我们从一个简单的例子开始，以比较这两种方法。我们将首先实现经典的事件处理程序方法。

首先，我们定义一个实用函数，它将：

+   创建一个定时器

+   为`Elapsed`事件注册一个处理程序

+   运行计时器五秒钟然后停止它

这是代码：

```
open System
open System.Threading

/// create a timer and register an event handler, 
/// then run the timer for five seconds
let createTimer timerInterval eventHandler =
    // setup a timer
    let timer = new System.Timers.Timer(float timerInterval)
    timer.AutoReset <- true

    // add an event handler
    timer.Elapsed.Add eventHandler

    // return an async task
    async {
        // start timer...
        timer.Start()
        // ...run for five seconds...
        do! Async.Sleep 5000
        // ... and stop
        timer.Stop()
        } 
```

现在交互式地测试它：

```
// create a handler. The event args are ignored
let basicHandler _ = printfn "tick %A" DateTime.Now

// register the handler
let basicTimer1 = createTimer 1000 basicHandler

// run the task now
Async.RunSynchronously basicTimer1 
```

现在让我们创建一个类似的实用方法来创建一个定时器，但这次它还会返回一个“可观察”的东西，即事件流。

```
let createTimerAndObservable timerInterval =
    // setup a timer
    let timer = new System.Timers.Timer(float timerInterval)
    timer.AutoReset <- true

    // events are automatically IObservable
    let observable = timer.Elapsed  

    // return an async task
    let task = async {
        timer.Start()
        do! Async.Sleep 5000
        timer.Stop()
        }

    // return a async task and the observable
    (task,observable) 
```

再次交互式测试它：

```
// create the timer and the corresponding observable
let basicTimer2 , timerEventStream = createTimerAndObservable 1000

// register that everytime something happens on the 
// event stream, print the time.
timerEventStream 
|> Observable.subscribe (fun _ -> printfn "tick %A" DateTime.Now)

// run the task now
Async.RunSynchronously basicTimer2 
```

不同之处在于，我们不是直接向事件注册处理程序，而是“订阅”事件流。微妙的不同，但很重要。

## 计算事件

在下一个示例中，我们将有一个稍微复杂一些的要求：

```
Create a timer that ticks every 500ms. 
At each tick, print the number of ticks so far and the current time. 
```

要以经典的命令式方式做到这一点，我们可能会创建一个带有可变计数器的类，如下所示：

```
type ImperativeTimerCount() =

    let mutable count = 0

    // the event handler. The event args are ignored
    member this.handleEvent _ =
      count <- count + 1
      printfn "timer ticked with count %i" count 
```

我们可以重用之前创建的实用函数来测试它：

```
// create a handler class
let handler = new ImperativeTimerCount()

// register the handler method
let timerCount1 = createTimer 500 handler.handleEvent

// run the task now
Async.RunSynchronously timerCount1 
```

让我们看看如何以函数方式做同样的事情：

```
// create the timer and the corresponding observable
let timerCount2, timerEventStream = createTimerAndObservable 500

// set up the transformations on the event stream
timerEventStream 
|> Observable.scan (fun count _ -> count + 1) 0 
|> Observable.subscribe (fun count -> printfn "timer ticked with count %i" count)

// run the task now
Async.RunSynchronously timerCount2 
```

在这里，我们看到如何构建事件转换的层次，就像您在 LINQ 中处理列表转换一样。

第一个转换是`scan`，它为每个事件累积状态。它大致相当于我们已经在列表中使用过的`List.fold`函数。在这种情况下，累积的状态只是一个计数器。

然后，对于每个事件，计数都会被打印出来。

注意，在这种函数式方法中，我们没有任何可变状态，也不需要创建任何特殊的类。

## 合并多个事件流

对于最后一个示例，我们将看一下如何合并多个事件流。

让我们根据众所周知的“FizzBuzz”问题制定一个需求：

```
Create two timers, called '3' and '5'. The '3' timer ticks every 300ms and the '5' timer ticks 
every 500ms. 

Handle the events as follows:
a) for all events, print the id of the time and the time
b) when a tick is simultaneous with a previous tick, print 'FizzBuzz'
otherwise:
c) when the '3' timer ticks on its own, print 'Fizz'
d) when the '5' timer ticks on its own, print 'Buzz' 
```

首先让我们创建一些两种实现都可以使用的代码。

我们将需要一个通用的事件类型来捕获计时器 ID 和时钟的时间。

```
type FizzBuzzEvent = {label:int; time: DateTime} 
```

然后我们需要一个实用函数来查看两个事件是否同时发生。我们将慷慨地允许时间差达到 50ms。

```
let areSimultaneous (earlierEvent,laterEvent) =
    let {label=_;time=t1} = earlierEvent
    let {label=_;time=t2} = laterEvent
    t2.Subtract(t1).Milliseconds < 50 
```

在命令式设计中，我们需要跟踪上一个事件，以便我们可以比较它们。当上一个事件不存在时，我们将需要特殊情况的代码。

```
type ImperativeFizzBuzzHandler() =

    let mutable previousEvent: FizzBuzzEvent option = None

    let printEvent thisEvent  = 
      let {label=id; time=t} = thisEvent
      printf "[%i] %i.%03i " id t.Second t.Millisecond
      let simultaneous = previousEvent.IsSome && areSimultaneous (previousEvent.Value,thisEvent)
      if simultaneous then printfn "FizzBuzz"
      elif id = 3 then printfn "Fizz"
      elif id = 5 then printfn "Buzz"

    member this.handleEvent3 eventArgs =
      let event = {label=3; time=DateTime.Now}
      printEvent event
      previousEvent <- Some event

    member this.handleEvent5 eventArgs =
      let event = {label=5; time=DateTime.Now}
      printEvent event
      previousEvent <- Some event 
```

现在代码开始变得混乱了！我们已经有了可变状态、复杂的条件逻辑和特殊情况，仅仅是为了一个如此简单的需求。

让我们测试一下：

```
// create the class
let handler = new ImperativeFizzBuzzHandler()

// create the two timers and register the two handlers
let timer3 = createTimer 300 handler.handleEvent3
let timer5 = createTimer 500 handler.handleEvent5

// run the two timers at the same time
[timer3;timer5]
|> Async.Parallel
|> Async.RunSynchronously 
```

它确实有效，但你确定代码没有 bug 吗？如果更改它，你会不会意外地破坏某些东西？

这个命令式代码的问题在于它有很多噪音，使需求变得模糊。

函数式版本能做得更好吗？让我们看看！

首先，我们创建 *两个* 事件流，一个用于每个计时器：

```
let timer3, timerEventStream3 = createTimerAndObservable 300
let timer5, timerEventStream5 = createTimerAndObservable 500 
```

接下来，我们将每个“原始”事件流中的事件转换为我们的 FizzBuzz 事件类型：

```
// convert the time events into FizzBuzz events with the appropriate id
let eventStream3  = 
   timerEventStream3  
   |> Observable.map (fun _ -> {label=3; time=DateTime.Now})

let eventStream5  = 
   timerEventStream5  
   |> Observable.map (fun _ -> {label=5; time=DateTime.Now}) 
```

现在，要判断两个事件是否同时发生，我们需要以某种方式比较它们来自两个不同的流。

实际上比听起来要容易，因为我们可以：

+   将两个流合并为一个流：

+   然后创建连续事件的配对

+   然后测试这些配对事件是否同时发生

+   然后根据该测试将输入流拆分为两个基于该测试的新输出流

这里是实际的代码：

```
// combine the two streams
let combinedStream = 
    Observable.merge eventStream3 eventStream5

// make pairs of events
let pairwiseStream = 
   combinedStream |> Observable.pairwise

// split the stream based on whether the pairs are simultaneous
let simultaneousStream, nonSimultaneousStream = 
    pairwiseStream |> Observable.partition areSimultaneous 
```

最后，我们可以再次根据事件 id 拆分 `nonSimultaneousStream`：

```
// split the non-simultaneous stream based on the id
let fizzStream, buzzStream  =
    nonSimultaneousStream  
    // convert pair of events to the first event
    |> Observable.map (fun (ev1,_) -> ev1)
    // split on whether the event id is three
    |> Observable.partition (fun {label=id} -> id=3) 
```

让我们回顾一下。我们从两个原始事件流开始，创建了四个新的事件流：

+   `combinedStream` 包含所有事件

+   `simultaneousStream` 只包含同时发生的事件

+   `fizzStream` 只包含 id=3 的非同时发生事件

+   `buzzStream` 只包含 id=5 的非同时发生事件

现在我们只需要为每个流附加行为：

```
//print events from the combinedStream
combinedStream 
|> Observable.subscribe (fun {label=id;time=t} -> 
                              printf "[%i] %i.%03i " id t.Second t.Millisecond)

//print events from the simultaneous stream
simultaneousStream 
|> Observable.subscribe (fun _ -> printfn "FizzBuzz")

//print events from the nonSimultaneous streams
fizzStream 
|> Observable.subscribe (fun _ -> printfn "Fizz")

buzzStream 
|> Observable.subscribe (fun _ -> printfn "Buzz") 
```

让我们测试一下：

```
// run the two timers at the same time
[timer3;timer5]
|> Async.Parallel
|> Async.RunSynchronously 
```

这里是所有代码的完整集合：

```
// create the event streams and raw observables
let timer3, timerEventStream3 = createTimerAndObservable 300
let timer5, timerEventStream5 = createTimerAndObservable 500

// convert the time events into FizzBuzz events with the appropriate id
let eventStream3  = timerEventStream3  
                    |> Observable.map (fun _ -> {label=3; time=DateTime.Now})
let eventStream5  = timerEventStream5  
                    |> Observable.map (fun _ -> {label=5; time=DateTime.Now})

// combine the two streams
let combinedStream = 
   Observable.merge eventStream3 eventStream5

// make pairs of events
let pairwiseStream = 
   combinedStream |> Observable.pairwise

// split the stream based on whether the pairs are simultaneous
let simultaneousStream, nonSimultaneousStream = 
   pairwiseStream |> Observable.partition areSimultaneous

// split the non-simultaneous stream based on the id
let fizzStream, buzzStream  =
    nonSimultaneousStream  
    // convert pair of events to the first event
    |> Observable.map (fun (ev1,_) -> ev1)
    // split on whether the event id is three
    |> Observable.partition (fun {label=id} -> id=3)

//print events from the combinedStream
combinedStream 
|> Observable.subscribe (fun {label=id;time=t} -> 
                              printf "[%i] %i.%03i " id t.Second t.Millisecond)

//print events from the simultaneous stream
simultaneousStream 
|> Observable.subscribe (fun _ -> printfn "FizzBuzz")

//print events from the nonSimultaneous streams
fizzStream 
|> Observable.subscribe (fun _ -> printfn "Fizz")

buzzStream 
|> Observable.subscribe (fun _ -> printfn "Buzz")

// run the two timers at the same time
[timer3;timer5]
|> Async.Parallel
|> Async.RunSynchronously 
```

代码可能看起来有点冗长，但这种逐步、分步的方法非常清晰和自我说明。

这种风格的一些好处是：

+   我只需看一眼就能看出它符合要求，甚至不需要运行它。而命令式版本就不行。

+   从设计角度来看，每个最终的“输出”流都遵循单一职责原则 -- 它只做一件事情 -- 因此很容易将行为与之关联起来。

+   这段代码没有条件语句，没��可变状态，没有边缘情况。希望很容易维护或更改。

+   容易调试。例如，我可以轻松地“监听”`simultaneousStream`的输出，看看它是否包含我认为的内容：

```
// debugging code
//simultaneousStream |> Observable.subscribe (fun e -> printfn "sim %A" e)
//nonSimultaneousStream |> Observable.subscribe (fun e -> printfn "non-sim %A" e) 
```

这在命令式版本中会困难得多。

## 摘要

函数式响应式编程（称为 FRP）是一个大课题，我们在这里只是触及了一点点。希望这个介绍让你一窥这种做事方式的用处。

如果你想了解更多，请参阅 F# [Observable module](http://msdn.microsoft.com/en-us/library/ee370313) 的文档，其中包含上述使用的基本转换。还有 [Reactive Extensions (Rx)](http://msdn.microsoft.com/en-us/library/hh242985%28v=vs.103%29) 库，作为 .NET 4 的一部分发布。其中包含许多其他额外的转换。

# 完整性

# 完整性

在这组最后的帖子中，我们将以“完整性”为主题，查看 F#的一些其他方面。

来自学术界的编程语言往往注重优雅和纯度而不是现实世界的实用性，而像 C#和 Java 这样的更主流的商业语言之所以受到重视，正是因为它们是实用的；它们可以在各种情况下工作，并且具有丰富的工具和库，几乎可以满足每一个需求。换句话说，为了在企业中有用，一种语言需要是*完整的*，而不仅仅是设计良好的。

F#之所以与众不同，是因为它成功地搭起了两个世界的桥梁。尽管到目前为止的所有示例都集中在 F#作为一个优雅的函数式语言上，但它也支持面向对象的范式，并且可以轻松集成到其他.NET 语言和工具中。因此，F#不是一个孤立的岛屿，而是受益于整个.NET 生态系统的一部分。

F#“完整”的其他方面包括成为官方.NET 语言（具有所有相关的支持和文档），以及被设计为在 Visual Studio 中工作（提供了一个带有 IntelliSense 支持、调试器等的良好编辑器）。这些好处应该是显而易见的，这里不会讨论。

因此，在这最后一节中，我们将重点关注两个特定领域：

+   **与.NET 库无缝互操作**。显然，F#的函数式方法与基础库中设计的命令式方法之间可能存在不匹配。我们将看一些使这种集成更容易的 F#功能。

+   **完全支持类和其他 C#风格的代码**。F#被设计为一种混合的函数式/OO 语言，因此它几乎可以做任何 C#可以做的事情。我们将快速了解一下这些其他功能的语法。

# 与.NET 库无缝互操作

# 与.NET 库无缝互操作

我们已经看到了很多关于使用.NET 库的 F#的示例，比如使用`System.Net.WebRequest`和`System.Text.RegularExpressions`。而且，集成确实是无缝的。

对于更复杂的需求，F#本身就原生支持.NET 类、接口和结构，因此互操作仍然非常简单。例如，你可以在 C#中编写一个`ISomething`接口，然后在 F#中实现它。

但不仅可以 F#调用现有的.NET 代码，还可以将几乎任何.NET API 暴露给其他语言。例如，你可以在 F#中编写类和方法，并将它们暴露给 C#、VB 或 COM。你甚至可以反过来做上述示例 -- 在 F#中定义一个`ISomething`接口，然后在 C#中实现它！所有这些的好处在于，你不必丢弃任何现有的代码库；你可以开始使用 F#来做一些事情，同时保留 C#或 VB 来做其他事情，并选择最适合的工具来完成工作。

除了紧密集成之外，F#中还有许多很好的功能，通常使得与.NET 库一起工作比 C#更方便。以下是我最喜欢的一些功能：

+   您可以在不传递“out”参数的情况下使用`TryParse`和`TryGetValue`。

+   您可以使用参数名解决方法重载，这也有助于类型推断。

+   您可以使用“活动模式”将.NET API 转换为更友好的代码。

+   您可以动态从接口（如`IDisposable`）创建对象，而无需创建具体类。

+   您可以混合和匹配“纯”F#对象与现有的.NET API

## TryParse 和 TryGetValue

用于值和字典的`TryParse`和`TryGetValue`函数经常用于避免额外的异常处理。但是 C#语法有点笨拙。在 F#中使用它们更加优雅，因为 F#会自动将函数转换为一个元组，其中第一个元素是函数的返回值，第二个是“out”参数。

```
//using an Int32
let (i1success,i1) = System.Int32.TryParse("123");
if i1success then printfn "parsed as %i" i1 else printfn "parse failed"

let (i2success,i2) = System.Int32.TryParse("hello");
if i2success then printfn "parsed as %i" i2 else printfn "parse failed"

//using a DateTime
let (d1success,d1) = System.DateTime.TryParse("1/1/1980");
let (d2success,d2) = System.DateTime.TryParse("hello");

//using a dictionary
let dict = new System.Collections.Generic.Dictionary<string,string>();
dict.Add("a","hello")
let (e1success,e1) = dict.TryGetValue("a");
let (e2success,e2) = dict.TryGetValue("b"); 
```

## 命名参数有助于类型推断

在 C#（以及.NET 一般），您可以有许多不同参数的重载方法。F#可能会遇到麻烦。例如，这里是尝试创建`StreamReader`的尝试：

```
let createReader fileName = new System.IO.StreamReader(fileName)
// error FS0041: A unique overload for method 'StreamReader' 
//               could not be determined 
```

问题在于 F#不知道参数应该是字符串还是流。您可以显式指定参数的类型，但这不是 F#的方式！

相反，一个很好的解决方法是，由于在 F#中调用.NET 库中的方法时，可以指定命名参数。

```
let createReader2 fileName = new System.IO.StreamReader(path=fileName) 
```

在许多情况下，就像上面的情况一样，只使用参数名就足以解决类型问题。而且使用显式参数名通常可以帮助使代码更易读。

## 用于.NET 函数的活动模式

有许多情况下，您希望针对.NET 类型使用模式匹配，但本机库不支持这一点。之前，我们简要提到了 F#功能称为“活动模式”，它允许您动态创建选择以匹配。这对于.NET 集成非常有用。

一个常见情况是，一个.NET 库类有许多互斥的`isSomething`，`isSomethingElse`方法，必须用可怕的级联 if-else 语句进行测试。活动模式可以隐藏所有丑陋的测试，让您的其余代码使用更自然的方法。

例如，这是用于测试各种`System.Char`的`isXXX`方法的代码。

```
let (|Digit|Letter|Whitespace|Other|) ch = 
   if System.Char.IsDigit(ch) then Digit
   else if System.Char.IsLetter(ch) then Letter
   else if System.Char.IsWhiteSpace(ch) then Whitespace
   else Other 
```

一旦选择被定义，正常的代码可以很直接：

```
let printChar ch = 
  match ch with
  | Digit -> printfn "%c is a Digit" ch
  | Letter -> printfn "%c is a Letter" ch
  | Whitespace -> printfn "%c is a Whitespace" ch
  | _ -> printfn "%c is something else" ch

// print a list
['a';'b';'1';' ';'-';'c'] |> List.iter printChar 
```

另一个常见情况是，当您必须解析文本或错误代码以确定异常或结果的类型时。这里有一个使用活动模式解析与`SqlExceptions`相关的错误编号的示例，使它们更易接受。

首先，设置错误编号的活动模式匹配：

```
open System.Data.SqlClient

let (|ConstraintException|ForeignKeyException|Other|) (ex:SqlException) = 
   if ex.Number = 2601 then ConstraintException 
   else if ex.Number = 2627 then ConstraintException 
   else if ex.Number = 547 then ForeignKeyException 
   else Other 
```

现在我们可以在处理 SQL 命令时使用这些模式：

```
let executeNonQuery (sqlCommmand:SqlCommand) = 
    try
       let result = sqlCommmand.ExecuteNonQuery()
       // handle success
    with 
    | :?SqlException as sqlException -> // if a SqlException
        match sqlException with         // nice pattern matching
        | ConstraintException  -> // handle constraint error
        | ForeignKeyException  -> // handle FK error
        | _ -> reraise()          // don't handle any other cases
    // all non SqlExceptions are thrown normally 
```

## 直接从接口创建对象

F# 还有一个有用的功能叫做 "对象表达式"。这是直接从接口或抽象类创建对象的能力，而不必首先定义一个具体类。

在下面的示例中，我们使用 `makeResource` 辅助函数创建了一些实现 `IDisposable` 的对象。

```
// create a new object that implements IDisposable
let makeResource name = 
   { new System.IDisposable 
     with member this.Dispose() = printfn "%s disposed" name }

let useAndDisposeResources = 
    use r1 = makeResource "first resource"
    printfn "using first resource" 
    for i in [1..3] do
        let resourceName = sprintf "\tinner resource %d" i
        use temp = makeResource resourceName 
        printfn "\tdo something with %s" resourceName 
    use r2 = makeResource "second resource"
    printfn "using second resource" 
    printfn "done." 
```

该示例还演示了 "`use`" 关键字如何在超出作用域时自动释放资源。以下是输出：

```
using first resource
    do something with     inner resource 1
    inner resource 1 disposed
    do something with     inner resource 2
    inner resource 2 disposed
    do something with     inner resource 3
    inner resource 3 disposed
using second resource
done.
second resource disposed
first resource disposed 
```

## 将 .NET 接口与纯 F# 类型混合使用

动态创建接口的能力意味着很容易将现有 API 中的接口与纯 F# 类型混合使用。

例如，假设您有一个使用 `IAnimal` 接口的现有 API，如下所示。

```
type IAnimal = 
   abstract member MakeNoise : unit -> string

let showTheNoiseAnAnimalMakes (animal:IAnimal) = 
   animal.MakeNoise() |> printfn "Making noise %s" 
```

但是我们想要享受模式匹配等所有优势，因此我们创建了纯 F# 类型的猫和狗，而不是类。

```
type Cat = Felix | Socks
type Dog = Butch | Lassie 
```

但是使用这种纯 F# 方法意味着我们不能直接将猫和狗传递给 `showTheNoiseAnAnimalMakes` 函数。

但是，我们不必创建新的具体类集合来实现 `IAnimal`。相反，我们可以通过扩展纯 F# 类型动态创建 `IAnimal` 接口。

```
// now mixin the interface with the F# types
type Cat with
   member this.AsAnimal = 
        { new IAnimal 
          with member a.MakeNoise() = "Meow" }

type Dog with
   member this.AsAnimal = 
        { new IAnimal 
          with member a.MakeNoise() = "Woof" } 
```

这是一些测试代码：

```
let dog = Lassie
showTheNoiseAnAnimalMakes (dog.AsAnimal)

let cat = Felix
showTheNoiseAnAnimalMakes (cat.AsAnimal) 
```

这种方法给了我们两全其美的结果。内部使用纯 F# 类型，但可以根据需要将其转换为接口以与库进行接口。

## 使用反射来检查 F# 类型

F# 可以利用 .NET 反射系统的优势，这意味着您可以使用语言本身的语法无法直接访问的各种有趣的功能。 `Microsoft.FSharp.Reflection` 命名空间有许多专为帮助 F# 类型而设计的函数。

例如，这是一种打印记录类型字段和联合类型选择项的方法。

```
open System.Reflection
open Microsoft.FSharp.Reflection

// create a record type...
type Account = {Id: int; Name: string}

// ... and show the fields
let fields = 
    FSharpType.GetRecordFields(typeof<Account>)
    |> Array.map (fun propInfo -> propInfo.Name, propInfo.PropertyType.Name)

// create a union type...
type Choices = | A of int | B of string

// ... and show the choices
let choices = 
    FSharpType.GetUnionCases(typeof<Choices>)
    |> Array.map (fun choiceInfo -> choiceInfo.Name) 
```

# 任何 C# 都能做到...

# 任何 C# 都能做到...

显而易见的是，在 F# 中通常应该尽量使用函数式代码，而不是面向对象的代码，但在某些情况下，您可能需要完全成熟的 OO 语言的所有功能？类、继承、虚方法等。

所以，就在这一部分结束时，这里是 F# 版本的这些特性的一场风驰电掣的旅行。

这些异常中的一些将在后面关于 .NET 集成的系列中更深入地讨论。但是我不会涉及一些更难理解的异常，因为如果你需要的话，可以在 MSDN 文档中阅读相关内容。

## 类和接口

首先，这里有一些接口、抽象类和从抽象类继承的具体类的示例。

```
// interface
type IEnumerator<'a> = 
    abstract member Current : 'a
    abstract MoveNext : unit -> bool 

// abstract base class with virtual methods
[<AbstractClass>]
type Shape() = 
    //readonly properties
    abstract member Width : int with get
    abstract member Height : int with get
    //non-virtual method
    member this.BoundingArea = this.Height * this.Width
    //virtual method with base implementation
    abstract member Print : unit -> unit 
    default this.Print () = printfn "I'm a shape"

// concrete class that inherits from base class and overrides 
type Rectangle(x:int, y:int) = 
    inherit Shape()
    override this.Width = x
    override this.Height = y
    override this.Print ()  = printfn "I'm a Rectangle"

//test
let r = Rectangle(2,3)
printfn "The width is %i" r.Width
printfn "The area is %i" r.BoundingArea
r.Print() 
```

类可以有多个构造函数、可变属性等。

```
type Circle(rad:int) = 
    inherit Shape()

    //mutable field
    let mutable radius = rad

    //property overrides
    override this.Width = radius * 2
    override this.Height = radius * 2

    //alternate constructor with default radius
    new() = Circle(10)      

    //property with get and set
    member this.Radius
         with get() = radius
         and set(value) = radius <- value

// test constructors
let c1 = Circle()   // parameterless ctor
printfn "The width is %i" c1.Width
let c2 = Circle(2)  // main ctor
printfn "The width is %i" c2.Width

// test mutable property
c2.Radius <- 3
printfn "The width is %i" c2.Width 
```

## 泛型

F# 支持泛型及其相关约束。

```
// standard generics
type KeyValuePair<'a,'b>(key:'a, value: 'b) = 
    member this.Key = key
    member this.Value = value

// generics with constraints
type Container<'a,'b 
    when 'a : equality 
    and 'b :> System.Collections.ICollection>
    (name:'a, values:'b) = 
    member this.Name = name
    member this.Values = values 
```

## 结构体

F# 不仅支持类，还支持 .NET 结构类型，这在某些情况下可以提高性能。

```
 type Point2D =
   struct
      val X: float
      val Y: float
      new(x: float, y: float) = { X = x; Y = y }
   end

//test
let p = Point2D()  // zero initialized
let p2 = Point2D(2.0,3.0)  // explicitly initialized 
```

## 异常

F# 可以创建异常类，引发异常并捕获异常。

```
// create a new Exception class
exception MyError of string

try
    let e = MyError("Oops!")
    raise e
with 
    | MyError msg -> 
        printfn "The exception error was %s" msg
    | _ -> 
        printfn "Some other exception" 
```

## 扩展方法

就像在 C# 中一样，F# 可以使用扩展方法扩展现有类。

```
type System.String with
    member this.StartsWithA = this.StartsWith "A"

//test
let s = "Alice"
printfn "'%s' starts with an 'A' = %A" s s.StartsWithA

type System.Int32 with
    member this.IsEven = this % 2 = 0

//test
let i = 20
if i.IsEven then printfn "'%i' is even" i 
```

## 参数数组

就像 C# 的可变长度 "params" 关键字一样，这允许将可变长度的参数列表转换为单个数组参数。

```
open System
type MyConsole() =
    member this.WriteLine([<ParamArray>] args: Object[]) =
        for arg in args do
            printfn "%A" arg

let cons = new MyConsole()
cons.WriteLine("abc", 42, 3.14, true) 
```

## 事件

F# 类可以拥有事件，并且可以触发和响应事件。

```
type MyButton() =
    let clickEvent = new Event<_>()

    [<CLIEvent>]
    member this.OnClick = clickEvent.Publish

    member this.TestEvent(arg) =
        clickEvent.Trigger(this, arg)

// test
let myButton = new MyButton()
myButton.OnClick.Add(fun (sender, arg) -> 
        printfn "Click event with arg=%O" arg)

myButton.TestEvent("Hello World!") 
```

## 委托

F# 可以使用委托。

```
// delegates
type MyDelegate = delegate of int -> int
let f = MyDelegate (fun x -> x * x)
let result = f.Invoke(5) 
```

## 枚举

F# 支持 CLI 枚举类型，它们看起来类似于 "union" 类型，但实际上在内部是不同的。

```
// enums
type Color = | Red=1 | Green=2 | Blue=3

let color1  = Color.Red    // simple assignment
let color2:Color = enum 2  // cast from int
// created from parsing a string
let color3 = System.Enum.Parse(typeof<Color>,"Green") :?> Color // :?> is a downcast

[<System.FlagsAttribute>]
type FileAccess = | Read=1 | Write=2 | Execute=4 
let fileaccess = FileAccess.Read ||| FileAccess.Write 
```

## 使用标准用户界面工作

最后，F# 可以与 WinForms 和 WPF 用户界面库一起工作，就像 C# 一样。

这是一个打开窗体并处理点击事件的简单示例。

```
open System.Windows.Forms 

let form = new Form(Width= 400, Height = 300, Visible = true, Text = "Hello World") 
form.TopMost <- true
form.Click.Add (fun args-> printfn "the form was clicked")
form.Show() 
```

# 为什么使用 F#: 结论

# 为什么使用 F#: 结论

这完成了对 F# 特性的介绍。我希望这些示例能让您更加欣赏 F# 和函数式编程的强大之处。如果您对整个系列有任何评论，请在本页面底部留言。

在后续系列中，我希望能更深入地讨论数据结构、模式匹配、列表处理、异步和并行编程等内容。

但在这之前，我建议您阅读"函数式思维"系列，这将帮助您更深入地理解函数式编程。
