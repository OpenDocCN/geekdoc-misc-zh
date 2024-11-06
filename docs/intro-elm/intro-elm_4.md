# 类型

# 类型

Elm 的一个主要优点是**用户在实践中看不到运行时错误**。这是可能的，因为 Elm 编译器可以快速分析您的源代码，看看值如何在程序中流动。如果一个值可能以无效方式使用，编译器会用友好的错误消息告诉您。这被称为*类型推断*。编译器会弄清楚所有函数中的值是什么*类型*。

## 类型推断的一个例子

以下代码定义了一个`toFullName`函数，该函数提取一个人的全名作为字符串：

```
toFullName person =
  person.firstName ++ " " ++ person.lastName

fullName =
  toFullName { fistName = "Hermann", lastName = "Hesse" } 
```

就像在 JavaScript 或 Python 中一样，我们只需编写代码，没有额外的混乱。不过你看到了 bug 吗？

在 JavaScript 中，等效的代码输出`"undefined Hesse"`。甚至没有错误！希望你的用户中的某个人在实际使用中看到时会告诉你。相比之下，Elm 编译器只查看源代码并告诉你：

```
-- TYPE MISMATCH ---------------------------------------------------------------

The argument to function `toFullName` is causing a mismatch.

6│   toFullName { fistName = "Hermann", lastName = "Hesse" }
                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Function `toFullName` is expecting the argument to be:

    { …, firstName : … }

But it is:

    { …, fistName : … }

Hint: I compared the record fields and found some potential typos.

    firstName <-> fistName 
```

它发现`toFullName`得到了错误的*类型*参数。就像错误消息中的提示所说，有人不小心写成了`fist`而不是`first`。

对于这种简单错误有一个助手是很棒的，但是当你有数百个文件和一堆合作者进行更改时，它甚至更有价值。无论事情变得多么庞大和复杂，Elm 编译器都会根据源代码检查*一切*是否正确地组合在一起。

你越了解类型，编译器就越像一个友好的助手。所以让我们开始学习更多吧！

# 阅读类型

# 阅读类型

在本书的核心语言部分，我们在 REPL 中运行了一堆代码。好吧，我们将再次这样做，但现在重点放在输出的类型上。所以在终端中键入`elm repl`。你应该看到这个：

```
---- elm repl 0.18.0 -----------------------------------------------------------
 :help for help, :exit to exit, more at <https://github.com/elm-lang/elm-repl>
--------------------------------------------------------------------------------
> 
```

## 基本类型和列表

让我们输入一些简单的表达式，看看会发生什么：

```
> "hello"
"hello" : String

> not True
False : Bool

> round 3.1415
3 : Int 
```

在这三个例子中，REPL 告诉我们结果值以及它是什么*类型*的值。值`"hello"`是一个`String`。值`3`是一个`Int`。这里没有什么太疯狂的东西。

让我们看看持有不同类型值的列表会发生什么：

```
> [ "Alice", "Bob" ]
[ "Alice", "Bob" ] : List String

> [ 1.0, 8.6, 42.1 ]
[ 1.0, 8.6, 42.1 ] : List Float

> []
[] : List a 
```

在第一个案例中，我们有一个填充有`String`值的`List`。在第二个案例中，`List`填充有`Float`值。在第三个案例中，列表是空的，所以我们实际上不知道列表中有什么类型的值。因此，类型`List a`表示“我知道我有一个列表，但它可以填充任何内容”。小写的`a`被称为*类型变量*，意味着在我们的程序中没有约束将其固定为某种特定类型。换句话说，类型可以根据使用方式而变化。

## 函数

让我们看看一些函数的类型：

```
> import String
> String.length
<function> : String -> Int 
```

函数`String.length`的类型为`String -> Int`。这意味着它*必须*接受一个`String`参数，并且肯定会返回一个整数结果。所以让我们尝试给它一个参数：

```
> String.length "Supercalifragilisticexpialidocious"
34 : Int 
```

这里要理解的重要一点是结果类型`Int`如何从初始表达式构建起来的。我们有一个`String -> Int`函数并给它一个`String`参数。这将导致一个`Int`。

如果不给出一个`String`会发生什么？

```
> String.length [1,2,3]
-- error!

> String.length True
-- error! 
```

一个`String -> Int`函数 *必须* 接收一个`String`参数！

### 匿名函数

Elm 有一个称为*匿名函数*的特性。基本上，你可以创建一个不命名的函数，就像这样：

```
> \n -> n / 2
<function> : Float -> Float 
```

在反斜杠和箭头之间，列出函数的参数，在箭头的右侧，说明对这些参数要做什么。在这个例子中，它的意思是：我接收一个名为`n`的参数，然后我将把它除以二。

我们可以直接使用匿名函数。这是我们使用`128`作为参数的匿名函数的使用方式：

```
> (\n -> n / 2) 128
64 : Float 
```

我们从一个`Float -> Float`函数开始，并给它一个`Float`参数。结果是另一个`Float`。

> **注：**开始匿名函数的反斜杠如果你眯眼看的话应该看起来像一个λ。这是对导致 Elm 等语言出现的知识历史的可能不切实际的暗示。
> 
> 此外，当我们写表达式`(\n -> n / 2) 128`时，重要的是我们在匿名函数周围放置括号。在箭头之后，Elm 只会继续读取代码，只要它能。括号对此进行了界定，指示函数体的结束位置。

### 命名函数

就像我们可以给一个值取一个名字一样，我们也可以给一个匿名函数取一个名字。太叛逆了！

```
> oneHundredAndTwentyEight = 128.0
128 : Float

> half = \n -> n / 2
<function> : Float -> Float

> half oneHundredAndTwentyEight
64 : Float 
```

最后，它的工作方式就像没有命名的时候一样。你有一个`Float -> Float`函数，你给它一个`Float`，最终你得到另一个`Float`。

但是这里有个疯狂的秘密：这就是所有函数的定义方式！你只是给一个匿名函数取了一个名字。所以当你看到这样的东西时：

```
> half n = n / 2
<function> : Float -> Float 
```

你可以将其视为一种方便的简写形式：

```
> half = \n -> n / 2
<function> : Float -> Float 
```

所有函数都适用，无论它们有多少个参数。所以现在让我们更进一步，思考一下对于具有*多个*参数的函数意味着什么：

```
> divide x y = x / y
<function> : Float -> Float -> Float

> divide 3 2
1.5 : Float 
```

看起来没问题，但是为什么`divide`的类型中有*两个*箭头？起初，认为“所有参数都被箭头分隔，最后的是函数的结果”是可以的。所以`divide`接受两个参数并返回一个`Float`。

要真正理解`divide`类型中为什么有两个箭头，有助于将定义转换为使用匿名函数。

```
> divide x y = x / y
<function> : Float -> Float -> Float

> divide x = \y -> x / y
<function> : Float -> Float -> Float

> divide = \x -> (\y -> x / y)
<function> : Float -> Float -> Float 
```

所有这些都是完全等价的。我们只是将参数移到了一边，一次将它们转换为匿名函数。所以当我们运行像`divide 3 2`这样的表达式时，实际上进行了一系列的求值步骤：

```
 divide 3 2
  (divide 3) 2                 -- Step 1 - Add the implicit parentheses
  ((\x -> (\y -> x / y)) 3) 2  -- Step 2 - Expand `divide`
  (\y -> 3 / y) 2              -- Step 3 - Replace x with 3
  3 / 2                        -- Step 4 - Replace y with 2
  1.5                          -- Step 5 - Do the math 
```

扩展`divide`之后，你实际上是逐个提供参数。替换`x`和`y`实际上是两个不同的步骤。

让我们更详细地分解一下看看类型是如何工作的。在求值步骤#3 中，我们看到了以下函数：

```
> (\y -> 3 / y)
<function> : Float -> Float 
```

这是一个 `Float -> Float` 函数，就像 `half` 一样。现在在步骤＃2 中，我们看到了一个更复杂的函数：

```
> (\x -> (\y -> x / y))
<function> : Float -> Float -> Float 
```

好吧，我们从 `\x -> ...` 开始，所以我们知道类型将会是像 `Float -> ...` 这样的东西。我们还知道 `(\y -> x / y)` 具有类型 `Float -> Float`。

所以如果您实际上写下了类型中的所有括号，它将会说 **`Float -> (Float -> Float)`**。您一次提供一个参数。所以当您替换 `x` 时，结果实际上是*另一个函数*。

Elm 中的所有函数都是一样的：

```
> import String
> String.repeat
<function> : Int -> String -> String 
```

这实际上是 `Int -> (String -> String)`，因为您一次提供一个参数。

因为 Elm 中的所有函数都是这样工作的，所以你不需要一次性提供所有的参数。可以这样说：

```
> divide 128
<function> : Float -> Float

> String.repeat 3
<function> : String -> String 
```

这称为*部分应用*。它让我们以一种很好的方式使用 [the `|>` operator](http://package.elm-lang.org/packages/elm-lang/core/latest/Basics#|>) 来链接函数，这也是为什么函数类型有这么多箭头的原因！

## 类型注解

到目前为止，我们只是让 Elm 自己找出类型，但它也允许您在定义的上面一行写一个*类型注解*。所以当您编写代码时，您可以这样说：

```
half : Float -> Float
half n =
  n / 2

divide : Float -> Float -> Float
divide x y =
  x / y

askVegeta : Int -> String
askVegeta powerLevel =
  if powerLevel > 9000 then
    "It's over 9000!!!"

  else
    "It is " ++ toString powerLevel ++ "." 
```

人们在类型注解中可能会犯错误，那么如果他们说错了会发生什么？嗯，编译器不会犯错，所以它仍然自己找出类型。然后它检查您的注解是否与真实答案匹配。换句话说，编译器将始终验证您添加的所有注解是否正确。

> **注意：**有些人觉得类型注解放在实际定义的上面有点奇怪。理由是应该很容易和不具侵入性地稍后添加类型注解。这样你就可以通过添加行将一个懒散的原型转变为更高质量的代码。

# 类型别名

# 类型别名

类型别名的整个目的是使您的类型注解更易于阅读。

随着您的程序变得越来越复杂，您会发现自己处理着更大更复杂的数据。例如，也许您正在制作 Twitter-for-dogs，您需要代表一个用户。也许您想要一个检查用户是否有生物的函数。您可能会写一个像这样的函数：

```
hasBio : { name : String, bio : String, pic : String } -> Bool
hasBio user =
  String.length user.bio > 0 
```

那个类型注解有点混乱，而且用户甚至没有那么多细节！想象一下如果有十个字段会怎样。或者如果你有一个以用户作为参数并给出用户作为结果的函数。

在这种情况下，您应该为您的数据创建一个*类型别名*：

```
type alias User =
  { name : String
  , bio : String
  , pic : String
  } 
```

这意味着，无论你在哪里看到 `User`，都用所有这些其他内容替换它。所以现在我们可以用一种更好的方式重写我们的 `hasBio` 函数：

```
hasBio : User -> Bool
hasBio user =
  String.length user.bio > 0 
```

看起来好多了！重要的是要强调*这两个定义是完全相同的*。我们只是创建了一个别名，这样我们可以用更少的按键来说同样的话。

所以如果我们写一个添加生物的函数，它会是这样的：

```
addBio : String -> User -> User
addBio bio user =
  { user | bio = bio } 
```

想象一下如果我们没有 `User` 类型别名那个类型注解会是什么样子。糟糕！

类型别名不仅仅是为了美观。它们可以帮助你更清晰地思考。编写 Elm 程序时，通常最好是在编写一堆函数之前*先*写出类型别名。我发现这有助于以更高效的方式引导我的进展。突然间你完全知道你正在处理的是什么类型的数据。如果你需要向其添加内容，编译器会告诉你受到影响的任何现有代码。我认为大多数有经验的 Elm 开发者在处理记录时特别使用类似的过程。

> **注意：**当你为记录专门创建类型别名时，它还会生成一个*记录构造函数*。所以我们的`User`类型别名也会生成这个函数：
> 
> ```
> User : String -> String -> String -> User 
> ```
> 
> 参数的顺序与类型别名声明中出现的顺序相同，所以在 REPL 中你可以这样做：
> 
> ```
> > type alias User = { name : String, bio : String, pic : String }
> 
> > User "Tom" "Friendly Carpenter" "http://example.com/tom.jpg"
> { name = "Tom", bio = "Friendly Carpenter", pic = "http://example.com/tom.jpg" } : User 
> ```
> 
> 这可能会非常方便！

# 联合类型

# 联合类型

许多语言在表达具有奇怪形状的数据时会遇到麻烦。它们只给你提供了一小组内置类型，你必须用它们来表示一切。因此，你经常会发现自己使用`null`或布尔值或字符串来编码细节，这种方式相当容易出错。

Elm 的*联合类型*让你更自然地表示复杂的数据。我们将通过几个具体的例子来建立一些关于何时以及如何使用联合类型的直觉。

> **注意：**联合类型有时被称为[标签联合](https://en.wikipedia.org/wiki/Tagged_union)。一些社区将其称为[ADTs](https://en.wikipedia.org/wiki/Algebraic_data_type)。

## 过滤待办事项列表

> **问题：**我们正在创建一个[待办事项列表](http://evancz.github.io/elm-todomvc/)，其中充满了任务。我们想要有三个视图：显示*所有*任务，仅显示*活动*任务，仅显示*已完成*任务。我们如何表示我们处于这三种状态中的哪一种？

每当你在 Elm 中遇到奇怪形状的数据时，你会想要使用联合类型。在这种情况下，我们会创建一个名为`Visibility`的类型，它有三种可能的值：

```
> type Visibility = All | Active | Completed

> All
All : Visibility

> Active
Active : Visibility

> Completed
Completed : Visibility 
```

现在我们已经定义了这三种情况，我们想要创建一个名为`keep`的函数，它将正确地过滤我们的任务。它应该像这样工作：

```
type alias Task = { task : String, complete : Bool }

buy : Task
buy =
  { task = "Buy milk", complete = True }

drink : Task
drink =
  { task = "Drink milk", complete = False }

tasks : List Task
tasks =
  [ buy, drink ]

-- keep : Visibility -> List Task -> List Task

-- keep All tasks == [buy,drink]
-- keep Active tasks == [drink]
-- keep Complete tasks == [buy] 
```

因此，`keep`函数需要查看它的第一个参数，并根据它的内容以不同的方式过滤列表。我们使用`case`表达式来做到这一点。这就像是一个更强大的`if`：

```
keep : Visibility -> List Task -> List Task
keep visibility tasks =
  case visibility of
    All ->
      tasks

    Active ->
      List.filter (\task -> not task.complete) tasks

    Completed ->
      List.filter (\task -> task.complete) tasks 
```

`case`的意思是，看一看`visibility`的结构。如果它是`All`，就把所有的任务都交出来。如果是`Active`，只保留未完成的任务。如果是`Completed`，只保留已完成的任务。

`case`表达式的酷炫之处在于编译器会检查所有的分支。这带来了一些很好的好处：

1.  如果你无意中打错了`Compleet`，你会得到一个有关拼写错误的提示。

1.  如果你忘记处理一个情况，编译器会找出并告诉你。

所以说你想将`Recent`作为第四种可能的`Visibility`值添加进去。编译器将查找你的代码中所有使用`Visibility`值的`case`表达式，并提醒你处理新的可能性！这意味着你可以更改和扩展`Visibility`，而不会在现有代码中悄悄创建错误。

> **练习：** 想象一下你如何在 JavaScript 中解决相同的问题。三个字符串？一个可以为`null`的布尔值？`keep`的定义会是什么样子？你想要编写什么样的测试来确保稍后添加新代码是安全的。

## 匿名用户

> **问题：** 我们有一个聊天室，人们可以发布任何他们想要的东西。有些用户已登录，有些用户是匿名的。我们应该如何表示一个用户？

再一次，每当有奇怪形状的数据时，你都想使用联合类型。对于这种情况，我们想要一个用户要么是匿名的要么是命名的：

```
> type User = Anonymous | Named String

> Anonymous
Anonymous : User

> Named
<function> : String -> User

> Named "AzureDiamond"
Named "AzureDiamond" : User

> Named "abraham-lincoln"
Named "abraham-lincoln" : User 
```

所以创建`User`类型也创建了名为`Anonymous`和`Named`的构造函数。如果你想创建一个`User`，你*必须*使用这两个构造函数之一。这保证了所有可能的`User`值都是这样的：

```
 Anonymous
  Named "AzureDiamond"
  Named "abraham-lincoln"
  Named "catface420"
  Named "Tom"
  ... 
```

现在我们有了一个用户的表示，假设我们想要获取他们的照片以便在他们的帖子旁边显示。再次，我们需要使用一个`case`表达式来处理我们的`User`类型：

```
userPhoto : User -> String
userPhoto user =
  case user of
    Anonymous ->
      "anon.png"

    Named name ->
      "users/" ++ name ++ ".png" 
```

当我们有一个`User`时，有两种可能的情况。如果他们是`Anonymous`，我们显示一个虚拟图片。如果他们是`Named`，我们构造他们照片的 URL。这个`case`比我们之前看到的那个稍微花哨一点。注意第二个分支有一个小写变量`name`。这意味着当我们看到像`Named "AzureDiamond"`这样的值时，`name`变量将绑定到`"AzureDiamond"`，所以我们可以对其进行其他操作。这就是所谓的*模式匹配*。

现在假设我们有一群用户在一个聊天室里，我们想展示他们的图片。

```
activeUsers : List User
activeUsers =
  [ Anonymous, Named "catface420", Named "AzureDiamond", Anonymous ]

photos : List String
photos =
  List.map userPhoto activeUsers

-- [ "anon.png", "users/catface420.png", "users/AzureDiamond.png", "anon.png" ] 
```

创建像`User`这样的类型的好处是，你整个代码库中的任何人都不可能“忘记”一些用户可能是匿名的。任何能获取`User`的人都需要使用一个`case`来从中获取任何信息，编译器保证每个`case`都处理了所有可能的情况！

> **练习：** 想想你会如何用其他语言解决这个问题。一个字符串，空字符串表示他们是匿名的？一个可以为空的字符串？你会想要进行多少测试来确保每个人都正确处理这些特殊情况？

## 小部件仪表板

> **问题：** 你正在创建一个带有三种不同类型小部件的仪表板。一个显示最近的日志数据，一个显示时间图，一个显示散点图。如何表示一个小部件？

好了，我们现在有点高级了。在 Elm 中，你要从独立解决每种情况开始。（随着经验的增长，你会发现 Elm*希望*你从小而可重用的部分构建��序。这很奇怪。）所以我会为我们的三种情况创建表示，并编写`view`函数，将它们实际转换为 HTML 或 SVG 或其他内容：

```
type alias LogsInfo =
  { logs : List String
  }

type alias TimeInfo =
  { events : List (Time, Float)
  , yAxis : String
  }

type alias ScatterInfo =
  { points : List (Float, Float)
  , xAxis : String
  , yAxis : String
  }

-- viewLogs : LogsInfo -> Html msg
-- viewTime : TimeInfo -> Html msg
-- viewScatter : ScatterInfo -> Html msg 
```

到目前为止，你已经创建了所有需要独立处理这三种情况的辅助函数。稍后可以有人过来说，“我需要一个漂亮的方法来显示散点图”，然后只使用代码的那一部分。

所以问题实际上是：如何将这三个独立的事物组合起来以适应我的特定情况？

再次强调，联合类型用于组合各种不同的类型！

```
> type Widget = Logs LogsInfo | TimePlot TimeInfo | ScatterPlot ScatterInfo

> Logs
<function> : LogsInfo -> Widget

> TimePlot
<function> : TimeInfo -> Widget

> ScatterPlot
<function> : ScatterInfo -> Widget 
```

所以我们创建了一个只能使用这些构造函数创建的`Widget`类型。你可以将这些构造函数视为*标记*数据，以便我们可以在运行时区分它们。现在我们可以编写一些东西来渲染一个小部件，就像这样：

```
view : Widget -> Html msg
view widget =
  case widget of
    Logs info ->
      viewLogs info

    TimePlot info ->
      viewTime info

    ScatterPlot info ->
      viewScatter info 
```

这种方法的一个好处是，对于支持的小部件类型没有任何神秘之处。恰好有三种。如果有人想要添加第四种，他们会修改`Widget`类型。这意味着，即使其他团队的人在修改你的代码，你也永远不会对所获得的数据感到惊讶。

> **要点：**
> 
> +   先解决每个子问题。
> +   
> +   使用联合类型将所有解决方案组合在一起。
> +   
> +   创建一个联合类型会生成一堆*构造函数*。
> +   
> +   这些构造函数*标记*数据，以便我们可以在运行时区分它们。
> +   
> +   一个`case`表达式让我们根据这些标记拆分数据。
> +   
> 如果你正在制作游戏并有一堆不同的坏家伙，可以使用相同的策略。Goombas 应该以一种方式更新，但 Koopa Troopas 则完全不同。独立解决每个问题，然后使用联合类型将它们全部组合在一起。

## 链表

> **问题：** 你被困在一辆飞驰在高速公路上的公共汽车上。如果公共汽车减速，它将爆炸。拯救自己和公共汽车上的每个人的唯一方法是在 Elm 中重新实现链表。快点，我们的汽油快用完了！

是的，是的，这次问题是刻意设计的，但重要的是要看到你可以使用联合类型做一些更高级的事情！

一个[链表](https://en.wikipedia.org/wiki/Linked_list)是一系列值。如果你看着一个链表，它要么是空的，要么是一个值和更多的列表。那个列表要么是空的，要么是一个值和更多的列表。等等。这种直观的定义在 Elm 中直接有效。让我们看看整数列表的情况：

```
> type IntList = Empty | Node Int IntList

> Empty
Empty : IntList

> Node
<function> : Int -> IntList -> IntList

> Node 42 Empty
Node 42 Empty : IntList

> Node 64 (Node 128 Empty)
Node 64 (Node 128 Empty) : IntList 
```

现在我们在这里做了两件新事情：

1.  `Node`构造函数接受*两个*参数而不是一个。这没问题。事实上，你可以让它们接受任意数量的参数。

1.  我们的联合类型是*递归*的。`IntList`可能包含另一个`IntList`。同样，如果使用联合类型，这是可以的。

我们的`IntList`类型的好处在于现在我们只能构建有效的链表。每个链表都需要以`Empty`开始，而添加新值的唯一方法是使用`Node`。

它同样易于使用。假设我们想计算列表中所有数字的总和。与任何其他联合类型一样，我们需要使用`case`并处理所有可能的情况：

```
sum : IntList -> Int
sum numbers =
  case numbers of
    Empty ->
      0

    Node n remainingNumbers ->
      n + sum remainingNumbers 
```

如果我们得到一个`Empty`值，总和就是 0。如果我们有一个`Node`，我们将第一个元素加到所有剩余元素的总和中。因此，表达式`(sum (Node 1 (Node 2 (Node 3 Empty))))`的评估如下：

```
 sum (Node 1 (Node 2 (Node 3 Empty)))
  1 + sum (Node 2 (Node 3 Empty))
  1 + (2 + sum (Node 3 Empty))
  1 + (2 + (3 + sum Empty))
  1 + (2 + (3 + 0))
  1 + (2 + 3)
  1 + 5
  6 
```

在每一行上，我们看到一个评估步骤。当我们调用`sum`时，它会根据它是在查看`Node`还是`Empty`值来转换列表。

> **注意：**这是我们一起编写的第一个递归函数！请注意，`sum`调用自身以获得总和。编写递归函数的思维模式可能会有些棘手，因此我想分享一个奇怪的技巧。**假装你已经完成了。**
> 
> 我总是从一个`case`开始，列出所有分支但未填写。从那里，我逐个解决每个分支，假装没有其他东西存在。因此，对于`sum`，我会看`Empty ->`并说，空列表必须总和为零。然后我会看`Node n remainingNumbers ->`分支，并想，嗯，我知道我有一个数字，一个列表，还有一个肯定已经存在并且完全有效的`sum`函数。我可以只是使用它并将数字添加到其中！

## 通用数据结构

> **问题：**上一节展示了仅适用于整数的链表。那太糟糕了。我们如何制作可以保存任何类型值的链表？

一切都基本相同，只是在我们的列表定义中引入了*类型变量*：

```
> type List a = Empty | Node a (List a)

> Empty
Empty : List a

> Node
<function> : a -> List a -> List a

> Node "hi" Empty
Node "hi" Empty : List String

> Node 1.618 (Node 6.283 Empty)
Node 1.618 (Node 6.283 Empty) : List Float 
```

精彩之处在于`Node`构造函数。我们不是将数据固定在`Int`和`IntList`上，而是说它可以保存`a`和`List a`。基本上，只要添加的值与列表中的所有其他值的类型相同，就可以添加一个值。

其他一切都一样。您可以使用`case`对列表进行模式匹配，并编写递归函数。唯一的区别是我们的列表现在可以保存任何东西！

> **练习：**这正是 Elm 中的`List`类型的工作方式，因此请查看[列表库](http://package.elm-lang.org/packages/elm-lang/core/latest/List) ，看看您是否可以自己实现其中一些函数。

## 额外的例子

我们已经看到了一些情况，但更加熟悉的最佳方法是更多地使用联合类型！因此，这里有两个有趣的例子。

### 二叉树

[二叉树](https://zh.wikipedia.org/wiki/%E4%BA%8C%E5%8F%89%E6%A0%91)与链表几乎完全相同：

```
> type Tree a = Empty | Node a (Tree a) (Tree a)

> Node
<function> : a -> Tree a -> Tree a -> Tree a

> Node "hi" Empty Empty
Node "hi" Empty Empty : Tree String 
```

树要么为空，要么是具有值和两个子节点的节点。查看[此示例](http://elm-lang.org/examples/binary-tree)了解更多信息。如果您能完成该链接末尾的所有练习，请自认为是联合类型的熟练用户！

### 语言

我们甚至可以将编程语言建模为数据，如果我们想要变得疯狂的话！在这种情况下，它是仅涉及[布尔代数](https://en.wikipedia.org/wiki/Boolean_algebra#Operations)的一种语言：

```
type Boolean
    = T
    | F
    | Not Boolean
    | And Boolean Boolean
    | Or Boolean Boolean

true = Or T F
false = And T (Not T) 
```

一旦我们对可能的值进行了建模，我们就可以定义像`eval`这样的函数，它将任何`Boolean`评估为`True`或`False`。查看[此示例](http://elm-lang.org/examples/boolean-expressions)了解更多关于表示布尔表达式的内容。
