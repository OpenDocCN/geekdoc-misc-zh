# “递归类型和折叠”系列

在这个系列中，我们将看到递归类型及其如何使用，并在此过程中，我们将看到积累、尾递归、左折叠和右折叠之间的区别等等。

+   递归类型简介。不要害怕积累....

+   积累示例。将规则应用于其他领域。

+   介绍折叠。通过递归数据结构传递状态。

+   理解折叠。递归 vs. 迭代。

+   通用递归类型。以三种方式实现领域。

+   现实世界中的树。使用数据库、JSON 和错误处理的示例。

# 递归类型简介

# 递归类型简介

在这个系列中，我们将看到递归类型及其如何使用，并在此过程中，我们将看到积累、尾递归、左折叠和右折叠之间的区别等等。

## 系列内容

这个系列的内容如下：

+   **第 1 部分：介绍递归类型和积累**

    +   一个简单的递归类型

    +   参数化一切

    +   介绍积累

    +   积累的好处

    +   创建积累的规则

+   **第 2 部分：积累示例**

    +   积累示例：文件系统领域

    +   积累示例：产品领域

+   **第 3 部分：介绍折叠**

    +   我们的积累实现中的一个缺陷

    +   介绍 `fold`

    +   折叠的问题

    +   将函数用作累加器

    +   介绍 `foldback`

    +   创建折叠的规则

+   **第 4 部分：理解折叠**

    +   迭代 vs. 递归

    +   折叠示例：文件系统领域

    +   关于“fold”的常见问题

+   **第 5 部分：通用递归类型**

    +   LinkedList：一个通用的递归类型

    +   使 Gift 领域通用化

    +   定义一个通用的容器类型

    +   实现礼品领域的第三种方法

    +   抽象还是具体？比较这三种设计

+   **第 6 部分：现实世界中的树**

    +   定义通用的树类型

    +   现实世界中的树类型

    +   映射树类型

    +   示例：创建目录列表

    +   示例：并行 grep

    +   示例：将文件系统存储在数据库中

    +   示例：将树序列化为 JSON

    +   示例：从 JSON 反序列化树

    +   示例：从 JSON 反序列化树-带错误处理

* * *

## 一个基本的递归类型

让我们从一个简单的例子开始--如何建模一个礼物。

碰巧，我是一个非常懒惰的送礼者。我总是送人一本书或巧克力。我通常会包装它们，有时，如果我感觉格外慷慨，我会把它们放在礼品盒里，还会加上一张卡片。

让我们看看我如何在类型中建模这个：

```
type Book = {title: string; price: decimal}

type ChocolateType = Dark | Milk | SeventyPercent
type Chocolate = {chocType: ChocolateType ; price: decimal}

type WrappingPaperStyle = 
    | HappyBirthday
    | HappyHolidays
    | SolidColor

type Gift =
    | Book of Book
    | Chocolate of Chocolate 
    | Wrapped of Gift * WrappingPaperStyle
    | Boxed of Gift 
    | WithACard of Gift * message:string 
```

你可以看到三种情况是指向另一个`Gift`的“容器”。`Wrapped`情况有一些纸和一个内部礼物，`Boxed`情况也是如此，`WithACard`情况也是如此。另外两种情况，`Book`和`Chocolate`，不涉及礼物，可以被视为“叶”节点或终端。

在这三种情况中引用内部`Gift`使`Gift`成为*递归类型*。请注意，与函数不同，定义递归类型时*不*需要使用`rec`关键字。

让我们创建一些示例值：

```
// a Book
let wolfHall = {title="Wolf Hall"; price=20m}

// a Chocolate
let yummyChoc = {chocType=SeventyPercent; price=5m}

// A Gift
let birthdayPresent = WithACard (Wrapped (Book wolfHall, HappyBirthday), "Happy Birthday")
//  WithACard (
//    Wrapped (
//      Book {title = "Wolf Hall"; price = 20M},
//      HappyBirthday),
//    "Happy Birthday")

// A Gift
let christmasPresent = Wrapped (Boxed (Chocolate yummyChoc), HappyHolidays)
//  Wrapped (
//    Boxed (
//      Chocolate {chocType = SeventyPercent; price = 5M}),
//    HappyHolidays) 
```

在我们开始处理这些值之前，给出一个建议...

### 指南：避免无限递归类型

我建议，在 F#中，每个递归类型都应该包含递归和非递归情况的混合。如果没有非递归元素，比如`Book`，那么该类型的所有值都必须是无限递归的。

例如，在下面的`ImpossibleGift`类型中，所有情况都是递归的。要构造任何一个情况，你需要一个内部礼物，而那也需要被构造，依此类推。

```
type ImpossibleGift =
    | Boxed of ImpossibleGift 
    | WithACard of ImpossibleGift * message:string 
```

如果允许[懒惰](https://wiki.haskell.org/Tying_the_Knot)、变异或反射，就可以创建这种类型。但一般来说，在像 F#这样的非懒惰语言中，最好避免使用这种类型。

### 处理递归类型

公共服务公告结束--让我们开始编码吧！

首先，我们说我们想要一个礼物的描述。逻辑将是：

+   对于两种非递归情况，返回描述该情况的字符串。

+   对于三种递归情况，返回描述该情况的字符串，但也包括内部礼物的描述。这意味着`description`函数将引用自身，因此必须用`rec`关键字标记。

这里是一个示例实现：

```
let rec description gift =
    match gift with 
    | Book book -> 
        sprintf "'%s'" book.title 
    | Chocolate choc -> 
        sprintf "%A chocolate" choc.chocType
    | Wrapped (innerGift,style) -> 
        sprintf "%s wrapped in %A paper" (description innerGift) style
    | Boxed innerGift -> 
        sprintf "%s in a box" (description innerGift) 
    | WithACard (innerGift,message) -> 
        sprintf "%s with a card saying '%s'" (description innerGift) message 
```

注意`Boxed`情况中的递归调用，如下所示：

```
 | Boxed innerGift -> 
        sprintf "%s in a box" (description innerGift) 
                               ~~~~~~~~~~~ <= recursive call 
```

如果我们尝试用我们的示例值来做这个，让我们看看我们会得到什么：

```
birthdayPresent |> description  
// "'Wolf Hall' wrapped in HappyBirthday paper with a card saying 'Happy Birthday'"

christmasPresent |> description  
// "SeventyPercent chocolate in a box wrapped in HappyHolidays paper" 
```

对我来说看起来很不错。像`HappyHolidays`这样的东西没有空格看起来有点奇怪，但足以演示这个想法。

创建另一个函数怎么样？例如，一个礼物的总成本是多少？

对于`totalCost`，逻辑将是：

+   书籍和巧克力在特定情况下捕获了价格，所以使用它。

+   包装将成本增加`0.5`。

+   一个盒子将成本增加`1.0`。

+   一张卡将成本增加`2.0`。

```
let rec totalCost gift =
    match gift with 
    | Book book -> 
        book.price
    | Chocolate choc -> 
        choc.price
    | Wrapped (innerGift,style) -> 
        (totalCost innerGift) + 0.5m
    | Boxed innerGift -> 
        (totalCost innerGift) + 1.0m
    | WithACard (innerGift,message) -> 
        (totalCost innerGift) + 2.0m 
```

这是两个示例的成本：

```
birthdayPresent |> totalCost 
// 22.5m

christmasPresent |> totalCost 
// 6.5m 
```

有时候，人们问盒子或包装纸里面装了什么。一个`whatsInside`函数很容易实现——只需忽略容器情况并为非递归情况返回一些内容。

```
let rec whatsInside gift =
    match gift with 
    | Book book -> 
        "A book"
    | Chocolate choc -> 
        "Some chocolate"
    | Wrapped (innerGift,style) -> 
        whatsInside innerGift
    | Boxed innerGift -> 
        whatsInside innerGift
    | WithACard (innerGift,message) -> 
        whatsInside innerGift 
```

结果如下：

```
birthdayPresent |> whatsInside 
// "A book"

christmasPresent |> whatsInside 
// "Some chocolate" 
```

这是一个很好的开始——三个函数，都很容易编写。

## 参数化所有东西

然而，这三个函数有一些重复的代码。除了独特的应用逻辑之外，每个函数都在进行自己的模式匹配和递归访问内部礼物的逻辑。

我们如何将导航逻辑与应用逻辑分开？

答案：参数化所有东西！

一如既往，我们可以通过传递函数来参数化应用程序逻辑。在这种情况下，我们将需要*五个*函数，每个情况一个。

这是新的、参数化版本——我会解释为什么我称它为`cataGift`的。

```
let rec cataGift fBook fChocolate fWrapped fBox fCard gift =
    match gift with 
    | Book book -> 
        fBook book
    | Chocolate choc -> 
        fChocolate choc
    | Wrapped (innerGift,style) -> 
        let innerGiftResult = cataGift fBook fChocolate fWrapped fBox fCard innerGift
        fWrapped (innerGiftResult,style)
    | Boxed innerGift -> 
        let innerGiftResult = cataGift fBook fChocolate fWrapped fBox fCard innerGift
        fBox innerGiftResult 
    | WithACard (innerGift,message) -> 
        let innerGiftResult = cataGift fBook fChocolate fWrapped fBox fCard innerGift
        fCard (innerGiftResult,message) 
```

您可以看到，这个函数是使用一个纯机械的过程创建的：

+   每个函数参数（`fBook`，`fChocolate`等）对应一个情况。

+   对于两个非递归情况，将函数参数传递给与该情况相关的所有数据。

+   对于三个递归情况，有两个步骤：

    +   首先，在`innerGift`上递归调用`cataGift`函数以获得`innerGiftResult`

    +   然后，适当的处理程序将所有与该情况相关的数据传递给它，但是使用`innerGiftResult`替换`innerGift`。

让我们使用通用的`cataGift`函数重写总成本。

```
let totalCostUsingCata gift =
    let fBook (book:Book) = 
        book.price
    let fChocolate (choc:Chocolate) = 
        choc.price
    let fWrapped  (innerCost,style) = 
        innerCost + 0.5m
    let fBox innerCost = 
        innerCost + 1.0m
    let fCard (innerCost,message) = 
        innerCost + 2.0m
    // call the catamorphism
    cataGift fBook fChocolate fWrapped fBox fCard gift 
```

注：

+   现在，`innerGiftResult`是内部礼物的总成本，所以我将其重命名为`innerCost`。

+   `totalCostUsingCata`函数本身不是递归的，因为它使用了`cataGift`函数，所以不再需要`rec`关键字。

这个函数给出了与以前相同的结果：

```
birthdayPresent |> totalCostUsingCata 
// 22.5m 
```

我们可以以同样的方式使用`cataGift`重写`description`函数，将`innerGiftResult`改为`innerText`。

```
let descriptionUsingCata gift =
    let fBook (book:Book) = 
        sprintf "'%s'" book.title 
    let fChocolate (choc:Chocolate) = 
        sprintf "%A chocolate" choc.chocType
    let fWrapped (innerText,style) = 
        sprintf "%s wrapped in %A paper" innerText style
    let fBox innerText = 
        sprintf "%s in a box" innerText
    let fCard (innerText,message) = 
        sprintf "%s with a card saying '%s'" innerText message
    // call the catamorphism
    cataGift fBook fChocolate fWrapped fBox fCard gift 
```

结果和以前一样：

```
birthdayPresent |> descriptionUsingCata  
// "'Wolf Hall' wrapped in HappyBirthday paper with a card saying 'Happy Birthday'"

christmasPresent |> descriptionUsingCata  
// "SeventyPercent chocolate in a box wrapped in HappyHolidays paper" 
```

## 引入折叠函数

我们上面写的`cataGift`函数被称为"[折叠函数](https://en.wikipedia.org/wiki/Catamorphism)"，来自希腊词组"向下 + 形状"。在正常用法中，折叠函数是一个根据其*结构*将递归类型"折叠"为新值的函数。实际上，您可以将折叠函数看作是一种"访问者模式"。

折叠函数是一个非常强大的概念，因为它是您可以为这样的结构定义的最基本函数。*任何其他函数*都可以用它来定义。

也就是说，如果我们想要创建一个带有签名`Gift -> string`或`Gift -> int`的函数，我们可以使用 catamorphism 通过为`Gift`结构中的每个案例指定一个函数来创建它。

我们上面看到了如何使用 catamorphism 重写`totalCost`为`totalCostUsingCata`，以及以后会看到许多其他示例。

### Catamorphisms 和 folds

虽然`Catamorphisms`通常被称为“folds”，但是有多种类型的折叠，所以我倾向于使用“catamorphism”来指代*概念*，并使用“fold”来指代特定类型的实现。

我将在后续帖子中详细讨论各种折叠类型，所以在本帖子的其余部分，我将仅使用“catamorphism”。

### 整理实现

上面的`cataGift`实现故意冗长，以便您可以看到每个步骤。不过一旦您理解了正在发生的事情，您可以稍微简化它。

首先，`cataGift fBook fChocolate fWrapped fBox fCard`出现了三次，每次都是为了处理递归情况。让我们给它分配一个名称，比如`recurse`：

```
let rec cataGift fBook fChocolate fWrapped fBox fCard gift =
    let recurse = cataGift fBook fChocolate fWrapped fBox fCard
    match gift with 
    | Book book -> 
        fBook book
    | Chocolate choc -> 
        fChocolate choc
    | Wrapped (innerGift,style) -> 
        let innerGiftResult = recurse innerGift
        fWrapped (innerGiftResult,style)
    | Boxed innerGift -> 
        let innerGiftResult = recurse innerGift
        fBox innerGiftResult 
    | WithACard (innerGift,message) -> 
        let innerGiftResult = recurse innerGift
        fCard (innerGiftResult,message) 
```

`recurse`函数具有简单的签名`Gift -> 'a` -- 也就是说，它将`Gift`转换为我们需要的返回类型，因此我们可以使用它来处理各种`innerGift`值。

另一件事是在递归案例中将`innerGift`替换为`gift`--这被称为“遮蔽”。好处是“外部”的`gift`不再对案例处理代码可见，因此我们不会意外地递归进入其中，这会导致无限循环。

通常我会避免遮蔽，但这是一种情况，实际上这是一种良好的做法，因为它消除了一种特别讨厌的 bug。

这是清理后的版本：

```
let rec cataGift fBook fChocolate fWrapped fBox fCard gift =
    let recurse = cataGift fBook fChocolate fWrapped fBox fCard
    match gift with 
    | Book book -> 
        fBook book
    | Chocolate choc -> 
        fChocolate choc
    | Wrapped (gift,style) -> 
        fWrapped (recurse gift,style)
    | Boxed gift -> 
        fBox (recurse gift)
    | WithACard (gift,message) -> 
        fCard (recurse gift,message) 
```

还有一件事。我会明确注释返回类型并将其称为`'r`。在这个系列的后续部分中，我们将处理其他泛型类型，比如`'a`和`'b`，所以保持一致并始终为返回类型使用标准名称会很有帮助。

```
let rec cataGift fBook fChocolate fWrapped fBox fCard gift :'r =
//                                name the return type =>  ~~~~ 
```

这是最终版本：

```
let rec cataGift fBook fChocolate fWrapped fBox fCard gift :'r =
    let recurse = cataGift fBook fChocolate fWrapped fBox fCard
    match gift with 
    | Book book -> 
        fBook book
    | Chocolate choc -> 
        fChocolate choc
    | Wrapped (gift,style) -> 
        fWrapped (recurse gift,style)
    | Boxed gift -> 
        fBox (recurse gift)
    | WithACard (gift,message) -> 
        fCard (recurse gift,message) 
```

比起原始实现，这简单多了，也展示了像`Wrapped (gift,style)`这样的案例构造函数与相应的处理函数`fWrapped (recurse gift,style)`之间的对称性。这让我们很好地过渡到了...

### 类型构造函数和处理程序之间的关系

这是`cataGift`函数的签名。你可以看到每个案例处理函数（`fBook`，`fBox`等）都有相同的模式：一个包含该案例所有数据的输入，以及一个共同的输出类型`'r`。

```
val cataGift :
  fBook:(Book -> 'r) ->
  fChocolate:(Chocolate -> 'r) ->
  fWrapped:('r * WrappingPaperStyle -> 'r) ->
  fBox:('r -> 'r) ->
  fCard:('r * string -> 'r) -> 
  // input value
  gift:Gift -> 
  // return value
  'r 
```

另一种思考这个问题的方式是：在构造函数中的每个`Gift`类型处，它都已被替换为`'r`。

例如：

+   `Gift.Book`构造函数接受一个`Book`并返回一个`Gift`。`fBook`处理程序接受一个`Book`并返回一个`'r`。

+   `Gift.Wrapped`构造函数接受一个`Gift * WrappingPaperStyle`并返回一个`Gift`。`fWrapped`处理程序接受一个`'r * WrappingPaperStyle`作为输入，并返回一个`'r`。

这里通过类型签名表达了这种关系：

```
// The Gift.Book constructor 
Book -> Gift

// The fBook handler
Book -> 'r

// The Gift.Wrapped constructor 
Gift * WrappingPaperStyle -> Gift

// The fWrapped handler
'r   * WrappingPaperStyle -> 'r

// The Gift.Boxed constructor 
Gift -> Gift

// The fBox handler
'r   -> 'r 
```

等等，其他的都是一样的。

## 范畴折叠的好处

有很多关于范畴折叠的理论，但实践中有什么好处呢？

为什么要创建像`cataGift`这样的特殊函数？为什么不只是保留原始函数？

包括以下原因：

+   **重用**。稍后，我们将创建相当复杂的范畴折叠。如果你只需一次正确地处理逻辑就好了。

+   **封装**。通过仅暴露函数，你隐藏了数据类型的内部结构。

+   **灵活性**。函数比模式匹配更灵活 -- 它们可以组合，部分应用等。

+   **映射**。有了范畴折叠，你可以轻松地创建将各种情况映射到新结构的函数。

尽管大多数这些好处也适用于非递归类型，但递归类型往往更复杂，因此封装、灵活性等好处相应更强。

在接下来的章节中，我们将更详细地看一下最后三点。

### 使用函数参数隐藏内部结构

第一个好处是范畴折叠将内部设计抽象出来。通过使用函数，客户端代码与内部结构有些隔离。同样，你可以将访问者模式视为面向对象世界中的类比。

例如，如果所有客户端都使用范畴折叠函数而不是模式匹配，我可以安全地重命名情况，甚至在小心的情况下添加或删除情况。

这里有一个例子。假设我之前为`Gift`设计了一个没有`WithACard`情况的版本。我将其称为版本 1：

```
type Gift =
    | Book of Book
    | Chocolate of Chocolate 
    | Wrapped of Gift * WrappingPaperStyle
    | Boxed of Gift 
```

假设我们构建并发布了针对该结构的范畴折叠函数：

```
let rec cataGift fBook fChocolate fWrapped fBox gift :'r =
    let recurse = cataGift fBook fChocolate fWrapped fBox 
    match gift with 
    | Book book -> 
        fBook book
    | Chocolate choc -> 
        fChocolate choc
    | Wrapped (gift,style) -> 
        fWrapped (recurse gift,style)
    | Boxed gift -> 
        fBox (recurse gift) 
```

请注意，这只有*四*个函数参数。

现在假设`Gift`的第 2 个版本出现，添加了`WithACard`情况：

```
type Gift =
    | Book of Book
    | Chocolate of Chocolate 
    | Wrapped of Gift * WrappingPaperStyle
    | Boxed of Gift 
    | WithACard of Gift * message:string 
```

现在有五种情况。

经常情况下，当我们添加一个新情况时，*希望*打破所有客户端，强迫他们处理新情况。

但有时候，我们不这样做。因此，我们可以通过默默处理额外情况来保持与原始`cataGift`的兼容性，就像这样：

```
/// Uses Gift_V2 but is still backwards compatible with the earlier "cataGift".
let rec cataGift fBook fChocolate fWrapped fBox gift :'r =
    let recurse = cataGift fBook fChocolate fWrapped fBox 
    match gift with 
    | Book book -> 
        fBook book
    | Chocolate choc -> 
        fChocolate choc
    | Wrapped (gift,style) -> 
        fWrapped (recurse gift,style)
    | Boxed gift -> 
        fBox (recurse gift)
    // pass through the new case silently 
    | WithACard (gift,message) -> 
        recurse gift 
```

这个函数仍然只有四个函数参数 -- 对于`WithACard`情况没有特殊行为。

有许多其他兼容的替代方法，比如返回一个默认值。重要的是客户端不知道这个变化。

**另外：使用活动模式隐藏数据**

当谈到隐藏类型结构时，我应该提到你也可以使用活动模式来做到这一点。

例如，我们可以为前四种情况创建一个活动模式，并忽略`WithACard`情况。

```
let rec (|Book|Chocolate|Wrapped|Boxed|) gift =
    match gift with 
    | Gift.Book book -> 
        Book book
    | Gift.Chocolate choc -> 
        Chocolate choc
    | Gift.Wrapped (gift,style) -> 
        Wrapped (gift,style)
    | Gift.Boxed gift -> 
        Boxed gift
    | Gift.WithACard (gift,message) -> 
        // ignore the message and recurse into the gift
        (|Book|Chocolate|Wrapped|Boxed|) gift 
```

客户端可以在不知道新情况存在的情况下对这四种情况进行模式匹配：

```
let rec whatsInside gift =
    match gift with 
    | Book book -> 
        "A book"
    | Chocolate choc -> 
        "Some chocolate"
    | Wrapped (gift,style) -> 
        whatsInside gift
    | Boxed gift -> 
        whatsInside gift 
```

### 处理情况的函数 vs. 模式匹配

Catamorphisms 使用函数参数，正如上面所述，函数比模式匹配更灵活，因为可以使用组合、部分应用等工具。

这是一个例子，其中所有“容器”情况都被忽略，只处理“内容”情况。

```
let handleContents fBook fChocolate gift =
    let fWrapped (innerGiftResult,style) =   
        innerGiftResult
    let fBox innerGiftResult = 
        innerGiftResult
    let fCard (innerGiftResult,message) = 
        innerGiftResult

    // call the catamorphism
    cataGift fBook fChocolate fWrapped fBox fCard gift 
```

这是它的使用方式，剩下的两种情况使用管道“内联”处理：

```
birthdayPresent 
|> handleContents 
    (fun book -> "The book you wanted for your birthday") 
    (fun choc -> "Your fave chocolate")
// Result => "The book you wanted for your birthday"

christmasPresent 
|> handleContents 
    (fun book -> "The book you wanted for Christmas") 
    (fun choc -> "Don't eat too much over the holidays!")
// Result => "Don't eat too much over the holidays!" 
```

当然，这也可以通过模式匹配来完成，但直接使用现有的`cataGift`函数可以让生活更轻松。

### 使用 catamorphisms 进行映射

我之前说过，catamorphism 是一个将递归类型“折叠”为新值的函数。例如，在`totalCost`中，递归的礼物结构被折叠成一个单一的成本值。

但是“单一值”不仅仅是一个原始值 -- 它也可以是一个复杂的结构，比如另一个递归结构。

实际上，catamorphisms 非常适合将一种结构映射到另一种结构，特别是它们非常相似的情况。

例如，假设我有一个喜欢巧克力的室友，他会偷偷拿走并吃掉礼物中的任何巧克力，留下包装不动，但丢弃盒子和礼品卡。

最后剩下的是一个“减去巧克力的礼物”，我们可以这样建模：

```
type GiftMinusChocolate =
    | Book of Book
    | Apology of string
    | Wrapped of GiftMinusChocolate * WrappingPaperStyle 
```

我们可以很容易地从`礼物`映射到`减去巧克力的礼物`，因为这些情况几乎是平行的。

+   一个`书`被保持不变地传递。

+   巧克力被吃掉，然后用一个`道歉`替换。

+   `包装`情况被保持不变地传递。

+   `盒子`和`带卡片`的情况被忽略。

这是代码：

```
let removeChocolate gift =
    let fBook (book:Book) = 
        Book book
    let fChocolate (choc:Chocolate) = 
        Apology "sorry I ate your chocolate"
    let fWrapped (innerGiftResult,style) = 
        Wrapped (innerGiftResult,style) 
    let fBox innerGiftResult = 
        innerGiftResult
    let fCard (innerGiftResult,message) = 
        innerGiftResult
    // call the catamorphism
    cataGift fBook fChocolate fWrapped fBox fCard gift 
```

如果我们测试...

```
birthdayPresent |> removeChocolate
// GiftMinusChocolate = 
//     Wrapped (Book {title = "Wolf Hall"; price = 20M}, HappyBirthday)

christmasPresent |> removeChocolate
// GiftMinusChocolate = 
//     Wrapped (Apology "sorry I ate your chocolate", HappyHolidays) 
```

### 深度复制

还有一件事。记住每个情况处理函数都带有与该情况相关联的数据吗？这意味着我们可以直接使用*原始情况构造函数*作为函数！

为了理解我的意思，让我们定义一个名为`deepCopy`的函数，它克隆原始值。每个情况处理程序只是相应的情况构造函数：

```
let deepCopy gift =
    let fBook book = 
        Book book 
    let fChocolate (choc:Chocolate) = 
        Chocolate choc
    let fWrapped (innerGiftResult,style) = 
        Wrapped (innerGiftResult,style) 
    let fBox innerGiftResult = 
        Boxed innerGiftResult
    let fCard (innerGiftResult,message) = 
        WithACard (innerGiftResult,message) 
    // call the catamorphism
    cataGift fBook fChocolate fWrapped fBox fCard gift 
```

我们可以通过删除每个处理程序的冗余参数进一步简化这个过程：

```
let deepCopy gift =
    let fBook = Book 
    let fChocolate = Chocolate 
    let fWrapped = Wrapped 
    let fBox = Boxed 
    let fCard = WithACard 
    // call the catamorphism
    cataGift fBook fChocolate fWrapped fBox fCard gift 
```

你可以自己测试这个是否有效：

```
christmasPresent |> deepCopy
// Result => 
//   Wrapped ( 
//    Boxed (Chocolate {chocType = SeventyPercent; price = 5M;}),
//    HappyHolidays) 
```

这导致了另一种思考 catamorphism 的方式：

+   Catamorphism 是适用于递归类型的函数，当您传入类型的情况构造函数时，您会得到一个“克隆”函数。

### 在一次遍历中进行映射和转换

对`deepCopy`进行轻微变体，允许我们递归遍历对象并在此过程中更改其中的位。

例如，假设我不喜欢牛奶巧克力。好吧，我可以编写一个函数，将礼物升级为更好质量的巧克力，同时保持所有其他情况不变。

```
let upgradeChocolate gift =
    let fBook = Book 
    let fChocolate (choc:Chocolate) = 
        Chocolate {choc with chocType = SeventyPercent}
    let fWrapped = Wrapped 
    let fBox = Boxed 
    let fCard = WithACard 
    // call the catamorphism
    cataGift fBook fChocolate fWrapped fBox fCard gift 
```

这里是使用的示例：

```
// create some chocolate I don't like
let cheapChoc = Boxed (Chocolate {chocType=Milk; price=5m})

// upgrade it!
cheapChoc |> upgradeChocolate
// Result =>
//   Boxed (Chocolate {chocType = SeventyPercent; price = 5M}) 
```

如果你认为这开始有点像`map`，那么你是对的。我们将在第六篇文章中看到通用映射，作为对通用递归类型讨论的一部分。

## 创建 catamorphisms 的规则

我们之前看到创建 catamorphism 是一个机械过程：

+   创建一个函数参数来处理结构中的每种情况。

+   对于非递归情况，将函数参数传递给与该情况相关的所有数据。

+   对于递归情况，执行两个步骤：

    +   首先，在嵌套值上递归调用猫摄影术。

    +   然后将处理程序传递给该情况的所有数据，但将猫摄影术的结果替换原始嵌套值。

现在让我们看看是否可以应用这些规则来在其他领域创建猫摄影术。

* * *

## 总结

本文中我们已经看到如何定义递归类型，并介绍了猫摄影术。

在下一篇文章中，我们将使用这些规则为其他领域创建猫摄影术。

那么，我们下次见！

*本文的源代码可在[此代码片段](https://gist.github.com/swlaschin/60938b4417d12cfa0a97)中找到。*

# 猫摄影术示例

# 猫摄影术示例

本文是系列中的第二篇。

在上一篇文章中，我介绍了“猫摄影术”，这是一种创建递归类型函数的方法，并列举了一些可用于机械实现它们的规则。在本文中，我们将使用这些规则来为其他领域实现猫摄影术。

## 系列内容

以下是本系列的内容：

+   **第 1 部分：递归类型和猫摄影术简介**

    +   一个简单的递归类型

    +   参数化所有事物

    +   介绍猫摄影术

    +   猫摄影术的好处

    +   创建猫摄影术的规则

+   **第 2 部分：猫摄影术示例**

    +   猫摄影术示例：文件系统领域

    +   猫摄影术示例：产品领域

+   **第 3 部分：介绍折叠**

    +   我们猫摄影术实现中的一个缺陷

    +   介绍`fold`

    +   折叠的问题

    +   将函数用作累加器

    +   介绍`foldback`

    +   创建折叠的规则

+   **第 4 部分：理解折叠**

    +   迭代与递归的比较

    +   折叠示例：文件系统领域

    +   关于“折叠”的常见问题

+   **第 5 部分：通用递归类型**

    +   链表：一个通用递归类型

    +   使礼物领域变得通用

    +   定义通用的容器类型

    +   实现礼物领域的第三种方法

    +   抽象还是具体？比较这三种设计

+   **第 6 部分：现实世界中的树**

    +   定义通用的 Tree 类型

    +   现实世界中的 Tree 类型

    +   映射 Tree 类型

    +   示例：创建目录列表

    +   示例：并行 grep

    +   示例：将文件系统存储在数据库中

    +   示例：将树序列化为 JSON

    +   示例：从 JSON 反序列化树

    +   示例：从 JSON 反序列化树 - 带错误处理

* * *

## 创建 catamorphisms 的规则

我们在上一篇帖子中看到，创建 catamorphism 是一个机械过程，规则是：

+   为结构中的每种情况创建一个函数参数来处理。

+   对于非递归情况，将函数参数传递给与该情况相关联的所有数据。

+   对于递归情况，执行两个步骤：

    +   首先，在嵌套值上递归调用 catamorphism。

    +   然后，将处理程序传递给该情况相关联的所有数据，但是结果 catamorphism 替换了原始的嵌套值。

现在让我们看看是否可以应用这些规则来创建其他领域的 catamorphisms。

* * *

## Catamorphism 示例：文件系统领域

让我们从一个非常简陋的文件系统模型开始：

+   每个文件都有一个名称和一个大小。

+   每个目录都有一个名称、一个大小和一个子项列表。

这是我可能会模拟的方式：

```
type FileSystemItem =
    | File of File
    | Directory of Directory
and File = {name:string; fileSize:int}
and Directory = {name:string; dirSize:int; subitems:FileSystemItem list} 
```

我承认这是一个相当糟糕的模型，但对于这个例子来说已经足够好了！

好的，这里有一些示例文件和目录：

```
let readme = File {name="readme.txt"; fileSize=1}
let config = File {name="config.xml"; fileSize=2}
let build  = File {name="build.bat"; fileSize=3}
let src = Directory {name="src"; dirSize=10; subitems=[readme; config; build]}
let bin = Directory {name="bin"; dirSize=10; subitems=[]}
let root = Directory {name="root"; dirSize=5; subitems=[src; bin]} 
```

是时候创建 **catamorphism** 了！

让我们从查看签名开始，找出我们需要什么。

`File` 构造函数接受一个 `File` 并返回一个 `FileSystemItem`。根据上述指南，`File` 情况的处理程序需要具有签名 `File -> 'r`。

```
// case constructor
File  : File -> FileSystemItem

// function parameter to handle File case 
fFile : File -> 'r 
```

这很简单。让我们组合一个初始的 `cataFS` 框架，我将其称为：

```
let rec cataFS fFile fDir item :'r = 
    let recurse = cataFS fFile fDir 
    match item with
    | File file -> 
        fFile file
    | Directory dir -> 
        // to do 
```

`Directory` 情况更加复杂。如果我们天真地应用上述指南，`Directory` 情况的处理程序将具有签名 `Directory -> 'r`，但那将是不正确的，因为 `Directory` 记录本身包含一个需要用 `'r` 替换的 `FileSystemItem`。我们该怎么办？

一种方法是将 `Directory` 记录 "爆炸" 成一个元组 `(string,int,FileSystemItem list)`，然后在其中也用 `'r` 替换 `FileSystemItem`。

换句话说，我们有以下转换序列：

```
// case constructor (Directory as record)
Directory : Directory -> FileSystemItem

// case constructor (Directory unpacked as tuple)
Directory : (string, int, FileSystemItem list) -> FileSystemItem
//   replace with 'r ===> ~~~~~~~~~~~~~~          ~~~~~~~~~~~~~~

// function parameter to handle Directory case 
fDir :      (string, int, 'r list)             -> 'r 
```

另一个问题是与 Directory 情况相关联的数据是 `FileSystemItem` 的 *列表*。我们怎样才能将其转换为 `'r` 的列表？

嗯，`recurse`助手将`FileSystemItem`转换为`'r`，所以我们可以简单地使用`List.map`，将`recurse`作为映射函数传入，这将给我们提供所需的`'r`列表！

将所有内容组合起来，我们得到了这个实现：

```
let rec cataFS fFile fDir item :'r = 
    let recurse = cataFS fFile fDir 
    match item with
    | File file -> 
        fFile file
    | Directory dir -> 
        let listOfRs = dir.subitems |> List.map recurse 
        fDir (dir.name,dir.dirSize,listOfRs) 
```

如果我们看一下类型签名，我们会发现它正是我们想要的：

```
val cataFS :
    fFile : (File -> 'r) ->
    fDir  : (string * int * 'r list -> 'r) -> 
    // input value
    FileSystemItem -> 
    // return value
    'r 
```

所以我们完成了。设置起来有点复杂，但一旦建立起来，我们就有了一个不错的可重复使用的函数，可以成为许多其他函数的基础。

### 文件系统域：`totalSize`示例

好的，那么让我们实际使用它。

起初，我们可以轻松地定义一个`totalSize`函数，它返回项目及其所有子项目的总大小：

```
let totalSize fileSystemItem =
    let fFile (file:File) = 
        file.fileSize
    let fDir (name,size,subsizes) = 
        (List.sum subsizes) + size
    cataFS fFile fDir fileSystemItem 
```

这就是结果：

```
readme |> totalSize  // 1
src |> totalSize     // 16 = 10 + (1 + 2 + 3)
root |> totalSize    // 31 = 5 + 16 + 10 
```

### 文件系统域：`largestFile`示例

如何处理更复杂的函数，比如“树中最大的文件是什么”？

在我们开始之前，让我们想一想它应该返回什么。也就是说，什么是`'r`？

你可能会认为它只是一个`File`。但是如果子目录为空，而且没有文件呢？

所以我们将`'r`改为`File option`。

`File`情况的函数应该返回`Some file`：

```
let fFile (file:File) = 
    Some file 
```

`Directory`情况的函数需要更多的思考：

+   如果子文件列表为空，则返回`None`。

+   如果子文件列表非空，则返回最大的子文件。

```
let fDir (name,size,subfiles) = 
    match subfiles with
    | [] -> 
        None  // empty directory
    | subfiles -> 
        // return largest one 
```

但是请记住，`'r`不是`File`而是`File option`。这意味着`subfiles`不是文件列表，而是`File option`的列表。

现在，我们怎样才能找到这些中最大的一个呢？我们可能想要使用`List.maxBy`并传入大小。但是`File option`的大小是多少？

让我们编写一个辅助函数，提供`File option`的大小，使用以下逻辑：

+   如果`File option`为`None`，则返回 0

+   否则返回选项内文件的大小

这是代码：

```
// helper to provide a default if missing
let ifNone deflt opt =
    defaultArg opt deflt 

// get the file size of an option 
let fileSize fileOpt = 
    fileOpt 
    |> Option.map (fun file -> file.fileSize)
    |> ifNone 0 
```

将所有内容放在一起，我们有了我们的`largestFile`函数：

```
let largestFile fileSystemItem =

    // helper to provide a default if missing
    let ifNone deflt opt =
        defaultArg opt deflt 

    // helper to get the size of a File option
    let fileSize fileOpt = 
        fileOpt 
        |> Option.map (fun file -> file.fileSize)
        |> ifNone 0

    // handle File case 
    let fFile (file:File) = 
        Some file

    // handle Directory case 
    let fDir (name,size,subfiles) = 
        match subfiles with
        | [] -> 
            None  // empty directory
        | subfiles -> 
            // find the biggest File option using the helper
            subfiles 
            |> List.maxBy fileSize  

    // call the catamorphism
    cataFS fFile fDir fileSystemItem 
```

如果我们测试它，我们会得到我们预期的结果：

```
readme |> largestFile  
// Some {name = "readme.txt"; fileSize = 1}

src |> largestFile     
// Some {name = "build.bat"; fileSize = 3}

bin |> largestFile     
// None

root |> largestFile    
// Some {name = "build.bat"; fileSize = 3} 
```

再次，设置起来有点棘手，但不比完全不使用范畴形式写起来更复杂。

* * *

## 范畴形式示例：Product 域

让我们来处理一个稍微复杂的领域。这一次，想象一下我们制造和销售某种产品：

+   有些产品是购买的，有时会有可选供应商。

+   有些产品是在我们的场地上制造的，由子组件构建，其中子组件是另一种产品的某个数量。

这里是以类型建模的域：

```
type Product =
    | Bought of BoughtProduct 
    | Made of MadeProduct 
and BoughtProduct = {
    name : string 
    weight : int 
    vendor : string option }
and MadeProduct = {
    name : string 
    weight : int 
    components:Component list }
and Component = {
    qty : int
    product : Product } 
```

请注意，这些类型是相互递归的。`Product`引用`MadeProduct`，后者引用`Component`，后者又引用`Product`。

这里是一些示例产品：

```
let label = 
    Bought {name="label"; weight=1; vendor=Some "ACME"}
let bottle = 
    Bought {name="bottle"; weight=2; vendor=Some "ACME"}
let formulation = 
    Bought {name="formulation"; weight=3; vendor=None}

let shampoo = 
    Made {name="shampoo"; weight=10; components=
    [
    {qty=1; product=formulation}
    {qty=1; product=bottle}
    {qty=2; product=label}
    ]}

let twoPack = 
    Made {name="twoPack"; weight=5; components=
    [
    {qty=2; product=shampoo}
    ]} 
```

现在要设计这个范畴形式，我们需要做的就是在所有构造函数中将`Product`类型替换为`'r`。

与前面的示例一样，`Bought`情况很容易：

```
// case constructor
Bought  : BoughtProduct -> Product

// function parameter to handle Bought case 
fBought : BoughtProduct -> 'r 
```

`Made`情况更加棘手。我们需要将`MadeProduct`扩展为一个元组。但是该元组包含一个`Component`，所以我们也需要扩展它。最后我们到达内部的`Product`，然后可以机械地将其替换为`'r`。

这里是转换的顺序：

```
// case constructor
Made  : MadeProduct -> Product

// case constructor (MadeProduct unpacked as tuple)
Made  : (string,int,Component list) -> Product

// case constructor (Component unpacked as tuple)
Made  : (string,int,(int,Product) list) -> Product
//  replace with 'r ===> ~~~~~~~           ~~~~~~~

// function parameter to handle Made case 
fMade : (string,int,(int,'r) list)      -> 'r 
```

在实现`cataProduct`函数时，我们需要与之前相同类型的映射，将`Component`的列表转换为`(int,'r)`的列表。

我们需要一个辅助函数：

```
// Converts a Component into a (int * 'r) tuple
let convertComponentToTuple comp =
    (comp.qty,recurse comp.product) 
```

你可以看到这里使用`recurse`函数将内部产品（`comp.product`）转换为`'r`，然后制作一个元组`int * 'r`。

有了`convertComponentToTuple`可用，我们可以使用`List.map`将所有组件转换为元组：

```
let componentTuples = 
    made.components 
    |> List.map convertComponentToTuple 
```

`componentTuples`是一个`(int * 'r)`的列表，这正是我们需要的`fMade`函数。

`cataProduct`的完整实现如下：

```
let rec cataProduct fBought fMade product :'r = 
    let recurse = cataProduct fBought fMade 

    // Converts a Component into a (int * 'r) tuple
    let convertComponentToTuple comp =
        (comp.qty,recurse comp.product)

    match product with
    | Bought bought -> 
        fBought bought 
    | Made made -> 
        let componentTuples =  // (int * 'r) list
            made.components 
            |> List.map convertComponentToTuple 
        fMade (made.name,made.weight,componentTuples) 
```

### 产品领域：`productWeight`示例

现在我们可以使用`cataProduct`来计算权重，比如说。

```
let productWeight product =

    // handle Bought case
    let fBought (bought:BoughtProduct) = 
        bought.weight

    // handle Made case
    let fMade (name,weight,componentTuples) = 
        // helper to calculate weight of one component tuple
        let componentWeight (qty,weight) =
            qty * weight
        // add up the weights of all component tuples
        let totalComponentWeight = 
            componentTuples 
            |> List.sumBy componentWeight 
        // and add the weight of the Made case too
        totalComponentWeight + weight

    // call the catamorphism
    cataProduct fBought fMade product 
```

让我们进行交互式测试以确保它能正常工作：

```
label |> productWeight    // 1
shampoo |> productWeight  // 17 = 10 + (2x1 + 1x2 + 1x3)
twoPack |> productWeight  // 39 = 5  + (2x17) 
```

这正如我们所期望的。

尝试从头开始实现`productWeight`，而不使用像`cataProduct`这样的辅助函数。再次强调，这是可行的，但你可能会浪费相当多的时间来理清递归逻辑。

### 产品领域：`mostUsedVendor`示例

现在让我们做一个更复杂的函数。谁是最常用的供应商？

逻辑很简单：每当一个产品引用一个供应商，我们就给该供应商一个点，得分最高的供应商获胜。

再次，让我们考虑它应该返回什么。也就是说，`'r`是什么？

你可能认为这只是某种得分，但我们还需要知道供应商的名称。好的，那就是一个元组。但如果没有供应商呢？

因此让我们将`'r`设为`VendorScore option`，我们将创建一个小类型`VendorScore`，而不���使用元组。

```
type VendorScore = {vendor:string; score:int} 
```

我们还将定义一些辅助函数，以便轻松从`VendorScore`中获取数据：

```
let vendor vs = vs.vendor
let score vs = vs.score 
```

现在，在获得整个树的结果之前，你无法确定最常用的供应商，因此`Bought`情况和`Made`情况都需要返回一个列表，当我们递归遍历树时可以添加到其中。然后，在获取*所有*分数之后，我们将按降序排序以找到得分最高的供应商。

因此我们必须将`'r`变为`VendorScore list`，而不仅仅是一个选项！

`Bought`情况的逻辑是：

+   如果供应商存在，则返回一个得分为 1 的`VendorScore`，但作为一个元素列表而不是单个项目。

+   如果供应商缺失，则返回一个空列表。

```
let fBought (bought:BoughtProduct) = 
    // set score = 1 if there is a vendor
    bought.vendor
    |> Option.map (fun vendor -> {vendor = vendor; score = 1} )
    // => a VendorScore option
    |> Option.toList
    // => a VendorScore list 
```

`Made`情况的函数更复杂。

+   如果子分数列表为空，则返回一个空列表。

+   如果子分数列表非空，则按供应商对它们求和，然后返回新列表。

但传递给`fMade`函数的子结果列表将不是子分数列表，而是一个元组列表，`qty * 'r`其中`'r`是`VendorScore list`。复杂！

那么我们需要做的是：

+   将`qty * 'r`转换为`'r`，因为在这种情况下我们不关心数量。现在我们有一个`VendorScore list`的列表。我们可以使用`List.map snd`来做这个。

+   但现在我们将得到一个 `VendorScore list` 列表。我们可以使用 `List.collect` 将列表的列表展平为一个简单的列表。事实上，使用 `List.collect snd` 可以一次完成两个步骤。

+   将这个列表按供应商分组，这样我们就得到了一个 `key=vendor; values=VendorScore list` 元组的列表。

+   对每个供应商的分数进行求和（`values=VendorScore list`），得到一个单一的值，这样我们就有了一个 `key=vendor; values=VendorScore` 元组的列表。

此时，`cata` 函数将返回一个 `VendorScore list`。要获取最高分，请使用 `List.sortByDescending` 然后 `List.tryHead`。请注意，`maxBy` 不会起作用，因为列表可能为空。

下面是完整的 `mostUsedVendor` 函数：

```
let mostUsedVendor product =

    let fBought (bought:BoughtProduct) = 
        // set score = 1 if there is a vendor
        bought.vendor
        |> Option.map (fun vendor -> {vendor = vendor; score = 1} )
        // => a VendorScore option
        |> Option.toList
        // => a VendorScore list

    let fMade (name,weight,subresults) = 
        // subresults are a list of (qty * VendorScore list)

        // helper to get sum of scores
        let totalScore (vendor,vendorScores) =
            let totalScore = vendorScores |> List.sumBy score
            {vendor=vendor; score=totalScore}

        subresults 
        // => a list of (qty * VendorScore list)
        |> List.collect snd  // ignore qty part of subresult
        // => a list of VendorScore 
        |> List.groupBy vendor 
        // second item is list of VendorScore, reduce to sum
        |> List.map totalScore 
        // => list of VendorScores 

    // call the catamorphism
    cataProduct fBought fMade product
    |> List.sortByDescending score  // find highest score
    // return first, or None if list is empty
    |> List.tryHead 
```

现在让我们来测试一下：

```
label |> mostUsedVendor    
// Some {vendor = "ACME"; score = 1}

formulation |> mostUsedVendor  
// None

shampoo |> mostUsedVendor  
// Some {vendor = "ACME"; score = 2}

twoPack |> mostUsedVendor  
// Some {vendor = "ACME"; score = 2} 
```

当然，这并不是 `fMade` 的唯一可能实现。我本可以使用 `List.fold`，一次完成所有操作，但这个版本似乎是最明显和可读性最强的实现。

事实上，我完全可以避免使用 `cataProduct`，从头开始编写 `mostUsedVendor`。如果性能是一个问题，那么这可能是一个更好的方法，因为通用的折叠函数会创建中间值（比如 `qty * VendorScore option` 的列表），这些值过于一般化，可能是浪费的。

另一方面，通过使用对折叠函数，我可以只专注于计数逻辑，而忽略递归逻辑。

因此，您应该始终权衡重用和从头开始创建之间的利弊；编写通用代码一次并以标准化的方式使用它的好处，与自定义代码的性能但额外的努力（和潜在的错误）之间的权衡。

* * *

## 总结

在本篇中，我们看到了如何定义递归类型，并介绍了对折叠函数。

我们还看到了一些对折叠函数的用法：

+   任何“折叠”递归类型的函数，比如 `Gift -> 'r`，都可以根据该类型的对折叠函数来编写。

+   对折叠函数可用于隐藏类型的内部结构。

+   通过调整处理每种情况的函数，可以使用对折叠函数将一个类型映射到另一个类型。

+   对折叠函数可用于通过传递类型的 case 构造函数来创建原始值的克隆。

但是，在对折叠函数的国度中并非一切完美。实际上，本页面上所有的对折叠函数的实现都存在一个潜在的严重缺陷。

在下一篇文章中，我们将看到它们可能出现的问题，如何修复它们，并在此过程中查看各种类型的“折叠”。

到时见！

*本文的源代码可以在[此代码片段](https://gist.github.com/swlaschin/dc2b3fcdca319ca8be60)中找到。*

*更新：根据保罗·施纳普在评论中指出的逻辑错误，修复了 `mostUsedVendor`。谢谢，保罗！*

# 引入折叠

# 引入折叠

本文是系列文章的第三篇。

在第一篇文章中，我介绍了“catamorphisms”，一种为递归类型创建函数的方法，在第二篇文章中，我们创建了一些 catamorphism 的实现。

但在上一篇文章的结尾，我指出到目前为止，所有的 catamorphism 实现都存在一个潜在的严重缺陷。

在本篇文章中，我们将看到这个缺陷以及如何解决它，并在此过程中看到折叠、尾递归以及“左折叠”和“右折叠”之间的区别。

## 系列内容

本系列的内容如下：

+   **第 1 部分：递归类型和 catamorphisms 介绍**

    +   一个简单的递归类型

    +   参数化所有内容

    +   介绍 catamorphisms

    +   catamorphisms 的好处

    +   创建 catamorphism 的规则

+   **第 2 部分：Catamorphism 示例**

    +   Catamorphism 示例：文件系统领域

    +   Catamorphism 示例：产品领域

+   **第 3 部分：折叠介绍**

    +   我们 catamorphism 实现中的一个缺陷

    +   介绍 `fold`

    +   折叠的问题

    +   将函数用作累加器

    +   介绍 `foldback`

    +   创建折叠的规则

+   **第 4 部分：理解折叠**

    +   迭代 vs. 递归

    +   折叠示例：文件系统领域

    +   关于“折叠”的常见问题

+   **第 5 部分：通用递归类型**

    +   LinkedList：通用的递归类型

    +   使 Gift 领域通用化

    +   定义通用的容器类型

    +   实现 Gift 领域的第三种方式

    +   抽象还是具体？比较三种设计

+   **第 6 部分：现实世界中的树**

    +   定义通用的树类型

    +   现实世界中的树类型

    +   映射树类型

    +   示例：创建目录列表

    +   示例：并行 grep

    +   示例：将文件系统存储在数据库中

    +   示例：将树序列化为 JSON

    +   示例：从 JSON 反序列化树

    +   示例：从 JSON 反序列化树 - 带错误处理

* * *

## 我们的折叠实现中的一个缺陷

在我们看缺陷之前，让我们首先回顾一下递归类型`Gift`和我们为其创建的相关折叠`cataGift`。

这是领域：

```
type Book = {title: string; price: decimal}

type ChocolateType = Dark | Milk | SeventyPercent
type Chocolate = {chocType: ChocolateType ; price: decimal}

type WrappingPaperStyle = 
    | HappyBirthday
    | HappyHolidays
    | SolidColor

type Gift =
    | Book of Book
    | Chocolate of Chocolate 
    | Wrapped of Gift * WrappingPaperStyle
    | Boxed of Gift 
    | WithACard of Gift * message:string 
```

这里是本文中将要使用的一些示例值：

```
// A Book
let wolfHall = {title="Wolf Hall"; price=20m}
// A Chocolate
let yummyChoc = {chocType=SeventyPercent; price=5m}
// A Gift
let birthdayPresent = WithACard (Wrapped (Book wolfHall, HappyBirthday), "Happy Birthday")
// A Gift
let christmasPresent = Wrapped (Boxed (Chocolate yummyChoc), HappyHolidays) 
```

这是折叠：

```
let rec cataGift fBook fChocolate fWrapped fBox fCard gift :'r =
    let recurse = cataGift fBook fChocolate fWrapped fBox fCard
    match gift with 
    | Book book -> 
        fBook book
    | Chocolate choc -> 
        fChocolate choc
    | Wrapped (gift,style) -> 
        fWrapped (recurse gift,style)
    | Boxed gift -> 
        fBox (recurse gift)
    | WithACard (gift,message) -> 
        fCard (recurse gift,message) 
```

这里是使用`cataGift`构建的`totalCostUsingCata`函数：

```
let totalCostUsingCata gift =
    let fBook (book:Book) = 
        book.price
    let fChocolate (choc:Chocolate) = 
        choc.price
    let fWrapped  (innerCost,style) = 
        innerCost + 0.5m
    let fBox innerCost = 
        innerCost + 1.0m
    let fCard (innerCost,message) = 
        innerCost + 2.0m
    // call the catamorphism
    cataGift fBook fChocolate fWrapped fBox fCard gift 
```

### 有什么缺陷？

那么这个实现有什么问题呢？让我们对其进行压力测试并找出！

我们将创建一个非常多次嵌套的`Box`内部的`Box`内部的`Box`，看看会发生什么。

这是一个创建嵌套框的小助手函数：

```
let deeplyNestedBox depth =
    let rec loop depth boxSoFar =
        match depth with
        | 0 -> boxSoFar 
        | n -> loop (n-1) (Boxed boxSoFar)
    loop depth (Book wolfHall) 
```

让我们尝试一下，确保它能正常工作：

```
deeplyNestedBox 5
// Boxed (Boxed (Boxed (Boxed (Boxed (Book {title = "Wolf Hall"; price = 20M})))))

deeplyNestedBox 10
//  Boxed(Boxed(Boxed(Boxed(Boxed
//   (Boxed(Boxed(Boxed(Boxed(Boxed(Book {title = "Wolf Hall";price = 20M})))))))))) 
```

现在尝试使用这些深度嵌套的盒子运行`totalCostUsingCata`：

```
deeplyNestedBox 10 |> totalCostUsingCata       // OK     30.0M
deeplyNestedBox 100 |> totalCostUsingCata      // OK    120.0M
deeplyNestedBox 1000 |> totalCostUsingCata     // OK   1020.0M 
```

到目前为止一切顺利。

但是如果我们使用更大的数字，很快就会遇到堆栈溢出异常：

```
deeplyNestedBox 10000 |> totalCostUsingCata  // Stack overflow?
deeplyNestedBox 100000 |> totalCostUsingCata // Stack overflow? 
```

导致错误的确切数字取决于环境、可用内存等。但可以肯定的是，当你开始使用较大的数字时，你会遇到这个问题。

为什么会发生这种情况？

### 深度递归的问题

回想一下，`fBox`（Boxed 案例的成本定义）的定义是`innerCost + 1.0m`。内部成本是什么？那也是另一个盒子，所以我们最终得到一个看起来像这样的计算链：

```
innerCost + 1.0m where innerCost = 
  innerCost2 + 1.0m where innerCost2 = 
    innerCost3 + 1.0m where innerCost3 = 
      innerCost4 + 1.0m where innerCost4 = 
        ...
        innerCost999 + 1.0m where innerCost999 = 
          innerCost1000 + 1.0m where innerCost1000 = 
            book.price 
```

换句话说，`innerCost1000`必须在`innerCost999`之前计算，而在顶层`innerCost`可以计算之前，还必须计算其他 999 个内部成本。

每个级别都在等待其内部成本计算完成，然后再进行该级别的计算。

所有这些未完成的计算都堆积在一起，等待内部计算完成。当你有太多时？崩溃！堆栈溢出！

### 堆栈溢出的解决方案

解决这个问题很简单。每个级别不再等待内部成本计算完成，而是使用累加器计算到目前为止的成本，并将其传递给下一个内部级别。当我们到达底层时，我们就有了最终答案。

```
costSoFar = 1.0m; evaluate calcInnerCost with costSoFar: 
  costSoFar = costSoFar + 1.0m; evaluate calcInnerCost with costSoFar: 
    costSoFar = costSoFar + 1.0m; evaluate calcInnerCost with costSoFar: 
      costSoFar = costSoFar + 1.0m; evaluate calcInnerCost with costSoFar: 
        ...
        costSoFar = costSoFar + 1.0m; evaluate calcInnerCost with costSoFar: 
          costSoFar = costSoFar + 1.0m; evaluate calcInnerCost with costSoFar: 
            finalCost = costSoFar + book.price   // final answer 
```

这种方法的主要优点是，在特定级别的所有计算在下一个低级别被调用之前*完全完成*。这意味着该级别及其相关数据可以安全地从堆栈中丢弃。这意味着没有堆栈溢出！

这样的实现，其中较高级别可以安全丢弃，被称为*尾递归*。

### 使用累加器重新实现`totalCost`函数

让我们从头开始重新编写总成本函数，使用一个名为`costSoFar`的累加器：

```
let rec totalCostUsingAcc costSoFar gift =
    match gift with 
    | Book book -> 
        costSoFar + book.price  // final result
    | Chocolate choc -> 
        costSoFar + choc.price  // final result
    | Wrapped (innerGift,style) -> 
        let newCostSoFar = costSoFar + 0.5m
        totalCostUsingAcc newCostSoFar innerGift 
    | Boxed innerGift -> 
        let newCostSoFar = costSoFar + 1.0m
        totalCostUsingAcc newCostSoFar innerGift 
    | WithACard (innerGift,message) -> 
        let newCostSoFar = costSoFar + 2.0m
        totalCostUsingAcc newCostSoFar innerGift 
```

有几点需要注意：

+   函数的新版本有一个额外的参数（`costSoFar`）。当我们在顶层调用它时，我们将不得不为此提供一个初始值（比如零）。

+   非递归情况（`Book`和`Chocolate`）是终点。它们获取到目前为止的成本并将其加到它们的价格中，然后这就是最终结果。

+   递归情况根据传入的参数计算一个新的`costSoFar`。然后将新的`costSoFar`传递给下一个更低的级别，就像上面的例子一样。

让我们对这个版本进行压力测试：

```
deeplyNestedBox 1000 |> totalCostUsingAcc 0.0m     // OK    1020.0M
deeplyNestedBox 10000 |> totalCostUsingAcc 0.0m    // OK   10020.0M
deeplyNestedBox 100000 |> totalCostUsingAcc 0.0m   // OK  100020.0M
deeplyNestedBox 1000000 |> totalCostUsingAcc 0.0m  // OK 1000020.0M 
```

太棒了。最多可以嵌套一百万层而不出现任何问题。

## 引入“fold”

现在让我们将相同的设计原则应用于范畴实现。

我们将创建一个新函数`foldGift`。我们将引入一个累加器`acc`，我们将通过每个级别传递它，并且非递归情况将返回最终累加器。

```
let rec foldGift fBook fChocolate fWrapped fBox fCard acc gift :'r =
    let recurse = foldGift fBook fChocolate fWrapped fBox fCard 
    match gift with 
    | Book book -> 
        let finalAcc = fBook acc book
        finalAcc     // final result
    | Chocolate choc -> 
        let finalAcc = fChocolate acc choc
        finalAcc     // final result
    | Wrapped (innerGift,style) -> 
        let newAcc = fWrapped acc style
        recurse newAcc innerGift 
    | Boxed innerGift -> 
        let newAcc = fBox acc 
        recurse newAcc innerGift 
    | WithACard (innerGift,message) -> 
        let newAcc = fCard acc message 
        recurse newAcc innerGift 
```

如果我们看一下类型签名，我们会发现它略有不同。现在到处都使用累加器`'a`的类型。唯一使用最终返回类型的时��是在两个非递归情况（`fBook`和`fChocolate`）中。

```
val foldGift :
  fBook:('a -> Book -> 'r) ->
  fChocolate:('a -> Chocolate -> 'r) ->
  fWrapped:('a -> WrappingPaperStyle -> 'a) ->
  fBox:('a -> 'a) ->
  fCard:('a -> string -> 'a) -> 
  // accumulator
  acc:'a -> 
  // input value
  gift:Gift -> 
  // return value
  'r 
```

让我们更仔细地看一下这一点，并比较上一篇文章中原始范畴的签名与新`fold`函数的签名。

首先是非递归情况：

```
// original catamorphism
fBook:(Book -> 'r)
fChocolate:(Chocolate -> 'r)

// fold
fBook:('a -> Book -> 'r)
fChocolate:('a -> Chocolate -> 'r) 
```

正如你所看到的，使用“fold”，非递归情况需要一个额外的参数（累加器），并返回`'r`类型。

这是一个非常重要的观点：*累加器的类型不需要与返回类型相同*。我们很快将需要利用这一点。

递归情况呢？它们的签名如何改变？

```
// original catamorphism
fWrapped:('r -> WrappingPaperStyle -> 'r) 
fBox:('r -> 'r) 

// fold
fWrapped:('a -> WrappingPaperStyle -> 'a)
fBox:('a -> 'a) 
```

对于递归情况，结构是相同的，但所有对`'r`类型的使用都已替换为`'a`类型。递归情况根本不使用`'r`类型。

### 使用 fold 重新实现`totalCost`函数

再次，我们可以重新实现总成本函数，但这次使用`foldGift`函数：

```
let totalCostUsingFold gift =  

    let fBook costSoFar (book:Book) = 
        costSoFar + book.price
    let fChocolate costSoFar (choc:Chocolate) = 
        costSoFar + choc.price
    let fWrapped costSoFar style = 
        costSoFar + 0.5m
    let fBox costSoFar = 
        costSoFar + 1.0m
    let fCard costSoFar message = 
        costSoFar + 2.0m

    // initial accumulator
    let initialAcc = 0m

    // call the fold
    foldGift fBook fChocolate fWrapped fBox fCard initialAcc gift 
```

再次，我们可以处理非常大量的嵌套盒子而不会出现堆栈溢出：

```
deeplyNestedBox 100000 |> totalCostUsingFold  // no problem   100020.0M
deeplyNestedBox 1000000 |> totalCostUsingFold // no problem  1000020.0M 
```

## 使用 fold 的问题

所以使用 fold 解决了我们所有的问题，对吧？

不幸的是，不会。

是的，没有更多的堆栈溢出，但现在我们有另一个问题。

### 重新实现`description`函数

要看问题在哪里，让我们重新访问我们在第一篇文章中创建的`description`函数。

原始版本不是尾递归的，所以让我们更安全地使用`foldGift`重新实现它。

```
let descriptionUsingFold gift =
    let fBook descriptionSoFar (book:Book) = 
        sprintf "'%s' %s" book.title descriptionSoFar

    let fChocolate descriptionSoFar (choc:Chocolate) = 
        sprintf "%A chocolate %s" choc.chocType descriptionSoFar

    let fWrapped descriptionSoFar style = 
        sprintf "%s wrapped in %A paper" descriptionSoFar style

    let fBox descriptionSoFar = 
        sprintf "%s in a box" descriptionSoFar 

    let fCard descriptionSoFar message = 
        sprintf "%s with a card saying '%s'" descriptionSoFar message

    // initial accumulator
    let initialAcc = ""

    // main call
    foldGift fBook fChocolate fWrapped fBox fCard initialAcc gift 
```

让我们看看输出是什么：

```
birthdayPresent |> descriptionUsingFold  
// "'Wolf Hall'  with a card saying 'Happy Birthday' wrapped in HappyBirthday paper"

christmasPresent |> descriptionUsingFold  
// "SeventyPercent chocolate  wrapped in HappyHolidays paper in a box" 
```

这些输出是错误的！装饰的顺序被搞乱了。

它应该是一个包裹着卡片的书，而不是一本书和一张卡片一起包装。而且应该是盒子里的巧克力，然后包装，而不是包装着的巧克力在盒子里！

```
// OUTPUT: "'Wolf Hall'  with a card saying 'Happy Birthday' wrapped in HappyBirthday paper"
// CORRECT "'Wolf Hall' wrapped in HappyBirthday paper with a card saying 'Happy Birthday'"

// OUTPUT: "SeventyPercent chocolate  wrapped in HappyHolidays paper in a box"
// CORRECT "SeventyPercent chocolate in a box wrapped in HappyHolidays paper" 
```

发生了什么问题？

答案是，每一层的正确描述取决于下面一层的描述。我们不能“预先计算”一层的描述并将其传递给下一层，使用一个`descriptionSoFar`累加器。

但现在我们面临一个困境：一层依赖于下面一层的信息，但我们想避免堆栈溢出。

## 使用函数作为累加器

记住累加器类型不必与返回类型相同。我们可以使用任何东西作为累加器，甚至是一个函数！

所以我们将做的是，不再传递`descriptionSoFar`作为累加器，而是传递一个函数（比如说`descriptionGenerator`），它将根据下一层的值构建适当的描述。

这是非递归情况的实现：

```
let fBook descriptionGenerator (book:Book) = 
    descriptionGenerator (sprintf "'%s'" book.title)
//  ~~~~~~~~~~~~~~~~~~~~  <= a function as an accumulator!

let fChocolate descriptionGenerator (choc:Chocolate) = 
    descriptionGenerator (sprintf "%A chocolate" choc.chocType) 
```

递归情况的实现有点更复杂：

+   我们以一个累加器（`descriptionGenerator`）作为参数。

+   我们需要创建一个新的累加器（一个新的`descriptionGenerator`），传递给下一层。

+   描述生成器的*输入*将是从较低层累积的所有数据。我们操纵它以生成新的描述，然后调用从更高层传入的`descriptionGenerator`。

谈论起来比演示要复杂，所以这里有两个案例的实现：

```
let fWrapped descriptionGenerator style = 
    let newDescriptionGenerator innerText =
        let newInnerText = sprintf "%s wrapped in %A paper" innerText style
        descriptionGenerator newInnerText 
    newDescriptionGenerator 

let fBox descriptionGenerator = 
    let newDescriptionGenerator innerText =
        let newInnerText = sprintf "%s in a box" innerText 
        descriptionGenerator newInnerText 
    newDescriptionGenerator 
```

我们可以通过直接使用 lambda 稍微简化代码：

```
let fWrapped descriptionGenerator style = 
    fun innerText ->
        let newInnerText = sprintf "%s wrapped in %A paper" innerText style
        descriptionGenerator newInnerText 

let fBox descriptionGenerator = 
    fun innerText ->
        let newInnerText = sprintf "%s in a box" innerText 
        descriptionGenerator newInnerText 
```

我们可以继续使用管道和其他方法使其更加紧凑，但我认为我们现在有一个在简洁和晦涩之间保持良好平衡的东西。

这是整个函数：

```
let descriptionUsingFoldWithGenerator gift =

    let fBook descriptionGenerator (book:Book) = 
        descriptionGenerator (sprintf "'%s'" book.title)

    let fChocolate descriptionGenerator (choc:Chocolate) = 
        descriptionGenerator (sprintf "%A chocolate" choc.chocType)

    let fWrapped descriptionGenerator style = 
        fun innerText ->
            let newInnerText = sprintf "%s wrapped in %A paper" innerText style
            descriptionGenerator newInnerText 

    let fBox descriptionGenerator = 
        fun innerText ->
            let newInnerText = sprintf "%s in a box" innerText 
            descriptionGenerator newInnerText 

    let fCard descriptionGenerator message = 
        fun innerText ->
            let newInnerText = sprintf "%s with a card saying '%s'" innerText message 
            descriptionGenerator newInnerText 

    // initial DescriptionGenerator
    let initialAcc = fun innerText -> innerText 

    // main call
    foldGift fBook fChocolate fWrapped fBox fCard initialAcc gift 
```

再次，我使用过于描述性的中间值来清楚地说明正在发生的事情。

如果我们现在尝试`descriptionUsingFoldWithGenerator`，我们再次得到正确的答案：

```
birthdayPresent |> descriptionUsingFoldWithGenerator  
// CORRECT "'Wolf Hall' wrapped in HappyBirthday paper with a card saying 'Happy Birthday'"

christmasPresent |> descriptionUsingFoldWithGenerator  
// CORRECT "SeventyPercent chocolate in a box wrapped in HappyHolidays paper" 
```

## 介绍“折返”

现在我们明白了该做什么，让我们制作一个通用版本，处理生成函数逻辑。这个我们将称之为“折返”：

*顺便说一句，在这里我将使用术语“生成函数”。在其他地方，它通常被称为“续延”函数，常简称为“k”。*

这是实现：

```
let rec foldbackGift fBook fChocolate fWrapped fBox fCard generator gift :'r =
    let recurse = foldbackGift fBook fChocolate fWrapped fBox fCard 
    match gift with 
    | Book book -> 
        generator (fBook book)
    | Chocolate choc -> 
        generator (fChocolate choc)
    | Wrapped (innerGift,style) -> 
        let newGenerator innerVal =
            let newInnerVal = fWrapped innerVal style
            generator newInnerVal 
        recurse newGenerator innerGift 
    | Boxed innerGift -> 
        let newGenerator innerVal =
            let newInnerVal = fBox innerVal 
            generator newInnerVal 
        recurse newGenerator innerGift 
    | WithACard (innerGift,message) -> 
        let newGenerator innerVal =
            let newInnerVal = fCard innerVal message 
            generator newInnerVal 
        recurse newGenerator innerGift 
```

你可以看到它就像`descriptionUsingFoldWithGenerator`实现一样，只是我们现在使用泛型的`newInnerVal`和`generator`值。

类型签名与原始的范畴形式相似，只是现在每种情况都只使用`'a`。`'r`唯一使用的时间是在生成函数本身！

```
val foldbackGift :
  fBook:(Book -> 'a) ->
  fChocolate:(Chocolate -> 'a) ->
  fWrapped:('a -> WrappingPaperStyle -> 'a) ->
  fBox:('a -> 'a) ->
  fCard:('a -> string -> 'a) ->
  // accumulator
  generator:('a -> 'r) -> 
  // input value
  gift:Gift -> 
  // return value
  'r 
```

*上面的`foldback`实现是从头开始编写的。如果你想要一个有趣的练习，看看你是否能够根据`fold`来编写`foldback`。*

让我们使用`foldback`重新编写`description`函数：

```
let descriptionUsingFoldBack gift =
    let fBook (book:Book) = 
        sprintf "'%s'" book.title 
    let fChocolate (choc:Chocolate) = 
        sprintf "%A chocolate" choc.chocType
    let fWrapped innerText style = 
        sprintf "%s wrapped in %A paper" innerText style
    let fBox innerText = 
        sprintf "%s in a box" innerText 
    let fCard innerText message = 
        sprintf "%s with a card saying '%s'" innerText message 
    // initial DescriptionGenerator
    let initialAcc = fun innerText -> innerText 
    // main call
    foldbackGift fBook fChocolate fWrapped fBox fCard initialAcc gift 
```

结果仍然正确：

```
birthdayPresent |> descriptionUsingFoldBack
// CORRECT "'Wolf Hall' wrapped in HappyBirthday paper with a card saying 'Happy Birthday'"

christmasPresent |> descriptionUsingFoldBack
// CORRECT "SeventyPercent chocolate in a box wrapped in HappyHolidays paper" 
```

### 比较`foldback`和原始的范畴形式

使用`descriptionUsingFoldBack`的实现几乎与上一篇帖子中使用原始范畴形式`cataGift`的版本相同。

这是使用`cataGift`的版本：

```
let descriptionUsingCata gift =
    let fBook (book:Book) = 
        sprintf "'%s'" book.title 
    let fChocolate (choc:Chocolate) = 
        sprintf "%A chocolate" choc.chocType
    let fWrapped (innerText,style) = 
        sprintf "%s wrapped in %A paper" innerText style
    let fBox innerText = 
        sprintf "%s in a box" innerText
    let fCard (innerText,message) = 
        sprintf "%s with a card saying '%s'" innerText message
    // call the catamorphism
    cataGift fBook fChocolate fWrapped fBox fCard gift 
```

这是使用`foldbackGift`的版本：

```
let descriptionUsingFoldBack gift =
    let fBook (book:Book) = 
        sprintf "'%s'" book.title 
    let fChocolate (choc:Chocolate) = 
        sprintf "%A chocolate" choc.chocType
    let fWrapped innerText style = 
        sprintf "%s wrapped in %A paper" innerText style
    let fBox innerText = 
        sprintf "%s in a box" innerText 
    let fCard innerText message = 
        sprintf "%s with a card saying '%s'" innerText message 
    // initial DescriptionGenerator
    let initialAcc = fun innerText -> innerText    // could be replaced with id
    // main call
    foldbackGift fBook fChocolate fWrapped fBox fCard initialAcc gift 
```

所有处理程序函数基本上是相同的。唯一的变化是添加了一个初始生成函数，这在这种情况下只是`id`。

但是，尽管代码在两种情况下看起来相同，但它们在递归安全性上有所不同。`foldbackGift`版本仍然是尾递归的，并且可以处理非常大的嵌套深度，不像`cataGift`版本。

但是，这种实现也不完美。嵌套函数链可能会变得非常缓慢并且生成大量垃圾，对于这个特定的示例，有一种更快的方法，我们将在下一篇文章中介绍。

### 更改`foldback`的类型签名以避免混淆

在`foldGift`中，`fWrapped`的签名是：

```
fWrapped:('a -> WrappingPaperStyle -> 'a) 
```

但在`foldbackGift`中，`fWrapped`的签名是：

```
fWrapped:('a -> WrappingPaperStyle -> 'a) 
```

你能发现区别吗？不，我也不能。

这两个函数非常相似，但工作方式完全不同。在`foldGift`版本中，第一个参数是*外部*级别的累加器，而在`foldbackGift`版本中，第一个参数是*内部*级别的累加器。这是一个非常重要的区别！

因此，通常会更改`foldBack`版本的签名，以便累加器始终出现在*最后*，而在正常的`fold`函数中，累加器始终出现在*第一*。

```
let rec foldbackGift fBook fChocolate fWrapped fBox fCard gift generator :'r =
//swapped =>                                              ~~~~~~~~~~~~~~ 

    let recurse = foldbackGiftWithAccLast fBook fChocolate fWrapped fBox fCard 

    match gift with 
    | Book book -> 
        generator (fBook book)
    | Chocolate choc -> 
        generator (fChocolate choc)

    | Wrapped (innerGift,style) -> 
        let newGenerator innerVal =
            let newInnerVal = fWrapped style innerVal 
//swapped =>                           ~~~~~~~~~~~~~~ 
            generator newInnerVal 
        recurse innerGift newGenerator  
//swapped =>    ~~~~~~~~~~~~~~~~~~~~~~ 

    | Boxed innerGift -> 
        let newGenerator innerVal =
            let newInnerVal = fBox innerVal 
            generator newInnerVal 
        recurse innerGift newGenerator  
//swapped =>    ~~~~~~~~~~~~~~~~~~~~~~ 

    | WithACard (innerGift,message) -> 
        let newGenerator innerVal =
            let newInnerVal = fCard message innerVal 
//swapped =>                        ~~~~~~~~~~~~~~~~ 
            generator newInnerVal 
        recurse innerGift newGenerator 
//swapped =>    ~~~~~~~~~~~~~~~~~~~~~~ 
```

这个变化显示在类型签名中。现在，`Gift`值在累加器之前：

```
val foldbackGift :
  fBook:(Book -> 'a) ->
  fChocolate:(Chocolate -> 'a) ->
  fWrapped:(WrappingPaperStyle -> 'a -> 'a) ->
  fBox:('a -> 'a) ->
  fCard:(string -> 'a -> 'a) ->
  // input value
  gift:Gift -> 
  // accumulator
  generator:('a -> 'r) -> 
  // return value
  'r 
```

现在我们可以轻松地区分这两个版本了。

```
// fold
fWrapped:('a -> WrappingPaperStyle -> 'a) 

// foldback
fWrapped:(WrappingPaperStyle -> 'a -> 'a) 
```

## 创建折叠的规则

结束这篇文章时，让我们总结一下创建折叠的规则。

在第一篇文章中，我们看到创建一个析取范畴是一个遵循规则的机械过程。创建迭代式自顶向下折叠也是如此。该过程如下：

+   创建一个函数参数来处理结构中的每种情况。

+   添加一个额外的参数作为累加器。

+   对于非递归情况，将函数参数传递给累加器以及与该情况相关的所有数据。

+   对于递归情况，执行两个步骤：

    +   首先，将处理程序传递给累加器以及与该情况相关的所有数据（除了内部递归数据）。结果是一个新的累加器值。

    +   然后，使用新的累加器值对嵌套值递归调用折叠。

请注意，每个处理程序仅“看到”（a）该情况的数据和（b）从外部级别传递给它的累加器。它无法访问内部级别的结果。

* * *

## 摘要

在这篇文章中，我们看到了如何定义一个尾递归实现的析取范畴，称为“fold”和相反版本的“foldback”。

在下一篇文章中，我们将稍微退后一步，并花一些时间了解“折叠”真正意味着什么，并提供一些在`fold`、`foldback`和`cata`之间选择的指南。

我们将看看是否可以将这些规则应用于另一个领域。

*本文的源代码可在[此代码片段](https://gist.github.com/swlaschin/df4427d0043d7146e592)中找到。*

# 理解折叠

# 理解折叠

这篇文章是系列中的第四篇。

在上一篇文章中，我介绍了“折叠”，一种为递归类型创建自顶向下迭代函数的方法。

在这篇文章中，我们将花一些时间更详细地了解折叠。

## 系列目录

这个系列的内容如下：

+   **第 1 部分：递归类型和消解**

    +   一个简单的递归类型

    +   参数化一切

    +   介绍消解

    +   消解的好处

    +   创建消解的规则

+   **第 2 部分：消解示例**

    +   消解示例：文件系统领域

    +   消解示例：产品领域

+   **第 3 部分：介绍折叠**

    +   我们消解实现中的一个缺陷

    +   介绍 `fold`

    +   折叠的问题

    +   将函数用作累加器

    +   介绍 `foldback`

    +   创建折叠的规则

+   **第 4 部分：理解折叠**

    +   迭代 vs. 递归

    +   折叠示例：文件系统领域

    +   关于“折叠”的常见问题

+   **第 5 部分：通用递归类型**

    +   链表：一个通用递归类型

    +   使礼物领域通用化

    +   定义通用容器类型

    +   实现礼物领域的第三种方式

    +   抽象还是具体？比较三种设计

+   **第 6 部分：现实世界中的树**

    +   定义通用树类型

    +   现实世界中的树类型

    +   映射树类型

    +   示例：创建目录列表

    +   示例：并行 grep

    +   示例：将文件系统存储在数据库中

    +   示例：将树序列化为 JSON

    +   示例：从 JSON 反序列化树

    +   示例：从 JSON 反序列化树 - 带错误处理

* * *

## 迭代 vs. 递归

现在我们有了*三个*不同的函数 -- `cata`, `fold` 和 `foldback`。

那么它们之间的区别到底是什么？我们已经看到了一些在`fold`中不起作用但在`foldBack`中起作用的东西，但是否有一种容易记住区别的方法？

区分这三种方法的一种方法是记住这一点：

+   `fold`是自顶向下的*迭代*

+   `cata`是自底向上的*递归*

+   `foldBack`是自底向上的*迭代*

这是什么意思？

好吧，在`fold`中，累加器是在顶层初始化的，并且传递到每个较低级别，直到达到最低且最后一个级别。

在代码方面，每个级别都执行了这样的操作：

```
accumulatorFromHigherLevel, combined with 
  stuffFromThisLevel 
    => stuffToSendDownToNextLowerLevel 
```

在命令式语言中，这正是一个带有存储累加器的可变变量的“for 循环”。

```
var accumulator = initialValue
foreach level in levels do
{
  accumulator, combined with 
    stuffFromThisLevel 
      => update accumulator
} 
```

因此，这种自顶向下的折叠可以被视为迭代（实际上，F#编译器将像这样的尾递归函数转换为迭代）。

另一方面，在`cata`中，累加器从底部级别开始，并传递到每个较高级别，直到达到顶级。

在代码方面，每个级别都执行了这样的操作：

```
accumulatorFromLowerLevel, combined with 
  stuffFromThisLevel 
    => stuffToSendUpToNextHigherLevel 
```

这正是一个递归循环：

```
let recurse (head::tail) =
    if atBottomLevel then
       return something
    else    // if not at bottom level
       let accumulatorFromLowerLevel = recurse tail
       return stuffFromThisLevel, combined with 
          accumulatorFromLowerLevel 
```

最后，`foldback`可以被视为“反向迭代”。累加器在所有级别中都被穿过，但是从底部开始而不是从顶部开始。它具有`cata`的优点，即首先计算内部值并将其传递回来，但由于它是迭代的，所以不会发生堆栈溢出。

当以迭代与递归的方式表达时，我们讨论的许多概念变得清晰起来。例如：

+   迭代版本（`fold`和`foldback`）没有堆栈，不会导致堆栈溢出。

+   “总成本”函数不需要内部数据，所以自上而下的迭代版本（`fold`）可以顺利运行。

+   但是，“description”函数需要内部文本以正确格式化，因此递归版本（`cata`）或自底向上的迭代（`foldback`）更合适。

## 折叠示例：文件系统域

在上一篇文章中，我们描述了创建折叠的一些规则。让我们看看是否可以将这些规则应用于另一个领域的折叠，即来自系列第二篇文章的“文件系统”领域。

作为提醒，这是来自该文章的粗略“文件系统”域：

```
type FileSystemItem =
    | File of File
    | Directory of Directory
and File = {name:string; fileSize:int}
and Directory = {name:string; dirSize:int; subitems:FileSystemItem list} 
```

请注意，每个目录都包含一个*子项列表*，因此这不是像`Gift`那样的线性结构，而是一个类似树的结构。我们的折叠实现将必须考虑到这一点。

这里有一些样本值：

```
let readme = File {name="readme.txt"; fileSize=1}
let config = File {name="config.xml"; fileSize=2}
let build  = File {name="build.bat"; fileSize=3}
let src = Directory {name="src"; dirSize=10; subitems=[readme; config; build]}
let bin = Directory {name="bin"; dirSize=10; subitems=[]}
let root = Directory {name="root"; dirSize=5; subitems=[src; bin]} 
```

我们想要创建一个折叠，比如`foldFS`。因此，遵循规则，让我们添加一个额外的累加器参数`acc`，并将其传递给`File`情况：

```
let rec foldFS fFile fDir acc item :'r = 
    let recurse = foldFS fFile fDir 
    match item with
    | File file -> 
        fFile acc file
    | Directory dir -> 
        // to do 
```

`Directory`情况更棘手。我们不应该知道子项，这意味着我们只能使用`name`、`dirSize`和来自更高级别的累加器。这些被组合起来形成一个新的累加器。

```
| Directory dir -> 
    let newAcc = fDir acc (dir.name,dir.dirSize) 
    // to do 
```

*注意：我将`name`和`dirSize`保留为元组以进行分组，但当然你也可以将它们作为单独的参数传递。*

现在我们需要将这个新的累加器依次传递给每个子项，但是每个子项将返回自己的新累加器，所以我们需要使用以下方法：

+   将新创建的累加器传递给第一个子项。

+   将其输出（另一个累加器）传递给第二个子项。

+   将其输出（另一个累加器）传递给第三个子项。

+   依此类推。最后一个子项的输出是最终结果。

尽管这种方法已经可用于我们。这正是`List.fold`所做的！因此，这是 Directory 情况��代码： 

```
| Directory dir -> 
    let newAcc = fDir acc (dir.name,dir.dirSize) 
    dir.subitems |> List.fold recurse newAcc 
```

这里是整个`foldFS`函数：

```
let rec foldFS fFile fDir acc item :'r = 
    let recurse = foldFS fFile fDir 
    match item with
    | File file -> 
        fFile acc file
    | Directory dir -> 
        let newAcc = fDir acc (dir.name,dir.dirSize) 
        dir.subitems |> List.fold recurse newAcc 
```

有了这个，我们可以重写在上一篇文章中实现的相同的两个函数。

首先是`totalSize`函数，它只是将所有大小相加：

```
let totalSize fileSystemItem =
    let fFile acc (file:File) = 
        acc + file.fileSize
    let fDir acc (name,size) = 
        acc + size
    foldFS fFile fDir 0 fileSystemItem 
```

如果我们测试它，我们会得到与之前相同的结果：

```
readme |> totalSize  // 1
src |> totalSize     // 16 = 10 + (1 + 2 + 3)
root |> totalSize    // 31 = 5 + 16 + 10 
```

### 文件系统领域：`largestFile`示例

我们还可以重新实现“树中最大文件是什么？”函数。

与之前一样，它将返回一个`File option`，因为树可能为空。这意味着累加器也将是一个`File option`。

这次是`File`情况处理程序有点棘手：

+   如果传入的累加器是`None`，那么当前文件就成为新的累加器。

+   如果传入的累加器是`Some file`，那么将该文件的大小与此文件进行比较。哪个更大就成为新的累加器。

这是代码：

```
let fFile (largestSoFarOpt:File option) (file:File) = 
    match largestSoFarOpt with
    | None -> 
        Some file                
    | Some largestSoFar -> 
        if largestSoFar.fileSize > file.fileSize then
            Some largestSoFar
        else
            Some file 
```

另一方面，`Directory`处理程序很简单--只需将“到目前为止最大”的累加器传递到下一级

```
let fDir largestSoFarOpt (name,size) = 
    largestSoFarOpt 
```

这是完整的实现：

```
let largestFile fileSystemItem =
    let fFile (largestSoFarOpt:File option) (file:File) = 
        match largestSoFarOpt with
        | None -> 
            Some file                
        | Some largestSoFar -> 
            if largestSoFar.fileSize > file.fileSize then
                Some largestSoFar
            else
                Some file

    let fDir largestSoFarOpt (name,size) = 
        largestSoFarOpt

    // call the fold
    foldFS fFile fDir None fileSystemItem 
```

如果我们测试它，我们会得到与之前相同的结果：

```
readme |> largestFile  
// Some {name = "readme.txt"; fileSize = 1}

src |> largestFile     
// Some {name = "build.bat"; fileSize = 3}

bin |> largestFile     
// None

root |> largestFile    
// Some {name = "build.bat"; fileSize = 3} 
```

将这种实现与第二篇文章中的递归版本进行比较。我认为这个实现更容易实现。

### 树遍历类型

到目前为止讨论的各种折叠函数对应于各种树遍历方式：

+   一个`fold`函数（在这里实现）更恰当地称为“前序深度优先”树遍历。

+   `foldback`函数将是“后序深度优先”树遍历。

+   `cata`函数根本不是“遍历”，因为每个内部节点一次处理所有子结果的列表。

通过调整逻辑，您可以制作其他变体。

有关各种树遍历的描述，请参见[Wikipedia](https://en.wikipedia.org/wiki/Tree_traversal)。

### 我们需要`foldback`吗？

我们需要为文件系统领域实现一个`foldback`函数吗？

我不这么认为。如果我们需要访问内部数据，我们可以使用上一篇文章中原始的“天真”范畴折叠实现。

但是，等等，我不是在开头说过我们必须注意堆栈溢出吗？

是的，如果递归类型是深度嵌套的。但是考虑一个每个目录只有两个子目录的文件系统。如果有 64 个嵌套级别，会有多少个目录？（提示：你可能熟悉一个类似的问题。与[国际象棋棋盘上的麦粒问题](https://en.wikipedia.org/wiki/Wheat_and_chessboard_problem)有关）。

我们之前看到，堆栈溢出问题只会发生在超过 1000 个嵌套级别时，而那种级别的嵌套通常只出现在*线性*递归类型中，而不是像 FileSystem 领域这样的树形结构。

## 关于“折叠”的常见问题

此时你可能会感到不知所措！所有这些不同的实现都有不同的优势和劣势。

所以让我们稍作休息，解答一些常见问题。

### "左折叠"和"右折叠"有什么区别呢？

在折叠术语的术语方面常常会有相当多的混淆：“左”vs。“右”，“前”vs。“后”，等等。

+   *左折叠*或*前向折叠*就是我刚刚称为`fold`的东西——自上而下的迭代方法。

+   *右折叠*或*向后折叠*就是我所说的`foldBack`——自下而上的迭代方法。

然而，这些术语实际上只适用于像`Gift`这样的线性递归结构。当涉及到更复杂的树状结构时，这些区别就太简单了，因为有许多遍历方法：广度优先、深度优先、前序和后序等等。

### 我应该使用哪种类型的折叠函数？

这里有一些指导方针：

+   如果你的递归类型不会太深嵌套（比如少于 100 层深），那么我们在第一篇文章中描述的简单`cata`范畴叠加就可以了。它真的很容易机械化实现——只需用`'r`替换主递归类型即可。

+   如果你的递归类型将会被深度嵌套，并且你想要避免堆栈溢出，那就使用迭代的`fold`。

+   如果你使用的是迭代折叠，但需要访问内部数据，请将一个继续函数作为累加器传递。

+   最后，迭代方法通常比递归方法更快，且使用的内存更少（但如果传递了太多嵌套的继续，这个优势就会丧失）。

另一种思考方式是看你的“组合器”函数。在每一步，你都在组合来自不同层级的数据：

```
level1 data [combined with] level2 data [combined with] level3 data [combined with] level4 data 
```

如果你的组合器函数是“左结合”的，就像这样：

```
(((level1 combineWith level2) combineWith level3) combineWith level4) 
```

然后使用迭代方法，但如果你的组合器函数是“右结合”的，就像这样：

```
(level1 combineWith (level2 combineWith (level3 combineWith level4))) 
```

然后使用`cata`或`foldback`方法。

如果你的组合器函数不在乎（比如加法，例如），那就使用更方便的那种。

### 我怎么知道代码是否是尾递归的？

是否一个实现是尾递归并不总是明显的。确保的最简单方法是查看每种情况的最后一个表达式。

如果对“recurse”的调用是最后一个表达式，那么它是尾递归的。如果在此之后还有其他工作，则不是尾递归。

通过我们讨论过的三种实现自己看看。

首先，这是原始`cataGift`实现中`WithACard`情��的代码：

```
| WithACard (gift,message) -> 
    fCard (recurse gift,message) 
//         ~~~~~~~  <= Call to recurse is not last expression.
//                     Tail-recursive? No! 
```

`cataGift`实现*不是*尾递归的。

这是`foldGift`实现的代码：

```
| WithACard (innerGift,message) -> 
    let newAcc = fCard acc message 
    recurse newAcc innerGift
//  ~~~~~~~  <= Call to recurse is last expression.
//              Tail-recursive? Yes! 
```

`foldGift`实现*是*尾递归的。

这是`foldbackGift`实现的代码：

```
| WithACard (innerGift,message) -> 
    let newGenerator innerVal =
        let newInnerVal = fCard innerVal message 
        generator newInnerVal 
    recurse newGenerator innerGift 
//  ~~~~~~~  <= Call to recurse is last expression.
//              Tail-recursive? Yes! 
```

`foldbackGift`实现也是尾递归的。

### 如何中断折叠？

在像 C#这样的语言中，您可以使用`break`提前退出迭代循环，就像这样：

```
foreach (var elem in collection)
{
    // do something

    if ( x == "error")
    {
        break;
    }
} 
```

那么如何使用折叠做同样的事情呢？

简短的回答是，你不能！折叠设计为依次访问所有元素。访问者模式也有相同的约束。

有三种解决方法。

第一个方法是根本不使用`fold`，而是创建自己的递归函数，在满足所需条件时终止：

在这个例子中，当总和大于 100 时，循环退出：

```
let rec firstSumBiggerThan100 sumSoFar listOfInts =
    match listOfInts with
    | [] -> 
        sumSoFar // exhausted all the ints!
    | head::tail -> 
        let newSumSoFar = head + sumSoFar 
        if newSumSoFar > 100 then
            newSumSoFar 
        else
            firstSumBiggerThan100 newSumSoFar tail

// test
[30;40;50;60] |> firstSumBiggerThan100 0  // 120
[1..3..100] |> firstSumBiggerThan100 0  // 117 
```

第二种方法是使用`fold`，但向累加器添加某种“忽略”标志，一旦设置了此标志，剩余的迭代将不起作用。

这是一个计算总和的示例，但累加器实际上是一个元组，其中除了`sumSoFar`之外还有一个`ignoreFlag`：

```
let firstSumBiggerThan100 listOfInts =

    let folder accumulator i =
        let (ignoreFlag,sumSoFar) = accumulator
        if not ignoreFlag then
            let newSumSoFar = i + sumSoFar 
            let newIgnoreFlag  = newSumSoFar > 100 
            (newIgnoreFlag, newSumSoFar)
        else
            // pass the accumulator along
            accumulator 

    let initialAcc = (false,0)

    listOfInts 
    |> List.fold folder initialAcc  // use fold
    |> snd // get the sumSoFar

/// test 
[30;40;50;60] |> firstSumBiggerThan100  // 120
[1..3..100] |> firstSumBiggerThan100  // 117 
```

第三个版本是第二个的变体--创建一个特殊值来表示应忽略剩余数据，但将其包装在计算表达式中，使其看起来更自然。

这种方法在[Tomas Petricek 的博客](http://tomasp.net/blog/imperative-ii-break.aspx/)上有文档记录，代码如下：

```
let firstSumBiggerThan100 listOfInts =
    let mutable sumSoFar = 0
    imperative { 
        for x in listOfInts do 
            sumSoFar <- x + sumSoFar 
            if sumSoFar > 100 then do! break
    }
    sumSoFar 
```

* * *

## 总结

本文的目标是帮助您更好地理解折叠，并展示如何将其应用于文件系统等树结构。希望对您有所帮助！

到目前为止，系列中的所有示例都非常具体；我们为遇到的每个领域实现了自定义折叠。我们能否更通用一些，构建一些可重用的折叠实现呢？

在下一篇文章中，我们将看看通用递归类型，以及如何处理它们。

*本文的源代码可在[this gist](https://gist.github.com/swlaschin/e065b0e99dd68cd35846)中找到。*

# 通用递归类型

# 通用递归类型

本文是系列中的第五篇。

在上一篇文章中，我们花了一些时间理解特定领域类型的折叠。

在本文中，我们将拓宽视野，看看如何使用通用递归类型。

## 系列内容

以下是本系列的内容：

+   **第 1 部分：递归类型和 catamorphisms 简介**

    +   一个简单的递归类型

    +   参数化所有事物

    +   引入分类折叠法

    +   分类折叠法的好处

    +   创建分类折叠法的规则

+   **第二部分：分类折叠法示例**

    +   分类折叠法示例：文件系统领域

    +   分类折叠法示例：产品领域

+   **第三部分：介绍折叠法**

    +   我们折叠法实现的一个缺陷

    +   引入 `fold`

    +   折叠法的问题

    +   将函数用作累加器

    +   引入 `foldback`

    +   创建折叠法的规则

+   **第四部分：理解折叠**

    +   迭代与递归的比较

    +   折叠法示例：文件系统领域

    +   关于 "fold" 的常见问题

+   **第五部分：通用递归类型**

    +   LinkedList：一个通用的递归类型

    +   使礼物领域通用化

    +   定义一个通用的 Container 类型

    +   另一个礼物领域的实现方式

    +   抽象还是具体？比较三种设计

+   **第六部分：现实世界中的树**

    +   定义一个通用的 Tree 类型

    +   现实世界中的 Tree 类型

    +   映射 Tree 类型

    +   示例：创建目录列表

    +   示例：并行 grep

    +   示例：将文件系统存储在数据库中

    +   示例：将树序列化为 JSON

    +   示例：从 JSON 反序列化树

    +   示例：从 JSON 反序列化树 - 带错误处理

* * *

## LinkedList：一个通用的递归类型

这里有一个问题：如果你只有代数类型，并且只能将它们作为积（元组、记录）或和（鉴别联合）来组合，那么你如何仅使用这些操作来制作一个列表类型？

当然，答案是递归！

让我们从最基本的递归类型开始：列表。

我将我的版本称为 `LinkedList`，但它基本上与 F# 中的 `list` 类型相同。

那么，如何以递归方式定义列表呢？

嗯，它要么是空的，要么包含一个元素加上另一个列表。换句话说，我们可以定义它为一个选择类型（“鉴别联合”），如下所示：

```
type LinkedList<'a> = 
    | Empty
    | Cons of head:'a * tail:LinkedList<'a> 
```

`Empty` 案例表示空列表。`Cons` 案例有一个元组：头元素和尾部，即另一个列表。

然后，我们可以这样定义一个特定的 `LinkedList` 值：

```
let linkedList = Cons (1, Cons (2, Cons(3, Empty))) 
```

使用原生的 F# list 类型，等效的定义将是：

```
let linkedList = 1 :: 2 :: 3 :: [] 
```

它就是 `[1; 2; 3]`

### `cata` 适用于 LinkedList

按照这个系列中第一篇文章中的规则，我们可以通过用 `fEmpty` 和 `fCons` 替换 `Empty` 和 `Cons` 来机械地创建一个 `cata` 函数：

```
module LinkedList = 

    let rec cata fCons fEmpty list :'r=
        let recurse = cata fCons fEmpty 
        match list with
        | Empty -> 
            fEmpty
        | Cons (element,list) -> 
            fCons element (recurse list) 
```

*注意：我们将把与 `LinkedList<'a>` 关联的所有函数放在一个名为 `LinkedList` 的模块中。使用泛型类型的一个好处是类型名称不会与类似的模块名称冲突！*

与类型构造函数的签名平行的是案例处理函数的签名，其中 `LinkedList` 被替换为 `'r`。

```
val cata : 
    fCons:('a -> 'r -> 'r) ->   
    fEmpty:'r ->                
    list:LinkedList<'a> 
    -> 'r 
```

### `fold` 适用于 LinkedList

我们还可以使用这个系列中早期文章中的规则创建一个自上而下的迭代 `fold` 函数。

```
module LinkedList = 

    let rec cata ...

    let rec foldWithEmpty fCons fEmpty acc list :'r=
        let recurse = foldWithEmpty fCons fEmpty 
        match list with
        | Empty -> 
            fEmpty acc 
        | Cons (element,list) -> 
            let newAcc = fCons acc element 
            recurse newAcc list 
```

这个 `foldWithEmpty` 函数与标准的 `List.fold` 函数不完全相同，因为它有一个额外的函数参数用于空情况（`fEmpty`）。但是，如果我们消除该参数并只返回累加器，我们会得到这个变体：

```
module LinkedList = 

    let rec fold fCons acc list :'r=
        let recurse = fold fCons 
        match list with
        | Empty -> 
            acc 
        | Cons (element,list) -> 
            let newAcc = fCons acc element 
            recurse newAcc list 
```

如果我们将签名与[List.fold 文档](https://msdn.microsoft.com/en-us/library/ee353894.aspx)进行比较，我们会发现它们是等效的，其中 `'State` 被替换为 `'r`，`'T list` 被替换为 `LinkedList<'a>`：

```
LinkedList.fold : ('r     -> 'a -> 'r    ) -> 'r      -> LinkedList<'a> -> 'r
List.fold       : ('State -> 'T -> 'State) -> 'State -> 'T list         -> 'State 
```

让我们通过做一个小的求和来测试 `fold` 是否有效：

```
let linkedList = Cons (1, Cons (2, Cons(3, Empty)))  
linkedList |> LinkedList.fold (+) 0
// Result => 6 
```

### `foldBack` 适用于 LinkedList

最后，我们可以创建一个 `foldBack` 函数，使用前一篇文章中描述的“函数累加器”方法：

```
module LinkedList = 

    let rec cata ...

    let rec fold ...

    let foldBack fCons list acc :'r=
        let fEmpty' generator = 
            generator acc 
        let fCons' generator element= 
            fun innerResult -> 
                let newResult = fCons element innerResult 
                generator newResult 
        let initialGenerator = id
        foldWithEmpty fCons' fEmpty' initialGenerator  list 
```

再次，如果我们将签名与[List.foldBack 文档](https://msdn.microsoft.com/en-us/library/ee353846.aspx)进行比较，它们也是等效的，其中 `'State` 被替换为 `'r`，`'T list` 被替换为 `LinkedList<'a>`：

```
LinkedList.foldBack : ('a -> 'r     -> 'r    ) -> LinkedList<'a> -> 'r     -> 'r
List.foldBack       : ('T -> 'State -> 'State) -> 'T list        -> 'State -> 'State 
```

### 使用 `foldBack` 在列表类型之间进行转换

在第一篇文章中，我们注意到，catamorphisms 可用于在类似结构的类型之间进行转换。

现在，让我们通过创建一些函数来演示，将 `LinkedList` 转换为原生的 `list` 类型，然后再转回来。

要将 `LinkedList` 转换为原生的 `list`，我们只需要用 `Cons` 替换 `::`，用 `Empty` 替换 `[]`：

```
module LinkedList = 

    let toList linkedList = 
        let fCons head tail = head::tail
        let initialState = [] 
        foldBack fCons linkedList initialState 
```

要进行另一种转换，我们需要用 `Cons` 替换 `::`，用 `Empty` 替换 `[]`：

```
module LinkedList = 

    let ofList list = 
        let fCons head tail = Cons(head,tail)
        let initialState = Empty
        List.foldBack fCons list initialState 
```

简单！让我们测试 `toList`：

```
let linkedList = Cons (1, Cons (2, Cons(3, Empty)))  
linkedList |> LinkedList.toList       
// Result => [1; 2; 3] 
```

和 `ofList`：

```
let list = [1;2;3]
list |> LinkedList.ofList       
// Result => Cons (1,Cons (2,Cons (3,Empty))) 
```

两者都按预期工作。

### 使用 `foldBack` 实现其他函数

我之前说过，一个 catamorphism 函数（对于线性列表，`foldBack`）是递归类型可用的最基本函数，实际上是*唯一*需要的函数！

让我们通过使用`foldBack`实现一些其他常见函数来亲自看看。

这里是以`foldBack`定义的`map`：

```
module LinkedList = 

    /// map a function "f" over all elements
    let map f list = 
        // helper function 
        let folder head tail =
            Cons(f head,tail)

        foldBack folder list Empty 
```

这里是一个测试：

```
let linkedList = Cons (1, Cons (2, Cons(3, Empty)))  

linkedList |> LinkedList.map (fun i -> i+10)
// Result => Cons (11,Cons (12,Cons (13,Empty))) 
```

这里是以`foldBack`定义的`filter`：

```
module LinkedList = 

    /// return a new list of elements for which "pred" is true
    let filter pred list = 
        // helper function
        let folder head tail =
            if pred head then 
                Cons(head,tail)
            else
                tail

        foldBack folder list Empty 
```

这里是一个测试：

```
let isOdd n = (n%2=1)
let linkedList = Cons (1, Cons (2, Cons(3, Empty)))  

linkedList |> LinkedList.filter isOdd
// Result => Cons (1,Cons (3,Empty)) 
```

最后，这里是以`fold`定义的`rev`：

```
/// reverse the elements of the list
let rev list = 
    // helper function
    let folder tail head =
        Cons(head,tail)

    fold folder Empty list 
```

这里是一个测试：

```
let linkedList = Cons (1, Cons (2, Cons(3, Empty)))  
linkedList |> LinkedList.rev
// Result => Cons (3,Cons (2,Cons (1,Empty))) 
```

所以，希望你被说服了！

### 避免生成器函数

我之前提到过，有一种替代方法（有时更有效）可以实现`foldBack`，而无需使用生成器或延续。

正如我们所见，`foldBack`是反向迭代，这意味着它与应用于反转列表的`fold`相同！

所以我们可以这样实现它：

```
let foldBack_ViaRev fCons list acc :'r=
    let fCons' acc element = 
        // just swap the params!
        fCons element acc 
    list
    |> rev
    |> fold fCons' acc 
```

它涉及制作列表的额外副本，但另一方面不再有大量待处理的延续。如果性能是一个问题，那么在您的环境中比较这两个版本的配置文件可能是值得的。

## 使礼物领域通用化

在本文的其余部分，我们将查看`Gift`类型，并看看是否可以使其更通用。

作为提醒，这是原始设计：

```
type Gift =
    | Book of Book
    | Chocolate of Chocolate 
    | Wrapped of Gift * WrappingPaperStyle
    | Boxed of Gift 
    | WithACard of Gift * message:string 
```

三种情况是递归的，两种是非递归的。

现在，这个特定设计的重点是对领域进行建模，这就是为什么有这么多单独的情况。

但如果我们想要专注于*可重用性*而不是领域建模，那么我们应该简化设计至基本要素，所有这些特殊情况现在成为了障碍。

为了使其准备好重用，让我们将所有非递归情况合并为一个情况，比如`GiftContents`，将所有递归情况合并为另一个情况，比如`GiftDecoration`，如下所示：

```
// unified data for non-recursive cases
type GiftContents = 
    | Book of Book
    | Chocolate of Chocolate 

// unified data for recursive cases
type GiftDecoration = 
    | Wrapped of WrappingPaperStyle
    | Boxed 
    | WithACard of string

type Gift =
    // non-recursive case
    | Contents of GiftContents
    // recursive case
    | Decoration of Gift * GiftDecoration 
```

主要的`Gift`类型现在只有两种情况：非递归和递归。

## 定义一个通用的容器类型

现在类型被简化了，我们可以通过允许*任何*类型的内容*和*任何类型的装饰来“泛型化”它。

```
type Container<'ContentData,'DecorationData> =
    | Contents of 'ContentData
    | Decoration of 'DecorationData * Container<'ContentData,'DecorationData> 
```

就像以前一样，我们可以使用标准流程为其创建`cata`和`fold`和`foldBack`，如下所示：

```
module Container = 

    let rec cata fContents fDecoration (container:Container<'ContentData,'DecorationData>) :'r = 
        let recurse = cata fContents fDecoration 
        match container with
        | Contents contentData -> 
            fContents contentData 
        | Decoration (decorationData,subContainer) -> 
            fDecoration decorationData (recurse subContainer)

    (*
    val cata :
        // function parameters
        fContents:('ContentData -> 'r) ->
        fDecoration:('DecorationData -> 'r -> 'r) ->
        // input
        container:Container<'ContentData,'DecorationData> -> 
        // return value
        'r
    *)

    let rec fold fContents fDecoration acc (container:Container<'ContentData,'DecorationData>) :'r = 
        let recurse = fold fContents fDecoration 
        match container with
        | Contents contentData -> 
            fContents acc contentData 
        | Decoration (decorationData,subContainer) -> 
            let newAcc = fDecoration acc decorationData
            recurse newAcc subContainer

    (*
    val fold :
        // function parameters
        fContents:('a -> 'ContentData -> 'r) ->
        fDecoration:('a -> 'DecorationData -> 'a) ->
        // accumulator
        acc:'a -> 
        // input
        container:Container<'ContentData,'DecorationData> -> 
        // return value
        'r
    *)

    let foldBack fContents fDecoration (container:Container<'ContentData,'DecorationData>) :'r = 
        let fContents' generator contentData =
            generator (fContents contentData)
        let fDecoration' generator decorationData =
            let newGenerator innerValue =
                let newInnerValue = fDecoration decorationData innerValue 
                generator newInnerValue 
            newGenerator 
        fold fContents' fDecoration' id container

    (*
    val foldBack :
        // function parameters
        fContents:('ContentData -> 'r) ->
        fDecoration:('DecorationData -> 'r -> 'r) ->
        // input
        container:Container<'ContentData,'DecorationData> -> 
        // return value
        'r
    *) 
```

### 将礼物领域转换为使用容器类型

让我们将礼物类型转换为这个通用的容器类型：

```
type Gift = Container<GiftContents,GiftDecoration> 
```

现在我们需要一些辅助方法来构造值，同时隐藏通用类型的“真实”情况：

```
let fromBook book = 
    Contents (Book book)

let fromChoc choc = 
    Contents (Chocolate choc)

let wrapInPaper paperStyle innerGift = 
    let container = Wrapped paperStyle 
    Decoration (container, innerGift)

let putInBox innerGift = 
    let container = Boxed
    Decoration (container, innerGift)

let withCard message innerGift = 
    let container = WithACard message
    Decoration (container, innerGift) 
```

最后，我们可以创建一些测试值：

```
let wolfHall = {title="Wolf Hall"; price=20m}
let yummyChoc = {chocType=SeventyPercent; price=5m}

let birthdayPresent = 
    wolfHall 
    |> fromBook
    |> wrapInPaper HappyBirthday
    |> withCard "Happy Birthday"

let christmasPresent = 
    yummyChoc
    |> fromChoc
    |> putInBox
    |> wrapInPaper HappyHolidays 
```

### 使用容器类型的`totalCost`函数

“总成本”函数可以使用`fold`编写，因为它不需要任何内部数据。

与早期的实现不同，我们只有两个函数参数，`fContents`和`fDecoration`，因此每个参数都需要一些模式匹配来获取“真实”数据。

这是代码：

```
let totalCost gift =  

    let fContents costSoFar contentData = 
        match contentData with
        | Book book ->
            costSoFar + book.price
        | Chocolate choc ->
            costSoFar + choc.price

    let fDecoration costSoFar decorationInfo = 
        match decorationInfo with
        | Wrapped style ->
            costSoFar + 0.5m
        | Boxed ->
            costSoFar + 1.0m
        | WithACard message ->
            costSoFar + 2.0m

    // initial accumulator
    let initialAcc = 0m

    // call the fold
    Container.fold fContents fDecoration initialAcc gift 
```

代码按预期工作：

```
birthdayPresent |> totalCost 
// 22.5m

christmasPresent |> totalCost 
// 6.5m 
```

### 使用容器类型的`description`函数

“描述”函数需要使用`foldBack`编写，因为它确实需要内部数据。与上面的代码一样，我们需要一些模式匹配来获取每种情况的“真实”数据。

```
let description gift =

    let fContents contentData = 
        match contentData with
        | Book book ->
            sprintf "'%s'" book.title
        | Chocolate choc ->
            sprintf "%A chocolate" choc.chocType

    let fDecoration decorationInfo innerText = 
        match decorationInfo with
        | Wrapped style ->
            sprintf "%s wrapped in %A paper" innerText style
        | Boxed ->
            sprintf "%s in a box" innerText 
        | WithACard message ->
            sprintf "%s with a card saying '%s'" innerText message 

    // main call
    Container.foldBack fContents fDecoration gift 
```

而且代码按我们的期望工作：

```
birthdayPresent |> description
// CORRECT "'Wolf Hall' wrapped in HappyBirthday paper with a card saying 'Happy Birthday'"

christmasPresent |> description
// CORRECT "SeventyPercent chocolate in a box wrapped in HappyHolidays paper" 
```

## 实现礼物领域的第三种方式

这一切看起来相当不错，不是吗？

但我不得不承认，我一直有所保留。

上面的代码都不是严格必需的，因为事实证明，还有*另一种*方法来建模`Gift`，而无需创建任何新的通用类型！

`Gift`类型基本上是一系列装饰的线性序列，最后一步是一些内容。我们可以将其建模为一对--一个`Content`和一个`Decoration`列表。或者为了使其更友好一些，可以使用两个字段的记录：一个用于内容，一个用于装饰。

```
type Gift = {contents: GiftContents; decorations: GiftDecoration list} 
```

就这样！不需要其他新类型！

### 使用记录类型构建值

和以前一样，让我们创建一些辅助函数来使用这种类型构建值：

```
let fromBook book = 
    { contents = (Book book); decorations = [] }

let fromChoc choc = 
    { contents = (Chocolate choc); decorations = [] }

let wrapInPaper paperStyle innerGift = 
    let decoration = Wrapped paperStyle 
    { innerGift with decorations = decoration::innerGift.decorations }

let putInBox innerGift = 
    let decoration = Boxed
    { innerGift with decorations = decoration::innerGift.decorations }

let withCard message innerGift = 
    let decoration = WithACard message
    { innerGift with decorations = decoration::innerGift.decorations } 
```

有了这些辅助函数，值的构建方式与之前的版本*完全相同*。这就是为什么要隐藏你的原始构造函数，伙计们！

```
let wolfHall = {title="Wolf Hall"; price=20m}
let yummyChoc = {chocType=SeventyPercent; price=5m}

let birthdayPresent = 
    wolfHall 
    |> fromBook
    |> wrapInPaper HappyBirthday
    |> withCard "Happy Birthday"

let christmasPresent = 
    yummyChoc
    |> fromChoc
    |> putInBox
    |> wrapInPaper HappyHolidays 
```

### 使用记录类型的`totalCost`函数

现在编写`totalCost`函数甚至更容易了。

```
let totalCost gift =  

    let contentCost = 
        match gift.contents with
        | Book book ->
            book.price
        | Chocolate choc ->
            choc.price

    let decorationFolder costSoFar decorationInfo = 
        match decorationInfo with
        | Wrapped style ->
            costSoFar + 0.5m
        | Boxed ->
            costSoFar + 1.0m
        | WithACard message ->
            costSoFar + 2.0m

    let decorationCost = 
        gift.decorations |> List.fold decorationFolder 0m

    // total cost
    contentCost + decorationCost 
```

### 使用记录类型的`description`函数

同样，`description`函数也很容易编写。

```
let description gift =

    let contentDescription = 
        match gift.contents with
        | Book book ->
            sprintf "'%s'" book.title
        | Chocolate choc ->
            sprintf "%A chocolate" choc.chocType

    let decorationFolder decorationInfo innerText = 
        match decorationInfo with
        | Wrapped style ->
            sprintf "%s wrapped in %A paper" innerText style
        | Boxed ->
            sprintf "%s in a box" innerText 
        | WithACard message ->
            sprintf "%s with a card saying '%s'" innerText message 

    List.foldBack decorationFolder gift.decorations contentDescription 
```

## 抽象还是具体？比较三种设计

如果你对这么多种设计感到困惑，我不怪你！

但事实上，这三种不同的定义实际上是可以互换的：

**原始版本**

```
type Gift =
    | Book of Book
    | Chocolate of Chocolate 
    | Wrapped of Gift * WrappingPaperStyle
    | Boxed of Gift 
    | WithACard of Gift * message:string 
```

**通用容器版本**

```
type Container<'ContentData,'DecorationData> =
    | Contents of 'ContentData
    | Decoration of 'DecorationData * Container<'ContentData,'DecorationData> 

type GiftContents = 
    | Book of Book
    | Chocolate of Chocolate 

type GiftDecoration = 
    | Wrapped of WrappingPaperStyle
    | Boxed 
    | WithACard of string

type Gift = Container<GiftContents,GiftDecoration> 
```

**记录版本**

```
type GiftContents = 
    | Book of Book
    | Chocolate of Chocolate 

type GiftDecoration = 
    | Wrapped of WrappingPaperStyle
    | Boxed 
    | WithACard of string

type Gift = {contents: GiftContents; decorations: GiftDecoration list} 
```

如果这不明显，阅读我关于数据类型大小的帖子可能会有所帮助。它解释了两种类型如何“等价”，即使乍一看它们似乎完全不同。

### 选择设计

那么哪种设计最好？答案如常，“这取决于情况”。

对于建模和记录领域，我喜欢第一种设计，其中包含五个明确的情况。对我来说，易于其他人理解比为了可重用性而引入抽象更重要。

如果我想要一个适用于许多情况的可重用模型，我可能会选择第二种（“容器”）设计。在我看来，这种类型似乎代表了一个常见的情况，其中内容是一种东西，包装是另一种东西。因此，这种抽象很可能会被使用。

最终的“对”模型很好，但通过分离两个组件，我们为这种情况过度抽象了设计。在其他情况下，这种设计可能非常合适（例如装饰者模式），但在这里，我认为不适用。

还有一个选择，可以让你兼顾所有优点。

正如我上面所指出的，所有设计在逻辑上是等价的，这意味着它们之间存在“无损”映射。在这种情况下，你的“公共”设计可以是面向领域的设计，就像第一个设计一样，但在幕后，你可以将其映射到更高效和可重用的“私有”类型。

甚至 F# 的列表实现本身也这样做。例如，`List` 模块中的一些函数，如`foldBack`和`sort`，将列表转换为数组，执行操作，然后再将其转换回列表。

* * *

## 摘要

在本文中，我们探讨了一些将`Gift`建模为通用类型的方式，以及每种方法的优缺点。

在下一篇文章中，我们将看到使用通用递归类型的真实世界示例。

*本文的源代码可在[此处的 gist](https://gist.github.com/swlaschin/c423a0f78b22496a0aff)找到。*

# 现实世界中的树

# 现实世界中的树

这篇文章是系列中的第六篇。

在上一篇文章中，我们简要地看了一些通用类型。

在本文中，我们将深入研究一些使用树和折叠的真实世界示例。

## 系列内容

这个系列的内容如下：

+   **第一部分：递归类型和消解简介**

    +   一个简单的递归类型

    +   参数化所有东西

    +   介绍消解

    +   消解的好处

    +   创建消解的规则

+   **第二部分：消解示例**

    +   消解示例：文件系统领域

    +   消解示例：产品领域

+   **第三部分：介绍折叠**

    +   我们的消解实现中的一个缺陷

    +   介绍 `fold`

    +   折叠的问题

    +   将函数用作累加器

    +   介绍 `foldback`

    +   创建折叠的规则

+   **第四部分：理解折叠**

    +   迭代 vs. 递归

    +   折叠示例：文件系统领域

    +   关于“折叠”的常见问题

+   **第五部分：通用递归类型**

    +   LinkedList：通用递归类型

    +   使礼物领域成为通用的

    +   定义通用容器类型

    +   实现礼物领域的第三种方式

    +   抽象还是具体？比较三种设计

+   **第六部分：现实世界中的树**

    +   定义通用树类型

    +   现实世界中的树类型

    +   映射树类型

    +   示例：创建目录列表

    +   示例：并行 grep

    +   示例：将文件系统存储在数据库中

    +   示例：将 Tree 序列化为 JSON

    +   示例：从 JSON 反序列化 Tree

    +   示例：从 JSON 反序列化 Tree - 带错误处理

* * *

## 定义通用的 Tree 类型

在本文中，我们将使用受之前探索的`FileSystem`领域启发的通用`Tree`。

这是原始设计：

```
type FileSystemItem =
    | File of FileInfo
    | Directory of DirectoryInfo
and FileInfo = {name:string; fileSize:int}
and DirectoryInfo = {name:string; dirSize:int; subitems:FileSystemItem list} 
```

我们可以将数据与递归分开，并像这样创建通用的`Tree`类型：

```
type Tree<'LeafData,'INodeData> =
    | LeafNode of 'LeafData
    | InternalNode of 'INodeData * Tree<'LeafData,'INodeData> seq 
```

请注意，我使用`seq`来表示子项，而不是`list`。不久之后，这个原因就会变得显而易见。

然后，可以通过将`FileInfo`指定为叶节点关联的数据，并将`DirectoryInfo`指定为内部节点关联的数据来使用`Tree`来模拟文件系统领域：

```
type FileInfo = {name:string; fileSize:int}
type DirectoryInfo = {name:string; dirSize:int}

type FileSystemItem = Tree<FileInfo,DirectoryInfo> 
```

### `Tree`的`cata`和`fold`

我们可以按照通常的方式定义`cata`和`fold`：

```
module Tree = 

    let rec cata fLeaf fNode (tree:Tree<'LeafData,'INodeData>) :'r = 
        let recurse = cata fLeaf fNode  
        match tree with
        | LeafNode leafInfo -> 
            fLeaf leafInfo 
        | InternalNode (nodeInfo,subtrees) -> 
            fNode nodeInfo (subtrees |> Seq.map recurse)

    let rec fold fLeaf fNode acc (tree:Tree<'LeafData,'INodeData>) :'r = 
        let recurse = fold fLeaf fNode  
        match tree with
        | LeafNode leafInfo -> 
            fLeaf acc leafInfo 
        | InternalNode (nodeInfo,subtrees) -> 
            // determine the local accumulator at this level
            let localAccum = fNode acc nodeInfo
            // thread the local accumulator through all the subitems using Seq.fold
            let finalAccum = subtrees |> Seq.fold recurse localAccum 
            // ... and return it
            finalAccum 
```

请注意，我*不*打算为`Tree`类型实现`foldBack`，因为树很少会深入到导致堆栈溢出的程度。需要内部数据的函数可以使用`cata`。

### 使用 Tree 模拟文件系统领域

让我们用与之前相同的值来测试它：

```
let fromFile (fileInfo:FileInfo) = 
    LeafNode fileInfo 

let fromDir (dirInfo:DirectoryInfo) subitems = 
    InternalNode (dirInfo,subitems)

let readme = fromFile {name="readme.txt"; fileSize=1}
let config = fromFile {name="config.xml"; fileSize=2}
let build  = fromFile {name="build.bat"; fileSize=3}
let src = fromDir {name="src"; dirSize=10} [readme; config; build]
let bin = fromDir {name="bin"; dirSize=10} []
let root = fromDir {name="root"; dirSize=5} [src; bin] 
```

`totalSize`函数与上一篇文章中的函数几乎相同：

```
let totalSize fileSystemItem =
    let fFile acc (file:FileInfo) = 
        acc + file.fileSize
    let fDir acc (dir:DirectoryInfo)= 
        acc + dir.dirSize
    Tree.fold fFile fDir 0 fileSystemItem 

readme |> totalSize  // 1
src |> totalSize     // 16 = 10 + (1 + 2 + 3)
root |> totalSize    // 31 = 5 + 16 + 10 
```

`largestFile`函数也是如此：

```
let largestFile fileSystemItem =
    let fFile (largestSoFarOpt:FileInfo option) (file:FileInfo) = 
        match largestSoFarOpt with
        | None -> 
            Some file                
        | Some largestSoFar -> 
            if largestSoFar.fileSize > file.fileSize then
                Some largestSoFar
            else
                Some file

    let fDir largestSoFarOpt dirInfo = 
        largestSoFarOpt

    // call the fold
    Tree.fold fFile fDir None fileSystemItem

readme |> largestFile  
// Some {name = "readme.txt"; fileSize = 1}

src |> largestFile     
// Some {name = "build.bat"; fileSize = 3}

bin |> largestFile     
// None

root |> largestFile    
// Some {name = "build.bat"; fileSize = 3} 
```

此部分的源代码可在[此要点](https://gist.github.com/swlaschin/1ef784481bae91b63a36)处获得。

## 真实世界中的 Tree 类型

我们也可以使用`Tree`来模拟*真实*的文件系统！要做到这一点，只需将叶节点类型设置为`System.IO.FileInfo`，将内部节点类型设置为`System.IO.DirectoryInfo`。

```
open System
open System.IO

type FileSystemTree = Tree<IO.FileInfo,IO.DirectoryInfo> 
```

让我们创建一些辅助方法来创建各种节点：

```
let fromFile (fileInfo:FileInfo) = 
    LeafNode fileInfo 

let rec fromDir (dirInfo:DirectoryInfo) = 
    let subItems = seq{
        yield! dirInfo.EnumerateFiles() |> Seq.map fromFile
        yield! dirInfo.EnumerateDirectories() |> Seq.map fromDir
        }
    InternalNode (dirInfo,subItems) 
```

现在你可以看到我为什么使用`seq`而不是`list`作为子项。`seq`是惰性的，这意味着我们可以创建节点而不实际命中磁盘。

这是`totalSize`函数，这次使用真实的文件信息：

```
let totalSize fileSystemItem =
    let fFile acc (file:FileInfo) = 
        acc + file.Length
    let fDir acc (dir:DirectoryInfo)= 
        acc 
    Tree.fold fFile fDir 0L fileSystemItem 
```

让我们看看当前目录的大小：

```
// set the current directory to the current source directory
Directory.SetCurrentDirectory __SOURCE_DIRECTORY__

// get the current directory as a Tree
let currentDir = fromDir (DirectoryInfo("."))

// get the size of the current directory 
currentDir  |> totalSize 
```

类似地，我们可以获取最大的文件：

```
let largestFile fileSystemItem =
    let fFile (largestSoFarOpt:FileInfo option) (file:FileInfo) = 
        match largestSoFarOpt with
        | None -> 
            Some file                
        | Some largestSoFar -> 
            if largestSoFar.Length > file.Length then
                Some largestSoFar
            else
                Some file

    let fDir largestSoFarOpt dirInfo = 
        largestSoFarOpt

    // call the fold
    Tree.fold fFile fDir None fileSystemItem

currentDir |> largestFile 
```

所以这就是使用通用递归类型的一个巨大好处。如果我们可以将真实的层次结构转换为我们的树结构，我们就可以免费获得所有 fold 的好处。

## 使用通用类型进行映射

使用通用类型的另一个优点是可以执行诸如`map`之类的操作——将每个元素转换为新类型而不更改结构。

我们可以在真实的文件系统中看到这一点。但首先，我们需要为`Tree`类型定义`map`！

`map`的实现也可以机械化，使用以下规则：

+   创建一个函数参数来处理结构中的每种情况。

+   对于非递归案例

    +   首先，使用函数参数来转换与该情况相关的非递归数据

    +   然后用相同的情况构造器包装结果

+   对于递归情况，执行两个步骤：

    +   首先，使用函数参数来转换与该情况相关的非递归数据

    +   接下来，递归地 `map` 嵌套的值。

    +   最后，用相同的情况构造器包装结果

这是为 `Tree` 创建的 `map` 的实现，遵循了这些规则：

```
module Tree = 

    let rec cata ...

    let rec fold ...

    let rec map fLeaf fNode (tree:Tree<'LeafData,'INodeData>) = 
        let recurse = map fLeaf fNode  
        match tree with
        | LeafNode leafInfo -> 
            let newLeafInfo = fLeaf leafInfo
            LeafNode newLeafInfo 
        | InternalNode (nodeInfo,subtrees) -> 
            let newNodeInfo = fNode nodeInfo
            let newSubtrees = subtrees |> Seq.map recurse 
            InternalNode (newNodeInfo, newSubtrees) 
```

如果我们查看 `Tree.map` 的签名，我们可以看到所有叶子数据都被转换为类型 `'a`，所有节点数据都被转换为类型 `'b`，最终结果是一个 `Tree<'a,'b>`。

```
val map :
  fLeaf:('LeafData -> 'a) ->
  fNode:('INodeData -> 'b) ->
  tree:Tree<'LeafData,'INodeData> -> 
  Tree<'a,'b> 
```

我们可以以类似的方式定义 `Tree.iter`：

```
module Tree = 

    let rec map ...

    let rec iter fLeaf fNode (tree:Tree<'LeafData,'INodeData>) = 
        let recurse = iter fLeaf fNode  
        match tree with
        | LeafNode leafInfo -> 
            fLeaf leafInfo
        | InternalNode (nodeInfo,subtrees) -> 
            subtrees |> Seq.iter recurse 
            fNode nodeInfo 
```

* * *

## 示例：创建目录列表

假设我们想要使用 `map` 将文件系统转换为目录列表 - 一个包含有关相应文件或目录的信息的字符串树。 这是我们可以做的：

```
let dirListing fileSystemItem =
    let printDate (d:DateTime) = d.ToString()
    let mapFile (fi:FileInfo) = 
        sprintf "%10i  %s  %-s"  fi.Length (printDate fi.LastWriteTime) fi.Name
    let mapDir (di:DirectoryInfo) = 
        di.FullName 
    Tree.map mapFile mapDir fileSystemItem 
```

然后我们可以这样打印字符串：

```
currentDir 
|> dirListing 
|> Tree.iter (printfn "%s") (printfn "\n%s") 
```

结果会看起来像这样：

```
 8315  10/08/2015 23:37:41  Fold.fsx
  3680  11/08/2015 23:59:01  FoldAndRecursiveTypes.fsproj
  1010  11/08/2015 01:19:07  FoldAndRecursiveTypes.sln
  1107  11/08/2015 23:59:01  HtmlDom.fsx
    79  11/08/2015 01:21:54  LinkedList.fsx 
```

*这个示例的源代码可以在 [此代码片段](https://gist.github.com/swlaschin/77fadc19acb8cc850276) 上找到。*

* * *

## 示例：创建并行 grep

让我们看一个更复杂的例子。 我将演示如何使用 `fold` 创建并行的“grep”样式搜索。

逻辑将是这样的：

+   使用 `fold` 来迭代文件。

+   对于每个文件，如果其名称与所需文件模式不匹配，则返回 `None`。

+   如果要处理文件，则返回一个返回文件中所有行匹配的异步。

+   接下来，所有这些 async -- fold 的输出 -- 被聚合成一个序列。

+   使用 `Async.Parallel` 将异步序列转换为单个异步，该函数返回结果列表。

在我们开始编写主要代码之前，我们需要一些辅助函数。

首先，一个异步地在文件中折叠行的通用函数。 这将是模式匹配的基础。

```
/// Fold over the lines in a file asynchronously
/// passing in the current line and line number tothe folder function.
///
/// Signature:
///   folder:('a -> int -> string -> 'a) -> 
///   acc:'a -> 
///   fi:FileInfo -> 
///   Async<'a>
let foldLinesAsync folder acc (fi:FileInfo) = 
    async {
        let mutable acc = acc
        let mutable lineNo = 1
        use sr = new StreamReader(path=fi.FullName)
        while not sr.EndOfStream do
            let! lineText = sr.ReadLineAsync() |> Async.AwaitTask
            acc <- folder acc lineNo lineText 
            lineNo <- lineNo + 1
        return acc
    } 
```

接下来是一个小助手，允许我们对 `Async` 值进行 `map`：

```
let asyncMap f asyncX = async { 
    let! x = asyncX
    return (f x)  } 
```

现在是中心逻辑。 我们将创建一个函数，给定一个 `textPattern` 和一个 `FileInfo`，将异步返回与 textPattern 匹配的行的列表：

```
/// return the matching lines in a file, as an async<string list>
let matchPattern textPattern (fi:FileInfo) = 
    // set up the regex
    let regex = Text.RegularExpressions.Regex(pattern=textPattern)

    // set up the function to use with "fold"
    let folder results lineNo lineText =
        if regex.IsMatch lineText then
            let result = sprintf "%40s:%-5i   %s" fi.Name lineNo lineText
            result :: results
        else
            // pass through
            results

    // main flow
    fi
    |> foldLinesAsync folder []
    // the fold output is in reverse order, so reverse it
    |> asyncMap List.rev 
```

现在是 `grep` 函数本身：

```
let grep filePattern textPattern fileSystemItem =
    let regex = Text.RegularExpressions.Regex(pattern=filePattern)

    /// if the file matches the pattern
    /// do the matching and return Some async, else None
    let matchFile (fi:FileInfo) =
        if regex.IsMatch fi.Name then
            Some (matchPattern textPattern fi)
        else
            None

    /// process a file by adding its async to the list
    let fFile asyncs (fi:FileInfo) = 
        // add to the list of asyncs
        (matchFile fi) :: asyncs 

    // for directories, just pass through the list of asyncs
    let fDir asyncs (di:DirectoryInfo)  = 
        asyncs 

    fileSystemItem
    |> Tree.fold fFile fDir []    // get the list of asyncs
    |> Seq.choose id              // choose the Somes (where a file was processed)
    |> Async.Parallel             // merge all asyncs into a single async
    |> asyncMap (Array.toList >> List.collect id)  // flatten array of lists into a single list 
```

让我们测试一下吧！

```
currentDir 
|> grep "fsx" "LinkedList" 
|> Async.RunSynchronously 
```

结果会看起来像这样：

```
"                  SizeOfTypes.fsx:120     type LinkedList<'a> = ";
"                  SizeOfTypes.fsx:122         | Cell of head:'a * tail:LinkedList<'a>";
"                  SizeOfTypes.fsx:125     let S = size(LinkedList<'a>)";
"      RecursiveTypesAndFold-3.fsx:15      // LinkedList";
"      RecursiveTypesAndFold-3.fsx:18      type LinkedList<'a> = ";
"      RecursiveTypesAndFold-3.fsx:20          | Cons of head:'a * tail:LinkedList<'a>";
"      RecursiveTypesAndFold-3.fsx:26      module LinkedList = ";
"      RecursiveTypesAndFold-3.fsx:39              list:LinkedList<'a> ";
"      RecursiveTypesAndFold-3.fsx:64              list:LinkedList<'a> -> "; 
```

这对于大约 40 行代码来说不算糟糕。 这种简洁性是因为我们使用了各种隐藏了递归的 `fold` 和 `map`，这使我们能够专注于模式匹配逻辑本身。

当然，这并不高效或优化（每一行都有一个异步！），所以我不会将其用作真正的实现，但它确实给出了 `fold` 的强大功能的一个想法。

*这个示例的源代码可以在 [此代码片段](https://gist.github.com/swlaschin/137c322b5a46b97cc8be) 上找到。*

* * *

## 示例：将文件系统存储在数据库中

对于下一个示例，让我们看看如何在数据库中存储文件系统树。我真的不知道为什么你要这样做，但这些原则同样适用于存储任何分层结构，所以我还是会演示一下！

为了在数据库中建模文件系统层次结构，假设我们有四个表：

+   `DbDir` 存储关于每个目录的信息。

+   `DbFile` 存储关于每个文件的信息。

+   `DbDir_File` 存储目录和文件之间的关系。

+   `DbDir_Dir` 存储父目录和子目录之间的关系。

这里是数据库表定义：

```
CREATE TABLE DbDir (
    DirId int IDENTITY NOT NULL,
    Name nvarchar(50) NOT NULL
)

CREATE TABLE DbFile (
    FileId int IDENTITY NOT NULL,
    Name nvarchar(50) NOT NULL,
    FileSize int NOT NULL
)

CREATE TABLE DbDir_File (
    DirId int NOT NULL,
    FileId int NOT NULL
)

CREATE TABLE DbDir_Dir (
    ParentDirId int NOT NULL,
    ChildDirId int NOT NULL
) 
```

这很简单。但请注意，为了完全保存一个目录及其与子项的关系，我们首先需要所有子项的 id，每个子目录都需要其子项的 id，依此类推。

这意味着我们应该使用 `cata` 而不是 `fold`，这样我们就可以访问层次结构下层的数据。

### 实现数据库函数

我们不够聪明来使用 [SQL Provider](https://fsprojects.github.io/SQLProvider/)，所以我们编写了自己的表插入函数，就像这个虚拟的：

```
/// Insert a DbFile record 
let insertDbFile name (fileSize:int64) =
    let id = nextIdentity()
    printfn "%10s: inserting id:%i name:%s size:%i" "DbFile" id name fileSize 
```

在真实的数据库中，标识列会自动生成，但对于这个示例，我会使用一个小助手函数 `nextIdentity`：

```
let nextIdentity =
    let id = ref 0
    fun () -> 
        id := !id + 1
        !id

// test
nextIdentity() // 1
nextIdentity() // 2
nextIdentity() // 3 
```

现在为了插入一个目录，我们需要首先知道目录中所有文件的 id。这意味着 `insertDbFile` 函数应该返回生成的 id。

```
/// Insert a DbFile record and return the new file id
let insertDbFile name (fileSize:int64) =
    let id = nextIdentity()
    printfn "%10s: inserting id:%i name:%s size:%i" "DbFile" id name fileSize
    id 
```

但这个逻辑也适用于目录：

```
/// Insert a DbDir record and return the new directory id
let insertDbDir name =
    let id = nextIdentity()
    printfn "%10s: inserting id:%i name:%s" "DbDir" id name
    id 
```

但这还不够好。当子 id 传递给父目录时，它需要区分文件和目录，因为关系存储在不同的表中。

没问题 -- 我们只需使用一个选择类型来区分它们！

```
type PrimaryKey =
    | FileId of int
    | DirId of int 
```

有了这个，我们可以完成数据库函数的实现：

```
/// Insert a DbFile record and return the new PrimaryKey
let insertDbFile name (fileSize:int64) =
    let id = nextIdentity()
    printfn "%10s: inserting id:%i name:%s size:%i" "DbFile" id name fileSize
    FileId id

/// Insert a DbDir record and return the new PrimaryKey
let insertDbDir name =
    let id = nextIdentity()
    printfn "%10s: inserting id:%i name:%s" "DbDir" id name
    DirId id

/// Insert a DbDir_File record
let insertDbDir_File dirId fileId =
    printfn "%10s: inserting parentDir:%i childFile:%i" "DbDir_File" dirId fileId 

/// Insert a DbDir_Dir record
let insertDbDir_Dir parentDirId childDirId =
    printfn "%10s: inserting parentDir:%i childDir:%i" "DbDir_Dir" parentDirId childDirId 
```

### 使用 catamorphism

如上所述，我们需要使用 `cata` 而不是 `fold`，因为我们需要在每一步中访问内部 id。

处理 `File` 情况的函数很简单 -- 只需插入并返回 `PrimaryKey`。

```
let fFile (fi:FileInfo) = 
    insertDbFile fi.Name fi.Length 
```

处理 `Directory` 情况的函数将接收 `DirectoryInfo` 和已经插入的子项的 `PrimaryKey` 序列。

它应该插入主目录记录，然后插入子目录，然后返回下一个更高级别的 `PrimaryKey`：

```
let fDir (di:DirectoryInfo) childIds  = 
    let dirId = insertDbDir di.Name
    // insert the children
    // return the id to the parent
    dirId 
```

在插入目录记录并获取其 id 后，对于每个子 id，我们要插入到 `DbDir_File` 表或 `DbDir_Dir`，取决于 `childId` 的类型。

```
let fDir (di:DirectoryInfo) childIds  = 
    let dirId = insertDbDir di.Name
    let parentPK = pkToInt dirId 
    childIds |> Seq.iter (fun childId ->
        match childId with
        | FileId fileId -> insertDbDir_File parentPK fileId 
        | DirId childDirId -> insertDbDir_Dir parentPK childDirId 
    )
    // return the id to the parent
    dirId 
```

请注意，我还创建了一个小助手函数 `pkToInt`，从 `PrimaryKey` 类型中提取整数 id。

这里是所有代码的整体：

```
open System
open System.IO

let nextIdentity =
    let id = ref 0
    fun () -> 
        id := !id + 1
        !id

type PrimaryKey =
    | FileId of int
    | DirId of int

/// Insert a DbFile record and return the new PrimaryKey
let insertDbFile name (fileSize:int64) =
    let id = nextIdentity()
    printfn "%10s: inserting id:%i name:%s size:%i" "DbFile" id name fileSize
    FileId id

/// Insert a DbDir record and return the new PrimaryKey
let insertDbDir name =
    let id = nextIdentity()
    printfn "%10s: inserting id:%i name:%s" "DbDir" id name
    DirId id

/// Insert a DbDir_File record
let insertDbDir_File dirId fileId =
    printfn "%10s: inserting parentDir:%i childFile:%i" "DbDir_File" dirId fileId 

/// Insert a DbDir_Dir record
let insertDbDir_Dir parentDirId childDirId =
    printfn "%10s: inserting parentDir:%i childDir:%i" "DbDir_Dir" parentDirId childDirId

let pkToInt primaryKey = 
    match primaryKey with
    | FileId fileId -> fileId 
    | DirId dirId -> dirId 

let insertFileSystemTree fileSystemItem =

    let fFile (fi:FileInfo) = 
        insertDbFile fi.Name fi.Length

    let fDir (di:DirectoryInfo) childIds  = 
        let dirId = insertDbDir di.Name
        let parentPK = pkToInt dirId 
        childIds |> Seq.iter (fun childId ->
            match childId with
            | FileId fileId -> insertDbDir_File parentPK fileId 
            | DirId childDirId -> insertDbDir_Dir parentPK childDirId 
        )
        // return the id to the parent
        dirId

    fileSystemItem
    |> Tree.cata fFile fDir 
```

现在让我们来测试一下：

```
// get the current directory as a Tree
let currentDir = fromDir (DirectoryInfo("."))

// insert into the database
currentDir 
|> insertFileSystemTree 
```

输出应该看起来像这样：

```
 DbDir: inserting id:41 name:FoldAndRecursiveTypes
    DbFile: inserting id:42 name:Fold.fsx size:8315
DbDir_File: inserting parentDir:41 childFile:42
    DbFile: inserting id:43 name:FoldAndRecursiveTypes.fsproj size:3680
DbDir_File: inserting parentDir:41 childFile:43
    DbFile: inserting id:44 name:FoldAndRecursiveTypes.sln size:1010
DbDir_File: inserting parentDir:41 childFile:44
...
     DbDir: inserting id:57 name:bin
     DbDir: inserting id:58 name:Debug
 DbDir_Dir: inserting parentDir:57 childDir:58
 DbDir_Dir: inserting parentDir:41 childDir:57 
```

你可以看到，在迭代文件时生成了 ids，并且每个`DbFile`插入后都跟着一个`DbDir_File`插入。

*此示例的源代码可在[此代码片段](https://gist.github.com/swlaschin/3a416f26d873faa84cde)中找到。*

* * *

## 示例：将树序列化为 JSON

让我们再看一个常见的挑战：将树序列化和反序列化为 JSON、XML 或其他格式。

让我们再次使用 Gift 域，但这次，我们将`Gift`类型建模为一棵树。这意味着我们可以在一个盒子里放更多的东西！

### 将 Gift 域建模为树

这里再次是主要类型，但请注意最终的`Gift`类型被定义为一棵树：

```
type Book = {title: string; price: decimal}
type ChocolateType = Dark | Milk | SeventyPercent
type Chocolate = {chocType: ChocolateType ; price: decimal}

type WrappingPaperStyle = 
    | HappyBirthday
    | HappyHolidays
    | SolidColor

// unified data for non-recursive cases
type GiftContents = 
    | Book of Book
    | Chocolate of Chocolate 

// unified data for recursive cases
type GiftDecoration = 
    | Wrapped of WrappingPaperStyle
    | Boxed 
    | WithACard of string

type Gift = Tree<GiftContents,GiftDecoration> 
```

通常，我们可以创建一些辅助函数来帮助构建`Gift`：

```
let fromBook book = 
    LeafNode (Book book)

let fromChoc choc = 
    LeafNode (Chocolate choc)

let wrapInPaper paperStyle innerGift = 
    let container = Wrapped paperStyle 
    InternalNode (container, [innerGift])

let putInBox innerGift = 
    let container = Boxed
    InternalNode (container, [innerGift])

let withCard message innerGift = 
    let container = WithACard message
    InternalNode (container, [innerGift])

let putTwoThingsInBox innerGift innerGift2 = 
    let container = Boxed
    InternalNode (container, [innerGift;innerGift2]) 
```

我们可以创建一些示例数据：

```
let wolfHall = {title="Wolf Hall"; price=20m}
let yummyChoc = {chocType=SeventyPercent; price=5m}

let birthdayPresent = 
    wolfHall 
    |> fromBook
    |> wrapInPaper HappyBirthday
    |> withCard "Happy Birthday"

let christmasPresent = 
    yummyChoc
    |> fromChoc
    |> putInBox
    |> wrapInPaper HappyHolidays

let twoBirthdayPresents = 
    let thing1 = wolfHall |> fromBook 
    let thing2 = yummyChoc |> fromChoc
    putTwoThingsInBox thing1 thing2 
    |> wrapInPaper HappyBirthday

let twoWrappedPresentsInBox = 
    let thing1 = wolfHall |> fromBook |> wrapInPaper HappyHolidays
    let thing2 = yummyChoc |> fromChoc  |> wrapInPaper HappyBirthday
    putTwoThingsInBox thing1 thing2 
```

`description`等函数现在需要处理一个*列表*的内部文本，而不是一个。我们将用`&`分隔符将字符串连接在一起：

```
let description gift =

    let fLeaf leafData = 
        match leafData with
        | Book book ->
            sprintf "'%s'" book.title
        | Chocolate choc ->
            sprintf "%A chocolate" choc.chocType

    let fNode nodeData innerTexts = 
        let innerText = String.concat " & " innerTexts 
        match nodeData with
        | Wrapped style ->
            sprintf "%s wrapped in %A paper" innerText style
        | Boxed ->
            sprintf "%s in a box" innerText
        | WithACard message ->
            sprintf "%s with a card saying '%s'" innerText message 

    // main call
    Tree.cata fLeaf fNode gift 
```

最后，我们可以检查函数是否仍然像以前一样工作，并且多个项目是否被正确处理：

```
birthdayPresent |> description
// "'Wolf Hall' wrapped in HappyBirthday paper with a card saying 'Happy Birthday'"

christmasPresent |> description
// "SeventyPercent chocolate in a box wrapped in HappyHolidays paper"

twoBirthdayPresents |> description
// "'Wolf Hall' & SeventyPercent chocolate in a box 
//   wrapped in HappyBirthday paper"

twoWrappedPresentsInBox |> description
// "'Wolf Hall' wrapped in HappyHolidays paper 
//   & SeventyPercent chocolate wrapped in HappyBirthday paper 
//   in a box" 
```

### 第 1 步：定义`GiftDto`

我们的`Gift`类型由许多区分联合组成。根据我的经验，这些不会序列化得很好。事实上，大多数复杂类型都不会序列化得很好！

因此，我喜欢定义[DTO](https://en.wikipedia.org/wiki/Data_transfer_object)类型，这些类型专门设计用于良好的序列化。实际上，这意味着 DTO 类型受到以下约束：

+   只应使用记录类型。

+   记录字段应仅包含原始值，如`int`、`string`和`bool`。

这样做，我们还能获得一些其他优势：

**我们能控制序列化输出。** 大多数序列化器都以相同的方式处理这些数据类型，而“奇怪”的东西，比如联合类型，可能会被不同的库解释得不同。

**我们能更好地控制错误处理。** 我在处理序列化数据时的首要规则是“不要相信任何人”。很常见的情况是数据结构正确但对于域来说是无效的：被认为是非空字符串实际上是空的，字符串太长，整数超出了正确的范围，等等。

通过使用 DTO，我们可以确保反序列化步骤本身能够工作。然后，当我们将 DTO 转换为域类型时，我们可以进行适当的验证。

因此，让我们为我们的域定义一些 DTO 类型。每个 DTO 类型将对应一个域类型，所以让我们从`GiftContents`开始。我们将定义一个相应的 DTO 类型，称为`GiftContentsDto`，如下所示：

```
[<CLIMutableAttribute>]
type GiftContentsDto = {
    discriminator : string // "Book" or "Chocolate"
    // for "Book" case only
    bookTitle: string    
    // for "Chocolate" case only
    chocolateType : string // one of "Dark" "Milk" "SeventyPercent"
    // for all cases
    price: decimal
    } 
```

显然，这与原始的`GiftContents`相当不同，让我们看看它们的区别：

+   首先，它具有`CLIMutableAttribute`，允许反序列化器使用反射构造它们。

+   其次，它有一个`discriminator`，指示正在使用原始联合类型的哪种情况。显然，这个字符串可以设置为任何值，因此在将 DTO 转换回域类型时，我们必须仔细检查！

+   接下来是一系列字段，每个字段用于存储需要存储的所有可能数据项。例如，在`Book`情况下，我们需要一个`bookTitle`，而在`Chocolate`情况下，我们需要巧克力类型。最后`price`字段在两种类型中都存在。请注意，巧克力类型也存储为字符串，因此在从 DTO 转换为领域时也需要特殊处理。

`GiftDecorationDto` 类型以相同方式创建，具有鉴别器和字符串而不是联合。

```
[<CLIMutableAttribute>]
type GiftDecorationDto = {
    discriminator: string // "Wrapped" or "Boxed" or "WithACard"
    // for "Wrapped" case only
    wrappingPaperStyle: string  // "HappyBirthday" or "HappyHolidays" or "SolidColor" 
    // for "WithACard" case only
    message: string  
    } 
```

最后，我们可以将`GiftDto`类型定义为由两个 DTO 类型组成的树：

```
type GiftDto = Tree<GiftContentsDto,GiftDecorationDto> 
```

### 步骤 2：将`Gift`转换为`GiftDto`

现在我们有了这个 DTO 类型，我们只需要使用`Tree.map`将`Gift`转换为`GiftDto`。为了做到这一点，我们需要创建两个函数：一个将`GiftContents`转换为`GiftContentsDto`，另一个将`GiftDecoration`转换为`GiftDecorationDto`。

这是`giftToDto`的完整代码，应该是不言自明的：

```
let giftToDto (gift:Gift) :GiftDto =

    let fLeaf leafData :GiftContentsDto = 
        match leafData with
        | Book book ->
            {discriminator= "Book"; bookTitle=book.title; chocolateType=null; price=book.price}
        | Chocolate choc ->
            let chocolateType = sprintf "%A" choc.chocType
            {discriminator= "Chocolate"; bookTitle=null; chocolateType=chocolateType; price=choc.price}

    let fNode nodeData :GiftDecorationDto = 
        match nodeData with
        | Wrapped style ->
            let wrappingPaperStyle = sprintf "%A" style
            {discriminator= "Wrapped"; wrappingPaperStyle=wrappingPaperStyle; message=null}
        | Boxed ->
            {discriminator= "Boxed"; wrappingPaperStyle=null; message=null}
        | WithACard message ->
            {discriminator= "WithACard"; wrappingPaperStyle=null; message=message}

    // main call
    Tree.map fLeaf fNode gift 
```

您可以看到情况（`Book`，`Chocolate`等）被转换为`discriminator`字符串，`chocolateType`也被转换为字符串，就像上面解释的那样。

### 步骤 3：定义一个`TreeDto`

我之前说过，一个好的 DTO 应该是一个记录类型。我们已经转换了树的节点，但树*本身*是一个联合类型！我们还需要将`Tree`类型转换为比如`TreeDto`类型。

我们如何做到这一点？就像对于礼物 DTO 类型一样，我们将创建一个包含两种情况所有数据的记录类型。我们可以像之前一样使用鉴别器字段，但这次，由于只有两种选择，叶子和内部节点，当进行反序列化时，我将仅检查值是否为 null。如果叶子值不为 null，则记录必须表示`LeafNode`情况，否则记录必须表示`InternalNode`情况。

这是数据类型的定义：

```
/// A DTO that represents a Tree
/// The Leaf/Node choice is turned into a record
[<CLIMutableAttribute>]
type TreeDto<'LeafData,'NodeData> = {
    leafData : 'LeafData
    nodeData : 'NodeData
    subtrees : TreeDto<'LeafData,'NodeData>[] } 
```

与以前一样，类型具有`CLIMutableAttribute`。并且与以前一样，类型具有字段来存储所有可能选择的数据。`subtrees`存储为数组而不是 seq -- 这使得序列化程序很高兴！

要创建一个`TreeDto`，我们使用我们的老朋友`cata`从常规`Tree`中组装记录。

```
/// Transform a Tree into a TreeDto
let treeToDto tree : TreeDto<'LeafData,'NodeData> =

    let fLeaf leafData  = 
        let nodeData = Unchecked.defaultof<'NodeData>
        let subtrees = [||]
        {leafData=leafData; nodeData=nodeData; subtrees=subtrees}

    let fNode nodeData subtrees = 
        let leafData = Unchecked.defaultof<'NodeData>
        let subtrees = subtrees |> Seq.toArray 
        {leafData=leafData; nodeData=nodeData; subtrees=subtrees}

    // recurse to build up the TreeDto
    Tree.cata fLeaf fNode tree 
```

请注意，在 F# 中，记录不可为空，因此我使用`Unchecked.defaultof<'NodeData>`而不是`null`来指示缺失数据。

还要注意，我假设`LeafData`或`NodeData`是引用类型。如果`LeafData`或`NodeData`是像`int`或`bool`这样的值类型，那么这种方法将会失败，因为您无法区分默认值和缺失值。在这种情况下，我会像以前一样切换到鉴别器字段。

或者，我可以使用`IDictionary`。这样做反序列化会不太方便，但可以避免需要进行空值检查。

### 步骤 4：��列化`TreeDto`

最后，我们可以使用 JSON 序列化程序序列化`TreeDto`。

对于这个例子，我使用内置的 `DataContractJsonSerializer`，这样我就不需要依赖于 NuGet 包。还有其他一些 JSON 序列化器可能更适合一个正式的项目。

```
#r "System.Runtime.Serialization.dll"

open System.Runtime.Serialization
open System.Runtime.Serialization.Json

let toJson (o:'a) = 
    let serializer = new DataContractJsonSerializer(typeof<'a>)
    let encoding = System.Text.UTF8Encoding()
    use stream = new System.IO.MemoryStream()
    serializer.WriteObject(stream,o) 
    stream.Close()
    encoding.GetString(stream.ToArray()) 
```

### 第五步：组装管道

所以，把所有这些放在一起，我们有以下管道：

+   使用 `giftToDto` 将 `Gift` 转换为 `GiftDto`，

    即，使用 `Tree.map` 从 `Tree<GiftContents,GiftDecoration>` 转换到 `Tree<GiftContentsDto,GiftDecorationDto>`

+   转换 `Tree` 到 `TreeDto` 使用 `treeToDto`，

    即，使用 `Tree.cata` 从 `Tree<GiftContentsDto,GiftDecorationDto>` 转换到 `TreeDto<GiftContentsDto,GiftDecorationDto>`

+   将 `TreeDto` 序列化为 JSON 字符串

这是一些示例代码：

```
let goodJson = christmasPresent |> giftToDto |> treeToDto |> toJson 
```

这是 JSON 输出的样子：

```
{
  "leafData@": null,
  "nodeData@": {
    "discriminator@": "Wrapped",
    "message@": null,
    "wrappingPaperStyle@": "HappyHolidays"
  },
  "subtrees@": [
    {
      "leafData@": null,
      "nodeData@": {
        "discriminator@": "Boxed",
        "message@": null,
        "wrappingPaperStyle@": null
      },
      "subtrees@": [
        {
          "leafData@": {
            "bookTitle@": null,
            "chocolateType@": "SeventyPercent",
            "discriminator@": "Chocolate",
            "price@": 5
          },
          "nodeData@": null,
          "subtrees@": []
        }
      ]
    }
  ]
} 
```

字段名上的丑陋 `@` 符号是序列化 F# 记录类型的产物。这可以通过一点努力来纠正，但我现在不打算费心！

*此示例的源代码可在 [此代码片段](https://gist.github.com/swlaschin/bbe70c768215b209c06c) 上找到*

* * *

## 示例：从 JSON 反序列化树

现在我们已经创建了 JSON，那么反过来加载到 `Gift` 呢？

简单！我们只需要颠倒管道：

+   将 JSON 字符串反序列化为 `TreeDto`。

+   使用 `dtoToTree` 将 `TreeDto` 转换为 `Tree`，

    即，从 `TreeDto<GiftContentsDto,GiftDecorationDto>` 转换到 `Tree<GiftContentsDto,GiftDecorationDto>`。我们不能使用 `cata` 来实现这一点 -- 我们将不得不创建一个小的递归循环。

+   使用 `dtoToGift` 将 `GiftDto` 转换为 `Gift`，

    即，使用 `Tree.map` 从 `Tree<GiftContentsDto,GiftDecorationDto>` 转换到 `Tree<GiftContents,GiftDecoration>`。

### 第一步：反序列化 `TreeDto`

我们可以使用 JSON 序列化器反序列化 `TreeDto`。

```
let fromJson<'a> str = 
    let serializer = new DataContractJsonSerializer(typeof<'a>)
    let encoding = System.Text.UTF8Encoding()
    use stream = new System.IO.MemoryStream(encoding.GetBytes(s=str))
    let obj = serializer.ReadObject(stream) 
    obj :?> 'a 
```

如果反序列化失败会怎么样？暂时，我们将忽略任何错误处理，并让异常传播。

### 第二步：将 `TreeDto` 转换为 `Tree`

要将 `TreeDto` 转换为 `Tree`，我们需要递归地遍历记录及其子树，根据适当的字段是否为 null，将每个字段转换为 `InternalNode` 或 `LeafNode`。

```
let rec dtoToTree (treeDto:TreeDto<'Leaf,'Node>) :Tree<'Leaf,'Node> =
    let nullLeaf = Unchecked.defaultof<'Leaf>
    let nullNode = Unchecked.defaultof<'Node>

    // check if there is nodeData present
    if treeDto.nodeData <> nullNode then
        if treeDto.subtrees = null then
            failwith "subtrees must not be null if node data present"
        else
            let subtrees = treeDto.subtrees |> Array.map dtoToTree 
            InternalNode (treeDto.nodeData,subtrees)
    // check if there is leafData present
    elif treeDto.leafData <> nullLeaf then
        LeafNode (treeDto.leafData) 
    // if both missing then fail
    else
        failwith "expecting leaf or node data" 
```

正如你所见，有很多事情可能出错：

+   如果 `leafData` 和 `nodeData` 字段都为 null 会怎么样？

+   如果 `nodeData` 字段不为 null，但 `subtrees` 字段 *为* null 会怎么样？

再次，我们将忽略任何错误处理，只是抛出异常（暂时）。

*问题：我们是否可以为 `TreeDto` 创建一个 `cata`，使这段代码更简单？是否值得？*

### 第三步：将 `GiftDto` 转换为 `Gift`

现在我们有了一个合适的树，我们可以再次使用 `Tree.map` 将每个叶子和内部节点从 DTO 转换为适当的域类型。

这意味着我们需要将 `GiftContentsDto` 映射到 `GiftContents`，将 `GiftDecorationDto` 映射到 `GiftDecoration` 的函数。

这是完整的代码 -- 比起另一个方向要复杂得多！

代码可以分组如下：

+   辅助方法（如`strToChocolateType`），将字符串转换为适当的领域类型，并在输入无效时抛出异常。

+   case 转换器方法（如`bookFromDto`），将整个 DTO 转换为一个 case。

+   最后，`dtoToGift`函数本身。它查看`discriminator`字段，看看调用哪个 case 转换器，并在识别不出 discriminator 值时抛出异常。

```
let strToBookTitle str =
    match str with
    | null -> failwith "BookTitle must not be null" 
    | _ -> str

let strToChocolateType str =
    match str with
    | "Dark" -> Dark
    | "Milk" -> Milk
    | "SeventyPercent" -> SeventyPercent
    | _ -> failwithf "ChocolateType %s not recognized" str

let strToWrappingPaperStyle str =
    match str with
    | "HappyBirthday" -> HappyBirthday
    | "HappyHolidays" -> HappyHolidays
    | "SolidColor" -> SolidColor
    | _ -> failwithf "WrappingPaperStyle %s not recognized" str

let strToCardMessage str =
    match str with
    | null -> failwith "CardMessage must not be null" 
    | _ -> str

let bookFromDto (dto:GiftContentsDto) =
    let bookTitle = strToBookTitle dto.bookTitle
    Book {title=bookTitle; price=dto.price}

let chocolateFromDto (dto:GiftContentsDto) =
    let chocType = strToChocolateType dto.chocolateType 
    Chocolate {chocType=chocType; price=dto.price}

let wrappedFromDto (dto:GiftDecorationDto) =
    let wrappingPaperStyle = strToWrappingPaperStyle dto.wrappingPaperStyle
    Wrapped wrappingPaperStyle 

let boxedFromDto (dto:GiftDecorationDto) =
    Boxed

let withACardFromDto (dto:GiftDecorationDto) =
    let message = strToCardMessage dto.message
    WithACard message 

/// Transform a GiftDto to a Gift
let dtoToGift (giftDto:GiftDto) :Gift=

    let fLeaf (leafDto:GiftContentsDto) = 
        match leafDto.discriminator with
        | "Book" -> bookFromDto leafDto
        | "Chocolate" -> chocolateFromDto leafDto
        | _ -> failwithf "Unknown leaf discriminator '%s'" leafDto.discriminator 

    let fNode (nodeDto:GiftDecorationDto)  = 
        match nodeDto.discriminator with
        | "Wrapped" -> wrappedFromDto nodeDto
        | "Boxed" -> boxedFromDto nodeDto
        | "WithACard" -> withACardFromDto nodeDto
        | _ -> failwithf "Unknown node discriminator '%s'" nodeDto.discriminator 

    // map the tree
    Tree.map fLeaf fNode giftDto 
```

### 步骤 4：组装管道

现在我们可以组装管道，接受一个 JSON 字符串并创建一个`Gift`。

```
let goodGift = goodJson |> fromJson |> dtoToTree |> dtoToGift

// check that the description is unchanged
goodGift |> description
// "SeventyPercent chocolate in a box wrapped in HappyHolidays paper" 
```

这样做没问题，但错误处理很糟糕！

看看如果我们稍微损坏 JSON 会发生什么：

```
let badJson1 = goodJson.Replace("leafData","leafDataXX")

let badJson1_result = badJson1 |> fromJson |> dtoToTree |> dtoToGift
// Exception "The data contract type 'TreeDto' cannot be deserialized because the required data member 'leafData@' was not found." 
```

我们得到一个丑陋的异常。

或者如果 discriminator 是错误的会怎样？

```
let badJson2 = goodJson.Replace("Wrapped","Wrapped2")

let badJson2_result = badJson2 |> fromJson |> dtoToTree |> dtoToGift
// Exception "Unknown node discriminator 'Wrapped2'" 
```

或者 WrappingPaperStyle DU 的值之一？

```
let badJson3 = goodJson.Replace("HappyHolidays","HappyHolidays2")
let badJson3_result = badJson3 |> fromJson |> dtoToTree |> dtoToGift
// Exception "WrappingPaperStyle HappyHolidays2 not recognized" 
```

我们得到很多异常，作为函数式程序员，我们应该尽可能地消除它们。

我们将在下一节讨论如何做到这一点。

*此示例的源代码可在[此代码片段](https://gist.github.com/swlaschin/bbe70c768215b209c06c)中找到。*

* * *

## 示例：从 JSON 反序列化 Tree - 带有错误处理

为了解决错误处理问题，我们将使用下面显示的`Result`类型：

```
type Result<'a> = 
    | Success of 'a
    | Failure of string list 
```

我不会在这里解释它是如何工作的。如果你对这种方法不熟悉，请阅读我的文章或[观看我关于函数式错误处理主题的讲座](http://fsharpforfunandprofit.com/rop/)。

让我们重新审视前一节中的所有步骤，并使用`Result`而不是抛出异常。

### 步骤 1：反序列化`TreeDto`

当我们使用 JSON 序列化器反序列化`TreeDto`时，我们将捕获异常并将其转换为`Result`。

```
let fromJson<'a> str = 
    try
        let serializer = new DataContractJsonSerializer(typeof<'a>)
        let encoding = System.Text.UTF8Encoding()
        use stream = new System.IO.MemoryStream(encoding.GetBytes(s=str))
        let obj = serializer.ReadObject(stream) 
        obj :?> 'a 
        |> Result.retn
    with
    | ex -> 
        Result.failWithMsg ex.Message 
```

现在`fromJson`的签名是`string -> Result<'a>`。

### 步骤 2：将`TreeDto`转换为`Tree`

与以前一样，通过递归循环遍历记录及其子树，将每个转换为`InternalNode`或`LeafNode`，我们将`TreeDto`转换为`Tree`。不过，这次我们使用`Result`来处理任何错误。

```
let rec dtoToTreeOfResults (treeDto:TreeDto<'Leaf,'Node>) :Tree<Result<'Leaf>,Result<'Node>> =
    let nullLeaf = Unchecked.defaultof<'Leaf>
    let nullNode = Unchecked.defaultof<'Node>

    // check if there is nodeData present
    if treeDto.nodeData <> nullNode then
        if treeDto.subtrees = null then
            LeafNode <| Result.failWithMsg "subtrees must not be null if node data present"
        else
            let subtrees = treeDto.subtrees |> Array.map dtoToTreeOfResults 
            InternalNode (Result.retn treeDto.nodeData,subtrees) 
    // check if there is leafData present
    elif treeDto.leafData <> nullLeaf then
        LeafNode <| Result.retn (treeDto.leafData) 
    // if both missing then fail
    else
        LeafNode <| Result.failWithMsg "expecting leaf or node data"

// val dtoToTreeOfResults : 
//   treeDto:TreeDto<'Leaf,'Node> -> Tree<Result<'Leaf>,Result<'Node>> 
```

但是，糟糕的是，我们现在有一个`Tree`，其中每个内部节点和叶子都包裹在一个`Result`中。这是一个`Results`的树！实际的丑陋签名是这样的：`Tree<Result<'Leaf>,Result<'Node>>`。

但是这种类型是无用的 -- 我们*真正*想要的是将所有错误合并在一起，并返回包含`Tree`的`Result`。

我们如何将一组 Results 的 Tree 转换为一个 Tree 的 Result？

答案是使用一个`sequence`函数，它可以"交换"这两种类型。你可以在我的提升世界系列文章中更多地了解`sequence`。

*请注意，我们也可以使用稍微复杂一点的`traverse`变体将`map`和`sequence`合并为一步，但为了演示的目的，如果将步骤保持分开，更容易理解。*

我们需要为 Tree/Result 组合创建自己的`sequence`函数。幸运的是，创建一个序列函数是一个机械过程：

+   对于低类型（`Result`），我们需要定义 `apply` 和 `return` 函数。有关 `apply` 的更多详细信息，请参见这里。

+   对于更高的类型（`Tree`），我们需要一个 `cata` 函数，我们已经有了。

+   在范畴化中，高类型的每个构造器（在这种情况下是 `LeafNode` 和 `InternalNode`）都被等效地替换为一个被 "提升" 到 `Result` 类型的等价物（例如 `retn LeafNode <*> data`）。

这是实际的代码 -- 如果你不能立即理解也不要担心。幸运的是，我们只需要为每种类型组合写一次，所以对于将来任何类型的树/结果组合，我们都准备好了！

```
/// Convert a tree of Results into a Result of tree
let sequenceTreeOfResult tree =
    // from the lower level
    let (<*>) = Result.apply 
    let retn = Result.retn

    // from the traversable level
    let fLeaf data = 
        retn LeafNode <*> data

    let fNode data subitems = 
        let makeNode data items = InternalNode(data,items)
        let subItems = Result.sequenceSeq subitems 
        retn makeNode <*> data <*> subItems

    // do the traverse
    Tree.cata fLeaf fNode tree

// val sequenceTreeOfResult :
//    tree:Tree<Result<'a>,Result<'b>> -> Result<Tree<'a,'b>> 
```

最后，实际的 `dtoToTree` 函数很简单 -- 只需将 `treeDto` 通过 `dtoToTreeOfResults` 发送，然后使用 `sequenceTreeOfResult` 将最终结果转换为 `Result<Tree<..>>`，这正是我们需要的。

```
let dtoToTree treeDto =
    treeDto |> dtoToTreeOfResults |> sequenceTreeOfResult 

// val dtoToTree : treeDto:TreeDto<'a,'b> -> Result<Tree<'a,'b>> 
```

### 步骤 3：将 `GiftDto` 转换为 `Gift`

再次，我们可以使用 `Tree.map` 来将 DTO 的每个叶子和内部节点转换为正确的域类型。

但是我们的函数将处理错误，所以它们需要将 `GiftContentsDto` 映射到 `Result<GiftContents>`，将 `GiftDecorationDto` 映射到 `Result<GiftDecoration>`。这将再次导致结果的 Tree，并且我们将再次使用 `sequenceTreeOfResult` 将其转换回正确的 `Result<Tree<..>>` 形状。

让我们从辅助方法（如 `strToChocolateType`）开始，将字符串转换为正确的域类型。这一次，它们返回一个 `Result` 而不是抛出异常。

```
let strToBookTitle str =
    match str with
    | null -> Result.failWithMsg "BookTitle must not be null"
    | _ -> Result.retn str

let strToChocolateType str =
    match str with
    | "Dark" -> Result.retn Dark
    | "Milk" -> Result.retn Milk
    | "SeventyPercent" -> Result.retn SeventyPercent
    | _ -> Result.failWithMsg (sprintf "ChocolateType %s not recognized" str)

let strToWrappingPaperStyle str =
    match str with
    | "HappyBirthday" -> Result.retn HappyBirthday
    | "HappyHolidays" -> Result.retn HappyHolidays
    | "SolidColor" -> Result.retn SolidColor
    | _ -> Result.failWithMsg (sprintf "WrappingPaperStyle %s not recognized" str)

let strToCardMessage str =
    match str with
    | null -> Result.failWithMsg "CardMessage must not be null" 
    | _ -> Result.retn str 
```

情况转换器方法必须从 `Result` 而不是正常值构建一个 `Book` 或 `Chocolate`。这就是提升函数如 `Result.lift2` 如何帮助的地方。有关此操作的详细信息，请参见提升文章和应用验证的文章。

```
let bookFromDto (dto:GiftContentsDto) =
    let book bookTitle price = 
        Book {title=bookTitle; price=price}

    let bookTitle = strToBookTitle dto.bookTitle
    let price = Result.retn dto.price
    Result.lift2 book bookTitle price 

let chocolateFromDto (dto:GiftContentsDto) =
    let choc chocType price = 
        Chocolate {chocType=chocType; price=price}

    let chocType = strToChocolateType dto.chocolateType 
    let price = Result.retn dto.price
    Result.lift2 choc chocType price 

let wrappedFromDto (dto:GiftDecorationDto) =
    let wrappingPaperStyle = strToWrappingPaperStyle dto.wrappingPaperStyle
    Result.map Wrapped wrappingPaperStyle 

let boxedFromDto (dto:GiftDecorationDto) =
    Result.retn Boxed

let withACardFromDto (dto:GiftDecorationDto) =
    let message = strToCardMessage dto.message
    Result.map WithACard message 
```

最后，如果 `discriminator` 无效，`dtoToGift` 函数本身也将更改为返回一个 `Result`。

与以前一样，这种映射创建了一个结果的 Tree，因此我们将 `Tree.map` 的输出通过 `sequenceTreeOfResult` 管道 ...

```
`Tree.map fLeaf fNode giftDto |> sequenceTreeOfResult` 
```

... 返回一个 Tree 的 Result。

这是 `dtoToGift` 的完整代码：

```
open TreeDto_WithErrorHandling

/// Transform a GiftDto to a Result<Gift>
let dtoToGift (giftDto:GiftDto) :Result<Gift>=

    let fLeaf (leafDto:GiftContentsDto) = 
        match leafDto.discriminator with
        | "Book" -> bookFromDto leafDto
        | "Chocolate" -> chocolateFromDto leafDto
        | _ -> Result.failWithMsg (sprintf "Unknown leaf discriminator '%s'" leafDto.discriminator) 

    let fNode (nodeDto:GiftDecorationDto)  = 
        match nodeDto.discriminator with
        | "Wrapped" -> wrappedFromDto nodeDto
        | "Boxed" -> boxedFromDto nodeDto
        | "WithACard" -> withACardFromDto nodeDto
        | _ -> Result.failWithMsg (sprintf "Unknown node discriminator '%s'" nodeDto.discriminator)

    // map the tree
    Tree.map fLeaf fNode giftDto |> sequenceTreeOfResult 
```

`dtoToGift` 的类型签名已更改 -- 现在它返回一个 `Result<Gift>` 而不仅仅是一个 `Gift`。

```
// val dtoToGift : GiftDto -> Result<GiftUsingTree.Gift> 
```

### 步骤 4：组装管道

现在我们可以重新组合管道，以将 JSON 字符串转换为一个 `Gift`。

但是需要对新的错误处理代码进行更改：

+   `fromJson` 函数返回一个 `Result<TreeDto>`，但管道中的下一个函数（`dtoToTree`）期望一个常规的 `TreeDto` 作为输入。

+   同样，`dtoToTree` 返回一个 `Result<Tree>`，但管道中的下一个函数（`dtoToGift`）期望一个常规的 `Tree` 作为输入。

在这两种情况下，`Result.bind` 可以用来解决输出/输入不匹配的问题。有关更详细的 bind 讨论，请参见这里。

好的，让我们尝试反序列化我们之前创建的`goodJson`字符串。

```
let goodGift = goodJson |> fromJson |> Result.bind dtoToTree |> Result.bind dtoToGift

// check that the description is unchanged
goodGift |> description
// Success "SeventyPercent chocolate in a box wrapped in HappyHolidays paper" 
```

没问题。

看看现在错误处理是否改善了。我们再次破坏 JSON：

```
let badJson1 = goodJson.Replace("leafData","leafDataXX")

let badJson1_result = badJson1 |> fromJson |> Result.bind dtoToTree |> Result.bind dtoToGift
// Failure ["The data contract type 'TreeDto' cannot be deserialized because the required data member 'leafData@' was not found."] 
```

不错！我们得到了一个很好的`Failure`案例。

或者如果鉴别器错了呢？

```
let badJson2 = goodJson.Replace("Wrapped","Wrapped2")
let badJson2_result = badJson2 |> fromJson |> Result.bind dtoToTree |> Result.bind dtoToGift
// Failure ["Unknown node discriminator 'Wrapped2'"] 
```

或 WrappingPaperStyle DU 的值之一？

```
let badJson3 = goodJson.Replace("HappyHolidays","HappyHolidays2")
let badJson3_result = badJson3 |> fromJson |> Result.bind dtoToTree |> Result.bind dtoToGift
// Failure ["WrappingPaperStyle HappyHolidays2 not recognized"] 
```

再次出现了很好的`Failure`案例。

非常好的一点是（这是异常处理方法无法提供的），如果有多个错误，各种错误可以被聚合，这样我们就可以得到一个列出了*所有*出错原因的列表，而不仅仅是一次一个错误。

通过向 JSON 字符串引入两个错误，让我们看看它的实际效果：

```
// create two errors
let badJson4 = goodJson.Replace("HappyHolidays","HappyHolidays2")
                       .Replace("SeventyPercent","SeventyPercent2")
let badJson4_result = badJson4 |> fromJson |> Result.bind dtoToTree |> Result.bind dtoToGift
// Failure ["WrappingPaperStyle HappyHolidays2 not recognized"; 
//          "ChocolateType SeventyPercent2 not recognized"] 
```

总的来说，我认为这是一个成功！

*这个示例的源代码可以在[这个 gist](https://gist.github.com/swlaschin/2b06fe266e3299a656c1)找到。*

* * *

## 总结

在这个系列中，我们已经看到了如何定义 catamorphisms（折叠），以及特别是在这篇文章中，如何使用它们来解决实际问题。我希望这些文章对你有用，并为你提供了一些可以应用到自己代码中的提示和见解。

这个系列的长度超出了我的预期，所以感谢您一直坚持看到最后！干杯！
