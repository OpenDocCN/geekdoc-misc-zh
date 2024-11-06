# 属性基本测试简介

# 属性基本测试简介

> 这篇文章是[F# Advent Calendar in English 2014](https://sergeytihon.wordpress.com/2014/11/24/f-advent-calendar-in-english-2014/)项目的一部分。去那里查看所有其他精彩的帖子！特别感谢 Sergey Tihon 组织这个项目。

*更新：我根据这些帖子做了一个关于属性基本测试的演讲。[幻灯片和视频在这里。](http://fsharpforfunandprofit.com/pbt/)

让我们从一个我希望永远不要发生的讨论开始：

```
Me to co-worker: "We need a function that will add two numbers together, would you mind implementing it?" 
(a short time later) 
Co-worker: "I just finished implementing the 'add' function" 
Me: "Great, have you written unit tests for it?" 
Co-worker: "You want tests as well?" (rolls eyes) "Ok." 
(a short time later) 
Co-worker: "I just wrote a test. Look! 'Given 1 + 2, I expect output is 3'. " 
Co-worker: "So can we call it done now?" 
Me: "Well that's only *one* test. How do you know that it doesn't fail for other inputs?" 
Co-worker: "Ok, let me do another one." 
(a short time later) 
Co-worker: "I just wrote a another awesome test. 'Given 2 + 2, I expect output is 4'" 
Me: "Yes, but you're still only testing for special cases. How do you know that it doesn't fail for other inputs you haven't thought of?" 
Co-worker: "You want even *more* tests?"
(mutters "slavedriver" under breath and walks away) 
```

但是说真的，我的想象中的同事的抱怨有些合理：**多少测试才够？**

所以现在想象一下，你不是一名开发人员，而是一名负责测试“add”函数是否正确实现的测试工程师。

不幸的是，该实现是由一位疲惫不堪、总是懒惰而且经常恶意的程序员编写的，我将其称为*地狱企业开发者*，简称“EDFH”。（EDFH 有一个[你可能听说过的表兄弟](https://en.wikipedia.org/wiki/Bastard_Operator_From_Hell)）。

你正在练习企业级的测试驱动开发，这意味着你编写一个测试，然后 EDFH 实现通过测试的代码。

所以你从一个像这样的测试开始（使用原始的 NUnit 风格）：

```
[<Test>]
let ``When I add 1 + 2, I expect 3``()=
    let result = add 1 2
    Assert.AreEqual(3,result) 
```

然后，EDFH 像这样实现`add`函数：

```
let add x y =
    if x=1 && y=2 then 
        3
    else
        0 
```

你的测试通过了！

当你向 EDFH 抱怨时，他们说他们正在正确地进行 TDD，只[编写最小的代码来使测试通过](http://www.typemock.com/test-driven-development-tdd/)。

说得有道理。所以你又写了一个测试：

```
[<Test>]
let ``When I add 2 + 2, I expect 4``()=
    let result = add 2 2
    Assert.AreEqual(4,result) 
```

然后，EDFH 将`add`函数的实现更改为这样：

```
let add x y =
    if x=1 && y=2 then 
        3
    else if x=2 && y=2 then 
        4
    else
        0 
```

当你再次向 EDFH 抱怨时，他们指出这种方法实际上是最佳实践。显然，这被称为["变换优先原则"](http://blog.8thlight.com/uncle-bob/2013/05/27/TheTransformationPriorityPremise.html)。

在这一点上，你开始认为 EDFH 是恶意的，这种来回可能会永远持续下去！

## 打败恶意程序员

那么问题是，你可以写什么样的测试，以至于一个恶意的程序员即使想要也无法创建一个不正确的实现？

嗯，你可以从一个更大的已知结果列表开始，然后再稍微混合一下。

```
[<Test>]
let ``When I add two numbers, I expect to get their sum``()=
    for (x,y,expected) in [ (1,2,3); (2,2,4); (3,5,8); (27,15,42); ]
        let actual = add x y
        Assert.AreEqual(expected,actual) 
```

但是 EDFH 是不知疲倦的，将更新实现以包括所有这些情况。

一个更好的方法是生成随机数并将其用于输入，以便恶意程序员无法提前知道该怎么做。

```
let rand = System.Random()
let randInt() = rand.Next()

[<Test>]
let ``When I add two random numbers, I expect their sum``()=
    let x = randInt()
    let y = randInt()
    let expected = x + y
    let actual = add x y
    Assert.AreEqual(expected,actual) 
```

如果测试看起来像这样，那么 EDFH 将被*迫*正确实现`add`函数！

最后一个改进--EDFH 可能只是走运，选出的数字碰巧有效，所以让我们重复随机数测试多次，比如说 100 次。

```
[<Test>]
let ``When I add two random numbers (100 times), I expect their sum``()=
    for _ in [1..100] do
        let x = randInt()
        let y = randInt()
        let expected = x + y
        let actual = add x y
        Assert.AreEqual(expected,actual) 
```

所以现在我们完成了！

或者我们？

## 属性基本测试

只有一个问题。为了测试`add`函数，你正在使用`+`函数。换句话说，你正在使用一个实现来测试另一个实现。

在某些情况下这是可以接受的（请参见后面一篇文章中“测试预言”的用法），但一般来说，让你的测试重复你正在测试的代码是一个坏主意！这是浪费时间和精力，现在你有两个实现要构建和维护。

如果你不能通过使用`+`来测试，那么*如何*测试呢？

答案是创建专注于函数的*属性*--“要求”的测试。这些属性应该是*任何*正确实现都为真的事情。

那么让我们思考一下`add`函数的属性是什么。

开始的一种方法是思考`add`与其他类似函数的不同之处。

例如，`add`和`subtract`之间有什么区别？对于`subtract`，参数的顺序很重要，而对于`add`则不是。

所以这是一个很好的起点属性。它不依赖于加法本身，但它消除了一整类不正确的实现。

```
[<Test>]
let ``When I add two numbers, the result should not depend on parameter order``()=
    for _ in [1..100] do
        let x = randInt()
        let y = randInt()
        let result1 = add x y
        let result2 = add y x // reversed params
        Assert.AreEqual(result1,result2) 
```

这是一个很好的开始，但这并不能阻止 EDFH。EDFH 仍然可以使用`x * y`来实现`add`，而这个测试会通过！

那么现在`add`和`multiply`之间的区别是什么？加法真正意味着什么？

我们可以从类似这样的测试开始，即`x + x`应该等于`x * 2`：

```
let result1 = add x x   
let result2 = x * 2     
Assert.AreEqual(result1,result2) 
```

但现在我们假设了乘法的存在！我们能定义一个*仅*依赖于`add`本身的属性吗？

一个非常有用的方法是看看当函数重复多次时会发生什么。也就是说，如果你先`add`然后再对结果进行`add`会怎样？

这导致了两个`add 1`等于一个`add 2`的想法。这是测试：

```
[<Test>]
let ``Adding 1 twice is the same as adding 2``()=
    for _ in [1..100] do
        let x = randInt()
        let y = randInt()
        let result1 = x |> add 1 |> add 1
        let result2 = x |> add 2 
        Assert.AreEqual(result1,result2) 
```

太棒了！`add`与这个测试完美配合，而`multiply`则不行。

但是，请注意，EDFH 仍然可以使用`y - x`来实现`add`，而这个测试会通过！

幸运的是，我们上面还有“参数顺序”测试。因此这两个测试的结合应该将其缩小到只有一个正确的实现，对吧？

提交了这个测试套件后，我们发现 EDFH 编写了一个通过这两个测试的实现。让我们看看：

```
let add x y = 0  // malicious implementation 
```

啊啊啊！发生了什么？我们的方法错在哪里了？

哦，我们忘记了强制实现实际使用我们生成的随机数！

因此，我们需要确保实现确实*使用*传递给它的参数。我们将不得不检查结果与输入以特定方式相关联。

我们是否知道`add`的一个微不足道的特性，而无需重新实现我们自己的版本就能得到答案？

是的！

当你将零加到一个数字时会发生什么？你总是得到相同的数字。

```
[<Test>]
let ``Adding zero is the same as doing nothing``()=
    for _ in [1..100] do
        let x = randInt()
        let result1 = x |> add 0
        let result2 = x  
        Assert.AreEqual(result1,result2) 
```

现在我们有一组属性，可以用来测试`add`的任何实现，并强制 EDFH 创建一个正确的实现：

## 重构通用代码

在这三个测试中有相当多的重复代码。让我们做些重构。

首先，我们将编写一个名为`propertyCheck`的函数，该函数将生成 100 对随机整数。

`propertyCheck`还将需要一个用于属性本身的参数。这将是一个接受两个整数并返回布尔值的函数：

```
let propertyCheck property = 
    // property has type: int -> int -> bool
    for _ in [1..100] do
        let x = randInt()
        let y = randInt()
        let result = property x y
        Assert.IsTrue(result) 
```

有了这个基础，我们可以通过将属性提取到一个单独的函数中来重新定义一个测试，就像这样：

```
let commutativeProperty x y = 
    let result1 = add x y
    let result2 = add y x // reversed params
    result1 = result2

[<Test>]
let ``When I add two numbers, the result should not depend on parameter order``()=
    propertyCheck commutativeProperty 
```

我们也可以对其他两个属性做同样的事情。

重构之后，完整的代码如下所示：

```
let rand = System.Random()
let randInt() = rand.Next()

let add x y = x + y  // correct implementation

let propertyCheck property = 
    // property has type: int -> int -> bool
    for _ in [1..100] do
        let x = randInt()
        let y = randInt()
        let result = property x y
        Assert.IsTrue(result)

let commutativeProperty x y = 
    let result1 = add x y
    let result2 = add y x // reversed params
    result1 = result2

[<Test>]
let ``When I add two numbers, the result should not depend on parameter order``()=
    propertyCheck commutativeProperty 

let adding1TwiceIsAdding2OnceProperty x _ = 
    let result1 = x |> add 1 |> add 1
    let result2 = x |> add 2 
    result1 = result2

[<Test>]
let ``Adding 1 twice is the same as adding 2``()=
    propertyCheck adding1TwiceIsAdding2OnceProperty 

let identityProperty x _ = 
    let result1 = x |> add 0
    result1 = x

[<Test>]
let ``Adding zero is the same as doing nothing``()=
    propertyCheck identityProperty 
```

## 回顾我们到目前为止所做的工作

我们已经定义了任何`add`实现都应满足的一组属性：

+   参数顺序无关紧要（“交换性”属性）

+   用 1 两次进行`add`与一次用 2 进行`add`是相同的

+   加零什么也不做（“单位元”属性）

这些属性的好处在于它们适用于*所有*输入，而不仅仅是特殊的魔法数字。但更重要的是，它们向我们展示了加法的核心本质。

实际上，你可以将这种方法推到逻辑的极致，实际上*定义*加法为具有这些属性的任何东西。

这正是数学家所做的。如果你查阅 [维基百科上的加法](https://en.wikipedia.org/wiki/Addition#Properties)，你会看到它完全是根据可交换性、结合性、单位元等来定义的。

请注意，在我们的实验中，我们错过了定义“结合性”，而是创建了一个更弱的属性（`x+1+1 = x+2`）。我们稍后将看到，EDFH 确实可以编写一个满足此属性的恶意实现，并且结合性更好。

遗憾的是，第一次尝试很难完美地得到属性，但即使如此，通过使用我们提出的三个属性，我们对实现的正确性有了更高的信心，实际上，我们也学到了一些东西——我们更深入地理解了要求。

## 属性规范

这样的一组属性可以被视为*规范*。

从历史上看，单元测试除了是功能测试外，还被 [用作一种规范的一种方式](https://en.wikipedia.org/wiki/Unit_testing#Documentation)。但是，使用属性而不是带有“魔法”数据的测试的规范方法是一种我认为通常更短且更少歧义的替代方法。

你可能会认为只有数学类型的函数才能以这种方式进行规范，但在未来的文章中，我们将看到这种方法如何用于测试 Web 服务和数据库。

当然，并非每个业务需求都可以像这样表示为属性，我们也不应忽视软件开发的社交组成部分。[例如规范](https://en.wikipedia.org/wiki/Specification_by_example)和领域驱动设计在与非技术客户合作时可以发挥重要作用。

您可能也在考虑设计所有这些属性是很多工作--您是对的！这是最困难的部分。在���续帖子中，我将提供一些有助于减少工作量的属性设计提示。

即使在前期涉及额外的努力（这种活动的技术术语叫做“思考问题”）后，通过拥有自动化测试和明确的规范来节省的整体时间将远远超过后期的前期成本。

实际上，用来宣传单元测试好处的论点同样适用于基于属性的测试！因此，如果一个 TDD 粉丝告诉你他们没有时间想出基于属性的测试，那么他们可能没有看到全局。

## 引入 QuickCheck 和 FsCheck

我们已经实现了自己的属性检查系统，但存在一些问题：

+   它只适用于整数函数。如果我们可以对具有字符串参数的函数或实际上任何类型的参数（包括我们自己定义的参数）使用相同的方法就好了。

+   它只适用于具有两个参数的函数（我们不得不忽略其中一个参数对于`adding1TwiceIsAdding2OnceProperty`和`identity`属性）。如果我们可以对具有任意数量参数的函数使用相同的方法就好了。

+   当属性存在反例时，我们不知道是什么！当测试失败时并不是很有帮助！

+   我们生成的随机数没有记录，也没有设置种子的方法，这意味着我们无法轻松调试和重现错误。

+   它不可配置。例如，我们不能轻松地将循环次数从 100 更改为其他值。

如果有一个框架可以为我们做所有这些就好了！

幸运的是有的！["QuickCheck"](https://en.wikipedia.org/wiki/QuickCheck)库最初是由 Koen Claessen 和 John Hughes 为 Haskell 开发的，并已移植到许多其他语言。

在 F#（以及 C#）中使用的 QuickCheck 版本是由 Kurt Schelfthout 创建的优秀的["FsCheck"](https://fsharp.github.io/FsCheck/)库。虽然基于 Haskell QuickCheck，但它具有一些不错的附加功能，包括与 NUnit 和 xUnit 等测试框架的集成。

让我们看看 FsCheck 如何执行与我们自制的属性测试系统相同的操作。

## 使用 FsCheck 测试加法属性

首先，您需要安装 FsCheck 并加载 DLL（FsCheck 可能有点挑剔--请参阅本页底部的说明和故障排除）。

您的脚本文件顶部应该看起来像这样：

```
System.IO.Directory.SetCurrentDirectory (__SOURCE_DIRECTORY__)
#I @"Packages\FsCheck.1.0.3\lib\net45"
//#I @"Packages\FsCheck.0.9.2.0\lib\net40-Client"  // use older version for VS2012
#I @"Packages\NUnit.2.6.3\lib"
#r @"FsCheck.dll"
#r @"nunit.framework.dll"

open System
open FsCheck
open NUnit.Framework 
```

一旦加载了 FsCheck，你可以使用`Check.Quick`并传入任何“属性”函数。暂时来说，让我们说“属性”函数是任何返回布尔值的函数（带有任何参数）。

```
let add x y = x + y  // correct implementation

let commutativeProperty (x,y) = 
    let result1 = add x y
    let result2 = add y x // reversed params
    result1 = result2

// check the property interactively 
Check.Quick commutativeProperty 

let adding1TwiceIsAdding2OnceProperty x = 
    let result1 = x |> add 1 |> add 1
    let result2 = x |> add 2 
    result1 = result2

// check the property interactively 
Check.Quick adding1TwiceIsAdding2OnceProperty 

let identityProperty x = 
    let result1 = x |> add 0
    result1 = x

// check the property interactively 
Check.Quick identityProperty 
```

如果你交互式地检查其中一个属性，比如使用`Check.Quick commutativeProperty`，你会看到消息：

```
Ok, passed 100 tests. 
```

## 使用 FsCheck 找到不满足的属性

让我们看看当我们有一个恶意实现的`add`时会发生什么。在下面的代码中，EDFH 将`add`实现为乘法！

那个实现*将*满足交换性质，但`adding1TwiceIsAdding2OnceProperty`呢？

```
let add x y =
    x * y // malicious implementation

let adding1TwiceIsAdding2OnceProperty x = 
    let result1 = x |> add 1 |> add 1
    let result2 = x |> add 2 
    result1 = result2

// check the property interactively 
Check.Quick adding1TwiceIsAdding2OnceProperty 
```

来自 FsCheck 的结果是：

```
Falsifiable, after 1 test (1 shrink) (StdGen (1657127138,295941511)):
1 
```

这意味着将`1`作为`adding1TwiceIsAdding2OnceProperty`的输入将导致`false`，你可以很容易地看到它确实是这样的。

## 恶意 EDFH 的返回

��过使用随机测试，我们让恶意实现者变得更难。他们现在必须改变策略了！

EDFH 注意到我们在`adding1TwiceIsAdding2OnceProperty`中仍在使用一些魔法数字 -- 即 1 和 2，并决定创建一个利用这一点的实现。他们将为低输入值使用正确的实现，而对于高输入值则使用不正确的实现：

```
let add x y = 
    if (x < 10) || (y < 10) then
        x + y  // correct for low values
    else
        x * y  // incorrect for high values 
```

哦不！如果我们重新测试所有的属性，它们现在都通过了！

这将教会我们在测试中不要使用魔法数字！

替代方案是什么？嗯，让我们从数学家那里借鉴，创建一个关联属性测试。

```
let associativeProperty x y z = 
    let result1 = add x (add y z)    // x + (y + z)
    let result2 = add (add x y) z    // (x + y) + z
    result1 = result2

// check the property interactively 
Check.Quick associativeProperty 
```

啊哈！现在我们得到了一个证伪：

```
Falsifiable, after 38 tests (4 shrinks) (StdGen (127898154,295941554)):
8
2
10 
```

这意味着使用`(8+2)+10`不等于`8+(2+10)`。

请注意，FsCheck 不仅找到了一些破坏属性的输入，而且找到了一个最小的例子。它知道输入`8,2,9`是通过的，但再增加一个（`8,2,10`）就失败了。这非常好！

## 理解 FsCheck：生成器

现在我们已经真正使用了 FsCheck，让我们暂停一下，看看它是如何工作的。

FsCheck 首先为你生成随机输入。这称为“生成”，对于每种类型，都有一个关联的生成器。

例如，要生成一个样本数据列表，你使用生成器以及两个参数：列表中的元素数量和一个“大小”。 “大小”的确切含义取决于正在生成的类型和上下文。 “大小”用于的示例包括：int 的最大值；列表的长度；树的深度；等等。

这里有一些生成整数的代码：

```
// get the generator for ints
let intGenerator = Arb.generate<int>

// generate three ints with a maximum size of 1
Gen.sample 1 3 intGenerator    // e.g. [0; 0; -1]

// generate three ints with a maximum size of 10
Gen.sample 10 3 intGenerator   // e.g. [-4; 8; 5]

// generate three ints with a maximum size of 100
Gen.sample 100 3 intGenerator  // e.g. [-37; 24; -62] 
```

在这个例子中，整数并不是均匀生成的，而是聚集在零附近。你可以用一点代码自己看到这一点：

```
// see how the values are clustered around the center point
intGenerator 
|> Gen.sample 10 1000 
|> Seq.groupBy id 
|> Seq.map (fun (k,v) -> (k,Seq.length v))
|> Seq.sortBy (fun (k,v) -> k)
|> Seq.toList 
```

结果类似于这样：

```
[(-10, 3); (-9, 14); (-8, 18); (-7, 10); (-6, 27); (-5, 42); (-4, 49);
   (-3, 56); (-2, 76); (-1, 119); (0, 181); (1, 104); (2, 77); (3, 62);
   (4, 47); (5, 44); (6, 26); (7, 16); (8, 14); (9, 12); (10, 3)] 
```

你可以看到大多数值都在中心（0 生成了 181 次，1 生成了 104 次），而边缘值很少（10 只生成了 3 次）。

你也可以使用更大的样本重复。这个例子在范围[-30,30]内生成了 10000 个元素

```
intGenerator 
|> Gen.sample 30 10000 
|> Seq.groupBy id 
|> Seq.map (fun (k,v) -> (k,Seq.length v))
|> Seq.sortBy (fun (k,v) -> k)
|> Seq.toList 
```

还有许多其他的生成器函数可用，以及`Gen.sample`（更多文档请参见[这里](https://fsharp.github.io/FsCheck/TestData.html)）。

## 理解 FsCheck：自动生成各种类型

生成器逻辑的精妙之处在于它还会自动生成复合值。

例如，这里是一个包含三个整数的元组的生成器：

```
let tupleGenerator = Arb.generate<int*int*int>

// generate 3 tuples with a maximum size of 1
Gen.sample 1 3 tupleGenerator 
// result: [(0, 0, 0); (0, 0, 0); (0, 1, -1)]

// generate 3 tuples with a maximum size of 10
Gen.sample 10 3 tupleGenerator 
// result: [(-6, -4, 1); (2, -2, 8); (1, -4, 5)]

// generate 3 tuples with a maximum size of 100
Gen.sample 100 3 tupleGenerator 
// result: [(-2, -36, -51); (-5, 33, 29); (13, 22, -16)] 
```

一旦你有了基本类型的生成器，`option`和`list`的生成器就会跟随。这里是一个`int option`的生成器：

```
let intOptionGenerator = Arb.generate<int option>
// generate 10 int options with a maximum size of 5
Gen.sample 5 10 intOptionGenerator 
// result:  [Some 0; Some -1; Some 2; Some 0; Some 0; 
//           Some -4; null; Some 2; Some -2; Some 0] 
```

这里是一个`int list`的生成器：

```
let intListGenerator = Arb.generate<int list>
// generate 10 int lists with a maximum size of 5
Gen.sample 5 10 intListGenerator 
// result:  [ []; []; [-4]; [0; 3; -1; 2]; [1]; 
//            [1]; []; [0; 1; -2]; []; [-1; -2]] 
```

当然你也可以生成随机字符串！

```
let stringGenerator = Arb.generate<string>

// generate 3 strings with a maximum size of 1
Gen.sample 1 3 stringGenerator 
// result: [""; "!"; "I"]

// generate 3 strings with a maximum size of 10
Gen.sample 10 3 stringGenerator 
// result: [""; "eiX$a^"; "U%0Ika&r"] 
```

最棒的是，生成器也适用于你自己定义的用户类型！

```
type Color = Red | Green of int | Blue of bool

let colorGenerator = Arb.generate<Color>

// generate 10 colors with a maximum size of 50
Gen.sample 50 10 colorGenerator 

// result:  [Green -47; Red; Red; Red; Blue true; 
//           Green 2; Blue false; Red; Blue true; Green -12] 
```

这里有一个生成包含另一个用户定义类型的用户定义记录类型的生成器。

```
type Point = {x:int; y:int; color: Color}

let pointGenerator = Arb.generate<Point>

// generate 10 points with a maximum size of 50
Gen.sample 50 10 pointGenerator 

(* result
[{x = -8; y = 12; color = Green -4;}; 
 {x = 28; y = -31; color = Green -6;}; 
 {x = 11; y = 27; color = Red;}; 
 {x = -2; y = -13; color = Red;};
 {x = 6; y = 12; color = Red;};
 // etc
*) 
```

有方法可以更精细地控制你的类型是如何生成的，但这将等待另一篇文章！

## 理解 FsCheck：收缩

创建最小的反例是 QuickCheck 风格测试的一大亮点。

它是如何做到这一点的？

FsCheck 使用的过程有两个部分：

首先它生成一系列随机输入，从小到大。这是上面描述的“生成器”阶段。

如果任何输入导致属性失败，它会开始“收缩”第一个参数以找到一个更小的数字。收缩的确切过程取决于类型（你也可以覆盖它），但让我们说对于数字来说，它们以一种明智的方式变小。

例如，假设你有一个愚蠢的属性`isSmallerThan80`：

```
let isSmallerThan80 x = x < 80 
```

你已经生成了随机数，并发现属性对`100`失败了，你想尝试一个更小的数字。`Arb.shrink`将生成一系列小于 100 的整数。每一个都会依次用于属性，直到属性再次失败。

```
isSmallerThan80 100 // false, so start shrinking

Arb.shrink 100 |> Seq.toList 
//  [0; 50; 75; 88; 94; 97; 99] 
```

对列表中的每个元素，对其进行属性测试，直到找到另一个失败：

```
isSmallerThan80 0 // true
isSmallerThan80 50 // true
isSmallerThan80 75 // true
isSmallerThan80 88 // false, so shrink again 
```

属性在`88`失败了，所以再次从那里开始收缩：

```
Arb.shrink 88 |> Seq.toList 
//  [0; 44; 66; 77; 83; 86; 87]
isSmallerThan80 0 // true
isSmallerThan80 44 // true
isSmallerThan80 66 // true
isSmallerThan80 77 // true
isSmallerThan80 83 // false, so shrink again 
```

属性现在在`83`失败了，所以再次从那里开始收缩： 

```
Arb.shrink 83 |> Seq.toList 
//  [0; 42; 63; 73; 78; 81; 82]
// smallest failure is 81, so shrink again 
```

属性在`81`失败了，所以再次从那里开始收缩：

```
Arb.shrink 81 |> Seq.toList 
//  [0; 41; 61; 71; 76; 79; 80]
// smallest failure is 80 
```

在这一点之后，对 80 的收缩不起作用 -- 不会找到更小的值。

在这种情况下，FsCheck 将报告`80`使属性失效，并且需要 4 次收缩。

就像生成器一样，FsCheck 几乎可以为任何类型生成收缩序列：

```
Arb.shrink (1,2,3) |> Seq.toList 
//  [(0, 2, 3); (1, 0, 3); (1, 1, 3); (1, 2, 0); (1, 2, 2)]

Arb.shrink "abcd" |> Seq.toList 
//  ["bcd"; "acd"; "abd"; "abc"; "abca"; "abcb"; "abcc"; "abad"; "abbd"; "aacd"]

Arb.shrink [1;2;3] |> Seq.toList 
//  [[2; 3]; [1; 3]; [1; 2]; [1; 2; 0]; [1; 2; 2]; [1; 0; 3]; [1; 1; 3]; [0; 2; 3]] 
```

与生成器一样，如果需要，有方法可以自定义收缩的工作方式。

## 配置 FsCheck：更改测试次数

我提到了一个愚蠢的属性`isSmallerThan80` -- 让我们看看 FsCheck 如何处理它。

```
// silly property to test
let isSmallerThan80 x = x < 80

Check.Quick isSmallerThan80 
// result: Ok, passed 100 tests. 
```

哦，糟糕！FsCheck 没有找到反例！

在这一点上，我们可以尝试一些事情。首先，我们可以尝试增加测试次数。

我们通过更改默认（“Quick”）配置来实现这一点。有一个称为`MaxTest`的字段，我们可以设置它。默认值为 100，所以让我们将其增加到 1000。

最后，要使用特定配置，你需要使用`Check.One(config,property)`而不仅仅是`Check.Quick(property)`。

```
let config = {
    Config.Quick with 
        MaxTest = 1000
    }
Check.One(config,isSmallerThan80 )
// result: Ok, passed 1000 tests. 
```

哎呀！FsCheck 也没有在 1000 次测试中找到反例！让我们再试一次，进行 10000 次测试：

```
let config = {
    Config.Quick with 
        MaxTest = 10000
    }
Check.One(config,isSmallerThan80 )
// result: Falsifiable, after 8660 tests (1 shrink) (StdGen (539845487,295941658)):
//         80 
```

好的，最终我们让它工作了。但为什么需要这么多测试？

答案在其他一些配置设置中：`StartSize` 和 `EndSize`。

请记住，生成器从小数字开始逐渐增加。这由`StartSize`和`EndSize`设置控制。默认情况下，`StartSize`为 1，`EndSize`为 100。因此，在测试结束时，生成器的“大小”参数将为 100。

但是，正如我们所看到的，即使大小为 100，极端情况下也很少生成数字。在这种情况下，这意味着大于 80 的数字不太可能被生成。

那么让我们将`EndSize`更改为更大的值，看看会发生什么！

```
let config = {
    Config.Quick with 
        EndSize = 1000
    }
Check.One(config,isSmallerThan80 )
// result: Falsifiable, after 21 tests (4 shrinks) (StdGen (1033193705,295941658)):
//         80 
```

就像这样！现在只需要 21 次测试，而不是 8660 次测试！

## 配置 FsCheck：详细模式和日志记录

我提到 FsCheck 相对于自制解决方案的一个好处是日志记录和可重现性，让我们来看看。

我们将调整恶意实现的边界为`25`。让我们看看 FsCheck 如何通过日志检测到这个边界。

```
let add x y = 
    if (x < 25) || (y < 25) then
        x + y  // correct for low values
    else
        x * y  // incorrect for high values

let associativeProperty x y z = 
    let result1 = add x (add y z)    // x + (y + z)
    let result2 = add (add x y) z    // (x + y) + z
    result1 = result2

// check the property interactively 
Check.Quick associativeProperty 
```

结果是：

```
Falsifiable, after 66 tests (12 shrinks) (StdGen (1706196961,295941556)):
1
24
25 
```

再次，FsCheck 很快发现`25`是确切的边界点。但它是如何做到的呢？

首先，查看 FsCheck 的操作最简单的方法是使用“verbose”模式。也就是说，使用`Check.Verbose`而不是`Check.Quick`：

```
// check the property interactively 
Check.Quick associativeProperty 

// with tracing/logging
Check.Verbose associativeProperty 
```

这样做时，你将看到如下所示的输出。我已添加了所有注释以解释各个元素。

```
0:    // test 1
-1    // param 1
-1    // param 2 
0     // param 3 
      // associativeProperty -1 -1 0  => true, keep going
1:    // test 2
0
0
0     // associativeProperty 0 0 0  => true, keep going
2:    // test 3
-2
0
-3    // associativeProperty -2 0 -3  => true, keep going
3:    // test 4
1
2
0     // associativeProperty 1 2 0  => true, keep going
// etc
49:   // test 50
46
-4
50    // associativeProperty 46 -4 50  => false, start shrinking
// etc
shrink:
35
-4
50    // associativeProperty 35 -4 50  => false, keep shrinking
shrink:
27
-4
50    // associativeProperty 27 -4 50  => false, keep shrinking
// etc
shrink:
25
1
29    // associativeProperty 25 1 29  => false, keep shrinking
shrink:
25
1
26    // associativeProperty 25 1 26  => false, keep shrinking
// next shrink fails
Falsifiable, after 50 tests (10 shrinks) (StdGen (995282583,295941602)):
25
1
26 
```

这个显示占用了很多空间！我们能让它更加紧凑吗？

是的 -- 你可以通过编写自定义函数来控制每个测试和收缩的显示方式，并通过其`Config`结构告诉 FsCheck 使用它们。

这些函数是通用的，参数列表由一个未知长度的列表（`obj list`）表示。但由于我知道我正在测试一个三参数属性，我可以硬编码一个三元素列表参数，并将它们都打印在一行上。

配置还有一个名为`Replay`的槽，通常为`None`，这意味着每次运行都会不同。

如果将`Replay`设置为`Some seed`，则测试将以完全相同的方式重播。种子看起来像`StdGen (someInt,someInt)`，并在每次运行时打印，因此如果要保留运行，只需将该种子粘贴到配置中即可。

再次，要使用特定配置，你需要使用`Check.One(config,property)`而不仅仅是`Check.Quick(property)`。

这是代码，其中默认的跟踪函数已更改，并且回放种子已明确设置。

```
// create a function for displaying a test
let printTest testNum [x;y;z] = 
    sprintf "#%-3i %3O %3O %3O\n" testNum x y z

// create a function for displaying a shrink
let printShrink [x;y;z] = 
    sprintf "shrink %3O %3O %3O\n" x y z

// create a new FsCheck configuration
let config = {
    Config.Quick with 
        Replay = Random.StdGen (995282583,295941602) |> Some 
        Every = printTest 
        EveryShrink = printShrink
    }

// check the given property with the new configuration
Check.One(config,associativeProperty) 
```

现在输出更加紧凑，看起来像这样：

```
#0    -1  -1   0
#1     0   0   0
#2    -2   0  -3
#3     1   2   0
#4    -4   2  -3
#5     3   0  -3
#6    -1  -1  -1
// etc
#46  -21 -25  29
#47  -10  -7 -13
#48   -4 -19  23
#49   46  -4  50
// start shrinking first parameter
shrink  35  -4  50
shrink  27  -4  50
shrink  26  -4  50
shrink  25  -4  50
// start shrinking second parameter
shrink  25   4  50
shrink  25   2  50
shrink  25   1  50
// start shrinking third parameter
shrink  25   1  38
shrink  25   1  29
shrink  25   1  26
Falsifiable, after 50 tests (10 shrinks) (StdGen (995282583,295941602)):
25
1
26 
```

所以，如果需要，定制 FsCheck 日志是相当容易的。

让我们详细看看如何进行收缩。最后一组输入（46，-4，50）是错误的，因此开始收缩。

```
// The last set of inputs (46,-4,50) was false, so shrinking started
associativeProperty 46 -4 50  // false, so shrink

// list of possible shrinks starting at 46
Arb.shrink 46 |> Seq.toList 
// result [0; 23; 35; 41; 44; 45] 
```

我们将循环遍历列表`[0; 23; 35; 41; 44; 45]`，在导致属性失败的第一个元素处停止：

```
// find the next test that fails when shrinking the x parameter 
let x,y,z = (46,-4,50) 
Arb.shrink x
|> Seq.tryPick (fun x -> if associativeProperty x y z then None else Some (x,y,z) )
// answer (35, -4, 50) 
```

导致失败的第一个元素是`x=35`，作为输入`(35, -4, 50)`的一部分。

现在我们从 35 开始缩小：

```
// find the next test that fails when shrinking the x parameter 
let x,y,z = (35,-4,50) 
Arb.shrink x
|> Seq.tryPick (fun x -> if associativeProperty x y z then None else Some (x,y,z) )
// answer (27, -4, 50) 
```

导致失败的第一个元素现在是`x=27`，作为输入`(27, -4, 50)`的一部分。

现在我们从 27 开始继续：

```
// find the next test that fails when shrinking the x parameter 
let x,y,z = (27,-4,50) 
Arb.shrink x
|> Seq.tryPick (fun x -> if associativeProperty x y z then None else Some (x,y,z) )
// answer (26, -4, 50)

// find the next test that fails when shrinking the x parameter 
let x,y,z = (26,-4,50) 
Arb.shrink x
|> Seq.tryPick (fun x -> if associativeProperty x y z then None else Some (x,y,z) )
// answer (25, -4, 50)

// find the next test that fails when shrinking the x parameter 
let x,y,z = (25,-4,50) 
Arb.shrink x
|> Seq.tryPick (fun x -> if associativeProperty x y z then None else Some (x,y,z) )
// answer None 
```

在这一点上，`x=25`是您可以达到的最低点。它的缩小序列中没有一个导致失败。所以我们已经完成了`x`参数！

现在我们只需重复这个过程与`y`参数

```
// find the next test that fails when shrinking the y parameter 
let x,y,z = (25,-4,50) 
Arb.shrink y
|> Seq.tryPick (fun y -> if associativeProperty x y z then None else Some (x,y,z) )
// answer (25, 4, 50)

// find the next test that fails when shrinking the y parameter 
let x,y,z = (25,4,50) 
Arb.shrink y
|> Seq.tryPick (fun y -> if associativeProperty x y z then None else Some (x,y,z) )
// answer (25, 2, 50)

// find the next test that fails when shrinking the y parameter 
let x,y,z = (25,2,50) 
Arb.shrink y
|> Seq.tryPick (fun y -> if associativeProperty x y z then None else Some (x,y,z) )
// answer (25, 1, 50)

// find the next test that fails when shrinking the y parameter 
let x,y,z = (25,1,50) 
Arb.shrink y
|> Seq.tryPick (fun y -> if associativeProperty x y z then None else Some (x,y,z) )
// answer None 
```

在这一点上，`y=1`是您可以达到的最低点。它的缩小序列中没有一个导致失败。所以我们已经完成了`y`参数！

最后，我们重复这个过程与`z`参数

```
// find the next test that fails when shrinking the z parameter 
let x,y,z = (25,1,50) 
Arb.shrink z
|> Seq.tryPick (fun z -> if associativeProperty x y z then None else Some (x,y,z) )
// answer (25, 1, 38)

// find the next test that fails when shrinking the z parameter 
let x,y,z = (25,1,38) 
Arb.shrink z
|> Seq.tryPick (fun z -> if associativeProperty x y z then None else Some (x,y,z) )
// answer (25, 1, 29)

// find the next test that fails when shrinking the z parameter 
let x,y,z = (25,1,29) 
Arb.shrink z
|> Seq.tryPick (fun z -> if associativeProperty x y z then None else Some (x,y,z) )
// answer (25, 1, 26)

// find the next test that fails when shrinking the z parameter 
let x,y,z = (25,1,26) 
Arb.shrink z
|> Seq.tryPick (fun z -> if associativeProperty x y z then None else Some (x,y,z) )
// answer None 
```

现在我们已经完成了所有的参数！

缩小后的最终反例是`(25,1,26)`。

## 添加前提条件

假设我们有一个新的想法要检查的属性。我们将创建一个名为`addition is not multiplication`的属性，这将有助于阻止实现中的任何恶意（甚至是意外）混淆。

这是我们的第一次尝试：

```
let additionIsNotMultiplication x y = 
    x + y <> x * y 
```

但是当我们运行这个测试时，我们得到了一个失败！

```
Check.Quick additionIsNotMultiplication 
// Falsifiable, after 3 tests (0 shrinks) (StdGen (2037191079,295941699)):
// 0
// 0 
```

嗯，显然`0+0`和`0*0`是相等的。但我们如何告诉 FsCheck 忽略这些输入，而保留其他所有输入？

这是通过使用`==>`（由 FsCheck 定义的运算符）将“条件”或过滤表达式添加到属性函数之前完成的。

这里是一个例子：

```
let additionIsNotMultiplication x y = 
    x + y <> x * y

let preCondition x y = 
    (x,y) <> (0,0)

let additionIsNotMultiplication_withPreCondition x y = 
    preCondition x y ==> additionIsNotMultiplication x y 
```

新属性是`additionIsNotMultiplication_withPreCondition`，可以像任何其他属性一样传递给`Check.Quick`。

```
Check.Quick additionIsNotMultiplication_withPreCondition
// Falsifiable, after 38 tests (0 shrinks) (StdGen (1870180794,295941700)):
// 2
// 2 
```

糟糕！我们忘记了另一个情况！让我们再次修复我们的前提条件：

```
let preCondition x y = 
    (x,y) <> (0,0)
    && (x,y) <> (2,2)

let additionIsNotMultiplication_withPreCondition x y = 
    preCondition x y ==> additionIsNotMultiplication x y 
```

现在这个方法有效了。

```
Check.Quick additionIsNotMultiplication_withPreCondition
// Ok, passed 100 tests. 
```

只有在想要过滤掉少数情况时，才应该使用这种前提条件。

如果大多数输入都是无效的，那么这种过滤将会很昂贵。在这种情况下，有一种更好的方法，将在未来的帖子中讨论。

FsCheck 文档中有更多关于如何调整属性的信息[在这里](https://fsharp.github.io/FsCheck/Properties.html)。

## 属性的命名约定

这些属性函数的目的与“正常”函数不同，那么我们应该如何命名它们？

在 Haskell 和 Erlang 世界中，按照惯例，属性以`prop_`前缀开头。在 .NET 世界中，更常见的是使用类似`AbcProperty`的后缀。

此外，在 F# 中，我们有命名空间、模块和属性（如`[<Test>]`），我们可以使用它们来组织属性并将其与其他函数区分开。

## 结合多个属性

一旦您有一组属性，您可以将它���组合成一个组（甚至，啧啧，一个*规范*！），通过将它们作为类类型的静态成员添加。

然后您可以执行`Check.QuickAll`并传入类的名称。

例如，这里是我们的三个加法属性：

```
let add x y = x + y // good implementation

let commutativeProperty x y = 
    add x y = add y x    

let associativeProperty x y z = 
    add x (add y z) = add (add x y) z    

let leftIdentityProperty x = 
    add x 0 = x

let rightIdentityProperty x = 
    add 0 x = x 
```

这里是与`Check.QuickAll`一起使用的相应静态类：

```
type AdditionSpecification =
    static member ``Commutative`` x y = commutativeProperty x y
    static member ``Associative`` x y z = associativeProperty x y z 
    static member ``Left Identity`` x = leftIdentityProperty x 
    static member ``Right Identity`` x = rightIdentityProperty x 

Check.QuickAll<AdditionSpecification>() 
```

## 将基于属性的测试与基于示例的测试结合起来

在本文的开头，我对使用“魔术”数字来测试输入空间的非常小部分的测试持否定态度。

但是，我认为基于示例的测试与基于属性的测试相辅相成。

基于示例的测试通常更容易理解，因为它不太抽象，因此与属性一起提供了很好的入口点和文档。

这里有一个例子：

```
type AdditionSpecification =
    static member ``Commutative`` x y = commutativeProperty x y
    static member ``Associative`` x y z = associativeProperty x y z 
    static member ``Left Identity`` x = leftIdentityProperty x 
    static member ``Right Identity`` x = rightIdentityProperty x 

    // some examples as well
    static member ``1 + 2 = 3``() =  
        add 1 2 = 3

    static member ``1 + 2 = 2 + 1``() =  
        add 1 2 = add 2 1 

    static member ``42 + 0 = 0 + 42``() =  
        add 42 0 = add 0 42 
```

## 从 NUnit 使用 FsCheck

您可以使用 FsCheck 进行 NUnit 和其他测试框架，只需使用额外的插件（例如 `FsCheck.NUnit` 用于 NUnit）。

而不是将测试标记为 `Test` 或 `Fact`，您可以使用 `Property` 属性。与普通测试不同，这些测试可以有参数！

这是一些测试的示例。

```
open NUnit.Framework
open FsCheck
open FsCheck.NUnit

[<Property(QuietOnSuccess = true)>]
let ``Commutative`` x y = 
    commutativeProperty x y

[<Property(Verbose= true)>]
let ``Associative`` x y z = 
    associativeProperty x y z 

[<Property(EndSize=300)>]
let ``Left Identity`` x = 
    leftIdentityProperty x 
```

如您所见，您可以通过注解的属性更改每个测试的配置（例如 `Verbose` 和 `EndSize`）。

并且 `QuietOnSuccess` 标志可用于使 FsCheck 与标准测试框架兼容，这些框架在成功时保持沉默，仅在出现问题时显示消息。

## 摘要

在本文中，我向您介绍了基于属性的检查的基础知识。

当然还有更多内容需要涵盖！在未来的文章中，我将涵盖诸如：

+   **如何提出适用于您的代码的属性**。属性不一定是数学的。我们将查看更一般的属性，例如反演（用于测试序列化/反序列化）、幂等性（用于安全处理多次更新或重复消息），以及测试预言。

+   **如何创建你自己的生成器和收缩器**。我们已经看到了 FsCheck 能够很好地生成随机值。但是，对于诸如正数、有效电子邮件地址或电话号码等约束条件的值，该怎么办呢？FsCheck 为您提供了构建自己的工具。

+   **如何进行基于模型的测试**，特别是如何测试并发问题。

我还介绍了一个邪恶的恶意程序员的概念。你可能认为这样的恶意程序员是不现实和过火的。

但是在许多情况下，*您*表现得像一个无意中的恶意程序员。您愉快地创建一个只适用于一些特殊情况但在更一般情况下却无法正常工作的实现，这并非出于恶意，而是出于无意识和盲目。

就像鱼对水毫无所知一样，我们经常对自己所做的假设毫不知情。基于属性的测试可以迫使我们意识到这些假设。

下次再见 —— 愉快的测试！

*本文中使用的代码示例可在 [GitHub 上找到](https://github.com/swlaschin/PropertyBasedTesting/blob/master/part1.fsx)*。

**想要了解更多吗？我写了[一篇关于选择属性进行基于属性的测试的后续文章](http://fsharpforfunandprofit.com/posts/property-based-testing-2/)。**

*更新：我做了一个基于这些文章的基于属性的测试的演讲。[幻灯片和视频在此处。](http://fsharpforfunandprofit.com/pbt/)*

## 附录：安装和故障排除 FsCheck

让 FsCheck 对您可用的最简单方法是创建一个 F# 项目并添加 NuGet 包 "FsCheck.NUnit"。这将在 `packages` 目录中安装 FsCheck 和 NUnit。

如果你正在使用 FSX 脚本文件进行交互式开发，你需要从适当的包位置加载 DLL，像这样：

```
// sets the current directory to be same as the script directory
System.IO.Directory.SetCurrentDirectory (__SOURCE_DIRECTORY__)

// assumes nuget install FsCheck.Nunit has been run 
// so that assemblies are available under the current directory
#I @"Packages\FsCheck.1.0.3\lib\net45"
//#I @"Packages\FsCheck.0.9.2.0\lib\net40-Client"  // use older version for VS2012
#I @"Packages\NUnit.2.6.3\lib"

#r @"FsCheck.dll"
#r @"nunit.framework.dll"

open System
open FsCheck
open NUnit.Framework 
```

接下来，通过运行以下命令来测试 FsCheck 是否正常工作：

```
let revRevIsOrig (xs:list<int>) = List.rev(List.rev xs) = xs

Check.Quick revRevIsOrig 
```

如果没有出现错误，那么一切都很顺利。

如果*确实*出现错误，那可能是因为你使用的是较旧版本的 Visual Studio。升级到 VS2013，或者如果失败了，执行以下操作：

+   首先确保你已经安装了最新的 F# 核心（[目前是 3.1](https://stackoverflow.com/questions/20332046/correct-version-of-fsharp-core)）。

+   确保你的`app.config`文件有[适当的绑定重定向](http://blog.ploeh.dk/2014/01/30/how-to-use-fsharpcore-430-when-all-you-have-is-431/)。

+   确保你的 NUnit 程序集是从本地引用而不是从全局程序集缓存（GAC）引用的。

这些步骤应该可以确保编译后的代码正常工作。

使用 F# 交互式环境可能会更加棘手。如果你没有使用 VS2013，可能会遇到诸如`System.InvalidCastException: Unable to cast object of type 'Arrow'`的错误。

最好的解决方法是升级到 VS2013！如果不行，你可以使用较旧版本的 FsCheck，比如 0.9.2（我已经成功地在 VS2012 中测试过）。
