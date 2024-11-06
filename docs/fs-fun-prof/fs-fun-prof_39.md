# 使用编译器指令交换类型安全性以获得高性能

# 使用编译器指令交换类型安全性以获得高性能

*简而言之：一个实验：您可以在开发时使用大量领域建模类型，并使用编译器指令稍后将其替换为性能更高的实现。*

## 领域建模与性能

我非常喜欢使用[用于领域建模的类型](http://fsharpforfunandprofit.com/ddd/)--非常非常*多*的类型！

这些类型既作为文档，又作为编译时约束，以确保只使用有效数据。

例如，如果我有两种类型`CustomerId`和`OrderId`，我可以将它们表示为不同的类型：

```
type CustomerId = CustomerId of int
type OrderId = OrderId of int 
```

通过这样做，我保证不能在需要`CustomerId`的地方使用`OrderId`。

问题在于，添加这样一层间接引用可能会影响性能：

+   额外的间接引用可能导致数据访问速度大大降低。

+   包装类需要额外的内存，会造成内存压力。

+   这反过来又会更频繁地触发垃圾回收器，这经常是托管代码性能问题的原因。

一般来说，我通常不会在设计时过分担心微小的性能问题。许多事情将对性能产生*更大*的影响，包括任何类型的 I/O 和您选择的算法。

结果，我非常*反对*在上下文之外进行微型基准测试。您应该始终在实际上下文中对真实应用程序进行分析，而不是过分担心可能不重要的事情。

话虽如此，我现在打算做一些微型基准测试！

### 微型基准测试包装类型

看看当大量使用包装类型时它的表现如何。假设我们想要：

+   创建一千万个客户 ID

+   然后，再对它们进行两次映射

+   然后，对它们进行过滤

诚然，将 1 添加到客户 ID 有点愚蠢--我们稍后会看一个更好的例子。

无论如何，这里是代码：

```
// type is an wrapper for a primitive type
type CustomerId = CustomerId of int

// create two silly functions for mapping and filtering 
let add1ToCustomerId (CustomerId i) = 
    CustomerId (i+1)

let isCustomerIdSmall (CustomerId i) = 
    i < 100000

// ---------------------------------
// timed with a 1 million element array
// ---------------------------------
#time
Array.init 1000000 CustomerId
// map it 
|> Array.map add1ToCustomerId 
// map it again
|> Array.map add1ToCustomerId 
// filter it 
|> Array.filter isCustomerIdSmall 
|> ignore
#time 
```

*上面的代码示例可以在 GitHub 上[找到](https://gist.github.com/swlaschin/348b6b9e64d4b150cf86#file-typesafe-performance-with-compiler-directives-1-fsx)*。

*(再次强调，这是一种糟糕的编码分析方式！)*

典型的计时结果如下：

```
Real: 00:00:00.296, CPU: 00:00:00.296, GC gen0: 6, gen1: 4, gen2: 0 
```

也就是说，执行这些步骤大约需要 0.3 秒，并且会创建相当多的垃圾，触发四次 gen1 收集。如果您不确定“gen0”、“gen1”和“gen2”是什么意思，那么[这是一个好的起点](https://msdn.microsoft.com/en-us/library/ms973837.aspx)。

*免责声明：我将在 F#互动环境中进行所有基准测试。经过优化的编译代码可能具有完全不同的性能特征。过去的表现不能保证未来的结果。请自行推断。等等，等等。*

如果我们将数组大小增加到 1000 万，我们会得到一个超过 10 倍的更慢结果：

```
Real: 00:00:03.489, CPU: 00:00:03.541, GC gen0: 68, gen1: 46, gen2: 2 
```

也就是说，执行这些步骤大约需要 3.5 秒，并且创建了*很多*垃圾，包括一些非常糟糕的 gen2 GC。实际上，你甚至可能会遇到“内存不足”的异常，这种情况下，你将不得不重新启动 F# 交互！

那么使用包装的替代方法有哪些？有两种常见的方法：

+   使用类型别名

+   使用单位量

让我们从类型别名开始。

## 使用类型别名

在类型别名方法中，我将简单地放弃包装，但保留类型作为文档。

```
type CustomerId = int
type OrderId = int 
```

如果我想要将类型用作文档，那么必须适当地注释函数。

例如，在下面的`add1ToCustomerId`中，参数和返回值都已经注释，所以它的类型是`CustomerId -> CustomerId`而不是`int -> int`。

```
let add1ToCustomerId (id:CustomerId) :CustomerId = 
    id+1 
```

### 对类型别名进行微型基准测试

让我们创建另一个微型基准：

```
type CustomerId = int

// create two silly functions for mapping and filtering 
let add1ToCustomerId (id:CustomerId) :CustomerId = 
    id+1
// val add1ToCustomerId : id:CustomerId -> CustomerId

let isCustomerIdSmall (id:CustomerId) = 
    id < 100000
// val isCustomerIdSmall : id:CustomerId -> bool

// ---------------------------------
// timed with a 1 million element array
// ---------------------------------
#time
Array.init 1000000 (fun i -> i)
// map it 
|> Array.map add1ToCustomerId 
// map it again
|> Array.map add1ToCustomerId 
// filter it 
|> Array.filter isCustomerIdSmall 
|> Array.length
#time 
```

*上面的代码示例可在 [GitHub](https://gist.github.com/swlaschin/348b6b9e64d4b150cf86#file-typesafe-performance-with-compiler-directives-2-fsx) 上找到*。

结果真是太棒了！

```
Real: 00:00:00.017, CPU: 00:00:00.015, GC gen0: 0, gen1: 0, gen2: 0 
```

执行这些步骤大约需要 17 毫秒，更重要的是，几乎没有产生垃圾。

如果我们将数组大小增加到 1000 万，我们会得到一个慢了 10 倍的结果，但仍然没有垃圾：

```
Real: 00:00:00.166, CPU: 00:00:00.156, GC gen0: 0, gen1: 0, gen2: 0 
```

与之前的版本相比超过三秒，这是非常好的。

### 类型别名的问题

遗憾的是，类型别名的问题是，我们现在完全失去了类型安全性！

为了演示，这里是一些创建 `CustomerId` 和 `OrderId` 的代码：

```
type CustomerId = int
type OrderId = int

// create two
let cid : CustomerId = 12
let oid : OrderId = 12 
```

令人遗憾的是，这两个标识符相等，并且我们可以将 `OrderId` 传递给期望 `CustomerId` 的函数，而编译器不会有任何投诉。

```
cid = oid              // true

// pass OrderId to function expecting a CustomerId 
add1ToCustomerId oid   // CustomerId = 13 
```

好吧，这看起来不太乐观！接下来怎么办？

## 使用单位量

另一种常见的选项是使用单位量来区分两种类型，像这样：

```
type [<Measure>] CustomerIdUOM 
type [<Measure>] OrderIdUOM 

type CustomerId = int<CustomerIdUOM>
type OrderId = int<OrderIdUOM> 
```

`CustomerId` 和 `OrderId` 仍然是两种不同的类型，但是单位量被擦除了，所以当 JIT 看到它时，该类型看起来像一个原始的 int。

我们可以看到当我们计时相同的步骤时，这是正确的：

```
// create two silly functions for mapping and filtering 
let add1ToCustomerId id  = 
    id+1<CustomerIdUOM>

let isCustomerIdSmall i = 
    i < 100000<CustomerIdUOM>

// ---------------------------------
// timed with a 1 million element array
// ---------------------------------
#time
Array.init 1000000 (fun i -> LanguagePrimitives.Int32WithMeasure<CustomerIdUOM> i)
// map it 
|> Array.map add1ToCustomerId 
// map it again
|> Array.map add1ToCustomerId 
// filter it 
|> Array.filter isCustomerIdSmall 
|> ignore
#time 
```

*上面的代码示例可在 [GitHub](https://gist.github.com/swlaschin/348b6b9e64d4b150cf86#file-typesafe-performance-with-compiler-directives-3-fsx) 上找到*。

典型的计时结果如下：

```
Real: 00:00:00.022, CPU: 00:00:00.031, GC gen0: 0, gen1: 0, gen2: 0 
```

再次，代码非常快（22 毫秒），同样重要的是，几乎没有产生垃圾。

如果我们将数组大小增加到 1000 万，我们仍然保持高性能（与类型别名方法一样），而且仍然没有垃圾：

```
Real: 00:00:00.157, CPU: 00:00:00.156, GC gen0: 0, gen1: 0, gen2: 0 
```

### 单位量的问题

使用单位量的优势在于，`CustomerId` 和 `OrderId` 类型是不兼容的，因此我们得到了想要的类型安全性。

但是我觉得它们从审美的角度来看不令人满意。我喜欢我的包装类型！

此外，单位量确实是用于数值值的。例如，我可以创建一个客户 ID 和订单 ID：

```
let cid = 12<CustomerIdUOM>
let oid = 4<OrderIdUOM> 
```

然后我可以将 CustomerId(12) 除以 OrderId(4) 来得到三...

```
let ratio = cid / oid
// val ratio : int<CustomerIdUOM/OrderIdUOM> = 3 
```

三个什么？每个订单 ID 三个客户 ID？这到底是什么意思？

是的，当然这在实践中永远不会发生，但是我还是很烦！

## 使用编译器指令来兼顾两全其美

我提到过我真的很喜欢包装类型吗？直到我接到电话说生产系统由于太多大的 GC 而出现性能问题之前，我真的很喜欢它们。

那么，我们能否两全其美？类型安全的包装类型和快速性能？

我认为可以，如果你愿意在开发和构建过程中进行一些额外的工作。

关键是同时拥有“包装类型”实现和“类型别名”实现，并根据编译器指令在它们之间进行切换。

要使此工作正常：

+   你将需要调整你的代码，不要直接访问类型，而是通过函数和模式匹配。

+   你将需要创建一个“类型别名”实现，其中包括一个“构造函数”，各种“获取器”和用于模式匹配的主动模式。

这是一个例子，使用`COMPILED`和`INTERACTIVE`指令，这样你就可以交互式地进行操作。显然，在实际代码中，你会使用自己的指令，比如`FASTTYPES`或类似的指令。

```
#if COMPILED  // uncomment to use aliased version 
//#if INTERACTIVE // uncomment to use wrapped version

// type is an wrapper for a primitive type
type CustomerId = CustomerId of int

// constructor
let createCustomerId i = CustomerId i

// get data
let customerIdValue (CustomerId i) = i

// pattern matching
// not needed

#else
// type is an alias for a primitive type
type CustomerId = int

// constructor
let inline createCustomerId i :CustomerId = i

// get data
let inline customerIdValue (id:CustomerId) = id

// pattern matching
let inline (|CustomerId|) (id:CustomerId) :int = id

#endif 
```

你可以看到，对于两个版本，我都创建了一个构造函数`createCustomerId`和一个获取器`customerIdValue`，对于类型别名版本，还有一个看起来就像`CustomerId`的主动模式。

有了这段代码，我们可以使用`CustomerId`而不用担心具体的实现：

```
// test the getter
let testGetter c1 c2 =
    let i1 = customerIdValue c1
    let i2 = customerIdValue c2
    printfn "Get inner value from customers %i %i" i1 i2
// Note that the signature is as expected:
// c1:CustomerId -> c2:CustomerId -> unit

// test pattern matching
let testPatternMatching c1 =
    let (CustomerId i) = c1
    printfn "Get inner value from Customers via pattern match: %i" i

    match c1 with
    | CustomerId i2 -> printfn "match/with %i" i
// Note that the signature is as expected:
// c1:CustomerId -> unit

let test() = 
    // create two ids
    let c1 = createCustomerId 1
    let c2 = createCustomerId 2
    let custArray : CustomerId [] = [| c1; c2 |]

    // test them
    testGetter c1 c2 
    testPatternMatching c1 
```

现在我们可以使用*相同的*微基准测试来运行两种实现：

```
// create two silly functions for mapping and filtering 
let add1ToCustomerId (CustomerId i) = 
    createCustomerId (i+1)

let isCustomerIdSmall (CustomerId i) = 
    i < 100000

// ---------------------------------
// timed with a 1 million element array
// ---------------------------------
#time
Array.init 1000000 createCustomerId
// map it 
|> Array.map add1ToCustomerId 
// map it again
|> Array.map add1ToCustomerId 
// filter it 
|> Array.filter isCustomerIdSmall 
|> Array.length
#time 
```

*上面的代码示例可在[GitHub](https://gist.github.com/swlaschin/348b6b9e64d4b150cf86#file-typesafe-performance-with-compiler-directives-4-fsx)上找到*。

结果与之前的例子类似。别名版本更快，不会产生 GC 压力：

```
// results using wrapped version
Real: 00:00:00.408, CPU: 00:00:00.405, GC gen0: 7, gen1: 4, gen2: 1

// results using aliased version
Real: 00:00:00.022, CPU: 00:00:00.031, GC gen0: 0, gen1: 0, gen2: 0 
```

对于一千万个元素的版本：

```
// results using wrapped version
Real: 00:00:03.199, CPU: 00:00:03.354, GC gen0: 67, gen1: 45, gen2: 2

// results using aliased version
Real: 00:00:00.239, CPU: 00:00:00.202, GC gen0: 0, gen1: 0, gen2: 0 
```

## 更复杂的示例

在实践中，我们可能需要比简单包装类型更复杂的东西。

例如，这里有一个`EmailAddress`（一个简单的包装类型，但受限于非空且包含“@”）和某种类型的`Activity`记录，其中存储了一个电子邮件和访问次数。

```
module EmailAddress =
    // type with private constructor 
    type EmailAddress = private EmailAddress of string

    // safe constructor
    let create s = 
        if System.String.IsNullOrWhiteSpace(s) then 
            None
        else if s.Contains("@") then
            Some (EmailAddress s)
        else
            None

    // get data
    let value (EmailAddress s) = s

module ActivityHistory =
    open EmailAddress

    // type with private constructor 
    type ActivityHistory = private {
        emailAddress : EmailAddress
        visits : int
        }

    // safe constructor
    let create email visits = 
        {emailAddress = email; visits = visits }

    // get data
    let email {emailAddress=e} = e
    let visits {visits=a} = a 
```

与之前一样，对于每种类型，都有一个构造函数和每个字段的获取器。

*注意：通常情况下，我会在模块外定义一个类型，但是由于真正的构造函数需要是私有的，我将类型放在了模块内，并给了模块和类型相同的名称。如果这太麻烦了，你可以将模块重命名为与类型不同的名称，或者使用 OCaml 约定，将模块中的主要类型命名为“T”，这样你就会得到`EmailAddress.T`作为类型名称。*

为了创建更高性能的版本，我们将`EmailAddress`替换为类型别名，并将`Activity`替换为结构体，就像这样：

```
module EmailAddress =

    // aliased type 
    type EmailAddress = string

    // safe constructor
    let inline create s :EmailAddress option = 
        if System.String.IsNullOrWhiteSpace(s) then 
            None
        else if s.Contains("@") then
            Some s
        else
            None

    // get data
    let inline value (e:EmailAddress) :string = e

module ActivityHistory =
    open EmailAddress

    [<Struct>]
    type ActivityHistory(emailAddress : EmailAddress, visits : int) = 
        member this.EmailAddress = emailAddress 
        member this.Visits = visits 

    // safe constructor
    let create email visits = 
        ActivityHistory(email,visits)

    // get data
    let email (act:ActivityHistory) = act.EmailAddress
    let visits (act:ActivityHistory) = act.Visits 
```

这个版本重新实现了构造函数和每个字段的 getter。我也可以使`ActivityHistory`的字段名称在两种情况下相同，但是在结构体情况下，类型推断将无法工作。通过使它们不同，用户被迫使用 getter 函数而不是点操作。

两种实现具有相同的“API”，因此我们可以创建适用于两者的代码：

```
let rand = new System.Random()

let createCustomerWithRandomActivityHistory() = 
    let emailOpt = EmailAddress.create "abc@example.com"
    match emailOpt with
    | Some email  -> 
        let visits = rand.Next(0,100) 
        ActivityHistory.create email visits 
    | None -> 
        failwith "should not happen"

let add1ToVisits activity = 
    let email = ActivityHistory.email activity
    let visits = ActivityHistory.visits activity 
    ActivityHistory.create email (visits+1)

let isCustomerInactive activity = 
    let visits = ActivityHistory.visits activity 
    visits < 3

// execute creation and iteration for a large number of records
let mapAndFilter noOfRecords = 
    Array.init noOfRecords (fun _ -> createCustomerWithRandomActivity() )
    // map it 
    |> Array.map add1ToVisits 
    // map it again
    |> Array.map add1ToVisits 
    // filter it 
    |> Array.filter isCustomerInactive 
    |> ignore  // we don't actually care! 
```

### 这种方法的利弊

这种方法的一个好处是它是自我纠正的--它强迫你正确使用“API”。

例如，如果我开始直接通过点操作访问`ActivityHistory`记录中的字段，那么当编译器指令打开并且使用结构实现时，该代码将会出错。

当然，你也可以创建一个签名文件来强制执行 API。

不足之处在于，我们失去了一些优雅的语法，比如`{rec with ...}`。但你真的只应该在小记录（2-3 个字段）上使用这种技术，所以没有`with`并不是一个大负担。

### 计时两种实现方式

而不是使用`#time`，这次我编写了一个自定义计时器，运行一个函数 10 次，并打印出每次运行时使用的 GC 和内存。

```
/// Do countN repetitions of the function f and print the 
/// time elapsed, number of GCs and change in total memory
let time countN label f  = 

    let stopwatch = System.Diagnostics.Stopwatch()

    // do a full GC at the start but NOT thereafter
    // allow garbage to collect for each iteration
    System.GC.Collect()  
    printfn "Started"         

    let getGcStats() = 
        let gen0 = System.GC.CollectionCount(0)
        let gen1 = System.GC.CollectionCount(1)
        let gen2 = System.GC.CollectionCount(2)
        let mem = System.GC.GetTotalMemory(false)
        gen0,gen1,gen2,mem

    printfn "======================="         
    printfn "%s (%s)" label WrappedOrAliased
    printfn "======================="         
    for iteration in [1..countN] do
        let gen0,gen1,gen2,mem = getGcStats()
        stopwatch.Restart() 
        f()
        stopwatch.Stop() 
        let gen0',gen1',gen2',mem' = getGcStats()
        // convert memory used to K
        let changeInMem = (mem'-mem) / 1000L
        printfn "#%2i elapsed:%6ims gen0:%3i gen1:%3i gen2:%3i mem:%6iK" iteration stopwatch.ElapsedMilliseconds (gen0'-gen0) (gen1'-gen1) (gen2'-gen2) changeInMem 
```

*上面的代码示例可以在[GitHub 上找到](https://gist.github.com/swlaschin/348b6b9e64d4b150cf86#file-typesafe-performance-with-compiler-directives-5-fsx)*。

现在让我们在数组中运行`mapAndFilter`，其中包含一百万条记录：

```
let size = 1000000
let label = sprintf "mapAndFilter: %i records" size 
time 10 label (fun () -> mapAndFilter size) 
```

结果如下所示：

```
=======================
mapAndFilter: 1000000 records (Wrapped)
=======================
# 1 elapsed:   820ms gen0: 13 gen1:  8 gen2:  1 mem: 72159K
# 2 elapsed:   878ms gen0: 12 gen1:  7 gen2:  0 mem: 71997K
# 3 elapsed:   850ms gen0: 12 gen1:  6 gen2:  0 mem: 72005K
# 4 elapsed:   885ms gen0: 12 gen1:  7 gen2:  0 mem: 72000K
# 5 elapsed:  6690ms gen0: 16 gen1: 10 gen2:  1 mem:-216005K
# 6 elapsed:   714ms gen0: 12 gen1:  7 gen2:  0 mem: 72003K
# 7 elapsed:   668ms gen0: 12 gen1:  7 gen2:  0 mem: 71995K
# 8 elapsed:   670ms gen0: 12 gen1:  7 gen2:  0 mem: 72001K
# 9 elapsed:  6676ms gen0: 16 gen1: 11 gen2:  2 mem:-215998K
#10 elapsed:   712ms gen0: 13 gen1:  7 gen2:  0 mem: 71998K

=======================
mapAndFilter: 1000000 records (Aliased)
=======================
# 1 elapsed:   193ms gen0:  7 gen1:  0 gen2:  0 mem: 25325K
# 2 elapsed:   142ms gen0:  8 gen1:  0 gen2:  0 mem: 23779K
# 3 elapsed:   143ms gen0:  8 gen1:  0 gen2:  0 mem: 23761K
# 4 elapsed:   138ms gen0:  8 gen1:  0 gen2:  0 mem: 23745K
# 5 elapsed:   135ms gen0:  7 gen1:  0 gen2:  0 mem: 25327K
# 6 elapsed:   135ms gen0:  8 gen1:  0 gen2:  0 mem: 23762K
# 7 elapsed:   137ms gen0:  8 gen1:  0 gen2:  0 mem: 23755K
# 8 elapsed:   140ms gen0:  8 gen1:  0 gen2:  0 mem: 23777K
# 9 elapsed:   174ms gen0:  7 gen1:  0 gen2:  0 mem: 25327K
#10 elapsed:   180ms gen0:  8 gen1:  0 gen2:  0 mem: 23762K 
```

现在这段代码不再只由值类型组成，所以性能分析现在变得更加混乱！`mapAndFilter`函数使用`createCustomerWithRandomActivity`，后者又使用`Option`，一个引用类型，因此将会分配大量引用类型。就像在现实生活中一样，保持事情纯粹是很困难的！

即使如此，你可以看到封装版本比别名版本慢（大约 800ms 对 150ms），并且在每次迭代中产生更多的垃圾（大约 72Mb 对 24Mb），最重要的是在第 5 次和第 9 次迭代中有两次大的 GC 暂停，而别名版本甚至从未进行过 gen1 GC，更不用说 gen2 了。

*注意：别名版本正在使用内存，但没有 gen1，这让我对这些数字有些怀疑。我认为如果在 F#交互环境之外运行，结果可能会有所不同。*

## 那么非记录类型呢？

���果我们要优化的类型是一个判别联合而不是记录呢？

我的建议是将 DU 转换为一个带有每种情况标签和所有可能数据字段的结构。

例如，假设我们有一个 DU，将`Activity`分类为`Active`和`Inactive`，对于`Active`情况，我们存储电子邮件和访问次数，而对于`Inactive`情况，我们只存储电子邮件：

```
module Classification =
    open EmailAddress
    open ActivityHistory

    type Classification = 
        | Active of EmailAddress * int
        | Inactive of EmailAddress 

    // constructor
    let createActive email visits = 
        Active (email,visits)
    let createInactive email = 
        Inactive email

    // pattern matching
    // not needed 
```

要将其转换为结构体，我会这样做：

```
module Classification =
    open EmailAddress
    open ActivityHistory
    open System

    [<Struct>]
    type Classification(isActive : bool, email: EmailAddress, visits: int) = 
        member this.IsActive = isActive 
        member this.Email = email
        member this.Visits = visits

    // constructor
    let inline createActive email visits = 
        Classification(true,email,visits)
    let inline createInactive email = 
        Classification(false,email,0)

    // pattern matching
    let inline (|Active|Inactive|) (c:Classification) = 
        if c.IsActive then 
            Active (c.Email,c.Visits)
        else
            Inactive (c.Email) 
```

注意`Visits`在`Inactive`情况下没有使用，因此设置为默认值。

现在让我们创建一个函数，对活动历史进行分类，创建一个`Classification`，然后仅为活跃客户过滤和提取电子邮件。

```
open Classification

let createClassifiedCustomer activity = 
    let email = ActivityHistory.email activity
    let visits = ActivityHistory.visits activity 

    if isCustomerInactive activity then 
        Classification.createInactive email 
    else
        Classification.createActive email visits 

// execute creation and iteration for a large number of records
let extractActiveEmails noOfRecords =
    Array.init noOfRecords (fun _ -> createCustomerWithRandomActivityHistory() )
    // map to a classification
    |> Array.map createClassifiedCustomer
    // extract emails for active customers
    |> Array.choose (function
        | Active (email,visits) -> email |> Some
        | Inactive _ -> None )
    |> ignore 
```

*上面的代码示例可以在[GitHub 上找到](https://gist.github.com/swlaschin/348b6b9e64d4b150cf86#file-typesafe-performance-with-compiler-directives-5-fsx)*。

使用两种不同实现对这个函数进行性能分析的结果如下：

```
=======================
extractActiveEmails: 1000000 records (Wrapped)
=======================
# 1 elapsed:   664ms gen0: 12 gen1:  6 gen2:  0 mem: 64542K
# 2 elapsed:   584ms gen0: 14 gen1:  7 gen2:  0 mem: 64590K
# 3 elapsed:   589ms gen0: 13 gen1:  7 gen2:  0 mem: 63616K
# 4 elapsed:   573ms gen0: 11 gen1:  5 gen2:  0 mem: 69438K
# 5 elapsed:   640ms gen0: 15 gen1:  7 gen2:  0 mem: 58464K
# 6 elapsed:  4297ms gen0: 13 gen1:  7 gen2:  1 mem:-256192K
# 7 elapsed:   593ms gen0: 14 gen1:  7 gen2:  0 mem: 64623K
# 8 elapsed:   621ms gen0: 13 gen1:  7 gen2:  0 mem: 63689K
# 9 elapsed:   577ms gen0: 11 gen1:  5 gen2:  0 mem: 69415K
#10 elapsed:   609ms gen0: 15 gen1:  7 gen2:  0 mem: 58480K

=======================
extractActiveEmails: 1000000 records (Aliased)
=======================
# 1 elapsed:   254ms gen0: 32 gen1:  1 gen2:  0 mem: 33162K
# 2 elapsed:   221ms gen0: 33 gen1:  0 gen2:  0 mem: 31532K
# 3 elapsed:   196ms gen0: 32 gen1:  0 gen2:  0 mem: 33113K
# 4 elapsed:   185ms gen0: 33 gen1:  0 gen2:  0 mem: 31523K
# 5 elapsed:   187ms gen0: 33 gen1:  0 gen2:  0 mem: 31532K
# 6 elapsed:   186ms gen0: 32 gen1:  0 gen2:  0 mem: 33095K
# 7 elapsed:   191ms gen0: 33 gen1:  0 gen2:  0 mem: 31514K
# 8 elapsed:   200ms gen0: 32 gen1:  0 gen2:  0 mem: 33096K
# 9 elapsed:   189ms gen0: 33 gen1:  0 gen2:  0 mem: 31531K
#10 elapsed:  3732ms gen0: 33 gen1:  1 gen2:  1 mem:-256432K 
```

与之前一样，别名/结构体版本更具性能，更快，生成的垃圾更少（尽管最后有一个 GC 暂停，哦，天哪）。

## 问题

### 这不是很多工作吗，创建两种实现？

是的！*我认为一般情况下你不应该这样做。*这只是我的一个实验。

我建议将记录和 DUs 转换为结构体是最后的选择，只有在消除所有其他瓶颈之后才这样做。

然而，可能有一些特殊情况，速度和内存是至关重要的，那么，也许值得做一些类似的事情。

### 有什么不足之处吗？

除了所有额外的工作和维护，你是这个意思吗？

嗯，因为这些类型本质上是私有的，我们失去了一些在访问类型内部时可用的漂亮语法，比如`{rec with ...}`，但正如我所说，你应该只在小记录中使用这种技术。

更重要的是，像结构体这样的值类型并不是万能的。它们有自己的问题。

例如，当作为参数传递时可能会更慢（因为按值复制），你必须小心不要[隐式装箱它们](http://theburningmonk.com/2015/07/beware-of-implicit-boxing-of-value-types/)，否则你最终会进行分配并创建垃圾。微软有关于使用类 vs 结构体的[指南](https://msdn.microsoft.com/en-us/library/ms229017.aspx)，但也请参考[这篇关于打破这些指南的评论](http://stackoverflow.com/a/6973171/1136133)和[这些规则](http://stackoverflow.com/a/598268/1136133)。

### 考虑使用阴影吗？

当客户想要使用不同的实现时，就会使用阴影。例如，你可以通过打开[Checked module](https://msdn.microsoft.com/en-us/library/ee340296.aspx)来从无检查切换到有检查的算术。[更多细节请看这里](http://theburningmonk.com/2012/01/checked-context-in-c-and-f/)。

但这在这里行不通——我不希望每个客户端决定他们将使用哪个版本的类型。这将导致各种不兼容问题。而且，这不是一个模块决策，而是基于部署上下文的决策。

### 关于更高性能的��合类型呢？

我到处都在使用`array`作为集合类型。如果你想要其他高性能的集合，请查看[FSharpx.Collections](https://fsprojects.github.io/FSharpx.Collections/)或[Funq collections](https://github.com/GregRos/Funq)。

### 你混淆了分配、映射、过滤。需要更细致的分析吗？

我试图在说微基准测试不好之后保持一些尊严！

所以，是的，我故意创建了一个混合使用的案例，并将其作为一个整体进行测量，而不是分别对每个部分进行基准测试。你的使用场景显然会有所不同，所以我认为没有必要深入研究。

另外，我所有的基准测试都是在 F# 交互式环境中进行的。带有优化的编译代码可能具有完全不同的性能特征。

### 还有哪些方法可以提高性能？

由于 F# 是一种.NET 语言，C# 的性能提示同样适用于 F#，像标准的东西：

+   所有 I/O 都应该是异步的。如果可能的话，使用流式 I/O 而不是随机访问 I/O。批量处理你的请求。

+   检查你的算法。任何比 O(n log(n)) 更糟糕的算法都应该被审视。

+   不要重复做同样的事情。根据需要进行缓存。

+   通过将对象保持在连续内存中并避免过多的深度引用（指针）链，将事物保持在 CPU 缓存中。有助于此的事物包括使用数组而不是列表，值类型而不是引用类型等。

+   通过减少分配来避免对垃圾收集器的压力。避免创建在 gen0 收集中幸存的长寿命对象。

明确一点，我并不自称是.NET 性能和垃圾收集方面的专家。实际上，如果你发现这个分析有什么问题，请告诉我！

这里有一些帮助我的资源：

+   本书 [编写高性能.NET 代码](http://www.writinghighperf.net/) 由本·沃森编写。

+   马丁·汤普森在性能方面有一个很棒的[博客](http://mechanical-sympathy.blogspot.jp/2012/08/memory-access-patterns-are-important.html)，还有一些优秀的视频，比如[前 10 个性能迷思](http://www.infoq.com/presentations/top-10-performance-myths)。（[这里有一个很好的总结](http://weronikalabaj.com/performance-myths-and-facts/)。）

+   [理解延迟](https://www.youtube.com/watch?v=9MKY4KypBzg)，由吉尔·特纳制作的视频。

+   [每个人都应该了解的大型托管代码库性能的基本真相](https://channel9.msdn.com/Events/TechEd/NorthAmerica/2013/DEV-B333)，由微软的达斯汀·坎贝尔制作的视频。

+   特别是对于 F#：

    +   Yan Cui 在 [记录 vs 结构](http://theburningmonk.com/2011/10/fsharp-performance-test-structs-vs-records/) 和 [内存布局](http://theburningmonk.com/2015/07/smallest-net-ref-type-is-12-bytes-or-why-you-should-consider-using-value-types) 上有一些博客文章。

    +   乔恩·哈罗普有很多好文章，比如[这篇](http://flyingfrogblog.blogspot.co.uk/2012/06/are-functional-languages-inherently.html)，但其中一些内容是付费的。

    +   视频：[在.NET 和 GPU 上进行高性能 F#编程](https://vimeo.com/33699102)，由杰克·帕帕斯制作。声音很糟糕，但幻灯片和讨论很好！

    +   [数学和统计资源](http://fsharp.org/guides/math-and-statistics/) 在 fsharp.org 上

## 摘要

> "保持干净；保持简单；力求优雅。" -- *马丁·汤普森*

这只是一个小实验，看看我是否能两全其美。使用大量类型进行领域建模，但在需要时以一种优雅的方式获得性能。

我认为这是一个相当不错的解决方案，但正如我之前所说，这种优化（和丑化）应该只在一小部分被大量使用的核心类型上需要，这些类型被分配了很多次。

最后，我自己在一个大型生产系统中没有使用过这种方法（我从未需要过），所以我很想听听战壕中的人们对他们的做法有什么反馈。

*本文中使用的代码示例可以在[GitHub 上找到](https://gist.github.com/swlaschin/348b6b9e64d4b150cf86)*。
