# 错误处理与任务

# 错误处理与任务

Elm 的一个保证是你实际上不会看到运行时错误。NoRedInk 已经在生产环境中使用 Elm 约一年了，他们还从未出现过一个！像 Elm 中的所有保证一样，这归结于基本语言设计选择。在这种情况下，我们受益于 Elm 将错误视为数据的事实。（你是否注意到我们在这里经常将事物视为数据？）

这一部分将介绍三种数据结构，帮助你以几种不同的方式处理错误。

+   `Maybe`

+   `Result`

+   `Task`

现在你们中的一些人可能想直接转到任务，但相信我，按顺序进行会有所帮助！你可以把这三种数据结构看作是逐渐解决越来越疯狂情况的进展。所以如果你直接跳到最后，一下子就会有很多事情要弄清楚。

## 一些历史背景

有两种流行的语言特性经常会导致意外问题。如果你使用过 Java、C、JavaScript、Python 或 Ruby，你几乎肯定因为`null`值或其他人代码中的意外异常而使你的代码崩溃。

现在，这些东西对人们来说极其熟悉，但这并不意味着它们就是好的！

### 空

每当你认为你有一个`String`，你可能只有一个`null`。你应该检查吗？给你值的人有检查吗？也许它会没事？也许它会导致服务器崩溃？我想我们以后会知道的！

发明者 Tony Hoare 对此有以下看法：

> 我称之为我的亿万美元错误。这是在 1965 年发明了空引用。当时，我正在设计第一个面向对象语言（ALGOL W）中引用的全面类型系统。我的目标是确保所有引用的使用都应该绝对安全，由编译器自动执行检查。但我忍不住想要放入一个空引用，因为这样做太容易了。这导致了无数的错误、漏洞和系统崩溃，可能在过去四十年里造成了数十亿美元的痛苦和损失。

正如我们很快将看到的，`Maybe` 的要点是以一种愉快的方式避免这个问题。

### 异常

Joel Spolsky 在[2003 年](http://www.joelonsoftware.com/items/2003/10/13.html)详细概述了异常的问题。基本上，看起来没问题的代码在运行时可能会崩溃。惊喜！

`Result` 的要点在于明确失败的可能性，并确保适当处理。

`Task`的要点基本相同，但在我们有异步运行的代码时也适用。你的错误处理机制不应该仅仅因为你发起了一个 HTTP 请求就完全崩溃！

# 或许

# 或许

最好先从`Maybe`的定义开始。它像这样定义的联合类型就像所有这里的示例一样。它的定义如下：

```
> type Maybe a = Nothing | Just a

> Nothing
Nothing : Maybe a

> Just
<function> : a -> Maybe a

> Just "hello"
Just "hello" : Maybe String

> Just 1.618
Just 1.618 : Maybe Float 
```

如果你想要一个`Maybe`值，你必须使用`Nothing`或`Just`构造函数来创建它。这意味着为了处理数据，你必须使用一个`case`表达式。这意味着编译器可以确保你肯定已经涵盖了两种可能性！

有两种情况会出现`Maybe`值。

## 可选字段

假设我们正在运行一个社交网络网站。连接人们，友谊等等。你知道这一套。洋葱最好地概括了我们的真正目标：[尽可能多地为中央情报局挖掘数据](http://www.theonion.com/video/cias-facebook-program-dramatically-cut-agencys-cos-19753)。如果我们想要*所有*的数据，我们需要让人们逐渐接受它。让他们以后再添加。增加一些功能，鼓励他们随着时间分享更多的信息。

所以让我们从一个用户的简单模型开始。他们必须有一个名字，但我们将年龄设为可选。

```
type alias User =
  { name : String
  , age : Maybe Int
  } 
```

现在假设苏登陆并决定不提供她的生日：

```
sue : User
sue =
  { name = "Sue", age = Nothing } 
```

现在她的朋友们无法祝她生日快乐了。伤心！后来汤姆创建了一个个人资料，并*确实*提供了他的年龄：

```
tom : User
tom =
  { name = "Tom", age = Just 24 } 
```

太好了，那将是他的生日礼物。但更重要的是，汤姆是一个有价值的人群！广告商会很高兴的。

好的，现在我们有了一些用户，我们如何在不违反任何法律的情况下向他们推销酒精？如果我们向 21 岁以下的人推销，人们可能会生气，所以让我们检查一下：

```
canBuyAlcohol : User -> Bool
canBuyAlcohol user =
  case user.age of
    Nothing ->
      False

    Just age ->
      age >= 21 
```

现在很酷的是，我们被迫使用`case`来对用户的年龄进行模式匹配。实际上，写出忘记用户可能没有年龄的代码是不可能的。Elm 可以确保这一点。现在我们可以自信地宣传酒精，而不会直接影响未成年人！只会影响他们年长的同龄人。

## 部分函数

有时候你需要一个函数，在某些情况下给出答案，但在其他情况下却不给出。

假设百事可乐想要为 13 到 18 岁的人做一些广告购买。老实说，最好是让孩子们在这个年龄之前就开始喝百事可乐，但是对于 13 岁以下的孩子来说，在我们的网站上是违法的。

所以假设我们想要编写一个函数，告诉我们用户的年龄，但只有当他们年龄在 13 到 18 岁之间时：

```
getTeenAge : User -> Maybe Int
getTeenAge user =
  case user.age of
    Nothing ->
      Nothing

    Just age ->
      if 13 <= age && age <= 18 then
        Just age

      else
        Nothing 
```

再次提醒我们，用户可能没有年龄，但如果有的话，我们只想返回介于 13 到 18 岁之间的年龄。现在 Elm 可以保证任何调用`getTeenAge`的人都必须处理年龄超出范围的可能性。

当你开始将其与像[`List.filterMap`](http://package.elm-lang.org/packages/elm-lang/core/latest/List#filterMap)这样的库函数结合使用时，情况就变得非常有趣，它可以帮助你处理更多的数据。例如，也许我们想要弄清楚 13 到 18 岁之间年龄的分布。我们可以这样做：

```
> alice = User "Alice" (Just 14)
... : User

> bob = User "Bob" (Just 16)
... : User

> users = [ sue, tom, alice, bob ]
... : List User

> List.filterMap getTeenAge users
[14,16] : List Int 
```

我们最终只关心的年龄。现在我们可以将我们的`List Int`输入到一个函数中，该函数可以计算出每个数字的分布。

# 结果

# 结果

当你有可能“失败”的逻辑时，`Result` 就非常有用。例如，将一个 `String` 解析成一个 `Int` 可能会失败。如果字符串填充了字母 B 呢？在这种情况下，我们想要一个这样类型的函数：

```
String.toInt : String -> Result String Int 
```

这意味着 `String.toInt` 将接收一个字符串值并开始处理该字符串。如果它不能转换为整数，我们提供一个 `String` 错误消息。如果它可以转换为整数，我们就返回那个 `Int`。所以 `Result String Int` 类型的含义是，“我的错误是字符串，我的成功是整数。”

为了尽可能具体，让我们看看 `Result` 的实际定义。它实际上与 `Maybe` 类型非常相似，但它有 *两个* 类型变量：

```
type Result error value
  = Err error
  | Ok value 
```

你有两个构造函数：`Err` 标记错误和 `Ok` 标记成功。让我们看看当我们在 REPL 中实际使用 `String.toInt` 时会发生什么：

```
> import String

> String.toInt "128"
Ok 128 : Result String Int

> String.toInt "64"
Ok 64 : Result String Int

> String.toInt "BBBB"
Err "could not convert string 'BBBB' to an Int" : Result String Int 
```

因此，与大多数语言不同，我们不会抛出异常，而是返回表示事情进行得如何的数据。让我们想象有人正在一个文本字段中输入他们的年龄，我们想要显示一个验证消息：

```
view : String -> Html msg
view userInputAge =
  case String.toInt userInputAge of
    Err msg ->
      span [class "error"] [text msg]

    Ok age ->
      if age < 0 then
        span [class "error"] [text "I bet you are older than that!"]

      else if age > 140 then
        span [class "error"] [text "Seems unlikely..."]

      else
        text "OK!" 
```

再次，我们必须使用 `case`，这样我们就能保证处理数字不好的特殊情况。

# 任务

# 任务

这些文档正在更新至 0.18 版本。它们很快就会回来！在那之前，[文档](http://package.elm-lang.org/packages/elm-lang/core/4.0.0/Task) 将提供部分概述。
