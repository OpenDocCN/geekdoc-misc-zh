# Elm 入门指南

**Elm 是一种编译成 JavaScript 的函数式语言。** 它与像 React 这样的项目竞争，作为创建网站和 Web 应用程序的工具。 Elm 非常强调简单性、易用性和高质量的工具。

本指南将：

+   教你 Elm 编程的基础知识。

+   向你展示如何使用*Elm 架构*制作交互式应用程序。

+   强调适用于任何编程语言的原则和模式。

最终，我希望你不仅能在 Elm 中创建出色的 Web 应用程序，还能理解使 Elm 使用起来愉快的核心思想和模式。

如果你还在犹豫不决，我可以肯定地保证，如果你尝试一下 Elm 并实际上在其中做一个项目，你最终会写出更好的 JavaScript 和 React 代码。这些想法相当容易转移！

## 一个快速示例

当然，*我*认为 Elm 很好，所以你自己看看吧。

这里是[一个简单的计数器](http://elm-lang.org/examples/buttons)。如果你看一下代码，它只是让你增加和减少计数器：

```
import Html exposing (Html, button, div, text)
import Html.Events exposing (onClick)

main =
  Html.beginnerProgram { model = 0, view = view, update = update }

type Msg = Increment | Decrement

update msg model =
  case msg of
    Increment ->
      model + 1

    Decrement ->
      model - 1

view model =
  div []
    [ button [ onClick Decrement ] [ text "-" ]
    , div [] [ text (toString model) ]
    , button [ onClick Increment ] [ text "+" ]
    ] 
```

注意`update`和`view`完全解耦。你以声明方式描述你的 HTML，而 Elm 负责处理 DOM。

## 为什么选择*函数式*语言？

忘记你听到的关于函数式编程的一切。花哨的词汇，奇怪的想法，糟糕的工具。呕。Elm 是关于：

+   在实践中没有运行时错误。没有`null`。没有`undefined`不是一个函数。

+   友好的错误消息帮助您更快地添加功能。

+   良好架构的代码在应用程序增长时*保持*良好架构。

+   所有 Elm 包都自动强制执行语义版本控制。

任何 JS 库的组合都无法给你这个，但在 Elm 中所有这些都是免费且易于实现。现在这些好处*只有*在 Elm 上才可能，因为 Elm 建立在 40 多年关于类型化函数式语言的工作基础之上。因此 Elm 是一种函数式语言，因为实际的好处值得你花几个小时阅读本指南。

我非常强调让 Elm 易于学习和使用，所以我只是要求你尝试一下 Elm，看看你的想法。我希望你会感到惊喜！
