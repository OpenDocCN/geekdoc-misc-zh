# 核心语言

# 核心语言

本节将带您了解 Elm 的简单核心语言。

最好是跟着操作，所以在安装之后，在终端启动`elm-repl`。（或者使用[在线 REPL](http://elmrepl.cuberoot.in/)。）无论哪种方式，你都应该看到类似这样的内容：

```
---- elm repl 0.18.0 -----------------------------------------------------------
 :help for help, :exit to exit, more at <https://github.com/elm-lang/elm-repl>
--------------------------------------------------------------------------------
> 
```

REPL 会打印出每个结果的类型，但是**我们将在本教程中略去类型注释**，以便逐渐介绍概念。

我们将涵盖值、函数、列表、元组和记录。这些构建块与 JavaScript、Python 和 Java 等语言中的结构相对应得相当紧密。

## 值

让我们从一些字符串开始：

```
> "hello"
"hello"

> "hello" ++ "world"
"helloworld"

> "hello" ++ " world"
"hello world" 
```

Elm 使用`(++)`运算符将字符串连接在一起。请注意，当将两个字符串放在一起时，两个字符串都完全保留，因此当我们将`"hello"`和`"world"`组合在一起时，结果没有空格。

数学看起来也很正常：

```
> 2 + 3 * 4
14

> (2 + 3) * 4
20 
```

与 JavaScript 不同，Elm 区分整数和浮点数。就像 Python 3 一样，有浮点除法`(/)`和整数除法`(//)`。

```
> 9 / 2
4.5

> 9 // 2
4 
```

## 函数

让我们从编写一个函数`isNegative`开始，该函数接受一个数字并检查它是否小于零。结果将是`True`或`False`。

```
> isNegative n = n < 0
<function>

> isNegative 4
False

> isNegative -7
True

> isNegative (-3 * -4)
False 
```

注意函数应用看起来与 JavaScript、Python 和 Java 等语言不同。我们不是用括号将所有参数括起来，然后用逗号分隔它们，而是用空格应用函数。所以`(add(3,4))`变成了`(add 3 4)`，这样可以避免一堆括号和逗号，当事情变得更复杂时，这看起来更加清晰。[elm-html 包](http://elm-lang.org/blog/blazing-fast-html)是一个很好的例子，它展示了这种方法如何保持事物轻盈。

## 如果表达式

当你想要在 Elm 中进行条件行为时，你使用一个 if 表达式。

```
> if True then "hello" else "world"
"hello"

> if False then "hello" else "world"
"world" 
```

关键字`if` `then` `else`用于分隔条件和两个分支，因此我们不需要任何括号或花括号。

Elm 没有“真实性”的概念，因此数字、字符串和列表不能用作布尔值。如果我们尝试，Elm 会告诉我们需要使用真实的布尔值。

现在让我们来编写一个函数，告诉我们一个数字是否超过了`9000`。

```
> over9000 powerLevel = \
|   if powerLevel > 9000 then "It's over 9000!!!" else "meh"
<function>

> over9000 42
"meh"

> over9000 100000
"It's over 9000!!!" 
```

在 REPL 中使用反斜杠让我们将内容分成多行。我们在上面的`over9000`的定义中使用了这个。此外，最好的做法是始终将函数的主体放在下一行。这样做使事物更加统一和易于阅读，因此你应该在你在正常代码中定义的所有函数和值中都这样做。

> **注意：** 确保在函数的第二行之前加上一个空格。Elm 有一个“语法上有意义的空格”意味着缩进是其语法的一部分。

## 列表

列表是 Elm 中最常见的数据结构之一。它们保存一系列相关的事物，类似于 JavaScript 中的数组。

列表可以容纳许多值。这些值必须都具有相同的类型。以下是一些使用[List 库](http://package.elm-lang.org/packages/elm-lang/core/latest/List)中的函数的示例：

```
> names = [ "Alice", "Bob", "Chuck" ]
["Alice","Bob","Chuck"]

> List.isEmpty names
False

> List.length names
3

> List.reverse names
["Chuck","Bob","Alice"]

> numbers = [1,4,3,2]
[1,4,3,2]

> List.sort numbers
[1,2,3,4]

> double n = n * 2
<function>

> List.map double numbers
[2,8,6,4] 
```

再次强调，列表中的所有元素必须具有相同的类型。

## 元组

元组是另一个有用的数据结构。元组可以容纳固定数量的值，每个值可以是任何类型。一个常见用法是如果您需要从函数返回多个值。以下函数获取一个名称并为用户提供消息：

```
> import String

> goodName name = \
|   if String.length name <= 20 then \
|     (True, "name accepted!") \
|   else \
|     (False, "name was too long; please limit it to 20 characters")

> goodName "Tom"
(True, "name accepted!") 
```

这可能非常方便，但当事情开始变得更加复杂时，通常最好使用记录而不是元组。

## 记录

记录是一组键值对，类似于 JavaScript 或 Python 中的对象。您会发现它们在 Elm 中非常常见和有用！让我们看一些基本示例。

```
> point = { x = 3, y = 4 }
{ x = 3, y = 4 }

> point.x
3

> bill = { name = "Gates", age = 57 }
{ age = 57, name = "Gates" }

> bill.name
"Gates" 
```

因此，我们可以使用花括号创建记录，并使用点访问字段。Elm 还有一种类似函数的记录访问版本。通过以点开头的变量，您在说*请访问以下名称的字段*。这意味着`.name`是一个获取记录的`name`字段的函数。

```
> .name bill
"Gates"

> List.map .name [bill,bill,bill]
["Gates","Gates","Gates"] 
```

在使用记录创建函数时，您可以进行一些模式匹配，使事情变得更加轻松。

```
> under70 {age} = age < 70
<function>

> under70 bill
True

> under70 { species = "Triceratops", age = 68000000 }
False 
```

因此，只要记录中有一个包含数字的`age`字段，我们就可以传入任何记录。

更新记录中的值通常很有用。

```
> { bill | name = "Nye" }
{ age = 57, name = "Nye" }

> { bill | age = 22 }
{ age = 22, name = "Gates" } 
```

需要注意的是我们不进行*破坏性*更新。当我们更新`bill`的一些字段时，实际上是创建一个新记录而不是覆盖现有记录。Elm 通过尽可能共享内容来实现这一点。如果您更新十个字段中的一个，新记录将共享九个未更改的值。

### 比较记录和对象

Elm 中的记录与 JavaScript 中的对象*相似*，但有一些关键的区别。主要区别在于记录：

+   您不能请求不存在的字段。

+   没有字段会是未定义或空值。

+   您不能使用`this`或`self`关键字创建递归记录。

Elm 鼓励严格区分数据和逻辑，并且主要用于打破这种分离的能力。这是 Elm 故意避免的面向对象语言中的系统性问题。

记录还支持[结构类型](https://en.wikipedia.org/wiki/Structural_type_system "结构类型")，这意味着在 Elm 中的记录可以在任何情况下使用，只要必要的字段存在。这为我们提供了灵活性，而不会影响可靠性。
