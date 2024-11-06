# 34 适用于 Racket 和 Schemers 的 Pyret

|     34.1 数字、字符串和布尔值 |
| --- |
|     34.2 中缀表达式 |
|     34.3 函数定义和应用 |
|     34.4 变量名 |
|     34.5 数据定义 |
|     34.6 条件语句 |
|     34.7 注释 |
|     34.8 还有什么？ |

如果您之前在 Scheme 或 Racket 的学生级别（或 WeScheme 编程环境）中编程过，或者在 OCaml、Haskell、Scala、Erlang、Clojure 或其他语言的某些部分中编程过，您会发现 Pyret 的许多部分非常熟悉。本章专门编写，以帮助您从（学生）Racket/Scheme/WeScheme（简称“RSW”）过渡到 Pyret，向您展示如何转换语法。我们说的大部分内容都适用于所有这些语言，尽管在某些情况下，我们会具体提到 Racket（和 WeScheme）中的特性，这些特性在 Scheme 中找不到。

在下面的每个示例中，这两个程序将产生相同的结果。

## 34.1 数字、字符串和布尔值

两者之间的数字非常相似。与 Scheme 一样，Pyret 实现了任意精度的数字和有理数。一些 Scheme 中更奇特的数字系统（如复数）不在 Pyret 中；Pyret 也稍微不同地处理不精确的数字。

| RSW | Pyret |
| --- | --- |
| 1 | 1 |
| RSW | Pyret |
| 1/2 | 1/2 |
| RSW | Pyret |
| #i3.14 | ~3.14 |

字符串也非常相似，尽管 Pyret 也允许您使用单引号。

| RSW | Pyret |
| --- | --- |
| "你好，世界！" | "Hello, world!" |
| RSW | Pyret |
| "\"Hello\", he said" | "\"Hello\", he said" |
| RSW | Pyret |
| "\"Hello\", he said" | '"Hello", he said' |

布尔值具有相同的名称：

| RSW | Pyret |
| --- | --- |
| true | true |
| RSW | Pyret |
| false | false |

## 34.2 中缀表达式

Pyret 使用中缀语法，让人想起许多其他文本编程语言：

| RSW | Pyret |
| --- | --- |
| (+ 1 2) | 1 + 2 |
| RSW | Pyret |
| (* (- 4 2) 5) | (4 - 2) * 5 |

请注意，Pyret 没有关于运算符优先级顺序的规则，因此当您混合运算符时，必须用括号括起表达式以明确您的意图。当您链接相同的运算符时，您不需要使用括号；在这两种语言中，链接都是向左关联的：

| RSW | Pyret |
| --- | --- |
| (/ 1 2 3 4) | 1 / 2 / 3 / 4 |

这两者都计算为 1/24。

## 34.3 函数定义和应用

Pyret 中的函数定义和应用具有中缀语法，更像许多其他文本编程语言。应用使用了一种熟悉的语法，类似于传统代数书籍：

| RSW | Pyret |
| --- | --- |
| (dist 3 4) | dist(3, 4) |

应用在函数头部使用类似的语法，而在主体中使用中缀：

| RSW | Pyret |
| --- | --- |

|

> &#124; (define (dist x y) &#124;
> 
> &#124;   (sqrt (+ (* x x) &#124;
> 
> &#124;            (* y y)))) &#124;

|

```
fun dist(x, y):
  num-sqrt((x * x) +
           (y * y))
end
```

|

## 34.4 变量名

这两种语言对于变量命名都有相当宽松的系统。虽然在两种语言中都可以使用 CamelCase 和 under_scores，但习惯上使用所谓的 [kebab-case](http://c2.com/cgi/wiki?KebabCase)。这个名字是不准确的。单词 “kebab” 只是意味着 “肉”。串是 “shish”。因此，它至少应该被称为 “shish kebab case”。因此：

| RSW | Pyret |
| --- | --- |
| this-is-a-name | this-is-a-name |

尽管 Pyret 具有中缀减法，但语言可以明确区分此名称（一个变量）和此 - 名称（一个减法表达式），因为后者中的 - 必须被空格包围。

尽管有这种空格约定，但 Pyret 不允许 Scheme 允许的一些更奇特的名称。例如，人们可以写

> | (define e^i*pi -1) |
> | --- |

在 Scheme 中，但这不是 Pyret 中的有效变量名。

## 34.5 数据定义

Pyret 在处理数据定义时与 Racket（甚至是 Scheme）不同。首先，我们将看到如何定义一个结构：

| RSW | Pyret |
| --- | --- |
| (define-struct pt (x y)) |

```
data Point:
  &#124; pt(x, y)
end
```

|

这可能看起来有点过度，但我们很快就会看到为什么这很有用。同时，值得注意的是，当您在数据定义中只有一种数据时，占用这么多行会让人感觉不方便。写在一行上是有效的，但现在在中间加上 | 看起来很难看：

```
data Point: | pt(x, y) end
```

因此，Pyret 允许您删除初始 |，从而得到更易读的结果

```
data Point: pt(x, y) end
```

现在假设我们有两种类型的点。在 Racket 的学生语言中，我们会用注释来描述这一点：

> | ;; A Point is either |
> | --- |
> | ;; - (pt number number)，或者 |
> | ;; - (pt3d number number number) |

在 Pyret 中，我们可以直接表达这一点：

```
data Point:
  | pt(x, y)
  | pt3d(x, y, z)
end
```

简而言之，Racket 优化了单变量情况，而 Pyret 优化了多变量情况。因此，在 Racket 中清晰地表达多变量情况很困难，而在 Pyret 中表达单变量情况则很不方便。对于结构，Racket 和 Pyret 都公开了构造函数、选择器和谓词。构造函数只是函数：

| RSW | Pyret |
| --- | --- |
| (pt 1 2) | pt(1, 2) |

谓词也是具有特定命名方案的函数：

| RSW | Pyret |
| --- | --- |
| (pt? x) | is-pt(x) |

它们的行为方式相同（如果参数由该构造函数构造，则返回 true，否则返回 false）。相比之下，在这两种语言中选择是不同的（我们将在下面更多地看到关于选择的内容，以及用例）：

| RSW | Pyret |
| --- | --- |
| (pt-x v) | v.x |

注意，在 Racket 的情况下，pt-x 检查参数是否由 pt 构造，然后提取 x 字段的值。因此，pt-x 和 pt3d-x 是两个不同的函数，两者都不能互换使用。相比之下，在 Pyret 中，.x 提取任何具有该字段的值的 x 字段，而不关注它是如何构造的。因此，我们可以在值上使用 .x，无论它是由 pt 还是 pt3d 构造的（或者实际上是任何具有该字段的东西）。相比之下，cases 确实关注这种区别。

## 34.6 条件

Pyret 中有几种类型的条件，比 Racket 学生语言多一个。

通用条件可以使用 if 来编写，对应于 Racket 的 if，但具有更多的语法。

| RSW | Pyret |
| --- | --- |

|

> &#124; (if full-moon &#124;
> 
> &#124;     "howl" &#124;
> 
> &#124;     "meow") &#124;

|

```
if full-moon:
  "howl"
else:
  "meow"
end
```

|

| RSW | Pyret |
| --- | --- |

|

> &#124; (if full-moon &#124;
> 
> &#124;     "howl" &#124;
> 
> &#124;     (if new-moon &#124;
> 
> &#124;         "bark" &#124;
> 
> &#124;         "meow")) &#124;

|

```
if full-moon:
  "howl"
else if new-moon:
  "bark"
else:
  "meow"
end
```

|

请注意，如果包含 else if，这使得可能在相同缩进级别上列出一系列问题，而 Racket 中的 if 没有这种可能性。Racket 中的相应代码将被编写为

> | (cond |
> | --- |
> |   [full-moon "howl"] |
> |   [new-moon "bark"] |
> |   [else "meow"]) |

以恢复缩进。Pyret 中有一个类似的构造，称为 ask，旨在与 cond 平行：

```
ask:
  | full-moon then: "howl"
  | new-moon then:  "bark"
  | otherwise:      "meow"
end
```

在 Racket 中，我们还使用 cond 来分派数据类型：

> | (cond |
> | --- |
> |   [(pt? v)   (+ (pt-x v) (pt-y v))] |
> |   [(pt3d? v) (+ (pt-x v) (pt-z v))]) |

我们可以在 Pyret 中写出与之紧密平行的内容：

```
ask:
  | is-pt(v)   then: v.x + v.y
  | is-pt3d(v) then: v.x + v.z
end
```

或者甚至是：

```
if is-pt(v):
  v.x + v.y
else if is-pt3d(v):
  v.x + v.z
end
```

（与 Racket 学生语言一样，在 Pyret 版本中，如果条件的任何分支都不匹配，将会发出错误信号。）然而，Pyret 提供了一个专门的语法用于数据定义：

```
cases (Point) v:
  | pt(x, y)    => x + y
  | pt(x, y, z) => x + z
end
```

这检查 v 是否为 Point，提供了一种清晰的语法方式来识别不同的分支，并且可以给每个字段位置提供简洁的本地名称，而不必使用 .x 这样的选择器。一般来说，在 Pyret 中，我们更喜欢使用 cases 处理数据定义。然而，有时候，例如，当数据的变体很多但函数只处理其中很少一部分时。在这种情况下，明确使用谓词和选择器更合理。

## 34.7 注释

在学生 Racket 语言中，注释通常写作注释：

> | ; square: Number -> Number |
> | --- |
> | ; sort-nums: List<Number> -> List<Number> |
> | ; sort: List<T> * (T * T -> Boolean) -> List<T> |

在 Pyret 中，我们可以直接在参数和返回值上写注释。Pyret 将动态地在有限的程度上检查它们，并且可以使用其类型检查器静态地检查它们。以上相应的注释将被编写为

```
fun square(n :: Number) -> Number: ...

fun sort-nums(l :: List<Number>) -> List<Number>: ...

fun sort<T>(l :: List<T>, cmp :: (T, T -> Boolean)) -> List<T>: ...
```

尽管 Pyret 确实有一种写注释的表示法（类似于 Racket 中的注释语法），但目前语言中没有强制执行，因此我们在此不包括它。

## 34.8 还有什么？

如果您希望看到 Scheme 或 Racket 语法的其他部分的翻译，请[告诉我们](http://cs.brown.edu/~sk/Contact/)。
