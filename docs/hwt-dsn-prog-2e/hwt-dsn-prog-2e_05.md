# 间奏曲 1：初学者的语言🔗

> 原文：[`htdp.org/2024-11-6/Book/i1-2.html`](https://htdp.org/2024-11-6/Book/i1-2.html)

|   BSL 词汇 |
| --- |
|   BSL 语法 |
|   BSL 意义 |
|   意义与计算 |
|   BSL 错误 |
|   布尔表达式 |
|   常量定义 |
|   结构类型定义 |
|   BSL 测试 |
|   BSL 错误信息 |

固定大小数据 将 BSL 视为一个自然语言。它介绍了语言的“基本词汇”，建议如何将“词汇”组合成“句子”，并利用你对代数的知识来直观理解这些“句子”。虽然这种介绍在一定程度上是有效的，但真正有效的沟通需要一些正式的学习。

在许多方面，固定大小数据 的类比是正确的。编程语言确实有词汇和语法，尽管程序员用“语法”这个词来指这些元素。BSL 中的一个句子是一个表达式或定义。BSL 的语法规定了如何形成这些短语。但并非所有语法句子都是有意义的——无论是在英语中还是在编程语言中。例如，英语句子“猫是圆的”是一个有意义的句子，但“砖是车”即使完全符合语法，也没有意义。要确定一个句子是否有意义，我们必须了解语言的意义；程序员称这为语义。

本间奏曲将 BSL 介绍得仿佛它是中学熟悉的算术和代数语言的扩展。毕竟，计算始于这种简单的数学形式，我们应该理解这种数学与计算之间的联系。前三部分介绍了 BSL 的大部分语法和语义。程序员最终必须理解这些计算原理，但这些原理与设计原理是相辅相成的。基于对 BSL 的新理解，第四部分继续讨论错误。其余部分扩展了这种理解到完整的语言；最后一部分扩展了表达测试的工具。

### BSL 词汇🔗 "链接至此")

图 39 介绍了并定义了 BSL 的基本词汇。它包括字面常数，例如数字或布尔值；根据 BSL 有意义的名称，例如[cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)或[+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29)；以及程序可以通过[define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29)或函数参数赋予意义的名称。

> > > 名称或变量是一系列字符，不包括空格或以下之一：" , ' ` ( ) [ ] { } | ; #:
> > > 
> > > +   基本上是一个 BSL 赋予意义的名称，例如[+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29)或[sqrt](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._sqrt%29%29)。
> > > +   
> > > +   变量是一个没有预定义意义的名称。
> > > +   
> > > 值是以下之一：
> > > 
> > > +   数字是以下之一：1，-1，3/5，1.22，#i1.22，0+1i，等等。BSL 数字的语法很复杂，因为它适应了多种格式：正数和负数、分数和小数、精确数和不精确数、实数和复数、非十进制基数等。理解数字的确切表示法需要彻底理解语法和解析，这超出了本小节的范围。
> > > +   
> > > +   布尔值是以下之一：#true 或 #false。
> > > +   
> > > +   字符串是以下之一：""，"他说“你好世界”"，"娃娃"，等等。一般来说，它是由一对双引号包围的字符序列。
> > > +   
> > > +   图像是 png，jpg，tiff，以及其他各种格式。我们故意省略了精确的定义。
> > > +   
> > > 当我们想要表达“任何可能的值”时，我们使用 v，v-1，v-2 等等。
> > > 
> 图 39：BSL 核心词汇

每个解释都通过其元素的提示性列举来定义一个集合。尽管可以完全指定这些集合，但我们认为在这里这样做是多余的，并相信你的直觉。只需记住，这些集合中可能包含一些额外的元素。

### BSL 语法🔗 "链接到此处")

图 40 展示了 BSL 语法的大部分内容，与其他语言相比——<wbr>极其简单。至于 BSL 的表达能力，不要被外观所欺骗。然而，首要任务是讨论如何阅读这样的语法。大声朗读语法会使它听起来像数据定义。确实可以使用语法来记录我们许多的数据定义。使用 a = 引入语法类别；发音 = 的最佳方式是“是之一”，而 | 是“或”。无论你在哪里看到三个点，想象你想要的重复次数与点之前的内容相同。这意味着，例如，程序要么什么都没有，要么是 def-expr 的单个出现，或者两个、三个、四个、五个，或者任何你想要的。由于这个例子并不特别具有启发性，让我们看看第二个语法类别。它说明 def 要么是

> ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (变量 变量) 表达式)

因为“尽可能多”包括零，或者

> ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (变量 变量 变量) 表达式)

这是一重重复，或者

> ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (变量 变量 变量 变量) 表达式)

这使用了两个。

> > > |   程序 |   | = |   | 定义表达式... |
> > > | --- | --- | --- | --- | --- |
> > > |   |   |   |   |   |
> > > |   定义表达式 |   | = |   | 定义 |
> > > |   |   | &#124; |   | 表达式 |
> > > |   |   |   |   |   |
> > > |   定义 |   | = |   | ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (变量 变量 变量 ...) 表达式) |
> > > |   |   |   |   |   |
> > > |   表达式 |   | = |   | 变量 |
> > > |   |   | &#124; |   | 值 |
> > > |   |   | &#124; |   | (原始表达式 表达式 ...) |
> > > |   |   | &#124; |   | (变量 表达式 表达式 ...) |
> > > |   |   | &#124; |   | ([条件](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) [表达式 表达式] ... [表达式 表达式]) |
> > > |   |   | &#124; |   | ([条件](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) [表达式 表达式] ... [[否则](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) 表达式]) |
> > > 
> 图 40: BSL 核心语法

关于语法的最后一点涉及三个以特殊字体呈现的“单词”：[定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29)、[条件](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)和[否则](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29)。根据 BSL 词汇的定义，这三个单词是名称。词汇定义没有告诉我们的是，这些名称具有预定义的含义。在 BSL 中，这些单词作为标记，区分了一些复合句与其他句子，为了认可它们的作用，这些词被称为关键字。

现在我们准备陈述语法的目的。编程语言的语法决定了如何从语法的词汇表中形成句子。有些句子仅仅是词汇表中的元素。例如，根据图 40 42 是一个 BSL 的句子：

+   第一个句法类别说明程序是一个 def-expr。表达式可以引用定义。

+   第二点告诉我们，def-expr 要么是 def，要么是 expr。在 DrRacket 中，一个程序实际上由两个不同的部分组成：定义区域和交互区域中的表达式。

+   最后一个定义列出了形成 expr 的所有方式，其中第二个是值。

由于我们从图 39 中知道 42 是一个值，我们得到了确认。

语法中有趣的部分展示了如何形成复合句，即由其他句子构建的句子。例如，def 部分告诉我们，函数定义是通过使用“（”，然后是关键字[定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29)，然后是另一个“（”，然后是一系列至少两个变量，然后是“）”，然后是一个 expr，最后由与第一个相匹配的右括号“）”关闭。注意，前导关键字[定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29)如何区分定义和表达式。

表达式（expr）有六种类型：变量、常量、原始应用、（函数）应用和两种类型的 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 件。虽然前两种是原子句子，但后四种是复合句子。像 [define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) 一样，关键字 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 区分条件表达式和应用。

这里有三个表达式的例子：“all”，x，和 (f  x)。第一个属于字符串类，因此是一个表达式。第二个是变量，每个变量都是一个表达式。第三个是函数应用，因为 f 和 x 都是变量。

相比之下，以下括号内的句子不是合法的表达式：(f  [define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29))，([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)  x)，和 ((f  2)  10)。第一个部分匹配函数应用的形状，但它将 [define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) 当作变量使用。第二个因为第二个项包含一个变量而不是括号内的表达式对，所以不是一个正确的 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 表达式。最后一个既不是条件语句也不是应用，因为第一部分是一个表达式。

最后，你可能注意到语法并没有提到空白：空格、制表符和换行符。BSL 是一种宽容的语言。只要程序中任何序列的元素之间有一些空白，DrRacket 就能理解你的 BSL 程序。优秀的程序员请注意，有两种读者会研究你的 BSL 程序：人和 DrRacket。然而，他们可能不喜欢你所写的代码。这些程序员使用空白来使他们的程序易于阅读。最重要的是，他们采用一种优先考虑人类读者而不是处理程序的软件应用（如 DrRacket）的风格。他们从仔细阅读书籍中的代码示例中吸取这种风格，注意它们的格式。

练习 116。看看以下句子：

1.  x

1.  ([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29)  y  z)

1.  ([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29)  ([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29)  y  z)  0)

解释为什么它们是语法上合法的表达式练习 117。考虑以下句子：

1.  (3  [+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29)  4)

1.  [number?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._number~3f%29%29)

1.  (x)

解释为什么它们是语法上非法的。练习 118。看看以下句子：

1.  ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29)  (f  x)  x)

1.  ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29)  (f  x)  y)

1.  ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29)  (f  x  y)  3)

解释为什么它们是语法上合法的定义练习 119。考虑以下句子：

1.  ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29)  (f  "x")  x)

1.  ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29)  (f  x  y  z)  (x))

解释为什么它们是语法上非法的。练习 120。区分合法句子和非法句子：

1.  (x)

1.  ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29)  1  ([not](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._not%29%29)  x))

1.  ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29)  1  2  3)

解释为什么这些句子是合法的或非法的。确定合法的句子属于 expr 或 def 类别。

关于语法术语的说明复合句的组成部分有名称。我们已经在非正式的基础上介绍了一些这些名称。图 41 提供了惯例的总结。

> > > | ; function application: |
> > > | --- |
> > > | (function argument [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) argument) |
> > > |   |
> > > | ; function definition: |
> > > | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (function-name parameter [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) parameter) |
> > > |   function-body) |
> > > |   |
> > > | ; 条件表达式： |
> > > | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) |
> > > |   cond-clause |
> > > |   [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) |
> > > |   cond-clause) |
> > > |   |
> > > | ; [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) clause |
> > > | [条件 答案] |
> > > 
> 图 41：语法命名约定

除了图 41 中的术语之外，我们还称定义的第二部分为函数头。相应地，表达式部分被称为函数体。将编程语言视为数学形式的人使用左侧作为头，右侧作为体。有时，你也会听到或读到函数应用中参数的实际参数这个术语。结束

### BSL 意义🔗 "链接到此处")

当你在键盘上按下回车键并要求 DrRacket 评估一个表达式时，它使用算术和代数定律来获得一个值。对于迄今为止处理的 BSL 变体，图 39 在语法上定义了什么是值——值集只是所有表达式的一个子集。该集合包括布尔值、字符串和图像。

评估规则分为两类。无限数量的规则，如算术规则，解释了如何确定原始操作应用于值时的值：

> | ([(+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) 1 1) == 2) |
> | --- |
> | ([(-](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._-%29%29) 2 1) == 1) |
> | [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) |

记住==表示根据 BSL 的计算定律，两个表达式是相等的。但 BSL 的算术比仅仅进行数字运算更通用。它还包括处理布尔值、字符串等规则的规则：

> | ([not](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._not%29%29) #true)        == #false |
> | --- |
> | ([string=?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._string~3d~3f%29%29) "a" "a") == #true |
> | [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) |

就像在代数中一样，你总是可以用等于替换等于；参见图 42 中的示例计算。

> > > | ([boolean?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._boolean~3f%29%29) ([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) ([string-length](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._string-length%29%29) ([string-append](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._string-append%29%29) "h" "w")) |
> > > | --- |
> > > |           ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29)  1  3))) |
> > > | == |
> > > | ([boolean?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._boolean~3f%29%29) ([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) ([string-length](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._string-length%29%29) ([string-append](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._string-append%29%29)  "h"  "w")) 4)) |
> > > | == |
> > > | ([boolean?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._boolean~3f%29%29) ([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) ([string-length](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._string-length%29%29)  "hw") 4)) |
> > > | == |
> > > | ([boolean?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._boolean~3f%29%29) ([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29)  2  4)) |
> > > | == |
> > > | ([boolean?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._boolean~3f%29%29)  #false) |
> > > | == #true |
> > > 
> 图 42：用等于替换等于

其次，我们需要从代数中获取一条规则来理解函数对参数的应用。假设程序包含以下定义

> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (f x-1 [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) x-n) |
> | --- |
> |   f-body) |

函数的应用受以下法则控制：

> | (f v-1 [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) v-n) == f-body |
> | --- |
> | ; 用所有出现的 x-1 [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) x-n |
> | ; 用 v-1 ... v-n 分别替换 |

由于 BSL 等语言的历史，我们称此规则为 beta 或查看使用 lambda 进行计算以了解更多关于此规则的信息。beta 值规则。此规则尽可能普遍地制定，因此最好查看一个具体的例子。比如说定义是

> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (poly x y) |
> | --- |
> |   ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) ([expt](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._expt%29%29) 2 x) y)) |

然后 DrRacket 得到表达式(poly 3 5)。在表达式的评估过程中的第一步使用 beta 规则：

> (poly 3 5) == ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) ([expt](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._expt%29%29) 2 3) 5) [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) == ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) 8 5) == 13

除了 beta 规则外，我们还需要确定[cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)表达式值的规则。即使这些规则不是作为标准课程的一部分明确教授，它们也是代数规则。当第一个条件为#false 时，第一个[cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)行消失，其余行保持不变：

> | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) == ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) |
> | --- |
> |   [#false [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29)]               ; 第一行已删除 |
> |   [condition2 answer2]       [condition2 answer2] |
> |   [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29))                       [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29)) |

这条规则被命名为 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)false。以下是 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)true 的示例：

> | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)                    == answer-1 |
> | --- |
> |   [#true answer-1] |
> |   [condition2 answer2] |
> |   [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29)) |

当第一个条件是 [else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) 时，此规则同样适用。考虑以下评估：

> | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)) |
> | --- |
> |   [([zero?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._zero~3f%29%29) 3) 1] |
> |   [([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) 3 3) ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) 1 1)] |
> |   [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) 3]] |
> | == ; 通过普通算术和等于等于 |
> | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)) |
> |   [#false 1] |
> |   [([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) 3 3) ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) 1 1)] |
> |   [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) 3]] |
> | == ; 通过规则 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)false |
> | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)) |
> |   [([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) 3 3) ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) 1 1)] |
> |   [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) 3]) |
> |   |
> |   |
> |   |
> |   |
> | == ; 通过普通算术和等号替换等号 |
> | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) |
> |   [#true ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) 1 1)] |
> |   [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) 3]) |
> | == ; 通过规则 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)true |
> | ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) 1 1) |

计算展示了普通算术规则、等号替换等号以及 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 规则。练习 121. 逐步评估以下表达式：

1.  | ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) 12 8) 2/3) |
1.  | --- |
    |    ([-](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._-%29%29) 20 ([sqrt](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._sqrt%29%29) 4))) |
1.  | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) |
    |   [([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) 0 0) #false] |
    |   [([>](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3e%29%29) 0 1) ([string=?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._string~3d~3f%29%29) "a" "a")] |
    |   [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) ([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) 1 0) 9)]) |
1.  | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) |
    |   [([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) 2 0) #false] |
    |   [([>](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3e%29%29) 2 1) ([string=?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._string~3d~3f%29%29) "a" "a")] |
    |   [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) ([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29)  1 2) 9)]) |

使用 DrRacket 的步进器来确认你的计算。练习 122。假设程序包含以下定义：

> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (f x y) |
> | --- |
> |   ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 3 x) ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) y y))) |

展示 DrRacket 如何逐步评估以下表达式：

1.  ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) (f 1 2) (f 2 1))

1.  (f 1 ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 2 3))

1.  (f (f 1 ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 2 3)) 19)

使用 DrRacket 的步进器来确认你的计算。

### 意义与计算🔗 "链接至此")

DrRacket 中的步进器工具模仿了预代数课程中的学生。与您不同，步进器在应用这里阐述的算术和代数法则方面非常出色，并且也非常快速。科学家称步进器是 DrRacket 评估机制的模型。精炼解释器部分介绍了另一个模型，即解释器。

当你不懂新的语言结构如何工作时，你应该使用步进器。计算部分建议了这方面的练习，但你也可以自己编一些例子，通过步进器运行它们，并思考为什么它采取某些步骤。

最后，当你对程序计算出的结果感到惊讶时，你可能也想使用步进器。有效地使用步进器这种方式需要练习。例如，这通常意味着复制程序并修剪不必要的部分。但一旦你学会了如何有效地使用步进器，你会发现这种方法可以清楚地解释程序中的运行时错误和逻辑错误。

### BSL 错误🔗 "链接到此处")

当 DrRacket 发现某些括号内的短语不属于 BSL 时，它会发出语法错误。为了确定一个完全括号化的程序是否语法正确，DrRacket 使用 图 40)) 中的语法，并按照上述解释的思路进行推理。然而，并非所有语法正确的程序都有意义。

当 DrRacket 评估一个语法正确的程序并发现某些操作被用于错误类型的值时，它会引发运行时错误。考虑语法正确的表达式（[/(http://docs.racket-lang.org/htdp-langs/beginner.html#(def._htdp-beginner._((lib._lang/htdp-beginner..rkt)_/))) 1 0），正如你所知，从数学上讲，它没有值。由于 BSL 的计算必须与数学一致，DrRacket 会发出错误信号：

> | > ([/(http://docs.racket-lang.org/htdp-langs/beginner.html#(def._htdp-beginner._((lib._lang/htdp-beginner..rkt)_/))) 1 0) |
> | --- |
> | 除以零 |

自然地，当表达式（如[/(http://docs.racket-lang.org/htdp-langs/beginner.html#(def._htdp-beginner._((lib._lang/htdp-beginner..rkt)_/))) 1 0）深深嵌套在另一个表达式内部时，它也会表示一个错误：

> | > ([+(http://docs.racket-lang.org/htdp-langs/beginner.html#(def._htdp-beginner._((lib._lang/htdp-beginner..rkt)_+))) (* (http://docs.racket-lang.org/htdp-langs/beginner.html#(def._htdp-beginner._((lib._lang/htdp-beginner..rkt)_*)) 20 2) (/ (http://docs.racket-lang.org/htdp-langs/beginner.html#(def._htdp-beginner._((lib._lang/htdp-beginner..rkt)_/))) 1 (- (http://docs.racket-lang.org/htdp-langs/beginner.html#(def._htdp-beginner._((lib._lang/htdp-beginner..rkt)_-))) 10 10))) |
> | --- |
> | 除以零 |

DrRacket 的行为转化为我们的计算如下。当我们找到一个不是值的表达式，并且评估规则不允许进一步简化时，我们说计算陷入停滞。这种停滞的概念对应于运行时错误。例如，计算上述表达式的值会导致停滞状态：

> | ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 20 2) ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) 1 ([-](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._-%29%29) 10 10))) |
> | --- |
> | == |
> | ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 20 2) ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) 1 0)) |
> | == |
> | ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) 40 ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) 1 0)) |

这种计算还表明，DrRacket 在报告错误时会消除一个卡住的表达式的上下文。在这个具体的例子中，它会消除将 40 加到卡住的表达式 ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) 1 0) 上的操作。并非所有嵌套的卡住表达式最终都会报告错误。假设一个程序包含以下定义：

> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (my-divide n) |
> | --- |
> |    ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) |
> |     [([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) n 0) "inf"] |
> |   [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) 1 n)])) |

如果你现在将 my-divide 应用于 0，DrRacket 将按照以下方式计算：

> |   (my-divide 0) |
> | --- |
> | == |
> |   ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) |
> |    [([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) 0 0) "inf"] |
> |   [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29)  1  0)]) |

显然，不能说函数现在会报告除以零错误，即使对阴影子表达式的评估可能会暗示这一点。原因是 ([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29)  0  0) 评估为 #true，因此第二个 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 子句没有任何作用：

> | (my-divide 0) |
> | --- |
> | == |
> | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) |
> |   [([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) 0 0) "inf"] |
> |   [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29)  1  0)]) |
> | == |
> | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) |
> |   [#true "inf"] |
> |   [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29)  1  0)]) |
> | == "inf" |

幸运的是，我们的评估法则会自动处理这些情况。我们只需要记住它们何时适用。例如，在

> ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 20 2) ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) 20 2))

加法不能在乘法或除法之前进行。同样，阴影中的除法

> | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) |
> | --- |
> |   [([=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) 0 0) "inf"] |
> | （[否则](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) ([除法](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) 1 0)]) |

不能在相应的行是 [条件](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 的第一个条件之前替换完整的 [条件](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 表达式。一般来说，最好记住以下几点：

> 总是选择最外层且最左侧的嵌套表达式进行评估。

虽然这个指南看起来很简单，但它总是解释了 BSL 的结果。在某些情况下，程序员还想要定义会引发错误的函数。回想一下来自 输入错误 的已检查的磁盘区域版本：

> | ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (已检查的磁盘区域 v) |
> | --- |
> | （[条件](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)） |
> |     [([数字?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._number~3f%29%29) v) (磁盘区域 v)] |
> |     [[否则](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) ([错误](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._error%29%29) "期望数字")]]) |

现在想象将已检查的磁盘区域应用于一个字符串：

> | ([减法](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._-%29%29) ([已检查的磁盘区域 "a"]) |
> | --- |
> |     (已检查的磁盘区域 10)) |
> | == |
> | ([减法](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._-%29%29) ([条件](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) |
> |     [([数字?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._number~3f%29%29) "a") (磁盘区域 "a")] |
> |     [[否则](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) ([错误](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._error%29%29) "期望数字")]] |
> | （已检查的磁盘区域 10） |
> | == |
> | ([-](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._-%29%29) ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) |
> |        [#false (area-of-disk "a")] |
> |        [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) ([error](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._error%29%29) "number expected")]] |
> |        (checked-area-of-disk 10)) |
> | == |
> | ([-](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._-%29%29) ([error](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._error%29%29) "number expected") |
> |        (checked-area-of-disk 10)) |

在这一点上，你可能尝试评估第二个表达式，即使你发现其结果大约是 314，你的计算最终也必须处理 [error](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._error%29%29) 表达式，它就像一个卡住的表达式。简而言之，计算以

> ([error](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._error%29%29) "number expected")

### 布尔表达式🔗 "链接到此处")

我们当前对 BSL 的定义省略了 [or](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._or%29%29) 和 [and](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) 表达式。添加它们提供了一个如何研究新语言构造的案例研究。我们首先必须理解它们的语法，然后是它们的语义。

这里是表达式的修订语法：

|    expr |    | = |    | ... |
| --- | --- | --- | --- | --- |
|    |    | |    | ([and](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) expr expr) |
|        |        | |        | ([or](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._or%29%29) expr expr) |

语法说明 [and](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) 和 [or](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._or%29%29) 是关键字，每个后面跟两个表达式。它们不是函数应用。

要理解为什么 [并且](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) 和 [或](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._or%29%29) 不是 BSL 定义的函数，我们首先必须看看它们的语用学。假设我们需要制定一个条件来确定 ([除以](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) 1 n) 是否等于 r：

> | ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (check n r) |
> | --- |
> |   ([并且](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) ([非](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._not%29%29) ([等于](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) n 0)) ([等于](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) ([除以](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) 1 n) r))) |

我们将这个条件作为 [并且](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) 组合来制定，因为我们不希望不小心除以 0。现在让我们将 check 应用于 0 和 1/5：

> | (check 0 1/5) |
> | --- |
> | == ([并且](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) ([非](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._not%29%29) ([等于](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) 0 0)) ([等于](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3d%29%29) ([除以](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) 1 0) 1/5)) |

如果 [and](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) 是一个普通操作，我们就必须评估两个子表达式，这样做会触发一个错误。相反，[and](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) 在第一个表达式为 #false 时，简单地不会评估第二个表达式，这意味着 [and](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) 会短路评估。为 [and](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) 和 [or](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._or%29%29) 制定评估规则会很容易。另一种解释它们意义的方法是将它们翻译成其他表达式：为了确保 expr-2 评估为布尔值，这些缩写应该使用 ([if](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._if%29%29) expr-2 #true #false)) 而不是仅仅 expr-2。我们在这里忽略了这个细节。

> | ([and](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) expr-1 expr-2) |  | 是 |  |
> | --- | --- | --- | --- |
> 
> [[cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)] &#124;
> 
> [[expr-1 expr-2]] &#124;
> 
> [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) #false] &#124;
> 
> |

和

> | ([or](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._or%29%29) expr-1 expr-2) |  | 是 |  |
> | --- | --- | --- | --- |
> 
> [[cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)] &#124;
> 
> [[expr-1 #true]] &#124;
> 
> [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) expr-2]] &#124;
> 
> |

所以，如果你对如何评估一个 [and](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) 或 [or](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._or%29%29) 表达式有疑问，请使用上述等价性进行计算。但我们相信你直觉上理解了这些操作，这通常就足够了。练习 123。如果你对 [if](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._if%29%29) 的使用感到惊讶，可能是因为这个插曲没有在其他地方提到这个形式。简而言之，这个插曲似乎是用没有解释的形式来解释 [and](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29)。在这个点上，我们依赖于你对 [if](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._if%29%29) 作为 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 简写的直觉理解。写下一条规则，说明如何重新表述

> ([if](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._if%29%29) expr-test expr-then expr-else)

作为一个 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 表达式。

### 常量定义🔗 "链接到此处")

程序不仅包括函数定义，还包括常量定义，但我们的第一个语法中没有包括这些。因此，这里有一个扩展的语法，它包括了常量定义：

> | 定义 | | = | | ... |
> | --- | --- | --- | --- | --- |
> | | | | | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) name expr) |

常量定义的形状与函数定义类似。虽然关键字 [define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) 将常量定义与表达式区分开来，但它并不区分函数定义。实际上，DrRacket 处理函数定义还有另一种方式；参见 无名称函数。为此，读者必须查看定义的第二部分。接下来，我们必须理解常量定义的含义。对于右侧有文字常量的常量定义，例如

> ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) RADIUS 5)

变量只是值的简写。无论 DrRacket 在评估过程中遇到 RADIUS，它都会将其替换为 5。对于右侧有正确表达式的定义，例如，

> ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) DIAMETER ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 2 RADIUS))

我们必须立即确定表达式的值。这个过程使用了在此常量定义之前的所有定义。因此，

> | ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) RADIUS 5) |
> | --- |
> | ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) DIAMETER ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 2 RADIUS)) |

等价于

> | ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) RADIUS 5) |
> | --- |
> | ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) DIAMETER 10) |

这个过程甚至涉及函数定义时也适用：

> | ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) RADIUS 10) |
> | --- |
> | ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) DIAMETER ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 2 RADIUS)) |
> | ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (area r) ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 3.14 ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) r r))) |
> | ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) AREA-OF-RADIUS (area RADIUS)) |

当 DrRacket 遍历这个定义序列时，它首先确定 RADIUS 代表 10，DIAMETER 代表 20，而 area 是函数的名称。最后，它评估(area RADIUS)得到 314，并将 AREA-OF-RADIUS 与该值关联。混合常量和函数定义也会引发一种新的运行时错误。看看这个程序：

> | ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) RADIUS 10) |
> | --- |
> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) DIAMETER ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 2 RADIUS)) |
> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) AREA-OF-RADIUS (area RADIUS)) |
> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (area r) ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 3.14 ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) r r))) |

这与上面的例子类似，只是最后两个定义的位置互换了。对于前两个定义，评估过程与之前相同。然而，对于第三个定义，评估出现了问题。这个过程需要评估 (area RADIUS)。虽然 RADIUS 的定义在表达式之前，但 area 的定义尚未遇到。如果你用 DrRacket 评估这个程序，你会得到一个错误，解释说“这个函数未定义。”因此，在使用常量定义中仅当你知道它们已定义时才使用函数。练习 124：逐步评估以下程序：

> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) PRICE 5) |
> | --- |
> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) SALES-TAX ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 0.08 PRICE)) |
> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) TOTAL ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) PRICE SALES-TAX)) |

以下程序的评估是否会产生错误？

> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) COLD-F 32) |
> | --- |
> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) COLD-C (fahrenheit->celsius COLD-F)) |
> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (fahrenheit->celsius f) |
> |  ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 5/9 ([-](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._-%29%29) f 32))) |

怎么样，下一个呢？

> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) LEFT -100) |
> | --- |
> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) RIGHT 100) |
> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (f x) ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) ([*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29) 5 ([expt](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._expt%29%29) x 2)) 10)) |
> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) f@LEFT (f LEFT)) |
> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) f@RIGHT (f RIGHT)) |

使用 DrRacket 的步进器检查你的计算。

### 结构类型定义🔗 "链接到此处")

如你所想，[define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) 是最复杂的 BSL 结构。因此，我们将解释留到最后。以下是语法：

> |   定义 |   | = |   | ... |
> | --- | --- | --- | --- | --- |
> |   |   | &#124; |   | ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) name [name ...]) |

结构类型定义是定义的第三种形式。关键字将其与函数和常量定义区分开来。以下是一个简单的例子：

> ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) point [x y z])

由于点、x、y 和 z 是变量，括号的位置是根据语法模式放置的，因此这是一个结构类型的正确定义。相比之下，这两个括号内的句子

> | ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) [point x y z]) |
> | --- |
> | ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) point x y z) |

是非法定义，因为[define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29)后面没有跟一个单变量名和括号中的变量序列。虽然[define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29)的语法简单，但其含义难以用评估规则表达。正如多次提到的，[define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29)定义一次定义了多个函数：一个构造函数，几个选择器和一个谓词。因此，对以下内容的评估：

> ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) c [s-1 [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) s-n])

将以下函数引入程序中：

1.  make-c：一个构造函数；

1.  c-s-1...  c-s-n：一系列选择器；以及

1.  c?: 一个谓词。

这些函数与[+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29)，[-](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._-%29%29)，或[*](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2A%29%29)具有相同的地位。然而，在我们理解这些新函数的规则之前，我们必须回到值的定义。毕竟，[define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29)的一个目的就是引入一个与所有现有值都不同的值的类别。简单来说，使用[define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29)扩展了值的宇宙。首先，它现在也包含结构，将几个值组合成一个。当程序包含一个[define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29)定义时，其评估会修改值的定义：

> 一个值可以是以下之一：一个数字，一个布尔值，一个字符串，一个图像，
> 
> +   或者一个结构值：
> +   
>     > | (make-c _value-1 [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) _value-n) |
>     > | --- |
>     > 
>     假设已定义了一个结构类型 c。

例如，点的定义添加了这种形状的值：

> | (make-point 1 2 -1) |
> | --- |
> | (make-point "one" "hello" "world") |
> | (make-point 1 "one" (make-point 1 2 -1)) |
> | [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) |

现在我们已经可以理解新函数的评估规则。如果 c-s-1 应用到一个 c 结构上，它返回值的第一个组件。同样，第二个选择器提取第二个组件，第三个选择器提取第三个组件，依此类推。新数据构造函数和选择器之间的关系可以用添加到 BSL 规则中的 n 个方程来最好地描述：

> | (c-s-1 (make-c V-1 [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) V-n)) == V-1 |
> | --- |
> | (c-s-n (make-c V-1 [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) V-n)) == V-n |

对于我们的运行示例，我们得到具体的方程

> | (point-x (make-point V U W)) == V |
> | --- |
> | (point-y (make-point V U W)) == U |
> | (point-z (make-point V U W)) == W |

当 DrRacket 看到表达式 (point-y  (make-point  3  4  5)) 时，它将表达式替换为 4，而 (point-x  (make-point  (make-point  1  2  3)  4  5)) 的评估结果为 (make-point  1  2  3)。谓词 c? 可以应用于任何值。如果值是类型 c，则返回 #true，否则返回 #false。我们可以将这两部分翻译成两个方程：

> | (c? (make-c V-1 [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29) V-n)) == #true |
> | --- |
> | (c? V)                    == #false |

如果 V 是一个不是用 make-c 构造的值。再次，这些方程最好通过我们的例子来理解：

> | (point? (make-point U V W)) == #true |
> | --- |
> | (point? X)                  == #false |

如果 X 是一个值但不是点结构。练习 125。区分合法句子和非法句子：

1.  ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) oops  [])

1.  ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) child  [parents  dob  date])

1.  ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29)  (child  person)  [dob  date])

解释为什么这些句子是合法的或不合法的。练习 126。在假设 area 包含这些结构类型定义的情况下，识别以下表达式中的值：

> | ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) point [x y z]) |
> | --- |
> | ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) none  []) |

1.  (make-point  1  2  3)

1.  (make-point  (make-point  1  2  3)  4  5)

1.  (make-point  ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29)  1  2)  3  4)

1.  (make-none)

1.  (make-point  (point-x  (make-point  1  2  3))  4  5)

解释为什么这些表达式是值或不是值。练习 127。假设程序包含

> ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) ball [x y speed-x speed-y])

预测以下表达式的评估结果：

1.  ([number?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._number~3f%29%29)  (make-ball  1  2  3  4))

1.  (ball-speed-y  (make-ball  ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29)  1  2)  ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29)  3  3)  2  3))

1.  (ball-y  (make-ball  ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29)  1  2)  ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29)  3  3)  2  3))

1.  (ball-x  ([make-posn](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._make-posn%29%29)  1  2))

1.  (ball-speed-y  5)

在交互区域和步进器中检查你的预测。

> > > | |  定义表达式 |   | = |   | 定义 |
> > > | --- | --- | --- | --- | --- | --- |
> > > |   |   | &#124; |   | 表达式 |
> > > |   |   | &#124; |   | 测试用例 |
> > > |   |   |   |   |   |
> > > |   定义 |   | = |   | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (name variable variable ...) expr) |
> > > |   |   | &#124; |   | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) name expr) |
> > > |   |   | &#124; |   | ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) name [name ...]) |
> > > |   |   |   |   |   |
> > > |   表达式 |   | = |   | (name expr expr ...) |
> > > |   |   | &#124; |   | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) [expr expr] ... [expr expr]) |
> > > |   |   | &#124; |   | ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) [expr expr] ... [[else](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) expr]) |
> > > |   |   | &#124; |   | ([and](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._and%29%29) expr expr expr ...) |
> > > | |   |   | &#124; |   | ([or](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._or%29%29) expr expr expr ...) |
> > > | |   |   | &#124; |   | 名称 |
> > > |   |   | &#124; |   | 数字 |
> > > |   |   | &#124; |   | 字符串 |
> > > |   |   | &#124; |   | 图片 |
> > > |   |   |   |   |   |
> > > | |   测试用例 |   = |   |   ([check-expect](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-expect%29%29) expr expr) |
> > > |   |   | &#124; |   | ([check-within](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-within%29%29) expr expr expr) |
> > > |   |   | &#124; |   | ([check-member-of](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-member-of%29%29) expr expr ...) |
> > > |   |   | &#124; |   | ([check-range](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-range%29%29) expr expr expr) |
> > > | |   |   | &#124; |   | ([check-error](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-error%29%29) expr) |
> > > |   |   | &#124; |   | ([check-random](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-random%29%29) expr expr) |
> > > |   |   | &#124; |   | ([check-satisfied](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-satisfied%29%29) expr name) |
> > > 
> 图 43：BSL，完整语法

### BSL 测试🔗 "链接到此处")

图 43 展示了 BSL 的所有内容以及一些测试形式。

测试表达式的总体含义很容易解释。当你点击“运行”按钮时，DrRacket 会收集所有测试表达式并将它们移动到程序末尾，保持它们出现的顺序。然后评估定义区域的内容。每个测试都会评估其部分，然后通过某个谓词与预期结果进行比较。除此之外，测试还会与 DrRacket 通信，收集一些统计数据和有关如何显示测试失败的信息。

有关详细信息，请阅读这些测试形式的文档。以下是一些示例：

> | ; [check-expect](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-expect%29%29) 比较结果和预期值与 [equal?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._equal~3f%29%29) |
> | --- |
> | ([check-expect](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-expect%29%29) 3 3) |
> | |   |
> | ; [check-member-of](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-member-of%29%29)将结果与预期值与[equal?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._equal~3f%29%29)进行比较 |
> | ; 如果其中之一返回#true，则测试成功 |
> | ([check-member-of](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-member-of%29%29) "green" "red" "yellow" "green") |
> |   |
> | ; [check-within](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-within%29%29)使用谓词比较结果和预期值 |
> | ; 类似于[equal?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._equal~3f%29%29)，但允许每个不精确数字有 epsilon 的容差 |
> | ([check-within](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-within%29%29) ([make-posn](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._make-posn%29%29) #i1.0 #i1.1) ([make-posn](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._make-posn%29%29) #i0.9 #i1.2) 0.2) |
> |   |
> | ; [check-range](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-range%29%29)与[check-within](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-within%29%29)类似 |
> | 但允许指定一个区间 |
> | ([check-range](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-range%29%29) 0.9 #i0.6 #i1.0) |
> |   |
> | ; [check-error](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-error%29%29)检查表达式是否引发（任何）错误 |
> | ([check-error](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-error%29%29) ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) 1 0)) |
> |   |
> | ; [check-random](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-random%29%29)评估对[random](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._random%29%29)的调用序列 |
> | ; 两个表达式，它们返回相同的数字 |
> | ([检查随机数](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-random%29%29) ([创建位置](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._make-posn%29%29) ([随机数](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._random%29%29) 3) ([随机数](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._random%29%29) 9))) |
> |               ([创建位置](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._make-posn%29%29) ([随机数](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._random%29%29) 3) ([随机数](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._random%29%29) 9))) |
> |   |
> | ; [检查满意](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-satisfied%29%29) 判断谓词是否产生 #true |
> | ; 当应用于结果时，即结果是否具有某种属性 |
> | ([检查满意](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-satisfied%29%29) 4 [even?](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._even~3f%29%29)) |

所有上述测试均成功。本书的剩余部分将根据需要重新引入这些测试形式。练习 128。将以下测试复制到 DrRacket 的定义区域：

> | ([检查成员](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-member-of%29%29) "green" "red" "yellow" "grey") |
> | --- |
> | ([检查在范围内](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-within%29%29) ([创建位置](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._make-posn%29%29) #i1.0 #i1.1) |
> |               ([创建位置](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._make-posn%29%29) #i0.9 #i1.2)  0.01) |
> | ([检查范围](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-range%29%29) #i0.9 #i0.6 #i0.8) |
> | ([检查随机](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-random%29%29) ([创建位置](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._make-posn%29%29) ([随机](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._random%29%29) 3) ([随机](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._random%29%29) 9)) |
> | |   ([创建位置](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._make-posn%29%29) ([随机](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._random%29%29) 9) ([随机](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._random%29%29) 3))) |
> | ([检查满足](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._check-satisfied%29%29) 4 [奇数？](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._odd~3f%29%29)) |

验证所有这些条目都失败，并解释原因。

### BSL 错误信息🔗 "链接到此处")

BSL 程序可能会显示许多种语法错误。虽然我们开发了 BSL 及其错误报告系统，专门针对新手，他们按照定义会犯错误，但错误信息需要一些时间来适应。

下面我们展示了你可能会遇到的各种错误信息。列表中的每个条目由三部分组成：

+   引发错误信息的代码片段；

+   错误信息；并且

+   对错误进行解释并提出如何修复错误的建议。

考虑以下示例，这是你可能会看到的最糟糕的错误信息：

|

&#124;

&#124; ([定义](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (绝对 n) &#124;

&#124;   ([条件](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) &#124;

&#124;   [[<](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3c%29%29) 0 ([-](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._-%29%29) n)] &#124;

&#124;   [[否则](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._else%29%29) n])) &#124;

&#124;

&#124; 预期一个函数调用，但在此函数之前没有开括号；

| 一个 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 表达式由关键字后跟一个任意长度的 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 子句序列组成。反过来，每个子句由两部分组成：一个条件和答案，这两者都是表达式。在这个绝对值的定义中，第一个子句以 [<](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3c%29%29) 开始，这应该是一个条件，但根据我们的定义甚至不是一个表达式。这使得 BSL 非常困惑，以至于它甚至“看不到” [<](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3c%29%29) 左边的开括号。修复方法是使用 ([<](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3c%29%29)  n  0) 作为条件。 |
| --- |

函数定义中 [<](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3c%29%29) 的突出显示指向错误。在定义下方，你可以看到如果你点击 RUN，DrRacket 在交互窗口中显示的错误信息。研究错误解释的右侧，了解如何解决这个有些自相矛盾的信息。现在请放心，没有其他错误信息甚至接近如此晦涩难懂。

因此，当出现错误并且你需要帮助时，找到适当的图，搜索条目以找到匹配项，然后研究完整的条目。

BSL 中关于函数应用的错误信息

假设定义区域包含以下内容，没有其他内容：

> | ; Number  Number -> Number |
> | --- |
> | ; 查找 x 和 y 的平均值 |
> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (average x y) |
> |   ([/](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2F%29%29) ([+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) x y) |
> |      2)) |

点击 RUN 按钮。现在你可能遇到以下错误信息。

|

&#124; (f 1) &#124;

&#124; f: 这个函数未定义 &#124;

| 应用名称 f 作为函数，但 f 在定义区域中未定义。定义该函数，或确保变量名拼写正确。 |
| --- |

|

&#124; (1 3 "three" #true) &#124;

&#124; 函数调用：在开括号后期望一个函数，但找到一个数字 &#124;

| 一个开括号必须始终后面跟着一个关键字或函数名，1 既不是关键字也不是函数名。函数名要么由 BSL 定义，比如 [+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29)，要么在定义区域中定义，比如 average。 |
| --- |

|

&#124; (average  7) &#124;

&#124; average: expects 2 arguments, but found only 1 &#124;

| 这个函数调用对一个参数 7 应用了平均值，尽管其定义要求两个数字。 |
| --- |

|

&#124; (average  1  2  3) &#124;

&#124; average: expects 2 arguments, but found 3 &#124;

| 这里平均值被应用于三个数字而不是两个。 |
| --- |

|

&#124; ([make-posn](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._make-posn%29%29)  1) &#124;

&#124; make-posn: expects 2 arguments, but found only 1 &#124;

| BSL 定义的函数也必须应用于正确的参数数量。例如，[make-posn](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._make-posn%29%29) 必须应用于两个参数。 |
| --- |

BSL 中关于错误数据的错误信息

以下错误场景再次假设定义区域包含以下内容：

> | ; Number  Number -> Number |
> | --- |
> | ; find the average of x and y |
> | ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (average x y) [...](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._......%29%29)) |

记住，posn 是一个预定义的结构类型。

|

&#124; ([posn-x](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._posn-x%29%29) #true) &#124;

&#124; posn-x: expects a posn, given #true &#124;

| 函数必须应用于它期望的参数。例如，[posn-x](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._posn-x%29%29) 期望一个 posn 实例。 |
| --- |

|

&#124; (average "one" "two") &#124;

&#124; +: expects a number as 1st argument, given "one" &#124;

| 定义一个用于消耗两个 Number 的函数必须应用于两个 Number；这里平均数应用于 String。只有当平均数应用于这些 String 时，才会触发错误信息。像所有原始操作一样，[+](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._%2B%29%29) 是一个检查函数。 |
| --- |

错误信息关于 BSL 中的条件语句

这次我们期望在定义区域中有一个常量定义：

|

> > &#124; ; N in [0,1,...10) &#124;
> > 
> > &#124; ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) 0-to-9 ([random](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._random%29%29) 10)) &#124;

|

|

&#124;

&#124; ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) &#124;

&#124;   ([>=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3e~3d%29%29) 0-to-9 5)]) &#124;

&#124;

&#124; cond: expected a clause with a question and an answer, but found a clause with only one part &#124;

| 每个 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 条件语句必须恰好由两个部分组成：一个条件和答案。这里 ([>=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3e~3d%29%29) 0-to-9 5) 明显是作为条件；答案缺失。 |
| --- |

|

&#124;

&#124; ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) &#124;

&#124;   ([>=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3e~3d%29%29) 0-to-9 5) &#124;

&#124; "head" &#124;

&#124;   "tail"]) &#124;

&#124;

&#124; cond: expected a clause with a question and an answer, but found a clause with 3 parts &#124;

| 在这个例子中，[cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 条件语句由三个部分组成，这也违反了语法规则。虽然 ([>=](http://docs.racket-lang.org/htdp-langs/beginner.html#%28def._htdp-beginner._%28%28lib._lang%2Fhtdp-beginner..rkt%29._~3e~3d%29%29) 0-to-9 5) 明显是作为条件，但该语句附带两个答案：“head”和“tail”。选择其中一个或从两个字符串中创建一个单一值。 |
| --- |

|

&#124; ([cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29)) &#124;

&#124; cond: 在 cond 后期望有一个子句，但没有找到任何内容 &#124;

| 条件语句必须至少包含一个 [cond](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._cond%29%29) 子句，通常至少包含两个。 |
| --- |

BSL 中关于函数定义的错误信息

所以下列所有错误场景都假设你已经将代码片段放入定义区域并点击了运行。

|

&#124; ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) f(x) x) &#124;

&#124; define: 在变量名 f 后期望只有一个表达式，但找到了额外的 1 个部分 &#124;

| 一个定义由三部分组成：[define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) 关键字、括号内的变量名序列和一个表达式。此定义由四个部分组成；此定义是尝试使用代数课程的标准符号 f(x) 而不是 (f x)。 |
| --- |

|

&#124; ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (f x x) x) &#124;

&#124; define: 发现了一个被多次使用的变量：x &#124;

| 函数定义中的参数序列不能包含重复的变量。 |
| --- |

|

&#124; ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (g) x) &#124;

&#124; define: 在函数名后期望至少有一个变量，但未找到任何变量 &#124;

| 在 BSL 中，函数标题必须包含至少两个名称。第一个是函数的名称；其余的变量名称是参数，这里缺少了它们。 |
| --- |

|

&#124; ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (f (x)) x) &#124;

&#124; define: 期望一个变量，但找到了一个部分 &#124;

| 函数标题包含 (x)，这不是一个变量名。 |
| --- |

|

&#124; ([define](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define%29%29) (h x y) x y) &#124;

&#124; define: 期望函数体只有一个表达式，但找到了额外的 1 个部分 &#124;

| 此函数定义在标题之后包含两个表达式：x 和 y。 |
| --- |

错误信息关于 BSL 中结构类型定义

现在您需要将结构类型定义放入定义区域并点击运行以实验以下错误。

|

&#124;

&#124; ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) [x]) &#124;

&#124; ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) [x y]) &#124;

&#124;

&#124; define-struct: 在 define-struct 后期望结构名称，但找到了其他部分 &#124;

| 结构类型定义由三部分组成：[define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) 关键字、结构的名称以及括号内的名称序列。这里缺少了结构的名称。 |
| --- |

|

&#124;

&#124; ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) x) &#124;

&#124; [y y]) &#124;

&#124;

&#124; define-struct: 发现了一个被多次使用的字段名称：y &#124;

| 结构类型定义中的字段名称序列不得包含重复的名称。 |
| --- |

|

&#124;

&#124; ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) x y) &#124;

&#124; ([define-struct](http://docs.racket-lang.org/htdp-langs/beginner.html#%28form._%28%28lib._lang%2Fhtdp-beginner..rkt%29._define-struct%29%29) x y z) &#124;

&#124;

&#124; define-struct: 期望在结构名称之后至少有一个字段名称（括号内），但找到了其他内容 &#124;

| 这些结构类型定义缺少字段名称的序列，字段名称用括号括起来。 |
| --- |
