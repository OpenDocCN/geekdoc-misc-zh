# 27 关于程序的推理：类型的初步了解

|     27.1 类型作为静态学科 |
| --- |
|     27.2 可替代性原则 |
|     27.3 类型化的语言和类型错误 |
|       27.3.1 假设-保证推理 |
|     27.4 表达式和函数的类型检查器 |
|       27.4.1 一个纯粹的检查器 |
|       27.4.2 一个计算器和检查器 |
|       27.4.3 类型检查与解释 |
|     27.5 类型检查、测试和覆盖率 |
|     27.6 代码中的递归 |
|       27.6.1 对递归进行类型检查的第一次尝试 |
|       27.6.2 程序终止 |
|       27.6.3 对递归进行类型检查 |
|     27.7 数据中的递归 |
|       27.7.1 递归数据类型定义 |
|       27.7.2 引入的类型 |
|       27.7.3 选择器 |
|       27.7.4 模式匹配和解糖 |

本书的一个主题是可预测性（作为主题的可预测性）。在我们运行程序之前推理程序行为的一个关键工具是类型的静态检查。例如，当我们写 x :: Number 时，我们的意思是 x 将始终保存一个数字，并且所有依赖于 x 的程序部分都可以依赖于这个语句被执行。正如我们将看到的，类型只是我们可能希望陈述的不变量光谱中的一个点，而静态类型检查——<wbr>本身是一系列多样的技术——<wbr>也是我们可以用来强制执行不变量的方法光谱中的一个点。

## 27.1 类型作为静态学科

在本章中，我们将特别关注静态类型检查：也就是说，在程序执行之前检查（声明的）类型。这是一个非常丰富和活跃的主题。为了进一步学习，我强烈建议阅读皮尔斯的《类型与编程语言》。我们将探讨一些类型设计空间和它们的权衡。最后，虽然静态类型是一种特别强大和重要的不变量强制形式，但我们还将检查一些其他可用的技术[REF]。

考虑这个 Pyret 程序：

```
fun f(n :: Number) -> Number:
  n + 3
end

f("x")
```

我们希望在程序开始执行之前收到类型错误。Pyret 目前不执行静态类型检查，但这很快会改变。同样的程序（没有类型注释）只能在运行时失败：

```
fun f(n):
  n + 3
end

f("x")
```

> 练习
> 
> > 你如何测试一个在程序执行之前失败而另一个在执行过程中失败的断言？

现在考虑以下 Pyret 程序：

```
fun f n:
  n + 3
end
```

这也在程序执行之前失败，出现了解析错误。虽然我们认为解析与类型检查在某种程度上是不同的——通常是因为类型检查器假定它已经有了一个解析的程序——但将解析视为最简单的类型检查可能是有用的：通常是确定程序是否遵守无上下文语法。然后，类型检查问是否遵守上下文敏感（或更丰富）的语法。简而言之，类型检查是解析的一般化，因为两者都关注强制程序遵守规则的句法方法。这种特定且非常有影响力的表述归功于约翰·雷诺兹。

我们将首先介绍传统核心类型语言。稍后，我们将探讨扩展[REF]和变体[REF]。

## 27.2 可替代性原则

任何类型机制的本质通常是可替代性原则：当一个类型 A 和 B“匹配”时，一个类型的值可以用于另一个类型的值的位置。因此，类型系统的设计隐含地迫使我们考虑这种替换何时是安全的（如中心定理：类型完备性所述）。

当然，最简单的可替代性概念就是身份：一个类型只能被其自身替代，不能被其他任何东西替代。例如，如果函数参数的声明类型是 String，那么你只能用 String 类型的值调用它，不能用其他任何东西。这被称为不变性：可以传递到类型中的值的集合不能与该类型期望的集合“变化”。这是如此显而易见，以至于似乎几乎不值得一提！然而，给它起个名字是有用的，因为它与后来的类型系统形成对比，当我们有更丰富、非平凡的可替代性概念时（参见子类型化）。

## 27.3A 类型(d) 语言和类型错误

在我们定义类型检查器之前，我们必须解决两个问题：我们的类型核心语言的语法以及与此同时，类型本身的语法。

我们将从具有函数作为值的语言开始（随处可见的函数）。对于这种语言，我们必须添加类型注释。通常，我们不会对常量或原始操作（如加法）强加类型注释，因为这将令人无法忍受；相反，我们将它们强加在函数或方法的边界上。在本研究过程中，我们将探讨为什么这是注释的一个好位置。

给定这个决定，我们的核心语言变成了：

```
data TyExprC:
  | numC(n :: Number)
  | plusC(l :: TyExprC, r :: TyExprC)
  | multC(l :: TyExprC, r :: TyExprC)
  | trueC
  | falseC
  | ifC(c :: TyExprC, t :: TyExprC, e :: TyExprC)
  | idC(s :: String)
  | appC(f :: TyExprC, a :: TyExprC)
  | fdC(arg :: String, at :: Type, rt :: Type, body :: TyExprC)
end
```

换句话说，每个过程都注释了它期望的参数类型和它声称要生成的参数类型。

现在我们必须决定一种类型语言。为此，我们遵循的传统是类型抽象于值集合之上。在我们的语言中，我们有三种值的类型。因此，我们应该有三种类型：分别用于数字、布尔值和函数。

数字类型需要记录哪些信息？在大多数语言中，实际上有许多数字类型，甚至可能没有一个表示“数字”的类型。然而，我们忽略了数字之间的这些渐变（（部分“change-rep”）），因此对于我们来说，只有一个就足够了。决定了这一点之后，我们是否记录关于哪个数字的附加信息？原则上我们可以，但这意味着为了检查类型，我们必须能够决定两个表达式是否计算出相同的数字——<wbr>这是一个归结为停机问题的问题[REF]。然而，在一些专门的类型系统中，我们确实记录了有关数字的一些信息。这些系统要么具有一些近似的手段，可以避免停机问题，要么通过不保证终止来接受它！

我们将布尔值视为数字：我们忽略它是哪种布尔值。在这里，我们可能更需要精确，因为我们只需要跟踪两个值，而不是无限个数。这意味着在某些情况下，我们甚至知道将会执行条件语句的哪个分支，并且可以仅检查该分支（尽管这可能会错过另一个分支中潜在的类型错误：我们应该怎么处理？）。然而，甚至知道我们有哪种精确布尔值的问题都归结为停机问题[REF]。

> 练习
> 
> > 为什么确定任意表达式求值为哪个数字或布尔值等同于解决停机问题的一个理由。

至于函数，我们有更多信息：期望参数的类型和声称结果的类型。我们可能会记录这些信息，直到它被证明是无用的为止。将这些结合起来，我们得到以下抽象类型语言：

```
data Type:
  | numT
  | boolT
  | funT(a :: Type, r :: Type)
end
```

现在我们已经修复了语言的术语和类型结构，让我们确保我们对于在我们的语言中构成类型错误的内容达成一致意见（并且，按照规定，任何不是类型错误的内容都必须通过类型检查器）。类型错误有三种明显的形式：

+   乘法的一个或两个参数不是数字，即不具有类型 numT。

+   乘法的一个或两个参数不是数字。

+   应用的函数位置上的表达式不是一个函数，即不具有类型 funT。

> 现在动手！
> 
> > 还有吗？

我们确实漏掉了一个：

+   应用的函数位置上的表达式是一个函数，但实际参数的类型与函数期望的形式参数的类型不匹配。

> 现在动手！
> 
> > 还有吗？

那么呢：

+   应用的函数位置上的表达式是一个函数，但其返回类型与调用该函数的表达式所期望的类型不匹配？

我们还没有完成！与其进行这种临时枚举，我们真正应该做的是系统地审查我们语言的每种语法形式，并询问每种形式如何产生类型错误。这表示：

```
| numC(n :: Number)
| plusC(l :: TyExprC, r :: TyExprC)
| multC(l :: TyExprC, r :: TyExprC)
```

单独的数字永远不会导致类型错误。对于加法和乘法，两个分支都必须具有数字类型。

```
| trueC
| falseC
| ifC(c :: TyExprC, t :: TyExprC, e :: TyExprC)
```

与数字一样，布尔常量本身不会导致类型错误。然而，在条件语句中，我们要求：

+   条件表达式必须具有布尔类型。

+   两个分支必须具有相同的类型（无论它是什么）。隐含的是我们可以轻松确定两种类型何时相同的想法。我们将在 子类型化 中返回这一点。

最后：

```
| idC(s :: String)
| appC(f :: TyExprC, a :: TyExprC)
| fdC(arg :: String, at :: Type, rt :: Type, body :: TyExprC)
```

单独的标识符永远不会导致类型错误。应用期望：

+   函数位置（f）必须具有函数类型（funT）。

+   实际参数表达式（a）的类型必须与函数位置的形式参数的类型（.arg）匹配。

最后，函数定义期望：

+   体的类型——<wbr>假设形式参数（arg）已经被赋予了声明类型（at）的值——与声明的返回类型（rt）相匹配。

### 27.3.1 假设保证推理

我们刚刚看到的最后几种情况有一个非常有趣的结构。你注意到了吗？

函数定义和声明的规则完美地相辅相成。让我们通过一个用 Pyret 语法编写的程序来说明这一点：

```
fun f(x :: String) -> Number:
  if x == "pi":
    3.14
  else:
    2.78
  end
end

2 + f("pi")
```

在对 f 的定义进行类型检查时，我们假设当 f 最终被应用时，它将被应用到一个 String 类型的值上。我们之所以假设这一点是因为 x 上的注释是 String。我们可以这样假设是因为在检查应用时，我们将首先查找 f 的类型，观察到它期望一个 String 类型的值，并确认实际参数确实匹配了这种类型。也就是说，类型检查器对应用的处理保证了这一假设的安全性。

同样，在对应用程序进行类型检查时，我们查找了 f 的类型后，假设它确实会返回一个 Number 类型的值。我们可以这样假设，因为那是 f 的返回类型注释。我们之所以这样假设，是因为类型检查器将确保 f 的主体——假设 x 的类型——确实会返回一个 Number。换句话说，再次强调，函数定义的类型检查器处理保证了函数应用程序的假设是安全的。

简而言之，函数定义和应用程序的处理是互补的。它们通过一种称为假设-保证推理的方法联系在一起，每一方的假设都由另一方保证，并且两者完美地结合在一起，以给我们所需的安全执行（我们稍后会详细介绍：中心定理：类型正确性）。

## 27.4A 表达式和函数的类型检查器

### 27.4.1A 纯类型检查器

由于类型检查器的工作是对程序进行评判——特别是指示程序是否通过类型检查——类型检查器的自然类型将是：

```
tc :: TyExprC -> Boolean
```

但是，因为我们知道表达式包含标识符，所以很快就会清楚，我们将需要一个类型环境，它将名称映射到类型，类似于我们到目前为止所看到的值环境。

> 练习
> 
> > 定义与类型环境相关的类型和函数。

因此，我们可能会这样开始我们的程序：<hof-tc-bool> ::=

|   fun tc(e :: TyExprC, tnv :: TyEnv) -> Boolean: |
| --- |
|     cases (TyExprC) e: |
|       <hof-tc-bool-numC> |
|       <hof-tc-bool-idC> |
|       <hof-tc-bool-appC> |
|     end |
|   end |

正如上面缩写的情况集所示，这种方法不会奏效。我们很快就会看到原因。让我们从简单的情况开始：数字。数字类型检查吗？当然检查；可能周围的上下文不希望是数字，但那种错误将在其他地方被标识。因此：<hof-tc-bool-numC> ::=

|   &#124; numC(_) => true |
| --- |

（请注意，我们明确忽略了它是哪个数字。）现在让我们处理标识符。标识符是否被正确地类型化？同样，单独来看，它似乎是，只要它实际上是一个已绑定的标识符；它可能不是上下文所需的，但希望那也会在其他地方处理。因此，我们可能会写<hof-tc-bool-idC> ::=

|   &#124; idC(s) => ty-lookup(s, tnv) |
| --- |

其中，如果标识符已绑定，则 ty-lookup 返回 true，否则返回 false。

这可能让你有点不舒服：我们似乎正在丢弃关于标识符类型的宝贵信息。当然，类型确实会丢失信息（例如，表达式计算的具体数字）。然而，我们在这里丢弃的信息类型更为重要：它不是关于类型内特定值的信息，而是类型本身。尽管如此，让我们继续前进。你可能也会觉得困扰，因为我们只返回一个布尔值，我们无法表达发���了什么类型错误。但你可以安慰自己说这只是因为我们的返回类型太弱。

现在我们来处理应用程序。我们应该对函数部分进行类型检查，确保它是一个函数，然后确保实际参数的类型与函数声明的形式参数类型一致。代码看起来怎么样？<hof-tc-bool-appC> ::=

|   &#124; appC(f, a) => |
| --- |
|     f-t = tc(f, tnv) |
|     a-t = tc(a, tnv) |
|     ... |

对 tc 的两个递归调用只能告诉我们函数和参数表达式是否通过类型检查。关键是，它们无法告诉我们参数表达式的类型（它是什么？）是否与函数期望的参数类型匹配（它是什么？）。虽然在简单表达式的情况下我们可能能够糊弄过去，但对于复杂表达式，我们不能仅仅检查表达式；此外，这违反了我们希望避免深入表达式的原则。换句话说，我们希望写成

```
| appC(f, a) =>
  f-t = tc(f, tnv)
  a-t = tc(a, tnv)
  if is-funT(f-t):
    if a-t == f-t.arg:
```

但 f-t 是一个布尔值，因此永远无法通过 is-funT；同样，将 a-t 与 f-t.arg 进行比较是没有意义的，因为两者都是布尔值（表示相应的子表达式是否通过类型检查），而不是这些表达式的实际类型。

换句话说，我们需要的是一种能够计算表达式类型的东西，无论它有多复杂。当然，这样的过程只有在表达式类型正确时才能成功；否则它将无法提供一个连贯的答案。换句话说，类型“计算器”将类型“检查”作为一个特例！

> 现在动手！
> 
> > 这有点微妙。再读一遍。

因此，我们应该加强对 tc 的归纳不变性：它不仅告诉我们一个表达式是否有类型，还告诉我们它的类型是什么。实际上，通过给出任何类型，它确认了表达式的类型，否则它会报错。

### 27.4.2A 计算器和检查器

现在让我们定义这个更丰富的类型“检查器”。<hof-tc> ::=

|   fun tc(e :: TyExprC, tnv :: TyEnv) -> Type: |
| --- |
|     cases (TyExprC) e: |
|       <hof-tc-numC> |
|       <hof-tc-plusC> |
|       <hof-tc-multC> |
|       <hof-tc-bools> |
|       <hof-tc-idC> |
|       <hof-tc-fdC> |
|       <hof-tc-appC> |
|     end |
|   end |

现在让我们填补这些空白。数字很容易：它们有数字类型。<hof-tc-numC> ::=

|   &#124; numC(_) => numT |
| --- |

同样，标识符具有环境中指定的任何类型（如果它们没有绑定，查找它们会报错）。<hof-tc-idC> ::=

|   &#124; idC(s) => ty-lookup(s, tnv) |
| --- |

注意到，到目前为止，解释和类型检查之间的相似性和差异：在标识符情况下，我们基本上做了相同的事情（除了我们返回一个类型而不是实际值），而在数字情况下，我们返回了抽象的“数字”（numT）而不是指示它是哪个具体的数字。现在让我们来看看加法。我们必须确保两个子表达式都有数字类型；只有这样，整体表达式才能评估为一个数字本身。使用一个辅助函数会很有用：<hof-tc-plusC> ::=

|   &#124; plusC(l, r) => tc-arith-binop(l, r, tnv) |
| --- |

其中：

```
fun tc-arith-binop(l :: TyExprC, r :: TyExprC, tnv :: TyEnv) -> Type:
  if (tc(l, tnv) == numT) and (tc(r, tnv) == numT):
    numT
  else:
    raise('type error in arithmetic')
  end
end
```

不要忽略乘法的重要性：<hof-tc-multC> ::=

|   &#124; multC(l, r) => tc-arith-binop(l, r, tnv) |
| --- |

> 现在开始！
> 
> > 你看到了什么不同的地方吗？

没错：什么都没有！这是因为，从类型检查的角度来看（在这种类型语言中），加法和乘法之间没有区别，实际上在任何消耗两个数字并返回一个数字的两个操作之间也没有区别。因为我们忽略了实际的数字，所以我们甚至不需要费心向 tc-arith-binop 传递一个反映如何处理数字对的函数。

注意解释和类型检查之间的另一个差异。两者都关心参数是数字。然后解释器返回一个精确的和或乘积，但类型检查器对它们之间的区别漠不关心：因此计算返回的表达式（numT）是一个常量，并且两种情况下都是相同的常量。

接下来，让我们处理布尔值和条件语句。我们将简单地把我们先前同意的内容转录成代码：<hof-tc-bools> ::=

|   &#124; trueC => boolT |
| --- |
|   &#124; falseC => boolT |
|   &#124; ifC(cnd, thn, els) => |
|     cnd-t = tc(cnd, tnv) |
|     if cnd-t == boolT: |
|       thn-t = tc(thn, tnv) |
|       els-t = tc(els, tnv) |
|       if thn-t == els-t: |
|         thn-t |
|       else: |
|         raise("conditional branches don't match") |
|       end |
|     else: |
|       raise("conditional isn't Boolean") |
|     end |

然而，请回想我们对条件语句的设计空间的讨论，所有这些都会对类型检查产生影响。我们在这里应用了我们先前做出的决定。

> 练习
> 
> > 考虑之前做出的三个决定。更改每个决定，并解释它对类型检查器的影响。

最后，两个棘手的情况：应用和函数。我们已经讨论了应用必须做的事情：计算函数和参数表达式的值；确保函数表达式具有函数类型；检查参数表达式是否具有兼容的类型。如果所有这些都成立，那么总体应用的类型就是函数体将返回的任何类型（因为最终在运行时返回的值是评估函数体的结果）。注意，这在某种程度上取决于评估和类型检查的和谐性。我们在中心定理：类型完整性下讨论这一点。<hof-tc-appC> ::=

|   &#124; appC(f, a) => |
| --- |
|     f-t = tc(f, tnv) |
|     a-t = tc(a, tnv) |
|     if is-funT(f-t): |
|       if a-t == f-t.arg: |
|         f-t.ret |
|       else: |
|         raise("argument type doesn't match declared type") |
|       end |
|     else: |
|       raise("not a function in application position") |
|     end |

这留下了函数定义。函数有一个形式参数；除非在类型环境中绑定了这个参数，否则在函数体中使用该参数将导致类型错误。因此，我们必须扩展类型环境，将形式名称绑定到其类型，并在扩展的环境中检查类型体。这个计算出的任何值必须与体的声明类型相同。如果是这样，那么函数本身就有一个从参数类型到体类型的函数类型。<hof-tc-fdC> ::=

|   &#124; fdC(a, at, rt, b) => |
| --- |
|     bt = tc(b, xtend-t-env(tbind(a, at), tnv)) |
|     if bt == rt: |
|       funT(at, rt) |
|     else: |
|       raise("body type doesn't match declared type") |
|     end |

### 27.4.3 类型检查与解释

> 现在就开始吧！
> 
> > 当面对一个头等函数时，我们的解释器创建了一个闭包。然而，我们的类型检查器似乎没有任何关于“闭包”的概念，即使我们使用了（类型）环境。为什么？特别是，请回想一下，没有闭包导致了静态作用域的违反。这里是否发生了同样的情况？编写一些测试来调查。

观察解释器和类型检查器之间一个有趣的区别。在解释器中，应用负责评估参数表达式，扩展环境，并评估体。在这里，应用案例确实检查参数表达式，但不会改变环境，只是返回体的类型而不对其进行遍历。相反，当检查函数定义时，体实际上是由检查器遍历的，因此这是环境实际上扩展的地方。

> 练习
> 
> > 为什么解释和类型检查之间的遍历时间不同？

这样做的后果值得理解。

+   考虑 Pyret 函数

    ```
    p =
      lam(x :: Number) -> (Number -> Number):
        lam(y :: Number) -> Number:
          x + y
        end
      end
    ```

    当我们简单地定义 p 时，解释器不会遍历这些表达式的内部，特别是 x + y。相反，这些被搁置等待以后使用（实际上是我们利用的一个特性（（部分 "惰性"）））。此外，当我们将 p 应用于某个参数时，这会计算外部函数，导致一个闭包（它关闭了 x 的绑定）。

    现在考虑一下类型检查器。只要我们给出这个定义，它就遍历整个表达式，包括最内层的子表达式。因为它知道关于 x 和 y 的一切信息-它们的类型-它可以立即对整个表达式进行类型检查。这就是为什么它不需要创建一个闭包：没有什么需要推迟到应用时间（事实上，我们不想把类型检查推迟到执行时）。

    另一种思考方式是它的行为类似于替换-替换没有使用闭包来提供静态作用域，因为它更加急切：它可以仅使用程序文本进行替换，而不需要任何值，因为它正在替换类型，这些类型已经给定。我们使用类型环境使这一点难以看到，因为我们可能已经将环境与闭包联系起来。然而，重要的是何时提供必要的值。换句话说，我们主要出于惯例使用环境：在这里，我们同样可以很好地使用（类型）替换。

    > 练习
    > 
    > > 编写示例来研究这一点。考虑将上面的示例转换为起点。还要将你的例子从之前转换。

+   考虑以下表达式：

    ```
    lam(f :: (Number -> String), n :: Number) -> String:
      f(n)
    end
    ```

    在评估内部的 f(n) 时，解释器可以访问 f 和 n 的实际值。相反，当对其进行类型检查时，它不知道将作为 f 传入的函数是哪个。那么，它如何进行类型检查呢？

    答案是注释告诉类型检查器它需要知道的一切。注释表明 f 必须接受数字；由于 n 被注释为一个数字，所以应用可以工作。它还表示 f 将返回字符串；因为这是整个函数返回的内容，所以这也是可以的。

    换句话说，注释（Number -> String）表示的不是一个函数，而是一个无限的函数族，而不会承诺其中任何一个。类型检查器然后检查任何这样的函数在这个设置中是否可行。一旦它完成了它的工作，实际上我们传递的是哪个函数就不重要了，只要它有这个类型。当然，检查这一点是假设-保证推理的核心。

## 27.5 类型检查、测试和覆盖率

可以将类型检查器看作是一种非常特殊的测试框架：

+   它不使用具体的值，而是只使用类型。因此，它不能检查值内部的细微差别。

+   作为回报，它是静态工作的：也就是说，就像在运行程序之前运行轻量级测试程序一样。（我们不应该低估这一点的价值：依赖于交互式或其他外部输入、专用硬件、定时等的程序可能非常难以测试。对于这样的程序，获得一种不需要运行它的轻量级测试的形式是无价的。）

+   测试仅覆盖测试用例执行的程序部分。相反，类型检查器对整个程序进行检查。因此，它可以捕获潜在的错误。当然，这也意味着整个程序必须符合类型：不能有一些部分（例如，条件分支）尚未符合类型，它们可能无法正常工作，但可以被不执行它们的测试忽略。

+   最后，类型提供了另一个非常重要的属性：量化。回想一下我们之前的例子：类型检查器已经对无限数量的函数做出了某种规定！

这最后一点触及了类型和测试之间的权衡的核心：类型是“广泛的”，而测试是“深入的”。也就是说，因为测试涉及非常具体的值及其实际评估，它们可以提出任意深入的问题，但仅限于一个特定情况。相反，由于类型缺乏值和评估所提供的特定性，它们无法提出深入的问题；它们通过能够讨论某种形状的所有可能值来弥补这一点，提供其广度。正如本讨论所说明的，这两个属性都没有支配另一个：良好的软件实践将同时使用两者的明智组合。

## 27.6 代码中的递归

现在我们已经获得了一个基本的编程语言，让我们给它加上递归。我们之前已经看到（递归和非终止），这可以很容易地实现。但是这里会变得更加复杂。

### 27.6.1 对递归类型的初步尝试

现在让我们尝试表达一个简单的递归函数。我们已经看到如何为一阶函数编写无限循环。对它们进行注释不会引入复杂性。

> 练习
> 
> > 确认给递归和非终止的一阶函数添加类型不会引起额外的问题。

现在让我们转向高阶函数。我们已经看到这导致了一个无限循环：

```
(fun(x): x(x) end)(fun(x):  x(x) end)
```

现在我们有了一个带类型的语言，我们必须对其进行注释。（通常，我们将这个术语称为 Ω。）

回想一下，这个程序是通过将 ω 应用到它自身而形成的。当然，并不是说相同的术语必须具有完全相同的类型，因为它取决于使用的上下文。然而，ω 的特定结构意味着在两个上下文中——作为函数和参数——最终都是相同的术语，所以这两者的类型最好是相同的。换句话说，对 ω 的一个实例进行类型标注就足以对它们两个进行类型标注。

因此，让我们尝试对 ω 进行类型检查；让我们将这种类型称为 T。显然，这是一个函数类型，这个函数接受一个参数，因此它必须是 A -> B 的形式。那么这个参数是什么？就是 ω 本身。也就是说，进入 A 的值的类型本身就是 T。因此，ω 的类型就是 T，即 A -> B，这与 T -> B 相同。这扩展为 (A -> B) -> B，这与 (T -> B) -> B 相同。因此，这进一步扩展为 ((A -> B) -> B) -> B，依此类推。换句话说，这种类型无法被写成任何有限字符串！

> 现在就做！
> 
> > 你是否注意到我们刚刚进行的微妙但重要的跳跃？
> > 
> 现在就做！
> 
> > 我们刚刚论证了我们无法输入 ω。但为什么会导致我们无法输入 Ω 呢？

### 27.6.2 程序终止

因为类型检查是通过对子项进行递归来实现的，要对 Ω 进行类型检查，我们必须能够对 ω 进行类型检查，然后将其类型组合以获得 Ω 的类型。但是，正如我们所看到的，对 ω 进行类型检查似乎会遇到严重问题。然而，从那里，我们跳到了 ω 的类型无法被写成任何有限字符串的结论，对此我们只给出了直觉，而不是证明。事实上，更奇怪的是：在我们迄今定义的类型系统中，我们根本无法对 Ω 进行类型检查！

这是一个强有力的陈述，但它源自更强大的东西。到目前为止，我们的类型化语言具有一种称为强归一化的属性：每个具有类型的表达式在有限步骤后将终止计算。换句话说，这个特殊（而奇特的）无限循环程序并不是我们无法对其进行类型检查的唯一程序；我们无法对任何无限循环（甚至潜在的无限循环）进行类型检查。一个可能有所帮助的粗略直觉是，任何类型—必须是一个有限字符串—其中只能有有限数量的 ->，每个应用都会释放一个，因此我们只能执行有限数量的应用。

> 练习
> 
> > 当我们有命名的一阶函数时，为什么这不成立？

如果我们的语言只允许直线程序，那将是不足为奇的。然而，我们有条件语句，甚至函数作为值传递，而且我们可以使用它们来编码我们迄今为止编写的几乎每个程序。然而，我们仍然得到了这个保证！这使得这个结果有些令人惊讶。

> 练习
> 
> > 尝试使用未类型化语言和类型化语言中的函数来编码列表（如果不确定如何，请参见[REF]）。你看到了什么？这对编码的影响告诉了你什么？

这个结果还揭示了更深层次的东西。它表明，与你可能相信的相反—<wbr>即类型系统仅阻止一些有错误的程序运行—<wbr>类型系统可以改变语言的语义。而以前我们可以用一两行代码写一个无限循环，现在我们根本就不能写。它还表明，类型系统不仅可以建立关于特定程序的不变性，还可以建立关于语言本身的不变性。如果我们想绝对确保一个程序会终止，我们只需用这种语言编写并通过类型检查，保证就是我们的！

在所有程序都终止的语言中有什么可能的用途？对于通用编程来说，当然没有。但在许多专业领域中，拥有这一保证是非常有用的。以下是几个可能受益的领域的示例：

+   一个复杂的调度算法（保证将确保调度程序完成，并且正在调度的任务实际上将运行）。

+   一个路由器中的数据包过滤器。（进入无限循环的网络元素会影响实用性。）

+   一个编译器。（它生成的程序可能会终止，也可能不会，但至少应该完成程序的生成。）

+   一个设备初始化程序。（现代电子产品—<wbr>比如智能手机和复印机—<wbr>有复杂的初始化程序。这些程序必须完成，以便设备真正投入使用。）

+   JavaScript 中的回调函数。（因为该语言是单线程的，不放弃控制意味着事件循环将被饿死。当这种情况发生在网页中时，浏览器通常会在一段时间后介入，并询问是否要关闭该页—<wbr>否则页面的其余部分（甚至整个浏览器）都将无响应。）

+   配置系统，如构建系统或链接器。在 Standard ML 语言中，用于链接模块的语言基本上使用了这种类型的语言来编写模块链接规范。这意味着开发人员可以编写非常复杂的抽象—<wbr>他们终究有函数作为值！—<wbr>同时仍然保证链接将始终终止，产生一个程序。

还要注意类型和测试之间的重要区别（类型检查、测试和覆盖 |
| --- |
|         (if0 n |
|              0 |
|              (n + (S (n + -1))))) |
|   (S 10)) |

对于求和函数，其中 S 是函数的名称，n 是其参数，第一个 num 是 n 的类型，第二个 num 是函数返回的类型。表达式 (S 10) 表示使用该函数对从 10 到 0 的数字求和。

我们如何为这样的表达式确定类型？显然，我们在编写函数时必须将 n 绑定到其主体中（但当然不是在函数的使用中，因为由于静态范围，我们知道了函数的类型）。但是 S 呢？显然，在检查使用 (S 10)) 时，它必须在类型环境中绑定，并且其类型必须为 num -> num。但是，在检查函数主体时，它也必须绑定到相同的类型。（还要注意，主体返回的类型必须与其声明的返回类型匹配。）

现在我们可以看到如何打破类型的有限性。毫无疑问，我们在程序源代码中只能写入有限数量的->。然而，这种用于类型递归的规则复制了指向自身的主体中的->，从而确保了有无穷无尽的应用程序供应。这是我们无限的箭头集合。

实施此规则的代码如下。假设 f 绑定到函数的名称，v 绑定到函数的参数名称，at 是函数的参数类型，rt 是其返回类型，b 是函数的主体，c 是函数的使用：<tc-recC> ::=

|   &#124; recC(f, v, at, rt, b, c) => |
| --- |
|     extended-env = xtend-t-env(tbind(f, funT(at, rt)), tnv) |
|     如果 not(rt == tc(b, xtend-t-env(tbind(v, at), extended-env))): |
|       raise("rec: function return type not correct") |
|     否则: |
|       tc(c, extended-env); |

## 27.7 数据中的递归

我们已经看到了如何编写递归程序，但这还不能让我们创建递归数据。我们已经有一种递归数据类型——函数类型——但这是内置的。我们还没有看到开发者如何创建他们自己的递归数据类型。

### 27.7.1 递归数据类型定义

当我们谈论允许程序员创建递归数据时，实际上我们一次在谈论三个不同的设施：

+   创建一个新类型。

+   让新类型的实例拥有一个或多个字段。

+   让其中一些字段引用相同类型的实例。

实际上，一旦我们允许第三个，我们必须再允许一个：

+   允许非递归基本情况的类型。

这些设计标准的融合导致了通常称为代数数据类型的东西。例如，考虑以下数字二叉树的定义：稍后[REF]，我们将讨论类型如何被参数化。

```
data BinTree:
  | leaf
  | node (value :: Number,
          left :: BinTree,
          right :: BinTree)
end
```

注意，如果没有新数据类型 BinTree 的名称，我们将无法在 node 中引用它。同样，如果没有能够有多种 BinTree 的能力，我们将无法定义叶子，因此也无法终止递归。最后，当然，我们需要多个字段（如在 node 中）来构造有用和有趣的数据。换句话说，这三种机制之所以被包装在一起，是因为它们在结合使用时最有用。（但是，一些语言确实允许定义独立的结构。我们稍后会回到这种设计决策对类型系统的影响 [REF]。）

这种数据定义风格有时也被称为和的总和。在外层，数据类型提供了一组选择（一个值可以是叶子或节点）。这对应于析取（“或”），有时写成和（真值表是有启示性的）。在每个和内部是一组字段，所有字段都必须存在。这对应于合取（“和”），有时写成积（同上）。

这涵盖了符号，但我们还没有解释这个新类型 BinTree 是从哪里来的。显然，假装它被烘焙到我们的类型检查器中是不现实的，因为我们不能为每个新的递归类型定义都改变它——这就像每次程序包含递归函数时都修改我们的解释器一样！相反，我们需要找到一种方法，使这样的定义成为类型语言的固有部分。我们稍后会回到这个问题 [REF]。

### 27.7.2 引入的类型

现在，数据类型定义有什么影响呢？首先，它引入了一个新类型；然后，它使用这个类型来定义多个构造器、谓词和选择器。例如，在上面的示例中，它首先引入了 BinTree，然后用它来赋予以下类型：

```
leaf :: BinTree  # a constant, so no arrow
node :: Number, BinTree, BinTree -> BinTree
is-leaf :: BinTree -> Bool
is-node :: BinTree -> Bool
.value :: BinTree%(is-node) -> Number
.left :: BinTree%(is-node) -> BTnum
.right :: BinTree%(is-node) -> BTnum
```

> 现在！
> 
> > 上述最后三个条目中有哪两个是虚构的？

注意几个显著的事实：

+   两个构造器都创建 BinTree 的实例，而不是更精细的东西。我们将在稍后讨论这种设计折衷 [REF]。

+   两个谓词都消耗 BinTree 类型的值，而不是“任何”值。这是因为类型系统已经可以告诉我们一个值是什么类型。因此，我们只需要区分这一个类型的各种变体。

+   这些选择器实际上只对相关变体的实例起作用——例如，.value 只能对节点的实例起作用，而不能对叶子的实例起作用——但由于缺乏合适的静态类型，我们没有办法在静态类型系统中表达这一点。因此，应用这些只会导致动态错误，而不是静态类型系统捕获的静态错误。

还有更多关于递归类型的内容需要讨论，我们马上就会回来 [REF]。

### 27.7.3 选择器

.value、.left 和.right 是选择器：它们按名称选择记录的部分。但以下是它们虚构的两种方式。首先，语法上：在大多数具有“点字段访问”的语言中，没有像.value 这样的独立运算符：例如，你不能写成.value(...)。但是即使放开这个语法问题（可以通过论证写成 v.value 只是应用这个操作符的一个晦涩的语法来解决），更有趣的微妙之处在于语义上。

在上面，我们给.value 赋了一个非常特定的类型。然而，假设这个数据类型也在同一个程序中定义了：

```
data Payment:
  | cash(value :: Number)
  | card(number :: Number, value :: Number)
end
```

这也似乎定义了一个具有以下类型的.value 运算符：

```
.value :: Payment(is-cash) -> Number
.value :: Payment(is-card) -> Number
```

或者等价地，

```
.value :: Payment -> Number
```

真正的.value 请站出来？有多少个.value 操作？事实上，似乎这个“运算符”自由地横跨了每一个数据类型定义，甚至是每一个模块边界！这些问题并不是特定于类型的：字段访问的横跨性与之无关。然而，给予类型迫使我们去面对这些问题，因为我们不能忽视这个操作的类型困难。为了让这个问题显得更加具体，考虑另外两种处理选择器的非常不同的样式：

+   脚本语言的一个特征是对象仅仅是哈希表，所有字段访问都被转换为对表示字段名称的字符串的哈希表引用。因此，o.f 只是查找与 o 相关联的字典中由"f"索引的值的语法糖。

+   在 Racket 中，结构定义如

    > | (struct cash (value)) |
    > | --- |
    > | (struct card (number value)) |

    生成不同的选择器：在这种情况下，分别是 cash-value 和 card-value。现在再也没有混淆的可能性了，因为它们有不同的名称，每个名称都可以有不同的类型。

编译这些语言之间的区别会突显出这些区别。从 Pyret 或 Java 编译到 JavaScript 很容易，因为所有字段解引用都变成了字典查找。从（未类型化的）Pyret 编译到 Racket 尤其容易，因为这两种语言非常相似—<wbr>直到我们到达点式访问为止。然后，假设我们希望将 Pyret 数据定义编译成 Racket 对应的结构定义，编译器将不得不遍历 Pyret 程序，收集所有具有相同名称的字段，并将它们转换为区分选择器：例如，v.value 可能会编译成 Racket 的（->value v），其中->value 被定义为（给定上述两个数据定义）：

> | (define (->value v) |
> | --- |
> |   (cond |
> |     [(node? v) (node-value v)] |
> |     [(cash? v) (cash-value v)] |
> |     [(card? v) (card-value v)])) |

相反，向另一个方向走是容易的：（node-value v）将检查 v 是否确实是一个节点，然后访问 v.value。

### 27.7.4 模式匹配和解糖

一旦我们理解了由数据类型定义引入的名称以及选择器的性质，唯一剩下的就是提供模式匹配的说明。例如，我们可以写出表达式

```
cases (BinTree) t:
  | leaf => e1
  | node(v, l, r) => e2
end
```

这只是将上述谓词的用法扩展，并绑定这些部分：

```
if is-leaf(t):
  e1
else if is-node(t):
  v = t.value
  l = t.left
  r = t.right
  e2
end
```

简而言之，这可以通过去糖化来实现，因此模式匹配不需要在核心语言中。这反过来意味着一个语言可以有许多不同的模式匹配机制。

但是，这并不那么容易。以 if 形式生成上述代码的去糖化需要知道节点的三个位置选择器分别是 value、left 和 right。这些信息在类型定义中是显式的，但在模式匹配器的使用中只是隐含的（这确实是重点）。某种方式必须将这些信息从定义传达到使用。因此，去糖化器需要类似于类型环境的东西来完成其任务。

此外，请注意，诸如 e1 和 e2 这样的表达式无法进行类型检查—<wbr>事实上，甚至无法可靠地识别为表达式—<wbr>直到去糖化扩展了 cases 的使用。因此，去糖化依赖于类型环境，而类型检查依赖于去糖化的结果。换句话说，这两者是共生的，需要发生，不完全是“并行”的，而是步调一致的。这意味着，当语法糖对类型做出假设时，为带类型的语言构建去糖化比为无类型语言这样做更加复杂。