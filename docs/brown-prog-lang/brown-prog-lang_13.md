# 13 函数作为数据

|     13.1 一点微积分 |
| --- |
|     13.2 匿名函数的一个有用简写 |
|     13.3 函数生成流 |
|     13.4 合力：导数流 |

考虑到到目前为止我们学到的少量编程可以有多具有表现力是很有趣的。为了说明这一点，我们将通过几个有趣的概念练习来展示，这些概念可以仅使用函数作为值来表达。我们将写两个非常不同的东西，然后展示它们如何很好地融合。

## 13.1 一点微积分

如果你学过微分学，你可能遇到过这样的奇怪的句法陈述：

\begin{equation*}{\frac{d}{dx}} x² = 2x\end{equation*}

让我们解开这句话的含义：\(d/dx\)，\(x²\)和\(2x\)。

首先，让我们来看看这两个表达式；我们将讨论一个，而讨论也将涵盖另一个。对于“\(x²\)是什么意思？”的正确回答当然是一个错误：它没有任何意义，因为\(x\)是一个未绑定的标识符。

那么它打算表示什么？显然，意图是代表将其输入平方的函数，就像\(2x\)意味着将其输入加倍的函数一样。我们有更好的写法：

```
fun square(x :: Number) -> Number: x * x end
fun double(x :: Number) -> Number: 2 * x end
```

而我们真正想说的是，平方的\(d/dx\)（不管那是什么）是双倍。我们假设在变化的变量中具有一元函数。现在让我们解开\(d/dx\)，从其类型开始。正如上面的例子所示，\(d/dx\)实际上是一个从函数到函数的函数。也就是说，我们可以将其类型写成如下形式：

```
d-dx :: ((Number -> Number) -> (Number -> Number))
```

（这种类型可能解释了为什么你的微积分课程从未以这种方式解释这个操作——尽管模糊其真正含义是否对你的理解更有益尚不清楚。）

现在让我们实现 d-dx。我们将实现数值微分，尽管原则上我们也可以实现符号微分——使用你学到的规则，例如，给定一个多项式，乘以指数并减少一个——使用表达式的表示（表示算术）。

一般来说，函数在某一点的数值微分产生该点处导数的值。我们有一个方便的公式：在\(x\)处的\(f\)的导数是

\begin{equation*}\frac{f(x + \epsilon) - f(x)}{\epsilon}\end{equation*}

当\(\epsilon\)趋近于零时。现在我们将给予这个微小值一个小但固定的值，稍后[合力：导数流]看看我们如何改进这一点。

```
epsilon = 0.001
```

现在让我们尝试将上述公式翻译成 Pyret：

```
fun d-dx(f :: (Number -> Number)) -> (Number -> Number):
  (f(x + epsilon) - f(x)) / epsilon
end
```

> 现在！
> 
> > 上述定义有什么问题？

如果你没有注意到，Pyret 很快就会告诉你：x 没有绑定。事实上，x 是什么？这是我们试图计算数值导数的点。也就是说，d-dx 需要返回的不是一个数字，而是一个函数（如类型所示），这个函数将消耗这个 x：

```
fun d-dx(f :: (Number -> Number)) -> (Number -> Number):
  lam(x :: Number) -> Number:
    (f(x + epsilon) - f(x)) / epsilon
  end
end
```

确实，这个定义现在有效了。例如，我们可以这样测试它（注意使用 num-floor 避免数值精度问题导致我们的测试看起来失败）：

```
d-dx-square = d-dx(square)

check:
  ins = [list: 0, 1, 10, 100]
  for map(n from ins):
    num-floor(d-dx-square(n))
  end
  is
  for map(n from ins):
    num-floor(double(n))
  end
end
```

现在我们可以回到引发这一调查的原始示例了：数学中草率而神秘的符号到底想表达什么，

```
d-dx(lam(x): x * x end) = lam(x): 2 * x end
```

或者，用 函数表示法 的符号表示，

\begin{equation*}{\frac{d}{dx}} [x \rightarrow x²] = [x \rightarrow 2x]\end{equation*}

可怜的数学教科书不愿告诉我们真相！

## 13.2 匿名函数的有用简写

Pyret 提供了一种更短的语法来编写匿名函数。虽然从风格上讲，我们通常避免使用它，以免我们的程序变成一堆特殊字符，但有时它特别方便，正如我们将在下面看到的那样。这个语法是

```
{(a): b}
```

这里 a 是零个或多个参数，b 是函数体。例如，我们可以写成 lam(x): x * x end，如下所示

```
{(x): x * x}
```

我们可以看到简洁性的好处。特别要注意，因为大括号代替了显示表达式开始和结束的位置，所以不需要结束。同样地，我们也可以将 d-dx 写成

```
fun d-dx-short(f):
  {(x): (f(x + epsilon) - f(x)) / epsilon}
end
```

但许多读者会说这使函数更难阅读，因为突出显示的 lam 清楚地表明 d-dx 返回一个（匿名）函数，而这种语法则使其模糊不清。因此，我们通常只在“一行式”中使用这种简写语法。

## 13.3 函数流

人们通常认为函数只有一个目的：对表达式进行参数化。虽然这既正确又是函数的最常见用法，但这并不能证明存在一个没有参数的函数的合理性，因为这显然是对什么都不参数化的参数化。然而，没有参数的函数也有用处，因为函数实际上有两个目的：参数化和推迟对函数体的求值直到函数被应用。事实上，这两个用途是正交的，即一个功能可以使用而不使用另一个功能。在 糖化匿名性 中，我们看到了这一方面：立即使用的参数化函数，因此我们只使用抽象而不使用延迟。下面，我们将看到另一个方面：延迟而不使用抽象。

让我们考虑一下简单的列表。列表只能是有限长的。然而，在自然界中有许多没有自然上限的列表（或序列）：从数学对象（自然数序列）到自然对象（网站点击次数序列）。与其试图将这些无限制的列表压缩成有限制的列表，不如看看我们如何表示和对这些无限制的列表进行编程。

首先，让我们编写一个计算自然数序列的程序：

```
fun nats-from(n):
  link(n, nats-from(n + 1))
end
```

> 现在做！
> 
> > 这个程序有问题吗？

虽然这代表了我们的意图，但它不起作用：运行它——例如，nats-from(0)——会创建一个无限循环，评估每个后续自然数的 nats-from。换句话说，我们想写的东西与上面的非常相似，但不会在我们想要的时候发生递归，即，按需发生。换句话说，我们希望列表的其余部分是惰性的。

这就是我们对函数的洞察力的地方。正如我们刚刚注意到的，函数推迟对其主体的评估，直到应用时才会执行。因此，原则上，函数会推迟对 nats-from(n + 1) 的调用，直到需要它。

除了，这会导致类型问题：link 的第二个参数需要是一个列表，不能是一个函数。实际上，因为它必须是一个列表，而且每个已构造的值必须是有限的，因此每个列表都是有限的，并且最终在空处终止。因此，我们需要一种新的数据结构来表示这些惰性列表（也称为流）：<stream-type-def> ::=

|   数据 Stream<T>: |
| --- |
|     &#124; lz-link(h :: T, t :: ( -> Stream<T>)) |
|   end |

注释（ -> Stream<T>）表示没有参数的函数（因此 -> 前面没有任何内容），也称为 thunk。请注意，我们定义流的方式必须是无限的，因为我们没有提供终止它们的方法。让我们构造我们可以的最简单的例子，一个常量值流：

```
ones = lz-link(1, lam(): ones end)
```

Pyret 实际上会抱怨这个定义。请注意，相应的列表版本也不起作用：

```
ones = link(1, ones)
```

因为 ones 在定义点没有被定义，所以当 Pyret 评估 link(1, ones) 时，它会抱怨 ones 未定义。但是，对于我们以前的定义，它过于保守了：ones 的使用位于“lam”下面，因此在定义 ones 完成后才需要，此时 ones 将被定义。我们可以通过使用关键字 rec 来向 Pyret 指示这一点：

```
rec ones = lz-link(1, lam(): ones end)
```

要了解有关递归定义的更多信息，请参阅递归函数。请注意，在 Pyret 中，每个 fun 隐含地有一个 rec，在此之下，这就是我们为什么可以毫不费力地创建递归函数的原因。

> 练习
> 
> > 之前我们说过，我们不能写
> > 
> > ```
> > ones = link(1, ones)
> > ```
> > 
> > 如果我们试图写
> > 
> > ```
> > rec ones = link(1, ones)
> > ```
> > 
> > 相反？这是否有效，如果有效， ones 绑定到什么值？如果它不起作用，它是否由于没有 rec 的定义相同的原因而无法工作？

因此，我们将使用缩写 [匿名函数的有用缩写]。因此，我们可以将上述定义重写为：

```
rec ones = lz-link(1, {(): ones})
```

注意 {(): …} 定义了一个没有参数的匿名函数。你不能忽略 ()！如果你这样做了，Pyret 将会对你的程序意义感到困惑。因为函数会自动递归，所以当我们编写一个函数来创建一个流时，我们不需要使用 rec。考虑这个例子：

```
fun nats-from(n :: Number):
  lz-link(n, {(): nats-from(n + 1)})
end
```

通过它我们可以定义自然数：

```
nats = nats-from(0)
```

请注意，nats 的定义本身不是递归的——递归在 nats-from 内部——所以我们不需要使用 rec 来定义 nats。

> 现在动手！
> 
> > 之前，我们说过每个列表都是有限的，因此最终会终止。这个说法如何适用于流，例如上面的 ones 或 nats 的定义？

ones 的描述仍然是有限的；它只是表示了无限数量的值的潜在性。请注意：

1.  类似的推理不适用于列表，因为列表的其余部分已经构建完成；相反，在那里放置一个函数会导致可能有潜在的无限量的计算仍在进行中。

1.  话虽如此，即使对于流，每次给定的计算中，我们只会创建流的有限前缀。但是，我们不必过早地决定有多少；每个客户端和用途都可以根据需要提取更少或更多的内容。

现在我们已经创建了多个流，但是我们仍然没有一个简单的方法来“看见”其中一个流。首先我们将定义传统的类列表选择器。获取第一个元素的方法与列表完全相同：

```
fun lz-first<T>(s :: Stream<T>) -> T: s.h end
```

相比之下，当尝试访问流的其余部分时，我们从数据结构中得到的是一个惰性计算。要访问实际的剩余部分，我们需要强制执行该惰性计算，这当然意味着对其应用零个参数：

```
fun lz-rest<T>(s :: Stream<T>) -> Stream<T>: s.t() end
```

这对于检查流的各个值很有用。将其作为（常规）列表提取其有限前缀（给定大小）也很有用，这对于测试将是特别方便的。让我们写一个函数：

```
fun take<T>(n :: Number, s :: Stream<T>) -> List<T>:
  if n == 0:
    empty
  else:
    link(lz-first(s), take(n - 1, lz-rest(s)))
  end
end
```

如果你仔细观察，你会发现这个主体并不是通过对（流）输入的结构进行分析来定义的，而是通过自然数（零或后继）的定义案例来定义的。我们将在下面回到这一点（<lz-map2-def>）。现在我们有了这个，我们可以用它来进行测试。请注意，通常我们使用我们的数据来测试我们的函数；在这里，我们使用这个函数来测试我们的数据：

```
check:
  take(10, ones) is map(lam(_): 1 end, range(0, 10))
  take(10, nats) is range(0, 10)
  take(10, nats-from(1)) is map((_ + 1), range(0, 10))
end
```

符号（_ + 1）定义了一个参数的 Pyret 函数，该函数将给定参数加 1。让我们再定义一个函数：对流进行映射的等价函数。出于很快就会变得明显的原因，我们将定义一个接受两个列表并逐点应用第一个参数的版本：<lz-map2-def> ::=

|   fun lz-map2<A, B, C>( |
| --- |
|       f :: (A, B -> C), |
|       s1 :: Stream<A>, |
|       s2 :: Stream<B>): |
|     lz-link( |
|       f(lz-first(s1), lz-first(s2)), |
|       {(): lz-map2(f, lz-rest(s1), lz-rest(s2))}) |
|   end |

现在我们可以看到我们早期关于函数结构的评论特别清晰。而传统的列表映射会有两种情况，这里只有一种情况，因为数据定义（<stream-type-def>）只有一种情况！这有什么后果？在传统的映射中，一种情况看起来像上面那样，但另一种情况对应于空输入，对于这种情况，它产生相同的输出。在这里，因为流永远不会终止，对它进行映射也不会终止，函数的结构反映了这一点。这引出了一个更微妙的问题：如果函数的主体没有基础和归纳案例，我们如何执行归纳证明呢？简短的答案是我们不能：我们必须使用☛ coinduction。为什么我定义 lz-map2 而不是 lz-map？因为它使我们能够编写以下内容：

```
rec fibs =
  lz-link(0,
    {(): lz-link(1,
          {(): lz-map2({(a :: Number, b :: Number): a + b},
                fibs,
            lz-rest(fibs))})})
```

当然，我们可以提取出我们想要的任意多个斐波那契数！

```
check:
  take(10, fibs) is [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
end
```

> 练习
> 
> > 为流定义与映射、过滤器和折叠相当的等价物。

流以及更一般地说，按需展开的无限数据结构在编程中非常有价值。例如考虑一场比赛中可能的走法。在某些游戏中，这可能是无限的；即使它是有限的，对于有趣的游戏，组合学意味着树太大而无法在内存中存储。因此，计算机智能的程序员必须按需展开游戏树。通过使用我们上面描述的编码来编写程序，意味着程序按需描述整个树，并且树会自动按需展开，从而解除了程序员实现这种策略的负担。

在某些语言中，如 Haskell，惰性求值默认内置。在这样的语言中，不需要使用惰性。然而，惰性求值会给语言带来其他负担[REF]。

## 13.4 合力：导数流

当我们定义 d-dx 时，我们将 epsilon 设置为一个任意的高值。我们可以将 epsilon 看作是一个产生逐渐细化的值的流；然后，例如，当导数值的差异变得足够小时，我们可以决定我们对导数有足够的近似。

因此，第一步是将 epsilon 变成某种参数，而不是一个全局常量。这留下了应该是什么类型的参数（数字还是流？）以及何时提供它的问题。

在我们决定要对什么函数进行微分以及我们想要其导数的值之后，消耗这个参数才是最合理的；毕竟，epsilon 值流可能取决于两者。因此，我们得到：

```
fun d-dx(f :: (Number -> Number)) ->
    (Number -> (Number -> Number)):
  lam(x :: Number) -> (Number -> Number):
    lam(epsilon :: Number) -> Number:
      (f(x + epsilon) - f(x)) / epsilon
    end
  end
end
```

我们可以回到我们的正方形示例：

```
d-dx-square = d-dx(square)
```

请注意，此时我们只是重新定义了 d-dx，没有任何与流相关的引用：我们只是将一个常量变成了一个参数。现在让我们定义十的负幂流：

```
tenths = block:
  fun by-ten(d):
    new-denom = d / 10
    lz-link(new-denom, lam(): by-ten(new-denom) end)
  end
  by-ten(1)
end
```

以便

```
check:
  take(3, tenths) is [list: 1/10, 1/100, 1/1000]
end
```

为了具体起见，让我们选择一个横坐标来计算平方的数值导数—比如说 10：

```
d-dx-square-at-10 = d-dx-square(10)
```

从类型中回想起，现在这是一个类型为(Number -> Number)的函数：给定一个 epsilon 的值，它使用该值计算导数。我们知道，从分析上来看，这个导数的值应该是 20。我们现在可以（懒惰地）映射十分之一，以提供越来越好的 epsilon 近似值，并看看会发生什么：

```
lz-map(d-dx-square-at-10, tenths)
```

确实，我们得到的值是 20.1、20.01、20.001 等等：逐渐更好的对 20 的数值近似。

> 练习
> 
> > 将上述程序扩展为接受一个容差，并绘制出从 epsilon 流中提取的值，直到连续近似值之间的差值落在此容差范围内为止。