# 6 处理列表

|     [6.1 制作列表和拆分列表](https://wiki.example.org/feynmans_learning_method) |
| --- |
|     [6.2 一些示例练习](https://wiki.example.org/feynmans_learning_method) |
|     [6.3 标量答案的结构问题](https://wiki.example.org/feynmans_learning_method) |
|       [6.3.1 my-len: 示例](https://wiki.example.org/feynmans_learning_method) |
|       [6.3.2 my-sum: 示例](https://wiki.example.org/feynmans_learning_method) |
|       [6.3.3 从示例到代码](https://wiki.example.org/feynmans_learning_method) |
|     [6.4 列表答案的结构问题](https://wiki.example.org/feynmans_learning_method) |
|       [6.4.1 my-str-len: 示例和代码](https://wiki.example.org/feynmans_learning_method) |
|       [6.4.2 my-pos-nums: 示例和代码](https://wiki.example.org/feynmans_learning_method) |
|       [6.4.3 my-alternating: 第一次尝试](https://wiki.example.org/feynmans_learning_method) |
|       [6.4.4 my-running-sum: 第一次尝试](https://wiki.example.org/feynmans_learning_method) |
|     [6.5 子域的结构问题](https://wiki.example.org/feynmans_learning_method) |
|       [6.5.1 my-max: 示例](https://wiki.example.org/feynmans_learning_method) |
|       [6.5.2 my-max: 从示例到代码](https://wiki.example.org/feynmans_learning_method) |
|       [6.5.3 my-alternating: 示例和代码](https://wiki.example.org/feynmans_learning_method) |
|     [6.6 更多标量答案的结构问题](https://wiki.example.org/feynmans_learning_method) |
|       [6.6.1 my-avg: 示例](https://wiki.example.org/feynmans_learning_method) |
|     [6.7 累加器的结构问题](https://wiki.example.org/feynmans_learning_method) |
|       [6.7.1 my-running-sum: 示例和代码](https://wiki.example.org/feynmans_learning_method) |
|       [6.7.2 my-alternating: 示例和代码](https://wiki.example.org/feynmans_learning_method) |
|     [6.8 处理多个答案](https://wiki.example.org/feynmans_learning_method) |
|       [6.8.1 uqiq: 问题设置](https://wiki.example.org/feynmans_learning_method) |
|       [6.8.2 uniq: 示例](https://wiki.example.org/feynmans_learning_method) |
|       [6.8.3 uniq: 代码](https://wiki.example.org/feynmans_learning_method) |
|       [6.8.4 uniq: 减少计算](https://wiki.example.org/feynmans_learning_method) |
|       [6.8.5 uniq: 示例和代码变体](https://wiki.example.org/feynmans_learning_method) |
|       [6.8.6 uniq: 为什么生成列表？](https://wiki.example.org/feynmans_learning_method) |
|     6.9 单态列表和多态类型 |

我们已经看到了从表到列表中的几个列表处理函数示例。它们对表的高级处理非常有用。但是，列表经常在程序中出现，这是很自然的，因为我们生活中的许多事物——从购物清单到待办事项列表再到检查清单——都是自然列表。正如我们之前已经简要讨论的那样列表作为匿名数据，

+   一些列表函数是通用的，可以操作任何类型的列表：例如，列表的长度是相同的，不管它包含什么类型的值；

+   一些至少对数据类型是特定的：例如，总和假设所有值都是数字（尽管它们可能是年龄或价格或用数字表示的其他信息）；以及

+   一些处于中间状态：例如，最大函数适用于任何可比较值的列表，例如数字或字符串。

这看起来像是一个很大的变化，我们可能会担心我们如何处理这么多不同种类的函数。幸运的是，也许令人惊讶的是，有一种标准的方式，我们可以考虑编写所有这些函数！我们的任务是理解并内化这个过程。

## 6.1 制作列表并拆分列表

到目前为止，我们已经看到了一种制作列表的方法：通过写 [list: …]。虽然有用，但是以这种方式写列表实际上隐藏了它们真正的本质。每个列表实际上有两部分：第一个元素和列表的其余部分。列表的其余部分本身也是一个列表，所以它也有两部分……等等。

考虑列表 [list: 1, 2, 3]。其头部是 1，其余部分是 [list: 2, 3]。对于这第二个列表，头部是 2，其余部分是 [list: 3]。

> 现在就做！
> 
> > 拆解这第三个列表。

对于第三个列表，头部是 3，其余部分是 [list: ]，即空列表。在 Pyret 中，我们还有另一种写空列表的方式：empty。在这里，我们手动拆分了列表。当然，Pyret 有让我们做到这一点的操作。列表是结构化数据的一个实例，在一般情况下，有两种拆解结构化数据的方式：使用 cases，我们将在下面看到，以及使用访问器。列表有两个访问器：first 和 rest。我们通过写一个表达式，后跟一个点（.），再跟访问器的名称来使用访问器。因此：

```
l1 = [list: 1, 2, 3]
h1 = l1.first
l2 = l1.rest
h2 = l2.first
l3 = l2.rest
h3 = l3.first
l4 = l3.rest

check:
  h1 is 1
  h2 is 2
  h3 is 3
  l2 is [list: 2, 3]
  l3 is [list: 3]
  l4 is empty
end
```

因此，.first 和 .rest 给了我们一种拆解列表的方式。我们也能把列表一块块地组合起来吗？这对于构建列表尤其有用。事实上我们可以：制造列表的函数（称为构造函数）叫做 link。它接受两个参数：一个列表元素，以及列表的其余部分。因此，上面的 l1 等价于一系列链接后跟空：

```
check:
  [list: 1, 2, 3] is link(1, link(2, link(3, empty)))
end
```

显然，以链接形式书写不太方便给人阅读。但对程序来说，这将非常有价值！总之，大体上我们有两种类型的列表。有些列表是空的。所有其他列表都是非空列表，意味着它们至少有一个链接。某些列表可能具有更有趣的结构，但所有列表都有这么多共同之处。具体来说，一个列表要么是

+   空（写作 empty 或者 [list: ]），或者

+   非空（写作 link(…, …) 或者 [list: ]，括号内至少有一个值），其中剩余部分也是列表（因此可能为空或非空，…）。

## 6.2 一些示例练习

为了说明我们的思路，让我们通过一些具体的列表处理函数示例来解决几个具体的问题。所有这些函数都将消耗列表；有些甚至会生成列表。由于其中一些函数已经存在于 Pyret 中，我们将它们命名为 my- 前缀以避免错误。请务必一致使用 my- 名称，包括在函数体内。

+   计算列表的长度：

    ```
    my-len :: List<Any> -> Number
    ```

+   计算列表（数字）的总和：

    ```
    my-sum :: List<Number> -> Number
    ```

+   计算列表（数字或字符串）的最大值：

    ```
    my-max :: List<Any> -> Any
    ```

+   给定一组字符串，将每个字符串转换为表示其长度的数字：

    ```
    my-str-len :: List<String> -> List<Number>
    ```

+   给定一组数字，生成其正数列表：如果你想追究起来：具有相同数量并且顺序相同的正数列表。

    ```
    my-pos-nums :: List<Number> -> List<Number>
    ```

+   给定一组数字，将每个元素替换为累加和，即从列表开头到该元素的所有元素的总和（含该元素）：

    ```
    my-running-sum :: List<Number> -> List<Number>
    ```

+   给定一个列表，从第一个元素开始，保留其中的每个交替元素：

    ```
    my-alternating :: List<Any> -> List<Any>
    ```

+   给定一组数字，计算数字的平均值：

    ```
    my-avg :: List<Number> -> List<Number>
    ```

要解决这类问题，我们应该做两件事：

+   构造函数行为的示例。

+   使用建议可能解决方案的模板。

这两个步骤听起来很简单，但有几个细微之处，我们将探讨。

## 6.3 标量答案的结构性问题

让我们为上述几个函数写出一些示例。我们将以一种非常具体、风格化的方式编写示例。首先，我们应该至少构造两个示例：一个是空的，另一个至少有一个链接，这样我们就涵盖了两种非常广泛的列表类型。然后，我们应该有更多针对问题陈述的列表类型的具体示例。最后，我们应该有更多示例来说明我们如何考虑解决问题。

### 6.3.1 my-len：示例

我们没有精确定义“列表的长度”是什么意思。在尝试编写示例时，我们立即面对这个问题。空列表的长度是多少？

> 现在就做！
> 
> > 你认为呢？

两个常见的示例是 0 和 1。后者，1，看起来肯定合理。但是，如果你把列表写成 [list: ]，现在它看起来不太对：显然（正如 empty 这个名称所暗示的那样）这是一个空列表，并且空列表中没有元素。因此，习惯上声明

```
my-len(empty) is 0
```

对于像[list: 7]这样的列表呢？嗯，显然它只有一个元素（7），所以

```
my-len([list: 7]) is 1
```

类似地，对于像[list: 7, 8, 9]这样的列表，我们会说

```
my-len([list: 7, 8, 9]) is 3
```

现在让我们从另一个角度来看最后一个例子。考虑参数[list: 7, 8, 9]。它的第一个元素是 7，其余部分是[list: 8, 9]。嗯，7 是一个数字，而不是一个列表；但[list: 8, 9]显然是一个列表，所以我们可以问它的长度。my-len([list: 8, 9])是多少？它有两个元素，所以

```
my-len([list: 8, 9]) is 2
```

列表的第一个元素是 8，而其余部分是[list: 9]。它的长度是多少？请注意，我们之前问过一个非常类似的问题，关于列表[list: 7]的长度。但是[list: 7]不是[list: 7, 8, 9]的子列表，而我们起初的列表是，而[list: 9]是。使用与之前相同的推理，我们可以说

```
my-len([list: 9]) is 1
```

这个最后一个列表的其余部分当然是空列表，我们已经决定其长度为 0。将这些示例放在一起，并用其另一种形式写出 empty，我们得到以下结果：

```
my-len([list: 7, 8, 9]) is 3
my-len([list:    8, 9]) is 2
my-len([list:       9]) is 1
my-len([list:        ]) is 0
```

我们可以将其另一种写法（注意右侧）为

```
my-len([list: 7, 8, 9]) is 1 + 2
my-len([list:    8, 9]) is 1 + 1
my-len([list:       9]) is 1 + 0
my-len([list:        ]) is     0
```

由此，也许你可以开始看到一个模式。对于空列表，长度为 0。对于非空列表，它是 1（第一个元素对列表长度的“贡献”）加上列表其余部分的长度的总和。也就是说，

```
my-len([list: 7, 8, 9]) is 1 + my-len([list: 8, 9])
my-len([list:    8, 9]) is 1 + my-len([list:    9])
my-len([list:       9]) is 1 + my-len([list:     ])
my-len([list:        ]) is 0
```

也就是说，我们可以使用计算出的 my-len 在列表的其余部分上计算出整个列表的答案。

仔细检查所有这些，并确保你理解这些计算。这将对我们后面如何编写程序至关重要！

### 6.3.2my-sum：示例

类似的逻辑适用于我们如何处理像 my-sum 这样的函数。我们希望空列表的总和是多少？嗯，可能并不是完全清楚，所以让我们暂时继续。列表[list: 7, 8, 9]的总和是多少？显然，我们打算它是 24。让我们看看结果如何。

暂时搁置空列表，以下是我们可以达成一致的总和：

```
my-sum([list: 7, 8, 9]) is 7 + 8 + 9
my-sum([list:    8, 9]) is     8 + 9
my-sum([list:       9]) is         9
```

这与以下相同：

```
my-sum([list: 7, 8, 9]) is 7 + my-sum([list: 8, 9])
my-sum([list:    8, 9]) is 8 + my-sum([list:    9])
my-sum([list:       9]) is 9 + my-sum([list:     ])
```

由此，我们可以看出空列表的总和必须为 0：零被称为加法恒等式：一个说法是，将零添加到任何数字 N 中都会得到 N。因此，它是空列表的长度是有道理的，因为空列表没有项目可以贡献给总和。你能想出乘法恒等式是什么吗？

```
my-sum(empty) is 0
```

再次观察，我们如何使用计算出的 my-sum 的结果来计算整个列表的结果。

### 6.3.3 从示例到代码

有了这些示例，我们现在可以将它们转换为代码。我们引入了 cases 结构，它让我们区分不同类型的列表，并使用它来为每种类型的列表提供答案。

情况的语法如下：[填充] [填充模板]

现在让我们使用 cases 来定义 my-len：

```
fun my-len(l):
  cases (List) l:
    | empty      => 0
    | link(f, r) => 1 + my-len(r)
  end
end
```

这是从我们的示例中得出的：当列表为空时，my-len 产生 0；当它不为空时，我们将其余部分的长度（这里是 r）加一。同样，让我们定义 my-sum：

```
fun my-sum(l):
  cases (List) l:
    | empty      => 0
    | link(f, r) => f + my-sum(r)
  end
end
```

注意它们在代码中是多么相似，以及数据结构如何迅速地为程序的结构提供了结构。这是一个你很快会非常熟悉的模式！

## 6.4 列表答案的结构问题

现在让我们来解决产生列表作为答案的函数。

### 6.4.1 我的字符串长度：示例和代码

一如既往，我们将从一些示例开始。给定一个字符串列表，我们想要每个字符串的长度（按照相同的顺序）。因此，这是一个合理的例子：

```
my-str-len([list: "hi", "there", "mateys"]) is [list: 2, 5, 6]
```

正如我们以前所做的，我们应该考虑以上例子的每个子问题的答案：

```
my-str-len([list:       "there", "mateys"]) is [list:    5, 6]
my-str-len([list:                "mateys"]) is [list:       6]
```

或者，换句话说：

```
my-str-len([list: "hi", "there", "mateys"]) is link(2, [list: 5, 6])
my-str-len([list:       "there", "mateys"]) is link(5, [list:    6])
my-str-len([list:                "mateys"]) is link(6, [list:     ])
```

这告诉我们空列表的响应应该是空的：

```
my-str-len(empty) is empty
```

请注意，为了简洁起见，我们已经写出了转换每个字符串（2、5 和 6）的答案，每个答案都是通过将字符串长度应用于列表中的第一个元素而获得的。因此，我们可以从中制定一个解决方案：

```
fun my-str-len(l):
  cases (List) l:
    | empty => empty
    | link(f, r) =>
      link(string-length(f), my-str-len(r))
  end
end
```

### 6.4.2 我的正数：示例和代码

> 立即行动！
> 
> > 构造我们从输入 [list: 1, -2, 3, -4] 得到的示例序列。

我们开始吧：

```
my-pos-nums([list: 1, -2, 3, -4]) is [list: 1, 3]
my-pos-nums([list:    -2, 3, -4]) is [list:    3]
my-pos-nums([list:        3, -4]) is [list:    3]
my-pos-nums([list:           -4]) is [list:     ]
my-pos-nums([list:             ]) is [list:     ]
```

我们可以用以下形式写出它：

```
my-pos-nums([list: 1, -2, 3, -4]) is link(1, [list: 3])
my-pos-nums([list:    -2, 3, -4]) is         [list: 3]
my-pos-nums([list:        3, -4]) is link(3, [list: ])
my-pos-nums([list:           -4]) is         [list: ]
my-pos-nums([list:             ]) is         [list: ]
```

或者，更明确地说，

```
my-pos-nums([list: 1, -2, 3, -4]) is link(1, my-pos-nums([list: -2, 3, -4]))
my-pos-nums([list:    -2, 3, -4]) is         my-pos-nums([list:     3, -4])
my-pos-nums([list:        3, -4]) is link(3, my-pos-nums([list:        -4]))
my-pos-nums([list:           -4]) is         my-pos-nums([list:          ])
my-pos-nums([list:             ]) is         [list: ]
```

也就是说，当第一个元素为正时，我们将其连接到计算列表其余部分的我的正数结果中；当第一个元素为负时，结果只是计算列表其余部分的我的正数。这产生了以下程序：

```
fun my-pos-nums(l):
  cases (List) l:
    | empty => empty
    | link(f, r) =>
      if f > 0:
        link(f, my-pos-nums(r))
      else:
        my-pos-nums(r)
      end
  end
end
```

> 立即行动！
> 
> > 我们的示例集是否全面？

其实不是。我们还没有考虑许多示例，比如以正数结尾的列表和包含 0 的列表。

> 练习
> 
> > 通过这些示例看看它们如何影响程序！

### 6.4.3 我的替代：第一次尝试

再次，我们将从示例开始。

> 立即行动！
> 
> > 计算从列表 [list: 1, 2, 3, 4, 5, 6] 开始的我的替代结果。

这是它们的计算结果：<alternating-egs-1> ::=

```
check:
  my-alternating([list: 1, 2, 3, 4, 5, 6]) is [list: 1, 3, 5]
  my-alternating([list:    2, 3, 4, 5, 6]) is [list: 2, 4, 6]
  my-alternating([list:       3, 4, 5, 6]) is [list:    3, 5]
  my-alternating([list:          4, 5, 6]) is [list:    4, 6]
end
```

等等，什么？以上两个答案都是正确的，但第二个答案并没有帮助我们构建第一个答案。这意味着我们到目前为止解决这些问题的方式还不够，我们还需要更多的思考。我们稍后会回到这个问题 [我的替代：示例和代码 和 我的替代：示例和代码]。

### 6.4.4 我的累积和：第一次尝试

再一次，我们将从一个例子开始。

> 立即行动！
> 
> > 计算从列表 [list: 1, 2, 3, 4, 5] 开始的我的累积和结果。

这是我们的前几个示例的样子：<running-sum-egs-1> ::=

```
check:
  my-running-sum([list: 1, 2, 3, 4, 5]) is [list: 1, 3, 6, 10, 15]
  my-running-sum([list:    2, 3, 4, 5]) is [list: 2, 5, 9, 14]
  my-running-sum([list:       3, 4, 5]) is [list: 3,  7, 12]
end
```

再次，似乎没有明显的联系在列表其余部分的结果和整个列表的结果之间。（这并不严格正确：我们仍然可以按照以下方式排列答案：

```
my-running-sum([list: 1, 2, 3, 4, 5]) is [list: 1, 3, 6, 10, 15]
my-running-sum([list:    2, 3, 4, 5]) is [list:    2, 5,  9, 14]
my-running-sum([list:       3, 4, 5]) is [list:       3,  7, 12]
```

并且观察我们正在计算列表的其余部分的答案，然后将第一个元素添加到答案中的每个元素，并将第一个元素链接到前面。原则上，我们可以直接计算这个解决方案（正如我们将在稍后看到的那样[REF]），但是目前这可能比找到一个更简单的方法来回答它更费力。）

我们稍后也会回到这个函数 [my-running-sum: Examples and Code]。

## 6.5 子域的结构问题

### 6.5.1my-max：示例

现在让我们找到列表的最大值。为了简单起见，假设我们只处理数字列表。我们应该构造什么样的列表？显然，我们应该有空列表和非空列表...但是还有什么？像 [list: 1, 2, 3] 这样的列表是一个好的例子吗？嗯，这没问题，但是我们还应该考虑列表中的最大值在开始而不是结束；最大值可能在中间；最大值可能重复；最大值可能是负数；等等。虽然不全面，但这里是一组小但有趣的例子：

```
my-max([list: 1, 2, 3]) is 3
my-max([list: 3, 2, 1]) is 3
my-max([list: 2, 3, 1]) is 3
my-max([list: 2, 3, 1, 3, 2]) is 3
my-max([list: 2, 1, 4, 3, 2]) is 4
my-max([list: -2, -1, -3]) is -1
```

my-max(empty) 怎么样？

> 现在就做！
> 
> > 我们能把 my-max(empty) 定义为 0 吗？返回空列表的 0 已经成功两次了！

我们一会儿会回到这个问题。在我们继续之前，了解一下在 Pyret 中已经定义了一个叫做 num-max 的函数，它可以比较两个数字：

```
num-max(1, 2) is 2
num-max(-1, -2) is -1
```

> 练习
> 
> > 假设 num-max 还没有内置。你能定义它吗？你会发现你对布尔值所学的东西很有用。记得写一些测试！

现在我们可以看看 my-max 在工作了：

```
my-max([list: 1, 2, 3]) is 3
my-max([list:    2, 3]) is 3
my-max([list:       3]) is 3
```

嗯。那并没有真正教给我们什么，对吧？也许，我们不能确定。而且我们还不知道该怎么处理空。让我们尝试第二个示例输入：

```
my-max([list: 3, 2, 1]) is 3
my-max([list:    2, 1]) is 2
my-max([list:       1]) is 1
```

这实际上也告诉了我们一些有用的信息，但也许我们还看不到。让我们尝试一些更有雄心的事情：

```
my-max([list: 2, 1, 4, 3, 2]) is 4
my-max([list:    1, 4, 3, 2]) is 4
my-max([list:       4, 3, 2]) is 4
my-max([list:          3, 2]) is 3
my-max([list:             2]) is 2
```

注意观察剩余列表的最大值如何给我们一个候选答案，但是与第一个元素进行比较给我们一个确定的答案：

```
my-max([list: 2, 1, 4, 3, 2]) is num-max(2, 4)
my-max([list:    1, 4, 3, 2]) is num-max(1, 4)
my-max([list:       4, 3, 2]) is num-max(4, 3)
my-max([list:          3, 2]) is num-max(3, 2)
my-max([list:             2]) is …
```

最后一个有点尴尬：我们想写

```
my-max([list:             2]) is num-max(2, …)
```

但是我们并不真正知道空列表的最大值（或最小值，或任何其他元素），但是我们只能向 num-max 提供数字。因此，略过这个可疑的情况，我们剩下的是

```
my-max([list: 2, 1, 4, 3, 2]) is num-max(2, my-max([list: 1, 4, 3, 2]))
my-max([list:    1, 4, 3, 2]) is num-max(1, my-max([list:    4, 3, 2]))
my-max([list:       4, 3, 2]) is num-max(4, my-max([list:       3, 2]))
my-max([list:          3, 2]) is num-max(3, my-max([list:          2]))
```

我们的例子再次有所帮助：它们揭示了我们如何使用列表的每个剩余部分的答案来计算整个列表的答案，而整个列表的答案又是另一个列表的剩余部分，依此类推。如果你回头看一下我们上面写过的其他示例列表，你会发现模式也适用于那里。然而，现在是时候面对空情况了。真正的问题是，我们没有空列表的最大值：无论我们提供的数字是多少，总有一个比它更大的数字（假设我们的计算机足够大），可以成为答案。简而言之，询问空列表的最大值（或最小值）是不合逻辑的：“最大值”这个概念仅在非空列表上定义！也就是说，当被问及空列表的最大值时，我们应该发出错误信号：

```
my-max(empty) raises ""
```

（这就是在 Pyret 中我们说它会生成错误的方式；我们不关心错误的细节，因此为空字符串）。

### 6.5.2my-max: 从示例到代码

再次，我们可以将上述例子编码，即将它们转换为适用于所有实例的统一程序。然而，现在我们有了一个转折。如果我们盲目地遵循我们之前使用的模式，我们最终会得到：

```
fun my-max(l):
  cases (List) l:
    | empty      => raise("not defined for empty lists")
    | link(f, r) => num-max(f, my-max(r))
  end
end
```

> 现在动手！
> 
> > 这有什么问题？

考虑列表 [list: 2]。这变成了

```
num-max(2, my-max([list: ]))
```

当然会引发错误。因此，这个函数永远不会对任何具有一个或多个元素的列表起作用！

这是因为我们需要确保不要尝试计算空列表的最大值。有两种方法可以做到这一点。我们现在来看一种方法，稍后回到另一种方法[REF: 累加器]。

回到我们的例子，我们看到在调用 my-max 之前，我们需要做的是检查列表的剩余部分是否为空。如果是的话，我们根本不想调用 my-max。也就是：

```
fun my-max(l):
  cases (List) l:
    | empty      => raise("not defined for empty lists")
    | link(f, r) =>
      cases (List) r:
        | empty => …
        | …
      end
  end
end
```

我们马上会回到当剩余部分不为空时该怎么办的问题。如果列表 l 的剩余部分为空，我们上面的例子告诉我们最大值是列表中的第一个元素。因此，我们可以填写这个：

```
fun my-max(l):
  cases (List) l:
    | empty      => raise("not defined for empty lists")
    | link(f, r) =>
      cases (List) r:
        | empty => f
        | …
      end
  end
end
```

特别注意，没有调用 my-max。然而，如果列表不为空，我们上面的例子告诉我们 my-max 将给出列表剩余部分的最大值，我们只需要将这个答案与第一个元素（f）进行比较：

```
fun my-max(l):
  cases (List) l:
    | empty      => raise("not defined for empty lists")
    | link(f, r) =>
      cases (List) r:
        | empty => f
        | else  => num-max(f, my-max(r))
      end
  end
end
```

而确实，这个定义完成了任务！

### 6.5.3my-alternating: 示例和代码

回顾一下 my-alternating: 第一次尝试，我们可以看到每个交替的例子都是我们想要的。问题在于，要从一个例子到下面的两个例子，我们必须移除两个元素，而不仅仅是一个。也就是说，我们必须假装我们的列表是成对的元素，而不是单个元素。就示例而言，这看起来如下：

```
my-alternating([list: 1, 2, 3, 4, 5, 6]) is [list: 1, 3, 5]
my-alternating([list:       3, 4, 5, 6]) is [list:    3, 5]
my-alternating([list:             5, 6]) is [list:       5]
my-alternating([list:                 ]) is [list:        ]
```

现在很容易看出如何构建一个程序：保留第一个元素，跳过第二个元素，然后重复。让我们看看使用模板能走多远：

```
fun my-alternating(l):
  cases (List) l:
    | empty => empty
    | link(f, r) =>
      link(f, … r …)
  end
end
```

> 现在动手！
> 
> > 想一想如何完成这个定义。

在我们继续之前，有一个小问题：我们的例子不足以涵盖我们将遇到的所有情况。具体来说，要以两个元素遍历，我们必须有两个元素，但我们可能没有：列表可能只有奇数个元素。也就是说，我们可能会有

```
my-alternating([list: 1, 2, 3, 4, 5]) is [list: 1, 3, 5]
my-alternating([list:       3, 4, 5]) is [list:    3, 5]
my-alternating([list:             5]) is [list:       5]
```

这意味着：我们不会总是以空列表终止。我们必须准备以一个元素的列表终止。这提示了我们如何完成定义：

```
fun my-alternating(l):
  cases (List) l:
    | empty => empty
    | link(f, r) =>
      cases (List) r: # note: deconstructing r, not l
        | empty =>    # the list has an odd number of elements
          [list: f]
              | link(fr, rr) =>
                # fr = first of rest, rr = rest of rest
                link(f, my-alternating(rr))
      end
  end
end
```

在 my-alternating：示例和代码中，我们将看到另一种解决这个问题的方法。

## 6.6 更多具有标量答案的结构性问题

### 6.6.1my-avg：示例

现在让我们尝试计算一组数字的平均值。让我们从示例列表[list: 1, 2, 3, 4]开始，并从中找出更多例子。这个列表中数字的平均值显然是(1 + 2 + 3 + 4)/4，或 10/4。

根据列表的结构，我们看到剩余列表是[list: 2, 3, 4]，其余部分是[list: 3, 4]，依此类推。得到的平均值是：

```
my-avg([list: 1, 2, 3, 4]) is 10/4
my-avg([list:    2, 3, 4]) is 9/3
my-avg([list:       3, 4]) is 7/2
my-avg([list:          4]) is 4/1
```

问题是，我们如何从子列表的答案得到整个列表的答案并不清楚。也就是说，给定以下两个信息：

+   剩余列表的平均值为 9/3，即 3。

+   列表中的第一个数字是 1。

我们如何确定整个列表的平均值必须是 10/4？如果你不清楚，不要担心：仅凭这两个信息，是不可能的！以下是一个更简单的例子，解释了为什么。假设列表中的第一个值是 1，剩余列表的平均值为 2。以下是两个符合此描述的非常不同的列表：

```
[list: 1, 2]    # the rest has one element with sum 2
[list: 1, 4, 0] # the rest has two elements with sum 4
```

整个第一个列表的平均值为 3/2，而整个第二个列表的平均值为 5/3，两者并不相同。

也就是说，要计算整个列表的平均值，甚至不需要知道剩余列表的平均值。相反，我们需要知道剩余列表的总和和长度。有了这两个信息，我们可以将第一个值加到总和中，将 1 加到长度中，并计算新的平均值。

原则上，我们可以尝试制作一个返回所有这些信息的平均函数。相反，将任务简单分解为两个较小的任务会更简单。毕竟，我们已经看到如何计算长度和如何计算总和。因此，平均值可以简单地使用这些现有函数：

```
fun my-avg(l):
  my-sum(l) / my-len(l)
end
```

> 立即行动！
> 
> > 空列表的平均值应该是多少？上面的代码产生了你期望的结果吗？

就像我们之前讨论过关于最大值[具有子域的结构性问题]一样，空列表的平均值不是一个明确定义的概念。因此，适当的做法是发出错误信号。上面的实现做到了这一点，但效果不佳：它在除法上报告错误。更好的编程实践是捕获这种情况并立即报告错误，而不是希望其他函数会报告错误。

> 练习
> 
> > 修改上面的`my-avg`，当给出空列表时发出错误信号。

因此，我们看到我们使用的推断代码的过程——从示例中推断代码——并不总是足够，我们需要更复杂的技术来解决一些问题。然而，请注意，从示例中工作有助于我们快速识别这种方法何时有效，何时无效。此外，如果你仔细观察，你会注意到上面的示例暗示了如何解决问题：在我们的第一个示例中，我们写下了像 10/4、9/3 和 7/2 这样的答案，这对应于数字之和除以长度。因此，以这种形式写答案（而不是例如将第二个写为 3）已经揭示了解决方案的结构。

## 6.7 累加器的结构问题

现在我们准备解决我们留下的问题。它们将需要一种新的技术来解决。

### 6.7.1`my-running-sum`：示例和代码

回想一下我们是如何开始的 my-running-sum: First Attempt。我们的示例[<running-sum-egs-1>]展示了以下问题。当我们处理列表的其余部分时，我们忘记了之前的一切。也就是说，当从 2 开始处理列表时，我们忘记了之前看到的 1；当从 3 开始时，我们忘记了之前看到的 1 和 2；依此类推。换句话说，我们一直在忘记过去。我们需要一种避免这种情况的方法。

我们可以做的最简单的事情就是简单地改变我们的函数来携带这个“记忆”，或者我们将其称为累加器。也就是说，想象我们正在定义一个名为`my-rs`的新函数。它将消耗一个数字列表并产生一个数字列表，但另外它还将取当前列表之前数字的总和。

> 现在开始吧！
> 
> > 初始总和应该是多少？

最初没有“先前的列表”，所以我们将使用加法恒等式：0。`my-rs`的类型是

```
my-rs :: Number, List<Number> -> List<Number>
```

现在让我们重新将我们的示例从<running-sum-egs-1>重新作为`my-rs`的示例：

```
my-rs( 0, [list: 1, 2, 3, 4, 5]) is [list:  0 + 1] + my-rs( 0 + 1, [list: 2, 3, 4, 5])
my-rs( 1, [list:    2, 3, 4, 5]) is [list:  1 + 2] + my-rs( 1 + 2, [list:    3, 4, 5])
my-rs( 3, [list:       3, 4, 5]) is [list:  3 + 3] + my-rs( 3 + 3, [list:       4, 5])
my-rs( 6, [list:          4, 5]) is [list:  6 + 4] + my-rs( 6 + 4, [list:          5])
my-rs(10, [list:             5]) is [list: 10 + 5] + my-rs(10 + 5, [list:           ])
my-rs(15, [list:              ]) is empty
```

也就是说，`my-rs`转换为以下代码：

```
fun my-rs(acc, l):
  cases (List) l:
    | empty => empty
    | link(f, r) =>
      new-sum = acc + f
      link(new-sum, my-rs(new-sum, r))
  end
end
```

��后剩下的就是从`my-running-sum`中调用它：

```
fun my-running-sum(l):
  my-rs(0, l)
end
```

注意到我们并没有改变`my-running-sum`本身来接受额外的参数。这样做有多个原因。[FILL]

### 6.7.2`my-alternating`：示例和代码

回想一下我们在 my-alternating: First Attempt 中的努力，我们在 my-alternating: Examples and Code 中解决了这个问题。在那里，我们通过以稍微不同的方式考虑列表来解决问题：我们尽可能地跳过两个元素，这样我们看到的第一个元素总是我们想要保留作为答案的元素。在这里，我们将看到另一种思考相同问题的方式。

返回我们已经看过的示例[<alternating-egs-1>]。正如我们已经指出的[我的交替：示例和代码]，实际上我们想要从每个交替示例中得到输出。一种选择是基本上每次遍历列表两个元素。另一种选择是每次只遍历一个元素，但要跟踪我们是否处于奇数还是偶数元素位置-即，向我们的程序添加“内存”。由于我们只需要跟踪一个信息片段，我们可以使用布尔值来做到这一点。让我们为此定义一个新函数：

```
my-alt :: List<Any>, Boolean -> List<Any>
```

额外的参数累积我们是否处于要保留的元素还是要丢弃的元素。我们可以重用现有的列表函数模板。当我们有一个元素时，我们必须咨询累加器是否保留它。如果它的值为真，则将其链接到答案；否则，我们将忽略它。但是，当我们处理列表的其余部分时，我们必须记住更新累加器：如果我们保留了一个元素，我们不希望保留下一个元素，反之亦然。

```
fun my-alt(l, keep):
  cases (List) l:
    | empty => empty
    | link(f, r) =>
      if keep:
        link(f, my-alt(r, false))
      else:
        my-alt(r, true)
  end
end
```

最后，我们必须确定累加器的初始值。在这种情况下，由于我们想要交替保留从第一个元素开始的元素，所以它的初始值应该是 true：

```
fun my-alternating(l):
  my-alt(l, true)
end
```

## 6.8 处理多个答案

上面的讨论假设给定输入只有一个答案。这通常是正确的，但它还取决于问题的措辞方式和我们选择生成示例的方式。我们现在将详细研究这个问题。

### 6.8.1uqiq：问题设定

考虑写作 uniq 的任务：uniq 是类似行为的 Unix 实用程序的名称；因此名字的拼写也类似。给定一个值列表，它产生相同元素的集合，同时避免任何重复项（因此 uniq，缩写为“unique”）。

考虑以下输入：[list: 1, 2, 1, 3, 1, 2, 4, 1]。

> 现在开始！
> 
> > 这个输入生成的示例序列是什么？停下来尝试手工完成这个是非常重要的。正如我们将看到的那样，有多种解决方案，你考虑生成的内容非常有用。即使你不能生成一个序列，尝试这样做也会更好地为你阅读下面的内容做准备。

你是如何获得你的例子的？如果你只是“花了一会儿时间思考然后写下了一些东西”，你可能得到了或者可能没有得到可以转换为程序的东西。程序只能系统地进行；它们不能“思考”。所以，希望你以计算答案的明确定义路径进行。

### 6.8.2uniq：示例

结果有几个可能的答案，因为我们故意（有意地）没有明确说明问题。假设列表中有两个值的实例；我们保留哪一个，第一个还是第二个？一方面，由于这两个实例必须是等价的，所以无所谓，但对于编写具体示例和推导解决方案却很重要。

例如，你可能生成了这个序列：

```
examples:
  uniq([list: 1, 2, 1, 3, 1, 2, 4, 1]) is [list: 3, 2, 4, 1]
  uniq([list:    2, 1, 3, 1, 2, 4, 1]) is [list: 3, 2, 4, 1]
  uniq([list:       1, 3, 1, 2, 4, 1]) is [list: 3, 2, 4, 1]
  uniq([list:          3, 1, 2, 4, 1]) is [list: 3, 2, 4, 1]
  uniq([list:             1, 2, 4, 1]) is [list:    2, 4, 1]
  uniq([list:                2, 4, 1]) is [list:    2, 4, 1]
  uniq([list:                   4, 1]) is [list:       4, 1]
  uniq([list:                      1]) is [list:          1]
  uniq([list:                       ]) is [list:           ]
end
```

但是，你可能也生成了以…开头的序列

```
uniq([list: 1, 2, 1, 3, 1, 2, 4, 1]) is [list: 1, 2, 3, 4]
```

或者

```
uniq([list: 1, 2, 1, 3, 1, 2, 4, 1]) is [list: 4, 3, 2, 1]
```

等等。让我们使用我们上面解决过的例子来工作。

### 6.8.3uniq：代码

这个问题的系统化方法是什么？当给定一个非空列表时，我们将其分成第一个元素和列表的其余部分。假设我们已经对剩余列表应用了 uniq 的答案。现在我们可以问：第一个元素是否在剩余列表中？如果是，则我们可以忽略它，因为它肯定是在剩余列表的 uniq 中。然而，如果它不在剩余列表中，将它与答案联系起来是至关重要的。

这转化为以下程序。对于空列表，我们返回空列表。如果列表不为空，我们检查第一个元素是否在剩余列表中。如果不是，我们将其包含进去；否则我们可以暂时忽略它。

这导致了以下程序：

```
fun uniq-rec(l :: List<Any>) -> List<Any>:
  cases (List) l:
    | empty => empty
    | link(f, r) =>
      if r.member(f):
        uniq-rec(r)
      else:
        link(f, uniq-rec(r))
      end
  end
end
```

我们将其称为 uniq-rec 而不是 uniq，以区别于其他版本的 uniq。

> 练习
> 
> > 请注意，我们使用 .member 来检查一个元素是否是列表的成员。编写一个函数 member，它接受一个元素和一个列表，并告诉我们该元素是否是列表的成员。

### 6.8.4uniq：减少计算

请注意，此函数具有重复的表达式。我们可以不必两次写入它，而只需调用一次并在两个地方使用结果：

```
fun uniq-rec2(l :: List<Any>) -> List<Any>:
  cases (List) l:
    | empty => empty
    | link(f, r) =>
      ur = uniq-rec(r)
      if r.member(f):
        ur
      else:
        link(f, ur)
      end
  end
end
```

尽管看起来我们仅仅是避免了重复表达式，通过将计算 uniq-rec(r) 移到条件之前，我们实际上以微妙的方式改变了程序的行为。我们将在[REC tail calls]时稍后讨论这一点。

你可能会认为，因为我们用一个函数调用替换了两个函数调用，所以我们减少了程序的计算量。并不是这样！两个函数调用都在同一个条件分支的两个分支中；因此，对于任何给定的列表元素，只会发生一次或另一次对 uniq 的调用。事实上，在这两种情况下，以前都有一次对 uniq 的调用，现在也是一样。因此，我们减少了源程序中的调用次数，但并没有减少程序运行时发生的调用次数。在这个意义上，本节的名称是故意误导的！

但是，我们可以执行一个有用的简化，这是由 uniq-rec2 的结构所启用的。我们目前检查 f 是否是 r 的成员，r 是所有剩余元素的列表。在我们的例子中，这意味着在第二轮中，我们检查 2 是否是列表 [list: 1, 3, 1, 2, 4, 1] 的成员。这是一个包含六个元素的列表，包括三个副本的 1。我们将 2 与两个 1 进行比较。然而，我们从第二次比较中没有收获任何东西。换句话说，我们可以将 uniq(r) 视为剩余列表的“摘要”，它对于检查成员的效果与 r 本身一样好，但它可能要短得多。当然，这正是 ur 所代表的。因此，我们可以将这种直觉编码如下：

```
fun uniq-rec3(l :: List<Any>) -> List<Any>:
  cases (List) l:
    | empty => empty
    | link(f, r) =>
      ur = uniq-rec(r)
      if ur.member(f):
        ur
      else:
        link(f, ur)
      end
  end
end
```

请注意，所有的改变都只是我们检查 ur 而不是 r 是否为成员。

> 练习
> 
> > 稍后[预测增长]，我们将学习如何正式研究程序运行所需时间的长短。根据那一部分介绍的度量标准，我们刚刚做的更改有没有任何区别？注意你的答案：这取决于我们如何计算列表的“长度”。

注意，如果列表从未包含重复项，那么我们检查成员身份的列表就不重要了，但是如果我们知道列表不包含重复项，我们就不会首先使用 uniq！我们将在（part "sets"）中回到列表和重复元素的问题。

### 6.8.5uniq：示例和代码变体

正如我们之前提到的，你可能已经写下了其他示例序列。这是一个非常不同的过程：

+   从给定的整个列表和空白答案（到目前为止）开始。

+   对于每个列表元素，检查它是否已经在到目前为止的答案中。如果是，则忽略它，否则将答案扩展为包含它。

+   当列表中没有更多元素时，到目前为止的答案就是整个列表的答案。

注意，这个解决方案假设我们在遍历列表时将答案累积起来。因此，我们甚至不能像之前那样只用一个参数写出这个例子。我们会认为一个自然的解决方案是询问我们是否可以仅通过已经定义的计算来解决问题，就像我们之前做过的那样，而不是通过累加器。但是因为我们可以，所以在这里累加器是不必要的，并且甚至大大地复杂化了写下例子（试试看！）。

### 6.8.6uniq：为什么要生成一个列表？

如果你回顾一下 uniq 问题的原始陈述[uqiq：问题设置]，你会注意到它对输出的顺序没有任何要求；实际上，它甚至没有说输出需要是一个列表（因此没有顺序）。在这种情况下，我们应该考虑一下列表是否对这个问题有意义。实际上，如果我们不关心顺序，也不想要重复（根据 uniq 的定义），那么有一个更简单的解决方案，就是生成一个集合。Pyret 已经内置了集合，并且将列表转换为集合可以自动处理重复项。当然，从学习如何编写 uniq 的角度来看，这是作弊的，但值得记住的是，有时候产生的正确数据结构并不一定与我们给出的数据结构相同。此外，稍后[(part "sets")]，我们将看到如何自己构建集合（在这一点上，uniq 看起来会很熟悉，因为它是集合性质的核心）。

## 6.9 单态列表和多态类型

之前我们写下了像这样的合同：

```
my-len :: List<Any> -> Number
my-max :: List<Any> -> Any
```

这些原因令人不满意。
