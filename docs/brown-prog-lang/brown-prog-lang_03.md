# 从重复表达式到函数

|     [3.1 示例：月球重量](https://wiki.example.org/example_moon_weight) |
| --- |
|     [3.2 Example: Japanese Flag](https://wiki.example.org/example_japanese_flag) |
|     [3.3 Tests: Keeping Track of Examples](https://wiki.example.org/tests_keeping_track_of_examples) |
|     [3.4 Type Annotations](https://wiki.example.org/type_annotations) |
|     [3.5 Defining Functions in Steps](https://wiki.example.org/defining_functions_in_steps) |

## 3.1 示例：月球重量

假设我们负责为一支登月探险队配备装备。我们必须确定他们每个人在月球表面的重量。我们知道如何做到这一点—<wbr>我们之前看到过这个表达式 [REF]—<wbr>但是一遍又一遍地写这个表达式很无聊。此外，如果我们多次复制或重新输入表达式，迟早我们会出现抄写错误。这是 [DRY 原则](https://zh.wikipedia.org/wiki/不要重复你自己)的一个例子。另外，纠正错误本身就是一个有趣的计算机科学主题，我们稍后会详细讨论 [REF]。

当看到我们的月球重量计算时—<wbr>说

```
100 * 1/6
150 * 1/6
90 * 1/6
```

—<wbr>我们看到有一些部分是“固定的”，有一些部分是“变化的”。固定部分是我们不想重复的部分；变化部分是我们无法选择的部分（并且希望自由变化）。我们很希望能制作一个清晰地表明这种差异的包。我们将这样做的方式是编写一个函数。一个函数接受一个或多个参数，这些参数是变化的部分。具体来说，我们创建函数的方式是

+   写下所需计算的一些示例。

+   辨别哪些部分是固定的（上面，* 1/6），哪些是变化的（上面，100、150、90...）。

+   对于每个变化的部分，给它一个名称（比如 earth-weight），它将是代表它的参数。

+   重新编写示例，以适应这个参数：

    ```
    earth-weight * 1/6
    ```

    > 现在开始！
    > 
    > > 为什么只有一个表达式，而以前我们有很多个？

    我们只有一个表达式，因为整个重点是摆脱所有变化的部分，并用参数替换它们。

+   给函数取一个有意义的名字：例如，moon-weight。

+   在表达式周围编写函数的语法：

    ```
    fun <function name>(<parameters>):
      <the expression goes here>
    end
    ```

    表达式被称为函数的主体。

哇，那看起来像是很多工作！但最终产品确实非常简单：

```
fun moon-weight(earth-weight):
  earth-weight * 1/6
end
```

我们将一遍又一遍地进行相同的步骤，最终它们会变得如此直观，以至于我们甚至不会记得我们实际上是如何从示例到函数的：它将成为一个单一的、自然的步骤。我们如何使用这个？从 Pyret 的角度来看，月球重量只是另一个操作符，就像 num-expt 或 overlay 一样。因此：

```
moon-weight(100)
moon-weight(150)
moon-weight(90)
```

将产生与我们开始的表达式相同的答案，但由于复制或重新输入而在公式中不会出现任何错误。

## 3.2 示例：日本国旗

让我们创建另一个函数。还记得我们的日本国旗吗（[REF]）？每次我们想要不同大小的旗帜时，我们都必须更改 unit 的值并重新运行整个程序。相反，我们应该创建一个生成日本国旗的函数。

这个函数需要多少个参数？回顾我们早期的代码，我们看到唯一真正变化的是单位。其他所有事物都是根据那个计算的。因此，我们应该将单位转换为参数，并保持其余计算（已经以单位为单位）不变：

```
fun japan-flag(unit):
  bg-width = unit * 3
  bg-height = unit * 2
  circ-rad = 3/5 * 1/2 * bg-height
  red-circ = circle(circ-rad, "solid", "red")
  white-rect = rectangle(bg-width, bg-height, "solid", "white")
  overlay(red-circ, white-rect)
end
```

此函数体创建了几个本地[REF]变量，并最终生成了叠加表达式的结果，即旗帜形状。因此，我们可以多次使用它：

```
japan-flag(100)
japan-flag(200)
japan-flag(50)
```

在更改之间无需重新运行程序。请注意，如果生成的图像很大，Pyret 将用缩略图替换实际图像。点击缩略图查看完整图像。

## 3.3 测试：跟踪示例

在上述每个函数中，我们都从要计算的一些示例开始，从中概括出一个通用的公式，然后将其转换为函数，并在原始表达式的位置使用该函数。

现在我们完成了，最初的示例有什么用？扔掉它们似乎很诱人。但是，有一条关于软件的重要规则你应该了解：软件会不断发展。随着时间的推移，任何有用的程序都会发生变化和增长，因此可能最终产生与最初不同的值。有时这些是有意的，但有时这些是错误的结果（包括像在输入时意外添加或删除文本这样愚蠢但不可避免的错误）。因此，将这些示例保留下来以供将来参考总是有用的，这样如果函数偏离了它应该泛化的示例，你就可以立即得到通知。

Pyret 使这变得很容易。每个函数都可以附带一个记录示例的 where 子句。例如，我们的月球重量可以修改为：

```
fun moon-weight(earth-weight):
  earth-weight * 1/6
where:
  moon-weight(100) is 100 * 1/6
  moon-weight(150) is 150 * 1/6
  moon-weight(90) is 90 * 1/6
end
```

当以这种方式编写时，Pyret 将在每次运行程序时实际检查答案，并在您将函数更改为与这些示例不一致时通知您。

> 现在做！
> 
> > 检查一下！更改公式，例如，用函数的主体替换
> > 
> > ```
> > earth-weight * 1/3
> > ```
> > 
> > 看看发生了什么。

当然，你很难通过这么简单的函数犯错（除非打错字）。毕竟，这些示例与函数自身的主体非常相似。然而，后来我们会发现，这些示例可以比主体简单得多，因此很难确定它们是否表现相同，我们会发现很难使主体与示例匹配。事实上，在真实的软件生产中，这是非常常见的，专业程序员总是写下这些示例，称为测试，以确保他们的程序行为符合他们的期望。

## 3.4 类型注释

假设我们要在字符串上调用 moon-weight：

```
moon-weight("Armstrong")
```

> 现在做！
> 
> > 发生了什么？

Pyret 生成一个错误，说你不能用一个字符串乘以一个数字（教你算术的人会很高兴听到这个消息）。

在这样一个小函数中，这几乎无关紧要。但是如果你有一个更大的函数，从其深处得到类似的错误将令人沮丧。更糟糕的是，如果你得到的函数是别人写的，你需要阅读整个函数——<wbr>这可能要大得多——<wbr>才能弄清它消耗和生成什么样的值。

幸运的是，我们可以做得更好。Pyret 允许你在函数上写注释，指示它的值。具体来说，在 moon-weight 的情况下，因为它消耗和生成数字，我们将写：

```
fun moon-weight(earth-weight :: Number) -> Number:
  earth-weight * 1/6
end
```

为了简洁起见，我们省略了 where 示例，但你也可以写出来。现在，只需阅读函数，你就可以知道它消耗一个数字（:: Number 部分）并且也生成一个数字（-> Number 部分）。

> 现在做！
> 
> > 当你运行 moon-weight("Armstrong")时会发生什么？
> > 
> 现在做！
> 
> > japan-flag 的注释会是什么？

因为 japan-flag 消耗一个数字并产生一个图像，我们写：

```
fun japan-flag(unit :: Number) -> Image:
  bg-width = unit * 3
  bg-height = unit * 2
  circ-rad = 3/5 * 1/2 * bg-height
  red-circ = circle(circ-rad, "solid", "red")
  white-rect = rectangle(bg-width, bg-height, "solid", "white")
  overlay(red-circ, white-rect)
end
```

注意，这些注释显然是可选的：直到本节为止，我们的函数都没有。实际上，你可以在一个地方使用注释而不在另一个地方使用。此外，你可以在任何新变量上放置注释，而不仅仅是在参数中：例如，japan-flag 内部的变量也可以被注释。

> 现在做！
> 
> > 在每个空白处填上注释：
> > 
> > ```
> > fun japan-flag(unit :: Number) -> Image:
> >   bg-width :: ___ = unit * 3
> >   bg-height :: ___ = unit * 2
> >   circ-rad :: ___ = 3/5 * 1/2 * bg-height
> >   red-circ :: ___ = circle(circ-rad, "solid", "red")
> >   white-rect :: ___ = rectangle(bg-width, bg-height, "solid", "white")
> >   overlay(red-circ, white-rect)
> > end
> > ```

完全注释的函数将是：

```
fun japan-flag(unit :: Number) -> Image:
  bg-width :: Number = unit * 3
  bg-height :: Number = unit * 2
  circ-rad :: Number = 3/5 * 1/2 * bg-height
  red-circ :: Image = circle(circ-rad, "solid", "red")
  white-rect :: Image = rectangle(bg-width, bg-height, "solid", "white")
  overlay(red-circ, white-rect)
end
```

> 现在做！
> 
> > 更改其中一个注释使其不正确：例如，
> > 
> > ```
> > red-circ :: Number = circle(circ-rad, "solid", "red")
> > ```
> > 
> > +   什么时候会出错？是当你点击运行时还是只有当你实际使用 japan-flag 时？
> > +   
> > +   程序的哪一部分出错了？

我们放在注释中的东西——<wbr>Number、String 等——<wbr>被称为类型。类型帮助我们区分不同类型的数据。每个值都有一个类型，并且没有值有多于一个类型。因此，3 是一个 Number（没有其他类型），"hello"是一个 String（没有其他类型），依此类推。稍后[REF]我们将看到，我们可以“细化”类型，使得一个值可以有多个细化的类型：3 可以是一个数字，一个奇数，但也可以是一个质数，等等。在一些语言[REF]中，这些类型注释在程序运行之前被检查，因此你可以在运行程序之前了解可能的错误。在其他语言中，你只能在程序执行期间发现它们。Pyret 本身旨在提供两种模式，因此你可以选择在你的上下文中最合适的模式。

## 3.5 逐步定义函数

在编写函数时，逐步编写是很有用的。首先，给它一个名字，确保你了解它的类型，并写一些文档以提醒你的用户和读者，他们可能对你的函数不熟悉——几周后，可能就是你！——它的用途是什么。例如，这是一个给定工作小时数后计算相应工资的函数：

```
fun hours-to-wages(hours :: Number) -> Number:
  doc: "Compute total wage from hours, with overtime, at $10/hr base"
end
```

请注意，上述目的陈述未明确指出“加班”何时开始；在美国，这是每周 40 小时后。接下来，我们写下例子：

```
fun hours-to-wages(hours :: Number) -> Number:
  doc: "Compute total wage from hours, with overtime, at $10/hr base"
where:
  hours-to-wages(40) is 400
  hours-to-wages(40.5) is 407.5
  hours-to-wages(41) is 415
  hours-to-wages(0) is 0
  hours-to-wages(45) is 475
  hours-to-wages(20) is 200
end
```

示例应至少涵盖数据定义中提到的所有不同情况。例如，在这种情况下，有必要注意到第 40 小时不算加班，但第 41 小时算加班。请注意，通过以上方式编写示例，不太清楚哪种计算会产生这些答案；相比之下，编写

```
hours-to-wages(0)  is 0  * 10
hours-to-wages(20) is 20 * 10
hours-to-wages(40) is 40 * 10
```

请注意，我们甚至将 0 写成 0 * 10，以明确我们使用的是每小时$10 的费率……当然，我们也应该计算超过 40 小时的计算。现在，公式将变得复杂起来。前 40 小时，员工按每小时工资支付工资，这贡献了 40 * 10（就像上面的最后一个示例中一样）。对于每个额外的小时（即，总工作时间减去 40），他们将以 1.5 倍的工资支付，即，10 * 1.5。结合这两个部分，我们得到：

```
hours-to-wages(40.5) is (40 * 10) + ((40.5 - 40) * (10 * 1.5))
hours-to-wages(41)   is (40 * 10) + ((41   - 40) * (10 * 1.5))
hours-to-wages(45)   is (40 * 10) + ((45   - 40) * (10 * 1.5))
```

从这些例子中，我们可以确定身体的形状：

```
fun hours-to-wages(hours :: Number) -> Number:
  doc: "Compute total wage from hours, with overtime, at $10/hr base"
  if hours <= 40:
    hours * 10
  else:
    (40 * 10) + ((hours - 40) * (10 * 1.5))
  end
where:
  hours-to-wages(40) is 400
  hours-to-wages(40.5) is 407.5
  hours-to-wages(41) is 415
  hours-to-wages(0) is 0
  hours-to-wages(45) is 475
  hours-to-wages(20) is 200
end
```

hours-to-wages 函数始终假定每小时工资为$10。我们可以通过更改常量 10（代表小时工资的地方）来更改它以适应不同的小时工资，例如$20/小时：

```
fun hours-to-wages-20(hours :: Number) -> Number:
  doc: "Compute total wage from hours, accounting for overtime, at $20/hr base"
  if hours <= 40:
    hours * 20
  else:
    (40 * 20) + ((hours - 40) * (20 * 1.5))
  end
end
```

我们可以为每小时$30 的工人制作另一个函数副本，等等。然而，改变函数以适用于任何小时工资也是可能的，而且相当简单。我们注意到实现中的共享部分，并将其提取出来，向函数添加一个新参数。

```
fun hours-to-wages-at-rate(rate :: Number, hours :: Number) -> Number:
  doc: "Compute total wage from hours, accounting for overtime, at the given rate"
  if hours <= 40:
    hours * rate
  else:
    (40 * rate) + ((hours - 40) * (rate * 1.5))
  end
end
```

注意，我们将约定在参数列表的开头添加新参数。我们只需添加新参数（带有适当的注释），并用它替换所有常量的实例。

> 练习
> 
> > 编写一个名为 has-overtime 的函数，该函数接受小时数，并在小时数大于 40 时返回 true，否则返回 false。
> > 
> 练习
> 
> > 工作负数小时是没有意义的。编写一个使用 raise 函数在报告少于 0 小时时抛出错误的 hours-to-wages 版本。使用 raises 表单进行测试（阅读有关 raises 的[Pyret 文档](http://www.pyret.org/docs/latest/testing.html#%28part._testing_raises%29)）。
> > 
> 练习
> 
> > 编写一个名为 hours-to-wages-ot 的函数，该函数接受小时数、每小时工资和加班阈值，并产生总工资。任何超过加班阈值的工作时间都应以 1.5 倍的正常工资率计入，与以前一样。
