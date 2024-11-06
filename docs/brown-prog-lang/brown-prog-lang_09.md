# 递归数据

|  |
| --- |

有时，数据定义有一个指向自身的部分。例如，一个数字的链表：

```
data NumList:
  | nl-empty
  | nl-link(first :: Number, rest :: NumList)
end
```

继续定义示例，我们可以谈论空列表：

nl-代表 NumList。这样避免了与 Pyret 的 empty 冲突。

```
nl-empty
```

我们可以表示短列表，比如两个 4 的序列：

```
nl-link(4, nl-link(4, nl-empty))
```

由于这些是由数据的构造函数创建的，我们可以使用 cases 与它们：

```
    cases (NumList) nl-empty:
      | nl-empty => "empty!"
      | nl-link(first, rest) => "not empty"
    end

=>  "empty!"
```

```
    cases (NumList) nl-link(1, nl-link(2, nl-empty)):
      | nl-empty => "empty!"
      | nl-link(first, rest) => first
    end

=>  1
```

这种数据定义风格允许我们创建无界或任意大小的数据。给定一个 NumList，有一种简单的方法来制作一个新的、更大的列表：只需使用 nl-link。所以，我们需要考虑更大的列表：

```
nl-link(1,
  nl-link(2,
    nl-link(3,
      nl-link(4,
        nl-link(5,
          nl-link(6,
            nl-link(7,
              nl-link(8,
                nl-empty))))
```

让我们尝试编写一个名为 contains-3 的函数，如果 NumList 包含值 3，则返回 true，否则返回 false。

首先，我们的标题：

```
fun contains-3(nl :: NumList) -> Boolean:
  doc: "Produces true if the list contains 3, false otherwise"
end
```

接下来，一些测试：

```
fun contains-3(nl :: NumList) -> Boolean:
  doc: "Produces true if the list contains 3, false otherwise"
where:
  contains-3(nl-empty) is false
  contains-3(nl-link(3, nl-empty)) is true
  contains-3(nl-link(1, nl-link(3, nl-empty))) is true
  contains-3(nl-link(1, nl-link(2, nl-link(3, nl-link(4, nl-empty))))) is true
  contains-3(nl-link(1, nl-link(2, nl-link(5, nl-link(4, nl-empty))))) is false
end
```

接下来，我们需要用一个对 NumLists 的函数的模板来填充体部。我们可以从之前使用 cases 的类似模板开始：

```
fun contains-3(nl :: NumList) -> Boolean:
  doc: "Produces true if the list contains 3, false otherwise"
  cases (NumList) nl:
    | nl-empty => ...
    | nl-link(first, rest) =>
      ... first ...
      ... rest ...
  end
end
```

空列表肯定不包含数字 3，所以在 nl-empty 情况下答案必须是 false。在 nl-link 情况下，如果第一个元素是 3，我们已经成功地回答了问题。这只留下了参数是 nl-link 且第一个元素不等于 3 的情况：

```
fun contains-3(nl :: NumList) -> Boolean:
  cases (NumList) nl:
    | nl-empty => false
    | nl-link(first, rest) =>
      if first == 3:
        true
      else:
        # handle rest here
      end
  end
end
```

由于我们知道 rest 是一个 NumList（基于数据定义），我们可以使用 cases 表达式与它一起工作。这有点像再次填写模板的一部分：

```
fun contains-3(nl :: NumList) -> Boolean:
  cases (NumList) nl:
    | nl-empty => false
    | nl-link(first, rest) =>
      if first == 3:
        true
      else:
        cases (NumList) rest:
          | nl-empty => ...
          | nl-link(first-of-rest, rest-of-rest) =>
            ... first-of-rest ...
            ... rest-of-rest ...
        end
      end
  end
end
```

如果 rest 为空，则我们没有找到 3（就像我们检查原始参数 nl 时一样）。如果 rest 是一个 nl-link，那么我们需要检查列表的剩余部分中的第一个元素是否为 3：

```
fun contains-3(nl :: NumList) -> Boolean:
  cases (NumList) nl:
    | nl-empty => false
    | nl-link(first, rest) =>
      if first == 3:
        true
      else:
        cases (NumList) rest:
          | nl-empty => false
          | nl-link(first-of-rest, rest-of-rest) =>
            if first-of-rest == 3:
              true
            else:
              # fill in here ...
            end
        end
      end
  end
end
```

由于 rest-of-rest 是一个 NumList，我们可以再次为其填写 cases：

```
fun contains-3(nl :: NumList) -> Boolean:
  cases (NumList) nl:
    | nl-empty => false
    | nl-link(first, rest) =>
      if first == 3:
        true
      else:
        cases (NumList) rest:
          | nl-empty => false
          | nl-link(first-of-rest, rest-of-rest) =>
            if first-of-rest == 3:
              true
            else:
              cases (NumList) rest-of-rest:
                | nl-empty => ...
                | nl-link(first-of-rest-of-rest, rest-of-rest-of-rest) =>
                  ... first-of-rest-of-rest ...
                  ... rest-of-rest-of-rest ...
              end
            end
        end
      end
  end
end
```

看到这里了吗？没有任何好的方向。我们可以将此 cases 表达式复制任意次数，但我们永远无法回答仅比我们复制代码次数多一个元素的列表的问题。

那么该怎么办？我们尝试过使用另一个基于观察到 rest 是 NumList 的 cases 的副本的方法，而 cases 提供了一种有意义地将 NumList 分解的方法；实际上，这似乎是自然而然地导致的。

让我们回到问题开始的步骤，即在使用第一个检查 3 的模板之后：

```
fun contains-3(nl :: NumList) -> Boolean:
  cases (NumList) nl:
    | nl-empty => false
    | nl-link(first, rest) =>
      if first == 3:
        true
      else:
        # what to do with rest?
      end
  end
end
```

我们需要一种方法来计算值 3 是否包含在 rest 中。回顾数据定义，我们可以看到 rest 是一个完全有效的 NumList，仅仅是根据 nl-link 的定义。而且，我们有一个函数（或者说大部分函数）的工作是确定一个 NumList 是否包含 3：contains-3。这应该是我们可以用 rest 作为参数调用的东西，并且得到我们想要的值：

```
fun contains-3(nl :: NumList) -> Boolean:
  cases (NumList) nl:
    | nl-empty => false
    | nl-link(first, rest) =>
      if first == 3:
        true
      else:
        contains-3(rest)
      end
  end
end
```

看哪，所有上面定义的测试都通过了。当调用此函数时，逐步了解发生了什么是有用的。让我们看一个例子：

```
contains-3(nl-link(1, nl-link(3, nl-empty)))
```

首先，我们在所有出现 nl 的地方用参数值代替 nl；这只是函数调用的通常规则。

```
=>  cases (NumList) nl-link(1, nl-link(3, nl-empty)):
       | nl-empty => false
       | nl-link(first, rest) =>
         if first == 3:
           true
         else:
           contains-3(rest)
         end
     end
```

接下来，我们找到与构造函数 nl-link 匹配的情况，并将 nl-link 值的相应部分替换为第一个和 rest 标识符。

```
=>  if 1 == 3:
      true
    else:
      contains-3(nl-link(3, nl-empty))
    end
```

由于 1 不是 3，比较结果为 false，整个表达式评估为 else 分支的内容。

```
=>  if false:
      true
    else:
      contains-3(nl-link(3, nl-empty))
    end

=>  contains-3(nl-link(3, nl-empty))
```

这是另一个函数调用，所以这次我们将原始输入的 rest 字段 nl-link(3, nl-empty) 替换到 contains-3 的主体中。

```
=>  cases (NumList) nl-link(3, nl-empty):
      | nl-empty => false
      | nl-link(first, rest) =>
        if first == 3:
          true
        else:
          contains-3(rest)
        end
    end
```

再次将值替换到 nl-link 分支中。

```
=>  if 3 == 3:
      true
    else:
      contains-3(nl-empty)
    end
```

这一次，由于 3 是 3，我们选择了 if 表达式的第一个分支，整个原始调用评估为 true。

```
=>  if true:
      true
    else:
      contains-3(nl-empty)
    end

=> true
```

这个跟踪评估的有趣特点是，我们到达了包含-3(nl-link(3, nl-empty)) 表达式，这是对 contains-3 的正常调用；它甚至可以作为一个独立的测试用例。该实现通过对数据的非递归部分执行某些操作（检查是否等于 3），并将该结果与对数据的递归部分执行相同操作（contains-3）的结果结合起来。这种使用相同函数对自递归数据类型的递归的想法让我们扩展了模板以处理递归位置。

简单的设计方案规定了这个模板：

```
#|
fun num-list-fun(nl :: NumList) -> ???:
  cases (NumList) nl:
    | nl-empty => ...
    | nl-link(first, rest) =>
      ... first ...
      ... rest ...
  end
end
|#
```

然而，这个模板并没有给出如何处理 rest 字段的指导。我们将使用以下规则扩展模板：数据定义中的每个自递归位置在模板中变为自递归函数调用。因此，新模板如下所示：

```
#|
fun num-list-fun(nl :: NumList) -> ???:
  cases (NumList) nl:
    | nl-empty => ...
    | nl-link(first, rest) =>
      ... first ...
      ... num-list-fun(rest) ...
  end
end
|#
```

为了处理递归数据，设计方案只需要修改为具有这个扩展模板。当你看到一个递归数据定义（在 Pyret 编程中会有很多），你应该自然而然地开始思考递归调用将返回什么以及如何将它们的结果与数据类型的其他非递归部分结合起来。

> 练习
> 
> > 使用设计方案编写一个函数 contains-n，它接受一个 NumList 和一个数字，并返回该数字是否在 NumList 中。
> > 
> 练习
> 
> > 使用设计方案编写一个函数 sum，它接受一个 NumList，并返回其中所有数字的总和。空列表的总和为 0。
> > 
> 练习
> 
> > 使用设计方案编写一个函数 remove-3，它接受一个 NumList，并返回一个删除任何 3 的新 NumList。剩余的元素应该按照它们在输入中的顺序在列表中。
> > 
> 练习
> 
> > 编写一个名为 NumListList 的数据定义，表示 NumLists 的列表，并使用设计方案编写一个函数 sum-of-lists，它接受一个 NumListList 并生成一个包含子列表和的 NumList。
