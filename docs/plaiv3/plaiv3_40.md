## 缓存替换

我们反复——并且正确地——回溯到替换以了解程序应该如何工作，并且确实会在以后再次这样做。但是，作为评估技术的替换是混乱的。这要求我们不断重写程序文本，这需要与程序大小成线性关系的线性时间（这可以相当大）来处理每个变量绑定。大多数真实语言实现都不是这样做的。

相反，我们可能会考虑采用时空权衡：我们会用一点额外的空间来节省大量的时间。也就是说，我们将把替换保存在一个称为环境的数据结构中。环境记录名称及其对应的值：也就是说，它是一系列键值对。因此，每当遇到绑定时，我们会记住它的值，当我们遇到变量时，我们会查找它的值。

顺便说一句：与所有缓存一样，我们希望它们只在某个维度上提高性能，而不是改变意义。也就是说，我们不再希望替换定义我们如何产生答案。但是，我们仍然希望它告诉我们应该产生什么答案。这将在下面变得很重要。

我们将使用哈希表来表示环境：

```
(define-type-alias Env (Hashof Symbol Value))
(define mt-env (hash empty)) ;; "empty environment"
```

我们将需要解析器实际接受一个环境作为形式参数，以替换的形式使用。因此：

```
(interp : (Exp Env -> Value))
(define (interp e nv) …)
```

现在我们遇到变量时会发生什么？我们试图在环境中查找它。这可能成功，或者，在我们的上一个例子中，失败。我们将使用`hash-ref`，它在哈希表中查找键，并返回一个`Optionof`类型以考虑到失败的可能性。我们可以将其封装在一个我们将反复发现有用的函数中：

```
(define (lookup (s : Symbol) (n : Env))
  (type-case (Optionof Value) (hash-ref n s)
    [(none) (error s "not bound")]
    [(some v) v]))
```

如果查找成功，我们想要找到的值，它被包裹在`some`中。这个函数使我们的解析器保持非常干净和可读：

```
    [(varE s) (lookup s nv)]
```

最后，我们准备处理`let1`。这里会发生什么？我们必须

+   在`in`中评估表达式的主体

+   一个扩展了的环境，其中

+   新的名称

+   绑定到它的值。

呼吸一下！

幸运的是，这并不像听起来那么糟糕。同样，一个函数会大有帮助：

```
(extend : (Env Symbol Value -> Env))
(define (extend old-env new-name value)
  (hash-set old-env new-name value))
```

这样，我们可以清楚地看到结构：

```
    [(let1E var val body)
     (let ([new-env (extend nv
                            var
                            (interp val nv))])
```

（注意，我们在 Paret 中使用了`let`来定义`let1`。我们将会看到更多这样的例子……）

总的来说，我们的核心解析器现在是这样的：

```
(define (interp e nv)
  (type-case Exp e
    [(numE n) n]
    [(varE s) (lookup s nv)]
    [(plusE l r) (+ (interp l nv) (interp r nv))]
    [(let1E var val body)
     (let ([new-env (extend nv
                            var
                            (interp val nv))])
       (interp body new-env))]))
```

练习：

1.  如果我们没有在上面调用`(interp val nv)`会怎样？

1.  如果我们在调用`interp`时使用了`nv`而不是`new-env`会怎样？}

1.  在基于复制我们之前的内容的解析器中，还有其他错误吗？

1.  我们似乎扩展了环境，但从未从其中删除任何东西。这是否可以？如果不可以，它应该导致错误。哪个程序可以演示这个错误，并且它实际上是这样做的吗？（如果不是，为什么不是？）

这标志着我们第一个有趣的“编程语言”的结束。我们已经不得不处理一些相当微妙的作用域问题，以及如何解释它们。从这里开始，事情只会变得更加有趣！
