## 首先解析器

现在行动：考虑我们想要为我们的解析器选择哪种类型。

我们的解析器需要产生什么？无论计算器消费什么，即`Expr`。它消费什么？用“方便”的语法编写的程序源表达式，即`S-Exp`。因此，它的类型必须是

```
(parse : (S-Exp -> Exp))
```

也就是说，它将人类友好的（更友好的）语法转换为计算机的内部表示。

编写这需要一定程度的繁琐。首先，我们需要一个条件来检查我们得到了哪种类型的 s 表达式：

```
(define (parse s)
  (cond
    [(s-exp-number? s) …]
    [(s-exp-list? s) …]))
```

如果它是一个数值 s 表达式，那么我们需要提取这个数字并将其传递给`num`构造函数：

```
(num (s-exp->number s))
```

否则，我们需要提取列表并检查列表中的第一项是否是加法符号。如果不是，我们发出错误信号：

```
     (let ([l (s-exp->list s)])
       (if (symbol=? '+
                     (s-exp->symbol (first l)))
           …
           (error 'parse "list not an addition")))
```

否则，我们通过递归两个子部分来创建一个加法项。

```
            (plus (parse (second l))
                  (parse (third l)))

```

将所有这些放在一起：

```
(define (parse s)
  (cond
    [(s-exp-number? s)
     (num (s-exp->number s))]
    [(s-exp-list? s)
     (let ([l (s-exp->list s)])
       (if (symbol=? '+
                     (s-exp->symbol (first l)))
           (plus (parse (second l))
                 (parse (third l)))
           (error 'parse "list not an addition")))]))
```

这一切似乎有点多，但幸运的是，这本书中解析的难度不会超过这个程度！从现在开始，你看到的所有内容基本上都是这种类型的模式，你可以自由地复制。

当然，我们应该确保我们的解析器有良好的测试。例如：

```
(test (parse `1) (num 1))
(test (parse `2.3) (num 2.3))
(test (parse `{+ 1 2}) (plus (num 1) (num 2)))
(test (parse `{+ 1
                 {+ {+ 2 3}
                    4}})
      (plus (num 1)
            (plus (plus (num 2)
                        (num 3))
                  (num 4))))
```

现在行动：我们是否应该编写其他类型的测试？

我们只写了正测试。我们还可以为预期出现错误的情况编写负测试：

```
(test/exn (parse `{1 + 2}) "")
```

`test/exn`接受一个字符串，该字符串必须是错误消息的子串。你可能会惊讶，上面的测试使用空字符串而不是，比如说，`"addition"`。尝试这个例子来调查为什么。你如何改进你的解析器来解决这个问题？

我们还应该检查的其他情况包括子部分太少或太多。例如，加法被定义为恰好接受两个子表达式。如果源程序包含零个、一个、三个、四个……会发生什么？这就是解析所要求的这种繁琐。

一旦我们考虑了这些情况，我们就处于一个愉快的位置，因为`parse`产生的输出是`calc`可以消费的。因此，我们可以组合这两个函数！更好的是，我们可以编写一个辅助函数来为我们完成这项工作：

```
(run : (S-Exp -> Number))
```

```
(define (run s)
  (calc (parse s)))
```

因此，我们现在可以用一种更方便的方式重写我们旧的评估器测试：

```
(test (run `1) 1)
(test (run `2.3) 2.3)
(test (run `{+ 1 2}) 3)
(test (run `{+ {+ 1 2} 3})
      6)
(test (run `{+ 1 {+ 2 3}})
      6)
(test (run `{+ 1 {+ {+ 2 3} 4}})
      10)
```

将其与我们在早期进行的`calc`测试进行比较！
