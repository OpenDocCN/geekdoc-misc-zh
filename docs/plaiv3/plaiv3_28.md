## 扩展计算器

显然，添加条件语句并没有改变我们的计算器之前的功能，我们可以保持它不变，只需专注于处理`if`：

```
(define (calc e)
  (type-case Exp e
    [(num n) n]
    [(plus l r) (+ (calc l) (calc r))]
    [(cnd c t e) …]))
```

事实上，我们可以递归地评估每个项，以防它有用：

```
(define (calc e)
  (type-case Exp e
    [(num n) n]
    [(plus l r) (+ (calc l) (calc r))]
    [(cnd c t e) … (calc c) … (calc t) … (calc e) …]))
```

让我们逐个来看这些。

但现在我们遇到了一个问题。调用`(calc c)`的结果是什么？我们期望它是一个某种布尔值。但我们语言中没有布尔值！

这还不是全部。在上面，我们既写了`(calc t)`也写了`(calc e)`。然而，条件语句的整个目的就是，我们不想评估两个，只想评估一个。所以我们必须根据某些标准来选择评估哪一个。
