## 值数据类型

因此，我们首先需要定义一个数据类型，以反映评估器可以产生的不同类型的值。我们将遵循一个约定，并将返回类型构造函数称为`…V`以区分输入。相应地，我们将输入称为`…E`（对于表达式）以区分输出。

首先，我们将重命名我们的表达式：

```
(define-type Exp
  [numE (n : Number)]
  [boolE (b : Boolean)]
  [plusE (left : Exp) (right : Exp)]
  [cndE (test : Exp) (then : Exp) (else : Exp)])
```

（除了构造函数的名称外，没有其他变化）。

现在我们引入一个`Value`数据类型来表示评估器可以产生的答案类型：

```
(define-type Value
  [numV (the-number : Number)]
  [boolV (the-boolean : Boolean)])
```

我们更新了评估器的类型：

```
(calc : (Exp -> Value))
```

以及早期部分很简单：

```
(define (calc e)
  (type-case Exp e
    [(numE n) (numV n)]
    [(boolE b) (boolV b)]
    …))
```
