## 扩展抽象语法树（AST）

因为我们将条件语句固定为三个部分，所以我们只需要在抽象语法树（AST）中表达这一点。这是直截了当的：

```
(define-type Exp
  [num (n : Number)]
  [plus (left : Exp) (right : Exp)]
  [cnd (test : Exp) (then : Exp) (else : Exp)])
```

真正的工作将在评估器中发生。
