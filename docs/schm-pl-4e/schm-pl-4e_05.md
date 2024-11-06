# 第五章。控制操作

本章介绍了作为 Scheme 程序控制结构的语法形式和过程，第一节涵盖了最基本的控制结构，即过程应用，其余部分涵盖了顺序执行、条件评估、递归、映射、延迟评估、多值和在运行时构建的程序的评估。

### 第 5.1 节。过程应用

**语法：** `(*expr[0]* *expr[1]* ...)`

**返回：** 将`*expr[0]*`的值应用于`*expr[1]* ...`的值

过程应用是最基本的 Scheme 控制结构。在第一个位置没有语法关键字的结构化形式是一个过程应用。表达式`*expr[0]*`和`*expr[1]* ...`被评估；每个应该评估为单个值。在每个表达式被评估之后，`*expr[0]*`的值被应用于`*expr[1]* ...`的值。如果`*expr[0]*`不评估为过程，或者过程不接受提供的参数数量，那么将引发一个带有条件类型`&assertion`的异常。

过程和参数表达式的评估顺序是未指定的。可能是从左到右，从右到左，或者任何其他顺序。然而，评估是有保证的：无论选择了哪种顺序，每个表达式在下一个表达式的评估开始之前都会被完全评估。

`(+ 3 4) ![<graphic>](img/ch2_0.gif) 7

((if (odd? 3) + -) 6 2) ![<graphic>](img/ch2_0.gif) 8

((lambda (x) x) 5) ![<graphic>](img/ch2_0.gif) 5

(let ([f (lambda (x) (+ x x))])

(f 8)) ![<graphic>](img/ch2_0.gif) 16`

**过程：** `(apply *procedure* *obj* ... *list*)`

**返回：** 将`*procedure*`应用于`*obj* ...`和`*list*`的值

**库：** `(rnrs base)`, `(rnrs)`

`apply`调用`*procedure*`，将第一个`*obj*`作为第一个参数传递，第二个`*obj*`作为第二个参数传递，依此类推，对于`*obj* ...`中的每个对象，将`*list*`中的元素按顺序作为剩余参数传递。因此，`*procedure*`被调用的参数数量等于`*objs*`的数量加上`*list*`的元素数量。

当要传递给过程的一些或所有参数在列表中时，`apply`是有用的，因为它使程序员免于显式地解构列表。

(apply + '(4 5)) ![<graphic>](img/ch2_0.gif) 9

(apply min '(6 8 3 2 5)) ![<graphic>](img/ch2_0.gif) 2

(apply min  5 1 3 '(6 8 3 2 5)) ![<graphic>](img/ch2_0.gif) 1

(apply vector 'a 'b '(c d e)) ![<graphic>](img/ch2_0.gif) #(a b c d e)

(define first

(lambda (ls)

(apply (lambda (x . y) x) ls)))

(define rest

(lambda (ls)

(apply (lambda (x . y) y) ls)))

(first '(a b c d)) ![<graphic>](img/ch2_0.gif) a

(rest '(a b c d)) ![<graphic>](img/ch2_0.gif) (b c d)

(apply append

'(1 2 3)

'((a b) (c d e) (f))) ![<graphic>](img/ch2_0.gif) (1 2 3 a b c d e f)`

### 第 5.2 节。顺序执行

**语法：** `(begin *expr[1]* *expr[2]* ...)`

**返回：** 最后一个子表达式的值

**libraries:** `(rnrs base)`, `(rnrs)`

表达式 `*expr[1]* *expr[2]* ...` 从左到右顺序执行。`begin` 用于顺序执行赋值、输入/输出或其他会引起副作用的操作。

`(define x 3)

(begin

(set! x (+ x 1))

(+ x x)) ![<graphic>](img/ch2_0.gif) 8`

`begin` 表单可以包含零个或多个定义，代替表达式 `*expr[1]* *expr[2]* ...`，在这种情况下，它被视为定义，并且只能出现在定义有效的地方。

`(let ()

(begin (define x 3) (define y 4))

(+ x y)) ![<graphic>](img/ch2_0.gif) 7`

这种形式的 `begin` 主要用于必须扩展为多个定义的语法扩展中。（参见第 101 页。）

许多语法形式的主体，包括 `lambda`、`case-lambda`、`let`、`let*`、`letrec` 和 `letrec*`，以及 `cond`、`case` 和 `do` 的结果子句，被视为在隐式 `begin` 内部；即，构成主体或结果子句的表达式按顺序执行，最后一个表达式的值被返回。

`(define swap-pair!

(lambda (x)

(let ([temp (car x)])

(set-car! x (cdr x))

(set-cdr! x temp)

x)))

(swap-pair! (cons 'a 'b)) ![<graphic>](img/ch2_0.gif) (b . a)`

### 第 5.3 节 条件语句

**syntax**: `(if *test* *consequent* *alternative*)`

**syntax**: `(if *test* *consequent*)`

**returns:** 根据 `*test*` 的值返回 `*consequent*` 或 `*alternative*` 的值

**libraries:** `(rnrs base)`, `(rnrs)`

`*test*`、`*consequent*` 和 `*alternative*` 子表达式必须是表达式。如果 `*test*` 评估为真值（除了 `#f` 之外的任何值），则评估 `consequent` 并返回其值。否则，评估 `alternative` 并返回其值。对于第二种“单臂”形式，没有 `*alternative*`，如果 `*test*` 评估为假，则结果是未指定的。

`(let ([ls '(a b c)])

(if (null? ls)

'()

(cdr ls))) ![<graphic>](img/ch2_0.gif) (b c)

(let ([ls '()])

(if (null? ls)

'()

(cdr ls))) ![<graphic>](img/ch2_0.gif) ()

(let ([abs

(lambda (x)

(if (< x 0)

(- 0 x)

x))])

(abs -4)) ![<graphic>](img/ch2_0.gif) 4

(let ([x -4])

(if (< x 0)

(list 'minus (- 0 x))

(list 'plus 4))) ![<graphic>](img/ch2_0.gif) (minus 4)`

**procedure**: `(not *obj*)`

**returns:** 如果 `*obj*` 为假，则返回 `#t`，否则返回 `#f`

**libraries:** `(rnrs base)`, `(rnrs)`

`not` 等同于 `(lambda (x) (if x #f #t))`。

`(not #f) ![<graphic>](img/ch2_0.gif) #t

(not #t) ![<graphic>](img/ch2_0.gif) #f

(not '()) ![<graphic>](img/ch2_0.gif) #f

(not (< 4 5)) ![<graphic>](img/ch2_0.gif) #f`

**syntax**: `(and *expr* ...)`

**returns:** 见下文

**libraries:** `(rnrs base)`, `(rnrs)`

如果没有子表达式，则 `and` 形式评估为 `#t`。否则，`and` 从左到右按顺序评估每个子表达式，直到只剩下一个子表达式或一个子表达式返回 `#f`。如果只剩下一个子表达式，则对其进行评估并返回其值。如果一个子表达式返回 `#f`，则 `and` 返回 `#f` 而不评估剩余的子表达式。`and` 的语法定义见第 62 页。

`(let ([x 3])

(和 (> x 2) (< x 4))) ![<graphic>](img/ch2_0.gif) #t

(let ([x 5])

(和 (> x 2) (< x 4))) ![<graphic>](img/ch2_0.gif) #f

(和 #f '(a b) '(c d)) ![<graphic>](img/ch2_0.gif) #f

(和 '(a b) '(c d) '(e f)) ![<graphic>](img/ch2_0.gif) (e f)`

**语法**: `(or *expr* ...)`

**返回:** 见下文

**库:** `(rnrs base)`，`(rnrs)`

如果没有子表达式，则 `or` 形式评估为 `#f`。否则，`or` 从左到右按顺序评估每个子表达式，直到只剩下一个子表达式或一个子表达式返回一个不是 `#f` 的值。如果只剩下一个子表达式，则对其进行评估并返回其值。如果一个子表达式返回一个不是 `#f` 的值，则 `or` 返回该值而不评估剩余的子表达式。`or` 的语法定义见第 63 页。

`(let ([x 3])

(或者 (< x 2) (> x 4))) ![<graphic>](img/ch2_0.gif) #f

(let ([x 5])

(或者 (< x 2) (> x 4))) ![<graphic>](img/ch2_0.gif) #t

(或者 #f '(a b) '(c d)) ![<graphic>](img/ch2_0.gif) (a b)`

**语法**: `(cond *clause[1]* *clause[2]* ...)`

**返回:** 见下文

**库:** `(rnrs base)`，`(rnrs)`

每个 `*clause*` 除了最后一个必须采用以下形式之一。

`(*test*)

(*test* *expr[1]* *expr[2]* ...)

(*test* => *expr*)`

最后一个子句可以采用上述任何形式之一，或者可以是形式为 "`else` 子句" 的形式

`(else *expr[1]* *expr[2]* ...)`

每个 `*test*` 按顺序评估，直到有一个评估为真值或者所有测试都已经评估。如果第一个子句的 `*test*` 评估为真值，则返回 `*test*` 的值。

如果第一个子句的 `*test*` 评估为真值，则给定上述第二种形式，将按顺序评估表达式 `*expr[1]* *expr[2]*...`，并返回最后一个表达式的值。

如果第一个子句的 `*test*` 评估为真值，则给定上述第三种形式，将评估表达式 `*expr*`。该值应为一个接受一个参数的过程，该参数应用于 `*test*` 的值。此应用的值将被返回。

如果没有测试评估为真值且存在 `else` 子句，则按顺序评估 `else` 子句的表达式 `*expr[1]* *expr[2]* ...`，并返回最后一个表达式的值。

如果没有测试评估为真值且没有 `else` 子句，则值或值未指定。

有关 `cond` 的语法定义，请参见第 305 页。

`(let ([x 0])

(条件

[(< x 0) (列表 'minus (绝对值 x))]

[(> x 0) (列表 'plus x)]

[else (列表 'zero x)])) ![<graphic>](img/ch2_0.gif) (零 0)

(定义 select

(lambda (x)

(条件

[(不是 (符号？ x))]

[(assq x '((a . 1) (b . 2) (c . 3))) => cdr]

[else 0])))

(选择 3) ![<graphic>](img/ch2_0.gif) #t

(选择 'b) ![<graphic>](img/ch2_0.gif) 2

(选择 'e) ![<graphic>](img/ch2_0.gif) 0`

**语法**：`else`

**语法**：`=>`

**库：**`(rnrs base)`，`(rnrs exceptions)`，`(rnrs)`

这些标识符是`cond`的辅助关键字。它们也作为`guard`和`case`的辅助关键字。在除了它们被识别为辅助关键字的上下文之外引用这些标识符是语法违例。

**语法**：`(when *test-expr* *expr[1]* *expr[2]* ...)`

**语法**：`(unless *test-expr* *expr[1]* *expr[2]* ...)`

**返回：**见下文

**库：**`(rnrs control)`，`(rnrs)`

对于`when`，如果`*test-expr*`评估为真值，则按顺序评估表达式`*expr[1]* *expr[2]* ...`，并返回最后一个表达式的值。如果`*test-expr*`评估为假，则不评估其他表达式，并且`when`的值或值是未指定的。

对于`unless`，如果`*test-expr*`评估为假，则按顺序评估表达式`*expr[1]* *expr[2]* ...`，并返回最后一个表达式的值。如果`*test-expr*`评估为真值，则不评估其他表达式，并且`unless`的值或值是未指定的。

`when`或`unless`表达式通常比相应的"单臂" `if`表达式更清晰。

`(让 ([x -4] [sign 'plus])

(当 (< x 0)

(设定！ x (- 0 x))

(设定！ sign 'minus))

(列表 符号 x)) ![<graphic>](img/ch2_0.gif) (减 4)

(定义 check-pair

(lambda (x)

(unless (pair? x)

(语法违例 'check-pair "无效的参数" x))

x))

(check-pair '(a b c)) ![<graphic>](img/ch2_0.gif) (a b c)`

`when`可以定义如下：

`(define-syntax when

(语法规则 ()

[(_ e0 e1 e2 ...)

(如果 e0 (开始 e1 e2 ...))]))`

`unless`可以定义如下：

`(define-syntax unless

(语法规则 ()

[(_ e0 e1 e2 ...)

(如果 (不是 e0) (开始 e1 e2 ...))]))`

或者用`when`表示如下：

`(define-syntax unless

(语法规则 ()

[(_ e0 e1 e2 ...)

(当 (不是 e0) e1 e2 ...)]))`

**语法**：`(case *expr[0]* *clause[1]* *clause[2]* ...)`

**返回：**见下文

**库：**`(rnrs base)`，`(rnrs)`

每个子句除了最后一个必须采用以下形式

`((*key* ...) *expr[1]* *expr[2]* ...)`

每个`*key*`都是与其他键不同的数据。最后一个子句可以是上述形式，也可以是一个`else`子句的形式

`(else *expr[1]* *expr[2]* ...)`

`*expr[0]*`被评估，并且结果（使用`eqv?`）与每个子句的键按顺序进行比较。如果找到包含匹配键的子句，则按顺序评估表达式`*expr[1]* *expr[2]* ...`，并返回最后一个表达式的值。

如果没有一个子句包含匹配的键，且存在一个 `else` 子句，则按顺序评估 `else` 子句的表达式 `*expr[1]* *expr[2]* ...`，并返回最后一个表达式的值。

如果没有一个子句包含匹配的键，且没有 `else` 子句存在，则值或值是未指定的。

请参见第 306 页，了解 `case` 的语法定义。

`(let ([x 4] [y 5])

(case (+ x y)

[(1 3 5 7 9) 'odd]

[(0 2 4 6 8) 'even]

[else 'out-of-range])) ![<graphic>](img/ch2_0.gif) odd`

### 第 5.4 节。递归和迭代

**语法**: `(let *name* ((*var* *expr*) ...) *body[1]* *body[2]* ...)`

**返回:** 最终体表达式的值

**库:** `(rnrs base)`, `(rnrs)`

这种形式的 `let`，称为*命名* `let`，是一个通用的迭代和递归构造。它类似于更常见的 `let` 形式（参见第 4.4 节），在其中将变量 `*var* ...` 绑定到 `*expr* ...` 的值，这些值在体 `*body[1]* *body[2]* ...` 中被处理和评估，就像一个 `lambda` 体一样。此外，变量 `*name*` 在体内绑定到一个可以用于递归或迭代的过程，该过程的参数成为变量 `*var* ...` 的新值。

一个形式为 `let` 的命名表达式

`(let *name* ((*var*��*expr*) ...)

*body[1]* *body[2]* ...)`

可以用 `letrec` 重写如下。

`((letrec ((*name* (lambda (*var* ...) *body[1]* *body[2]* ...)))

*name*)

*expr* ...)`

可以在第 312 页找到实现此转换并处理未命名 `let` 的 `let` 的语法定义。

下面定义的 `divisors` 过程使用命名 `let` 来计算非负整数的非平凡除数。

`(define divisors

(lambda (n)

(let f ([i 2])

(条件

[(>= i n) '()]

[(integer? (/ n i)) (cons i (f (+ i 1)))]

[else (f (+ i 1))]))))

(divisors 5) ![<graphic>](img/ch2_0.gif) ()

(divisors 32) ![<graphic>](img/ch2_0.gif) (2 4 8 16)`

上面的版本在找到除数时是非尾递归的，在找不到除数时是尾递归的。下面的版本是完全尾递归的。它以相反的顺序构建列表，但如果需要，可以在退出时轻松纠正这一点，通过反转列表。

`(define divisors

(lambda (n)

(let f ([i 2] [ls '()])

(条件

[(>= i n) ls]

[(integer? (/ n i)) (f (+ i 1) (cons i ls))]

[else (f (+ i 1) ls)]))))`

**语法**: `(do ((*var* *init* *update*) ...) (*test* *result* ...) *expr* ...)`

**返回:** 最后一个 `*result*` 表达式的值

**库:** `(rnrs control)`, `(rnrs)`

`do` 允许以简洁的方式表达常见的受限迭代形式。变量 `*var* ...` 最初绑定到 `*init* ...` 的值，并在每次迭代中重新绑定到 `*update* ...` 的值。表达式 `*test*`、`*update* ...`、`*expr* ...` 和 `*result* ...` 都在为 `*var* ...` 建立的绑定范围内。

在每一步中，测试表达式 `*test*` 被评估。如果 `*test*` 的值为真，则迭代停止，表达式 `*result* ...` 按顺序被评估，并返回最后一个表达式的值。如果没有结果表达式，则 `do` 表达式的值是未指定的。

如果 `*test*` 的值为假，则表达式 `*expr* ...` 按顺序被评估，表达式 `*update* ...` 被评估，为 `*var* ...` 创建到 `*update* ...` 值的新绑定，并继续迭代。

表达式 `*expr* ...` 仅用于效果评估，通常完全省略。任何 `*update*` 表达式都可以省略，此时效果与 `*update*` 简单地是相应的 `*var*` 一样。

尽管大多数语言中的循环结构要求通过赋值来更新循环迭代器，`do` 要求通过重新绑定来更新循环迭代器 `*var* ...`。实际上，在 `do` 表达式的评估中不涉及任何副作用，除非它们由其子表达式显式执行。

查看页面 313 以获取 `do` 的语法定义。

下面的 `factorial` 和 `fibonacci` 的定义是第 3.2 节中给出的尾递归具名 `let` 版本的直接翻译。

`(define factorial

(lambda (n)

(do ([i n (- i 1)] [a 1 (* a i)])

((zero? i) a))))

(factorial 10) ![<graphic>](img/ch2_0.gif) 3628800

(define fibonacci

(lambda (n)

(if (= n 0)

0

(do ([i n (- i 1)] [a1 1 (+ a1 a2)] [a2 0 a1])

((= i 1) a1)))))

(fibonacci 6) ![<graphic>](img/ch2_0.gif) 8`

下面的 `divisors` 的定义类似于上面给出的具名 `let` 的尾递归定义 `divisors` 的描述。

`(define divisors

(lambda (n)

(do ([i 2 (+ i 1)]

[ls '()

(如果 (integer? (/ n i))

(cons i ls)

ls)])

((>= i n) ls))))`

下面的 `scale-vector!` 的定义，它通过一个常数 *k* 缩放向量 *v* 的每个元素，演示了一个非空的 `do` 体。

`(define scale-vector!

(lambda (v k)

(let ([n (vector-length v)])

(do ([i 0 (+ i 1)])

((= i n))

(vector-set! v i (* (vector-ref v i) k))))))

(define vec (vector 1 2 3 4 5))

(scale-vector! vec 2)

vec ![<graphic>](img/ch2_0.gif) #(2 4 6 8 10)`

### 第 5.5 节。映射和折叠

当程序必须对列表进行递归或迭代时，映射或折叠运算符通常更方便。这些运算符通过逐个应用过程到列表的元素来抽象出空检查和显式递归。一些映射运算符也适用于向量和字符串。

**procedure**: `(map *procedure* *list[1]* *list[2]* ...)`

**returns:** 结果列表

**libraries:** `(rnrs base)`, `(rnrs)`

`map` 将 `*procedure*` 应用于列表 `*list[1]* *list[2]* ...` 中对应的元素，并返回结果值的列表。列表 `*list[1]* *list[2]* ...` 必须具有相同长度。`*procedure*` 应接受与列表数量相同的参数，应返回单个值，并且不应改变 `*list*` 参数。

`(map abs '(1 -2 3 -4 5 -6)) ![<graphic>](img/ch2_0.gif) (1 2 3 4 5 6)

(map (lambda (x y) (* x y))

'(1 2 3 4)

'(8 7 6 5)) ![<graphic>](img/ch2_0.gif) (8 14 18 20)`

尽管应用本身的顺序没有指定，但输出列表中值的顺序与输入列表中相应值的顺序相同。

`map` 可能定义如下。

`(定义 map

(lambda (f ls . more)

(if (null? more)

(let map1 ([ls ls])

(if (null? ls)

'()

(cons (f (car ls))

(map1 (cdr ls)))))

(let map-more ([ls ls] [more more])

(if (null? ls)

'()

(cons

(apply f (car ls) (map car more))

(map-more (cdr ls) (map cdr more))))))))`

这个版本的 `map` 没有进行错误检查；假定 `f` 是一个过程，其他参数假定为相同长度的适当列表。这个定义的一个有趣特点是，`map` 使用自身来提取输入列表的 car 和 cdr；这是因为对于单列表情况的特殊处理。

**procedure**: `(for-each *procedure* *list[1]* *list[2]* ...)`

**返回:** 未指定

**libraries:** `(rnrs base)`, `(rnrs)`

`for-each` 类似于 `map`，但 `for-each` 不会创建并返回结果值的列表，并且 `for-each` 保���按顺序从左到右对元素执行应用。`*procedure*` 应接受与列表数量相同的参数，并且不应改变 `*list*` 参数。`for-each` 可以如下定义而无需错误检查。

`(定义 for-each

(lambda (f ls . more)

(do ([ls ls (cdr ls)] [more more (map cdr more)])

((null? ls))

(apply f (car ls) (map car more)))))

(let ([same-count 0])

(for-each

(lambda (x y)

(when (= x y)

(set! same-count (+ same-count 1))))

'(1 2 3 4 5 6)

'(2 3 3 4 7 6))

same-count) ![<graphic>](img/ch2_0.gif) 3`

**procedure**: `(存在 *procedure* *list[1]* *list[2]* ...)`

**返回:** 见下文

**libraries:** `(rnrs lists)`, `(rnrs)`

列表 `*list[1]* *list[2]* ...` 必须具有相同长度。`*procedure*` 应接受与列表数量相同的参数，并且不应改变 `*list*` 参数。如果列表为空，则 `exists` 返回 `#f`。否则，`exists` 依次对列表 `*list[1]* *list[2]* ...` 中对应的元素应用 `*procedure*`，直到每个列表仅剩一个元素或 `*procedure*` 返回真值 `*t*`。在前一种情况下，`exists` 尾调用 `*procedure*`，将其应用于每个列表的剩余元素。在后一种情况下，`exists` 返回 `*t*`。

`(存在 symbol? '(1.0 #\a "hi" '())) ![<graphic>](img/ch2_0.gif) #f

(存在 member

'(a b c)

'((c b) (b a) (a c))) ![<graphic>](img/ch2_0.gif) (b a)

(exists (lambda (x y z) (= (+ x y) z))

'(1 2 3 4)

'(1.2 2.3 3.4 4.5)

'(2.3 4.4 6.4 8.6)) ![<graphic>](img/ch2_0.gif) #t`

`exists`可以定义为（有些低效且没有错误检查）如下：

`(define exists

(lambda (f ls . more)

(and (not (null? ls))

(let exists ([x (car ls)] [ls (cdr ls)] [more more])

(if (null? ls)

(apply f x (map car more))

(or (apply f x (map car more))

(exists (car ls) (cdr ls) (map cdr more))))))))`

**procedure**：`(for-all *procedure* *list[1]* *list[2]* ...)`

**返回：**见下文

**库：**`(rnrs lists)`，`(rnrs)`

列表`*list[1]* *list[2]* ...`必须具有相同的长度。`*procedure*`应接受与列表数量相同的参数，并且不应该改变`*list*`参数。如果列表为空，则`for-all`返回`#t`。否则，`for-all`将`*procedure*`应用于列表`*list[1]* *list[2]* ...`中对应的元素，直到每个列表仅剩下一个元素或`*procedure*`返回`#f`为止。在前一种情况下，`for-all`尾调用`*procedure*`，将其应用于每个列表的剩余元素。在后一种情况下，`for-all`返回`#f`。

`(for-all symbol? '(a b c d)) ![<graphic>](img/ch2_0.gif) #t

(for-all =

'(1 2 3 4)

'(1.0 2.0 3.0 4.0)) ![<graphic>](img/ch2_0.gif) #t

(for-all (lambda (x y z) (= (+ x y) z))

'(1 2 3 4)

'(1.2 2.3 3.4 4.5)

'(2.2 4.3 6.5 8.5)) ![<graphic>](img/ch2_0.gif) #f`

`for-all`可以定义为（有些低效且没有错误检查）如下：

`(define for-all

(lambda (f ls . more)

(or (null? ls)

(let for-all ([x (car ls)] [ls (cdr ls)] [more more])

(if (null? ls)

(apply f x (map car more))

(and (apply f x (map car more))

(for-all (car ls) (cdr ls) (map cdr more))))))))`

**procedure**：`(fold-left *procedure* *obj* *list[1]* *list[2]* ...)`

**返回：**见下文

**库：**`(rnrs lists)`，`(rnrs)`

所有`*list*`参数应具有相同的长度。`*procedure*`应接受比`*list*`参数数量多一个的参数，并返回单个值。它不应该改变`*list*`参数。

`fold-left`如果`*list*`参数为空，则返回`*obj*`。如果它们不为��，则`fold-left`将`*procedure*`应用于`*obj*`和`*list[1]* *list[2]* ...`的 car，然后用`*procedure*`返回的值替换`*obj*`，用每个`*list*`的 cdr 替换`*list*`进行递归。

`(fold-left cons '() '(1 2 3 4)) ![<graphic>](img/ch2_0.gif) ((((() . 1) . 2) . 3) . 4)

(fold-left

(lambda (a x) (+ a (* x x)))

0 '(1 2 3 4 5)) ![<graphic>](img/ch2_0.gif) 55

(fold-left

(lambda (a . args) (append args a))

'(question)

'(that not to)

'(is to be)

'(the be: or)) ![<graphic>](img/ch2_0.gif) (to be or not to be: that is the question)`

**procedure**：`(fold-right *procedure* *obj* *list[1]* *list[2]* ...)`

**返回：**见下文

**库：**`(rnrs lists)`，`(rnrs)`

所有 `*list*` 参数的长度应相同。 `*procedure*` 应接受比 `*list*` 参数数量多一个参数，并返回单个值。 它不应更改 `*list*` 参数。

`fold-right` 如果 `*list*` 参数为空，则返回 `*obj*`。 如果它们不为空，则 `fold-right` 递归地用每个 `*list*` 的 cdr 替换 `*list*`���然后将 `*procedure*` 应用于 `*list[1]* *list[2]* ...` 的 car 和递归返回的结果。

`(fold-right cons '() '(1 2 3 4)) ![<graphic>](img/ch2_0.gif) (1 2 3 4)

(fold-right

(lambda (x a) (+ a (* x x)))

0 '(1 2 3 4 5)) ![<graphic>](img/ch2_0.gif) 55

(fold-right

(lambda (x y a) (cons* x y a))   ![<graphic>](img/ch2_0.gif) 分别是如此甜蜜的离别

'((with apologies))              ![](img/ch3_ghostRightarrow.gif)  明天见

'(parting such sorrow go ya)     ![](img/ch3_ghostRightarrow.gif)  (with apologies))

'(is sweet gotta see tomorrow))`

**procedure**: `(vector-map *procedure* *vector[1]* *vector[1]* ...)`

**返回:** 结果的向量

**库:** `(rnrs base)`, `(rnrs)`

`vector-map` 将 `*procedure*` 应用于 `*vector[1]* *vector[2]* ...` 的对应元素，并返回一个包含结果值的向量。 向量 `*vector[1]* *vector[2]* ...` 必须具有相同的长度，而 `*procedure*` 应接受与向量数量相同的参数，并返回单个值。

`(vector-map abs '#(1 -2 3 -4 5 -6)) ![<graphic>](img/ch2_0.gif) #(1 2 3 4 5 6)

(vector-map (lambda (x y) (* x y))

'#(1 2 3 4)

'#(8 7 6 5)) ![<graphic>](img/ch2_0.gif) #(8 14 18 20)`

尽管应用本身的顺序未指定，但输出向量中的值的顺序与输入向量中相应值的顺序相同。

**procedure**: `(vector-for-each *procedure* *vector[1]* *vector[2]* ...)`

**返回:** 未指定

**库:** `(rnrs base)`, `(rnrs)`

`vector-for-each` 类似于 `vector-map`，但 `vector-for-each` 不会创建并返回包含结果值的向量，并且 `vector-for-each` 保证按顺序从左到右对元素执行应用。

`(let ([same-count 0])

(vector-for-each

(lambda (x y)

(当 (= x y)

(set! same-count (+ same-count 1))))

'#(1 2 3 4 5 6)

'#(2 3 3 4 7 6))

same-count) ![<graphic>](img/ch2_0.gif) 3`

**procedure**: `(string-for-each *procedure* *string[1]* *string[2]* ...)`

**返回:** 未指定

**库:** `(rnrs base)`, `(rnrs)`

`string-for-each` 类似于 `for-each` 和 `vector-for-each`，但输入是字符串而不是列表或向量。

`(let ([ls '()])

(string-for-each

(lambda r (set! ls (cons r ls)))

"abcd"

"===="

"1234")

(map list->string (reverse ls))) ![<graphic>](img/ch2_0.gif) ("a=1" "b=2" "c=3" "d=4")`

### 第 5.6 节。 续延

Scheme 中的续延是代表计算中给定点后续部分的过程。可以使用`call-with-current-continuation`获得续延，可以缩写为`call/cc`。

**procedure**: `(call/cc *procedure*)`

**procedure**: `(call-with-current-continuation *procedure*)`

**returns:** 请参见下文

**libraries:** `(rnrs base)`, `(rnrs)`

这些过程是相同的。通常使用较短的名称是因为它需要更少的按键次数来输入。

`call/cc`获取其续延并将其传递给`*procedure*`，后者应接受一个参数。续延本身由一个过程表示。每次将此过程应用于零个或多个值时，它将这些值返回给`call/cc`应用的续延。也就是说，当调用续延过程时，它将其参数作为`call/cc`应用的值返回。

如果`*procedure*`在传递续延过程时正常返回，则`call/cc`返回的值是`*procedure*`返回的值。

续延允许实现非局部退出、回溯 [14,29]、协程 [16]和多任务 [10,32]。

下面的示例说明了使用续延从循环中进行非局部退出的用法。

`(define member

(lambda (x ls)

(call/cc

(lambda (break)

(do ([ls ls (cdr ls)])

((null? ls) #f)

(when (equal? x (car ls))

(break ls)))))))

(member 'd '(a b c)) ![<graphic>](img/ch2_0.gif) #f

(member 'b '(a b c)) ![<graphic>](img/ch2_0.gif) (b c)`

在第 3.3 和 12.11 节中提供了其他示例。

当前续延通常在内部表示为一堆过程激活记录的堆栈，并且获取续延涉及将堆栈封装在过程对象中。由于封装的堆栈具有无限范围，必须使用某种机制无限期地保留堆栈内容。这可以以惊人的轻松和效率完成，并且不会对不使用续延的程序产生影响 [17]。

**procedure**: `(dynamic-wind *in* *body* *out*)`

**returns:** values resulting from the application of `*body*`

**libraries:** `(rnrs base)`, `(rnrs)`

`dynamic-wind`提供了对续延调用的“保护”。它用于执行必须在控制进入或离开`*body*`时执行的任务，无论是正常执行还是通过续延应用。

三个参数`*in*`、`*body*`和`*out*`必须是过程，并且应该接受零个参数，即它们应该是`*thunks*`。在应用`*body*`之前，以及每次通过在`*body*`内创建的 continuation 应用`*body*`时，都会应用`*in*` thunk。在从`*body*`正常退出以及每次通过在`*body*`外创建的 continuation 退出`*body*`时，都会应用`*out*` thunk。

因此，可以保证至少调用一次`*in*`。此外，如果`*body*`返回，至少会调用一次`*out*`。

以下示例演示了使用`dynamic-wind`确保在处理后关闭输入端口，无论处理是否正常完成。

`(let ([p (open-input-file "input-file")])

(dynamic-wind

(lambda () #f)

(lambda () (process p))

(lambda () (close-port p))))

Common Lisp 提供了类似的机制（`unwind-protect`）来保护非局部退出。这通常足够了。然而，`unwind-protect`只提供了等价于`*out*`的功能，因为 Common Lisp 不支持完全通用的 continuations。以下是如何使用`dynamic-wind`指定`unwind-protect`的方式。

`(define-syntax unwind-protect

(syntax-rules ()

[(_ body cleanup ...)

(dynamic-wind

(lambda () #f)

(lambda () body)

(lambda () cleanup ...))]))

((call/cc

(let ([x 'a])

(lambda (k)

(unwind-protect

(k (lambda () x))

(set! x 'b)))))) ![<graphic>](img/ch2_0.gif) b`

一些 Scheme 实现支持一种受控的赋值形式，称为*fluid binding*，其中一个变量在给定计算期间采用临时值，并在计算完成后恢复到旧值。以下所定义的语法形式`fluid-let`使用`dynamic-wind`允许将单个变量`x`的 fluid binding 到表达式`e`的值在`b1 b2 ...`体内。

`(define-syntax fluid-let

(syntax-rules ()

[(_ ((x e)) b1 b2 ...)

(let ([y e])

(let ([swap (lambda () (let ([t x]) (set! x y) (set! y t)))])

(dynamic-wind swap (lambda () b1 b2 ...) swap)))]))`

支持`fluid-let`的实现通常会扩展它，允许无限数量的`(x e)`对，就像`let`一样。

如果在`fluid-let`的主体中没有调用 continuations，那么行为就像变量在进入时简单地被赋予新值，返回时被赋予旧值一样。

`(let ([x 3])

(+ (fluid-let ([x 5])

x)

x)) ![<graphic>](img/ch2_0.gif) 8`

如果在`fluid-let`之外创建的 continuation 被调用，fluid-bound 变量也会恢复到旧值。

`(let ([x 'a])

(let ([f (lambda () x)])

(cons (call/cc

(lambda (k)

(fluid-let ([x 'b])

(k (f)))))

(f)))) ![<graphic>](img/ch2_0.gif) (b . a)`

如果控制已经离开了`fluid-let`的主体，无论是正常离开还是通过调用 continuation，如果控制通过调用 continuation 重新进入主体，fluid-bound 变量的临时值将被恢复。此外，对临时值的任何更改都将得到维护和在重新进入时反映出来。

`(define reenter #f)

(define x 0)

(fluid-let ([x 1])

(call/cc (lambda (k) (set! reenter k)))

(set! x (+ x 1))

x) ![<graphic>](img/ch2_0.gif) 2

x ![<graphic>](img/ch2_0.gif) 0

(reenter '*) ![<graphic>](img/ch2_0.gif) 3

(reenter '*) ![<graphic>](img/ch2_0.gif) 4

x ![<graphic>](img/ch2_0.gif) 0`

展示了`dynamic-wind`如果不是内建的情况下可能如何实现的库。除了定义`dynamic-wind`之外，代码还定义了一个版本的`call/cc`，该版本对支持`dynamic-wind`做出了贡献。

`(library (dynamic-wind)

(export dynamic-wind call/cc

(rename (call/cc call-with-current-continuation)))

(import (rename (except (rnrs) dynamic-wind) (call/cc rnrs:call/cc)))

(define winders '())

(define common-tail

(lambda (x y)

(let ([lx (length x)] [ly (length y)])

(do ([x (if (> lx ly) (list-tail x (- lx ly)) x) (cdr x)]

[y (if (> ly lx) (list-tail y (- ly lx)) y) (cdr y)])

((eq? x y) x)))))

(define do-wind

(lambda (new)

(let ([tail (common-tail new winders)])

(let f ([ls winders])

(if (not (eq? ls tail))

(begin

(set! winders (cdr ls))

((cdar ls))

(f (cdr ls)))))

(let f ([ls new])

(if (not (eq? ls tail))

(begin

(f (cdr ls))

((caar ls))

(set! winders ls)))))))`

`  (define call/cc

(lambda (f)

(rnrs:call/cc

(lambda (k)

(f (let ([save winders])

(lambda (x)

(unless (eq? save winders) (do-wind save))

(k x))))))))

(define dynamic-wind

(lambda (in body out)

(in)

(set! winders (cons (cons in out) winders))

(let-values ([ans* (body)])

(set! winders (cdr winders))

(out)

(apply values ans*)))))`

`dynamic-wind`和`call/cc`共同管理着一个*winders*列表。winder 是通过调用`dynamic-wind`建立的一个包含*in*和*out* thunk 的对。每当调用`dynamic-wind`时，将调用*in* thunk，一个新的 winder（包含*in*和*out* thunk）将被放置在 winder 列表上，将调用*body* thunk，然后将 winder 从 winder 列表中移除，并调用*out* thunk。这种顺序确保了 winder 只有在通过*in*传递控制而尚未进入*out*时才存在于 winder 列表中。每当获得一个 continuation 时，winders 列表将被保存，每当调用 continuation 时，保存的 winders 列表将被恢复。在恢复期间，当前 winders 列表上的每个 winder 的*out* thunk 将被调用，而不在当前 winders 列表上但在保存的 winders 列表上的每个 winder 的*in* thunk 将被调用。winders 列表会进行增量更新，以确保只有当控制通过其*in* thunk 并且尚未进入其*out* thunk 时，winder 才存在于当前 winders 列表中。

在 `call/cc` 中执行的测试 `(not (eq? save winders))` 不是严格必要的，但在保存的 winders 列表与当前 winders 列表相同时，使调用 continuation 更少成本。

### 第 5.7 节。延迟评估

语法形式 `delay` 和过程 `force` 可以结合使用以实现*惰性评估*。受惰性评估影响的表达式直到需要其值时才被评估，并且一旦评估，就不会重新评估。

**语法**：`(delay *expr*)`

**返回：** 一个 promise

**过程**：`(force *promise*)`

**返回：** 强制 `*promise*` 的结果

**库：** `(rnrs r5rs)`

通过 `delay` 创建的 promise 第一次被 *强制*（使用 `force`）时，它评估 `*expr*`，"记住"结果值。此后，每次强制 promise 时，它返回记住的值，而不是重新评估 `*expr*`。

`delay` 和 `force` 通常仅在没有副作用的情况下使用，例如赋值，以便评估顺序不重要。

使用 `delay` 和 `force` 的好处在于，如果延迟到绝对需要时，可以完全避免一些计算。延迟评估可用于构建概念上无限的列表，或*流*。下面的示例显示了如何使用 `delay` 和 `force` 构建流抽象。流是一个 promise，当强制时返回一个 cdr 是流的对。

`(定义 stream-car

(lambda (s)

(car (force s))))

(定义 stream-cdr

(lambda (s)

(cdr (force s))))

(定义 counters

(让 next ([n 1])

(delay (cons n (next (+ n 1))))))

(stream-car counters) ![<graphic>](img/ch2_0.gif) 1

(stream-car (stream-cdr counters)) ![<graphic>](img/ch2_0.gif) 2

(定义 stream-add

(lambda (s1 s2)

(延迟 (cons

(+ (stream-car s1) (stream-car s2))

(stream-add (stream-cdr s1) (stream-cdr s2))))))

(定义 even-counters

(stream-add counters counters))

(stream-car even-counters) ![<graphic>](img/ch2_0.gif) 2

(stream-car (stream-cdr even-counters)) ![<graphic>](img/ch2_0.gif) 4`

`delay` 可以定义为

`(定义语法 delay

(syntax-rules ()

[(_ expr) (make-promise (lambda () expr))]))`

其中 `make-promise` 可能定义如下。

`(定义 make-promise

(lambda (p)

(让 ([val #f] [set? #f])

(lambda ()

(除非 set?

(让 ([x (p)])

(除非 set?

(set! val x)

(set! set? #t))))

val))))`

使用这种 `delay` 的定义，`force` 简单地调用 promise 来强制评估或检索保存的值。

`(定义 force

(lambda (promise)

(promise)))`

`make-promise` 中对变量 `set?` 的第二次测试是必要的，以防由于应用 `*p*` 的结果而递归强制 promise。由于 promise 必须始终返回相同的值，因此返回完成第一次应用 `*p*` 的结果。

`delay` 和 `force` 是否处理多个返回值是未指定的；上面给出的实现不处理，但以下版本使用 `call-with-values` 和 `apply` 来处理。

`(定义 make-promise

(lambda (p)

(让 ([vals #f] [set? #f])

(lambda ()

(除非 set?

(call-with-values p

(lambda x

(除非 set?

(set! vals x)

(set! set? #t)))))

(apply values vals)))))

(定义 p (delay (values 1 2 3)))

(force p) ![<graphic>](img/ch2_0.gif) 1

![](img/ch3_ghostRightarrow.gif) 2

![](img/ch3_ghostRightarrow.gif) 3

(call-with-values (lambda () (force p)) +) ![<graphic>](img/ch2_0.gif) 6`

两种实现都不太正确，因为如果`force`的参数不是一个 promise，它必须引发一个条件类型为`&assertion`的异常。由于无法区分由`make-promise`创建的过程和其他过程，`force`无法可靠地执行此操作。下面对`make-promise`和`force`的重新实现将 promise 表示为类型为`promise`的记录，以允许`force`进行所需的检查。

`(define-record-type promise

(字段 (不可变 p) (可变 vals) (可变 set?))

(协议 (lambda (new) (lambda (p) (new p #f #f)))))

(定义 force

(lambda (promise)

(除非 (promise? promise)

(assertion-violation 'promise "invalid argument" promise))

(除非 (promise-set? promise)

(call-with-values (promise-p promise)

(lambda x

(除非 (promise-set? promise)

(promise-vals-set! promise x)

(promise-set?-set! promise #t)))))

(apply values (promise-vals promise))))`

### 第 5.8 节。多值

虽然所有 Scheme 原语和大多数用户定义的过程都返回一个值，但某些编程问题最好通过返回零个值、多个值甚至可变数量的值来解决。例如，将值列表分成两个子���表的过程需要返回两个值。虽然生产多个值的程序员可以将它们打包成数据结构，消费者可以提取它们，但通常更干净的方法是使用内置的多值接口。该接口由两个过程组成：`values`和`call-with-values`。前者产生多个值，后者将产生多值的过程与消费它们的过程链接起来。

**过程**: `(values *obj* ...)`

**返回:** `*obj* ...`

**库:** `(rnrs base)`, `(rnrs)`

过程`values`接受任意数量的参数，并简单地将这些参数传递（返回）给其续体。

`(values) ![<graphic>](img/ch2_0.gif)

(values 1) ![<graphic>](img/ch2_0.gif) 1

(values 1 2 3) ![<graphic>](img/ch2_0.gif) 1

![](img/ch3_ghostRightarrow.gif) 2

![](img/ch3_ghostRightarrow.gif) 3

(定义 head&tail

(lambda (ls)

(values (car ls) (cdr ls))))

(head&tail '(a b c)) ![<graphic>](img/ch2_0.gif) a

![](img/ch3_ghostRightarrow.gif) (b c)`

**过程**: `(call-with-values *producer* *consumer*)`

**返回:** 请参见下文

**库:** `(rnrs base)`, `(rnrs)`

`*producer*`和`*consumer*`必须是过程。`call-with-values`将`*consumer*`应用于调用`*producer*`而不带参数返回的值。

`(call-with-values

(lambda () (values 'bond 'james))

(lambda (x y) (cons y x))) ![<graphic>](img/ch2_0.gif) (james . bond)

(call-with-values values list) ![<graphic>](img/ch2_0.gif) '()`

在第二个例子中，`values`本身充当生产者。它不接收任何参数，因此不返回任何值。因此，`list`被应用于没有参数，因此返回空列表。

下面定义的`dxdy`过程计算由`(*x* . *y*)`对表示的一对点的坐标的`*x*`和`*y*`坐标的变化。

`(define dxdy

(lambda (p1 p2)

(values (- (car p2) (car p1))

(- (cdr p2) (cdr p1)))))

(dxdy '(0 . 0) '(0 . 5)) ![<graphic>](img/ch2_0.gif) 0

![](img/ch3_ghostRightarrow.gif) 5`

`dxdy`可以用于计算由两个端点表示的线段的长度和斜率。

`(define segment-length

(lambda (p1 p2)

(call-with-values

(lambda () (dxdy p1 p2))

(lambda (dx dy) (sqrt (+ (* dx dx) (* dy dy)))))))

(define segment-slope

(lambda (p1 p2)

(call-with-values

(lambda () (dxdy p1 p2))

(lambda (dx dy) (/ dy dx)))))

(segment-length '(1 . 4) '(4 . 8)) ![<graphic>](img/ch2_0.gif) 5

(segment-slope '(1 . 4) '(4 . 8)) ![<graphic>](img/ch2_0.gif) 4/3`

当然，我们可以将这些组合成一个返回两个值的过程。

`(define describe-segment

(lambda (p1 p2)

(call-with-values

(lambda () (dxdy p1 p2))

(lambda (dx dy)

(values

(sqrt (+ (* dx dx) (* dy dy)))

(/ dy dx))))))

(describe-segment '(1 . 4) '(4 . 8)) ![<graphic>](img/ch2_0.gif) 5

![<graphic>](img/ch2_0.gif) 4/3`

下面的示例使用多个值将列表非破坏性地分成两个交替元素的子列表。

`(define split

(lambda (ls)

(if (or (null? ls) (null? (cdr ls)))

(values ls '())

(call-with-values

(lambda () (split (cddr ls)))

(lambda (odds evens)

(values (cons (car ls) odds)

(cons (cadr ls) evens)))))))

(split '(a b c d e f)) ![<graphic>](img/ch2_0.gif) (a c e)

![](img/ch3_ghostRightarrow.gif) (b d f)`

在递归的每个级别，`split`过程返回两个值：参数列表中奇数元素的列表和偶数元素的列表。

对`values`的调用的继续不一定是由对`call-with-values`的调用建立的，也不一定只有`values`用于返回到由`call-with-values`建立的继续。特别地，`(values *e*)`和`*e*`是等价的表达式。例如：

`(+ (values 2) 4) ![<graphic>](img/ch2_0.gif) 6

(if (values #t) 1 2) ![<graphic>](img/ch2_0.gif) 1

(call-with-values

(lambda () 4)

(lambda (x) x)) ![<graphic>](img/ch2_0.gif) 4`

同样，`values`可以用于将任意数量的值传递给忽略这些值的继续，如下所示。

`(begin (values 1 2 3) 4) ![<graphic>](img/ch2_0.gif) 4`

因为继续可能接受零个或多个值，通过`call/cc`获得的继续可能接受零个或多个参数。

`(call-with-values

(lambda ()

(call/cc (lambda (k) (k 2 3))))

(lambda (x y) (list x y))) ![<graphic>](img/ch2_0.gif) (2 3)`

当一个期望正好一个值的延续接收到零个值或多个值时，行为是未指定的。例如，以下每个表达式的行为都是未指定的。一些实现会引发异常，而其他实现会在沉默中抑制额外的值或为丢失的值提供默认值。

`(if (values 1 2) 'x 'y)`

`(+ (values) 5)`

希望在特定上下文中强制忽略额外值的程序可以通过显式调用`call-with-values`轻松实现。可以定义一个称为`first`的语法形式来抽象出当只需要一个值时丢弃多个值。

`(define-syntax first`

`(syntax-rules ()`

`[(_ expr)`

`(call-with-values`

`(lambda () expr)`

`(lambda (x . y) x))]))`

`(if (first (values #t #f)) 'a 'b) ![<graphic>](img/ch2_0.gif) a`

由于实现必须在过程不接受传递给它的参数数量时引发带有条件类型`&assertion`的异常，因此以下每个都会引发异常。

`(call-with-values`

`(lambda () (values 2 3 4))`

`(lambda (x y) x))`

`(call-with-values`

`(lambda () (call/cc (lambda (k) (k 0))))`

`(lambda (x y) x))`

由于`*producer*`通常是一个`lambda`表达式，因此通常可以使用语法扩展来抑制 lambda 表达式以提高可读性。

`(define-syntax with-values`

`(syntax-rules ()`

`[(_ expr consumer)`

`(call-with-values (lambda () expr) consumer)]))`

`(with-values (values 1 2) list) ![<graphic>](img/ch2_0.gif) (1 2)`

`(with-values (split '(1 2 3 4))

`(lambda (odds evens)`

`evens)) ![<graphic>](img/ch2_0.gif) (2 4)`

如果`*consumer*`也是一个`lambda`表达式，那么第 4.5 节描述的`let`和`let*`的多值变体通常更加方便。

`(let-values ([(odds evens) (split '(1 2 3 4))])`

`evens) ![<graphic>](img/ch2_0.gif) (2 4)`

`(let-values ([ls (values 'a 'b 'c)])`

`ls) ![<graphic>](img/ch2_0.gif) (a b c)`

许多标准的语法形式和过程传递多个值。其中大多数是“自动”的，意味着实现不需要特别处理就可以使这种情况发生。`let`的通常展开成直接的`lambda`调用会自动传播`let`体产生的多个值。其他运算符必须特别编码以传递多个值。例如，`call-with-port`过程（第 7.6 页）调用其过程参数，然后在返回过程的值之前关闭端口参数，因此它必须临时保存值。这可以通过`let-values`、`apply`和`values`轻松实现：

`(define call-with-port`

`(lambda (port proc)`

`(let-values ([val* (proc port)])`

`(close-port port)`

`(apply values val*))))`

如果当返回单个值时看起来太过头疼，代码可以使用`call-with-values`和`case-lambda`来更有效地处理单值情况：

`(define call-with-port`

`(lambda (port proc)`

`(call-with-values (lambda () (proc port))`

(case-lambda

[(val) (close-port port) val]

[val* (close-port port) (apply values val*)]))))`

下面库中 `values` 和 `call-with-values` 的定义（以及与之相关的 `call/cc` 的重新定义）演示了如果不是已经内置的，多返回值接口可以在 Scheme 中实现。然而，不能对将多个值返回给单值上下文（例如 `if` 表达式的测试部分）进行任何错误检查。

`(library (mrvs)

(export call-with-values values call/cc

(rename (call/cc call-with-current-continuation)))

(import

(rename

(except (rnrs) values call-with-values)

(call/cc rnrs:call/cc)))

(define magic (cons 'multiple 'values))

(define magic?

(lambda (x)

(and (pair? x) (eq? (car x) magic))))`

`  (define call/cc

(lambda (p)

(rnrs:call/cc

(lambda (k)

(p (lambda args

(k (apply values args))))))))

(define values

(lambda args

(if (and (not (null? args)) (null? (cdr args)))

(car args)

(cons magic args))))

(define call-with-values

(lambda (producer consumer)

(let ([x (producer)])

(if (magic? x)

(apply consumer (cdr x))

(consumer x))))))`

可以更有效地实现多值 [2]，但此代码用于说明操作符的含义，并且可以用于在不支持它们的旧的、非标准实现中提供多个值。

### 第 5.9\. 评估

Scheme 的 `eval` 过程允许程序员编写构造和评估其他程序的程序。这种运行时*元编程*的能力不应该被滥用，但在需要时非常方便。

**procedure**: `(eval *obj* *environment*)`

**返回：** `*obj*` 在 `*environment*` 中表示的 Scheme 表达式的值

**libraries:** `(rnrs eval)`

如果 `*obj*` 不表示语法上有效的表达式，则 `eval` 引发带有条件类型 `&syntax` 的异常。由 `environment`、`scheme-report-environment` 和 `null-environment` 返回的环境是不可变的。因此，如果表达式中出现对环境中的任何变量的赋值，则 `eval` 还将引发带有条件类型 `&syntax` 的异常。

`(define cons 'not-cons)

(eval '(let ([x 3]) (cons x 4)) (environment '(rnrs))) ![<graphic>](img/ch2_0.gif) (3 . 4)

(define lambda 'not-lambda)

(eval '(lambda (x) x) (environment '(rnrs))) ![<graphic>](img/ch2_0.gif) #<procedure>

(eval '(cons 3 4) (environment)) ![<graphic>](img/ch2_0.gif) *exception*`

**procedure**: `(environment *import-spec* ...)`

**返回：** 一个环境

**libraries:** `(rnrs eval)`

`environment` 返回一个由给定导入说明符的组合绑定形成的环境。每个 `*import-spec*` 必须是一个表示有效导入说明符的 S 表达式（参见第 10 章）。

`(define env (environment '(rnrs) '(prefix (rnrs lists) $)))

(eval '($cons* 3 4 (* 5 8)) env) ![<graphic>](img/ch2_0.gif) (3 4 . 40)`

**procedure**: `(null-environment *version*)`

**procedure**: `(scheme-report-environment *version*)`

**returns:** 一个 R5RS 兼容环境

**libraries:** `(rnrs r5rs)`

`*version*` 必须是精确的整数 `5`。

`null-environment` 返回一个包含由 Scheme 修订⁵报告定义含义的关键字绑定的环境，以及辅助关键字 `else`、`=>`、`...` 和 `_` 的绑定。

`scheme-report-environment` 返回一个包含与由 `null-environment` 返回的环境相同的关键字绑定的环境，以及由 Scheme 修订⁵报告定义含义的变量的绑定，除了修订⁶报告未定义的变量：`load`、`interaction-environment`、`transcript-on`、`transcript-off` 和 `char-ready?`。

这些过程返回的环境中每个标识符的绑定都是对应的修订⁶报告库的绑定，因此即使未使用预期的标识符绑定，也不会提供完全的向后兼容性。

* * *

R. Kent Dybvig / <it>《Scheme 编程语言，第四版》</it>

版权所有 © 2009 [麻省理工学院出版社](http://mitpress.mit.edu/catalog/item/default.asp?ttype=2&tid=11984)。经许可电子重印。

插图 © 2009 [Jean-Pierre Hébert](http://hebert.kitp.ucsb.edu/)

ISBN 978-0-262-51298-5 / LOC QA76.73.S34D93

[购买此书](http://mitpress.mit.edu/catalog/item/default.asp?ttype=2&tid=11984) / 关于此书

[`www.scheme.com`](http://www.scheme.com/)
