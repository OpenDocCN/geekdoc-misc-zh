# 第四章。过程和变量绑定

过程和变量绑定是 Scheme 程序的基本构建块。本章描述了一小组主要用于创建过程和操作变量绑定的语法形式。它从 Scheme 程序的两个最基本的构建块开始：变量引用和`lambda`表达式，并继续描述变量绑定和赋值形式，如`define`、`letrec`、`let-values`和`set!`。

其他各种绑定或赋值变量的形式，其绑定或赋值不是主要目的（如命名的`let`），可在第五章中找到。

### 第 4.1 节。变量引用

**语法**：`*variable*`

**返回：** `*variable*`的值

程序中作为表达式出现的任何标识符，如果存在可见的变量绑定，则是一个变量，例如，该标识符出现在由`define`、`lambda`、`let`或其他变量绑定构造创建的绑定的范围内。

`list ![<graphic>](img/ch2_0.gif) #<procedure>

(define x 'a)

(list x x) ![<graphic>](img/ch2_0.gif) (a a)

(let ([x 'b])

(list x x)) ![<graphic>](img/ch2_0.gif) (b b)

(let ([let 'let]) let) ![<graphic>](img/ch2_0.gif) let`

如果在`library`形式或顶层程序中出现标识符引用，且未绑定为变量、关键字、记录名称或其他实体，则这是语法违例。由于`library`、顶层程序、`lambda`或其他局部主体中定义的范围是整个主体，因此变量的定义不必出现在其第一次引用之前，只要引用在定义完成之前实际上不被评估即可。因此，例如，下面`f`的定义中对`g`的引用

`(define f

(lambda (x)

(g x)))

(define g

(lambda (x)

(+ x x)))`

是可以的，但下面`q`的定义中对`g`的引用则不行。

`(define q (g 3))

(define g

(lambda (x)

(+ x x)))`

### 第 4.2 节。Lambda

**语法**：`(lambda *formals* *body[1]* *body[2]* ...)`

**返回：** 一个过程

**libraries:** `(rnrs base)`, `(rnrs)`

`lambda`语法形式用于创建过程。任何创建过程或建立局部变量绑定的操作最终都是以`lambda`或`case-lambda`来定义的。

`*formals*`中的变量是过程的形式参数，子形式序列`*body[1]* *body[2]* ...`是其主体。

如果正文以一系列定义开始，则由定义创建的绑定仅在正文中局部有效。如果存在定义，则在展开正文时使用并且丢弃关键字绑定，将正文展开为由变量定义和剩余表达式形成的`letrec*`表达式，如 292 页所述。`lambda`的描述的其余部分假定如果需要，已经进行了这种转换，以便正文是一系列不带定义的表达式。

创建过程时，保留在正文中自由出现的所有变量的绑定，不包括形式参数，与该过程一起。随后，每当将过程应用于一系列实际参数时，形式参数绑定到实际参数，恢复保留的绑定，并评估正文。

在应用时，由`*formals*`定义的形式参数绑定到实际参数如下。

+   如果`*formals*`是变量的适当列表，例如`(x y z)`，则每个变量都绑定到相应的实际参数。如果提供的实际参数太少或太多，则引发条件类型为`&assertion`的异常。

+   如果`*formals*`是单个变量（不在列表中），例如`z`，则它绑定到实际参数的列表。

+   如果`*formals*`是以变量结尾的不规则列表，例如`(x y . z)`，则除最后一个变量外，每个变量都绑定到相应的实际参数。最后一个变量绑定到剩余的实际参数列表。如果提供的实际参数太少，则引发条件类型为`&assertion`的异常。

当评估正文时，按顺序评估正文中的表达式，并且过程返回最后一个表达式的值。

过程在通常意义上没有打印表示。 Scheme 系统以不同的方式打印过程； 本书使用符号`#<procedure>`。

`(lambda (x) (+ x 3)) ![<graphic>](img/ch2_0.gif) #<procedure>

((lambda (x) (+ x 3)) 7) ![<graphic>](img/ch2_0.gif) 10

((lambda (x y) (* x (+ x y))) 7 13) ![<graphic>](img/ch2_0.gif) 140

((lambda (f x) (f x x)) + 11) ![<graphic>](img/ch2_0.gif) 22

((lambda () (+ 3 4))) ![<graphic>](img/ch2_0.gif) 7

((lambda (x . y) (list x y))

28 37) ![<graphic>](img/ch2_0.gif) (28 (37))

((lambda (x . y) (list x y))

28 37 47 28) ![<graphic>](img/ch2_0.gif) (28 (37 47 28))

((lambda (x y . z) (list x y z))

1 2 3 4) ![<graphic>](img/ch2_0.gif) (1 2 (3 4))

((lambda x x) 7 13) ![<graphic>](img/ch2_0.gif) (7 13)`

### 第 4.3 节。Case-Lambda

Scheme `lambda`表达式始终生成具有固定数量的参数或具有大于或等于某个数量的不确定数量的参数的过程。 特别地，

`(lambda (*var[1]* ... *var[n]*) *body[1]* *body[2]* ...)`

接受`*n*`个参数，

`(lambda *r* *body[1]* *body[2]* ...)`

接受零个或多个参数，并且

`(lambda (*var[1]* ... *var[n]* . *r*) *body[1]* *body[2]* ...)`

接受`*n*`个或更多参数。

`lambda`不能直接生成一个接受两个或三个参数的过程。特别是，接受可选参数的过程不能直接由`lambda`支持。上面显示的后一种`lambda`形式可以与长度检查和`car`和`cdr`的组合一起使用，以实现具有可选参数的过程，尽管这会牺牲清晰度和效率。

`case-lambda`语法形式直接支持具有可选参数以及具有固定或不定数量参数的过程。`case-lambda`基于文章"A New Approach to Procedures with Variable Arity" [11]中介绍的`lambda*`语法形式。

**语法**：`(case-lambda *clause* ...)`

**返回**：一个过程

**库**：`(rnrs control)`，`(rnrs)`

一个`case-lambda`表达式由一组类似于`lambda`表达式的子句组成。每个`*clause*`的形式如下。

`[*formals* *body[1]* *body[2]* ...]`

子句的形式参数由`*formals*`以与`lambda`表达式相同的方式定义。`case-lambda`表达式的过程值接受的参数数量由各个子句接受的参数数量确定。

当使用`case-lambda`创建的过程被调用时，子句按顺序考虑。选择接受给定实际参数数量的第一个子句，其由`*formals*`定义的形式参数绑定到相应的实际参数，并且该体按照上述`lambda`的描述进行评估。如果子句中的`*formals*`是标识符的适当列表，则该子句接受与`*formals*`中的形式参数（标识符）数量相同的实际参数。与`lambda`的`*formals*`一样，`case-lambda`子句的`*formals*`可以是单个标识符，此时该子句接受任意数量的参数，或者是由标识符终止的不适当的标识符列表，此时该子句接受大于或等于形式参数数量的参数数量，不包括终止标识符。如果没有子句接受提供的实际参数数量，则会引发一个带有条件类型`&assertion`的异常。

下面的`make-list`定义使用`case-lambda`来支持一个可选的填充参数。

`(define make-list

(case-lambda

[(n) (make-list n #f)]

[(n x)

(do ([n n (- n 1)] [ls '() (cons x ls)])

((zero? n) ls))]))

`substring`过程可以通过`case-lambda`扩展，以接受没有`*end*`索引的情况，此时默认为字符串的末尾，或者没有`*start*`和`*end*`索引的情况，此时`substring`等同于`string-copy`：

`(define substring1

(case-lambda

[(s) (substring1 s 0 (string-length s))]

[(s start) (substring1 s start (string-length s))]

[(s start end) (substring s start end)]))`

当只提供一个索引时，默认可以将`*start*`索引而不是`*end*`索引设置为默认值：

`(define substring2

(case-lambda

[(s) (substring2 s 0 (string-length s))]

[(s end) (substring2 s 0 end)]

[(s start end) (substring s start end)]))`

甚至可以要求`*start*`和`*end*`索引都提供或都不提供，只需省略中间子句：

`(define substring3

(case-lambda

[(s) (substring3 s 0 (string-length s))]

[(s start end) (substring s start end)]))`

### 第 4.4 节。局部绑定

**语法**: `(let ((*var* *expr*) ...) *body[1]* *body[2]* ...)`

**返回:** 最终体表达式的值

**库:** `(rnrs base)`, `(rnrs)`

`let`用于建立局部变量绑定。每个变量`*var*`绑定到相应表达式`*expr*`的值。`let`的体，其中变量绑定，是子形式的序列`*body[1]* *body[2]* ...`，并且像`lambda`体一样被处理和计算。

`let`、`let*`、`letrec`和`letrec*`（其他描述在`let`之后）的形式类似，但用途略有不同。与`let*`、`letrec`和`letrec*`相比，`let`中的表达式`*expr* ...`都不在变量`*var* ...`的作用域内。此外，与`let*`和`letrec*`相比，不暗示表达式`*expr* ...`的评估顺序。它们可以按照任意顺序由实现自行决定从左到右、从右到左或以其他任何顺序进行评估。只有当值与变量无关且评估顺序不重要时才使用`let`。

`(let ([x (* 3.0 3.0)] [y (* 4.0 4.0)])

(sqrt (+ x y))) ![<graphic>](img/ch2_0.gif) 5.0

(let ([x 'a] [y '(b c)])

(cons x y)) ![<graphic>](img/ch2_0.gif) (a b c)

(let ([x 0] [y 1])

(let ([x y] [y x])

(list x y))) ![<graphic>](img/ch2_0.gif) (1 0)`

`let`的以下定义显示了从`lambda`到`let`的典型推导。

`(define-syntax let

(syntax-rules ()

[(_ ((x e) ...) b1 b2 ...)

((lambda (x ...) b1 b2 ...) e ...)]))`

另一种形式的`let`，*命名*为`let`，在第 5.4 节中描述，并且完整`let`的定义可在第 312 页找到。

**语法**: `(let* ((*var* *expr*) ...) *body[1]* *body[2]* ...)`

**返回:** 最终体表达式的值

**库:** `(rnrs base)`, `(rnrs)`

`let*`类似于`let`，不同之处在于表达式`*expr* ...`按从左到右的顺序依次计算，并且每个表达式都在左侧变量的作用域内。当值之间存在线性依赖或计算顺序重要时，请使用`let*`。

`(let* ([x (* 5.0 5.0)]

[y (- x (* 4.0 4.0))])

(sqrt y)) ![<graphic>](img/ch2_0.gif) 3.0

(let ([x 0] [y 1])

(let* ([x y] [y x])

(list x y))) ![<graphic>](img/ch2_0.gif) (1 1)`

任何`let*`表达式都可以转换为一组嵌套的`let`表达式。以下对`let*`的定义展示了典型的转换。

`(define-syntax let*

(syntax-rules ()

[(_ () e1 e2 ...)

(let () e1 e2 ...)]

[(_ ((x1 v1) (x2 v2) ...) e1 e2 ...)

(let ((x1 v1))

(let* ((x2 v2) ...) e1 e2 ...))]))`

**语法**：`(letrec ((*var* *expr*) ...) *body[1]* *body[2]* ...)`

**返回**：最终主体表达式的值

**库**：`(rnrs base)`，`(rnrs)`

`letrec`类似于`let`和`let*`，不同之处在于所有表达式`*expr* ...`都在所有变量`*var* ...`的作用域内。`letrec`允许定义相互递归的过程。

`(letrec ([sum (lambda (x)

(if (zero? x)

0

(+ x (sum (- x 1)))))])

(sum 5)) ![<graphic>](img/ch2_0.gif) 15`

对表达式`*expr* ...`的评估顺序是未指定的，因此程序在计算所有值之前不能评估`letrec`表达式中绑定的任何变量的引用。 （变量在`lambda`表达式中的出现不算作引用，除非生成的过程在计算所有值之前被应用。）如果违反此限制，将引发带条件类型`&assertion`的异常。

一个`*expr*`不应该返回多次。也就是说，在其评估过程中，它不应该正常返回和通过调用其获得的延续返回，也不应该通过两次调用这样的延续返回两次。实现不需要检测此限制的违反，但如果检测到，将引发带有条件类型`&assertion`的异常。

当变量及其值之间存在循环依赖且评估顺序不重要时，选择`letrec`而不是`let`或`let*`。当存在循环依赖并且需要从左到右评估绑定时，选择`letrec*`而不是`letrec`。

`letrec`表达式的形式

`(letrec ((*var* *expr*) ...) *body[1]* *body[2]* ...)`

可以用`let`和`set!`来表达

`(let ((*var* #f) ...)

(let ((*temp* *expr*) ...)

(set! *var* *temp*) ...

(let () *body[1]* *body[2]* ...)))`

其中`*temp* ...`是新变量，即在`letrec`表达式中尚未出现的变量，每个`(*var* *expr*)`对应一个变量。外部`let`表达式建立变量绑定。每个变量的初始值并不重要，因此在`#f`的位置上任何值都可以。首先建立绑定，以便`*expr* ...`可以包含变量的出现，即在变量的作用域内计算表达式。中间的`let`评估值并将其绑定到临时变量，`set!`表达式将每个变量分配给相应的值。内部的`let`存在是为了防止主体包含内部定义。

使用这种转换的`letrec`的定义在第 310 页上显示。

此转换不强制`*expr*`表达式不能评估任何对变量的引用或赋值的限制。可以进行更复杂的转换，以强制执行此限制并实际生成更有效的代码 [31]。

**syntax**: `(letrec* ((*var* *expr*) ...) *body[1]* *body[2]* ...)`

**返回值:** 最终 body 表达式的值

**libraries:** `(rnrs base)`，`(rnrs)`

`letrec*`类似于`letrec`，不同之处在于`letrec*`按从左到右的顺序评估`*expr* ...`。虽然程序仍然不能在相应的`*expr*`被评估之前评估对任何`*var*`的引用，但对`*var*`的引用可以在此后的任何时间评估，包括在任何后续绑定的`*expr*`的评估过程中。

一个形式为`letrec*`的表达式

`(letrec* ((*var* *expr*) ...) *body[1]* *body[2]* ...)`

可以用`let`和`set!`来表达

`(let ((*var* #f) ...)

(set! *var* *expr*) ...

(let () *body[1]* *body[2]* ...))`

外部的`let`表达式创建了绑定，每个赋值都评估一个表达式并立即将相应的变量设置为其值，按顺序进行，内部的 let 评估 body。在后一种情况下使用`let`而不是`begin`，因为 body 可能包括内部定义以及表达式。

`(letrec* ([sum (lambda (x)

(if (zero? x)

0

(+ x (sum (- x 1)))))]

[f (lambda () (cons n n-sum))]

[n 15]

[n-sum (sum n)])

(f)) ![<graphic>](img/ch2_0.gif) (15 . 120)

(letrec* ([f (λ () (λ () g))]

[g (f)]

(eq? (g) g)) ![<graphic>](img/ch2_0.gif) #t

(letrec* ([g (λ () (λ () g))]

[f (lambda () (lambda () g))])

(eq? (g) g)) ![<graphic>](img/ch2_0.gif) *异常：尝试引用未定义的变量 f*`

### 第 4.5 节。多值

**syntax**: `(let-values ((*formals* *expr*) ...) *body[1]* *body[2]* ...)`

**syntax**: `(let*-values ((*formals* *expr*) ...) *body[1]* *body[2]* ...)`

**返回值:** 最终 body 表达式的值

**libraries:** `(rnrs base)`，`(rnrs)`

`let-values`是接收多个值并将它们绑定到变量的便捷方式。它的结构类似于`let`，但允许在每个左侧都有一个任意的形式列表（类似于`lambda`）。`let*-values`类似，但按从左到右的顺序执行绑定，就像`let*`一样。如果由`*expr*`返回的值的数量不适合相应的`*formals*`，则会引发带有条件类型`&assertion`的异常，如上面`lambda`条目中所述。`let-values`的定义在第 310 页上给出。

`(let-values ([(a b) (values 1 2)] [c (值 1 2 3)])

(list a b c)) ![<graphic>](img/ch2_0.gif) (1 2 (1 2 3))

(let*-values ([(a b) (values 1 2)] [(a b) (values b a)])

(list a b)) ![<graphic>](img/ch2_0.gif) (2 1)`

### 第 4.6 节。变量定义

**syntax**: `(define *var* *expr*)`

**语法**：`(define *var*)`

**语法**：`(define (*var[0]* *var[1]* ...) *body[1]* *body[2]* ...)`

**语法**：`(define (*var[0]* . *var[r]*) *body[1]* *body[2]* ...)`

**语法**：`(define (*var[0]* *var[1]* *var[2]* ... . *var[r]*) *body[1]* *body[2]* ...)`

**库：**`(rnrs base)`，`(rnrs)`

在第一种形式中，`define`创建一个新的将`*var*`绑定到`*expr*`值的绑定。`*expr*`不应返回多次。也就是说，在其评估期间，它不应正常返回并通过调用期间获得的延续调用两次而正常返回。实现不需要检测此限制的违反，但如果检测到，则引发具有条件类型`&assertion`的异常。

第二种形式等同于`(define *var* *unspecified*)`，其中`*unspecified*`是某个未指定的值。其余的是将变量绑定到过程的速记形式；它们与`lambda`中的以下定义相同。

`(define *var*

(lambda *formals*

*body[1]* *body[2]* ...))`

其中`*formals*`为`(*var[1]* ...)`，`*var[r]*`或第三个，第四个和第五个`define`格式的`(*var[1]* *var[2]* ... . *var[r]*)`。

定义可以出现在`library`主体的前面，在顶级程序主体的任何形式之间的任何位置，以及在`lambda`或`case-lambda`主体或任何形式的主体中，例如`lambda`，`let`或`letrec*`的派生主体。以一系列定义开始的任何主体在宏扩展期间转换为`letrec*`表达式，如第 292 页所述。

语法定义可以与变量定义一起出现，无论变量定义何时出现；参见第八章。

`(define x 3)

x ![<graphic>](img/ch2_0.gif) 3

(define f

(lambda (x y)

(* (+ x y) 2)))

(f 5 4) ![<graphic>](img/ch2_0.gif) 18

(define (sum-of-squares x y)

(+ (* x x) (* y y)))

(sum-of-squares 3 4) ![<graphic>](img/ch2_0.gif) 25

(define f

(lambda (x)

(+ x 1)))

(let ([x 2])

(define f

(lambda (y)

(+ y x)))

(f 3)) ![<graphic>](img/ch2_0.gif) 5

(f 3) ![<graphic>](img/ch2_0.gif) 4`

一组定义可以通过将它们封装在`begin`形式中来分组。以这种方式分组的定义可以出现在普通变量和语法定义可以出现的任何地方。它们被视为分开编写，即不带有封装的`begin`形式。此功能允许语法扩展扩展为定义组。

`(define-syntax multi-define-syntax

(syntax-rules ()

[(_ (var expr) ...)

(begin

(define-syntax var expr)

...)]))

(let ()

(define plus

(lambda (x y)

(if (zero? x)

y

(plus (sub1 x) (add1 y)))))

(multi-define-syntax

(add1 (syntax-rules () [(_ e) (+ e 1)]))

(sub1 (syntax-rules () [(_ e) (- e 1)])))

(plus 7 8)) ![<graphic>](img/ch2_0.gif) 15`

许多实现支持交互式的“顶层”，其中变量和其他定义可以交互输入或从文件加载。这些顶层定义的行为超出了修订⁶报告的范围，但只要在评估任何引用或分配之前定义顶层变量，大多数实现的行为是一致的。因此，例如，下面 `f` 的顶层定义中对 `g` 的引用是可以的，如果 `*g*` 尚未定义，并且假定 `g` 是一个稍后要定义的变量。

`(define f

(lambda (x)

(g x)))`

如果随后在评估 `f` 之前定义了 `g`，则假设 `g` 将被定义为一个变量的假设是正确的，并且对 `f` 的调用按预期工作。

`(define g

(lambda (x)

(+ x x)))

(f 3) ![<graphic>](img/ch2_0.gif) 6`

如果 `g` 被定义为语法扩展的关键字，那么假设 `g` 会被绑定为一个变量是错误的，如果在调用之前 `f` 没有被重新定义，那么实现很可能会引发异常。

### 第 4.7 节。赋值

**语法：** `(set! *var* *expr*)`

**返回：** 未指定

**库：** `(rnrs base)`, `(rnrs)`

`set!` 并不为 `*var*` 建立新的绑定，而是改变现有绑定的值。它首先评估 `*expr*`，然后将 `*var*` 分配给 `*expr*` 的值。在修改后的绑定范围内，对 `*var*` 的任何后续引用都会评估为新值。

在 Scheme 中，赋值并不像大多数其他语言那样频繁使用，但对于实现状态变化很有用。

`(define flip-flop

(让 ([state #f])

(lambda ()

(set! state (not state))

state)))

(flip-flop) ![<graphic>](img/ch2_0.gif) #t

(flip-flop) ![<graphic>](img/ch2_0.gif) #f

(flip-flop) ![<graphic>](img/ch2_0.gif) #t`

赋值还可用于缓存值。下面的示例使用一种称为 *记忆化* 的技术，其中一个过程记录与旧输入值相关联的值，因此无需重新计算它们，以实现对斐波那契函数的指数双递归定义的快速版本（参见第 69 页）。

`(define memoize

(lambda (proc)

(让 ([cache '()])

(lambda (x)

(cond

[(assq x cache) => cdr]

[否则

(让 ([ans (proc x)])

(set! cache (cons (cons x ans) cache))

ans)])))))

(define fibonacci

(记忆化

(lambda (n)

(if (< n 2)

1

(+ (fibonacci (- n 1)) (fibonacci (- n 2)))))))

(fibonacci 100) ![<graphic>](img/ch2_0.gif) 573147844013817084101`
