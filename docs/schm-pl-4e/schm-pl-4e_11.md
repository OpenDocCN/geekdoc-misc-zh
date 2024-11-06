# 第十一章。异常和条件

*异常*和*条件*提供了系统和用户代码在运行程序时信号、检测和从错误中恢复的手段。

标准语法形式和过程在各种情况下引发异常，例如当向过程传递了错误数量的参数时，当传递给`eval`的表达式的语法不正确时，或者当文件不能被一个文件打开过程打开时。在这些情况下，异常将被引发为标准条件类型。

异常也可以通过`raise`或`raise-continuable`过程由用户代码引发。在这种情况下，异常可以由标准条件类型、标准条件类型的用户定义子类型（可能使用`define-condition-type`定义）、或者不是条件类型的任意 Scheme 值引发。

在程序执行过程中的任何时刻，都有一个称为*当前异常处理程序*的单一异常处理程序负责处理所有引发的异常。默认情况下，当前异常处理程序是由实现提供的。默认异常处理程序通常会打印一个描述引发异常的条件或其他值的消息，并且对于任何严重的条件，会终止正在运行的程序。在交互式系统中，这通常意味着重置为读取-求值-打印循环。

用户代码可以通过`guard`语法或`with-exception-handler`过程建立一个新的当前异常处理程序。在任何情况下，用户代码都可以处理所有异常，或者根据异常引发的条件或其他值，只处理其中的一些异常，同时将其他异常重新引发给旧的当前异常处理程序处理。当动态嵌套`guard`形式和`with-exception-handler`调用时，会建立一个异常处理程序链，并且每个异常处理程序可能会推迟到链中的下一个处理程序。

### 第 11.1 节。抛出和处理异常

**过程**: `(raise *obj*)`

**过程**: `(raise-continuable *obj*)`

**返回**: 见下文

**库**: `(rnrs exceptions)`，`(rnrs)`

这两个过程都会引发异常，有效地调用当前异常处理程序，并将`*obj*`作为唯一参数传递。对于`raise`，异常是*不可继续的*，而对于`raise-continuable`，异常是*可继续的*。异常处理程序可以返回（带有零个或更多个值）到可继续异常的继续。然而，如果异常处理程序尝试返回到不可继续异常的继续，将引发一个新的条件类型为`&non-continuable`的异常。因此，`raise`永远不会返回，而`raise-continuable`可能根据异常处理程序返回零个或多个值。

如果当前的异常处理程序 `*p*` 是通过 `guard` 表单或调用 `with-exception-handler` 建立的，则在 `raise` 或 `raise-continuable` 调用 `*p*` 之前将当前的异常处理程序重置为建立 `*p*` 时当前的处理程序。这允许 `*p*` 简单地通过重新引发异常来推迟到先前存在的异常处理程序，并且当异常处理程序无意中导致引发其他异常时，它有助于防止无限递归。如果 `*p*` 返回并且异常是可继续的，则 `*p*` 将被重新设置为当前的异常处理程序。

`(raise

(condition

(make-error)

(make-message-condition "不行了"))) ![<graphic>](img/ch2_0.gif) *错误：不行了*

(raise-continuable

(condition

(make-violation)

(make-message-condition "哎呀"))) ![<graphic>](img/ch2_0.gif) *违反：哎呀*

(list

(call/cc

(lambda (k)

(vector

(with-exception-handler

(lambda (x) (k (+ x 5)))

(lambda () (+ (raise 17) 8))))))) ![<graphic>](img/ch2_0.gif) (22)

(list

(vector

(with-exception-handler

(lambda (x) (+ x 5))

(lambda () (+ (raise-continuable 17) 8))))) ![<graphic>](img/ch2_0.gif) (#(30))

(list

(vector

(with-exception-handler

(lambda (x) (+ x 5))

(lambda () (+ (raise 17) 8))))) ![<graphic>](img/ch2_0.gif) *违反：不可继续*`

**过程**: `(error *who* *msg* *irritant* ...)`

**过程**: `(assertion-violation *who* *msg* *irritant* ...)`

**库:** `(rnrs base)`, `(rnrs)`

`error` 引发一个具有条件类型 `&error` 的不可继续异常，并应用于描述与程序外部交互有关的情况，典型情况涉及程序与程序外部的某些东西的交互。 `assertion-violation` 引发一个具有条件类型 `&assertion` 的不可继续异常，并应用于描述适用于 `&assertion` 条件类型的情况，典型情况是过程的无效参数或语法形式的子表达式的无效值。

触发异常的延续对象还包括一个 `&who` 条件，其 who 字段为 `*who*`，如果 `*who*` 不是 `#f`，则一个 `&message` 条件，其 message 字段为 `*msg*`，以及一个 `&irritants` 条件，其 irritants 字段为 `(*irritant* ...)`。

`*who*` 必须是字符串、符号或 `#f`，用于标识报告错误的过程或语法形式所在的过程。通常最好标识程序员调用的过程，而不是程序员可能不知道涉及执行操作的其他过程。 `*msg*` 必须是字符串，并应描述异常情况。激怒物可以是任何 Scheme 对象，并且应包括可能导致或实质上涉及异常情况的值。

**语法**: `(assert *expression*)`

**返回:** 见下文

**库:** `(rnrs base)`, `(rnrs)`

`assert` evaluates `*expression*` and returns the value of `*expression*` if the value is not `#f`. If the value of `*expression*` is `#f`, `assert` raises a non-continuable exception with condition types `&assertion` and `&message`, with an implementation-dependent value in its message field. Implementations are encouraged to provide information about the location of the `assert` call within the condition whenever possible.

**procedure**: `(syntax-violation *who* *msg* *form*)`

**procedure**: `(syntax-violation *who* *msg* *form* *subform*)`

**returns:** does not return

**libraries:** `(rnrs syntax-case)`, `(rnrs)`

This procedure raises a non-continuable exception with a condition of type `&syntax`. It should be used to report a syntax error detected by the transformer of a syntactic extension. The value of the condition's form field is `*form*`, and the value of its subform field is `*subform*`, or `#f` if `*subform*` is not provided.

The continuation object with which the exception is raised also includes a `&who` condition whose who field is `*who*`, if `*who*` is not `#f` or is inferred from `*form*`, and a `&message` condition whose message field is `*msg*`.

`*who*` must be a string, a symbol, or `#f`. If `*who*` is `#f`, it is inferred to be the symbolic name of `*form*` if `*form*` is an identifier or the symbolic name of the first subform of `*form*` if `*form*` is a list-structured form whose first subform is an identifier. `*message*` must be a string. `*form*` should be the syntax object or datum representation of the syntactic form within which the syntax violation occurred, and `*subform*`, if not `#f`, should be a syntax object or datum representation of a subform more specifically involved in the violation. For example, if a duplicate formal parameter is found in a `lambda` expression, `*form*` might be the `lambda` expression and `*subform*` might be the duplicated parameter.

Some implementations attach source information to syntax objects, e.g., line, character, and filename for forms originating in a file, in which case this information might also be present as some implementation-dependent condition type within the condition object.

**procedure**: `(with-exception-handler *procedure* *thunk*)`

**returns:** see below

**libraries:** `(rnrs exceptions)`, `(rnrs)`

This procedure establishes `*procedure*`, which should accept one argument, as the current exception handler in place of the old current exception handler, `*old-proc*`, and invokes `*thunk*` without arguments. If the call to `*thunk*` returns, `*old-proc*` is reestablished as the current exception handler and the values returned by `*thunk*` are returned. If control leaves or subsequently reenters the call to `*thunk*` via the invocation of a continuation obtained via `call/cc`, the procedure that was the current exception handler when the continuation was captured is reinstated.

`(define (try thunk)

(call/cc

(lambda (k)

(with-exception-handler

（lambda （x） （如果 （错误？ x） （k #f） （提高 x））

thunk））））

（尝试 （lambda （） 17）） ![<graphic>](img/ch2_0.gif) 17

（尝试 （lambda （） （提高 （制造错误））） ![<graphic>](img/ch2_0.gif) #f

（尝试 （lambda （） （提高 （制造违规））） ![<graphic>](img/ch2_0.gif) *违规*

（使用-异常-处理程序

（lambda （x）

（提高

（应用 条件

（制作-消息-条件“糟糕”）

（简单条件 x))))

（lambda （）

（尝试 （lambda （） （提高 （制造违规））））） ![<graphic>](img/ch2_0.gif) *违规：糟糕*`

**语法:** `（guard （*var* *clause[1]* *clause[2]* ...） *b1* *b2* ...）`

**返回:**见下文

**库:** `（rnrs 异常）`，`（rnrs）`

`guard`表达式建立了一个新的当前异常处理程序`*procedure*`（如下所述），代替了旧的当前异常处理程序`*old-proc*`，并评估了主体`*b1* *b2* ...`。如果主体返回，`guard`重新建立`*old-proc*`作为当前异常处理程序。如果控制通过`调用/ cc`获取的继续离开或随后重新进入主体，则重新建立捕获继续时的当前异常处理程序。

由`guard`建立的过程`*procedure*`将`*var*`绑定到接收的值，并在该绑定的范围内依次处理子句`*clause[1]* *clause[2]* ...`，就像包含在隐式`条件`表达式中一样。该隐式`条件`表达式在`guard`表达式的继续中求值，`*old-proc*`作为当前异常处理程序。

如果未提供`其他`子句，则`guard`会使用一个子句，以与`提高-可继续`相同的值重新引发异常，`*old-proc*`作为当前异常处理程序。

`（保护 （x [其他 x]） （提高 "糟糕"）） ![<graphic>](img/ch2_0.gif) "糟糕"

（保护 （x （[#f #f]）） （提高 （制造错误））） ![<graphic>](img/ch2_0.gif)  *错误*

（定义语法 尝试

（语法规则 ）

[（_ e1 e2 ...)

（保护 （x （（错误？ x） #f）） e1 e2 ...]）

（定义 open-one

（lambda fn*

（让 循环 （[ls fn*]）

（如果 （null？ ls）

（错误 'open-one "所有打开尝试均失败" fn*）

（或 （尝试 （打开输入文件 （car ls）））

（循环 （cdr ls）））））

; 假设 bar.ss 存在但 foo.ss 不存在：

（open-one "foo.ss" "bar.ss"） ![<graphic>](img/ch2_0.gif) #<input port bar.ss>`

### 第 11.2 节。定义条件类型

虽然程序可能传递`提高`或`提高-可继续`任何 Scheme 值，但通常描述异常情况的最佳方法是创建并传递*条件对象*。在修订⁶报告中要求实现引发异常的地方，传递给当前异常处理程序的值始终是一个或多个标准*条件类型*的条件对象，这些类型在第 11.3 节中描述。用户代码可以创建一个是一个或多个标准条件类型实例的条件对象，也可以创建一个扩展的条件类型并创建该类型的条件对象。

条件类型类似于记录类型，但更灵活，因为条件对象可以是两个或更多条件类型的实例，即使两者都不是彼此的子类型。当一个条件是多个类型的实例时，它被称为*复合条件*。复合条件对于向异常处理程序传递有关异常的多个信息非常有用。不是复合条件的条件被称为*简单条件*。在大多数情况下，这两者之间的区别并不重要，简单条件被视为只有自身作为其唯一简单条件的复合条件。

**syntax**: `&condition`

**libraries:** `(rnrs conditions)`, `(rnrs)`

`&condition`是一个记录类型名称（第九章）和条件类型层次结构的根。所有简单条件类型都是这种类型的扩展，所有条件，无论是简单的还是复合的，都被视为这种类型的实例。

**procedure**: `(condition? *obj*)`

**returns:** 如果`*obj*`是条件对象，则返回`#t`，否则返回`#f`

**libraries:** `(rnrs conditions)`, `(rnrs)`

条件对象是`&condition`的子类型的实例或可能由用户代码使用`condition`创建的复合条件。

`(condition? 'stable) ![<graphic>](img/ch2_0.gif) #f

(condition? (make-error)) ![<graphic>](img/ch2_0.gif) #t

(condition? (make-message-condition "oops")) ![<graphic>](img/ch2_0.gif) #t

(condition?

(condition

(make-error)

(make-message-condition "no such element"))) ![<graphic>](img/ch2_0.gif) #t`

**procedure**: `(condition *condition* ...)`

**returns:** 一个条件，可能是复合的

**libraries:** `(rnrs conditions)`, `(rnrs)`

`condition`用于创建可能由多个简单条件组成的条件对象。每个参数`*condition*`可以是简单的或复杂的；如果是简单的，则将其视为一个只有自身作为其唯一简单条件的复合条件。结果条件的简单条件是`*condition*`参数的简单条件，展平为一个列表并按顺序出现，第一个`*condition*`的简单条件后面是第二个的简单条件，依此类推。

如果列表恰好有一个元素，则结果条件可以是简单的或复合的；否则它是复合的。简单条件和复合条件之间的区别通常不重要，但如果使用`define-record-type`而不是`define-condition-type`来扩展现有条件类型，则可以通过`define-record-type`定义的谓词来检测。

`(condition) ![<graphic>](img/ch2_0.gif) #<condition>

(condition

(make-error)

(make-message-condition "oops")) ![<graphic>](img/ch2_0.gif) #<condition>

(define-record-type (&xcond make-xcond xcond?) (parent &condition))

(xcond? (make-xcond)) ![<graphic>](img/ch2_0.gif) #t

(xcond? (condition (make-xcond))) ![<graphic>](img/ch2_0.gif) #t *or* #f

(xcond? (condition)) ![<graphic>](img/ch2_0.gif) #f

(xcond? (condition (make-error) (make-xcond))) ![<graphic>](img/ch2_0.gif) #f`

**过程**：`(simple-conditions *condition*)`

**返回**：`*condition*`的简单条件列表

**库**：`(rnrs conditions)`，`(rnrs)`

`(simple-conditions (condition)) ![<graphic>](img/ch2_0.gif) '()

(simple-conditions (make-error)) ![<graphic>](img/ch2_0.gif) (#<condition &error>)

(simple-conditions (condition (make-error))) ![<graphic>](img/ch2_0.gif) (#<condition &error>)

(simple-conditions

(condition

(make-error)

(make-message-condition

"哎呀"))) ![<graphic>](img/ch2_0.gif) (#<condition &error> #<condition &message>)

(let ([c1 (make-error)]

[c2 (make-who-condition "f")]

[c3 (make-message-condition "无效参数")]

[c4 (make-message-condition

"读取文件时发生错误")]

[c5 (make-irritants-condition '("a.ss"))])

(equal?

(simple-conditions

(condition

(condition (condition c1 c2) c3)

(condition c4 (condition c5))))

(list c1 c2 c3 c4 c5))) ![<graphic>](img/ch2_0.gif) #t`

**语法**：`(define-condition-type *name* *parent* *constructor* *pred* *field* ...)`

**库**：`(rnrs conditions)`，`(rnrs)`

`define-condition-type`形式是一个定义，可以出现在其他定义可以出现的任何地方。它用于定义新的简单条件类型。

子表达式`*name*`、`*parent*`、`*constructor*`和`*pred*`必须是标识符。每个`*field*`必须是形式为`(*field-name* *accessor-name*)`的标识符，其中`*field-name*`和`*accessor-name*`是标识符。

`define-condition-type`将`*name*`定义为一个新的记录类型，其父记录类型是`*parent*`，构造函数名为`*constructor*`，谓词名为`*pred*`，字段为`*field-name* ...`，字段访问器由`*accessor-name* ...`命名。

除了谓词和字段访问器之外，`define-condition-type`本质上是一个普通的记录定义，等同于

`(define-record-type (*name* *constructor* *pred*)

(parent *parent*)

(fields ((immutable *field-name* *accessor-name*) ...)))`

谓词与`define-record-type`形式生成的谓词不同，它不仅对新类型的实例返回`#t`，而且对于包含新类型实例的复合条件也返回`#t`。类似地，字段访问器接受新类型的实例以及包含至少一个新记录类型实例的复合条件。如果访问器接收到一个包含新类型实例的复合条件，其简单条件列表包含一个或多个新类型实例，则访问器将操作列表中的第一个实例。

`(define-condition-type &mistake &condition make-mistake mistake?

(类型 mistake-type))

(mistake? 'booboo) ![<graphic>](img/ch2_0.gif) #f

(define c1 (make-mistake 'spelling))

(mistake? c1) ![<graphic>](img/ch2_0.gif) #t

(mistake-type c1) ![<graphic>](img/ch2_0.gif) 拼写

(define c2 (condition c1 (make-irritants-condition '(eggregius))))

(mistake? c2) ![<graphic>](img/ch2_0.gif)��#t

(mistake-type c2) ![<graphic>](img/ch2_0.gif) 拼写

(irritants-condition? c2) ![<graphic>](img/ch2_0.gif) #t

(condition-irritants c2) ![<graphic>](img/ch2_0.gif) (eggregius)`

**procedure**: `(condition-predicate *rtd*)`

**returns:** 一个条件谓词

**procedure**: `(condition-accessor *rtd* *procedure*)`

**returns:** 一个条件访问器

**libraries:** `(rnrs conditions)`, `(rnrs)`

这些过程可用于创建与由记录类型描述符 `*rtd*` 创建的特殊谓词和访问器相同类型的谓词和访问器，该描述符是简单条件类型或从简单条件类型派生的其他类型的实例。

对于这两个过程，`*rtd*` 必须是 `&condition` 的子类型的记录类型描述符，并且对于 `condition-accessor`，`*procedure*` 应接受一个参数。

`condition-predicate` 返回的谓词接受一个参数，该参数可以是任何 Scheme 值。 如果该值是由 `*rtd*` 描述的类型的条件，即由 `*rtd*` 描述的类型的实例（或其子类型之一）或其简单条件包括由 `*rtd*` 描述的类型的实例的复合条件，则谓词返回 `#t`。 否则，谓词返回 `#f`。

`condition-accessor` 返回的访问器接受一个参数 `*c*`，该参数必须是由 `*rtd*` 描述的类型的条件。 访问器将 `*procedure*` 应用于一个参数，即 `*c*` 的简单条件列表的第一个元素，该元素是由 `*rtd*` 描述的类型的实例（如果 `*c*` 是简单条件，则为 `*c*` 本身），并返回此应用的结果。 在大多数情况下，`*procedure*` 是由 `*rtd*` 描述的类型的字段的记录访问器。

`(define-record-type (&mistake make-mistake $mistake?)

(parent &condition)

(fields (immutable type $mistake-type)))

; 假设我们使用了 `define-condition-type` 来定义谓词和访问器

(define rtd (record-type-descriptor &mistake))

(define mistake? (condition-predicate rtd))

(define mistake-type (condition-accessor rtd $mistake-type))

(define c1 (make-mistake 'spelling)

(define c2 (condition c1 (make-irritants-condition '(eggregius))))

(list (mistake? c1) (mistake? c2)) ![<graphic>](img/ch2_0.gif) (#t #t)

(list ($mistake? c1) ($mistake? c2)) ![<graphic>](img/ch2_0.gif) (#t #f)

(mistake-type c1) ![<graphic>](img/ch2_0.gif) 拼写

($mistake-type c1) ![<graphic>](img/ch2_0.gif) 拼写

(mistake-type c2) ![<graphic>](img/ch2_0.gif) 拼写

($mistake-type c2) ![<graphic>](img/ch2_0.gif) *violation*`

### 第 11.3 节。标准条件类型

**syntax**: `&serious`

**procedure**: `(make-serious-condition)`

**returns:** 一个类型为 `&serious` 的条件

**procedure**: `(serious-condition? *obj*)`

**returns:** 如果 `*obj*` 是类型为 `&serious` 的条件，则返回 `#t`，否则返回 `#f`

**libraries:** `(rnrs conditions)`, `(rnrs)`

这种类型的条件指示了严重性质的情况，如果不被捕获，通常会导致程序执行的终止。这种类型的条件通常出现为更具体的子类型之一`&error`或`&violation`。这种条件类型可能定义如下。

`(define-condition-type &serious &condition`

make-serious-condition serious-condition?)`

**syntax**: `&violation`

**procedure**: `(make-violation)`

**returns:** 类型为`&violation`的条件

**procedure**: `(violation? *obj*)`

**returns:** 如果`*obj*`是类型为`&violation`的条件，则返回`#t`，否则返回`#f`。

**libraries:** `(rnrs conditions)`, `(rnrs)`

这种类型的条件指示程序违反了某些要求，通常是由于程序中的错误导致的。这种条件类型可能定义如下。

`(define-condition-type &violation &serious`

make-violation violation?)`

**syntax**: `&assertion`

**procedure**: `(make-assertion-violation)`

**returns:** 类型为`&assertion`的条件

**procedure**: `(assertion-violation? *obj*)`

**returns:** 如果`*obj*`是类型为`&assertion`的条件，则返回`#t`，否则返回`#f`。

**libraries:** `(rnrs conditions)`, `(rnrs)`

这种条件类型指示程序在向过程传递错误数量或类型的参数时发生了特定的违规。这种条件类型可能定义如下。

`(define-condition-type &assertion &violation`

make-assertion-violation assertion-violation?)`

**syntax**: `&error`

**procedure**: `(make-error)`

**returns:** 类型为`&error`的条件

**procedure**: `(error? *obj*)`

**returns:** 如果`*obj*`是类型为`&error`的条件，则返回`#t`，否则返回`#f`。

**libraries:** `(rnrs conditions)`, `(rnrs)`

这种类型的条件指示程序与其操作环境的交互发生了错误，例如尝试打开文件失败。它不用于描述程序检测到错误的情况。这种条件类型可能定义如下。

`(define-condition-type &error &serious`

make-error error?)`

**syntax**: `&warning`

**procedure**: `(make-warning)`

**returns:** 类型为`&warning`的条件

**procedure**: `(warning? *obj*)`

**returns:** 如果`*obj*`是类型为`&warning`的条件，则返回`#t`，否则返回`#f`。

**libraries:** `(rnrs conditions)`, `(rnrs)`

警告条件指示了不会阻止程序继续执行的情况，但在某些情况下，可能会在以后的某个时间点导致更严重的问题。例如，编译器可能使用这种类型的条件来指示它已经处理了对具有错误参数数量的标准过程的调用；除非在以后的某个时间点实际评估该调用，否则这不会成为一个严重问题。这种条件类型可能定义如下。

`(define-condition-type &warning &condition`

make-warning warning?)`

**syntax**: `&message`

**procedure**: `(make-message-condition *message*)`

**returns:** 类型为 `&message` 的条件

**procedure**: `(message-condition? *obj*)`

**returns:** 如果 `*obj*` 是类型为 `&message` 的条件，则返回 `#t`，否则返回 `#f`

**procedure**: `(condition-message *condition*)`

**returns:** `*condition*` 的 `message` 字段的内容

**libraries:** `(rnrs conditions)`, `(rnrs)`

这种类型的条件通常与 `&warning` 条件或 `&serious` 条件子类型之一一起包含，以提供异常情况的更具体描述。构造函数的 `*message*` 参数可以是任何 Scheme 值，但通常是一个字符串。这种条件类型可能定义如下。

`(define-condition-type &message &condition

make-message-condition message-condition?

(message condition-message))`

**syntax**: `&irritants`

**procedure**: `(make-irritants-condition *irritants*)`

**returns:** 类型为 `&irritants` 的条件

**procedure**: `(irritants-condition? *obj*)`

**returns:** 如果 `*obj*` 是类型为 `&irritants` 的条件，则返回 `#t`，否则返回 `#f`

**procedure**: `(condition-irritants *condition*)`

**returns:** `*condition*` 的 `irritants` 字段的内容

**libraries:** `(rnrs conditions)`, `(rnrs)`

这种类型的条件通常与 `&message` 条件一起包含，以提供有关可能导致或实质上涉及异常情况的 Scheme 值的信息。例如，如果一个过程接收到错误类型的参数，它可能引发一个异常，其中包含一个断言条件、一个命名该过程的 who 条件、一个说明接收到错误类型参数的 message 条件，以及一个列出参数的 irritants 条件。构造函数的 `*irritants*` 参数应该是一个列表。这种条件类型可能定义如下。

`(define-condition-type &irritants &condition

make-irritants-condition irritants-condition?

(irritants condition-irritants))`

**syntax**: `&who`

**procedure**: `(make-who-condition *who*)`

**returns:** 类型为 `&who` 的条件

**procedure**: `(who-condition? *obj*)`

**returns:** 如果 `*obj*` 是类型为 `&who` 的条件，则返回 `#t`，否则返回 `#f`

**procedure**: `(condition-who *condition*)`

**returns:** `*condition*` 的 `who` 字段的内容

**libraries:** `(rnrs conditions)`, `(rnrs)`

这种类型的条件经常与 `&message` 条件一起包含，以识别检测到错误的语法形式或过程。构造函数的 `*who*` 参数应该是一个符号或字符串。这种条件类型可能定义如下。

`(define-condition-type &who &condition

make-who-condition who-condition?

(who condition-who))

**syntax**: `&non-continuable`

**procedure**: `(make-non-continuable-violation)`

**returns:** 类型为 `&non-continuable` 的条件

**procedure**: `(non-continuable-violation? *obj*)`

**returns:** 如果 `*obj*` 是类型为 `&non-continuable` 的条件，则返回 `#t`，否则返回 `#f`

**libraries:** `(rnrs conditions)`, `(rnrs)`

此类型条件表示发生了不可继续的违规行为。如果当前异常处理程序返回，`raise`会引发此类型的异常。此条件类型可能定义如下。

`(define-condition-type &non-continuable &violation

make-non-continuable-violation

non-continuable-violation?)`

**syntax**: `&implementation-restriction`

**procedure**: `(make-implementation-restriction-violation)`

**returns:** 返回`&implementation-restriction`类型的条件

**procedure**: `(implementation-restriction-violation? *obj*)`

**returns:** 如果`*obj*`是`&implementation-restriction`类型的条件，则返回`#t`，否则返回`#f`

**libraries:** `(rnrs conditions)`, `(rnrs)`

实现限制条件表示程序尝试超出实现的某些限制，例如当 fixnum 加法操作的值导致数字超出实现的 fixnum 范围时。通常不表示实现的缺陷，而是表示程序尝试做什么与实现支持的内容不匹配。在许多情况下，实现限制由底层硬件决定。此条件类型可能定义如下。

`(define-condition-type &implementation-restriction &violation

make-implementation-restriction-violation

implementation-restriction-violation?)`

**syntax**: `&lexical`

**procedure**: `(make-lexical-violation)`

**returns:** 返回`&lexical`类型的条件

**procedure**: `(lexical-violation? *obj*)`

**returns:** 如果`*obj*`是`&lexical`类型的条件，则返回`#t`，否则返回`#f`

**libraries:** `(rnrs conditions)`, `(rnrs)`

此类型条件表示在解析 Scheme 程序或数据时发生了词法错误，例如括号不匹配或在数字常量中出现无效字符。此条件类型可能定义如下。

`(define-condition-type &lexical &violation

make-lexical-violation lexical-violation?)`

**syntax**: `&syntax`

**procedure**: `(make-syntax-violation *form* *subform*)`

**returns:** 返回`&syntax`类型的条件

**procedure**: `(syntax-violation? *obj*)`

**returns:** 如果`*obj*`是`&syntax`类型的条件，则返回`#t`，否则返回`#f`

**procedure**: `(syntax-violation-form *condition*)`

**returns:** 返回`*condition*`的`form`字段的内容

**procedure**: `(syntax-violation-subform *condition*)`

**returns:** 返回`*condition*`的`subform`字段的内容

**libraries:** `(rnrs conditions)`, `(rnrs)`

此类型的条件指示在解析 Scheme 程序时发生了语法错误。在大多数实现中，语法错误由宏展开器检测到。`make-syntax-violation`的每个`*form*`和`*subform*`参数应该是语法对象（第 8.3 节）或数据，前者表示包含的形式，后者表示具体的子形式。例如，如果在`lambda`表达式中发现重复的形式参数，则`*form*`可能是`lambda`表达式，`*subform*`可能是重复的参数。如果不需要标识子形式，则`*subform*`应为`#f`。此条件类型可能定义如下。

`(define-condition-type &syntax &violation`

`make-syntax-violation syntax-violation?`

(表单 `syntax-violation-form`)

(子形式 `syntax-violation-subform))`

**语法：** `&undefined`

**过程：** `(make-undefined-violation)`

**返回：** 一个类型为`&undefined`的条件

**过程：** `(undefined-violation? *obj*)`

**返回：** 如果`*obj*`是类型为`&undefined`的条件，则返回`#t`，否则返回`#f`

**库：** `(rnrs conditions)`，`(rnrs)`

未定义条件表示尝试引用未绑定变量。此条件类型可能定义如下。

`(define-condition-type &undefined &violation`

`make-undefined-violation undefined-violation?)`

接下来的几种条件类型描述了在输入或输出操作以某种方式失败时发生的条件。

**语法：** `&i/o`

**过程：** `(make-i/o-error)`

**返回：** 一个类型为`&i/o`的条件

**过程：** `(i/o-error? *obj*)`

**返回：** 如果`*obj*`是类型为`&i/o`的条件，则返回`#t`，否则返回`#f`

**库：** `(rnrs io ports)`，`(rnrs io simple)`，`(rnrs files)`，`(rnrs)`

类型为`&i/o`的条件表示发生了某种输入/输出错误。此类型的条件通常作为下面描述的更具体的子类型之一发生。此条件类型可能定义如下。

`(define-condition-type &i/o &error`

`make-i/o-error i/o-error?)`

**语法：** `&i/o-read`

**过程：** `(make-i/o-read-error)`

**返回：** 一个类型为`&i/o-read`的条件

**过程：** `(i/o-read-error? *obj*)`

**返回：** 如果`*obj*`是类型为`&i/o-read`的条件，则返回`#t`，否则返回`#f`

**库：** `(rnrs io ports)`，`(rnrs io simple)`，`(rnrs files)`，`(rnrs)`

此类型的条件表示在从端口读取时发生了错误。此条件类型可能定义如下。

`(define-condition-type &i/o-read &i/o`

`make-i/o-read-error i/o-read-error?)`

**语法：** `&i/o-write`

**过程：** `(make-i/o-write-error)`

**返回：** 一个类型为`&i/o-write`的条件

**过程：** `(i/o-write-error? *obj*)`

**返回：** 如果`*obj*`是类型为`&i/o-write`的条件，则返回`#t`，否则返回`#f`

**库：** `(rnrs io ports)`，`(rnrs io simple)`，`(rnrs files)`，`(rnrs)`

此条件类型指示在向端口写入时发生错误。此条件类型可能定义如下。

`(define-condition-type &i/o-write &i/o

make-i/o-write-error i/o-write-error?)`

**语法**：`&i/o-invalid-position`

**过程**：`(make-i/o-invalid-position-error *position*)`

**返回**：类型为`&i/o-invalid-position`的条件

**过程**：`(i/o-invalid-position-error? *obj*)`

**返回**：如果`*obj*`是类型为`&i/o-invalid-position`的条件，则返回`#t`，否则返回`#f`

**过程**：`(i/o-error-position *condition*)`

**返回**：`*condition*`的`position`字段的内容

**库**：`(rnrs io ports)`，`(rnrs io simple)`，`(rnrs files)`，`(rnrs)`

此条件类型指示尝试将端口位置设置为底层文件或其他对象范围之外的位置。构造函数的`*position*`参数应为无效位置。此条件类型可能定义如下。

`(define-condition-type &i/o-invalid-position &i/o

make-i/o-invalid-position-error

i/o-invalid-position-error?

(position i/o-error-position))`

**语法**：`&i/o-filename`

**过程**：`(make-i/o-filename-error *filename*)`

**返回**：类型为`&i/o-filename`的条件

**过程**：`(i/o-filename-error? *obj*)`

**返回**：如果`*obj*`是类型为`&i/o-filename`的条件，则返回`#t`，否则返回`#f`

**过程**：`(i/o-error-filename *condition*)`

**返回**：`*condition*`的`filename`字段的内容

**库**：`(rnrs io ports)`，`(rnrs io simple)`，`(rnrs files)`，`(rnrs)`

此条件类型指示在操作文件时发生的输入/输出错误。构造函数的`*filename*`参数应为文件名。此条件类型可能定义如下。

`(define-condition-type &i/o-filename &i/o

make-i/o-filename-error i/o-filename-error?

(filename i/o-error-filename))`

**语法**：`&i/o-file-protection`

**过程**：`(make-i/o-file-protection-error *filename*)`

**返回**：类型为`&i/o-file-protection`的条件

**过程**：`(i/o-file-protection-error? *obj*)`

**返回**：如果`*obj*`是类型为`&i/o-file-protection`的条件，则返回`#t`，否则返回`#f`

**库**：`(rnrs io ports)`，`(rnrs io simple)`，`(rnrs files)`，`(rnrs)`

此类型的条件指示尝试对程序没有适当权限的文件执行某些输入/输出操作。此条件类型可能定义如下。

`(define-condition-type &i/o-file-protection &i/o-filename

make-i/o-file-protection-error

i/o-file-protection-error?)`

**语法**：`&i/o-file-is-read-only`

**过程**：`(make-i/o-file-is-read-only-error *filename*)`

**返回**：类型为`&i/o-file-is-read-only`的条件

**过程**：`(i/o-file-is-read-only-error? *obj*)`

**返回**：如果`*obj*`是类型为`&i/o-file-is-read-only`的条件，则返回`#t`，否则返回`#f`

**库**：`(rnrs io ports)`，`(rnrs io simple)`，`(rnrs files)`，`(rnrs)`

此类型的条件指示试图将只读文件视为可写文件的尝试。此条件类型可能定义如下。

`(define-condition-type &i/o-file-is-read-only &i/o-file-protection

make-i/o-file-is-read-only-error

i/o-file-is-read-only-error?)`

**语法**：`&i/o-file-already-exists`

**过程**：`(make-i/o-file-already-exists-error *filename*)`

**返回**：类型为`&i/o-file-already-exists`的条���

**过程**：`(i/o-file-already-exists-error? *obj*)`

**返回**：如果`*obj*`是类型为`&i/o-file-already-exists`的条件，则返回`#t`，否则返回`#f`

**库**：`(rnrs io ports)`，`(rnrs io simple)`，`(rnrs files)`，`(rnrs)`

此类型的条件指示文件操作失败的情况，因为文件已经存在，例如，尝试打开现有文件进行输出而没有`no-fail`文件选项。此条件类型可能定义如下。

`(define-condition-type &i/o-file-already-exists &i/o-filename

make-i/o-file-already-exists-error

i/o-file-already-exists-error?)`

**语法**：`&i/o-file-does-not-exist`

**过程**：`(make-i/o-file-does-not-exist-error *filename*)`

**返回**：类型为`&i/o-file-does-not-exist`的条件

**过程**：`(i/o-file-does-not-exist-error? *obj*)`

**返回**：如果`*obj*`是类型为`&i/o-file-does-not-exist`的条件，则返回`#t`，否则返回`#f`

**库**：`(rnrs io ports)`，`(rnrs io simple)`，`(rnrs files)`，`(rnrs)`

此类型的条件指示文件操作失败的情况，因为文件不存在，例如，尝试仅打开不存在的文件进行输入。此条件类型可能定义如下。

`(define-condition-type &i/o-file-does-not-exist &i/o-filename

创建-i/o-文件不存在错误

i/o-file-does-not-exist-error?)`

**语法**：`&i/o-port`

**过程**：`(make-i/o-port-error *pobj*)`

**返回**：类型为`&i/o-port`的条件

**过程**：`(i/o-port-error? *obj*)`

**返回**：如果`*obj*`是类型为`&i/o-port`的条件，则返回`#t`，否则返回`#f`

**过程**：`(i/o-error-port *condition*)`

**返回**：`*condition*`的`pobj`字段的内容

**库**：`(rnrs io ports)`，`(rnrs io simple)`，`(rnrs files)`，`(rnrs)`

此类型的条件通常与其他`&i/o`子类型的条件一起包含，以指示异常情况中涉及的端口（如果涉及端口）。构造函数的`*pobj*`参数应为端口。此条件类型可能定义如下。

`(define-condition-type &i/o-port &i/o

make-i/o-port-error i/o-port-error?

(pobj i/o-error-port))

**语法**：`&i/o-decoding`

**过程**：`(make-i/o-decoding-error *pobj*)`

**返回**：类型为`&i/o-decoding`的条件

**过程**：`(i/o-decoding-error? *obj*)`

**返回**：如果`*obj*`是类型为`&i/o-decoding`的条件，则返回`#t`，否则返回`#f`

**库**：`(rnrs io ports)`，`(rnrs)`

此类型的条件指示在将字节转码为字符期间发生了解码错误。构造函数的`*pobj*`参数应该是涉及的端口（如果有的话）。端口应该定位在无效编码之后。此条件类型可能定义如下。

`(define-condition-type &i/o-decoding &i/o-port

make-i/o-decoding-error i/o-decoding-error?)`

**syntax**: `&i/o-encoding`

**procedure**: `(make-i/o-encoding-error *pobj* *cobj*)`

**returns:** 类型为`&i/o-encoding`的条件

**procedure**: `(i/o-encoding-error? *obj*)`

**returns:** 如果`*obj*`是类型为`&i/o-encoding`的条件，则返回`#t`，否则返回`#f`

**procedure**: `(i/o-encoding-error-char *condition*)`

**returns:** `*condition*`的`cobj`字段的内容

**libraries:** `(rnrs io ports)`, `(rnrs)`

此类型的条件指示在将字符转码为字节期间发生了编码错误。构造函数的`*pobj*`参数应该是涉及的端口（如果有的话），`*cobj*`参数应该是编码失败的字符。此条件类型可能定义如下。

`(define-condition-type &i/o-encoding &i/o-port

make-i/o-encoding-error i/o-encoding-error?

(cobj i/o-encoding-error-char))`

最后两种条件类型描述了当实现需要生成 NaN 或无穷大但没有这些值的表示时发生的条件。

**syntax**: `&no-infinities`

**procedure**: `(make-no-infinities-violation)`

**returns:** 类型为`&no-infinities`的条件

**procedure**: `(no-infinities-violation? *obj*)`

**returns:** 如果`*obj*`是类型为`&no-infinities`的条件，则返回`#t`，否则返回`#f`

**libraries:** `(rnrs arithmetic flonums)`, `(rnrs)`

此条件指示实现没有无穷大的表示。此条件类型可能定义如下。

`(define-condition-type &no-infinities &implementation-restriction

make-no-infinities-violation

no-infinities-violation?)`

**syntax**: `&no-nans`

**procedure**: `(make-no-nans-violation)`

**returns:** 类型为`&no-nans`的条件

**procedure**: `(no-nans-violation? *obj*)`

**returns:** 如果`*obj*`是类型为`&no-nans`的条件，则返回`#t`，否则返回`#f`

**libraries:** `(rnrs arithmetic flonums)`, `(rnrs)`

此条件指示实现没有 NaN 的表示。此条件类型可能定义如下。

`(define-condition-type &no-nans &implementation-restriction

make-no-nans-violation no-nans-violation?)`
