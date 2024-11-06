# 第九章。记录

本章描述了程序员可以定义新数据类型或*记录类型*的方式，每种类型都与所有其他类型不同。记录类型确定该类型的每个实例具有的字段数量和名称。记录通过`define-record-type`形式或`make-record-type-descriptor`过程定义。

### 第 9.1 节。定义记录

`define-record-type`形式定义了一个记录类型，以及该类型的记录构造函数，仅对该类型的记录返回 true 的类型谓词，每个字段的访问过程以及每个可变字段的赋值过程。例如，以下定义

`(define-record-type point (fields x y))`

创建了一个具有两个字段`x`和`y`的`point`记录类型，并定义了以下过程：

| `(make-point *x* *y*)` | 构造函数 |
| --- | --- |
| `(point? *obj*)` | 谓词 |
| `(point-x *p*)` | `x`字段的访问器 |
| `(point-y *p*)` | `y`字段的访问器 |

有了这个定义，我们可以使用这些过程来创建和操作`point`类型的记录，如下所示。

`(define p (make-point 36 -17))

(point? p) ![<graphic>](img/ch2_0.gif) #t

(point? '(cons 36 -17)) ![<graphic>](img/ch2_0.gif) #f

(point-x p) ![<graphic>](img/ch2_0.gif) 36

(point-y p) ![<graphic>](img/ch2_0.gif) -17`

默认情况下，字段是不可变的，但可以声明为可变。在下面的`point`的替代定义中，`x`字段是可变的，而`y`保持不可变。

`(define-record-type point (fields (mutable x) y))`

在这种情况下，`define-record-type`除了上述其他产品外还定义了`x`字段的修改器。

| `(point-x-set! *p* *x*)` | `x`字段的修改器 |
| --- | --- |

修改器可用于更改`x`字段的内容。

`(define p (make-point 36 -17))

(point-x-set! p (- (point-x p) 12))

(point-x p) ![<graphic>](img/ch2_0.gif) 24`

为了明确起见，可以显式声明字段为不可变；下面的`point`定义等同于上面的第二个定义。

`(define-record-type point (fields (mutable x) (immutable y)))`

`define-record-type`定义的过程名称遵循上面示例中的常规命名约定，默认情况下，但如果需要，程序员可以覆盖默认值。使用以下`point`的定义，构造函数是`mkpoint`，谓词是`ispoint?`，`x`和`y`的访问器是`x-val`和`y-val`。`x`的修改器是`set-x-val!`。

`(define-record-type (point mkpoint ispoint?)

(fields (mutable x x-val set-x-val!)

(immutable y y-val)))`

默认情况下，每次评估记录定义时都会创建一个新类型，如下例所示。

`(define (f p)

(define-record-type point (fields x y))

(if (eq? p 'make) (make-point 3 4) (point? p)))

(f (f 'make)) ![<graphic>](img/ch2_0.gif) #f`

对 `f` 的第一次（内部）调用返回一个点 `*p*`，它被传递给第二次（外部）调用的 `f`，该调用将 `point?` 应用于 `*p*`。这个 `point?` 寻找由第二次调用创建的类型的点，而 `*p*` 是由第一次调用创建的类型的点。因此 `point?` 返回 `#f`。

这种默认的 *生成* 行为可以通过在记录定义中包含 `nongenerative` 子句来覆盖。

`(define (f p)

(define-record-type point (fields x y) (nongenerative))

(if (eq? p 'make) (make-point 3 4) (point? p)))

(define p (f 'make))

(f p) ![<graphic>](img/ch2_0.gif) #t`

以这种方式创建的记录类型仍然与程序的不同部分中出现的定义创建的记录类型不同，即使这些定义在语法上是相同的：

`(define (f)

(define-record-type point (fields x y) (nongenerative))

(make-point 3 4))

(define (g p)

(define-record-type point (fields x y) (nongenerative))

(point? p))

(g (f)) ![<graphic>](img/ch2_0.gif) #f`

即使这样也可以通过在 `nongenerative` 子句中包含 uid（唯一标识符）来覆盖：

`(define (f)

(define-record-type point (fields x y)

(nongenerative really-the-same-point))

(make-point 3 4))

(define (g p)

(define-record-type point (fields x y)

(nongenerative really-the-same-point))

(point? p))

(g (f)) ![<graphic>](img/ch2_0.gif) #t`

uid 可以是任何标识符，但程序员被鼓励从 RFC 4122 UUID 命名空间[20]中选择 uid，可能以记录类型名称作为前缀。

可以通过使用 `parent` 子句声明现有记录类型的名称，将记录类型定义为现有“父”类型的子类型。如果指定了父类型，则新的“子”记录类型继承父记录的字段，并且将子类型的每个实例视为父类型的实例，因此可以在子类型的实例上使用父类型的访问器和修改��。

`(define-record-type point (fields x y))

(define-record-type cpoint (parent point) (fields color))`

子类型具有父类型的所有字段，以及子类型定义中声明的附加字段。这反映在 `cpoint` 的构造函数中，现在需要三个参数，父参数后跟子参数。

`(define cp (make-cpoint 3 4 'red))`

子类型的记录被视为父类型的记录，但父类型的记录不是新类型的记录。

`(point? (make-cpoint 3 4 'red)) ![<graphic>](img/ch2_0.gif) #t

(cpoint? (make-point 3 4)) ![<graphic>](img/ch2_0.gif) #f`

为 `cpoint` 只创建一个新的访问器，用于新字段 `color`。可以使用父类型的现有访问器和修改器来访问和修改子类型的父字段。

`(define cp (make-cpoint 3 4 'red))

(point-x cp) ![<graphic>](img/ch2_0.gif) 3

(point-y cp) ![<graphic>](img/ch2_0.gif) 4

(cpoint-color cp) ![<graphic>](img/ch2_0.gif) red`

正如迄今为止给出的示例所示，`define-record-type`定义的默认构造函数接受与记录具有的字段数量相同的参数，包括父字段，父的父字段等。 程序员可以覆盖默认值，并通过`protocol`子句指定新类型的构造函数的参数以及它如何确定构造记录字段的初始值。 以下定义创建一个具有三个字段的`point`记录：`x`，`y`和`d`，其中`d`表示与原点的位移。 构造函数仍然只接受两个参数，`x`和`y`值，并将`d`初始化为`x`和`y`的平方和的平方根。

`(define-record-type point

(fields x y d)

(protocol

(lambda (new)

(lambda (x y)

(new x y (sqrt (+ (* x x) (* y y))))))))

(define p (make-point 3 4))

(point-x p) ![<graphic>](img/ch2_0.gif) 3

(point-y p) ![<graphic>](img/ch2_0.gif) 4

(point-d p) ![<graphic>](img/ch2_0.gif) 5`

`protocol`子句内表达式的过程值接收一个原始构造函数`*new*`作为参数，并返回一个最终构造函数`*c*`。 `*c*`允许做的事情基本上没有限制，但如果它返回，应该返回调用`*new*`的结果。 在这样做之前，它可以修改新的记录实例（如果记录类型具有可变字段），将其注册到某些外部处理程序，打印消息等。 在这种情况下，`*c*`接受两个参数，`*x*`和`*y*`，并将`*new*`应用于`*x*`，`*y*`以及基于`*x*`和`*y*`计算原始位移的结果。

如果指定了父记录，则构造协议变得更加复杂。 以下`cpoint`的定义假定`point`已如上所示定义。

`(define-record-type cpoint

(parent point)

(fields color)

(protocol

(lambda (pargs->new)

(lambda (c x y)

((pargs->new x y) c)))))

(define cp (make-cpoint 'red 3 4))

(point-x cp) ![<graphic>](img/ch2_0.gif) 3

(point-y cp) ![<graphic>](img/ch2_0.gif) 4

(point-d cp) ![<graphic>](img/ch2_0.gif) 5

(cpoint-color cp) ![<graphic>](img/ch2_0.gif) red`

由于存在父子句，`protocol`子句内表达式的过程值接收一个过程`*pargs*->*new*`，当应用于父参数时，返回一个`*new*`过程。 当传递子字段的值时，`*new*`过程返回将父协议应用于其自身适当`*new*`过程的结果。 在这种情况下，`*pargs*->*new*`传递子构造函数的第二和第三参数的值（`*x*`和`*y*`值），并且生成的`*new*`过程传递子构造函数的第一个参数的值（颜色）。 因此，此示例中提供的协议有效地颠倒了父参数在子参数之前的正常顺序，同时安排传递父协议所需的参数。

默认协议等同于

`(lambda (new) new)`

对于没有父记录类型的记录类型，而对于具有父记录类型的记录类型，默认协议等同于以下内容

`(lambda (pargs->new)`

(lambda (*x[1]* ... *x[n]* *y[1]* ... *y[m]*)

((pargs->new *x[1]* ... *x[n]*) *y[1]* ... *y[m]*)))`

其中 `*n*` 是父（包括祖父等）字段的数量，而 `*m*` 是子字段的数量。

使用 `protocol` 条款可使子记录定义免受对父记录类型的某些更改的影响。可以修改父定义以添加或删除字段，甚至添加、删除或更改父级，但只要父协议不改变，子协议和构造函数就不需要更改。

`define-record-type` 的更多细节和选项在下面的正式描述中给出。

**语法：**`(define-record-type *record-name* *clause* ...)`

**语法：**`(define-record-type (*record-name* *constructor* *pred*) *clause* ...)`

**库：**`(rnrs records syntactic)`，`(rnrs)`

一个 `define-record-type` 表单，或 *记录定义*，是一个定义，并且可以出现在其他定义可能出现的任何地方。它定义了一个由 `*record-name*` 标识的记录类型，以及记录类型的谓词、构造函数、访问者和变异者。如果记录定义采用上述第一种形式，则构造函数和谓词的名称源自于 `*record-name*`：构造函数为 `make-*record-name*`，谓词为 `*record-name*?`。如果记录定义采用上述第二种形式，则构造函数的名称为 `*constructor*`，谓词的名称为 `*pred*`。记录定义定义的所有名称在记录定义出现的地方作用域。

记录定义的 `*clause* ...` 决定了记录类型的字段及其访问者和变异者的名称；其父类型（如果有）；其构造协议；它是否是非生成的，如果是，则其 uid 是否已指定；它是否被密封；以及它是否是不透明的。下面描述了每个条款的语法和影响。

没有一个条款是必需的；因此，最简单的记录定义是

`(define-record-type *record-name*)`

定义了一个新的，生成的，非密封的，非不透明的记录类型，没有父级和字段，以及一个无参数的构造函数和一个谓词。

每种类型的条款最多只能出现一次在条款集合中，并且如果出现了 `parent` 条款，则不能出现 `parent-rtd` 条款。出现的条款可以以任何顺序出现。

**字段条款。** `(fields *field-spec* ...)` 条款声明了记录类型的字段。每个 `*field-spec*` 必须采取以下形式之一：

`*field-name*

(不可变的 *field-name*)

(可变的 *field-name*)

(不可变的 *field-name* *accessor-name*)

(可变的 *field-name* *accessor-name* *mutator-name*)`

其中`*field-name*`、`*accessor-name*`和`*mutator-name*`是标识符。第一种形式，`*field-name*`，等价于`(immutable *field-name*)`。声明为不可变的字段的值不能被更改，并且不会为其创建修改器。对于前三种形式，访问器的名称是`*rname*-*fname*`，其中`*rname*`是记录名称，`*fname*`是字段名称。对于第三种形式，访问器的名称是`*rname*-*fname*-set!`。第四和第五种形式明确声明了访问器和修改器的名称。

如果没有出现`fields`子句或列表`*field-spec* ...`为空，则记录类型没有字段（除非有父字段）。

**父项子句。**  一个`(parent *parent-name*)`子句声明父记录类型；`*parent-name*`必须是先前通过`define-record-type`定义的非封闭记录类型的名称。记录类型的实例也被视为其父记录类型的实例，并且除了通过`fields`子句声明的字段外，还具有其父记录类型的所有字段。

**非生成子句。**  一个`nongenerative`子句可能有两种形式：

`(nongenerative)`

`(nongenerative *uid*)`

其中`*uid*`是一个符号。第一种形式等价于第二种形式，在宏展开时由实现生成的 uid。当评估具有非生成子句的`define-record-type`形式时，只有当 uid 不是现有记录类型的 uid 时，才会创建新类型。

如果它是现有记录类型的 uid，则父项、字段名称、封闭属性和不透明属性必须匹配如下。

+   如果指定了父项，则现有记录类型必须具有相同的父 rtd（通过`eqv?`）。如果未指定父项，则现有记录类型不得具有父项。

+   必须提供相同数量的字段，具有相同的名称和相同的顺序，并且每个字段的可变性必须相同。

+   如果出现`(sealed #t)`子句，则现有记录类型必须是封闭的。否则，现有记录类型必须不是封闭的。

+   如果出现`(opaque #t)`子句，则现有记录类型必须是不透明的。否则，仅当指定了不透明父类型时，现有记录类型才必须是不透明的。

如果满足这些约束条件，则不会创建新的记录类型，并且记录类型定义的其他产品（构造函数、谓词、访问器和修改器）将对现有类型的记录进行操作。如果不满足这些约束条件，实现可能会将其视为语法错误，或者可能会引发具有条件类型`&assertion`的运行时异常。

对于`nongenerative`子句的第一种形式，只有在相同的定义被多次执行时（例如，如果它出现在被多次调用的过程的体中），生成的 uid 才可以是现有记录类型的 uid。

如果`*uid*`不是现有记录类型的 uid，或者没有出现`nongenerative`子句，则会创建一个新的记录类型。

**Protocol 子句。**  一个`(protocol *expression*)`确定生成的构造函数用于构造记录类型实例的协议。它必须求值为一个过程，这个过程应该是记录类型的适当协议，如第 326 页所述。

**Sealed 子句。**  一个形式为`(sealed #t)`的`sealed`子句声明记录类型是*封闭*的。这意味着它不能被扩展，即不能用作另一个记录定义或`make-record-type-descriptor`调用的父记录。如果没有`sealed`子句或者形式为`(sealed #f)`之一，记录类型不是封闭的。

**Opaque 子句。**  一个形式为`(opaque #t)`的`opaque`子句声明记录类型是*不透明*的。不透明记录类型的实例不被`record?`谓词或更重要的是`record-rtd`提取过程视为记录，这两者都在第 9.3 节中描述。因此，如果没有访问`record-name`、访问器或修改器的代码，就无法访问或修改不透明记录类型的任何字段。如果记录类型的父记录是不透明的，则记录类型也是不透明的。如果没有`opaque`子句或者形式为`(opaque #f)`之一，且父记录（如果有）不是不透明的，则记录类型不是不透明的。

**Parent-rtd 子句。**  一个`(parent-rtd *parent-rtd* *parent-rcd*)`子句是指定父记录类型以及父记录构造函数描述符的`parent`子句的替代方案。当父 rtd 和 rcd 是通过调用`make-record-type-descriptor`和`make-record-constructor-descriptor`获得时，这是非常有用的。

`*parent-rtd*`必须求值为一个 rtd 或`#f`。如果`*parent-rtd*`求值为`#f`，`*parent-rcd*`也必须求值为`#f`。否则，`*parent-rcd*`必须求值为一个 rcd 或`#f`。如果`*parent-rcd*`求值为一个 rcd，则它必须封装一个与`*parent-rtd*`的值等效（通过`eqv?`）的 rtd。如果`*parent-rcd*`的值为`#f`，则将其视为具有默认协议的`*parent-rtd*`的 rcd。

`define-record-type`形式设计得通常可以使编译器确定其定义的记录类型的形状，包括所有字段的偏移量。然而，当使用`parent-rtd`子句时，这种保证不成立，因为父 rtd 可能直到运行时才能确定。因此，每当`parent`子句足够时，都应优先使用`parent`子句而不是`parent-rtd`子句。

**语法**：`fields`

**语法**：`mutable`

**语法**：`immutable`

**语法**：`parent`

**语法**：`protocol`

**语法**：`sealed`

**语法**：`opaque`

**语法**：`nongenerative`

**语法**：`parent-rtd`

**库：**`(rnrs records syntactic)`，`(rnrs)`

这些标识符是`define-record-type`的辅助关键字。在不被识别为辅助关键字的上下文中引用这些标识符是语法违例。

### 第 9.2 节。过程接口

过程（`make-record-type-descriptor`）接口也可以用于创建新的记录类型。过程接口比语法接口更灵活，但这种灵活性可能导致程序不够可读和高效，因此程序员应在足够的情况下使用语法接口。

**procedure**: `(make-record-type-descriptor *name* *parent* *uid* *s?* *o?* *fields*)`

**returns:** 一个新的或现有记录类型的记录类型描述符（rtd）

**libraries:** `(rnrs records procedural)`, `(rnrs)`

`*name*`必须是一个符号，`*parent*`必须是`#f`或者非密封记录类型的 rtd，`*uid*`必须是`#f`或者一个符号，`*fields*`必须是一个向量，其中每个元素都是形式为`(mutable *field-name*)`或`(immutable *field-name*)`的两元素列表。字段名称`*field-name* ...`必须是符号，不需要彼此不同。

如果`*uid*`是`#f`或者不是现有记录类型的 uid，则此过程将创建一个新的记录类型，并返回新类型的记录类型描述符（rtd）。该类型具有父类型（页面 325）由`*parent*`描述，如果非假；由`*uid*`指定的 uid，如果非假；以及由`*fields*`指定的字段。如果`*s?*`为非假，则它是密封的（页面 330）。如果`*opaque*`为非假或者父类型（如果指定）是不透明的，则它是不透明的（页面 330）。新记录类型的名称是`*name*`，字段的名称是`*field-name* ...`。

如果`*uid*`为非假并且是现有记录类型的 uid（页面 325），则`*parent*`、`*fields*`、`*s?*`和`*o?*`参数必须与现有记录类型的相应特征匹配。也就是说，`*parent*`必须相同（通过`eqv?`）；字段数量必须相同；字段必须具有相同的名称，按相同顺序排列，并具有相同的可变性；如果现有记录类型是密封的，则`*s?*`必须为假；如果未指定父类型或父类型不是不透明的，则`*o?*`必须为假，如果现有记录类型是不透明的。如果是这种情况，`make-record-type-descriptor`返回现有记录类型的 rtd。否则，将引发带有条件类型`&assertion`的异常。

使用`make-record-type-descriptor`返回的 rtd，程序可以动态生成构造函数、类型谓词、字段访问器和字段修改器。以下代码演示了如何使用过程接口创建一个`point`记录类型和与第 9.1 节中第二个`point`记录定义类似的相关定义，其中有一个可变的`x`字段和一个不可变的`y`字段。

`(define point-rtd (make-record-type-descriptor 'point #f #f #f #f

'#((mutable x) (immutable y))))

(define point-rcd (make-record-constructor-descriptor point-rtd

#f #f))

(define make-point (record-constructor point-rcd))

(define point? (record-predicate point-rtd))

(define point-x (record-accessor point-rtd 0))

(define point-y (record-accessor point-rtd 1))

(define point-x-set! (record-mutator point-rtd 0))`

请参考本节末尾给出的其他示例。

**procedure**: `(record-type-descriptor? *obj*)`

**returns:** 如果`*obj*`是记录类型描述符，则返回`#f`，否则返回`#f`。

**libraries:** `(rnrs records procedural)`, `(rnrs)`

请参考本节末尾给出的示例。

**procedure**: `(make-record-constructor-descriptor *rtd* *parent-rcd* *protocol*)`

**returns:** 记录构造器描述符（rcd）。

**libraries:** `(rnrs records procedural)`, `(rnrs)`

仅 rtd 就足以创建谓词、访问器和变异器。然而，要创建构造器，首先需要为记录类型创建记录构造器描述符（rcd）。rcd 封装了三个信息：为其创建了 rcd 的记录类型的 rtd、父 rcd（如果有）和协议。

`*parent-rcd*`参数必须是一个 rcd 或`#f`。如果它是一个 rcd，则`*rtd*`必须有一个父 rtd，并且父 rtd 必须与`*parent-rcd*`中封装的 rtd 相同。如果`*parent-rcd*`为 false，则`*rtd*`没有父级或者假定父级为具有默认协议的 rcd。

`*protocol*`参数必须是一个过程或`#f`。如果是`#f`，则假定默认协议。协议在第 326 页讨论（records.html#page:protocols）。

请参考本节末尾给出的示例。

**syntax**: `(record-type-descriptor *record-name*)`

**returns:** 返回由`record-name`标识的记录类型的 rtd。

**syntax**: `(record-constructor-descriptor *record-name*)`

**returns:** 返回由`record-name`标识的记录类型的 rcd。

**libraries:** `(rnrs records syntactic)`, `(rnrs)`

每个记录定义在幕后创建了一个定义的记录类型的 rtd 和 rcd。这些过程允许获取和使用 rtd 和 rcd，就像获取和使用任何其他 rtd 或 rcd 一样。`*record-name*`必须是先前通过`define-record-type`定义的记录的名称。

**procedure**: `(record-constructor *rcd*)`

**returns:** 封装在`*rcd*`中的记录类型的记录构造器。

**libraries:** `(rnrs records procedural)`, `(rnrs)`

记录构造器的行为由协议和父 rcd（如果有）也封装在`*rcd*`中来确定。

请参考本节末尾给出的示例。

**procedure**: `(record-predicate *rtd*)`

**returns:** 用于`*rtd*`的谓词。

**libraries:** `(rnrs records procedural)`, `(rnrs)`

此过程返回一个接受一个参数并返回`#t`（如果参数是由`*rtd*`描述的记录类型的实例）的谓词，否则返回`#f`。

查看本节末尾给出的示例。

**过程：** `(record-accessor *rtd* *idx*)`

**返回：** 用于指定`*rtd*`字段的访问器`*idx*`

**库：** `(rnrs records procedural)`, `(rnrs)`

`*idx*`必须是小于`*rtd*`字段数的非负整数，不包括父字段。`*idx*`值为 0 指定了在创建记录类型的`define-record-type`形式或`make-record-type-descriptor`调用中给出的第一个字段，1 指定了第二个字段，依此类推。

子 rtd 不能直接用于创建父字段的访问器。要为父字段创建访问��，必须使用父记录的记录类型描述符。

查看本节末尾给出的示例。

**过程：** `(record-mutator *rtd* *idx*)`

**返回：** 用于指定`*idx*`的`*rtd*`字段的修改器

**库：** `(rnrs records procedural)`, `(rnrs)`

`*idx*`必须是小于`*rtd*`字段数的非负整数，不包括父字段。`*idx*`值为 0 指定了在创建记录类型的`define-record-type`形式或`make-record-type-descriptor`调用中给出的第一个字段，1 指定了第二个字段，依此类推。指定的字段必须是可变的；否则，将引发带有条件类型`&assertion`的异常。

子 rtd 不能直接用于创建父字段的修改器。要为父字段创建修改器，必须使用父记录的记录类型描述符。

以下示例说明了使用本节描述的程序创建父记录和子记录类型、谓词、访问器、修改器和构造器。

`(define rtd/parent

(make-record-type-descriptor 'parent #f #f #f #f

'#((mutable x))))

(record-type-descriptor? rtd/parent) ![<graphic>](img/ch2_0.gif) #t

(define parent? (record-predicate rtd/parent))

(define parent-x (record-accessor rtd/parent 0))

(define set-parent-x! (record-mutator rtd/parent 0))

(define rtd/child

(make-record-type-descriptor 'child rtd/parent #f #f #f

'#((mutable x) (immutable y))))

(define child? (record-predicate rtd/child))

(define child-x (record-accessor rtd/child 0))

(define set-child-x! (record-mutator rtd/child 0))

(define child-y (record-accessor rtd/child 1))

(record-mutator rtd/child 1) ![<graphic>](img/ch2_0.gif) *异常：不可变字段*

(define rcd/parent

(make-record-constructor-descriptor rtd/parent #f

(lambda (new) (lambda (x) (new (* x x))))))

(record-type-descriptor? rcd/parent) ![<graphic>](img/ch2_0.gif) #f

(define make-parent (record-constructor rcd/parent))

(define p (make-parent 10))

(parent? p) ![<graphic>](img/ch2_0.gif) #t

(parent-x p) ![<graphic>](img/ch2_0.gif) 100

(set-parent-x! p 150)

(parent-x p) ![<graphic>](img/ch2_0.gif) 150

(define rcd/child

(make-record-constructor-descriptor rtd/child rcd/parent

(lambda (pargs->new)

(lambda (x y)

((pargs->new x) (+ x 5) y)))))

(define make-child (record-constructor rcd/child))

(define c (make-child 10 'cc))

(parent? c) ![<graphic>](img/ch2_0.gif) #t

(child? c) ![<graphic>](img/ch2_0.gif) #t

(child? p) ![<graphic>](img/ch2_0.gif) #f

(parent-x c) ![<graphic>](img/ch2_0.gif) 100

(child-x c) ![<graphic>](img/ch2_0.gif) 15

(child-y c) ![<graphic>](img/ch2_0.gif) cc

(child-x p) ![<graphic>](img/ch2_0.gif) *exception: invalid argument type*`

### Section 9.3\. Inspection

本节描述了有关记录类型描述符（rtds）询问问题或提取信息的各种过程。它还描述了`record-rtd`过程，通过该过程可以提取非不透明记录实例的 rtd，从而允许检查实例的记录类型，并通过从 rtd 生成的记录访问器和修改器检查或修改记录本身。这是一个强大的功能，允许编写可移植的记录打印机和检查器。

无法从不透明记录类型的实例中提取记录类型描述符；这是区分不透明记录类型和非不透明记录类型的特征。

**procedure**: `(record-type-name *rtd*)`

**returns:** the name associated with `*rtd*`

**libraries:** `(rnrs records inspection)`, `(rnrs)`

`(define record->name

(lambda (x)

(and (record? x) (record-type-name (record-rtd x)))))

(define-record-type dim (fields w l h))

(record->name (make-dim 10 15 6)) ![<graphic>](img/ch2_0.gif) dim

(define-record-type dim (fields w l h) (opaque #t))

(record->name (make-dim 10 15 6)) ![<graphic>](img/ch2_0.gif) #f`

**procedure**: `(record-type-parent *rtd*)`

**returns:** the parent of `*rtd*`, or `#f` if it has no parent

**libraries:** `(rnrs records inspection)`, `(rnrs)`

`(define-record-type point (fields x y))

(define-record-type cpoint (parent point) (fields color))

(record-type-parent (record-type-descriptor point)) ![<graphic>](img/ch2_0.gif) #f

(record-type-parent (record-type-descriptor cpoint)) ![<graphic>](img/ch2_0.gif) #<rtd>`

**procedure**: `(record-type-uid *rtd*)`

**returns:** the uid of `*rtd*`, or `#f` if it has no uid

**libraries:** `(rnrs records inspection)`, `(rnrs)`

创建没有程序员提供的 uid 的记录类型是否实际上有 uid 取决于实现，因此这个过程永远不能保证返回`#f`。

`(define-record-type point (fields x y))

(define-record-type cpoint

(父点)

(fields color)

(nongenerative e40cc926-8cf4-4559-a47c-cac636630314))

(record-type-uid (record-type-descriptor point)) ![<graphic>](img/ch2_0.gif) *unspecified*

(record-type-uid (record-type-descriptor cpoint)) ![<graphic>](img/ch2_0.gif)

e40cc926-8cf4-4559-a47c-cac636630314`

**procedure**: `(record-type-generative? *rtd*)`

**returns:** `#t` if the record type described by `*rtd*` is generative, `#f` otherwise

**procedure**: `(record-type-sealed? *rtd*)`

**returns:** `#t` if the record type described by `*rtd*` is sealed, `#f` otherwise

**procedure**: `(record-type-opaque? *rtd*)`

**returns:** `#t` if the record type described by `*rtd*` is opaque, `#f` otherwise

**libraries:** `(rnrs records inspection)`, `(rnrs)`

`(define-record-type table

(fields keys vals)

(opaque #t))

(define rtd (record-type-descriptor table))

(record-type-generative? rtd) ![<graphic>](img/ch2_0.gif) #t

(record-type-sealed? rtd) ![<graphic>](img/ch2_0.gif) #f

(record-type-opaque? rtd) ![<graphic>](img/ch2_0.gif) #t

(define-record-type cache-table

(parent table)

(fields key val)

(nongenerative))

(define rtd (record-type-descriptor cache-table))

(record-type-generative? rtd) ![<graphic>](img/ch2_0.gif) #f

(record-type-sealed? rtd) ![<graphic>](img/ch2_0.gif) #f

(record-type-opaque? rtd) ![<graphic>](img/ch2_0.gif) #t`

**过程：** `(record-type-field-names *rtd*)`

**返回：** 包含由`*rtd*`描述的类型的字段名称的向量

**库：** `(rnrs records inspection)`，`(rnrs)`

此过程返回的向量是不可变的：修改它对`*rtd*`的影响是未指定的。向量不包括父字段名称。向量中名称的顺序与在创建记录类型的`define-record-type`表单或`make-record-type-descriptor`调用中指定字段的顺序相同。

`(define-record-type point (fields x y))

(define-record-type cpoint (parent point) (fields color))

(record-type-field-names

(record-type-descriptor point)) ![<graphic>](img/ch2_0.gif) #(x y)

(record-type-field-names

(record-type-descriptor cpoint)) ![<graphic>](img/ch2_0.gif) #(color)`

**过程：** `(record-field-mutable?��*rtd* *idx*)`

**返回：** 如果`*rtd*`的指定字段是可变的，则返回`#t`，否则返回`#f`

**库：** `(rnrs records inspection)`，`(rnrs)`

`*idx*`必须是小于`*rtd*`字段数量的非负整数，不包括父字段。`*idx*`值为 0 指定了在创建记录类型的`define-record-type`表单或`make-record-type-descriptor`调用中给出的第一个字段，1 指定了第二个字段，依此类推。

`(define-record-type point (fields (mutable x) (mutable y)))

(define-record-type cpoint (parent point) (fields color))

(record-field-mutable? (record-type-descriptor point) 0) ![<graphic>](img/ch2_0.gif) #t

(record-field-mutable? (record-type-descriptor cpoint) 0) ![<graphic>](img/ch2_0.gif) #f`

**过程：** `(record? *obj*)`

**返回：** 如果`*obj*`是非透明记录实例，则返回`#t`，否则返回`#f`

**库：** `(rnrs records inspection)`，`(rnrs)`

当传递一个不透明记录类型的实例时，`record?`返回`#f`。虽然不透明记录类型的实例本质上是一个记录，但不透明性的目的是隐藏所有表示信息，使程序的部分不应访问信息，包括对象是否是记录。此外，此谓词的主要目的是允许程序检查是否可以通过下面描述的`record-rtd`过程从参数中获取 rtd。

`(define-record-type statement (fields str))

(define q (make-statement "He's dead, Jim"))

(statement? q) ![<graphic>](img/ch2_0.gif) #t

(record? q) ![<graphic>](img/ch2_0.gif) #t

(define-record-type opaque-statement (fields str) (opaque #t))

(define q (make-opaque-statement "He's moved on, Jim"))

(opaque-statement? q) ![<graphic>](img/ch2_0.gif) #t

(record? q) ![<graphic>](img/ch2_0.gif) #f`

**procedure**: `(record-rtd *record*)`

**returns:** `*record*`的记录类型描述符（rtd）

**libraries:** `(rnrs records inspection)`, `(rnrs)`

参数必须是非不透明记录类型的实例。与本节和第 9.2 节中描述的其他一些过程结合使用，`record-rtd`允许即使检查器不知道实例类型，也能检查或变异记录实例。这一功能由下面的过程`print-fields`示例所说明，该过程接受一个记录参数，并写入记录的每个字段的名称和值。

`(define print-fields

(lambda (r)

除非`(record? r)`，否则

(assertion-violation 'print-fields "not a record" r))

(let loop ([rtd (record-rtd r)])

(let ([prtd (record-type-parent rtd)])

当`prtd`时，`(when prtd (loop prtd)))

(let* ([v (record-type-field-names rtd)]

[n (vector-length v)])

(do ([i 0 (+ i 1)])

((= i n))

(write (vector-ref v i))

(display "=")

(write ((record-accessor rtd i) r))

(newline))))))`

使用熟悉的`point`和`cpoint`的定义：

`(define-record-type point (fields x y))

`(define-record-type cpoint (parent point) (fields color))`

表达式`(print-fields (make-cpoint -3 7 'blue))`显示以下三行。

`x=-3

y=7

color=blue`
