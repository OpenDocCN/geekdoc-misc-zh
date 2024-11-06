# 第十章。库和顶层程序

*库*和*顶层程序*是修订⁶报告中定义的语言中的可移植代码的基本单位。顶层程序可以从一个或多个库中导入，而库可以从其他库中导入。

库的命名采用括号语法，括号内包含一系列标识符，可选地跟随版本号；版本号本身是一个括号形式，括号内包含一系列表示为非负整数的子版本。因此，例如，`(a)`，`(a b)`，`(a b ())`和`(a b (1 2 3))`都是有效的库名称。实现通常将名称序列视为路径，通过该路径可以找到库的源代码或目标代码，可能根据主机文件系统中某些标准位置进行定位。

标准库机制的一个实现可在*http://www.cs.indiana.edu/syntax-case/*上找到可移植的`syntax-case`实现。

### 第 10.1 节。标准库

修订⁶报告[24]描述了一个基本库

`  (rnrs base (6))`

定义了语言中最常用的功能。一个单独的标准库文档[26]描述了下面列出的库。

`  (rnrs arithmetic bitwise (6))

(rnrs arithmetic fixnums (6))

(rnrs arithmetic flonums (6))

(rnrs bytevectors (6))

(rnrs conditions (6))

(rnrs control (6))

(rnrs enums (6))

(rnrs eval (6))

(rnrs exceptions (6))

(rnrs files (6))

(rnrs hashtables (6))

(rnrs io ports (6))

(rnrs io simple (6))

(rnrs lists (6))

(rnrs mutable-pairs (6))

(rnrs mutable-strings (6))

(rnrs programs (6))

(rnrs r5rs (6))

(rnrs records procedural (6))

(rnrs records syntactic (6))

(rnrs records inspection (6))

(rnrs sorting (6))

(rnrs syntax-case (6))

(rnrs unicode (6))`

标准库文档中还描述了另一个库，即一个复合库

`  (rnrs (6))`

该库导出了所有`(rnrs base (6))`绑定以及上述其他库的绑定，但不包括`(rnrs eval (6))`，`(rnrs mutable-pairs (6))`，`(rnrs mutable-strings (6))`和`(rnrs r5rs (6))`。

尽管这些库的版本都是`(6)`，但对它们的引用可以并且在大多数情况下应该省略版本，例如，复合库应该简单地被引用为`(rnrs)`。

### 第 10.2 节。定义新库

新库使用具有以下语法的`library`形式定义。

`(library *library-name*

(export *export-spec* ...)

(import *import-spec* ...)

*library-body*)`

`*library-name*`指定了库的名称和可能的版本，由另一个库或顶层程序的`import`形式识别。它还作为一种路径，实现在需要加载库时通过某种特定于实现的过程定位库。`*library-name*`具有以下两种形式之一：

`(*标识符* *标识符* ...)

(*标识符* *标识符* ... *版本*)`

其中 `*版本*` 具有以下形式：

`(*子版本* ...)`

每个 `*子版本*` 代表一个确切的非负整数。一个没有 `*版本*` 的库名称被视为具有空 `*版本*` `()` 的库名称。例如，`(list-tools setops)` 和 `(list-tools setops ())` 是等效的，指定了一个没有版本的库名称，而 `(list-tools setops (1 2))` 指定了一个带版本的库名称，可以将其视为 `(list-tools setops)` 库的版本 1.2。

`export` 子形式命名了导出项，以及可选地指定它们在库外应该被知道的名称。每个 `*导出规范*` 采用以下两种形式之一：

`*标识符*

(重命名 (*内部名称* *导出名称*) ...)`

其中每个 `*内部名称*` 和 `*导出名称*` 都是标识符。第一种形式命名了一个单一的导出项 `*标识符*`，其导出名称与其内部名称相同。第二种形式命名了一组导出项，每个导出项的导出名称都明确给出，可能与其内部名称不同。

`import` 子形式命名了新库依赖的其他库，可能还指定要导入的标识符集以及它们在新库中应该被知道的名称。它还可以指定实现需要这些信息时应该何时使绑定可用。每个 `*导入规范*` 采用以下两种形式之一：

`*导入集*

(对于 *导入集* *导入级别* ...)`

其中 `*导入级别*` 是以下之一：

`运行

扩展

(meta *级别*)`

和 `*级别*` 代表一个确切的整数。

`for` 语法声明了导入的绑定何时可能被导入库使用，因此实现必须使绑定可用。 `run` 和 `(meta 0)` 是等效的，指定了从库中导入的绑定可能被导入库的运行时表达式（`define` 右侧表达式和初始化表达式）引用。 `expand` 和 `(meta 1)` 是等效的，指定了从库中导入的绑定可能被导入库的转换器表达式（`define-syntax`、`let-syntax` 或 `letrec-syntax` 右侧表达式）引用。 `(meta 2)` 指定了从库中导入的绑定可能被引用导入库的转换器表达式中的转换器表达式，以此类推，适用于更高的元级别。在某些情况下，当一个转换器扩展为另一个关键字绑定的转换器时，可能还需要指定负元级别。

一个库导出可能具有非零的 *export* 元级别，此时有效的导入级别是由 `for` 指定的级别和导出级别的总和。除了 `(rnrs base)` 和 `(rnrs)` 之外的每个标准库的导出级别为零。对于 `(rnrs base)`，所有导出的元级别为零，除了 `syntax-rules`、`identifier-syntax` 和它们的辅助关键字 `_`、`...` 和 `set!`。`set!` 的导出级别为零和一，而其他的导出级别为一。`(rnrs)` 库的所有导出级别为零和一。

对于程序员来说，很难指定允许库或顶层程序正确编译或运行的导入级别。此外，通常无法在需要时使库的绑定可用，而在不需要时也使其可用。例如，无法说在扩展库 B 时需要库 A 的运行时绑定，而不在扩展导入 B 的代码时也使 A 的运行时绑定可用。使绑定可用涉及执行绑定的右侧代码以及可能执行初始化表达式，因此无法准确指定何时需要绑定可能会给程序增加编译和运行时开销。

因此，实现允许忽略导出级别和 `*import-set*` 上的 `for` 包装器，并在扩展导入库或顶层程序时自动确定导入库的绑定何时必须可用，这取决于导入库的导出实际出现的位置。在使用这种实现时，永远不需要使用 `for` 包装器，即所有 `*import-spec*` 都可以是 `*import-set*`。然而，如果代码打算与不自动确定库的绑定何时必须可用的系统一起使用，则在导入库的绑定在正确时间不可用时必须使用 `for`。

一个 `*import-set*` 可以采用以下形式：

`*library-spec*

(只有 *import-set* *identifier* ...)

(除了 *import-set* *identifier* ...)

(prefix *import-set* *prefix*)

(rename *import-set* (*import-name* *internal-name*) ...)

其中`*前缀*`、`*导入名称*`和`*内部名称*`是标识符。一个`*导入集*`是从库中导入的标识符的递归规范，可能还包括这些标识符在导入库内部应该使用的名称。在递归结构的底部必须有一个`*库规范*`，它标识一个库并从该库中导入所有标识符。一个`only`包装器将封闭的`*导入集*`的导入标识符限制为列出的标识符，一个`except`包装器将封闭的`*导入集*`的导入标识符限制为未列出的标识符，一个`prefix`包装器为封闭的`*导入集*`的每个导入标识符添加前缀，一个`rename`包装器为封闭的`*导入集*`的选定标识符指定内部名称，同时保持其他导入的名称不变。因此，例如，`*导入集*`

`(prefix

(only

(rename (list-tools setops) (difference diff))

union

diff)

set:)`

仅从`(list-tools setops)`库中导入`union`和`difference`，将`difference`重命名为`diff`，而保留`union`不变，并为这两个名称添加前缀`set:`，以便在导入库内部使用这两个导入的名称为`set:union`和`set:diff`。

一个`*库规范*`可以采用以下形式之一：

`*库引用*

(library *库引用*)`

其中一个`*库引用*`可以是以下两种形式之一：

`(*标识符* *标识符* ...)

(*标识符* *标识符* ... *版本引用*)`

将`*库引用*`放在`library`包装器中是必要的，当`*库引用*`的第一个标识符是`for`、`library`、`only`、`except`、`prefix`或`rename`时，以区别于由这些关键字标识的`*导入规范*`或`*导入集*`。

一个`*版本引用*`标识库的特定版本或一组可能的版本。一个`*版本引用*`可以采用以下形式之一：

`(*子版本引用[1]* ... *子版本引用[n]*)

(and *版本引用* ...)

(or *版本引用* ...)

(not *版本引用*)`

第一种形式的`*版本引用*`匹配具有至少*n*个元素的`*版本*`，如果每个`*子版本引用*`匹配`*版本*`的相应`*子版本*`。`and` `*版本引用*`形式匹配`*版本*`，如果它的每个`*版本引用*`子形式都匹配`*版本*`。`or` `*版本引用*`形式匹配`*版本*`，如果它的任何`*版本引用*`子形式都匹配`*版本*`。`not` `*版本引用*`形式匹配`*版本*`，如果它的`*版本引用*`子形式不匹配`*版本*`。

一个`*子版本引用*`可以采用以下形式之一：

`*子版本*

(>= *子版本*)

(<= *子版本*)

(和 *子版本引用* ...)

(or *子版本引用* ...)

(not *子版本引用*)`

第一种形式的`*subversion-reference*`与`*subversion*`匹配，如果它与之相同。`>=` `*subversion-reference*`与`*version*`的`*subversion*`匹配，如果`*version*`的`*subversion*`大于或等于出现在`>=`形式中的`*subversion*`。类似地，`<=` `*subversion-reference*`与`*version*`的`*subversion*`匹配，如果`*version*`的`*subversion*`小于或等于出现在`>=`形式中的`*subversion*`。`and` `*subversion-reference*`形式与`*version*`的`*subversion*`匹配，如果它的每个`*subversion-reference*`子形式都与`*version*`的`*subversion*`匹配。`or` `*subversion-reference*`与`*version*`的`*subversion*`匹配，如果它的任何`*subversion-reference*`子形式与`*version*`的`*subversion*`匹配。`not` `*subversion-reference*`与`*version*`的`*subversion*`匹配，如果它的`*subversion-reference*`子形式不与`*version*`的`*subversion*`匹配。

例如，如果有两个版本的库可用，一个版本为`(1 2)`，另一个版本为`(1 3 1)`，则版本引用`()`和`(1)`都匹配，`(1 2)`匹配第一个但不匹配第二个，`(1 3)`匹配第二个但不匹配第一个，`(1 (>= 2))`匹配两个，`(and (1 (>= 3)) (not (1 3 1)))`两者都不匹配。

当库引用标识多个可用库时，某些实现相关的方式会选择其中一个可用库。

库和顶层程序不应直接或间接指定导入具有相同名称但不同版本的两个库。为了避免诸如不兼容类型和复制状态之类的问题，鼓励实现，尽管不是必需的，禁止程序导入同一库的两个版本。

`*library-body*`包含导出标识符的定义，不打算导出的标识符的定义以及初始化表达式。它由一系列（可能为空）的定义后跟一系列（可能为空）的初始化表达式组成。当`begin`、`let-syntax`或`letrec-syntax`形式在第一个表达式之前出现在库体中时，它们会被插入到体中。任何体形式都可以由语法扩展生成，包括定义，刚才提到的插入形式或初始化表达式。库体的扩展方式与`lambda`或其他体（第 292 页）相同，并且它扩展为等效的`letrec*`形式，以便库体中的定义和初始化形式从左到右进行评估。

每个库的`export`表单中列出的导出必须从另一个库中导入或在`*library-body*`中定义，无论哪种情况都要使用内部名称而不是导出名称，如果两者不同。

导入到库中或在库内定义的每个标识符必须有且仅有一个绑定。如果导入到库中，则不能在库体中定义，如果在库体中定义，则必须只定义一次。如果从两个库中导入，它必须在两种情况下具有相同的绑定，这只有在绑定源自两个库之一并被另一个重新导出，或者绑定源自第三个库并被两个库都重新导出时才会发生。

在库内定义但未被库导出的标识符在出现在库外的代码中是不可见的。然而，在库内定义的语法扩展可能会扩展为对这种标识符的引用，以便扩展的代码确实包含对该标识符的引用；这被称为*间接导出*。

一个库的导出变量在库内部和外部都是*不可变*的，无论它们是显式还是隐式导出的。如果一个显式导出的变量出现在导出库内或外的`set!`表达式的左侧，这是语法违例。如果由库定义的任何其他变量出现在`set!`表达式的左侧并且是间接导出的，也是语法违例。

库是按需加载的，其中包含的代码由实现根据库之间的导入关系确定的。一个库的变换器表达式（库体的`define-syntax`形式右侧的表达式）可能在不同的时间被评估，与库体表达式（库体的`define`形式右侧的表达式，加上初始化表达式）不同。至少，当（如果不是在之前）在扩展另一个库或顶层程序时发现对库导出的关键字之一的引用时，必须评估库的变换器表达式，而当（如果不是在之前）评估库导出的变量之一的引用时，必须评估库的体表达式，这可能发生在运行使用库的程序时，或者在扩展另一个库或顶层程序时，如果引用是由在扩展过程中调用的变换器评估的。实现可以在扩展其他库的过程中随意评估库的变换器和体表达式多次。特别地，如果实际上不需要，它可以零次评估表达式，恰好一次，或者对扩展的每个元级别评估一次。通常，库的变换器或体表达式的评估涉及外部可见的副作用是一个坏主意，例如弹出一个窗口，因为这些副作用发生的时间是不确定的。只影响库初始化的局部效果，例如创建库使用的表，通常是可以接受的。

示例见第 10.4 节。

### 第 10.3 节。顶层程序

顶层程序本身不是一个语法形式，而是一组通常仅由文件边界限定的形式。顶层程序可以被视为没有`library`包装器、库名称和导出形式的库形式。另一个区别是定义和表达式可以在顶层程序的主体中交错，但不能在库的主体中交错。因此，顶层程序的语法就是一个`import`形式，后面跟着一系列的定义和表达式：

`(导入 *import-spec* ...)

*定义或表达式*

...`

出现在一个或多个定义之前的顶层程序主体中的表达式被视为出现在一个虚拟变量的定义的右侧，该虚拟变量在程序中任何地方都不可见。

**过程**: `(command-line)`

**返回:** 代表命令行参数的字符串列表

**库:** `(rnrs programs)`, `(rnrs)`

这个过程可以在顶层程序中使用，以获取传递给程序的命令行参数列表。

**过程**: `(exit)`

**过程**: `(exit *obj*)`

**返回:** 不返回

**库:** `(rnrs programs)`, `(rnrs)`

这个过程可以用于从顶层程序退出到操作系统。如果没有给出`*obj*`，则返回给操作系统的退出值应指示正常退出。如果`*obj*`为 false，则返回给操作系统的退出值应指示异常退出。否则，`*obj*`将根据操作系统适当地转换为退出值。

### 第 10.4 节。示例

下面的示例演示了`library`语法的几个特点。它定义了“(list-tools setops)”库的“版本 1”，导出了两个关键字和几个变量。该库导入了`(rnrs base)`库，它提供了除了`member`过程之外的所有需要的内容，该过程从`(rnrs lists)`导入。该库导出的大多数变量都绑定到过程，这是典型的。

语法扩展`set`扩展为对变量`list->set`的引用，而`member?`类似地扩展为对变量`$member?`的引用。虽然`list->set`被明确导出，但`$member?`没有。这使得`$member?`成为一种间接导出。过程`u-d-help`没有被明确导出，而且由于导出的语法扩展都没有扩展为对`u-d-help`的引用，它也不是间接导出的。这意味着它可以被赋值，但在这个例子中没有被赋值。

`(library (list-tools setops (1))

(导出 set empty-set empty-set? list->set set->list

union intersection difference member?)

(导入(rnrs base) (only (rnrs lists) member))

定义语法`set`

(syntax-rules ()

[(_ x ...)

(list->set (list x ...))]))

(define empty-set '())

(define empty-set? null?)

(define list->set

(lambda (ls)

(条件

[(null? ls) '()]

[(member (car ls) (cdr ls)) (list->set (cdr ls))]

[else (cons (car ls) (list->set (cdr ls)))])))

(define set->list (lambda (set) set))

(define u-d-help

(lambda (s1 s2 ans)

(let f ([s1 s1])

(cond

[(null? s1) ans]

[(member? (car s1) s2) (f (cdr s1))]

[else (cons (car s1) (f (cdr s1)))]))))

(define union

(lambda (s1 s2)

(u-d-help s1 s2 s2)))

(define intersection

(lambda (s1 s2)

(cond

[(null? s1) '()]

[(member? (car s1) s2)

(cons (car s1) (intersection (cdr s1) s2))]

[else (intersection (cdr s1) s2)])))

(define difference

(lambda (s1 s2)

(u-d-help s1 s2 '())))

(define member-help?

(lambda (x s)

(and (member x s) #t)))

(define-syntax member?

(syntax-rules ()

[(_ elt-expr set-expr)

(let ([x elt-expr] [s set-expr])

(and (not (null? s)) (member-help? x s)))])))`

下一个库 `(more-setops)` 定义了一些额外的集合操作，以 `(list-tools setops)` 操作为基础。库参考中没有版本信息 `(list-tools setops)`；这相当于一个空版本引用，可以匹配任何版本。`quoted-set` 关键字很有趣，因为其转换器在扩展时引用了 `(list-tools setops)` 中的 `list->set`。因此，如果另一个库或顶层程序导入了 `(more-setops)` 并引用了 `quoted-set`，那么在扩展其他库或顶层程序时，将不得不评估 `(list-tools setops)` 库的运行时表达式。另一方面，当 `(more-setops)` 库自身被扩展时，无需评估 `(list-tools setops)` 库的运行时表达式。

`(library (more-setops)

(export quoted-set set-cons set-remove)

(import (list-tools setops) (rnrs base) (rnrs syntax-case))

(define-syntax quoted-set

(lambda (x)

(syntax-case x ()

[(k elt ...)

#`(quote

#,(datum->syntax #'k

(list->set

(syntax->datum #'(elt ...)))))])))

(define set-cons

(lambda (opt optset)

(union (set opt) optset)))

(define set-remove

(lambda (opt optset)

(difference optset (set opt)))))`

如果实现不会自动推断何时需要进行绑定，那么 `(more-setops)` 库中的 `import` 表单必须修改，以指定它导入的绑定在哪些元级别上使用，通过 `for` `*import-spec*` 语法如下所示：

`(import

(for (list-tools setops) expand run)

(for (rnrs base) expand run)

(for (rnrs syntax-case) expand))`

要完成示例，下面是一个简短的顶层程序，演示了 `(list-tools setops)` 和 `(more-setops)` 导出的几个操作。

`(import (list-tools setops) (more-setops) (rnrs))

(define-syntax pr

(syntax-rules ()

[(_ obj)

(begin

(write 'obj)

(display " ;=> ")

(write obj)

(newline))]))

(define get-set1

(lambda ()

(quoted-set a b c d)))

(define set1 (get-set1))

(define set2 (quoted-set a c e))

(pr (list set1 set2))

(pr (eq? (get-set1) (get-set1)))

(pr (eq? (get-set1) (set 'a 'b 'c 'd)))

(pr (union set1 set2))

(pr (intersection set1 set2))

(pr (difference set1 set2))

(pr (set-cons 'a set2))

(pr (set-cons 'b set2))

(pr (set-remove 'a set2))`

运行这个程序应该打印出什么留给读者作为一个练习。

附加的库和顶层程序示例在第十二章中给出。
