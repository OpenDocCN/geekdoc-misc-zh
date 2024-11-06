# Coq 中的基本功能编程

```

```

# 介绍

    功能编程风格建立在简单的日常

    数学直觉：如果一个过程或方法没有副作用

    效果，那么（忽略效率）我们需要理解的一切

    它如何将输入映射到输出-也就是说，我们可以认为

    将其视为计算数学

    function。这是“functional”一词的一个意义

    “功能编程”。程序之间的直接联系

    和简单的数学对象支持形式上的正确性

    证明和对程序行为进行合理的非正式推理。

    功能编程是“functional”的另一种意义

    它强调函数（或方法）的使用

    *第一类*值-即可以传递的值

    传递给其他函数的参数，作为结果返回，包含在

    数据结构等。意识到函数可以

    被视为数据会产生许多有用和强大的

    编程习语。

    功能语言的其他常见特性包括*代数数据类型*和*模式匹配*，这使得

    构建和操作丰富的数据结构，以及复杂的

    *多态类型系统*支持抽象和代码重用。

    Coq 提供了所有这些功能。

    本章的前半部分介绍了最基本的

    Coq 的功能编程语言的元素，称为

    *Gallina*。后半部分介绍了一些基本的*tactics*

    可用于证明 Coq 程序的属性。

```

# Enumerated Types

    One notable aspect of Coq is that its set of built-in
    features is *extremely* small.  For example, instead of providing
    the usual palette of atomic data types (booleans, integers,
    strings, etc.), Coq offers a powerful mechanism for defining new
    data types from scratch, with all these familiar types as
    instances.

    Naturally, the Coq distribution comes preloaded with an extensive
    standard library providing definitions of booleans, numbers, and
    many common data structures like lists and hash tables.  But there
    is nothing magic or primitive about these library definitions.  To
    illustrate this, we will explicitly recapitulate all the
    definitions we need in this course, rather than just getting them
    implicitly from the library.

```

## 一周的日子

    看看这个定义机制是如何工作的，让我们从

    一个非常简单的例子。以下声明告诉 Coq

    我们正在定义一组新的数据值-一个*类型*。

```
Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

```

    类型称为 day，其成员是 monday，

    星期二等。定义的第二行和后续行

    可以阅读“星期一是一天，星期二是一天，等等”

    定义了 day 之后，我们可以编写操作 day 的函数

    天。

```
Definition next_weekday (d:day) : day :=
  match d with
  | monday    ⇒ tuesday
  | tuesday   ⇒ wednesday
  | wednesday ⇒ thursday
  | thursday  ⇒ friday
  | friday    ⇒ monday
  | saturday  ⇒ monday
  | sunday    ⇒ monday
  end.

```

    需要注意的一点是这个函数的参数和返回类型

    这个函数是显式声明的。像大多数功能

    编程语言，Coq 通常可以为这些类型找到

    当它们没有明确给出时，它可以自行推断类型-但我们通常会包括它们以便阅读

    更容易。

    定义了一个函数后，我们应该检查它在

    一些例子。实际上有三种不同的方法来做到这一点

    在 Coq 中。首先，我们可以使用 Compute 命令来评估一个

    包含 next_weekday 的复合表达式。

```
Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

```

    （我们在注释中展示 Coq 的响应，但是，如果你有一个

    电脑方便的话，现在是启动

    Coq 解释器在您喜欢的 IDE��-无论是 CoqIde 还是 Proof

    一般-并尝试自己做这个。加载这个文件，Basics.v，

    从书中的 Coq 源代码中，找到上面的例子，提交给

    Coq，并观察结果。）

    其次，我们可以记录我们*期望*结果是什么

    Coq 示例的形式：

```
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

```

    这个声明做了两件事：它使一个

    断言（即周六后的第二个工作日是星期二），

    并且给出了一个可以用来引用它的名称

    之后。做出了断言后，我们还可以要求 Coq 验证

    它，就像这样：

```
Proof. simpl. reflexivity. Qed.

```

    现在不重要（我们会回来

    他们稍微），但基本上可以理解为“断言

    我们刚刚做出的可以通过观察证明，两边都是

    相等性在一些简化后会得到相同的结果。”

    第三，我们可以要求 Coq 从我们的定义中*提取*

    在其他一些更传统的编程

    语言（OCaml、Scheme 或 Haskell）与高性能

    编译器。这个设施非常有趣，因为它给了我们

    从用 Gallina 编写的经过验证的算法到

    高效的机器代码。（当然，我们信任

    OCaml/Haskell/Scheme 编译器的正确性，以及 Coq 的

    提取设施本身，但这仍然是一个重要的进步

    从今天大多数软件开发的方式。）实际上，这是

    Coq 开发的主要用途之一。我们会回来

    对这个主题在后面的章节中。

```

## Homework Submission Guidelines

    If you are using Software Foundations in a course, your instructor
    may use automatic scripts to help grade your homework assignments.
    In order for these scripts to work correctly (so that you get full
    credit for your work!), please be careful to follow these rules:

*   The grading scripts work by extracting marked regions of the .v files that you submit. It is therefore important that you do not alter the "markup" that delimits exercises: the Exercise header, the name of the exercise, the "empty square bracket" marker at the end, etc. Please leave this markup exactly as you find it.

*   Do not delete exercises. If you skip an exercise (e.g., because it is marked Optional, or because you can't solve it), it is OK to leave a partial proof in your .v file, but in this case please make sure it ends with Admitted (not, for example Abort).

```

## 布尔值

    以类似的方式，我们可以定义标准类型 bool 的

    布尔值，具有成员 true 和 false。

```
Inductive bool : Type :=
  | true : bool
  | false : bool.

```

    虽然我们为了

    从头开始构建一切，当然，Coq

    提供布尔值的默认实现，以及

    大量有用的函数和引理。（看一看

    Coq.Init.Datatypes，如果您感兴趣

    感兴趣。）在可能的情况下，我们会为我们自己的定义命名

    和定理，使它们与

    标准库。

    布尔值的函数可以以与

    上面：

```
Definition negb (b:bool) : bool :=
  match b with
  | true ⇒ false
  | false ⇒ true
  end.

Definition andb (b[1]:bool) (b[2]:bool) : bool :=
  match b[1] with
  | true ⇒ b[2]
  | false ⇒ false
  end.

Definition orb (b[1]:bool) (b[2]:bool) : bool :=
  match b[1] with
  | true ⇒ true
  | false ⇒ b[2]
  end.

```

    这两个是 Coq 用于

    多参数函数定义。相应的

    多参数应用语法由以下示例说明

    “单元测试”，构成一个完整的规范 — 一个真理

    表格 — 对于 orb 函数：

```
Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity. Qed.

```

    我们还可以为布尔值引入一些熟悉的语法

    我们刚刚定义的操作。Infix 命令定义了一个新的

    对现有定义进行符号表示。

```
Infix "&&" := andb.
Infix "||" := orb.

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

```

    *关于符号的说明*：在 .v 文件中，我们使用方括号

    用注释来界定 Coq 代码片段；这种约定，

    也被 coqdoc 文档工具使用，使它们在视觉上保持一致

    与周围文本分开。在 html 版本中

    文件，这些文本片段以不同的字体出现。

    命令 Admitted 可以用作

    不完整的证明。我们将在练习中使用它，以指示

    我们留给你的部分 — 即，你的工作是替换

    具有真正证明的 Admitteds。

#### 练习：1 星（nandb）

    删除“Admitted.” 并完成以下定义

    函数；然后确保下面的示例断言可以

    每个都可以由 Coq 验证。（删除“Admitted.” 并填写每个

    证明，遵循上面 orb 测试的模型。）该函数

    如果其输入的一个或两个是真，则应返回 true

    假。

```
Definition nandb (b[1]:bool) (b[2]:bool) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_nandb1:               (nandb true false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb2:               (nandb false false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb3:               (nandb false true) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb4:               (nandb true true) = false.
(* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：1 星（andb3）

    对于下面的 andb3 函数做同样的事情。 这个函数应该

    当其所有输入都为 true 时返回 true，否则返回 false

    否则。

```
Definition andb3 (b[1]:bool) (b[2]:bool) (b[3]:bool) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_andb31:                 (andb3 true true true) = true.
(* FILL IN HERE *) Admitted.
Example test_andb32:                 (andb3 false true true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb33:                 (andb3 true false true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb34:                 (andb3 true true false) = false.
(* FILL IN HERE *) Admitted.

```

    ☐

```

## Function Types

    Every expression in Coq has a type, describing what sort of
    thing it computes. The Check command asks Coq to print the type
    of an expression.

```

检查 true.

(* ===> true : bool *)

检查 (negb true).

(* ===> negb true : bool *)

```

    Functions like negb itself are also data values, just like
    true and false.  Their types are called *function types*, and
    they are written with arrows.

```

检查 negb。

(* ===> negb : bool -> bool *)

```

    The type of negb, written bool → bool and pronounced
    "bool arrow bool," can be read, "Given an input of type
    bool, this function produces an output of type bool."
    Similarly, the type of andb, written bool → bool → bool, can
    be read, "Given two inputs, both of type bool, this function
    produces an output of type bool."

```

## 模块

    Coq 提供了一个*模块系统*，以帮助组织大型的

    发展。 在这门课程中，我们不需要大多数的功能

    但是有一个很有用的：如果我们围绕一组声明

    在模块 X 和 End X 标记之间，然后在剩余部分中

    在 End 之后，这些定义被引用为

    名称如 X.foo 而不仅仅是 foo。 我们将使用这个

    功能，引入内部的 nat 类型定义

    模块，以便它不会干扰来自

    标准库（因为它

    带有一点方便的特殊符号）。

```
Module NatPlayground.

```

## 数字

    到目前为止我们已经定义的类型是“列举的

    类型”：它们的定义明确列举了一个有限的集合

    元素。 定义类型的更有趣的方法是给出一个

    一组描述其元素的*归纳规则*。对于

    例如，我们可以定义（一种一元表示的）自然数

    数字如下：

```
Inductive nat : Type :=
  | O : nat
  | S : nat → nat.

```

    这个定义的子句可以被理解为：

+   O 是一个自然数（请注意这是字母“O”，不是数字“0”）。

+   S 是一个“构造函数”，它接受一个自然数并产生另一个自然数 — 即，如果 n 是一个自然数，那么 S n 也是。

    让我们稍微详细地看一下这个。

    每个归纳定义的集合（day、nat、bool 等）都是

    实际上是一组*从*构造函数*构建的*表达式

    像 O、S、true、false、monday 等。 定义

    nat 表示集合 nat 中的表达式如何构建：

+   O 和 S 是构造函数;

+   表达式 O 属于集合 nat；

+   如果 n 是属于集合 nat 的表达式，则 S n 也是属于集合 nat 的表达式；以及

+   用这两种方式形成的表达式是属于集合 nat 的唯一的表达式。

    我们的 day 和

    bool。 （我们用于它们的构造函数的注释是

    与 O 构造函数的类似，指示它们

    不带任何参数。)

    上述条件是归纳的准确含义

    声明。 它们意味着表达式 O、表达式

    S O、表达式 S (S O)、表达式 S (S (S O))，以及

    所有都属于集合 nat，而其他构建的表达式

    来自数据构造函数，如 true、andb true false、S (S false) 和 O (O (O S)) 不会。

    在这里的关键点是到目前为止我们所做的只是

    定义数字的 *表示*：一种书写它们的方式。

    名称 O 和 S 是任意的，在这一点上它们有

    没有特殊的意义 —— 它们只是两种不同的标记，我们

    可以用来写下数字（连同一个规则，规定任何

    nat 将被写成一些 S 标记的字符串，后跟一个

    O）。 如果愿意，我们可以写基本相同的定义

    这样：

```
Inductive nat' : Type :=
  | stop : nat'
  | tick : nat' → nat'.

```

    这些标记的*解释*来自于我们如何使用它们来

    计算。

    我们可以通过编写在上面的函数进行这样的操作

    自然数的表示法，就像我们上面所做的那样

    布尔值和天数——例如，这是前任者

    函数：

```
Definition pred (n : nat) : nat :=
  match n with
    | O ⇒ O
    | S n' ⇒ n'
  end.

```

    可以读取第二个分支：“如果 n 的形式是 S n'

    对于一些 n'，然后返回 n'。”

```
End NatPlayground.

Definition minustwo (n : nat) : nat :=
  match n with
    | O ⇒ O
    | S O ⇒ O
    | S (S n') ⇒ n'
  end.

```

    因为自然数是如此普遍的数据形式，

    Coq 为解析和打印提供了一点内置的魔法

    他们之间：普通的阿拉伯数字可以用作替代

    由构造函数 S 和 O 定义的“一元”表示法。 Coq

    默认情况下以阿拉伯形式打印数字：

```
Check (S (S (S (S O)))).
  (* ===> 4 : nat *)
Compute (minustwo 4).
  (* ===> 2 : nat *)

```

    构造函数 S 的类型为 nat → nat，就像

    函数 minustwo 和 pred：

```
Check S.
Check pred.
Check minustwo.

```

    这些都是可以应用于数字的事物，以产生一个

    数字。 但是，普通的阿拉伯数字可以用作的基本区别

    第一个和其他两个：像前任者和减去两个这样的函数

    附带*计算规则*——例如，pred 的定义

    表示 pred 2 可以简化为 1——而

    S 的定义没有附加此类行为。 虽然它是

    就像一个函数一样，因为它可以应用于一个

    参数，它根本不*做*任何事情！ 这只是一种

    写下数字。（想想标准的阿拉伯数字：这个

    数字 1 不是计算； 它是一块数据。 当我们

    写`111`来表示数字一百十一，我们是

    使用 1，三次，来写下具体的表示

    一个数字。）

    对于大多数针对数字的函数定义，只是模式匹配

    不够：我们还需要递归。 例如，要检查

    一个数字 n 是偶数，我们可能需要递归地检查是否

    n-2 是偶数。 为了编写这样的函数，我们使用关键字

    不动点。

```
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        ⇒ true
  | S O      ⇒ false
  | S (S n') ⇒ evenb n'
  end.

```

    我们可以通过类似的 Fixpoint 声明来定义 oddb，但是这里

    是一个更简单的定义：

```
Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2:    oddb 4 = false.
Proof. simpl. reflexivity. Qed.

```

    （如果您逐步执行这些证明，您会注意到

    简化实际上对目标没有任何影响——所有工作都是

    由反射完成。 我们很快会看到更多关于为什么的内容。）

    当然，我们也可以通过

    递归。

```
Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O ⇒ m
    | S n' ⇒ S (plus n' m)
  end.

```

    现在将三加到两上给了我们五，正如我们所预期的那样。

```
Compute (plus 3 2).

```

    Coq 执行的简化达到这个结论可能会

    可以可视化如下：

```
(*  plus (S (S (S O))) (S (S O)) ==> S (plus (S (S O)) (S (S O)))       by the second clause of the match ==> S (S (plus (S O) (S (S O))))       by the second clause of the match ==> S (S (S (plus O (S (S O)))))       by the second clause of the match ==> S (S (S (S (S O))))       by the first clause of the match *)

```

    作为一种方便的表示法，如果两个或更多个参数有

    相同的类型，它们可以一起写。 在下面

    定义，（n m：nat）意味着与我们写的一样

    （n：nat）（m：nat）。

```
Fixpoint mult (n m : nat) : nat :=
  match n with
    | O ⇒ O
    | S n' ⇒ plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

```

    您可以通过放置逗号同时匹配两个表达式

    之间：

```
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    ⇒ O
  | S _ , O    ⇒ n
  | S n', S m' ⇒ minus n' m'
  end.

```

    第一行中的 _ 是一个*通配符模式*。 在一中写入 _ 是一个

    模式与编写不使用的某个变量相同

    在右侧。 这样可以避免发明一个变量

    名字。

```
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O ⇒ S O
    | S p ⇒ mult base (exp base p)
  end.

```

#### 练习：1 星（阶乘）

    回忆标准数学阶乘函数：

```
       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

```

    将此翻译为 Coq。

```
Fixpoint factorial (n:nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_factorial1:          (factorial 3) = 6.
(* FILL IN HERE *) Admitted.
Example test_factorial2:          (factorial 5) = (mult 10 12).
(* FILL IN HERE *) Admitted.

```

    ☐

    我们可以使数值表达式更容易阅读和

    写入引入*符号*以进行加法，乘法和

    减法。

```
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

```

    （级别，结合性和 nat_scope 注释

    控制这些符号是如何由 Coq 的解析器处理的。该

    细节对我们的目的来说并不重要，但感兴趣的读者

    可以参考可选的“关于符号的更多信息”部分

    本章。）

    请注意，这些不会改变我们已经做出的定义：

    它们只是告诉 Coq 解析器接受 x + y

    而不是将 x + y 和相反的加法器

    以显示加法的加法 x y 为 x + y。

    当我们说 Coq 几乎没有内置任何内容时，我们真的是

    意思是：即使对数字的相等性测试也是用户定义的

    操作！我们现在定义了一个函数 beq_nat，用于测试

    自然数的相等性，产生一个布尔值。 请注意

    使用嵌套匹配（我们也可以同时使用

    匹配，就像我们在减法中所做的一样。）

```
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O ⇒ match m with
         | O ⇒ true
         | S m' ⇒ false
         end
  | S n' ⇒ match m with
            | O ⇒ false
            | S m' ⇒ beq_nat n' m'
            end
  end.

```

    函数 leb 测试其第一个参数是否小于或

等于它的第二个参数，产生一个布尔值。

```
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O ⇒ true
  | S n' ⇒
      match m with
      | O ⇒ false
      | S m' ⇒ leb n' m'
      end
  end.

Example test_leb1:             (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2:             (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3:             (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

```

#### 练习：1 星（blt_nat）

    函数 blt_nat 用于测试自然数的大小，

    产生一个布尔值。 不要制作新的 Fixpoint

    这是将其定义为先前定义的函数。

```
Definition blt_nat (n m : nat) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_blt_nat1:             (blt_nat 2 2) = false.
(* FILL IN HERE *) Admitted.
Example test_blt_nat2:             (blt_nat 2 4) = true.
(* FILL IN HERE *) Admitted.
Example test_blt_nat3:             (blt_nat 4 2) = false.
(* FILL IN HERE *) Admitted.

```

    ☐

```

# Proof by Simplification

    Now that we've defined a few datatypes and functions, let's
    turn to stating and proving properties of their behavior.
    Actually, we've already started doing this: each Example in the
    previous sections makes a precise claim about the behavior of some
    function on some particular inputs.  The proofs of these claims
    were always the same: use simpl to simplify both sides of the
    equation, then use reflexivity to check that both sides contain
    identical values.

    The same sort of "proof by simplification" can be used to prove
    more interesting properties as well.  For example, the fact that
    0 is a "neutral element" for + on the left can be proved just
    by observing that 0 + n reduces to n no matter what n is, a
    fact that can be read directly off the definition of plus.

```

定理 plus_O_n：∀n：nat，0 + n = n。

证明。

引入 n。 简化。 一致性。 QED。

```

    (You may notice that the above statement looks different in
    the .v file in your IDE than it does in the HTML rendition in
    your browser, if you are viewing both. In .v files, we write the
    ∀ universal quantifier using the reserved identifier
    "forall."  When the .v files are converted to HTML, this gets
    transformed into an upside-down-A symbol.)

    This is a good place to mention that reflexivity is a bit
    more powerful than we have admitted. In the examples we have seen,
    the calls to simpl were actually not needed, because
    reflexivity can perform some simplification automatically when
    checking that two sides are equal; simpl was just added so that
    we could see the intermediate state — after simplification but
    before finishing the proof.  Here is a shorter proof of the
    theorem:

```

定理 plus_O_n'：∀n：nat，0 + n = n。

证明。

引入 n。 一致性。 QED。

```

    Moreover, it will be useful later to know that reflexivity
    does somewhat *more* simplification than simpl does — for
    example, it tries "unfolding" defined terms, replacing them with
    their right-hand sides.  The reason for this difference is that,
    if reflexivity succeeds, the whole goal is finished and we don't
    need to look at whatever expanded expressions reflexivity has
    created by all this simplification and unfolding; by contrast,
    simpl is used in situations where we may have to read and
    understand the new goal that it creates, so we would not want it
    blindly expanding definitions and leaving the goal in a messy
    state.

    The form of the theorem we just stated and its proof are almost
    exactly the same as the simpler examples we saw earlier; there are
    just a few differences.

    First, we've used the keyword Theorem instead of Example.
    This difference is purely a matter of style; the keywords
    Example and Theorem (and a few others, including Lemma,
    Fact, and Remark) mean exactly the same thing to Coq.

    Second, we've added the quantifier ∀ n:nat, so that our
    theorem talks about *all* natural numbers n.  Informally, to
    prove theorems of this form, we generally start by saying "Suppose
    n is some number..."  Formally, this is achieved in the proof by
    intros n, which moves n from the quantifier in the goal to a
    *context* of current assumptions.

    The keywords intros, simpl, and reflexivity are examples of
    *tactics*.  A tactic is a command that is used between Proof and
    Qed to guide the process of checking some claim we are making.
    We will see several more tactics in the rest of this chapter and
    yet more in future chapters.

    Other similar theorems can be proved with the same pattern.

```

定理 plus_1_l：∀n:nat，1 + n = S n。

证明。

引入 n。 一致性。 QED。

定理 mult_0_l：∀n:nat，0 * n = 0。

证明。

引入 n。 一致性。 QED。

```

    The _l suffix in the names of these theorems is
    pronounced "on the left." 

    It is worth stepping through these proofs to observe how the
    context and the goal change.  You may want to add calls to simpl
    before reflexivity to see the simplifications that Coq performs
    on the terms before checking that they are equal.

    Although simplification is powerful enough to prove some fairly
    general facts, there are many statements that cannot be handled by
    simplification alone.  For instance, we cannot use it to prove
    that 0 is also a neutral element for + *on the right*.

```

定理 plus_n_O：∀n，n = n + 0。

证明。

引入 n。 简化。 （不做任何事情！）

```

    (Can you explain why this happens?  Step through both proofs
    with Coq and notice how the goal and context change.)

    When stuck in the middle of a proof, we can use the Abort
    command to give up on it for the moment.

```

中止。

```

    The next chapter will introduce *induction*, a powerful
    technique that can be used for proving this goal.  For the moment,
    though, let's look at a few more simple tactics.

```

# 重写证明

    这个定理比我们以前的其他定理更有趣

    看到：

```
Theorem plus_id_example : ∀n m:nat,
  n = m →
  n + n = m + m.

```

    不是对所有数字 n 和 m 做出普遍断言，

    它谈到了一个更专业的性质，仅当 n = m 时才成立。箭头符号发音为“意味着”。

    如前所述，我们需要能够假设我们已经拥有

    数字 n 和 m。 我们还需要假设假设

    n = m。 引入策略将用于移动所有这三个

    从目标到当前上下文中的假设。

    由于 n 和 m 是任意数字，我们不能只是使用

    通过简化来证明这个定理。 相反，我们通过

    观察到，如果我们假设 n = m，那么我们可以替换

    n 与 m 在目标语句中，并获得与

    两边都是相同的表达式。 告诉 Coq 的策略

    执行此替换称为重写。

```
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite → H.
  reflexivity. Qed.

```

    证明的第一行移动了普遍量化的

    变量 n 和 m 到上下文中。 第二个移动了

    假设 n = m 并将其命名为 H。

    第三个告诉 Coq 重写当前目标（n + n = m + m）

    通过用等式假设 H 的左侧替换。

    右侧。

    （重写中的箭头符号与这个函数无关，

    意味着：它告诉 Coq 应用从左到右的重写。

    要从右到左重写，可以使用 rewrite ←。 尝试

    进行这种更改在上面的证明中并看看有什么不同

    使得。）

#### 练习：1 星（plus_id_exercise）

    删除 "Admitted." 并填写证明。

```
Theorem plus_id_exercise : ∀n m o : nat,
  n = m → m = o → n + m = m + o.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    Admitted 命令告诉 Coq 我们要跳过尝试

    为了证明这个定理并将其接受为给定的。这可以

    对于开发更长证明很有用，因为我们可以陈述附属的

    我们相信这些引理对于构建一些更大的

    参数，使用 Admitted 来暂时接受它们的真实性，

    并继续处理主要参数，直到我们确定它

    有意义；然后我们可以回去填写我们

    跳过。但是要小心：每次说 Admitted 时，您

    留下一个门打开，让完全无意义的东西进入 Coq 的美好，

    严格的，形式上检查过的世界！

    我们也可以使用 rewrite 策略与先前证明的

    定理而不是上下文中的假设。如果陈述

    先前证明的定理涉及量化变量，

    就像下面的例子中一样，Coq 尝试实例化它们

    通过与当前目标匹配。

```
Theorem mult_0_plus : ∀n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite → plus_O_n.
  reflexivity. Qed.

```

#### 练习：2 星（mult_S_1）

```
Theorem mult_S_1 : ∀n m : nat,
  m = S n →
  m * (1 + n) = m * m.
Proof.
  (* FILL IN HERE *) Admitted.

(* (N.b. This proof can actually be completed without using rewrite,    but please do use rewrite for the sake of the exercise.) *)

```

    ☐

```

# Proof by Case Analysis

    Of course, not everything can be proved by simple
    calculation and rewriting: In general, unknown, hypothetical
    values (arbitrary numbers, booleans, lists, etc.) can block
    simplification.  For example, if we try to prove the following
    fact using the simpl tactic as above, we get stuck.

```

定理 plus_1_neq_0_firsttry: ∀n：nat，

beq_nat (n + 1) 0 = false。

证明。

引入 n。

简化。（* 什么也不做！ *）

放弃。

```

    The reason for this is that the definitions of both
    beq_nat and + begin by performing a match on their first
    argument.  But here, the first argument to + is the unknown
    number n and the argument to beq_nat is the compound
    expression n + 1; neither can be simplified.

    To make progress, we need to consider the possible forms of n
    separately.  If n is O, then we can calculate the final result
    of beq_nat (n + 1) 0 and check that it is, indeed, false.  And
    if n = S n' for some n', then, although we don't know exactly
    what number n + 1 yields, we can calculate that, at least, it
    will begin with one S, and this is enough to calculate that,
    again, beq_nat (n + 1) 0 will yield false.

    The tactic that tells Coq to consider, separately, the cases where
    n = O and where n = S n' is called destruct.

```

定理 plus_1_neq_0：∀n：nat，

beq_nat (n + 1) 0 = false。

证明。

引入 n。分解 n 为 [| n']。

- 反射性。

- 反射性。证毕。

```

    The destruct generates *two* subgoals, which we must then
    prove, separately, in order to get Coq to accept the theorem. The
    annotation "as [| n']" is called an *intro pattern*.  It tells
    Coq what variable names to introduce in each subgoal.  In general,
    what goes between the square brackets is a *list of lists* of
    names, separated by |.  In this case, the first component is
    empty, since the O constructor is nullary (it doesn't have any
    arguments).  The second component gives a single name, n', since
    S is a unary constructor.

    The - signs on the second and third lines are called *bullets*,
    and they mark the parts of the proof that correspond to each
    generated subgoal.  The proof script that comes after a bullet is
    the entire proof for a subgoal.  In this example, each of the
    subgoals is easily proved by a single use of reflexivity, which
    itself performs some simplification — e.g., the first one
    simplifies beq_nat (S n' + 1) 0 to false by first rewriting
    (S n' + 1) to S (n' + 1), then unfolding beq_nat, and then
    simplifying the match.

    Marking cases with bullets is entirely optional: if bullets are
    not present, Coq simply asks you to prove each subgoal in
    sequence, one at a time. But it is a good idea to use bullets.
    For one thing, they make the structure of a proof apparent, making
    it more readable. Also, bullets instruct Coq to ensure that a
    subgoal is complete before trying to verify the next one,
    preventing proofs for different subgoals from getting mixed
    up. These issues become especially important in large
    developments, where fragile proofs lead to long debugging
    sessions.

    There are no hard and fast rules for how proofs should be
    formatted in Coq — in particular, where lines should be broken
    and how sections of the proof should be indented to indicate their
    nested structure.  However, if the places where multiple subgoals
    are generated are marked with explicit bullets at the beginning of
    lines, then the proof will be readable almost no matter what
    choices are made about other aspects of layout.

    This is also a good place to mention one other piece of somewhat
    obvious advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or writing entire proofs on one line.  Good style lies somewhere
    in the middle.  One reasonable convention is to limit yourself to
    80-character lines.

    The destruct tactic can be used with any inductively defined
    datatype.  For example, we use it next to prove that boolean
    negation is involutive — i.e., that negation is its own
    inverse.

```

定理 negb_involutive：∀b：bool，

negb (negb b) = b。

证明。

引入 b。分解 b。

- 反射性。

- 反射性。证毕。

```

    Note that the destruct here has no as clause because
    none of the subcases of the destruct need to bind any variables,
    so there is no need to specify any names.  (We could also have
    written as [|], or as [].)  In fact, we can omit the as
    clause from *any* destruct and Coq will fill in variable names
    automatically.  This is generally considered bad style, since Coq
    often makes confusing choices of names when left to its own
    devices.

    It is sometimes useful to invoke destruct inside a subgoal,
    generating yet more proof obligations. In this case, we use
    different kinds of bullets to mark goals on different "levels."
    For example:

```

定理 andb_commutative: ∀b c，andb b c = andb c b。

证明。

引入 b c。分解 b。

- 分解 c。

+ 反射性。

+ 反射性。

- 分解 c。

+ 反射性。

+ 反射性。

证毕。

```

    Each pair of calls to reflexivity corresponds to the
    subgoals that were generated after the execution of the destruct c
    line right above it. 

    Besides - and +, we can use * (asterisk) as a third kind of
    bullet.  We can also enclose sub-proofs in curly braces, which is
    useful in case we ever encounter a proof that generates more than
    three levels of subgoals:

```

定理 andb_commutative'：∀b c，andb b c = andb c b。

证明。

引入 b c。分解 b。

{ 分解 c。

{ 反射性。}

{ 反射性。} }

{ 分解 c。

{ 反射性。}

{ 反射性。} }

证毕。

```

    Since curly braces mark both the beginning and the end of a
    proof, they can be used for multiple subgoal levels, as this
    example shows. Furthermore, curly braces allow us to reuse the
    same bullet shapes at multiple levels in a proof:

```

定理 andb3_exchange：

∀b c d，andb (andb b c) d = andb (andb b d) c。

证明。

引入 b c d。分解 b。

- 分解 c。

{ 分解 d。

- 反射性。

- 反射性。}

{ 分解 d。

- 反射性。

- 反射性。}

- 分解 c。

{ 分解 d。

- 反射性。

- 反射性。}

{ 分解 d。

- 反射性。

- 反射性。}

证毕。

```

    Before closing the chapter, let's mention one final
    convenience.  As you may have noticed, many proofs perform case
    analysis on a variable right after introducing it:

```

引入 x y。分解 y 为 [|y]。

    这种模式是如此常见，以至于 Coq 为其提供了一个简写：我们

    当引入一个变量时，可以对其执行案例分析

    使用一个引入模式而不是一个变量名。例如，

    这里是上面的 plus_1_neq_0 定理的更短证明。

```
Theorem plus_1_neq_0' : ∀n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

```

    如果没有要命名的参数，我们可以只写 []。

```
Theorem andb_commutative'' :
  ∀b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

```

#### 练习：2 星（andb_true_elim2）

    证明以下声明，使用

    当你使用 destruct 时，请使用项目符号。

```
Theorem andb_true_elim2 : ∀b c : bool,
  andb b c = true → c = true.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：1 星（zero_nbeq_plus_1）

```
Theorem zero_nbeq_plus_1 : ∀n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

## More on Notation (Optional)

    (In general, sections marked Optional are not needed to follow the
    rest of the book, except possibly other Optional sections.  On a
    first reading, you might want to skim these sections so that you
    know what's there for future reference.)

    Recall the notation definitions for infix plus and times:

```

记号 "x + y" := (plus x y)

（在 50 级，左结合性）

：nat_scope。

记号 "x * y" := (mult x y)

（在 40 级，左结合性）

：nat_scope。

```

    For each notation symbol in Coq, we can specify its *precedence level* and its *associativity*.  The precedence level n is
    specified by writing at level n; this helps Coq parse compound
    expressions.  The associativity setting helps to disambiguate
    expressions containing multiple occurrences of the same
    symbol. For example, the parameters specified above for + and
    * say that the expression 1+2*3*4 is shorthand for
    (1+((2*3)*4)). Coq uses precedence levels from 0 to 100, and
    *left*, *right*, or *no* associativity.  We will see more examples
    of this later, e.g., in the Lists
    chapter.

    Each notation symbol is also associated with a *notation scope*.
    Coq tries to guess what scope is meant from context, so when it
    sees S(O*O) it guesses nat_scope, but when it sees the
    cartesian product (tuple) type bool*bool (which we'll see in
    later chapters) it guesses type_scope.  Occasionally, it is
    necessary to help it out with percent-notation by writing
    (x*y)%nat, and sometimes in what Coq prints it will use %nat
    to indicate what scope a notation is in.

    Notation scopes also apply to numeral notation (3, 4, 5,
    etc.), so you may sometimes see 0%nat, which means O (the
    natural number 0 that we're using in this chapter), or 0%Z,
    which means the Integer zero (which comes from a different part of
    the standard library).

    Pro tip: Coq's notation mechanism is not especially powerful.
    Don't expect too much from it!

```

## 固定点和结构递归（可选）

    这里是加法的定义副本：

```
Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O ⇒ m
  | S n' ⇒ S (plus' n' m)
  end.

```

    当 Coq 检查这个定义时，它注意到 plus' 是

    "第一个参数递减"。这意味着我们

    执行 *结构递归* 时，i.e.，

    我们只对严格较小的值进行递归调用

    n。这意味着对 plus' 的所有调用最终将

    终止。Coq 要求每个 Fixpoint 的某个参数

    定义是 "递减的"。

    此要求是 Coq 设计的一个基本特征：在

    特别是，它保证可以定义的每个函数

    在 Coq 中将对所有输入终止。然而，由于 Coq 的

    "递减分析"并不是非常复杂，有时候

    编写函数时需要以稍微不自然的方式编写。

#### 练习：2 星，可选（递减）

    要具体了解这一点，找到一种合理的方式编写一个

    定义（比如一个简单的数字函数）的参数

    *确实* 在所有输入上终止，但 Coq 会拒绝，因为

    这个限制。

```
(* FILL IN HERE *)

```

    ☐

```

# More Exercises

#### Exercise: 2 starsM (boolean_functions)

    Use the tactics you have learned so far to prove the following
    theorem about boolean functions.

```

定理 identity_fn_applied_twice：

∀(f : bool → bool)，

(∀(x : bool)，f x = x) →

∀(b : bool)，f (f b) = b。

Proof。

(* 在此填入 *) 已被承认。

```

    Now state and prove a theorem negation_fn_applied_twice similar
    to the previous one but where the second hypothesis says that the
    function f has the property that f x = negb x.

```

(* 在此填入 *)

```

    ☐ 

#### Exercise: 2 stars (andb_eq_orb)

    Prove the following theorem.  (You may want to first prove a
    subsidiary lemma or two. Alternatively, remember that you do
    not have to introduce all hypotheses at the same time.)

```

定理 andb_eq_orb：

∀(b c : bool)，

（andb b c = orb b c）→

b = c。

Proof。

(* 在此填入 *) 已被承认。

```

    ☐ 

#### Exercise: 3 starsM (binary)

    Consider a different, more efficient representation of natural
    numbers using a binary rather than unary system.  That is, instead
    of saying that each natural number is either zero or the successor
    of a natural number, we can say that each binary number is either

*   zero,

*   twice a binary number, or

*   one more than twice a binary number.

    (a) First, write an inductive definition of the type bin
        corresponding to this description of binary numbers.

    (Hint: Recall that the definition of nat above,

```

Inductive nat：Type := | O：nat | S：nat → nat。

    对 O 和 S 的“含义”一无所知。它只是说“O 是

    在集合中叫做 nat，并且如果 n 在集合中，则 S n 也在其中。”将 O 解释为零，S 解释为后继/加法

    这是由于我们 *使用* nat 值的方式，

    处理它们的功能，证明与它们相关的事实，

    等等。你的 bin 的定义应该相应地简单；

    它是你接下来将要编写的函数

    数学含义。）

    （b）接下来，为二进制数编写一个增量函数 incr，

        以及一个将二进制数转换为一进制的函数 bin_to_nat

        数字。

    （c）编写五个单元测试 test_bin_incr1、test_bin_incr2 等。

        对于您的增量和二进制到一进制函数。（一个 "单元

        Coq 中的 "test" 是一个特定的例子，可以证明

        就是反射性，就像我们做过的一样

        定义。）请注意，增加一个二进制数和

        然后将其转换为一进制应该产生相同的结果

        首先将其转换为一进制，然后递增。

```
(* FILL IN HERE *)

```

    ☐

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```

```
