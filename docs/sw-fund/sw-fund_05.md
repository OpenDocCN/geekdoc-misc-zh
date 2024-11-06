# 多态性和高阶函数

```

```

需要导出列表。

```

# Polymorphism

    In this chapter we continue our development of basic
    concepts of functional programming.  The critical new ideas are
    *polymorphism* (abstracting functions over the types of the data
    they manipulate) and *higher-order functions* (treating functions
    as data).  We begin with polymorphism.

```

## 多态列表

    在过去的几章中，我们一直在工作

    与数字列表。显然，有趣的程序也需要

    能够操作具有其他类型元素的列表 —

    字符串列表，布尔列表，列表列表等。我们

    *可能*只是为这些中的每一个定义一个新的归纳数据类型，

    例如...

```
Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool → boollist → boollist.

```

    ...但这很快会变得乏味，部分原因是我们

    必须为每种数据类型编造不同的构造函数名称，但

    主要是因为我们还需要定义所有的新版本

    我们的列表操作函数（length，rev 等）对于每个

    新的数据类型定义。

    为了避免所有这些重复，Coq 支持*多态*

    归纳类型定义。例如，这是一个*多态列表*数据类型。

```
Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X → list X → list X.

```

    这与 natlist 的定义完全相同

    前一章节，除了 cons 的 nat 参数

    构造函数已被替换为任意类型 X，一个绑定

    对于 X 已经添加到标题中，并且出现的

    构造函数的类型中的 natlist 已被替换为

    列表 X。（我们可以重复使用构造函数名称 nil 和 cons

    因为 natlist 的早期定义在

    现在已经超出范围的模块定义。）

    list 本身是什么样的东西？一个好的思考方式

    关于它的一点是 list 是一个*从类型到函数*的

    归纳定义；或者，换句话说，list 是一个

    从类型到类型的函数。对于任何特定类型 X，

    类型列表 X 是一个归纳定义的列表集合

    元素的类型为 X。

    有了这个定义，当我们使用构造函数 nil 和

    cons 来构建列表，我们需要告诉 Coq 类型的

    我们正在构建的列表中的元素 — 即 nil 和 cons

    现在是*多态构造函数*。观察这些的类型

    构造函数：

```
Check nil.
(* ===> nil : forall X : Type, list X *)
Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

```

    （关于符号的侧注：在 .v 文件中，“forall”量词

    用字母拼写出来。在生成的 HTML 文件和

    各种 IDE 显示 .v 文件的方式（使用特定设置）

    显示控制），∀ 通常被排版为通常的

    数学中的"倒立的 A"，但你仍然会看到拼写出来的

    几个地方会看到"forall"。这只是排版的一种怪癖：

    意义上没有区别。)

    这些类型中的"∀ X"可以被解读为额外的

    构造函数的参数，确定预期的类型

    后面跟随的参数。当使用 nil 和 cons 时，这些

    参数以与其他参数相同的方式提供。对于

    例如，包含 2 和 1 的列表写成这样：

```
Check (cons nat 2 (cons nat 1 (nil nat))).

```

    (我们在这里明确写出了 nil 和 cons，因为我们还没有

    尚未定义新版本的 [] 和 :: 符号

    列表。我们稍后会做这个。)

    现在我们可以回去制作所有

    我们之前编写的列表处理函数。这是 repeat，

    例如：

```
Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 ⇒ nil X
  | S count' ⇒ cons X x (repeat X x count')
  end.

```

    与 nil 和 cons 一样，我们可以通过应用 repeat 来��用它

    首先是一个类型，然后是它的列表参数：

```
Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

```

    要使用重复来构建其他类型的列表，我们只需

    实例化它与适当的类型参数：

```
Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.

```

#### 练习：2 星 M（mumble_grumble）

    考虑以下两种归纳定义的类型。

```
Inductive mumble : Type :=
  | a : mumble
  | b : mumble → nat → mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble → grumble X
  | e : X → grumble X.

```

    以下哪些是 grumble X 的良好类型化元素

    一些类型 X？

+   d（b a 5）

+   d mumbo-jumbo（b a 5）

+   d 布尔（b a 5）

+   e bool true

+   e mumbo-jumbo（b c 0）

+   e 布尔（b c 0）

+   c

    （*填写此处*）

    ☐

```
End MumbleGrumble.

```

### 类型注释推断

    让我们再次编写 repeat 的定义，但这次我们

    将不指定任何参数的类型。 Coq 仍然会

    接受吗？

```
Fixpoint repeat' X x count : list X :=
  match count with
  | 0        ⇒ nil X
  | S count' ⇒ cons X x (repeat' X x count')
  end.

```

    的确会。 让我们看看 Coq 分配给 repeat' 的类型是什么：

```
Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)

```

    它的类型与 repeat 完全相同。 Coq 能够

    使用 *类型推断* 来推断 X、x 和

    根据它们的使用方式，count 必须是什么。 例如，因为

    X 用作 cons 的参数，它必须是一个 Type，因为

    cons 期望作为其第一个参数的类型； 匹配计数

    与 0 和 S 意味着它必须是 nat； 等等。

    这个强大的工具意味着我们不必总是写

    显式类型注释到处都是，尽管显式类型

    注释仍然非常有用作文档和理智

    检查，所以我们将继续大多数时候使用它们。 你

    应该尝试在自己的代码中找到太多之间的平衡

    类型注释（可能会混乱和分散注意力）和太

    很少（迫使读者在脑海中执行类型推断

    为了理解您的代码）。

```

### Type Argument Synthesis

    To use a polymorphic function, we need to pass it one or
    more types in addition to its other arguments.  For example, the
    recursive call in the body of the repeat function above must
    pass along the type X.  But since the second argument to
    repeat is an element of X, it seems entirely obvious that the
    first argument can only be X — why should we have to write it
    explicitly?

    Fortunately, Coq permits us to avoid this kind of redundancy.  In
    place of any type argument we can write the "implicit argument"
    _, which can be read as "Please try to figure out for yourself
    what belongs here."  More precisely, when Coq encounters a _, it
    will attempt to *unify* all locally available information — the
    type of the function being applied, the types of the other
    arguments, and the type expected by the context in which the
    application appears — to determine what concrete type should
    replace the _.

    This may sound similar to type annotation inference — indeed, the
    two procedures rely on the same underlying mechanisms.  Instead of
    simply omitting the types of some arguments to a function, like

```

重复' X x 计数：列表 X :=

    我们还可以用 _ 替换类型

```
      repeat' (X : _) (x : _) (count : _) : list X :=

    to tell Coq to attempt to infer the missing information.

    Using implicit arguments, the count function can be written like
    this:

```

递归重复'' X x count：列表 X :=

匹配 count with

| 0 ⇒ nil _

| S count' ⇒ cons _ x（repeat'' _ x count'）

结束。

```

    In this instance, we don't save much by writing _ instead of
    X.  But in many cases the difference in both keystrokes and
    readability is nontrivial.  For example, suppose we want to write
    down a list containing the numbers 1, 2, and 3.  Instead of
    writing this...

```

定义列表 123 :=

cons nat 1（cons nat 2（cons nat 3（nil nat）））。

```

    ...we can use argument synthesis to write this:

```

定义列表 123' :=

cons _ 1（cons _ 2（cons _ 3（nil _）））。

```

### Implicit Arguments

    We can go further and even avoid writing _'s in most cases by
    telling Coq *always* to infer the type argument(s) of a given
    function.  The Arguments directive specifies the name of the
    function (or constructor) and then lists its argument names, with
    curly braces around any arguments to be treated as implicit.  (If
    some arguments of a definition don't have a name, as is often the
    case for constructors, they can be marked with a wildcard pattern
    _.)

```

参数 nil {X}。

参数 cons {X} _ _。

参数重复 {X} x 计数。

```

    Now, we don't have to supply type arguments at all:

```

定义列表 123'' := cons 1 (cons 2 (cons 3 nil))。

```

    Alternatively, we can declare an argument to be implicit
    when defining the function itself, by surrounding it in curly
    braces instead of parens.  For example:

```

重复''' {X：Type}（x：X）（计数：nat）：列表 X :=

匹配 count with

| 0 ⇒ nil

| S count' ⇒ cons x（repeat''' x count'）

结束。

```

    (Note that we didn't even have to provide a type argument to the
    recursive call to repeat'''; indeed, it would be invalid to
    provide one!)

    We will use the latter style whenever possible, but we will
    continue to use use explicit Argument declarations for
    Inductive constructors.  The reason for this is that marking the
    parameter of an inductive type as implicit causes it to become
    implicit for the type itself, not just for its constructors.  For
    instance, consider the following alternative definition of the
    list type:

```

归纳列表' {X：Type}：Type :=

| nil' : list'

| cons' : X → list' → list'。

```

    Because X is declared as implicit for the *entire* inductive
    definition including list' itself, we now have to write just
    list' whether we are talking about lists of numbers or booleans
    or anything else, rather than list' nat or list' bool or
    whatever; this is a step too far. 

    Let's finish by re-implementing a few other standard list
    functions on our new polymorphic lists...

```

重复应用 {X：Type}（l[1] l[2]：列表 X）

：（列表 X）：=

匹配 l[1] with

| nil ⇒ l[2]

| cons h t ⇒ cons h (app t l[2])

结束。

递归 rev {X：Type}（l：列表 X）：列表 X :=

匹配 l with

| nil ⇒ nil

| cons h t ⇒ app（rev t）（cons h nil）

end.

递归长度 {X：Type}（l：列表 X）：nat :=

匹配 l with

| nil ⇒ 0

| cons _ l' ⇒ S (length l')

结束。

示例 test_rev1：

rev（cons 1（cons 2 nil））=（cons 2（cons 1 nil））。

证明。 一致性。 Qed。

示例 test_rev2：

rev（cons true nil）= cons true nil。

证明。 一致性。 Qed。

示例 test_length1：长度（cons 1（cons 2（cons 3 nil）））= 3。

证明。 一致性。 Qed。

```

### Supplying Type Arguments Explicitly

    One small problem with declaring arguments Implicit is
    that, occasionally, Coq does not have enough local information to
    determine a type argument; in such cases, we need to tell Coq that
    we want to give the argument explicitly just this time.  For
    example, suppose we write this:

```

Fail Definition mynil := nil。

```

    (The Fail qualifier that appears before Definition can be
    used with *any* command, and is used to ensure that that command
    indeed fails when executed. If the command does fail, Coq prints
    the corresponding error message, but continues processing the rest
    of the file.)

    Here, Coq gives us an error because it doesn't know what type
    argument to supply to nil.  We can help it by providing an
    explicit type declaration (so that Coq has more information
    available when it gets to the "application" of nil):

```

定义 mynil：列表 nat := nil。

```

    Alternatively, we can force the implicit arguments to be explicit by
   prefixing the function name with @.

```

检查 @nil。

定义 mynil' := @nil nat。

```

    Using argument synthesis and implicit arguments, we can
    define convenient notation for lists, as before.  Since we have
    made the constructor type arguments implicit, Coq will know to
    automatically infer these when we use the notations.

```

符号"x :: y" :=（cons x y）

（级别 60，右结合）。

符号"[ ]" := nil。

符号"[ x ; .. ; y ]" :=（cons x ..（cons y []）..）。

表示法 "x ++ y" := (app x y)

（在级别 60，右结合性）。

```

    Now lists can be written just the way we'd hope:

```

定义 list123''' := [1; 2; 3]。

```

### Exercises

#### Exercise: 2 stars, optional (poly_exercises)

    Here are a few simple exercises, just like ones in the Lists
    chapter, for practice with polymorphism.  Complete the proofs below.

```

定理 app_nil_r : ∀(X:Type), ∀l:list X,

l ++ [] = l.

证明。

(* 在此填写*）Admitted。

定理 app_assoc : ∀A (l m n:list A),

l ++ m ++ n = (l ++ m) ++ n。

证明。

(* 在此填写*）Admitted。

引理 app_length : ∀(X:Type) (l[1] l[2] : list X),

length (l[1] ++ l[2]) = length l[1] + length l[2].

证明。

(* 在此填写*）Admitted。

```

    ☐ 

#### Exercise: 2 stars, optional (more_poly_exercises)

    Here are some slightly more interesting ones...

```

定理 rev_app_distr: ∀X (l[1] l[2] : list X),

rev (l[1] ++ l[2]) = rev l[2] ++ rev l[1]。

证明。

(* 在此填写*）Admitted。

定理 rev_involutive : ∀X : Type, ∀l : list X,

rev (rev l) = l。

证明。

(* 在此填写*）Admitted。

```

    ☐

```

## 多态对

    遵循相同的模式，我们在

    对于数字对的最后一章可以推广到

    *多态对*，通常称为 *乘积*：

```
Inductive prod (X Y : Type) : Type :=
| pair : X → Y → prod X Y.

Arguments pair {X} {Y} _ _.

```

    与列表一样，我们使类型参数隐式，并定义

    熟悉的具体表示法。

```
Notation "( x , y )" := (pair x y).

```

    我们还可以使用表示法机制来定义标准的

    用于乘积 *类型* 的表示法：

```
Notation "X * Y" := (prod X Y) : type_scope.

```

    （注释 : type_scope 告诉 Coq 这个缩写

    在解析类型时应该使用，这样可以避免与

    乘法符号。）

    起初很容易混淆 (x,y) 和 X*Y。

    记住 (x,y) 是从另外两个值构建的 *值*，

    而 X*Y 是从其他两种类型构建的 *类型*。如果 x 有

    类型 X 和 y 的类型为 Y，那么 (x,y) 的类型为 X*Y。

    第一个和第二个投影函数现在看起来相当

    就像它们在任何函数式编程语言中一样。

```
Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) ⇒ x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) ⇒ y
  end.

```

    以下函数接受两个列表并将它们组合

    转换为一对列表。在其他函数式语言中，通常

    我们称之为 zip；为了与 Coq 的一致性，我们称之为 combine。

    标准库。

```
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ ⇒ []
  | _, [] ⇒ []
  | x :: tx, y :: ty ⇒ (x, y) :: (combine tx ty)
  end.

```

#### 练习：1 星，可选 M（combine_checks）

    尝试在纸上回答以下问题并

    检查你在 coq 中的答案：

+   combine 的类型是什么（即，Check @combine 打印什么？）

+   什么是

    ```
      Compute (combine [1;2] [false;false;true;true]).

     print?
    ```

    ☐

#### 练习：2 星，推荐（split）

    函数 split 是 combine 的右逆：它接受一个

    一对列表并返回一对列表。在许多函数式

    语言，它被称为 unzip。

    在下面填写 split 的定义。确保它通过

    给定的单元测试。

```
Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
(* FILL IN HERE *) Admitted.

```

    ☐

```

## Polymorphic Options

    One last polymorphic type for now: *polymorphic options*,
    which generalize natoption from the previous chapter:

```

形式 option (X:Type) : Type :=

| Some : X → option X

| None : option X。

参数 Some {X} _。

参数 None {X}。

```

    We can now rewrite the nth_error function so that it works
    with any type of lists.

```

Fixpoint nth_error {X : Type} (l : list X) (n : nat)

: option X :=

匹配 l with

| [] ⇒ None

| a :: l' ⇒ 如果 beq_nat n O 则 Some a 否则 nth_error l' (pred n)

结束。

例子 test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4。

    证明。反射性。Qed。

例子 test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].

    证明。反射性。Qed。

例子 test_nth_error3 : nth_error [true] 2 = None.

    证明。反射性。Qed。

```

#### Exercise: 1 star, optional (hd_error_poly)

    Complete the definition of a polymorphic version of the
    hd_error function from the last chapter. Be sure that it
    passes the unit tests below.

```

定义 hd_error {X : Type} (l : list X) : option X

(* 用":= _your_definition_ ." 替换此行*). Admitted.

```

    Once again, to force the implicit arguments to be explicit,
    we can use @ before the name of the function.

```

检查 @hd_error。

例子 test_hd_error1 : hd_error [1;2] = Some 1。

(* 在此填写*）Admitted。

Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1]。

(* 在这里填写内容 *) 已承认。

```

    ☐

```

# 函数作为数据

    与许多其他现代编程语言一样 — 包括

    所有的函数式语言（ML、Haskell、Scheme、Scala、Clojure 等）

    等等。） — Coq 将函数视为一等公民，允许它们作为参数传递给其他函数，作为结果返回，存储在数据结构中等。

    它们可以作为参数传递给其他函数，作为结果返回，存储在数据结构中等。

    结果，存储在数据结构中等。

```

## Higher-Order Functions

    Functions that manipulate other functions are often called
    *higher-order* functions.  Here's a simple one:

```

定义 doit3times {X:Type} (f:X→X) (n:X) : X :=

f (f (f n))。

```

    The argument f here is itself a function (from X to
    X); the body of doit3times applies f three times to some
    value n.

```

检查 @doit3times。

(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3。

Proof。反射性。Qed。

Example test_doit3times': doit3times negb true = false。

Proof。反射性。Qed。

```

## Filter

    Here is a more useful higher-order function, taking a list
    of Xs and a *predicate* on X (a function from X to bool)
    and "filtering" the list, returning a new list containing just
    those elements for which the predicate returns true.

```

固定点 filter {X:Type} (test: X→bool) (l:list X)，

: (list X) :=

匹配 l，

| []     ⇒ []

| h :: t ⇒ if test h then h :: (filter test t)

else       filter test t

end。

```

    For example, if we apply filter to the predicate evenb
    and a list of numbers l, it returns a list containing just the
    even members of l.

```

Example test_filter1: filter evenb [1;2;3;4] = [2;4]。

Proof。反射性。Qed。

定义 length_is_1 {X : Type} (l : list X) : bool :=

beq_nat (length l) 1。

Example test_filter2:

filter length_is_1

[ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]

= [ [3]; [4]; [8] ]。

Proof。反射性。Qed。

```

    We can use filter to give a concise version of the
    countoddmembers function from the Lists chapter.

```

定义 countoddmembers' (l:list nat) : nat :=

length (filter oddb l)。

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4。

Proof。反射性。Qed。

Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0。

Proof。反射性。Qed。

Example test_countoddmembers'3:   countoddmembers' nil = 0。

Proof。反射性。Qed。

```

## Anonymous Functions

    It is arguably a little sad, in the example just above, to
    be forced to define the function length_is_1 and give it a name
    just to be able to pass it as an argument to filter, since we
    will probably never use it again.  Moreover, this is not an
    isolated example: when using higher-order functions, we often want
    to pass as arguments "one-off" functions that we will never use
    again; having to give each of these functions a name would be
    tedious.

    Fortunately, there is a better way.  We can construct a function
    "on the fly" without declaring it at the top level or giving it a
    name.

```

Example test_anon_fun':

doit3times (fun n ⇒ n * n) 2 = 256。

Proof。反射性。Qed。

```

    The expression (fun n ⇒ n * n) can be read as "the function
    that, given a number n, yields n * n." 

    Here is the filter example, rewritten to use an anonymous
    function.

```

Example test_filter2':

filter (fun l ⇒ beq_nat (length l) 1)

[ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]

= [ [3]; [4]; [8] ]。

Proof。反射性。Qed。

```

#### Exercise: 2 stars (filter_even_gt[7])

    Use filter (instead of Fixpoint) to write a Coq function
    filter_even_gt[7] that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than
    7.

```

定义 filter_even_gt[7] (l : list nat) : list nat

(* 将此行替换为 ":= _your_definition_ ." *）。已承认。

Example test_filter_even_gt7_1 :

filter_even_gt[7] [1;2;6;9;10;3;12;8] = [10;12;8]。

(* 在这里填写内容 *) 已承认。

Example test_filter_even_gt7_2 :

filter_even_gt[7] [5;2;6;19;129] = []。

(* 在这里填写内容 *) 已承认。

```

    ☐ 

#### Exercise: 3 stars (partition)

    Use filter to write a Coq function partition:

```

partition : ∀X : Type，

(X → bool) → list X → list X * list X

    给定一个集合 X、一个类型为 X → bool 的测试函数和一个列表 X，partition 应该返回一个列表对。第一个成员是满足测试的元素的列表，第二个是原始列表中包含不满足测试的元素的子列表。元素的顺序应与原始列表中的顺序相同。

该对是原始列表中包含满足测试的子列表和包含不满足测试的子列表。

满足测试条件的元素，第二个是包含不满足测试的元素的子列表。元素的顺序应与原始列表中的顺序相同。

包含不满足测试的那些元素。元素的顺序应与原始列表中的顺序相同。

两个子列表的顺序应与它们在原始列表中的顺序相同。

list。

```
Definition partition {X : Type}
                     (test : X → bool)
                     (l : list X)
                   : list X * list X
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
(* FILL IN HERE *) Admitted.
Example test_partition2: partition (fun x ⇒ false) [5;9;0] = ([], [5;9;0]).
(* FILL IN HERE *) Admitted.

```

    ☐

```

## Map

    Another handy higher-order function is called map.

```

固定点 map {X Y:Type} (f:X→Y) (l:list X) : (list Y) :=

匹配 l，

| []     ⇒ []

| h :: t ⇒ (f h) :: (map f t)

end。

```

    It takes a function f and a list l = [n[1], n[2], n[3], ...] and returns the list [f n[1], f n[2], f n[3],...] , where f has
    been applied to each element of l in turn.  For example: 

```

Example test_map1: map (fun x ⇒ plus 3 x) [2;0;2] = [5;3;5]。

Proof。反射性。Qed。

```

    The element types of the input and output lists need not be
    the same, since map takes *two* type arguments, X and Y; it
    can thus be applied to a list of numbers and a function from
    numbers to booleans to yield a list of booleans:

```

Example test_map2:

map oddb [2;1;2;5] = [false;true;false;true]。

Proof。反射性。Qed。

```

    It can even be applied to a list of numbers and
    a function from numbers to *lists* of booleans to
    yield a *list of lists* of booleans:

```

Example test_map3:

map (fun n ⇒ [evenb n;oddb n]) [2;1;2;5]

= [[true;false];[false;true];[true;false];[false;true]]。

Proof。反射性。Qed。

```

### Exercises

#### Exercise: 3 stars (map_rev)

    Show that map and rev commute.  You may need to define an
    auxiliary lemma.

```

定理 map_rev : ∀(X Y : Type) (f : X → Y) (l : list X)，

map f（rev l）= rev（map f l）。

证明。

（* 在这里填写 *）承认。

```

    ☐ 

#### Exercise: 2 stars, recommended (flat_map)

    The function map maps a list X to a list Y using a function
    of type X → Y.  We can define a similar function, flat_map,
    which maps a list X to a list Y using a function f of type
    X → list Y.  Your definition should work by 'flattening' the
    results of f, like so:

```

flat_map （fun n ⇒ [n;n+1;n+2]） [1;5;10]

= [1; 2; 3; 5; 6; 7; 10; 11; 12]。

```
Fixpoint flat_map {X Y:Type} (f:X → list Y) (l:list X)
                   : (list Y)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_flat_map1:
  flat_map (fun n ⇒ [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 (* FILL IN HERE *) Admitted.

```

    ☐

    列表不是我们可以编写的唯一归纳类型

    map 函数。这是 map 的定义

    选项类型：

```
Definition option_map {X Y : Type} (f : X → Y) (xo : option X)
                      : option Y :=
  match xo with
    | None ⇒ None
    | Some x ⇒ Some (f x)
  end.

```

#### 练习：2 星，可选（implicit_args）

    filter 和 map 的定义和使用使用隐式

    许多地方使用参数。替换大括号周围的

    带括号的隐式参数，然后填写显式

    必要时使用类型参数，并使用 Coq 检查您是否

    这样做是正确的。（这个练习不需要提交；它是

    可能最容易在您可以

    之后丢弃。）

☐

```

## Fold

    An even more powerful higher-order function is called
    fold.  This function is the inspiration for the "reduce"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework.

```

Fixpoint fold {X Y:Type}（f：X→Y→Y）（l:list X）（b:Y）

：Y :=

匹配 l 与

| nil ⇒ b

| h :: t ⇒ f h (fold f t b)

结束。

```

    Intuitively, the behavior of the fold operation is to
    insert a given binary operator f between every pair of elements
    in a given list.  For example, fold plus [1;2;3;4] intuitively
    means 1+2+3+4.  To make this precise, we also need a "starting
    element" that serves as the initial second input to f.  So, for
    example,

```

fold plus [1;2;3;4] 0

    产生

```
       1 + (2 + (3 + (4 + 0))).

    Some more examples:

```

检查（fold andb）。

（* ===> fold andb : list bool -> bool -> bool *）

示例 fold_example1：

fold mult [1;2;3;4] 1 = 24。

    证明。反射性。Qed。

示例 fold_example2：

fold andb [true;true;false;true] true = false。

    证明。反射性。Qed。

示例 fold_example3：

fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4]。

    证明。反射性。Qed。

```

#### Exercise: 1 star, advancedM (fold_types_different)

    Observe that the type of fold is parameterized by *two* type
    variables, X and Y, and the parameter f is a binary operator
    that takes an X and a Y and returns a Y.  Can you think of a
    situation where it would be useful for X and Y to be
    different?

```

（* 在这里填写 *）

```

    ☐

```

## 构造函数的函数

    我们谈到的大多数高阶函数

    远的函数作为参数。让我们看一些示例

    涉及 *返回* 函数作为其他函数的结果。

    首先，这里有一个函数，它接受一个值 x（来自

    一些类型 X）并返回一个从自然数到 X 的函数

    每当调用它时，都会返回 x，忽略其自然数参数。

```
Definition constfun {X: Type} (x: X) : nat→X :=
  fun (k:nat) ⇒ x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.

    Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.

    Proof. reflexivity. Qed.

```

    实际上，我们已经

    看到的也是将函数作为数据传递的示例。要了解原因，请参考

    回忆加法的类型。

```
Check plus.
(* ==> nat -> nat -> nat *)

```

    这个表达式中的每个 → 实际上都是一个 *二元* 运算符

    在类型上。这个运算符是 *右结合* 的，所以类型

    加号实际上是 nat →（nat → nat）的简写，即

    可以解释为“plus 是一个接受一个参数的函数

    接受一个自然数并返回一个接受

    另一个自然数并返回一个自然数。”在上面的例子中，我们

    总是同时应用加法到它的两个参数，但

    如果我们愿意，我们可以只提供第一个。这被称为 *部分应用*。

```
Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

```

# 附加练习

```
Module Exercises.

```

#### 练习：2 星（fold_length）

    我们已经谈到的许多列表上的常见函数可以根据

折叠。例如，这里是长度的另一种定义：

```
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n ⇒ S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.

    Proof. reflexivity. Qed.

```

    证明 fold_length 的正确性。

```
Theorem fold_length_correct : ∀X (l : list X),
  fold_length l = length l.
(* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星 M（fold_map）

    我们也可以根据 fold 定义 map。完成 fold_map

    下面。

```
Definition fold_map {X Y:Type} (f : X → Y) (l : list X) : list Y
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

```

    在 Coq 中写下一个定理 fold_map_correct，陈述

fold_map 正确，并证明它。

```
(* FILL IN HERE *)

```

    ☐

#### 练习：2 星，高级（柯里化）

    在 Coq 中，函数 f：A → B → C 实际上具有类型 A →（B → C）。也就是说，如果您给 f 一个类型为 A 的值

    将给您一个函数 f'：B → C。然后，如果您给 f' 一个

    类型 B 的值，它将返回类型 C 的值。这

    允许部分应用，如 plus3。处理一个列表

    用返回函数的函数组合参数的过程被称为

    *柯里化*，以逻辑学家 Haskell Curry 命名。

    相反，我们可以重新解释类型 A → B → C 为 (A * B) → C。这被称为 *非柯里化*。通过一个非柯里化的二元

    函数，两个参数必须一次性给出作为一对；没有

    没有部分应用。

    我们可以将柯里化定义如下：

```
Definition prod_curry {X Y Z : Type}
  (f : X * Y → Z) (x : X) (y : Y) : Z := f (x, y).

```

    作为练习，定义它的逆函数 prod_uncurry。然后证明

    以下定理来展示这两者是互为反函数。

```
Definition prod_uncurry {X Y Z : Type}
  (f : X → Y → Z) (p : X * Y) : Z
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

```

    作为柯里化有用性的（微不足道的）例子，我们可以使用它

    缩短我们之前看到的例子之一：

```
Example test_map2: map (fun x ⇒ plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

```

    思考练习：在运行以下命令之前，你能否

    计算 prod_curry 和 prod_uncurry 的类型？

```
Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : ∀(X Y Z : Type)
                        (f : X → Y → Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem curry_uncurry : ∀(X Y Z : Type)
                        (f : (X * Y) → Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：2 星，高级 M（nth_error_informal）

    回顾 nth_error 函数的定义：

```
   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] ⇒ None
     | a :: l' ⇒ if beq_nat n O then Some a else nth_error l' (pred n)
     end.

    Write an informal proof of the following theorem:

```

∀X n l，length l = n → @nth_error X l n = None

    （*在这里填写*）

    ☐

#### 练习：4 星，高级（church_numerals）

    这个练习探讨了定义自然数的另一种方式

    数字，使用所谓的 *Church 数*，以其名字命名

    数学家阿隆佐·邱奇。我们可以用一种自然数表示

    将 n 视为一个以函数 f 为参数的函数，并

    返回 f 迭代 n 次。

```
Module Church.
Definition nat := ∀X : Type, (X → X) → X → X.

```

    让我们看看如何用这种表示法写一些数字。迭代

    一个函数应用一次应该与直接应用它相同。因此：

```
Definition one : nat :=
  fun (X : Type) (f : X → X) (x : X) ⇒ f x.

```

    同样，two 应该将 f 应用两次到它的参数上：

```
Definition two : nat :=
  fun (X : Type) (f : X → X) (x : X) ⇒ f (f x).

```

    定义零有些棘手：我们如何“应用一个函数

    零次”？答案实际上很简单：只需返回

    保持参数不变。

```
Definition zero : nat :=
  fun (X : Type) (f : X → X) (x : X) ⇒ x.

```

    更一般地，一个数 n 可以写成 fun X f x ⇒ f (f ... (f x) ...), 其中 f 出现 n 次。请注意

    特别是我们之前定义的 doit3times 函数

    实际上只是 3 的 Church 表示。

```
Definition three : nat := @doit3times.

```

    完成以下函数的定义。确保

    通过证明相应的单元测试是否通过

    自反性。

    自然数的后继：

```
Definition succ (n : nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example succ_1 : succ zero = one.
Proof. (* FILL IN HERE *) Admitted.

Example succ_2 : succ one = two.
Proof. (* FILL IN HERE *) Admitted.

Example succ_3 : succ two = three.
Proof. (* FILL IN HERE *) Admitted.

```

    两个自然数的加法：

```
Definition plus (n m : nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example plus_1 : plus zero one = one.
Proof. (* FILL IN HERE *) Admitted.

Example plus_2 : plus two three = plus three two.
Proof. (* FILL IN HERE *) Admitted.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* FILL IN HERE *) Admitted.

```

    乘法：

```
Definition mult (n m : nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example mult_1 : mult one one = one.
Proof. (* FILL IN HERE *) Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof. (* FILL IN HERE *) Admitted.

Example mult_3 : mult two three = plus three three.
Proof. (* FILL IN HERE *) Admitted.

```

    指数运算：

    （*提示*：多态在这里起着至关重要的作用。然而，

    选择正确的类型进行迭代可能会有些棘手。如果你遇到

    一个“宇宙不一致”错误，请尝试迭代不同的

    类型：nat 本身通常会有问题。）

```
Definition exp (n m : nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example exp_1 : exp two two = plus two two.
Proof. (* FILL IN HERE *) Admitted.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. (* FILL IN HERE *) Admitted.

Example exp_3 : exp three zero = one.
Proof. (* FILL IN HERE *) Admitted.

End Church.

```

    ☐

```
End Exercises.

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

```

```

```
