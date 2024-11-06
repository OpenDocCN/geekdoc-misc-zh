# 证明对象库里的柯里-霍华德对应

```

      "*Algorithms are the computational content of proofs*."  —Robert Harper

```

需要导出 IndProp。

```

    We have seen that Coq has mechanisms both for *programming*,
    using inductive data types like nat or list and functions over
    these types, and for *proving* properties of these programs, using
    inductive propositions (like ev), implication, universal
    quantification, and the like.  So far, we have mostly treated
    these mechanisms as if they were quite separate, and for many
    purposes this is a good way to think.  But we have also seen hints
    that Coq's programming and proving facilities are closely related.
    For example, the keyword Inductive is used to declare both data
    types and propositions, and → is used both to describe the type
    of functions on data and logical implication.  This is not just a
    syntactic accident!  In fact, programs and proofs in Coq are
    almost the same thing.  In this chapter we will study how this
    works.

    We have already seen the fundamental idea: provability in Coq is
    represented by concrete *evidence*.  When we construct the proof
    of a basic proposition, we are actually building a tree of
    evidence, which can be thought of as a data structure.

    If the proposition is an implication like A → B, then its proof
    will be an evidence *transformer*: a recipe for converting
    evidence for A into evidence for B.  So at a fundamental level,
    proofs are simply programs that manipulate evidence. 

    Question: If evidence is data, what are propositions themselves?

    Answer: They are types!

    Look again at the formal definition of the ev property.

```

打印 ev。

(* ==>   归纳定义 ev : nat -> Prop :=     | ev_0 : ev 0     | ev_SS : forall n, ev n -> ev (S (S n)). *)

```

    Suppose we introduce an alternative pronunciation of ":".
    Instead of "has type," we can say "is a proof of."  For example,
    the second line in the definition of ev declares that ev_0 : ev 0.  Instead of "ev_0 has type ev 0," we can say that "ev_0
    is a proof of ev 0." 

    This pun between types and propositions — between : as "has type"
    and : as "is a proof of" or "is evidence for" — is called the
    *Curry-Howard correspondence*.  It proposes a deep connection
    between the world of logic and the world of computation:

```

                命题  ~  类型

                证明        ~  数据值

```

    See [[Wadler 2015]](Bib.html#Wadler 2015) for a brief history and an up-to-date exposition.

    Many useful insights follow from this connection.  To begin with,
    it gives us a natural interpretation of the type of the ev_SS
    constructor:

```

检查 ev_SS。

(* ===> ev_SS : forall n,                   ev n ->                   ev (S (S n)) *)

```

    This can be read "ev_SS is a constructor that takes two
    arguments — a number n and evidence for the proposition ev n — and yields evidence for the proposition ev (S (S n))." 

    Now let's look again at a previous proof involving ev.

```

定理 ev_4 : ev 4。

证明。

应用 ev_SS。应用 ev_SS。应用 ev_0。Qed。

```

    As with ordinary data values and functions, we can use the Print
    command to see the *proof object* that results from this proof
    script.

```

打印 ev_4。

(* ===> ev_4 = ev_SS 2 (ev_SS 0 ev_0)      : ev 4  *)

```

    As a matter of fact, we can also write down this proof object
    *directly*, without the need for a separate proof script:

```

检查 (ev_SS 2 (ev_SS 0 ev_0))。

(* ===> ev 4 *)

```

    The expression ev_SS 2 (ev_SS 0 ev_0) can be thought of as
    instantiating the parameterized constructor ev_SS with the
    specific arguments 2 and 0 plus the corresponding proof
    objects for its premises ev 2 and ev 0.  Alternatively, we can
    think of ev_SS as a primitive "evidence constructor" that, when
    applied to a particular number, wants to be further applied to
    evidence that that number is even; its type,

```

∀n, ev n → ev (S (S n)),

    表达了这种功能，就像多态的方式一样

    类型 ∀ X, list X 表达了构造函数

    nil 可以被视为从类型到空列表的函数

    与该类型的元素。

    我们在 Logic 章节中看到，我们可以使用函数

    应用语法来实例化全称量化的变量

    在引理中，以及为假设提供证据

    这些引理施加的限制。例如：

```
Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

```

    现在我们可以看到这个特性是归纳定义的一个微不足道的结果

    Coq 授予证明和命题的状态：引理和

    假设可以在表达式中组合（即，证明对象中）

    根据用于程序的相同基本规则

    语言。

```

# Proof Scripts

    The *proof objects* we've been discussing lie at the core of how
    Coq operates.  When Coq is following a proof script, what is
    happening internally is that it is gradually constructing a proof
    object — a term whose type is the proposition being proved.  The
    tactics between Proof and Qed tell it how to build up a term
    of the required type.  To see this process in action, let's use
    the Show Proof command to display the current state of the proof
    tree at various points in the following tactic proof.

```

定理 ev_4'' : ev 4。

证明。

显示证明。

应用 ev_SS。

显示证明。

应用 ev_SS。

显示证明。

应用 ev_0。

显示证明。

Qed。

```

    At any given moment, Coq has constructed a term with a
    "hole" (indicated by ?Goal here, and so on), and it knows what
    type of evidence is needed to fill this hole.  

    Each hole corresponds to a subgoal, and the proof is
    finished when there are no more subgoals.  At this point, the
    evidence we've built stored in the global context under the name
    given in the Theorem command. 

    Tactic proofs are useful and convenient, but they are not
    essential: in principle, we can always construct the required
    evidence by hand, as shown above. Then we can use Definition
    (rather than Theorem) to give a global name directly to a
    piece of evidence.

```

定义 ev_4''' : ev 4 :=

ev_SS 2 (ev_SS 0 ev_0)。

```

    All these different ways of building the proof lead to exactly the
    same evidence being saved in the global environment.

```

打印 ev_4。

(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)

打印 ev_4'。

(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)

打印 ev_4''。

(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)

打印 ev_4'''。

(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)

```

#### Exercise: 1 star (eight_is_even)

    Give a tactic proof and a proof object showing that ev 8.

```

定理 ev_8 : ev 8。

证明。

(* 在这里填写*）Admitted。

定义 ev_8' : ev 8

(* 用":= _your_definition_ ." 替换此行*). Admitted。

```

    ☐

```

# 量词、蕴涵、函数

    在 Coq 的计算宇宙中（数据结构和

    程序存在的地方），有两种带有箭头的值

    类型：由归纳定义的数据引入的*构造函数*

    类型和*函数*。

    同样，在 Coq 的逻辑宇宙中（我们进行证明的地方），

    ��两种提供蕴涵证据的方法：

    由归纳定义的命题引入的构造函数，

    并且... 函数！

    例如，考虑这个陈述：

```
Theorem ev_plus4 : ∀n, ev n → ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

```

    与 ev_plus4 对应的证明对象是什么？

    我们正在寻找一个表达式，其类型为 ∀ n, ev n → ev (4 + n) — 也就是说，一个接受两个参数（一个

    数字和一段证据）并返回一段证据！

    这里是：

```
Definition ev_plus4' : ∀n, ev n → ev (4 + n) :=
  fun (n : nat) ⇒ fun (H : ev n) ⇒
    ev_SS (S (S n)) (ev_SS n H).

```

    回想一下 fun n ⇒ blah 的意思是“给定 n，返回 blah 的函数”

    产生 blah，”而 Coq 将 4 + n 和 S (S (S (S n)))

    作为同义词。另一种等效的写法是：

```
Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''.
(* ===> ev_plus4'' : forall n : nat, ev n -> ev (4 + n) *)

```

    当我们将 ev_plus4 证明的命题视为

    函数类型，其中的一个方面可能看起来有点不寻常。这

    第二个参数的类型，ev n，提到了第一个

    参数 n。虽然这样的*依赖类型*在

    传统编程语言，它们在

    编程也是如此，就像最近在

    函数式编程社区展示。

    注意到蕴含（→）和量化（∀）都

    对应于证据上的函数。实际上，它们确实是

    同样的事情：→只是一个简写，用于

    ∀在没有依赖性的情况下，即不需要给出一个

    左箭头的类型的名称。

    例如，考虑这个命题：

```
Definition ev_plus2 : Prop :=
  ∀n, ∀(E : ev n), ev (n + 2).

```

    居住在这个命题中的证明项将是一个函数

    有两个参数：一个数字 n 和一些证据 E，证明 n 是

    甚至。但是这个证据的名称 E 在其余部分中没有使用

    ev_plus2 的陈述，所以费事去打扰

    为其取一个名字。我们可以改为这样写，

    使用虚拟标识符 _ 代替真实名称：

```
Definition ev_plus2' : Prop :=
  ∀n, ∀(_ : ev n), ev (n + 2).

```

    或者，等效地，我们可以用更熟悉的符号表示：

```
Definition ev_plus2'' : Prop :=
  ∀n, ev n → ev (n + 2).

```

    一般来说，“P → Q”只是语法糖

    "∀ (_:P), Q"。

```

# Programming with Tactics

    If we can build proofs by giving explicit terms rather than
    executing tactic scripts, you may be wondering whether we can
    build *programs* using *tactics* rather than explicit terms.
    Naturally, the answer is yes!

```

定义 add1 : nat → nat。

intro n。

展示证明。

应用 S。

展示证明。

应用 n。已定义。

打印 add1。

(* ==>     add1 = fun n : nat => S n          : nat -> nat *)

计算 add1 2。

(* ==> 3 : nat *)

```

    Notice that we terminate the Definition with a . rather than
    with := followed by a term.  This tells Coq to enter *proof scripting mode* to build an object of type nat → nat.  Also, we
    terminate the proof with Defined rather than Qed; this makes
    the definition *transparent* so that it can be used in computation
    like a normally-defined function.  (Qed-defined objects are
    opaque during computation.)

    This feature is mainly useful for writing functions with dependent
    types, which we won't explore much further in this book.  But it
    does illustrate the uniformity and orthogonality of the basic
    ideas in Coq.

```

# 逻辑连接词作为归纳类型

    归纳定义足够强大，可以表达大多数

    到目前为止我们所见过的连接词和量词。实际上，只有

    全称量化（因此蕴含）内置于 Coq 中；

    其他都是归纳定义的。我们将看到这些

    本节中的定义中找不到。

```
Module Props.

```

## 合取

    要证明 P ∧ Q 成立，我们必须为两者提供证据

    P 和 Q。因此，定义 P ∧ Q 的证明对象为由两个证明组成：一个为 P，另一个为 Q。

    另一个为 Q。这导致以下定义。

```
Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P → Q → and P Q.

End And.

```

    注意与 prod 类型的定义相似，

    在章节 Poly 中给出；唯一的区别是 prod 接受

    类型参数，而且 and 接受 Prop 参数。

```
Print prod.
(* ===>    Inductive prod (X Y : Type) : Type :=    | pair : X -> Y -> X * Y. *)

```

    这应该澄清为什么析构和引入模式可以

    用于合取假设。案例分析允许我们

    考虑 P ∧ Q 被证明的所有可能方式 — 这里

    只有一个（conj 构造函数）。同样，split 策略

    实际上适用于只有归纳定义的命题

    一个构造函数。特别是，它适用于和：

```
Lemma and_comm : ∀P Q : Prop, P ∧ Q ↔ Q ∧ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

```

    这说明了合取的归纳定义为什么可以

    通过策略进行操作。我们也可以用它来

    直接构建证明，使用模式匹配。例如：

```
Definition and_comm'_aux P Q (H : P ∧ Q) :=
  match H with
  | conj HP HQ ⇒ conj HQ HP
  end.

Definition and_comm' P Q : P ∧ Q ↔ Q ∧ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

```

#### 练习：2 星，可选（conj_fact）

    构建一个证明对象，证明以下命题。

```
Definition conj_fact : ∀P Q R, P ∧ Q → Q ∧ R → P ∧ R 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

```

    ☐

## 析取

    析取的归纳定义使用两个构造函数，一个

    对于析取的每一侧：

```
Module Or.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P → or P Q
| or_intror : Q → or P Q.

End Or.

```

    此声明解释了对析构策略的行为

    一个析取假设，因为生成的子目标匹配

    or_introl 和 or_intror 构造函数的形状。

    再次，我们也可以直接为定理编写证明对象

    涉及或，而不借助策略。

#### 练习：2 星，可选（or_commut''）

    尝试为 or_commut 写下一个显式的证明对象（不使用

    使用 Print 来查看我们已经定义的内容！).

```
Definition or_comm : ∀P Q, P ∨ Q → Q ∨ P 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

```

    ☐

## 存在量化

    为存在量化器提供证据，我们打包一个

    证人 x 和一个证明 x 满足属性

    P：

```
Module Ex.

Inductive ex {A : Type} (P : A → Prop) : Prop :=
| ex_intro : ∀x : A, P x → ex P.

End Ex.

```

    这可能需要一点解释。核心定义是

    对于可以用来构建命题的类型形成 ex

    表达式 ex P 的形式，其中 P 本身是一个*函数*，从证明者

    类型 A 中的值到命题。ex_intro

    构造函数然后提供了构建 ex P 的证据的方法，

    给定一个证人 x 和一个证明 P x 的证明。

    更熟悉的形式 ∃ x, P x 展开为一个表达式

    涉及 ex：

```
Check ex (fun n ⇒ ev n).
(* ===> exists n : nat, ev n         : Prop *)

```

    这是���何定义涉及 ex 的显式证明对象的方法：

```
Definition some_nat_is_even : ∃n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

```

#### 练习：2 星，可选（ex_ev_Sn）

    完成以下证明对象的定义：

```
Definition ex_ev_Sn : ex (fun n ⇒ ev (S n)) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

```

    ☐

## 真和假

    True 命题的归纳定义很简单：

```
Inductive True : Prop :=
  | I : True.

```

    它有一个构造函数（因此每个 True 的证明都是相同的，所以

    给定 True 的证明并不具有信息量。）

    False 同样简单 — 实际上，如此简单以至于可能看起来

    乍一看在语法上是错误的！

```
Inductive False : Prop :=.

```

    也就是说，False 是一个没有构造函数的归纳类型 —

    即，没有办法为它建立证据。

```
End Props.

```

# 相等

    即使 Coq 的相等关系也不是内建的。它有

    以下归纳定义。（实际上，在

    标准库是这个的一个小变体，它提供了一个

    更容易使用的归纳原理。)

```
Module MyEquality.

Inductive eq {X:Type} : X → X → Prop :=
| eq_refl : ∀x, eq x x.

Notation "x = y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

```

    想到这个定义的方式是，给定一个集合 X，

    它定义了一个*命题*族“x 等于 y”，

    由值对（x 和 y）从 X 索引。只有

    为这个家族的每个成员构造证据的一种方法：

    将构造函数 eq_refl 应用于类型 X 和值 x：X 产生证据，证明 x 等于 x。

#### 练习：2 星（leibniz_equality）

    相等的归纳定义对应于*莱布尼兹相等*：当我们说“x 和 y 相等”时，我们指的是

    对于 P 的每个属性，如果 x 是真的，那么也是真的

    y。

```
Lemma leibniz_equality : ∀(X : Type) (x y: X),
  x = y → ∀P:X→Prop, P x → P y.
Proof.
(* FILL IN HERE *) Admitted.

```

    ☐

    我们可以使用 eq_refl 构造证据，例如，2 = 2。我们也可以使用它来构造证据，证明 1 + 1 = 2 吗？

    是的，我们可以。实际上，这正是同一证据！这

    原因是 Coq 将任何在语法上看起来是“相同”的两个术语视为

    根据一组简单的计算规则*可转换*。

    这些规则与 Compute 使用的规则类似，包括

    函数应用的求值，定义的内联，和

    匹配的简化。

```
Lemma four: 2 + 2 = 1 + 3.
Proof.
  apply eq_refl.
Qed.

```

    我们用来证明相等性的反射策略

    到目前为止基本上只是 apply refl_equal 的简写。

    在基于策略的相等证明中，转换规则是

    通常隐藏在 simpl 的使用中（无论是显式的还是隐式的

    其他策略，如反射）。但你可以看到它们

    直接在以下显式证明对象中工作：

```
Definition four' : 2 + 2 = 1 + 3 :=
  eq_refl 4.

Definition singleton : ∀(X:Set) (x:X), []++[x] = x::[]  :=
  fun (X:Set) (x:X) ⇒ eq_refl [x].

End MyEquality.

Definition quiz6 : ∃x,  x + 3 = 4
  := ex_intro (fun z ⇒ (z + 3 = 4)) 1 (refl_equal 4).

```

## 再次反转

    我们已经看到反演被用于等式假设和

    关于归纳定义命题的假设。现在我们已经

    看到这实际上是同一件事，我们处于一个位置

    更仔细地看一下反演的行为。

    一般来说，反演策略...

+   取一个类型为 P 的归纳定义的假设 H，并

+   对于 P 的定义中的每个构造函数 C，

    +   生成一个新的子目标，在其中我们假设 H 是用 C 构建的，

    +   将构造函数 C 的参数（前提）添加到子目标的上下文中作为额外的假设，

    +   将构造函数 C 的结论（结果类型）与当前目标进行匹配，并计算必须满足的一组相等性，

    +   将这些相等性添加到上下文中（为了方便起见，在目标中重写它们），并

    +   如果相等性不可满足（例如，它们涉及像 S n = O 这样的东西），立即解决子目标。

    *例子*：如果我们反演一个由 or 构建的假设，那么有两个

构造函数，所以生成两个子目标。这

构造函数（P ∨ Q）的结论（结果类型）不

不对 P 或 Q 的形式施加任何限制，所以我们不会得到

在子目标的上下文中有任何额外的相等性。

    *例子*：如果我们反演一个由 and 构建的假设，那么有

只有一个构造函数，所以只生成一个子目标。再次，

构造函数（P ∧ Q）的结论（结果类型）不

不对 P 或 Q 的形式施加任何限制，所以我们不会得到

在子目标的上下文中有任何额外的相等性。这

构造函数确实有两个参数，这两个参数可以看到

在子目标的上下文中。

    *例子*：如果我们反演一个由 eq 构建的假设，那么有

再次只有一个构造函数，所以只生成一个子目标。

现在，然而，refl_equal 构造函数的形式确实给了我们

一些额外的信息：它告诉我们 eq 的两个参数

必须相同！反演策略将这个事实添加到

上下文。

```

```

```

```

```

```
