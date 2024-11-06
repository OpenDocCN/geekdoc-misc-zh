# ImpSimple 命令式程序

```

    In this chapter, we begin a new direction that will continue for
    the rest of the course.  Up to now most of our attention has been
    focused on various aspects of Coq itself, while from now on we'll
    mostly be using Coq to formalize other things.  (We'll continue to
    pause from time to time to introduce a few additional aspects of
    Coq.)

    Our first case study is a *simple imperative programming language*
    called Imp, embodying a tiny core fragment of conventional
    mainstream languages such as C and Java.  Here is a familiar
    mathematical function written in Imp.

```

Z ::= X;;

Y ::= 1;;

当 WHILE not (Z = 0) DO 时

Y ::= Y * Z;;

Z ::= Z - 1

结束

    本章将讨论如何定义*语法*和*语义*

    的 Imp；接下来的章节将发展一个*程序等价*理论，并引入*霍尔逻辑*，这是一个广泛使用的逻辑

    推理关于命令式程序。

```
(* IMPORTS *)
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Maps.
(* /IMPORTS *)

```

# 算术和布尔表达式

    我们将以三部分呈现 Imp：首先是一个核心语言

    *算术和布尔表达式*，然后是这些的扩展

    带有*变量*的表达式，最后是*命令*的语言

    包括赋值、条件、顺序和循环。

```

## Syntax

```

模块 AExp。

```

    These two definitions specify the *abstract syntax* of
    arithmetic and boolean expressions.

```

归纳定义 aexp：类型 :=

| ANum : nat → aexp

| APlus : aexp → aexp → aexp

| AMinus : aexp → aexp → aexp

| AMult : aexp → aexp → aexp.

归纳定义 bexp：类型 :=

| BTrue : bexp

| BFalse : bexp

| BEq : aexp → aexp → bexp

| BLe : aexp → aexp → bexp

| BNot : bexp → bexp

| BAnd : bexp → bexp → bexp.

```

    In this chapter, we'll elide the translation from the
    concrete syntax that a programmer would actually write to these
    abstract syntax trees — the process that, for example, would
    translate the string "1+2*3" to the AST

```

APlus (ANum 1) (AMult (ANum 2) (ANum 3)).

    可选章节 ImpParser 开发了一个简单的

    实现一个可以执行的词法分析器和解析器

    这个翻译。你*不*需要理解那一章节

    理解这个，但如果您还没有参加过这些课程

    要覆盖的技术（例如，编译器课程），您可能希望

    略读它。

    作为比较，这里是一个传统的 BNF（巴科斯-瑙尔形式）

    定义相同抽象语法的语法：

```
    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a ≤ a
        | not b
        | b and b

    Compared to the Coq version above...

*   The BNF is more informal — for example, it gives some suggestions about the surface syntax of expressions (like the fact that the addition operation is written + and is an infix symbol) while leaving other aspects of lexical analysis and parsing (like the relative precedence of +, -, and *, the use of parens to explicitly group subexpressions, etc.) unspecified. Some additional information (and human intelligence) would be required to turn this description into a formal definition, for example when implementing a compiler. 

     The Coq version consistently omits all this information and concentrates on the abstract syntax only. 

*   On the other hand, the BNF version is lighter and easier to read. Its informality makes it flexible, a big advantage in situations like discussions at the blackboard, where conveying general ideas is more important than getting every detail nailed down precisely. 

     Indeed, there are dozens of BNF-like notations and people switch freely among them, usually without bothering to say which form of BNF they're using because there is no need to: a rough-and-ready informal understanding is all that's important.

    It's good to be comfortable with both sorts of notations: informal
    ones for communicating between humans and formal ones for carrying
    out implementations and proofs.

```

## 评估

    *评估*一个算术表达式会产生一个数字。

```
Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n ⇒ n
  | APlus a[1] a[2] ⇒ (aeval a[1]) + (aeval a[2])
  | AMinus a[1] a[2]  ⇒ (aeval a[1]) - (aeval a[2])
  | AMult a[1] a[2] ⇒ (aeval a[1]) * (aeval a[2])
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.

    Proof. reflexivity. Qed.

```

    同样，评估布尔表达式会产生一个布尔值。

```
Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       ⇒ true
  | BFalse      ⇒ false
  | BEq a[1] a[2]   ⇒ beq_nat (aeval a[1]) (aeval a[2])
  | BLe a[1] a[2]   ⇒ leb (aeval a[1]) (aeval a[2])
  | BNot b[1]     ⇒ negb (beval b[1])
  | BAnd b[1] b[2]  ⇒ andb (beval b[1]) (beval b[2])
  end.

```

## 优化

    我们还没有定义很多，但我们已经可以得到

    一些定义。假设我们定义一个函数

    接受一个算术表达式并稍微简化它，

    改变每个 0+e 的出现（即，(APlus (ANum 0) e)

    只需 e。

```
Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n ⇒
      ANum n
  | APlus (ANum 0) e[2] ⇒
      optimize_0plus e[2]
  | APlus e[1] e[2] ⇒
      APlus (optimize_0plus e[1]) (optimize_0plus e[2])
  | AMinus e[1] e[2] ⇒
      AMinus (optimize_0plus e[1]) (optimize_0plus e[2])
  | AMult e[1] e[2] ⇒
      AMult (optimize_0plus e[1]) (optimize_0plus e[2])
  end.

```

    为了确保我们的优化是正确的，我们

    可以在一些示例上测试它，看看输出是否正常。

```
Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).

    Proof. reflexivity. Qed.

```

    但如果我们想确保优化是正确的 —

    即，评估优化后的表达式会产生相同的

    结果与原始结果相同 — 我们应该证明它。

```
Theorem optimize_0plus_sound: ∀a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a[1].
    + (* a[1] = ANum n *) destruct n.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a[1] = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a[1] = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a[1] = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity. Qed.

```

# Coq 自动化

    在这最后一个证明中的重复量���点

    恼人。如果算术表达式的语言或

    正在被证明为正确的优化显着更多

    复杂，这将开始成为一个真正的问题。

    到目前为止，我们一直在使用只有一小撮的证明

    Coq 的策略，完全忽略其强大的功能

    用于自动构建证明的部分。本节

    介绍了一些这些设施，我们将在接下来看到更多

    接下来的几章。习惯于它们将需要一些

    能量 — Coq 的自动化是一个强大的工具 — 但它将允许我们

    扩展我们的努力到更复杂的定义和更多

    有趣的属性而不被无聊的细节所淹没，

    重复的，低级的细节。

```

## Tacticals

    *Tacticals* is Coq's term for tactics that take other tactics as
    arguments — "higher-order tactics," if you will.

```

### 尝试策略

    如果 T 是一个策略，那么 try T 是一个与 T 完全相同的策略

    除非 T 失败，否则尝试 T *成功* 什么也不做。

    全部（而不是失败）。

```
Theorem silly1 : ∀ae, aeval ae = aeval ae.
Proof. try reflexivity. (* this just does reflexivity *) Qed.

Theorem silly2 : ∀(P : Prop), P → P.
Proof.
  intros P HP.
  try reflexivity. (* just reflexivity would have failed *)
  apply HP. (* we can still finish the proof in some other way *)
Qed.

```

    没有真正的理由在完全手动的情况下使用 try

    这样的证明，但它在进行自动化时非常有用

    证明与; 策略一起使用的证明

    接下来。

```

### The ; Tactical (Simple Form)

    In its most common form, the ; tactical takes two tactics as
    arguments.  The compound tactic T;T' first performs T and then
    performs T' on *each subgoal* generated by T. 

    For example, consider the following trivial lemma:

```

引理 foo：∀n，leb 0 n = true。

证明。

引入。

分解 n。

（* 留下两个子目标，它们以相同的方式消除... *）

- （* n=0 *）简化。 反射性。

- （* n=Sn' *）简化。 反射性。

结束。

```

    We can simplify this proof using the ; tactical:

```

引理 foo'：∀n，leb 0 n = true。

证明。

引入。

（* 分解当前目标 *）

分解 n;

（* 然后简化每个产生的子目标 *）

简化;

（* 并对每个产生的子目标进行反射性操作 *）

反射性。

结束。

```

    Using try and ; together, we can get rid of the repetition in
    the proof that was bothering us a little while ago.

```

定理 optimize_0plus_sound'：∀a，

aeval（optimize_0plus a）= aeval a。

证明。

引入 a。

归纳 a;

（* 大多数情况都可以直接由 IH... *）

尝试（简化; 重写 IHa1; 重写 IHa2; 反射性）。

（* ... 但剩下的情况 -- ANum 和 APlus --        是不同的： *）

- （* ANum *）反射性。

- （* APlus *）

分解 a[1];

再次，大多数情况都可以直接通过 IH 解决：

尝试（简化; 简化在 IHa1 中; 重写 IHa1;

重写 IHa2; 反射性）。

（* 有趣的情况，在这种情况下，尝试...        什么也不做，是当 e[1] = ANum n 时。 在这种情况下，我们必须分解 n （看看是否         应用了优化）并使用归纳假设进行重写。 *）

+ （* a[1] = ANum n *）分解 n;

简化; 重写 IHa2; 反射性。 结束。

```

    Coq experts often use this "...; try... " idiom after a tactic
    like induction to take care of many similar cases all at once.
    Naturally, this practice has an analog in informal proofs.  For
    example, here is an informal proof of the optimization theorem
    that matches the structure of the formal one:

    *Theorem*: For all arithmetic expressions a,

```

aeval（optimize_0plus a）= aeval a。

    *证明*：通过对 a 进行归纳。 大多数情况直接由

    IH。 剩余的情况如下：

+   假设 a = ANum n 对某个 n 成立。 我们必须展示

    ```
      aeval (optimize_0plus (ANum n)) = aeval (ANum n).

     This is immediate from the definition of optimize_0plus. 

    ```

+   假设 a = APlus a[1] a[2] 对某些 a[1] 和 a[2] 成立。 我们必须展示

    ```
      aeval (optimize_0plus (APlus a[1] a[2])) = aeval (APlus a[1] a[2]).

     Consider the possible forms of a[1]. For most of them, optimize_0plus simply calls itself recursively for the subexpressions and rebuilds a new expression of the same form as a[1]; in these cases, the result follows directly from the IH. 

     The interesting case is when a[1] = ANum n for some n. If n = ANum 0, then 

    ```

    optimize_0plus（APlus a[1] a[2]）= optimize_0plus a[2]

    对于 a[2] 的 IH 恰好是我们所需的。 另一方面，如果 n = S n' 对某个 n' 成立，那么 optimize_0plus 再次简单地递归调用自身，结果就是由 IH 得出的。 ☐

    ```

    ```

    但是，这个证明仍然可以改进：第一个情况（对于

    a = ANum n）非常微不足道 —— 甚至比我们选择的案例

    我们简单地说是从 IH 中简单地得出的 —— 然而我们选择了

    完整地写出它会更好更清晰。最好是将其删除

    并且只需在顶部说，“大多数情况要么是即时的要么是

    直接来自 IH。 唯一有趣的情况是

    APlus..." 我们可以在我们的形式证明中做同样的改进

    也。 这是它的样子：

```
Theorem optimize_0plus_sound'': ∀a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a[1] a[2]. *)
  - (* APlus *)
    destruct a[1]; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a[1] = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

```

### ; 策略（一般形式）

    该; 策略也比简单的形式更加一般化

    T;T' 上面我们已经见过。 如果 T、T[1]、...、Tn 是策略，

    然后

```
      T; [T[1] | T[2] | ... | Tn]

    is a tactic that first performs T and then performs T[1] on the
   first subgoal generated by T, performs T[2] on the second
   subgoal, etc.

    So T;T' is just special notation for the case when all of the
   Ti's are the same tactic; i.e., T;T' is shorthand for:

```

T； [T' | T' | ... | T']

```

### The repeat Tactical

    The repeat tactical takes another tactic and keeps applying this
    tactic until it fails. Here is an example showing that 10 is in
    a long list using repeat.

```

定理 In[10]：在[1;2;3;4;5;6;7;8;9;10]中的 10。

证明。

重复（尝试（左; 反射性）; 右）。

结束。

```

    The tactic repeat T never fails: if the tactic T doesn't apply
    to the original goal, then repeat still succeeds without changing
    the original goal (i.e., it repeats zero times).

```

定理 In[10]'：在[1;2;3;4;5;6;7;8;9;10]中的 10。

证明。

重复（左; 反射性）。

重复（右; 尝试（左; 反射性））。

结束。

```

    The tactic repeat T also does not have any upper bound on the
    number of times it applies T.  If T is a tactic that always
    succeeds, then repeat T will loop forever (e.g., repeat simpl
    loops forever, since simpl always succeeds).  While evaluation
    in Coq's term language, Gallina, is guaranteed to terminate,
    tactic evaluation is not!  This does not affect Coq's logical
    consistency, however, since the job of repeat and other tactics
    is to guide Coq in constructing proofs; if the construction
    process diverges, this simply means that we have failed to
    construct a proof, not that we have constructed a wrong one. 

#### Exercise: 3 stars (optimize_0plus_b)

    Since the optimize_0plus transformation doesn't change the value
    of aexps, we should be able to apply it to all the aexps that
    appear in a bexp without changing the bexp's value.  Write a
    function which performs that transformation on bexps, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible.

```

定点 optimize_0plus_b（b：bexp）：bexp

（* 用你的定义替换此行为":= _your_definition_ ." *）。承认。

定理 optimize_0plus_b_sound：∀b，

beval（optimize_0plus_b b）= beval b。

证明。

(* 在这里填写 *) Admitted.

```

    ☐ 

#### Exercise: 4 stars, optional (optimizer)

    *Design exercise*: The optimization implemented by our
    optimize_0plus function is only one of many possible
    optimizations on arithmetic and boolean expressions.  Write a more
    sophisticated optimizer and prove it correct.  (You will probably
    find it easiest to start small — add just a single, simple
    optimization and prove it correct — and build up to something
    more interesting incrementially.)

    (* FILL IN HERE *)

    ☐

```

## 定义新的策略符号

    Coq 还提供了几种“编程”策略脚本的方式。

+   下面所示的 Tactic Notation 习语提供了一种方便的方式来定义“简写策略”，将几个策略捆绑成一个单一命令。

+   对于更复杂的编程，Coq 提供了一个名为 Ltac 的内置编程语言，其中包含可以检查和修改证明状态的原语。 这里的细节有点复杂（并且普遍认为 Ltac 不是 Coq 设计中最美丽的部分！），但可以在参考手册和其他关于 Coq 的书籍中找到，Coq 标准库中有许多 Ltac 定义的示例可供使用。

+   还有一个 OCaml API，可以用来构建访问 Coq 内部结构的策略，但对于普通的 Coq 用户来说很少值得麻烦。

    Tactic Notation 机制是最容易掌握的，

    它为许多目的提供了充足的功能。 这里有一个例子。

```
Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

```

    这定义了一个名为 simpl_and_try 的新策略，它接受一个

    策略 c 作为参数并定义为等价于

    策略 simpl; try c。 现在写成 "simpl_and_try reflexivity."

    在证明中将与写成 "simpl; try reflexivity." 相同。

```

## The omega Tactic

    The omega tactic implements a decision procedure for a subset of
    first-order logic called *Presburger arithmetic*.  It is based on
    the Omega algorithm invented in 1991 by William Pugh [[Pugh 1991]](Bib.html#Pugh 1991).

    If the goal is a universally quantified formula made out of

*   numeric constants, addition (+ and S), subtraction (- and pred), and multiplication by constants (this is what makes it Presburger arithmetic), 

*   equality (= and ≠) and inequality (≤), and 

*   the logical connectives ∧, ∨, ¬, and →,

    then invoking omega will either solve the goal or tell you that
    it is actually false.

```

导入 Coq.omega.Omega.

例如愚蠢的 presburger_example : ∀m n o p，

m + n ≤ n + o ∧ o + 3 = p + 3 →

m ≤ p.

证明。

intros. omega.

完毕。

```

## A Few More Handy Tactics

    Finally, here are some miscellaneous tactics that you may find
    convenient.

*   clear H: Delete hypothesis H from the context. 

*   subst x: Find an assumption x = e or e = x in the context, replace x with e throughout the context and current goal, and clear the assumption. 

*   subst: Substitute away *all* assumptions of the form x = e or e = x. 

*   rename... into...: Change the name of a hypothesis in the proof context. For example, if the context includes a variable named x, then rename x into y will change all occurrences of x to y. 

*   assumption: Try to find a hypothesis H in the context that exactly matches the goal; if one is found, behave like apply H. 

*   contradiction: Try to find a hypothesis H in the current context that is logically equivalent to False. If one is found, solve the goal. 

*   constructor: Try to find a constructor c (from some Inductive definition in the current environment) that can be applied to solve the current goal. If one is found, behave like apply c.

    We'll see examples below.

```

# 作为关系的评估

    我们已经将 aeval 和 beval 作为由函数定义的

    Fixpoints.  另一种思考评估的方式 — 我们

    经常更加灵活 — 是作为*关系*的一种

    表达式及其值。 这自然地导致归纳

    像下面这样为算术表达式定义...

```
Module aevalR_first_try.

Inductive aevalR : aexp → nat → Prop :=
  | E_ANum  : ∀(n: nat),
      aevalR (ANum n) n
  | E_APlus : ∀(e[1] e[2]: aexp) (n[1] n[2]: nat),
      aevalR e[1] n[1] →
      aevalR e[2] n[2] →
      aevalR (APlus e[1] e[2]) (n[1] + n[2])
  | E_AMinus: ∀(e[1] e[2]: aexp) (n[1] n[2]: nat),
      aevalR e[1] n[1] →
      aevalR e[2] n[2] →
      aevalR (AMinus e[1] e[2]) (n[1] - n[2])
  | E_AMult : ∀(e[1] e[2]: aexp) (n[1] n[2]: nat),
      aevalR e[1] n[1] →
      aevalR e[2] n[2] →
      aevalR (AMult e[1] e[2]) (n[1] * n[2]).

```

    为...定义一个中缀符号将很方便

    aevalR。 我们将写成 e ⇓ n 表示算术表达式

    e 评估为值 n。 （这种表示法是一个地方

    ASCII 符号的限制变得有点烦人。 这

    评估关系的标准符号是双

    向下箭头。 在 HTML 版本中我们会这样排版

    笔记中看到它们，并在 .v 中使用双斜杠作为最接近的近似

    文件。）

```
Notation "e '⇓' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.

```

    实际上，Coq 提供了一种在

    aevalR 本身的定义。 这通过避免

    在我们正在处理涉及语句的证明的情况下

    形式 e ⇓ n 但我们必须参考一个定义

    使用形式 aevalR e n。

    我们首先“保留”这个符号，然后给出

    一起的定义以及符号的声明

    意思。

```
Reserved Notation "e '⇓' n" (at level 50, left associativity).

Inductive aevalR : aexp → nat → Prop :=
  | E_ANum : ∀(n:nat),
      (ANum n) ⇓ n
  | E_APlus : ∀(e[1] e[2]: aexp) (n[1] n[2] : nat),
      (e[1] ⇓ n[1]) → (e[2] ⇓ n[2]) → (APlus e[1] e[2]) ⇓ (n[1] + n[2])
  | E_AMinus : ∀(e[1] e[2]: aexp) (n[1] n[2] : nat),
      (e[1] ⇓ n[1]) → (e[2] ⇓ n[2]) → (AMinus e[1] e[2]) ⇓ (n[1] - n[2])
  | E_AMult :  ∀(e[1] e[2]: aexp) (n[1] n[2] : nat),
      (e[1] ⇓ n[1]) → (e[2] ⇓ n[2]) → (AMult e[1] e[2]) ⇓ (n[1] * n[2])

  where "e '⇓' n" := (aevalR e n) : type_scope.

```

## 推理规则表示法

    在非正式讨论中，写规则对于

    aevalR 和类似关系以更可读的图形形式

    *推理规则*的形式，上面的前提证明

    下面的结论（我们已经在

    Prop 章节）。

    例如，构造函数 E_APlus...

```
      | E_APlus : ∀(e[1] e[2]: aexp) (n[1] n[2]: nat),
          aevalR e[1] n[1] →
          aevalR e[2] n[2] →
          aevalR (APlus e[1] e[2]) (n[1] + n[2])

    ...would be written like this as an inference rule:

                        e[1] ⇓ n[1]
           |

                     |

                        e[2] ⇓ n[2]
           |

                        (E_APlus)  
           |

* * *

           |

                        APlus e[1] e[2] ⇓ n[1]+n[2]
           |

                     |

    Formally, there is nothing deep about inference rules: they
    are just implications.  You can read the rule name on the right as
    the name of the constructor and read each of the linebreaks
    between the premises above the line (as well as the line itself)
    as →.  All the variables mentioned in the rule (e[1], n[1],
    etc.) are implicitly bound by universal quantifiers at the
    beginning. (Such variables are often called *metavariables* to
    distinguish them from the variables of the language we are
    defining.  At the moment, our arithmetic expressions don't include
    variables, but we'll soon be adding them.)  The whole collection
    of rules is understood as being wrapped in an Inductive
    declaration.  In informal prose, this is either elided or else
    indicated by saying something like "Let aevalR be the smallest
    relation closed under the following rules...". 

    For example, ⇓ is the smallest relation closed under these
    rules:

           |

                        (E_ANum)  
           |

* * *

           |

                        ANum n ⇓ n
           |

                     |

                        e[1] ⇓ n[1]
           |

                     |

                        e[2] ⇓ n[2]
           |

                        (E_APlus)  
           |

* * *

           |

                        APlus e[1] e[2] ⇓ n[1]+n[2]
           |

                     |

                        e[1] ⇓ n[1]
           |

                     |

                        e[2] ⇓ n[2]
           |

                        (E_AMinus)  
           |

* * *

           |

                        AMinus e[1] e[2] ⇓ n[1]-n[2]
           |

                     |

                        e[1] ⇓ n[1]
           |

                     |

                        e[2] ⇓ n[2]
           |

                        (E_AMult)  
           |

* * *

           |

                        AMult e[1] e[2] ⇓ n[1]*n[2]
           |

                     |

```

## 定义的等价性

    证明关系和功能性

    评估定义一致：

```
Theorem aeval_iff_aevalR : ∀a n,
  (a ⇓ n) ↔ aeval a = n.

    Proof.
 split.
 - (* -> *)
   intros H.
   induction H; simpl.
   + (* E_ANum *)
     reflexivity.
   + (* E_APlus *)
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   + (* E_AMinus *)
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   + (* E_AMult *)
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
 - (* <- *)
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
    Qed.

```

    我们可以通过更多地使用

    使用战术。

```
Theorem aeval_iff_aevalR' : ∀a n,
  (a ⇓ n) ↔ aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

```

#### 练习：3 星（bevalR）

    以与 bevalR 相同的风格编写一个关系

    aevalR，并证明它等效于 beval。

```
Inductive bevalR: bexp → bool → Prop :=
(* FILL IN HERE *)
.

Lemma beval_iff_bevalR : ∀b bv,
  bevalR b bv ↔ beval b = bv.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```
End AExp.

```

## 计算与关系定义

    对于算术和布尔值的评估定义

    表达式，选择使用函数式还是关系式

    定义主要是品味问题：任何一种方式都可以。

    然而，在某些情况下，关系定义的

    评估工作比功能性更好。

```
Module aevalR_division.

```

    例如，假设我们想要扩展算术

    通过考虑除法运算来扩展操作：

```
Inductive aexp : Type :=
  | ANum : nat → aexp
  | APlus : aexp → aexp → aexp
  | AMinus : aexp → aexp → aexp
  | AMult : aexp → aexp → aexp
  | ADiv : aexp → aexp → aexp. (* <--- new *)

```

    扩展 aeval 的定义以处理这个新操作

    将不是简单的（我们应该返回什么作为结果

    of ADiv（ANum 5）（ANum 0）？）。但扩展 aevalR 是

    直接的。

```
Reserved Notation "e '⇓' n"
                  (at level 50, left associativity).

Inductive aevalR : aexp → nat → Prop :=
  | E_ANum : ∀(n:nat),
      (ANum n) ⇓ n
  | E_APlus : ∀(a[1] a[2]: aexp) (n[1] n[2] : nat),
      (a[1] ⇓ n[1]) → (a[2] ⇓ n[2]) → (APlus a[1] a[2]) ⇓ (n[1] + n[2])
  | E_AMinus : ∀(a[1] a[2]: aexp) (n[1] n[2] : nat),
      (a[1] ⇓ n[1]) → (a[2] ⇓ n[2]) → (AMinus a[1] a[2]) ⇓ (n[1] - n[2])
  | E_AMult :  ∀(a[1] a[2]: aexp) (n[1] n[2] : nat),
      (a[1] ⇓ n[1]) → (a[2] ⇓ n[2]) → (AMult a[1] a[2]) ⇓ (n[1] * n[2])
  | E_ADiv :  ∀(a[1] a[2]: aexp) (n[1] n[2] n[3]: nat),
      (a[1] ⇓ n[1]) → (a[2] ⇓ n[2]) → (n[2] > 0) →
      (mult n[2] n[3] = n[1]) → (ADiv a[1] a[2]) ⇓ n[3]

where "a '⇓' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

```

    假设，相反，我们想要扩展算术运算

    由一个非确定性数生成器生成，当评估时，

    可能产生任何数字。（请注意，这与制作

    *概率*在所有可能的数字中进行选择——我们不是

    指定任何特定结果分布，而只是说

    什么结果是*可能的*。）

```
Reserved Notation "e '⇓' n" (at level 50, left associativity).

Inductive aexp : Type :=
  | AAny  : aexp                   (* <--- NEW *)
  | ANum : nat → aexp
  | APlus : aexp → aexp → aexp
  | AMinus : aexp → aexp → aexp
  | AMult : aexp → aexp → aexp.

```

    再次，扩展 aeval 将会很棘手，因为现在评估是

    *不*是从表达式到数字的确定性函数，而是

    扩展 aevalR 没有问题：

```
Inductive aevalR : aexp → nat → Prop :=
  | E_Any : ∀(n:nat),
      AAny ⇓ n                 (* <--- new *)
  | E_ANum : ∀(n:nat),
      (ANum n) ⇓ n
  | E_APlus : ∀(a[1] a[2]: aexp) (n[1] n[2] : nat),
      (a[1] ⇓ n[1]) → (a[2] ⇓ n[2]) → (APlus a[1] a[2]) ⇓ (n[1] + n[2])
  | E_AMinus : ∀(a[1] a[2]: aexp) (n[1] n[2] : nat),
      (a[1] ⇓ n[1]) → (a[2] ⇓ n[2]) → (AMinus a[1] a[2]) ⇓ (n[1] - n[2])
  | E_AMult :  ∀(a[1] a[2]: aexp) (n[1] n[2] : nat),
      (a[1] ⇓ n[1]) → (a[2] ⇓ n[2]) → (AMult a[1] a[2]) ⇓ (n[1] * n[2])

where "a '⇓' n" := (aevalR a n) : type_scope.

End aevalR_extended.

```

    此时，您可能会想：我应该使用哪种风格

    默认值？上面的例子表明关系定义是

    基本上比功能性更强大。对于情况

    像这样的情况，其中定义的事物不容易表达

    作为一个函数，或者确实不是一个函数，没有

    选择。但是当两种风格都可行时呢？

    支持关系定义的一个观点是，有些人

    感觉它们更加优雅和易于理解。另一个是

    Coq 自动生成漂亮的反演和归纳

    从归纳定义中的原则。

    另一方面，功能性定义通常更

    方便：

+   函数根据定义是确定性的，并且对所有参数进行定义；对于关系，如果需要这些属性，我们必须明确显示这些属性。

+   使用函数，我们还可以利用 Coq 的计算机制制简化证明过程中的表达式。

    此外，函数可以直接“提取”为可执行

    在 OCaml 或 Haskell 中的代码。

    最终，选��通常取决于具体情况。

    一个特定的情况或仅仅是品味问题。实际上，在

    在大型 Coq 开发中，通常会看到一个定义以

    *功能*和关系风格，再加上一个引理说明

    两者重合，允许进一步的证明从一个观点转换

    从一个视角到另一个视角。

```

# Expressions With Variables

    Let's turn our attention back to defining Imp.  The next thing we
    need to do is to enrich our arithmetic and boolean expressions
    with variables.  To keep things simple, we'll assume that all
    variables are global and that they only hold numbers.

```

## 状态

    由于我们将想要查找变量以了解它们当前的

    值，我们将从 Maps 章节中重用类型 id

    Imp 中变量的类型。

    *机器状态*（或者只是 *状态*）表示当前值

    在程序执行的某个时刻获取所有变量的值。

    为简单起见，我们假设状态已经定义好了

    *所有* 变量，尽管任何给定的程序只会

    提到它们的有限数量。状态捕获了所有

    存储在内存中的信息。对于 Imp 程序，因为每个

    变量存储一个自然数，我们可以将状态表示为

    从标识符到自然数的映射。���于更复杂的编程

    语言，状态可能具有更多结构。

```
Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.

```

## 语法

    我们可以通过在之前的算术表达式中添加变量来

    简单地添加一个构造函数：

```
Inductive aexp : Type :=
  | ANum : nat → aexp
  | AId : id → aexp                (* <----- NEW *)
  | APlus : aexp → aexp → aexp
  | AMinus : aexp → aexp → aexp
  | AMult : aexp → aexp → aexp.

```

    将一些变量名定义为符号缩写将使

    例子更容易阅读：

```
Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".

```

    （这种命名程序变量（X、Y、

    Z) 与我们之前使用大写字母表示

    类型。由于我们在章节中没有大量使用多态性

    开发到 Imp，这种重载不应该引起混淆。）

    bexps 的定义没有改变（除了使用新的

    aexps)：

```
Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp → aexp → bexp
  | BLe : aexp → aexp → bexp
  | BNot : bexp → bexp
  | BAnd : bexp → bexp → bexp.

```

## 评估

    算术和布尔表达式的评估器被扩展以处理

    变量的约定方式，以一个状态作为额外参数

    参数：

```
Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n ⇒ n
  | AId x ⇒ st x                                (* <----- NEW *)
  | APlus a[1] a[2] ⇒ (aeval st a[1]) + (aeval st a[2])
  | AMinus a[1] a[2]  ⇒ (aeval st a[1]) - (aeval st a[2])
  | AMult a[1] a[2] ⇒ (aeval st a[1]) * (aeval st a[2])
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       ⇒ true
  | BFalse      ⇒ false
  | BEq a[1] a[2]   ⇒ beq_nat (aeval st a[1]) (aeval st a[2])
  | BLe a[1] a[2]   ⇒ leb (aeval st a[1]) (aeval st a[2])
  | BNot b[1]     ⇒ negb (beval st b[1])
  | BAnd b[1] b[2]  ⇒ andb (beval st b[1]) (beval st b[2])
  end.

Example aexp1 :
  aeval (t_update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.

    Proof. reflexivity. Qed.

Example bexp1 :
  beval (t_update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.

    Proof. reflexivity. Qed.

```

# 命令

    现在我们准备定义 Imp 的语法和行为

    *命令*（有时称为 *语句*）有点冲突。

```

## Syntax

    Informally, commands c are described by the following BNF
    grammar.  (We choose this slightly awkward concrete syntax for the
    sake of being able to define Imp syntax using Coq's Notation
    mechanism.  In particular, we use IFB to avoid conflicting with
    the if notation from the standard library.)

```

c ::= SKIP | x ::= a | c ;; c | IFB b THEN c ELSE c FI

| WHILE b DO c END

    例如，在 Imp 中这是阶乘：

```
     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END

    When this command terminates, the variable Y will contain the
   factorial of the initial value of X. 

    Here is the formal definition of the abstract syntax of
    commands:

```

归纳定义 com : Type :=

| CSkip : com

| CAss : id → aexp → com

| CSeq : com → com → com

| CIf : bexp → com → com → com

| CWhile : bexp → com → com

```

    As usual, we can use a few Notation declarations to make things
    more readable.  To avoid conflicts with Coq's built-in notations,
    we keep this light — in particular, we don't introduce any
    notations for aexps and bexps to avoid confusion with the
    numeric and boolean operators we've already defined.

```

Notation "'SKIP'" :=

CSkip

Notation "x '::=' a" :=

（CAss x a）（在级别 60）。

Notation "c1 ;; c2" :=

(CSeq c[1] c[2]) (at level 80, right associativity)

Notation "'WHILE' b 'DO' c 'END'" :=

(CWhile b c) (at level 80, right associativity)

Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=

(CIf c[1] c[2] c[3]) (at level 80, right associativity)

```

    For example, here is the factorial function again, written as a
    formal definition to Coq:

```

Definition fact_in_coq : com :=

Z ::= AId X;;

Y ::= ANum 1;;

WHILE BNot (BEq (AId Z) (ANum 0)) DO

Y ::= AMult (AId Y) (AId Z);;

Z ::= AMinus (AId Z) (ANum 1)

END

```

## More Examples

    Assignment:

```

Definition plus2 : com :=

X ::= (APlus (AId X) (ANum 2))

Definition XtimesYinZ : com :=

Z ::= (AMult (AId X) (AId Y))

定义 subtract_slowly_body : com :=

Z ::= AMinus (AId Z) (ANum 1) ;;

X ::= AMinus (AId X) (ANum 1)

```

### Loops

```

Definition subtract_slowly : com :=

WHILE BNot (BEq (AId X) (ANum 0)) DO

subtract_slowly_body

END

定义 subtract_3_from_5_slowly : com :=

X ::= ANum 3 ;;

Z ::= ANum 5 ;;

subtract_slowly

```

### An infinite loop:

```

定义 loop : com :=

WHILE BTrue DO

SKIP

END

```

# Evaluating Commands

    Next we need to define what it means to evaluate an Imp command.
    The fact that WHILE loops don't necessarily terminate makes defining
    an evaluation function tricky...

```

## 作为一个函数的评估（失败的尝试）

    下面是为命令定义评估函数的尝试，

    省略 WHILE 情况。

```
Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP ⇒
        st
    | x ::= a[1] ⇒
        t_update st x (aeval st a[1])
    | c[1] ;; c[2] ⇒
        let st' := ceval_fun_no_while st c[1] in
        ceval_fun_no_while st' c[2]
    | IFB b THEN c[1] ELSE c[2] FI ⇒
        if (beval st b)
          then ceval_fun_no_while st c[1]
          else ceval_fun_no_while st c[2]
    | WHILE b DO c END ⇒
        st  (* bogus *)
  end.

```

    在传统的函数式编程语言如 OCaml 或

    Haskell 中我们可以添加 WHILE 情况如下：

```
  Fixpoint ceval_fun (st : state) (c : com) : state :=
    match c with
      ...
      | WHILE b DO c END =>
          if (beval st b)
            then ceval_fun st (c; WHILE b DO c END)
            else st
    end.

```

    Coq 不接受这样的定义（"错误：无法猜测

    修复 fix 的递减参数")，因为我们想要的函数

    定义并不保证终止。实际上，它*并不*总是

    终止：例如，ceval_fun 的完整版本

    应用于上述循环程序的函数永远不会

    终止。由于 Coq 不仅仅是一个函数式编程

    语言，而且是一致的逻辑，任何潜在的

    非终止函数需要被拒绝。这里是

    一个（无效的！）程序展示了如果 Coq 出了什么问题

    允许非终止递归函数：

```
         Fixpoint loop_false (n : nat) : False := loop_false n.

```

    也就是说，像 False 这样的命题将变得可证明

    (loop_false 0 would be a proof of False)，这

    对 Coq 的逻辑一致性将是一场灾难。

    因此，因为它不会在所有输入上终止，

    ceval_fun 的定义不能在 Coq 中写出 — 至少不能没有

    其他技巧和解决方法（参见章节 ImpCEvalFun

    如果你对这些感兴趣的话）。

```

## Evaluation as a Relation

    Here's a better way: define ceval as a *relation* rather than a
    *function* — i.e., define it in Prop instead of Type, as we
    did for aevalR above. 

    This is an important change.  Besides freeing us from awkward
    workarounds, it gives us a lot more flexibility in the definition.
    For example, if we add nondeterministic features like any to the
    language, we want the definition of evaluation to be
    nondeterministic — i.e., not only will it not be total, it will
    not even be a function! 

    We'll use the notation c / st ⇓ st' for the ceval relation:
    c / st ⇓ st' means that executing program c in a starting
    state st results in an ending state st'.  This can be
    pronounced "c takes state st to st'". 

### Operational Semantics

    Here is an informal definition of evaluation, presented as inference
    rules for readability:

           |

                        (E_Skip)  
           |

* * *

           |

                        SKIP / st ⇓ st
           |

                     |

                        aeval st a[1] = n
           |

                        (E_Ass)  
           |

* * *

           |

                        x := a[1] / st ⇓ (t_update st x n)
           |

                     |

                        c[1] / st ⇓ st'
           |

                     |

                        c[2] / st' ⇓ st''
           |

                        (E_Seq)  
           |

* * *

           |

                        c[1];;c[2] / st ⇓ st''
           |

                     |

                        beval st b[1] = true
           |

                     |

                        c[1] / st ⇓ st'
           |

                        (E_IfTrue)  
           |

* * *

           |

                        IF b[1] THEN c[1] ELSE c[2] FI / st ⇓ st'
           |

                     |

                        beval st b[1] = false
           |

                     |

                        c[2] / st ⇓ st'
           |

                        (E_IfFalse)  
           |

* * *

           |

                        IF b[1] THEN c[1] ELSE c[2] FI / st ⇓ st'
           |

                     |

                        beval st b = false
           |

                        (E_WhileEnd)  
           |

* * *

           |

                        WHILE b DO c END / st ⇓ st
           |

                     |

                        beval st b = true
           |

                     |

                        c / st ⇓ st'
           |

                     |

                        WHILE b DO c END / st' ⇓ st''
           |

                        (E_WhileLoop)  
           |

* * *

           |

                        WHILE b DO c END / st ⇓ st''
           |

                     |

    Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules.

```

保留记号 "c1 '/' st '⇓' st'"

（在第 40 级，st 在第 39 级）。

归纳定义 ceval：com → state → state → Prop :=

| E_Skip : ∀st，

SKIP / st ⇓ st

| E_Ass  : ∀st a[1] n x，

aeval st a[1] = n →

(x ::= a[1]) / st ⇓ (t_update st x n)

| E_Seq : ∀c[1] c[2] st st' st'',

c[1] / st  ⇓ st' →

c[2] / st' ⇓ st'' →

(c[1] ;; c[2]) / st ⇓ st''

| E_IfTrue : ∀st st' b c[1] c[2]，

beval st b = true →

c[1] / st ⇓ st' →

(IFB b THEN c[1] ELSE c[2] FI) / st ⇓ st'

| E_IfFalse : ∀st st' b c[1] c[2],

beval st b = false →

c[2] / st ⇓ st' →

(IFB b THEN c[1] ELSE c[2] FI) / st ⇓ st'

| E_WhileEnd : ∀b st c，

beval st b = false →

(WHILE b DO c END) / st ⇓ st

| E_WhileLoop : ∀st st' st'' b c，

beval st b = true →

c / st ⇓ st' →

(WHILE b DO c END) / st' ⇓ st'' →

(WHILE b DO c END) / st ⇓ st''

其中 "c1 '/' st '⇓' st'" := (ceval c[1] st st')。

```

    The cost of defining evaluation as a relation instead of a
    function is that we now need to construct *proofs* that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us.

```

例子 ceval_example1：

(X ::= ANum 2;;

IFB BLe (AId X) (ANum 1)

然后 Y ::= ANum 3

ELSE Z ::= ANum 4

FI）

/ empty_state

⇓ (t_update (t_update empty_state X 2) Z 4)。

证明。

(* 我们必须提供中间状态 *)

应用 E_Seq with (t_update empty_state X 2)。

- (* 赋值命令 *)

应用 E_Ass。反射性。

- (* if 命令 *)

应用 E_IfFalse。

反射性。

应用 E_Ass。反射性。证毕。

```

#### Exercise: 2 stars (ceval_example2)

```

例子 ceval_example2：

(X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ⇓

(t_update (t_update (t_update empty_state X 0) Y 1) Z 2)。

证明。

(* 在这里填写内容 *) 已承认。

```

    ☐ 

#### Exercise: 3 stars, advanced (pup_to_n)

    Write an Imp program that sums the numbers from 1 to
   X (inclusive: 1 + 2 + ... + X) in the variable Y.
   Prove that this program executes as intended for X = 2
   (this is trickier than you might expect).

```

定义 pup_to_n：com

(* 用 ":= _your_definition_ ." 替换这一行 *). 已承认。

定理 pup_to_2_ceval：

pup_to_n / (t_update empty_state X 2) ⇓

t_update (t_update (t_update (t_update (t_update (t_update empty_state

X 2) Y 0) Y 2) X 1) Y 3) X 0。

证明。

(* 在这里填写内容 *) 已承认。

```

    ☐

```

## 评估的确定性

    从计算定义转变为关系定义

    评估是一个��的举措，因为它使我们摆脱了人为的

    评估应该是一个全函数的要求。但是它

    也提出了一个问题：评估的第二个定义是什么

    真的是一个偏函数吗？或者可能是，从

    在相同的状态 st 下，我们可以评估一些命令 c

    达到两个不同输出状态 st'和的不同方式

    st''？

    实际上，这是不可能发生的：ceval *是*一个部分函数：

```
Theorem ceval_deterministic: ∀c st st[1] st[2],
     c / st ⇓ st[1]  →
     c / st ⇓ st[2] →
     st[1] = st[2].

    Proof.
  intros c st st[1] st[2] E[1] E[2].
  generalize dependent st[2].
  induction E[1];
           intros st[2] E[2]; inversion E[2]; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ[1].
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b[1] evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b[1] evaluates to false (contradiction) *)
      rewrite H in H[5]. inversion H[5].
  - (* E_IfFalse, b[1] evaluates to true (contradiction) *)
    rewrite H in H[5]. inversion H[5].
  - (* E_IfFalse, b[1] evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileEnd, b[1] evaluates to false *)
    reflexivity.
  - (* E_WhileEnd, b[1] evaluates to true (contradiction) *)
    rewrite H in H[2]. inversion H[2].
  - (* E_WhileLoop, b[1] evaluates to false (contradiction) *)
    rewrite H in H[4]. inversion H[4].
  - (* E_WhileLoop, b[1] evaluates to true *)
      assert (st' = st'0) as EQ[1].
      { (* Proof of assertion *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption. Qed.

```

# 关于 Imp 程序的推理

    我们将深入研究关于推理的系统技术

    在以下章节中的 Imp 程序，但我们可以做很多

    仅使用基本定义。本节探讨

    一些例子。

```
Theorem plus2_spec : ∀st n st',
  st X = n →
  plus2 / st ⇓ st' →
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.

```

    反演 Heval 基本上迫使 Coq 展开一步

    ceval 计算 - 在这种情况下揭示了 st'

    必须扩展为 X 的新值的 st，因为 plus2

    是一个赋值

```
  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq. Qed.

```

#### 练习：3 星，推荐 M（XtimesYinZ_spec）

    状态并证明 XtimesYinZ 的规范。

```
(* FILL IN HERE *)

```

    ☐

#### 练习：3 星，推荐（loop_never_stops）

```
Theorem loop_never_stops : ∀st st',
  ~(loop / st ⇓ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef
           eqn:Heqloopdef.

```

    通过对假设的推导进行归纳，展示

    loopdef 终止。大多数情况立即

    矛盾（因此可以在一步内解决

    反演）。

```
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星（无 whilesR）

    考虑以下函数：

```
Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP ⇒
      true
  | _ ::= _ ⇒
      true
  | c[1] ;; c[2] ⇒
      andb (no_whiles c[1]) (no_whiles c[2])
  | IFB _ THEN ct ELSE cf FI ⇒
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  ⇒
      false
  end.

```

    这个谓词仅在没有 while 的程序上返回 true

    循环。使用归纳，编写一个属性 no_whilesR，使得

    当 c 是一个没有时的程序时，no_whilesR c 是可证明的

    while 循环。然后证明它与 no_whiles 的等价性。

```
Inductive no_whilesR: com → Prop :=
 (* FILL IN HERE *)
.

Theorem no_whiles_eqv:
   ∀c, no_whiles c = true ↔ no_whilesR c.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：4 星 M（no_whiles_terminating）

    不涉及 while 循环的 Imp 程序总是终止。

    状态并证明一个定理 no_whiles_terminating，它说这个。使用 no_whiles 或 no_whilesR，根据您的喜好选择。

```
(* FILL IN HERE *)

```

    ☐

```

# Additional Exercises

#### Exercise: 3 stars (stack_compiler)

    HP Calculators, programming languages like Forth and Postscript
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a stack. For instance, the expression

```

    （2*3）+（3*（4-2））

```

    would be entered as

```

    2 3 * 3 4 2 - * +

```

    and evaluated like this (where we show the program being evaluated
   on the right and the contents of the stack on the left):

```

    [ ]           |    2 3 * 3 4 2 - * +

    [2]           |    3 * 3 4 2 - * +

    [3, 2]        |    * 3 4 2 - * +

    [6]           |    3 4 2 - * +

    [3, 6]        |    4 2 - * +

    [4, 3, 6]     |    2 - * +

    [2, 4, 3, 6]  |    - * +

    [2, 3, 6]     |    * +

    [6, 6]        |    +

    [12]          |

```

    The task of this exercise is to write a small compiler that
  translates aexps into stack machine instructions.

    The instruction set for our stack language will consist of the
  following instructions:

*   SPush n: Push the number n on the stack.

*   SLoad x: Load the identifier x from the store and push it on the stack

*   SPlus: Pop the two top numbers from the stack, add them, and push the result onto the stack.

*   SMinus: Similar, but subtract.

*   SMult: Similar, but multiply.

```

归纳 sinstr：类型 :=

| SPush：nat → sinstr

| SLoad：id → sinstr

| SPlus：sinstr

| SMinus：sinstr

| SMult：sinstr。

```

    Write a function to evaluate programs in the stack language. It
    should take as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and it should return the
    stack after executing the program.  Test your function on the
    examples below.

    Note that the specification leaves unspecified what to do when
    encountering an SPlus, SMinus, or SMult instruction if the
    stack contains less than two elements.  In a sense, it is
    immaterial what we do, since our compiler will never emit such a
    malformed program.

```

递归 s_execute（st：state）（stack：list nat）

（prog：list sinstr）

：list nat

(* 用":= _your_definition_ ."替换此行*）。已承认。

示例 s_execute1：

s_execute empty_state []

[SPush 5; SPush 3; SPush 1; SMinus]

= [2; 5]。

(* 在此填写 *)

示例 s_execute2：

s_execute（t_update empty_state X 3）[3;4]

[SPush 4; SLoad X; SMult; SPlus]

= [15; 4]。

(* 在此填写 *)

```

    Next, write a function that compiles an aexp into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack.

```

递归 s_compile（e：aexp）：list sinstr

(* 用":= _your_definition_ ."替换此行*）。已承认。

```

    After you've defined s_compile, prove the following to test
    that it works.

```

示例 s_compile1：

s_compile（AMinus（AId X）（AMult（ANum 2）（AId Y）））

= [SLoad X; SPush 2; SLoad Y; SMult; SMinus]。

(* 在此填写 *)

```

    ☐ 

#### Exercise: 4 stars, advanced (stack_compiler_correct)

    Now we'll prove the correctness of the compiler implemented in the
    previous exercise.  Remember that the specification left
    unspecified what to do when encountering an SPlus, SMinus, or
    SMult instruction if the stack contains less than two
    elements.  (In order to make your correctness proof easier you
    might find it helpful to go back and change your implementation!)

    Prove the following theorem.  You will need to start by stating a
    more general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma.

```

定理 s_compile_correct：∀（st：state）（e：aexp），

s_execute st []（s_compile e）= [ aeval st e ]。

证明。

(* 在此填写 *)

```

    ☐ 

#### Exercise: 3 stars, optional (short_circuit)

    Most modern programming languages use a "short-circuit" evaluation
    rule for boolean and: to evaluate BAnd b[1] b[2], first evaluate
    b[1].  If it evaluates to false, then the entire BAnd
    expression evaluates to false immediately, without evaluating
    b[2].  Otherwise, b[2] is evaluated to determine the result of the
    BAnd expression.

    Write an alternate version of beval that performs short-circuit
    evaluation of BAnd in this manner, and prove that it is
    equivalent to beval.

```

(* 在此填写 *)

```

    ☐

```

模块 BreakImp。

```

#### Exercise: 4 stars, advanced (break_imp)

    Imperative languages like C and Java often include a break or
    similar statement for interrupting the execution of loops. In this
    exercise we consider how to add break to Imp.  First, we need to
    enrich the language of commands with an additional case.

```

归纳 com：类型 :=

| CSkip：com

| CBreak：com               （<-- 新的）

| CAss：id → aexp → com

| CSeq：com → com → com

| CIf：bexp → com → com → com

| CWhile：bexp → com → com。

符号"'SKIP'"的表示法 :=

CSkip。

符号"'BREAK'"的表示法 :=

CBreak。

符号"x '::=' a"的表示法 :=

（CAss x a）（在级别 60 处）。

Notation "c1 ;; c2" :=

(CSeq c[1] c[2])（在级别 80，右结合）。

Notation "'WHILE' b 'DO' c 'END'" :=

(CWhile b c)（在级别 80，右结合）。

Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=

(CIf c[1] c[2] c[3])（在级别 80，右结合）。

```

    Next, we need to define the behavior of BREAK.  Informally,
    whenever BREAK is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the BREAK
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given BREAK. In those cases, BREAK should only
    terminate the *innermost* loop. Thus, after executing the
    following...

```

X ::= 0;;

Y ::= 1;;

WHILE 0 ≠ Y DO

WHILE TRUE DO

BREAK

END;;

X ::= 1;;

Y ::= Y - 1

END

    ... X 的值应为 1，而不是 0。

    表达这种行为的一种方式是向

    指定评估是否的评估关系

    命令执行 BREAK 语句：

```
Inductive result : Type :=
  | SContinue : result
  | SBreak : result.

Reserved Notation "c1 '/' st '⇓' s '/' st'"
                  (at level 40, st, s at level 39).

```

    直观地，c / st ⇓ s / st' 意味着，如果 c 在

    状态 st，那么它以状态 st' 终止，并且信号

    最内层周围循环（或整个程序）应该

    立即退出（s = SBreak）或继续执行

    正常（s = SContinue）。

    “c / st ⇓ s / st'”关系的定义非常

    与我们上面为常规评估给出的类似

    关系（c / st ⇓ st'）- 我们只需要处理

    终止信号适当：

+   如果命令是 SKIP，则状态不会改变，并且任何封闭循环的执行可以正常继续。

+   如果命令是 BREAK，则状态保持不变，但我们发出一个 SBreak 信号。

+   如果命令是赋值，则我们相应地更新状态中该变量的绑定，并发出执行可以正常继续的信号。

+   如果命令是 IFB b THEN c[1] ELSE c[2] FI 的形式，则状态更新如同 Imp 的原始语义一样，只是我们还传播了从执行任一分支中采取的信号。

+   如果命令是序列 c[1] ;; c[2]，我们首先执行 c[1]。如果这导致 SBreak，则跳过执行 c[2] 并将 SBreak 信号传播到周围的上下文；结果状态与仅执行 c[1] 获得的状态相同。否则，我们在执行 c[1] 后获得的状态上执行 c[2]，并传播在那里生成的信号。

+   最后，对于形式为 WHILE b DO c END 的循环，语义几乎与之前相同。唯一的区别是，当 b 评估为 true 时，我们执行 c 并检查它引发的信号。如果该信号是 SContinue，则执行过程与原始语义相同。否则，我们停止循环的执行，结果状态与当前迭代执行的结果状态相同。在任何情况下，由于 BREAK 仅终止最内层循环，WHILE 信号为 SContinue。

    根据上述描述，完成对以下定义的定义

    ceval 关系。

```
Inductive ceval : com → state → result → state → Prop :=
  | E_Skip : ∀st,
      CSkip / st ⇓ SContinue / st
  (* FILL IN HERE *)

  where "c1 '/' st '⇓' s '/' st'" := (ceval c[1] st s st').

```

    现在证明您对 ceval 的定义的以下属性：

```
Theorem break_ignore : ∀c st st' s,
     (BREAK;; c) / st ⇓ s / st' →
     st = st'.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem while_continue : ∀b c st st' s,
  (WHILE b DO c END) / st ⇓ s / st' →
  s = SContinue.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem while_stops_on_break : ∀b c st st',
  beval st b = true →
  c / st ⇓ SBreak / st' →
  (WHILE b DO c END) / st ⇓ SContinue / st'.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星，高级，可选（while_break_true）

```
Theorem while_break_true : ∀b c st st',
  (WHILE b DO c END) / st ⇓ SContinue / st' →
  beval st' b = true →
  ∃st'', c / st'' ⇓ SBreak / st'.
Proof.
(* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：4 星，高级，可选（ceval_deterministic）

```
Theorem ceval_deterministic: ∀(c:com) st st[1] st[2] s[1] s[2],
     c / st ⇓ s[1] / st[1]  →
     c / st ⇓ s[2] / st[2] →
     st[1] = st[2] ∧ s[1] = s[2].
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```
End BreakImp.

```

#### 练习：4 星，可选（add_for_loop）

    向命令语言添加 C 风格的 for 循环，更新

    ceval 定义以定义 for 循环的语义，并添加

    需要的 for 循环情况，以便此文件中的所有证明

    被 Coq 接受。

    一个 for 循环应该由（a）一条在每次迭代中执行的语句参数化

    最初，（b）在循环的每次迭代上运行的测试

    确定循环是否应该继续，（c）一个语句

    在每次循环迭代结束时执行，并且（d）一个语句

    构成循环主体的部分。（你不需要担心

    关于为循环制定一个具体的符号表示，但随意

    如果你喜欢的话，也可以玩一下这个。）

```
(* FILL IN HERE *)

```

    ☐

```
(* $Date: 2016-12-20 10:33:44 -0500 (Tue, 20 Dec 2016) $ *)

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
