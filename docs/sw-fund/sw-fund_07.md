# Coq 中的逻辑

```

```

需要导出的术语。

```

    In previous chapters, we have seen many examples of factual
    claims (*propositions*) and ways of presenting evidence of their
    truth (*proofs*).  In particular, we have worked extensively with
    *equality propositions* of the form e[1] = e[2], with
    implications (P → Q), and with quantified propositions (∀ x, P).  In this chapter, we will see how Coq can be used to carry
    out other familiar forms of logical reasoning.

    Before diving into details, let's talk a bit about the status of
    mathematical statements in Coq.  Recall that Coq is a *typed*
    language, which means that every sensible expression in its world
    has an associated type.  Logical claims are no exception: any
    statement we might try to prove in Coq has a type, namely Prop,
    the type of *propositions*.  We can see this with the Check
    command:

```

检查 3 = 3。

(* ===> Prop *)

检查 ∀n m : nat, n + m = m + n。

(* ===> Prop *)

```

    Note that *all* syntactically well-formed propositions have type
    Prop in Coq, regardless of whether they are true or not.

    Simply *being* a proposition is one thing; being *provable* is
    something else!

```

检查 ∀n : nat, n = 2。

(* ===> Prop *)

检查 3 = 4。

(* ===> Prop *)

```

    Indeed, propositions don't just have types: they are *first-class objects* that can be manipulated in the same ways as the other
    entities in Coq's world.  So far, we've seen one primary place
    that propositions can appear: in Theorem (and Lemma and
    Example) declarations.

```

定理 plus_2_2_is_4：

2 + 2 = 4。

证明。 反射性。 完成。

```

    But propositions can be used in many other ways.  For example, we
    can give a name to a proposition using a Definition, just as we
    have given names to expressions of other sorts.

```

定义 plus_fact : Prop := 2 + 2 = 4。

检查 plus_fact。

(* ===> plus_fact : Prop *)

```

    We can later use this name in any situation where a proposition is
    expected — for example, as the claim in a Theorem declaration.

```

定理 plus_fact_is_true：

plus_fact。

证明。 反射性。 完成。

```

    We can also write *parameterized* propositions — that is,
    functions that take arguments of some type and return a
    proposition. 

    For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three:

```

定义 is_three (n : nat) : Prop :=

n = 3。

检查 is_three。

(* ===> nat -> Prop *)

```

    In Coq, functions that return propositions are said to define
    *properties* of their arguments.

    For instance, here's a (polymorphic) property defining the
    familiar notion of an *injective function*.

```

定义 injective {A B} (f : A → B) :=

∀x y：A，f x = f y → x = y。

引理 succ_inj：injective S。

证明。

intros n m H。 反演 H。 反射性。

完成。

```

    The equality operator = is also a function that returns a
    Prop.

    The expression n = m is syntactic sugar for eq n m, defined
    using Coq's Notation mechanism. Because eq can be used with
    elements of any type, it is also polymorphic:

```

检查 @eq。

(* ===> forall A : Type, A -> A -> Prop *)

```

    (Notice that we wrote @eq instead of eq: The type
    argument A to eq is declared as implicit, so we need to turn
    off implicit arguments to see the full type of eq.)

```

# 逻辑连接词

## 连接

    命题 A 和 B 的 *合取*（或 *逻辑与*）

    是写成 A ∧ B，表示声明 A 和 B 都为真

    是真的。

```
Example and_example : 3 + 4 = 7 ∧ 2 * 2 = 4.

```

    要证明合取，使用 split 策略。 它将生成

    两个子目标，一个用于语句的每个部分：

```
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

```

    对于任何命题 A 和 B，如果我们假设 A 为真

    我们假设 B 为真，我们可以得出 A ∧ B 为真

    也是真的。

```
Lemma and_intro : ∀A B : Prop, A → B → A ∧ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

```

    由于将带有假设的定理应用于某个目标具有

    生成与假设数量相同的子目标的效果

    那个定理，我们可以应用 and_intro 来实现相同的效果

    如 split。

```
Example and_example' : 3 + 4 = 7 ∧ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

```

#### 练习：2 星 (and_exercise)

```
Example and_exercise :
  ∀n m : nat, n + m = 0 → n = 0 ∧ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    如此多地证明合取语句。 要进入另一个

    方向——即，*使用*合取假设来帮助证明

    其他——我们使用析构策略。

    如果证明上下文包含形式为 H 的假设

    A ∧ B，写成 destruct H as [HA HB] 将从中移除 H

    上下文并添加两个新的假设：HA，声明 A 为真

    真，和 HB，声明 B 为真。

```
Lemma and_example2 :
  ∀n m : nat, n = 0 ∧ m = 0 → n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

```

    通常，当我们介绍它时，我们也可以立即析构 H，

    而不是引入然后析构它：

```
Lemma and_example2' :
  ∀n m : nat, n = 0 ∧ m = 0 → n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

```

    你可能会想知道为什么我们费心打包两个假设 n = 0

    和 m = 0 合并为单个合取，因为我们也可以

    陈述了带有两个单独前提的定理：

```
Lemma and_example2'' :
  ∀n m : nat, n = 0 → m = 0 → n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

```

    对于这个定理，两种表述都可以。 但重要的是

    以了解如何处理合取假设，因为

    合取经常出现在证明的中间步骤中，

    特别是在更大的开发中。 以下是一个简单的例子：

```
Lemma and_example3 :
  ∀n m : nat, n + m = 0 → n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 ∧ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

```

    另一种常见的合取情况是我们知道

    A ∧ B 但在某些上下文中我们只需要 A（或只需要 B）。

    以下引理在这种情况下很有用：

```
Lemma proj1 : ∀P Q : Prop,
  P ∧ Q → P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.

```

#### 练习：1 星，可选 (proj2)

```
Lemma proj2 : ∀P Q : Prop,
  P ∧ Q → Q.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    最后，我们有时需要重新排列合取的顺序

    和/或多向合取的分组。 以下

    交换律和结合律定理在这种情况下很方便

    cases。

```
Theorem and_commut : ∀P Q : Prop,
  P ∧ Q → Q ∧ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. Qed.

```

#### 练习：2 星 (and_assoc)

    (在结合的下面证明中，请注意 *嵌套*

    引入模式将假设 H : P ∧ (Q ∧ R) 分解为

    HP：P，HQ：Q 和 HR：R。 完成证明从

    在这里。)

```
Theorem and_assoc : ∀P Q R : Prop,
  P ∧ (Q ∧ R) → (P ∧ Q) ∧ R.
Proof.
  intros P Q R [HP [HQ HR]].
  (* FILL IN HERE *) Admitted.

```

    ☐

    顺便说一句，中缀符号 ∧ 实际上只是句法糖

    是 and A B 的 Coq 运算符，它接受

    两个命题作为参数并产生一个命题。

```
Check and.
(* ===> and : Prop -> Prop -> Prop *)

```

## 析取

    另一个重要的连接词是*析取*，或*逻辑或*

    两个命题：A ∨ B 当 A 或 B 为真时

    是。（��者，我们可以写成 A B，其中 or：Prop → Prop → Prop。）

    在证明中使用析取假设，我们通过情况进行

    分析，就像对于 nat 或其他数据类型一样，可以完成

    用 destruct 或 intros。这是一个例子：

```
Lemma or_example :
  ∀n m : nat, n = 0 ∨ m = 0 → n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on      n = 0 ∨ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite ← mult_n_O.
    reflexivity.
Qed.

```

    相反，要证明析取成立，我们需要证明

    其中一方会。这是通过两种策略 left 和

    右。正如它们的名字所暗示的，第一个需要

    证明析取的左侧，而第二个

    需要证明其右侧。这是一个微不足道的用法...

```
Lemma or_intro : ∀A B : Prop, A → A ∨ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

```

    ...和一个稍微有趣的例子，需要左右两边

    和右：

```
Lemma zero_or_succ :
  ∀n : nat, n = 0 ∨ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

```

#### 练习：1 星（mult_eq_0）

```
Lemma mult_eq_0 :
  ∀n m, n * m = 0 → n = 0 ∨ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：1 星（or_commut）

```
Theorem or_commut : ∀P Q : Prop,
  P ∨ Q  → Q ∨ P.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

## 虚假和否定

    到目前为止，我们主要关注证明某些

    事情是*真的* — 加法是可交换的，追加列表是

    结合律等。当然，我们可能也对

    *负面*结果，显示某些命题*不是*

    真。在 Coq 中，这样的否定陈述用

    否定运算符 ¬。

    要了解否定的工作原理，请回顾 Tactics 章节中关于*爆炸原理*的讨论；它断言，如果我们

    假设有矛盾，那么任何其他命题都可以被推导出来。

    遵循这种直觉，我们可以将 ¬ P（“非 P”）定义为

    ∀ Q，P → Q。Coq 实际上做了一个稍微不同的

    选择，将 ¬ P 定义为 P → False，其中 False 是

    *特定*的矛盾命题定义在标准中

    库。

```
Module MyNot.

Definition not (P:Prop) := P → False.

Notation "¬ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.

```

    由于 False 是一个矛盾的命题，排中律原则

    爆炸也适用于它。如果我们在证明中得到 False

    上下文，我们可以将其分解以完成任何目标：

```
Theorem ex_falso_quodlibet : ∀(P:Prop),
  False → P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.

```

    拉丁文*ex falso quodlibet*的意思，字面上是“从虚假

    随你喜欢的方式进行”；这是另一个常见的名称

    爆炸原理。

#### 练习：2 星，可选（not_implies_our_not）

    证明 Coq 对否定的定义暗示了直观的定义

    如上所述：

```
Fact not_implies_our_not : ∀(P:Prop),
  ¬ P → (∀(Q:Prop), P → Q).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    这就是我们使用否定来陈述 0 和 1 是不同的

    nat 的元素：

```
Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

```

    这种不等式陈述是频繁的，值得

    特殊符号，x ≠ y：

```
Check (0 ≠ 1).
(* ===> Prop *)

Theorem zero_not_one' : 0 ≠ 1.
Proof.
  intros H. inversion H.
Qed.

```

    需要一点练习来习惯在否定中工作

    Coq。即使你可以很清楚地看到一个陈述

    涉及否定的命题是真的，一开始可能有点棘手

    将事物放置在正确的配置中，以便 Coq 可以理解

    它！这里有一些熟悉事实的证明，让你热身

    上。

```
Theorem not_False :
  ¬ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : ∀P Q : Prop,
  (P ∧ ¬P) → Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.

Theorem double_neg : ∀P : Prop,
  P → ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H. Qed.

```

#### 练习：2 星，高级，推荐（double_neg_inf）

    写一个非正式的 double_neg 证明：

    *定理*：P 暗示 ~~P，对于任何命题 P。

```
(* FILL IN HERE *)

```

    ☐

#### 练习：2 星，推荐（contrapositive）

```
Theorem contrapositive : ∀(P Q : Prop),
  (P → Q) → (¬Q → ¬P).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：1 星（not_both_true_and_false）

```
Theorem not_both_true_and_false : ∀P : Prop,
  ¬ (P ∧ ¬P).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：1 星，高级（informal_not_PNP）

    用英语写一个非正式的证明，证明 ∀ P：Prop，~（P ∧ ¬P）。

```
(* FILL IN HERE *)

```

    ☐

    同样���由于不等式涉及否定，它需要一个。

    有点练习就能流利地使用它。这里是一个。

    有用的技巧。如果你试图证明一个目标。

    荒谬的（例如，目标状态是 false = true），应用。

    ex_falso_quodlibet 将目标改为 False。这使得。

    更容易使用形如 ¬P 的假设，可能可用。

    在上下文中 — 特别是形如。

    x≠y。

```
Theorem not_true_is_false : ∀b : bool,
  b ≠ true → b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

```

    由于使用 ex_falso_quodlibet 推理是相当常见的，Coq。

    提供了一个内置策略，exfalso，用于应用它。

```
Theorem not_true_is_false' : ∀b : bool,
  b ≠ true → b = false.
Proof.
  intros [] H.
  - (* b = false *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = true *) reflexivity.
Qed.

```

## 真相

    除了 False，Coq 的标准库还定义了 True，一个。

    显然真的命题。为了证明它，我们使用。

    预定义常量 I：True。

```
Lemma True_is_true : True.
Proof. apply I. Qed.

```

    与 False 不同，True 的使用相当。

    很少，因为证明这个是微不足道的（因此无趣）。

    作为一个目标，并且作为一个假设没有带来有用的信息。

    但是在使用时定义复杂的 Props 时可能会非常有用。

    条件或作为高阶 Props 的参数。我们将。

    看到稍后的 True 的使用示例。

## 逻辑等价性

    方便的“当且仅当”连接词，断言两个。

    命题具有相同的真值，只是与之相连。

    两个蕴含。

```
Module MyIff.

Definition iff (P Q : Prop) := (P → Q) ∧ (Q → P).

Notation "P ↔ Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : ∀P Q : Prop,
  (P ↔ Q) → (Q ↔ P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. Qed.

Lemma not_true_iff_false : ∀b,
  b ≠ true ↔ b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. inversion H'.
Qed.

```

#### 练习：1 星，可选（iff_properties）

    使用上述证明 ↔ 是对称的（iff_sym）作为。

    一个指南，证明它也是自反的和传递的。

```
Theorem iff_refl : ∀P : Prop,
  P ↔ P.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem iff_trans : ∀P Q R : Prop,
  (P ↔ Q) → (Q ↔ R) → (P ↔ R).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星（or_distributes_over_and）

```
Theorem or_distributes_over_and : ∀P Q R : Prop,
  P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    Coq 的一些策略特殊处理 iff 语句，避免。

    一些低级别的证明状态操作。在。

    特别是，rewrite 和 reflexivity 可以与 iff 一起使用。

    陈述，不仅仅是相等。为了启用这种行为，我们需要。

    导入一个特殊的 Coq 库，允许与其他。

    除了相等之外的公式：

```
Require Import Coq.Setoids.Setoid.

```

    这里是一个简单的示例，演示这些策略如何与。

    当然。首先，让我们证明一些基本的当且仅当等价性...

```
Lemma mult_0 : ∀n m, n * m = 0 ↔ n = 0 ∨ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  ∀P Q R : Prop, P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

```

    我们现在可以使用这些事实与 rewrite 和 reflexivity 来。

    给出涉及等价性的陈述的顺利证明。这里是。

    之前 mult_0 结果的三元版本：

```
Lemma mult_0_3 :
  ∀n m p, n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

```

    apply 策略也可以与 ↔ 一起使用。当给出一个。

    等价性作为其参数，apply 会尝试猜测是哪一边。

    使用等价性。

```
Lemma apply_iff_example :
  ∀n m : nat, n * m = 0 → n = 0 ∨ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

```

## 存在量化

    另一个重要的逻辑连接词是*存在量化*。说有一些类型为 T 的 x。

    当某个属性 P 适用于 x 时，我们写成 ∃ x：T，P。与 ∀ 一样，类型注释：T 可以省略。

    Coq 能够从上下文推断出 x 的类型应该是什么。

    是。

    要证明形如 ∃ x，P 的陈述，我们必须展示。

    P 适用于某个特定的 x 值的选择，称为。

    *见证*存在。这是通过两个步骤完成的：首先，

    我们明确告诉 Coq 我们心目中的见证 t 是什么。

    调用策略 ∃ t。然后我们证明 P 在之后成立。

    所有 x 的出现都被 t 替换。

```
Lemma four_is_even : ∃n : nat, 4 = n + n.
Proof.
  ∃2\. reflexivity.
Qed.

```

    相反，如果我们有一个存在假设 ∃ x，P 在。

    上下文中，我们可以解构它以获得一个见证 x 和一个。

    假设 P 对 x 成立的假设。

```
Theorem exists_example_2 : ∀n,
  (∃m, n = 4 + m) →
  (∃o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit destruct here *)
  ∃(2 + m).
  apply Hm. Qed.

```

#### 练习：1 星（dist_not_exists）

    证明“对所有 x 成立的 P”意味着“没有 x 对

    P 不成立的地方。"

```
Theorem dist_not_exists : ∀(X:Type) (P : X → Prop),
  (∀x, P x) → ¬ (∃x, ¬ P x).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：2 星（dist_exists_or）

    证明存在量化在上面分布

    分离。

```
Theorem dist_exists_or : ∀(X:Type) (P Q : X → Prop),
  (∃x, P x ∨ Q x) ↔ (∃x, P x) ∨ (∃x, Q x).
Proof.
   (* FILL IN HERE *) Admitted.

```

    ☐

```

# Programming with Propositions

    The logical connectives that we have seen provide a rich
    vocabulary for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express the claim that an
    element x occurs in a list l.  Notice that this property has a
    simple recursive structure: 

*   If l is the empty list, then x cannot occur on it, so the property "x appears in l" is simply false. 

    *   Otherwise, l has the form x' :: l'. In this case, x occurs in l if either it is equal to x' or it occurs in l'. 

     We can translate this directly into a straightforward recursive function from taking an element and a list and returning a proposition:

```

递归函数 In {A：类型}（x：A）（l：列表 A）：命题 =

匹配 l 与

| [] ⇒ 假

| x' :: l' ⇒ x' = x ∨ In x l'

结束。

```

    When In is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions.

```

例子 In_example_1：In 4 [1; 2; 3; 4; 5]。

证明。

(* 在课堂上使用过的*)

简化。右。右。右。左。一致性。

Qed。

例子 In_example_2：

∀n, In n [2; 4] →

∃n'，n = 2 * n'。

证明。

(* 在课堂上使用过的*)

简化。

intros n [H | [H | []]]。

- ∃1\. 重写 ← H。一致性。

- ∃2\. 重写 ← H。一致性。

Qed.

```

    (Notice the use of the empty pattern to discharge the last case
    *en passant*.) 

    We can also prove more generic, higher-level lemmas about In.

    Note, in the next, how In starts out applied to a variable and
    only gets expanded when we do case analysis on this variable:

```

引理 In_map：

∀(A B : 类型) (f : A → B) (l : 列表 A) (x : A),

在 x l →

In（f x）（map f l）。

证明。

intros A B f l x。

对 l 进行归纳作为[|x' l' IHl']。

- (* l = nil, 矛盾 *)

简化。intros []。

- (* l = x' :: l' *)

简化。intros [H | H]。

+ 重写 H。左。一致性。

+ 右。应用 IHl'。应用 H。

Qed。

```

    This way of defining propositions recursively, though convenient
    in some cases, also has some drawbacks.  In particular, it is
    subject to Coq's usual restrictions regarding the definition of
    recursive functions, e.g., the requirement that they be "obviously
    terminating."  In the next chapter, we will see how to define
    propositions *inductively*, a different technique with its own set
    of strengths and limitations. 

#### Exercise: 2 stars (In_map_iff)

```

引理 In_map_iff：

∀（A B：类型）（f：A → B）（l：列表 A）（y：B），

在 y (map f l) ↔

∃x，f x = y ∧ In x l。

证明。

(* 在此处填写*）承认。

```

    ☐ 

#### Exercise: 2 stars (in_app_iff)

```

引理 in_app_iff：∀A l l' (a:A),

在（l++l'）中 a ↔ 在 l 中 a∨在 l'中 a。

证明。

(* 在此处填写*）承认。

```

    ☐ 

#### Exercise: 3 stars (All)

    Recall that functions returning propositions can be seen as
    *properties* of their arguments. For instance, if P has type
    nat → Prop, then P n states that property P holds of n.

    Drawing inspiration from In, write a recursive function All
    stating that some property P holds of all elements of a list
    l. To make sure your definition is correct, prove the All_In
    lemma below.  (Of course, your definition should *not* just
    restate the left-hand side of All_In.)

```

递归函数 All {T : 类型} (P : T → 命题) (l : 列表 T) : 命题

(* 用":= _your_definition_ ." 替换此行*). 承认。

引理 All_In：

∀T（P：T → 命题）（l：列表 T），

(∀x, In x l → P x) ↔

所有 P l。

证明。

(* 在此处填写*）承认。

```

    ☐ 

#### Exercise: 3 stars (combine_odd_even)

    Complete the definition of the combine_odd_even function below.
    It takes as arguments two properties of numbers, Podd and
    Peven, and it should return a property P such that P n is
    equivalent to Podd n when n is odd and equivalent to Peven n
    otherwise.

```

定义 combine_odd_even（Podd Peven：自然数 → 命题）：自然数 → 命题

(* 用":= _your_definition_ ." 替换此行*). 承认。

```

    To test your definition, prove the following facts:

```

定理 combine_odd_even_intro：

∀(Podd Peven : 自然数 → 命题) (n : 自然数),

(oddb n = true → Podd n) →

(oddb n = false → Peven n) →

combine_odd_even Podd Peven n。

证明。

(* 在此处填写*）承认。

定理 combine_odd_even_elim_odd：

∀(Podd Peven : 自然数 → 命题) (n : 自然数),

combine_odd_even Podd Peven n →

oddb n = true →

Podd n。

证明。

(* 在此处填写*）承认。

定理 combine_odd_even_elim_even：

∀(Podd Peven : 自然数 → 命题) (n : 自然数),

combine_odd_even Podd Peven n →

oddb n = false →

Peven n。

证明。

(* 在此处填写*）承认。

```

    ☐

```

# 将定理应用于参数

    Coq 的一个特点是它与许多其他证明系统不同的地方

    助手是将*证明*视为一等对象的特点。

    这方面有很多值得讨论的地方，但不是

    详细了解它以便使用 Coq。 这

    此节只是一个简单的介绍，深入探讨可以

    可在可选章节 ProofObjects 和

    IndPrinciples。

    我们已经看到，我们可以使用 Check 命令来询问 Coq

    打印表达式的类型。 我们也可以使用 Check 来询问

    特定标识符指的是哪个定理。

```
Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)

```

    Coq 以相同的方式打印 plus_comm 定理的*陈述*

    它以打印我们要求的任何术语的*类型*的方式

    检查。 为什么？

    原因是标识符 plus_comm 实际上指的是

    *证明对象* — 代表一个逻辑的数据结构

    建立了∀ n m：nat，n + m = m + n 的陈述的推导。这个对象的类型*是*该陈述

    它所证明的定理的类型。

    直观上，这是有道理的，因为一个定理的陈述

    告诉我们可以使用该定理的内容，就像一个

    计算对象告诉我们可以用该对象做什么——

    例如，如果我们有一个类型为 nat → nat → nat 的术语，我们可以给出

    它两个 nats 作为参数，然后得到一个 nat。同样，如果我们

    有一个类型为 n = m → n + n = m + m 的对象，我们提供它

    一个类型为 n = m 的“参数”，我们可以推导出 n + n = m + m。

    在操作上，这个类比甚至更进一步：通过应用一个

    定理，就像它是一个函数，对具有匹配的假设

    类型，我们可以专门化其结果，而无需求助于

    中间断言。例如，假设我们想要证明

    以下结果：

```
Lemma plus_comm3 :
  ∀n m p, n + (m + p) = (p + m) + n.

```

    乍看之下，我们应该能够证明这一点

    通过两次重写加上 plus_comm 使两边匹配。

    然而，问题在于第二次重写将撤消

    第一个的效果。

```
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)
Abort.

```

    修复这个问题的一个简单方法是，只使用我们的工具

    已知，是使用 assert 推导出一个专门化版本

    可以用于精确重写的 plus_comm 的版本

    想要的。

```
Lemma plus_comm3_take2 :
  ∀n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  assert (H : m + p = p + m).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

```

    一个更优雅的替代方法是直接将 plus_comm 应用于

    我们想要实例化它的参数，方式与

    我们将一个多态函数应用于一个类型参数时。

```
Lemma plus_comm3_take3 :
  ∀n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity.
Qed.

```

    您可以以几乎所有方式“将定理用作函数”使用

    接受定理名称作为参数的策略。还要注意

    定理应用使用与函数相同的推理机制

    应用；因此，例如，可以提供

    通配符作为要推断的参数，或者声明一些

    默认情况下将一个定理的假设声明为隐式。这些特性

    在下面的证明中进行了说明。

```
Example lemma_application_ex :
  ∀{n : nat} {ns : list nat},
    In n (map (fun m ⇒ m * 0) ns) →
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite ← Hm. reflexivity.
Qed.

```

    我们将在后面的章节中看到这一部分的习语的更多示例

    后续章节。

```

# Coq vs. Set Theory

    Coq's logical core, the *Calculus of Inductive Constructions*,
    differs in some important ways from other formal systems that are
    used by mathematicians for writing down precise and rigorous
    proofs.  For example, in the most popular foundation for
    mainstream paper-and-pencil mathematics, Zermelo-Fraenkel Set
    Theory (ZFC), a mathematical object can potentially be a member of
    many different sets; a term in Coq's logic, on the other hand, is
    a member of at most one type.  This difference often leads to
    slightly different ways of capturing informal mathematical
    concepts, but these are, by and large, quite natural and easy to
    work with.  For example, instead of saying that a natural number
    n belongs to the set of even numbers, we would say in Coq that
    ev n holds, where ev : nat → Prop is a property describing
    even numbers.

    However, there are some cases where translating standard
    mathematical reasoning into Coq can be either cumbersome or
    sometimes even impossible, unless we enrich the core logic with
    additional axioms.  We conclude this chapter with a brief
    discussion of some of the most significant differences between the
    two worlds. 

## Functional Extensionality

    The equality assertions that we have seen so far mostly have
    concerned elements of inductive types (nat, bool, etc.).  But
    since Coq's equality operator is polymorphic, these are not the
    only possibilities — in particular, we can write propositions
    claiming that two *functions* are equal to each other:

```

示例 function_equality_ex[1]：plus 3 = plus (pred 4)。

    证明。反射性。Qed。

```

    In common mathematical practice, two functions f and g are
    considered equal if they produce the same outputs:

```

(∀x，f x = g x) → f = g

    这被称为*功能性外延性*原则。

    非正式地说，一个“外延性属性”是

    与对象的可观察行为有关。因此，功能性

    外延性简单地意味着函数的身份是

    完全由我们可以从中观察到的东西决定——即，在

    Coq 术语，我们在应用后获得的结果。

    函数外延性不是 Coq 的基本公理的一部分。这

    意味着一些“合理”的命题是无法证明的。

```
Example function_equality_ex[2] :
  (fun x ⇒ plus x 1) = (fun x ⇒ plus 1 x).
Proof.
   (* Stuck *)
Abort.

```

    但是，我们可以将函数外延性添加到 Coq 的核心逻辑中

    使用 Axiom 命令。

```
Axiom functional_extensionality : ∀{X Y: Type}
                                    {f g : X → Y},
  (∀(x:X), f x = g x) → f = g.

```

    使用 Axiom 与陈述定理具有相同的效果，并且

    跳过使用 Admitted 的证明，但它提醒读者

    这不仅仅是我们要回来填写的东西

    以后！

    我们现在可以在证明中调用函数外延性：

```
Example function_equality_ex[2] :
  (fun x ⇒ plus x 1) = (fun x ⇒ plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

```

    当向 Coq 的核心逻辑添加新的公理时，我们必须小心

    逻辑，因为它们可能使其*不一致*—也就是说，它们可能

    使得每个命题都可以被证明，包括 False！

    不幸的是，没有简单的方法来告诉一个公理是否

    添加是安全的：通常需要大量工作来确定

    一致性的任何特定组合。

    然而，众所周知，添加函数外延性，在

    特别是，*是*一致的。

    要检查特定的证明是否依赖于任何额外的

    公理，使用 Print Assumptions 命令。

```
Print Assumptions function_equality_ex[2].
(* ===>      Axioms:      functional_extensionality :          forall (X Y : Type) (f g : X -> Y),                 (forall x : X, f x = g x) -> f = g *)

```

#### 练习：4 星（tr_rev）

    列表反转函数的定义之一存在的问题是

    我们有的 rev 这一点是它在每个

    步骤；运行 app 需要的时间与大小成线性关系

    的列表，这意味着 rev 具有二次运行时间。

    我们可以通过以下定义改进这一点：

```
Fixpoint rev_append {X} (l[1] l[2] : list X) : list X :=
  match l[1] with
  | [] ⇒ l[2]
  | x :: l[1]' ⇒ rev_append l[1]' (x :: l[2])
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

```

    此版本被称为*尾递归*，因为递归的

    对函数的调用是需要的最后一个操作

    执行（即，我们不必在递归后执行++）。

    调用）；一个体面的编译器将生成非常高效的代码

    情况。 证明这两个定义确实是等价的。

```
Lemma tr_rev_correct : ∀X, @tr_rev X = @rev X.
(* FILL IN HERE *) Admitted.

```

    ☐

## 命题和布尔值

    我们已经看到了两种在 Coq 中对逻辑事实进行编码的不同方式：

    与 *布尔*（类型为 bool）和 *命题*（类型为

    Prop）。

    例如，要声明一个数字 n 是偶数，我们可以说

    要么

+   （1）即 evenb n 返回 true，或

+   （2）存在某个 k 使得 n = double k。实际上，这两种偶数概念是等价的，可以很容易地通过几个辅助引理来证明。

    我们经常说布尔 evenb n *反映*命题

    ∃ k, n = double k。

```
Theorem evenb_double : ∀k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

```

#### 练习：3 星（evenb_double_conv）

```
Theorem evenb_double_conv : ∀n,
  ∃k, n = if evenb n then double k
                else S (double k).
Proof.
  (* Hint: Use the evenb_S lemma from Induction.v. *)
  (* FILL IN HERE *) Admitted.

```

    ☐

```
Theorem even_bool_prop : ∀n,
  evenb n = true ↔ ∃k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. ∃k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

```

    同样地，要声明两个数字 n 和 m 相等，我们可以

    要么说（1）即 beq_nat n m 返回 true，要么说（2）即 n = m。 这两种概念是等价的。

```
Theorem beq_nat_true_iff : ∀n[1] n[2] : nat,
  beq_nat n[1] n[2] = true ↔ n[1] = n[2].
Proof.
  intros n[1] n[2]. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite ← beq_nat_refl. reflexivity.
Qed.

```

    然而，虽然布尔和命题形式的

    声称在纯逻辑上是等价的，它们需要

    不会在操作上等价。 相等提供了一个极端

    例如：知道 beq_nat n m = true 通常意义不大

    在涉及 n 和 m 的证明中间直接帮助;

    然而，如果我们将陈述转换为等价形式 n = m，我们可以重写它。

    偶数的情况也很有趣。 回想一下，

    当证明 even_bool_prop 的反向方向时（即，

    evenb_double，从命题到布尔

    声称），我们对 k 进行了简单的归纳。 另一方面，该

    反之（evenb_double_conv 练习）需要一个巧妙

    泛化，因为我们不能直接证明 (∃ k, n = double k) → evenb n = true。

    对于这些例子，命题性声明比

    它们的布尔对应物，但并非总是如此。 对于

    举例来说，我们无法测试一个一般命题是否为真或者

    不在函数定义中； 因此，以下代码

    片段被拒绝：

```
Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

```

    Coq 抱怨 n = 2 具有类型 Prop，而它期望一个

    bool 元素（��其他具有两个的归纳类型

    元素）。这个错误消息的原因与

    Coq 核心语言的*计算*性质，这是设计的

    以便它能表达的每个函数都是可计算的和

    总共。这样做的一个原因是为了允许提取

    从 Coq 开发中执行的可执行程序。因此，

    Coq 中的 Prop 没有普遍的案例分析操作

    告诉任何给定命题是真还是假，因为这样的

    一个操作将允许我们编写不可计算的函数。

    尽管一般的不可计算属性不能被表述为

    布尔计算，值得注意的是，即使许多

    *可计算*属性更容易使用 Prop 表达

    bool，因为递归函数定义受到

    Coq 中的重要限制。例如，下一章

    展示如何定义正则表达式匹配的属性

    使用 Prop 来处理给定的字符串。使用 bool 做同样的事情

    编写一个正则表达式匹配器，这将是

    更复杂，更难理解，更难推理

    关于。

    相反，使用陈述事实的一个重要的附带好处是

    通过计算使一些证明自动化成为可能

    与 Coq 术语一起使用，一种称为*反射证明*的技术。考虑以下陈述：

```
Example even_1000 : ∃k, 1000 = double k.

```

    这个事实的最直接证明是给出 k 的值

    明确地简化。

```
Proof. ∃500\. reflexivity. Qed.

```

    另一方面，相应布尔值的证明

    陈述甚至更简单：

```
Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

```

    有趣的是，由于这两个概念是等价的，

    我们可以使用布尔形式来证明另一个，而不需要

    明确提到值 500：

```
Example even_1000'' : ∃k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

```

    尽管在这方面我们没有取得太多的证明大小

    情况下，更大的证明通常可以通过

    使用反射。作为一个极端的例子，Coq 证明了

    著名的*四色定理*使用反射来简化

    数百个不同情况到一个布尔计算。我们不会

    在大量细节中涵盖反射，但它作为一个很好的例子

    展示布尔值和一般的互补优势

    命题。

#### 练习：2 星（逻辑连接词）

    以下引理涉及研究的命题连接词

    在本章中对应的布尔运算。

```
Lemma andb_true_iff : ∀b[1] b[2]:bool,
  b[1] && b[2] = true ↔ b[1] = true ∧ b[2] = true.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma orb_true_iff : ∀b[1] b[2],
  b[1] || b[2] = true ↔ b[1] = true ∨ b[2] = true.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：1 星（beq_nat_false_iff）

    以下定理是对"负面"表述的替代形式

    beq_nat_true_iff 在某些情况下更方便

    情况（我们将在后面的章节中看到例子）。

```
Theorem beq_nat_false_iff : ∀x y : nat,
  beq_nat x y = false ↔ x ≠ y.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星（beq_list）

    给定一个用于测试元素相等性的布尔运算符 beq

    一些类型 A，我们可以定义一个用于测试的函数 beq_list beq

    具有元素在 A 中的列表的相等性。完成定义

    下面的 beq_list 函数。为了确保您的

    定义是正确的，证明引理 beq_list_true_iff。

```
Fixpoint beq_list {A : Type} (beq : A → A → bool)
                  (l[1] l[2] : list A) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma beq_list_true_iff :
  ∀A (beq : A → A → bool),
    (∀a[1] a[2], beq a[1] a[2] = true ↔ a[1] = a[2]) →
    ∀l[1] l[2], beq_list beq l[1] l[2] = true ↔ l[1] = l[2].
Proof.
(* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：2 星，推荐（All_forallb）

    回想一下，来自练习中的 forallb 函数

    forall_exists_challenge 在章节 Tactics 中：

```
Fixpoint forallb {X : Type} (test : X → bool) (l : list X) : bool :=
  match l with
  | [] ⇒ true
  | x :: l' ⇒ andb (test x) (forallb test l')
  end.

```

    证明下面的定理，它将 forallb 与 All 关联起来

    上述练习的性质。

```
Theorem forallb_true_iff : ∀X test (l : list X),
   forallb test l = true ↔ All (fun x ⇒ test x = true) l.
Proof.
  (* FILL IN HERE *) Admitted.

```

    函数 forallb 的重要属性有哪些

    这些规范无法捕捉到吗？

```
(* FILL IN HERE *)

```

    ☐

## 经典逻辑与构造性逻辑

    我们已经看到无法测试一个

    命题 P 在定义 Coq 函数时成立。你可能会

    惊讶地发现类似的限制也适用于*证明*！

    换句话说，以下直观的推理原则不成立

    在 Coq 中可推导：

```
Definition excluded_middle := ∀P : Prop,
  P ∨ ¬ P.

```

    要在操作上理解为什么会这样，回想一下

    为了证明形式为 P ∨ Q 的陈述，我们使用左

    和右策略，实际上需要知道哪一边

    析取的命题成立。但普遍量化的 P 在

    excluded_middle 是一个*任意*命题，我们知道

    什么都不知道。我们没有足够的信息来选择哪个

    左边或右边要应用，就像 Coq 没有足够的

    信息来机械地决定 P 在内部是成立还是不成立。

    一个函数。

    然而，如果我们碰巧知道 P 在某些地方反映出来

    布尔术语 b，那么知道它是否成立或不成立是微不足道的：

    我们只需检查 b 的值。

```
Theorem restricted_excluded_middle : ∀P b,
  (P ↔ b = true) → P ∨ ¬ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

```

    特别是，排中律对于方程 n = m 是有效的，

    两个自然数 n 和 m 之间。

```
Theorem restricted_excluded_middle_eq : ∀(n m : nat),
  n = m ∨ n ≠ m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (beq_nat n m)).
  symmetry.
  apply beq_nat_true_iff.
Qed.

```

    看起来奇怪的是，一般的排中律不是

    Coq 中默认可用；毕竟，任何给定的声明必须是

    要么是真的，要么是假的。尽管如此，不

    假设排中律：Coq 中的陈述可以做出更强的

    声称比标准数学中的类似陈述更强。

    值得注意的是，如果存在 Coq 证明 ∃ x, P x，那么

    明确展示一个值 x，我们可以

    证明 P x — 换句话说，每个存在的证明都是

    必须是*构造性*的。

    类似 Coq 的逻辑，不假设排中律，

    被称为*构造性逻辑*。

    更传统的逻辑系统，如 ZFC，在其中

    排中律是否适用于任意命题，都被称���

    称为*经典*。

    以下示例说明了为什么假设排中律

    可能导致非构造性证明：

    *声明*：存在无理数 a 和 b，使得 a ^ b 是有理数。

    *证明*：很容易证明 sqrt 2 是无理数。

    如果 sqrt 2 ^ sqrt 2 是有理数，只需取 a = b = sqrt 2 就可以了。否则，sqrt 2 ^ sqrt 2 是

    无理数。在这种情况下，我们可以取 a = sqrt 2 ^ sqrt 2 和

    b = sqrt 2，因为 a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^ 2 = 2。 ☐

    你看到这里发生了什么吗？我们使用排中律来

    分别考虑 sqrt 2 ^ sqrt 2 是有理数的情况

    而不知道哪一个实际上成立！

    由于这个原因，我们最终知道这样的 a 和 b 存在

    但我们无法确定它们的实际值是什么（至少

    使用这种论证方式）。

    尽管建设性逻辑很有用，但它也有局限性：

    有许多陈述在古典逻辑中很容易证明。

    逻辑，但具有更复杂的建设性证明，并且

    有一些已知没有建设性证明的

    全部！幸运的是，像函数外延性一样，排除

    中间是已知与 Coq 的逻辑兼容的，使我们能够

    安全地添加它作为公理。但是，在

    这本书中：我们涵盖的结果可以完全发展

    在建设性逻辑中几乎没有额外成本。

    需要一些实践来理解哪些证明技术必须

    在建设性推理中应避免，但通过论证

    矛盾，特别是以臭名昭著的方式导致

    非建设性证明。这里是一个典型的例子：假设

    我们想要展示存在具有某种属性 P 的 x，

    即，使得 P x。我们首先假设我们的结论

    是错误的；也就是说，¬ ∃ x, P x。从这个前提出发，不

    难以推导出 ∀ x, ¬ P x。如果我们设法证明这一点

    中间事实导致矛盾，我们得到一个

    存在证明而从未展示出 x 的值

    P x 成立！

    从建设性的角度来看，这里的技术缺陷是

    我们声称使用证明 ∃ x, P x 来证明

    ¬ ¬ (∃ x, P x)。允许我们去除双重

    从任意陈述中推导出否定等同于假设

    排除中间，如下面的一个练习所示。因此，

    这种推理不能在不假设的情况下编码到 Coq 中

    额外的公理。

#### 练习：3 星（excluded_middle_irrefutable）

    Coq 与普遍排除中间公理的一致性

    需要复杂的推理，无法在内部执行

    Coq 本身。但是，以下定理暗示着它是

    始终可以假设一个可决定性公理（即，一个实例

    任何*特定* Prop P。为什么？因为我们

    无法证明这种公理的否定；如果我们可以，我们将

    同时具有¬ (P ∨ ¬P) 和 ¬ ¬ (P ∨ ¬P)，矛盾。

```
Theorem excluded_middle_irrefutable:  ∀(P:Prop),
  ¬ ¬ (P ∨ ¬ P).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星，高级（not_exists_dist）

    这是古典逻辑的一个定理，以下两个

    断言是等价的：

```
    ¬ (∃x, ¬ P x)
    ∀x, P x

    The dist_not_exists theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle.

```

定理 not_exists_dist：

排除中间 →

∀(X:Type) (P : X → Prop)，

¬ (∃x, ¬ P x) → (∀x, P x)。

证明。

(* 在这里填写 *) Admitted。

```

    ☐ 

#### Exercise: 5 stars, optional (classical_axioms)

    For those who like a challenge, here is an exercise taken from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following four statements, together with excluded_middle, can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.

    Prove that all five propositions (these four plus
    excluded_middle) are equivalent.

```

定义 peirce := ∀P Q: Prop，

((P→Q)→P)→P。

定义 double_negation_elimination := ∀P:Prop，

~~P → P。

定义 de_morgan_not_and_not := ∀P Q:Prop，

~(~P ∧ ¬Q) → P∨Q。

定义 implies_to_or := ∀P Q:Prop，

(P→Q) → (¬P∨Q)。

(* 在这里填写 *)

```

    ☐ 

```

```

```

```

```

```

```
