# 用于 Coq 的 UseTacticsTactic 库：温和介绍

```

```

(* 由 Arthur Chargueraud 编写和维护的章节*)

```

    Coq comes with a set of builtin tactics, such as reflexivity,
    intros, inversion and so on. While it is possible to conduct
    proofs using only those tactics, you can significantly increase
    your productivity by working with a set of more powerful tactics.
    This chapter describes a number of such useful tactics, which, for
    various reasons, are not yet available by default in Coq.  These
    tactics are defined in the LibTactics.v file.

```

导入 Coq.Arith.Arith。

导入 Maps。

导入 Imp。

导入 Types。

导入 Smallstep。

导入 LibTactics。

```

    Remark: SSReflect is another package providing powerful tactics.
    The library "LibTactics" differs from "SSReflect" in two respects:

*   "SSReflect" was primarily developed for proving mathematical theorems, whereas "LibTactics" was primarily developed for proving theorems on programming languages. In particular, "LibTactics" provides a number of useful tactics that have no counterpart in the "SSReflect" package.

*   "SSReflect" entirely rethinks the presentation of tactics, whereas "LibTactics" mostly stick to the traditional presentation of Coq tactics, simply providing a number of additional tactics. For this reason, "LibTactics" is probably easier to get started with than "SSReflect".

    This chapter is a tutorial focusing on the most useful features
    from the "LibTactics" library. It does not aim at presenting all
    the features of "LibTactics". The detailed specification of tactics
    can be found in the source file LibTactics.v. Further documentation
    as well as demos can be found at [`www.chargueraud.org/softs/tlc/`](http://www.chargueraud.org/softs/tlc/). 

    In this tutorial, tactics are presented using examples taken from
    the core chapters of the "Software Foundations" course. To illustrate
    the various ways in which a given tactic can be used, we use a
    tactic that duplicates a given goal. More precisely, dup produces
    two copies of the current goal, and dup n produces n copies of it.

```

# 介绍和案例分析策略

    本节介绍以下策略：

+   introv，用于更有效地命名假设，

+   inverts，用于改进反演策略，

+   cases，用于执行案例分析而不丢失信息，

+   cases_if，用于自动化对 if 参数进行案例分析。

```

## The Tactic introv

```

模块 IntrovExamples。

导入 Stlc。

导入 Imp。

导入 STLC。

```

    The tactic introv allows to automatically introduce the
    variables of a theorem and explicitly name the hypotheses
    involved. In the example shown next, the variables c,
    st, st[1] and st[2] involved in the statement of determinism
    need not be named explicitly, because their name where already
    given in the statement of the lemma. On the contrary, it is
    useful to provide names for the two hypotheses, which we
    name E[1] and E[2], respectively.

```

定理 ceval_deterministic：∀c st st[1] st[2]，

c / st ⇓ st[1] →

c / st ⇓ st[2] →

st[1] = st[2]。

证明。

introv E[1] E[2]. (* was intros c st st[1] st[2] E[1] E[2] *)

放弃。

```

    When there is no hypothesis to be named, one can call
    introv without any argument.

```

定理 dist_exists_or：∀(X:Type) (P Q : X → Prop)，

(∃x，P x ∨ Q x) ↔ (∃x，P x) ∨ (∃x，Q x)。

证明。

introv。(* was intros X P Q *)

放弃。

```

    The tactic introv also applies to statements in which
    ∀ and → are interleaved.

```

定理 ceval_deterministic'：∀c st st[1]，

(c / st ⇓ st[1]) → ∀st[2]，(c / st ⇓ st[2]) → st[1] = st[2]。

证明。

introv E[1] E[2]. (* was intros c st st[1] E[1] st[2] E[2] *)

放弃。

```

    Like the arguments of intros, the arguments of introv
    can be structured patterns.

```

定理 exists_impl：∀X (P : X → Prop) (Q : Prop) (R : Prop)，

(∀x，P x → Q) →

((∃x，P x) → Q)。

证明。

introv [x H[2]]。eauto。

(* same as intros X P Q R H[1] [x H[2]].，这本身是 intros X P Q R H[1] H[2]的简写。destruct H[2] as [x H[2]]。*)

完成。

```

    Remark: the tactic introv works even when definitions
    need to be unfolded in order to reveal hypotheses.

```

模块 IntrovExamples。

```

## The Tactic inverts

```

模块 InvertsExamples。

导入 Stlc。

导入 Equiv。

导入 Imp。

导入 STLC。

```

    The inversion tactic of Coq is not very satisfying for
    three reasons. First, it produces a bunch of equalities
    which one typically wants to substitute away, using subst.
    Second, it introduces meaningless names for hypotheses.
    Third, a call to inversion H does not remove H from the
    context, even though in most cases an hypothesis is no longer
    needed after being inverted. The tactic inverts address all
    of these three issues. It is intented to be used in place of
    the tactic inversion. 

    The following example illustrates how the tactic inverts H
    behaves mostly like inversion H except that it performs
    some substitutions in order to eliminate the trivial equalities
    that are being produced by inversion.

```

定理 skip_left：∀c，

cequiv (SKIP;; c) c。

证明。

introv。分割；引入 H。

dup。(* 复制目标以进行比较*)

(* was... *)

- 反演 H。替换。反演 H[2]。替换。假设。

(* 现在... *)

- 反演 H。反演 H[2]。假设。

放弃。

```

    A slightly more interesting example appears next.

```

定理 ceval_deterministic：∀c st st[1] st[2]，

c / st ⇓ st[1] →

c / st ⇓ st[2] →

st[1] = st[2]。

证明。

introv E[1] E[2]。推广依赖于 st[2]。

对 E[1]进行归纳；引入 st[2]和 E[2]。

承认。承认。(* 跳过一些基本情况*)

dup。(* 复制目标以进行比较*)

(* was: *)

- 反演 E[2]。替换。承认。

(* 现在：*)

- 反演 E[2]。承认。

放弃。

```

    The tactic inverts H as. is like inverts H except that the
    variables and hypotheses being produced are placed in the goal
    rather than in the context. This strategy allows naming those
    new variables and hypotheses explicitly, using either intros
    or introv.

```

定理 ceval_deterministic'：∀c st st[1] st[2]，

c / st ⇓ st[1] →

c / st ⇓ st[2] →

st[1] = st[2]。

证明。

introv E[1] E[2]。推广依赖于 st[2]。

(对 E[1]进行归纳)；引入 st[2]和 E[2]；

反演 E[2]为。

- (* E_Skip *) reflexivity.

- (* E_Ass *)

(* 请注意，变量 n 不会自动替换，因为与 inversion E[2]; subst 相反，tactic inverts E[2]在运行反演之前不会替换存在的等式。*)

(* new: *) 替换 n。

反演。

- (* E_Seq *)

(* 在这里，新创建的变量可以通过 intros 引入，这样它们可以被赋予有意义的名称，例如 st[3]而不是 st'0。*)

(* new: *) 引入 st[3] Red1 Red2。

断言(st' = st[3])为 EQ[1]。

{ (* 断言的证明*)应用 IHE1_1；假设。}

替换 st[3]。

应用 IHE1_2。假设。

(* E_IfTrue *)

- （*b[1] 简化为 true*）

（*在这种简单情况下，不需要提供有意义的名称，所以我们可以直接使用 intros*）

（*新：*）引入。

应用 IHE1。假设。

- （*b[1] 简化为 false（矛盾）*）

（*新：*）引入。

重写 H 为 H[5]。反演 H[5]。

（*其他情况类似*）

放弃。

```

    In the particular case where a call to inversion produces
    a single subgoal, one can use the syntax inverts H as H[1] H[2] H[3]
    for calling inverts and naming the new hypotheses H[1], H[2]
    and H[3]. In other words, the tactic inverts H as H[1] H[2] H[3] is
    equivalent to inverts H as; introv H[1] H[2] H[3]. An example follows.

```

定理 skip_left'：∀c，

cequiv (SKIP;; c) c。

证明。

introv。分割；引入 H。

反演 H 为 U V。 （*新的假设命名为 U 和 V*）

反演 U。假设。

放弃。

```

    A more involved example appears next. In particular, this example
    shows that the name of the hypothesis being inverted can be reused.

```

举例 typing_nonexample_1：

¬ ∃T，

has_type empty

（tabs x TBool

（tabs y TBool

（tapp (tvar x) (tvar y))))

T。

证明。

dup 3。

（*旧证明：*）

- 引入 C。析取 C。

反演 H。替换。清除 H。

反演 H[5]。替换。清除 H[5]。

反演 H[4]。替换。清除 H[4]。

反演 H[2]。替换。清除 H[2]。

反演 H[5]。替换。清除 H[5]。

反演 H[1]。

（*新证明：*）

- 引入 C。析取 C。

反演 H 为 H[1]。

反演 H[1] 为 H[2]。

反演 H[2] 为 H[3]。

反演 H[3] 为 H[4]。

反演 H[4]。

（*新证明，另一种选择：*）

- 引入 C。析取 C。

反演 H 为 H。

反演 H 为 H。

反演 H 为 H。

反演 H 为 H。

反演 H。

完成。

结束 InvertsExamples。

```

    Note: in the rare cases where one needs to perform an inversion
    on an hypothesis H without clearing H from the context,
    one can use the tactic inverts keep H, where the keyword keep
    indicates that the hypothesis should be kept in the context.

```

# 用于 N 元连接词的策略

    因为 Coq 使用二进制编码合取和析取

    构造子 ∧ 和 ∨，处理合取或

    N 个事实的析取有时可能会相当繁琐。

    由于这个原因，"LibTactics" 提供了直接的策略

    对 n 元合取和析取提供支持。它还提供

    直接支持 n 元存在量词。

    本节介绍以下策略：

+   splits 用于分解 n 元合取，

+   branch 用于分解 n 元析取，

+   ∃ 用于证明 n 元存在量词。

```
Module NaryExamples.
  Require Import References.
  Require Import Smallstep.
  Import STLCRef.

```

## 策略 splits

    策略 splits 适用于由合取构成的目标

    n 个命题，产生 n 个子目标。例如，

    它将目标 G[1] ∧ G[2] ∧ G[3] 分解为三个子目标

    G[1]、G[2] 和 G[3]。

```
Lemma demo_splits : ∀n m,
  n > 0 ∧ n < m ∧ m < n+10 ∧ m ≠ 3.
Proof.
  intros. splits.
Abort.

```

## 策略 branch

    策略 branch k 可用于证明 n 元析取。

    例如，如果目标形式为 G[1] ∨ G[2] ∨ G[3]，

    策略 branch 2 只留下 G[2] 作为子目标。以下

    例子展示了 branch 策略的行为。

```
Lemma demo_branch : ∀n m,
  n < m ∨ n = m ∨ m < n.
Proof.
  intros.
  destruct (lt_eq_lt_dec n m) as [[H[1]|H[2]]|H[3]].
  - branch 1\. apply H[1].
  - branch 2\. apply H[2].
  - branch 3\. apply H[3].
Qed.

```

## 策略 ∃

    库"LibTactics"引入了 n 元反演的符号。

    存在量词。例如，可以写成 ∃ x y z, H

    而不是 ∃ x, ∃ y, ∃ z, H。同样，

    该库提供了一个 n 元策略 ∃ a b c，它是一个

    缩写为 ∃ a; ∃ b; ∃ c。以下

    例子展示了符号和策略的行为。

    处理 n 元存在量词。

```
Theorem progress : ∀ST t T st,
  has_type empty ST t T →
  store_well_typed ST st →
  value t ∨ ∃t' st', t / st ⇒ t' / st'.
  (* was: value t ∨ ∃ t', ∃ st', t / st ⇒ t' / st' *)
Proof with eauto.
  intros ST t T st Ht HST. remember (@empty ty) as Γ.
  (induction Ht); subst; try solve_by_invert...
  - (* T_App *)
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    + (* t[1] is a value *)
      inversion Ht1p; subst; try solve_by_invert.
      destruct IHHt2 as [Ht2p | Ht2p]...
      (* t[2] steps *)
      inversion Ht2p as [t[2]' [st' Hstep]].
      ∃(tapp (tabs x T t) t[2]') st'...
      (* was: ∃ (tapp (tabs x T t) t[2]'). ∃ st'... *)
Abort.

```

    备注：类似的 n 元存在量词的功能由

    由标准库中的 Coq.Program.Syntax 模块提供。

    （Coq.Program.Syntax 支持 arity 达到 4 的存在量词；

    LibTactics 支持它们的 arity 达到 10。

```
End NaryExamples.

```

# 用于处理等式的策略

    Coq 相对于其他交互式证明助手的一个主要弱点是它对推理的支持相对较差

    证明助手相对较差的一个主要原因是它对推理的支持相对较差

    使用等式。接下来描述的策略旨在简化

    操纵相等性的证明脚本片段。

    本节介绍以下策略：

+   用于引入要重写的相等性的 asserts_rewrite，

+   cuts_rewrite，与其相似，只是其子目标被交换，

+   substs 用于改进 subst 策略，

+   用于改进 f_equal 策略的 fequals，

+   使用假设 P x z 自动产生一个等式 y = z 作为子目标来证明 P x y 的 applys_eq。

```
Module EqualityExamples.

```

## 策略 asserts_rewrite 和 cuts_rewrite

    策略 asserts_rewrite (E[1] = E[2]) 将 E[1] 替换为 E[2] 在

    目标，并产生目标 E[1] = E[2]。

```
Theorem mult_0_plus : ∀n m : nat,
  (0 + n) * m = n * m.
Proof.
  dup.
  (* The old proof: *)
  intros n m.
  assert (H: 0 + n = n). reflexivity. rewrite → H.
  reflexivity.

  (* The new proof: *)
  intros n m.
  asserts_rewrite (0 + n = n).
    reflexivity. (* subgoal 0+n = n *)
    reflexivity. (* subgoal n*m = m*n *)
Qed.

(*** Remark: the syntax asserts_rewrite (E[1] = E[2]) in H allows      rewriting in the hypothesis H rather than in the goal. *)

```

    策略 cuts_rewrite (E[1] = E[2]) 就像

    断言重写 (E[1] = E[2])，除了等式 E[1] = E[2]

    出现为第一个子目标。

```
Theorem mult_0_plus' : ∀n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  cuts_rewrite (0 + n = n).
    reflexivity. (* subgoal n*m = m*n *)
    reflexivity. (* subgoal 0+n = n *)
Qed.

```

    更一般地说，策略 asserts_rewrite 和 cuts_rewrite

    可以提供引理作为参数。例如，可以写

    断言重写 (∀ a b, a*(S b) = a*b+a)。

    当 a 和 b 是大型项时，这种表述很有用，

    因为没有必要重复它们的陈述。

```
Theorem mult_0_plus'' : ∀u v w x y z: nat,
  (u + v) * (S (w * x + y)) = z.
Proof.
  intros. asserts_rewrite (∀a b, a*(S b) = a*b+a).
    (* first subgoal:  ∀ a b, a*(S b) = a*b+a *)
    (* second subgoal: (u + v) * (w * x + y) + (u + v) = z *)
Abort.

```

## 策略 substs

    策略 substs 类似于 subst，只是它

    当目标包含“循环相等性”时不会失败，

    例如 x = f x。

```
Lemma demo_substs : ∀x y (f:nat→nat),
  x = f x → y = x → y = f x.
Proof.
  intros. substs. (* the tactic subst would fail here *)
  assumption.
Qed.

```

## 策略 fequals

    策略 fequals 类似于 f_equal，只是

    直接解决产生的所有平凡子目标。此外，

    策略 fequals 具有增强的相等性处理功能

    在元组之间。

```
Lemma demo_fequals : ∀(a b c d e : nat) (f : nat→nat→nat→nat→nat),
  a = 1 → b = e → e = 2 →
  f a b c d = f 1 2 c 4.
Proof.
  intros. fequals.
  (* subgoals a = 1, b = 2 and c = c are proved, d = 4 remains *)
Abort.

```

## 策略 applys_eq

    策略 applys_eq 是 eapply 的一个变体，引入

    对于不统一的子项相等性。例如，假设

    目标是命题 P x y，假设我们有

    假设 H 断言 P x z 成立。我们知道我们可以

    证明 y 等于 z。因此，我们可以调用策略

    断言重写 (y = z) 并将目标更改为 P x z，但

    这将需要复制粘贴 y 和 z 的值。

    使用策略 applys_eq，我们可以调用 applys_eq H 1，这样

    证明目标，只留下子目标 y = z。值 1

    作为 applys_eq 的参数指示我们想要一个相等性

    要为 P x y 的第一个参数引入

    右边。以下三个示例说明了行为

    调用 applys_eq H 1，调用 applys_eq H 2 和

    调用 applys_eq H 1 2。

```
Axiom big_expression_using : nat→nat. (* Used in the example *)

Lemma demo_applys_eq_1 : ∀(P:nat→nat→Prop) x y z,
  P x (big_expression_using z) →
  P x (big_expression_using y).
Proof.
  introv H. dup.

  (* The old proof: *)
  assert (Eq: big_expression_using y = big_expression_using z).
    admit. (* Assume we can prove this equality somehow. *)
  rewrite Eq. apply H.

  (* The new proof: *)
  applys_eq H 1.
    admit. (* Assume we can prove this equality somehow. *)
Abort.

```

    如果不匹配是在 P 的第一个参数而不是

    第二个，我们会写 applys_eq H 2。回想一下

    从右边计数出现次数。

```
Lemma demo_applys_eq_2 : ∀(P:nat→nat→Prop) x y z,
  P (big_expression_using z) x →
  P (big_expression_using y) x.
Proof.
  introv H. applys_eq H 2.
Abort.

```

    当我们有两个参数不匹配时，我们想产生

    两个相等性。为了实现这一点，我们可以调用 applys_eq H 1 2。

    更一般地说，策略 applys_eq 预期一个引理和一个

    作为参数的自然数序列。

```
Lemma demo_applys_eq_3 : ∀(P:nat→nat→Prop) x[1] x[2] y[1] y[2],
  P (big_expression_using x[2]) (big_expression_using y[2]) →
  P (big_expression_using x[1]) (big_expression_using y[1]).
Proof.
  introv H. applys_eq H 1 2.
  (* produces two subgoals:      big_expression_using x[1] = big_expression_using x[2]      big_expression_using y[1] = big_expression_using y[2] *)
Abort.

End EqualityExamples.

```

# 一些方便的简写

    本教程的这一部分介绍了一些策略

    有助于使证明脚本更短更易读的：

+   展开（无参数）用于展开头部定义，

+   替换目标为 False，

+   作为依赖泛化的简写，

+   跳过一个子目标，即使它包含存在变量，

+   sort for re-ordering the proof context by moving moving all propositions at the bottom.

```

## The Tactic unfolds

```

Module UnfoldsExample.

Require Import Hoare.

```

    The tactic unfolds (without any argument) unfolds the
    head constant of the goal. This tactic saves the need to
    name the constant explicitly.

```

Lemma bexp_eval_true : ∀b st,

beval st b = true → (bassn b) st.

Proof.

intros b st Hbe. dup.

(* The old proof: *)

unfold bassn. assumption.

(* The new proof: *)

unfolds. assumption.

Qed.

```

    Remark: contrary to the tactic hnf, which may unfold several
    constants, unfolds performs only a single step of unfolding. 

    Remark: the tactic unfolds in H can be used to unfold the
    head definition of the hypothesis H.

```

End UnfoldsExample.

```

## The Tactics false and tryfalse

    The tactic false can be used to replace any goal with False.
    In short, it is a shorthand for exfalso.
    Moreover, false proves the goal if it contains an absurd
    assumption, such as False or 0 = S n, or if it contains
    contradictory assumptions, such as x = true and x = false.

```

Lemma demo_false :

∀n, S n = 1 → n = 0.

Proof.

intros. destruct n. reflexivity. false.

Qed.

```

    The tactic false can be given an argument: false H replace
    the goals with False and then applies H.

```

Lemma demo_false_arg :

(∀n, n < 0 → False) → (3 < 0) → 4 < 0.

Proof.

intros H L. false H. apply L.

Qed.

```

    The tactic tryfalse is a shorthand for try solve [false]:
    it tries to find a contradiction in the goal. The tactic
    tryfalse is generally called after a case analysis.

```

Lemma demo_tryfalse :

∀n, S n = 1 → n = 0.

Proof.

intros. destruct n; tryfalse. reflexivity.

Qed.

```

## The Tactic gen

    The tactic gen is a shortand for generalize dependent
    that accepts several arguments at once. An invokation of
    this tactic takes the form gen x y z.

```

Module GenExample.

Require Import Stlc.

Import STLC.

Lemma substitution_preserves_typing : ∀Γ x U v t S,

has_type (update Γ x U) t S →

has_type empty v U →

has_type Γ ([x:=v]t) S.

Proof.

dup.

(* The old proof: *)

intros Γ x U v t S Htypt Htypv.

generalize dependent S. generalize dependent Γ.

induction t; intros; simpl.

admit. admit. admit. admit. admit. admit.

(* The new proof: *)

introv Htypt Htypv. gen S Γ.

induction t; intros; simpl.

admit. admit. admit. admit. admit. admit.

Abort.

End GenExample.

```

## The Tactics skip, skip_rewrite and skip_goal

    Temporarily admitting a given subgoal is very useful when
    constructing proofs. It gives the ability to focus first
    on the most interesting cases of a proof. The tactic skip
    is like admit except that it also works when the proof
    includes existential variables. Recall that existential
    variables are those whose name starts with a question mark,
    (e.g., ?24), and which are typically introduced by eapply.

```

Module SkipExample.

Require Import Stlc.

Import STLC.

Notation " t '/' st '⇒a*' t' " := (multi (astep st) t t')

(at level 40, st at level 39).

Example astep_example1 :

(APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state ⇒[a]* (ANum 15).

Proof.

eapply multi_step. skip. (* the tactic admit would not work here *)

eapply multi_step. skip. skip.

(* Note that because some unification variables have      not been instantiated, we still need to write      Abort instead of Qed at the end of the proof. *)

Abort.

```

    The tactic skip H: P adds the hypothesis H: P to the context,
    without checking whether the proposition P is true.
    It is useful for exploiting a fact and postponing its proof.
    Note: skip H: P is simply a shorthand for assert (H:P). skip.

```

Theorem demo_skipH : True.

Proof.

skip H: (∀n m : nat, (0 + n) * m = n * m).

Abort.

```

    The tactic skip_rewrite (E[1] = E[2]) replaces E[1] with E[2] in
    the goal, without checking that E[1] is actually equal to E[2].

```

Theorem mult_0_plus : ∀n m : nat,

(0 + n) * m = n * m.

Proof.

dup.

(* The old proof: *)

intros n m.

assert (H: 0 + n = n). skip. rewrite → H.

reflexivity.

(* The new proof: *)

intros n m.

skip_rewrite (0 + n = n).

reflexivity.

Qed.

```

    Remark: the tactic skip_rewrite can in fact be given a lemma
    statement as argument, in the same way as asserts_rewrite. 

    The tactic skip_goal adds the current goal as hypothesis.
    This cheat is useful to set up the structure of a proof by
    induction without having to worry about the induction hypothesis
    being applied only to smaller arguments. Using skip_goal, one
    can construct a proof in two steps: first, check that the main
    arguments go through without waisting time on fixing the details
    of the induction hypotheses; then, focus on fixing the invokations
    of the induction hypothesis.

```

Theorem ceval_deterministic: ∀c st st[1] st[2],

c / st ⇓ st[1] →

c / st ⇓ st[2] →

st[1] = st[2].

Proof.

(* The tactic skip_goal creates an hypothesis called IH      asserting that the statment of ceval_deterministic is true. *)

skip_goal.

(* Of course, if we call assumption here, then the goal is solved      right away, but the point is to do the proof and use IH      only at the places where we need an induction hypothesis. *)

introv E[1] E[2]. gen st[2].

(induction E[1]); introv E[2]; inverts E[2] as.

- (* E_Skip *) reflexivity.

- (* E_Ass *)

subst n.

reflexivity.

- (* E_Seq *)

intros st[3] Red1 Red2.

assert (st' = st[3]) as EQ[1].

{ (* Proof of assertion *)

(* was: apply IHE1_1; assumption. *)

(* new: *) eapply IH. eapply E1_1. eapply Red1. }

subst st[3].

(* was: apply IHE1_2. assumption.] *)

(* new: *) eapply IH. eapply E1_2. eapply Red2.

(* The other cases are similiar. *)

Abort.

End SkipExample.

```

## The Tactic sort

```

Module SortExamples.

Require Import Imp.

```

    The tactic sort reorganizes the proof context by placing
    all the variables at the top and all the hypotheses at the
    bottom, thereby making the proof context more readable.

```

Theorem ceval_deterministic: ∀c st st[1] st[2],

c / st ⇓ st[1] →

c / st ⇓ st[2] →

st[1] = st[2]。

证明。

intros c st st[1] st[2] E[1] E[2]。

generalize dependent st[2]。

（归纳 E[1]）；intros st[2] E[2]；inverts E[2]。

承认。承认。(* 跳过一些琐碎的情况 *)

类型。(* 观察上下文如何重新组织 *)

放弃。

结束 SortExamples。

```

# Tactics for Advanced Lemma Instantiation

    This last section describes a mechanism for instantiating a lemma
    by providing some of its arguments and leaving other implicit.
    Variables whose instantiation is not provided are turned into
    existentential variables, and facts whose instantiation is not
    provided are turned into subgoals.

    Remark: this instantion mechanism goes far beyond the abilities of
    the "Implicit Arguments" mechanism. The point of the instantiation
    mechanism described in this section is that you will no longer need
    to spend time figuring out how many underscore symbols you need to
    write. 

    In this section, we'll use a useful feature of Coq for decomposing
    conjunctions and existentials. In short, a tactic like intros or
    destruct can be provided with a pattern (H[1] & H[2] & H[3] & H[4] & H[5]),
    which is a shorthand for [H[1] [H[2] [H[3] [H[4] H[5]]]]]]. For example,
    destruct (H _ _ _ Htypt) as [T [Hctx Hsub]]. can be rewritten in
    the form destruct (H _ _ _ Htypt) as (T & Hctx & Hsub).

```

## lets 的工作

    当我们有一个我们想要利用的引理（或假设）时，

    我们经常需要明确为这个引理提供参数，

    写一些像：

    destruct (typing_inversion_var _ _ _ Htypt) as (T & Hctx & Hsub)。

    需要多次写“下划线”符号是繁琐的。

    不仅需要弄清楚要写多少个，还需要弄清楚

    这也使得证明脚本看起来相当丑陋。使用这个策略

    允许，一个可以简单地写：

    lets (T & Hctx & Hsub): typing_inversion_var Htypt。

    简而言之，这种策略允许将引理专门化为一堆

    变量和假设。语法是 lets I: E[0] E[1] .. EN，

    通过将事实 E[0] 应用于

    参数 E[1] 到 EN。不需要提供所有参数，

    然而提供的参数需要在

    正确的顺序。该策略依赖于基于第一匹配算法的

    为了弄清楚如何实例化引理

    提供的参数。

```
Module ExamplesLets.
  Require Import Sub.

(* To illustrate the working of lets, assume that we want to    exploit the following lemma. *)

Axiom typing_inversion_var : ∀(G:context) (x:id) (T:ty),
  has_type G (tvar x) T →
  ∃S, G x = Some S ∧ subtype S T.

```

    首先，假设我们有一个类型为

    has_type G (tvar x) T。我们可以获得

    通过调用策略来证明 typing_inversion_var

    允许 K: typing_inversion_var H，如下所示。

```
Lemma demo_lets_1 : ∀(G:context) (x:id) (T:ty),
  has_type G (tvar x) T → True.
Proof.
  intros G x T H. dup.

  (* step-by-step: *)
  lets K: typing_inversion_var H.
  destruct K as (S & Eq & Sub).
  admit.

  (* all-at-once: *)
  lets (S & Eq & Sub): typing_inversion_var H.
  admit.
Abort.

```

    现在假设我们知道 G、x 和 T 的值，我们

    想要获得 S，并且有 has_type G (tvar x) T 被产生

    作为一个子目标。表示我们希望所有剩余的参数

    要产生 typing_inversion_var 的子目标，我们使用

    三个下划线符号 ___.（稍后我们将介绍一个简写

    调用 forwards 的策略来避免写三个下划线。）

```
Lemma demo_lets_2 : ∀(G:context) (x:id) (T:ty), True.
Proof.
  intros G x T.
  lets (S & Eq & Sub): typing_inversion_var G x T ___.
Abort.

```

    通常，只有一个上下文 G 和一个类型 T 是

    适合证明 has_type G (tvar x) T，所以

    我们实际上不需要麻烦地明确给出 G 和 T。

    只需调用 lets (S & Eq & Sub): typing_inversion_var x。

    然后使用存在性实例化变量 G 和 T

    变量。

```
Lemma demo_lets_3 : ∀(x:id), True.
Proof.
  intros x.
  lets (S & Eq & Sub): typing_inversion_var x ___.
Abort.

```

    我们甚至可以进一步不给任何参数来实例化

    typing_inversion_var。在这种情况下，三个统一变量

    被引入。

```
Lemma demo_lets_4 : True.
Proof.
  lets (S & Eq & Sub): typing_inversion_var ___.
Abort.

```

    注意：如果我们只提供引理的名称给 lets

    参数，它只是将这个引理添加到��明上下文中，而不是

    尝试实例化任何一个参数。

```
Lemma demo_lets_5 : True.
Proof.
  lets H: typing_inversion_var.
Abort.

```

    lets 的最后一个有用功能是双下划线符号，

    这允许在多个参数具有时跳过一个参数

    相同类型。在下面的例子中，我们的假设量化

    超过两个类型为 nat 的变量 n 和 m。我们希望

    m 被实例化为值 3，但没有指定

    n 的值。这可以通过写 lets K: H __ 3 来实现。

```
Lemma demo_lets_underscore :
  (∀n m, n ≤ m → n < m+1) → True.
Proof.
  intros H.

  (* If we do not use a double underscore, the first argument,      which is n, gets instantiated as 3. *)
  lets K: H 3\. (* gives K of type ∀ m, 3 ≤ m → 3 < m+1 *)
    clear K.

  (* The double underscore preceeding 3 indicates that we want      to skip a value that has the type nat (because 3 has      the type nat). So, the variable m gets instiated as 3. *)
  lets K: H __ 3\. (* gives K of type ?X ≤ 3 → ?X < 3+1 *)
    clear K.
Abort.

```

    注意：可以写 lets: E[0] E[1] E[2] 代替 lets H: E[0] E[1] E[2]。

    在这种情况下，名称 H 是任意选择的。

    注意：lets 策略最多接受五个参数。另一个

    语法可提供超过五个参数。

    它包括使用带有特殊符号 >> 引入的列表，

    例如 lets H: (>> E[0] E[1] E[2] E[3] E[4] E[5] E[6] E[7] E[8] E[9] 10)。

```
End ExamplesLets.

```

## 使用 applys, forwards 和 specializes 的工作方式

    tactics applys, forwards 和 specializes 是

    一个可以用来执行的快捷方式

    特定任务。

+   forwards 是一个快捷方式，用于实例化所有参数

    一个引理。更准确地说，forwards H: E[0] E[1] E[2] E[3] 是

    相同于 lets H: E[0] E[1] E[2] E[3] ___, 其中三个下划线

    具有与之前解释的相同含义。

+   applys 允许使用高级实例化构建引理

    lets 的模式，然后立即应用该引理。因此，

    应用 E[0] E[1] E[2] E[3] 是相同的，就像 lets H: E[0] E[1] E[2] E[3]

    跟随 eapply H 然后清除 H。

+   specializes 是一个快捷方式，用于就地实例化

    从上下文中得出一个特定参数的假设。

    更准确地说，specializes H E[0] E[1] 是相同的

    lets H': H E[0] E[1] 跟随清除 H 并将 H' 重命名为 H。

    使用 applys 的示例稍后出现。几个示例

    forwards 的使用可以在教程章节 UseAuto 中找到。

```

## Example of Instantiations

```

模块 ExamplesInstantiations。

Require Import Sub。

```

    The following proof shows several examples where lets is used
    instead of destruct, as well as examples where applys is used
    instead of apply. The proof also contains some holes that you
    need to fill in as an exercise.

```

引理 substitution_preserves_typing: ∀Γ x U v t S，

有类型 (update Γ x U) t S →

有类型 empty v U →

有类型 Γ ([x:=v]t) S。

Proof with eauto。

引入 Γ x U v t S Htypt Htypv。

推广相关 S。推广相关 Γ。

(对 t 进行归纳); 引入; 简化。

- (* tvar *)

将 i 重命名为 y。

(* 一个用 lets 替换 destruct 的例子。*)

(* 旧：destruct (typing_inversion_var _ _ _ Htypt) as T [Hctx Hsub].*)

(* 新：*) lets (T&Hctx&Hsub): typing_inversion_var Htypt。

展开 update, t_update 在 Hctx 中。

destruct (beq_idP x y)...

+ (* x=y *)

替换。

反演 Hctx；替换。清除 Hctx。

应用 context_invariance with empty...

引入 x Hcontra。

(* 一个更复杂的例子。*)

(* 旧：destruct (free_in_context _ _ S empty Hcontra) as T' HT'...*)

(* 新：*)

lets [T' HT']: free_in_context S (@empty ty) Hcontra...

反演 HT'。

- (* tapp *)

(* 练习：用 lets 替换以下 destruct。*)

(* 旧：destruct (typing_inversion_app _ _ _ _ Htypt) as T[1] [Htypt1 Htypt2]. eapply T_App...*)

(* 在这里填写*) admit。

- (* tabs *)

将 i 重命名为 y。将 t 重命名为 T[1]。

(* 这里是另一个使用 lets 的例子。*)

(* 旧：destruct (typing_inversion_abs _ _ _ _ _ Htypt)。*)

(* 新：*) lets (T[2]&Hsub&Htypt2): typing_inversion_abs Htypt。

(* 一个例子，其中 apply with 可以替换为 applys。*)

(* 旧：apply T_Sub with (TArrow T[1] T[2])...*)

(* 新：*) 应用 T_Sub (TArrow T[1] T[2])...

应用 T_Abs...

destruct (beq_idP x y)。

+ (* x=y *)

eapply context_invariance...

替换。

引入 x Hafi。展开 update, t_update。

destruct (beq_idP y x)...

+ (* x<>y *)

应用 IHt。应用 context_invariance...

引入 z Hafi。展开 update, t_update。

检测 (beq_idP y z)...

替换。重写 false_beq_id...

- (* ttrue *)

lets: typing_inversion_true Htypt...

- (* tfalse *)

lets: typing_inversion_false Htypt...

- (* tif *)

lets (Htyp1&Htyp2&Htyp3): typing_inversion_if Htypt...

- (* tunit *)

(* 一个 assert 可以被 lets 替换的示例。*)

(* 旧: 断言 (subtype TUnit S)              通过 应用 (typing_inversion_unit _ _ Htypt)... *)

(* 新: *) lets: typing_inversion_unit Htypt...

已承认。

结束 示例实例化。

```

# Summary

    In this chapter we have presented a number of tactics that help make
    proof script more concise and more robust on change.

*   introv and inverts improve naming and inversions. 

*   false and tryfalse help discarding absurd goals. 

*   unfolds automatically calls unfold on the head definition. 

*   gen helps setting up goals for induction. 

*   cases and cases_if help with case analysis. 

*   splits, branch and ∃ to deal with n-ary constructs. 

*   asserts_rewrite, cuts_rewrite, substs and fequals help working with equalities. 

*   lets, forwards, specializes and applys provide means of very conveniently instantiating lemmas. 

*   applys_eq can save the need to perform manual rewriting steps before being able to apply lemma. 

*   skip, skip_rewrite and skip_goal give the flexibility to choose which subgoals to try and discharge first.

    Making use of these tactics can boost one's productivity in Coq proofs.

    If you are interested in using LibTactics.v in your own developments,
    make sure you get the lastest version from:
    [`www.chargueraud.org/softs/tlc/`](http://www.chargueraud.org/softs/tlc/).

```

```

```

```

```

```

```
