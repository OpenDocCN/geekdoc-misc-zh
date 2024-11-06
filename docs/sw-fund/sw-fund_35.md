# 使用自动理论和 Coq 证明中的实践

```

```

(* 本章由 Arthur Chargueraud 编写和维护 *)

```

    In a machine-checked proof, every single detail has to be
    justified.  This can result in huge proof scripts. Fortunately,
    Coq comes with a proof-search mechanism and with several decision
    procedures that enable the system to automatically synthesize
    simple pieces of proof. Automation is very powerful when set up
    appropriately. The purpose of this chapter is to explain the
    basics of working of automation.

    The chapter is organized in two parts. The first part focuses on a
    general mechanism called "proof search." In short, proof search
    consists in naively trying to apply lemmas and assumptions in all
    possible ways. The second part describes "decision procedures",
    which are tactics that are very good at solving proof obligations
    that fall in some particular fragment of the logic of Coq.

    Many of the examples used in this chapter consist of small lemmas
    that have been made up to illustrate particular aspects of automation.
    These examples are completely independent from the rest of the Software
    Foundations course. This chapter also contains some bigger examples
    which are used to explain how to use automation in realistic proofs.
    These examples are taken from other chapters of the course (mostly
    from STLC), and the proofs that we present make use of the tactics
    from the library LibTactics.v, which is presented in the chapter
    UseTactics.

```

Require Import Coq.Arith.Arith。

Require Import Coq.Lists.List。

Import ListNotations。

Require Import Maps。

Require Import Smallstep。

Require Import Stlc。

Require Import LibTactics。

```

# Basic Features of Proof Search

    The idea of proof search is to replace a sequence of tactics
    applying lemmas and assumptions with a call to a single tactic,
    for example auto. This form of proof automation saves a lot of
    effort. It typically leads to much shorter proof scripts, and to
    scripts that are typically more robust to change.  If one makes a
    little change to a definition, a proof that exploits automation
    probably won't need to be modified at all. Of course, using too
    much automation is a bad idea.  When a proof script no longer
    records the main arguments of a proof, it becomes difficult to fix
    it when it gets broken after a change in a definition. Overall, a
    reasonable use of automation is generally a big win, as it saves a
    lot of time both in building proof scripts and in subsequently
    maintaining those proof scripts.

```

## 证明搜索的强度

    我们将研究四种证明搜索策略：auto，eauto，

    iauto 和 jauto。策略 auto 和 eauto 是内置的

    在 Coq 中。策略 iauto 是内置策略的简写

    尝试解决[intuition eauto]。策略 jauto 在

    库 LibTactics，并简单地执行一些预处理

    在调用 eauto 之前检查目标的结构。本章的目标是

    解释证明搜索的一般原则并给出

    猜测这四种策略中的哪一种是最好的

    上述最适合解决给定目标。

    证明搜索是效率和

    表达能力，即如何解决复杂目标之间的权衡

    策略可以解决多少和策略需要多长时间

    终止。策略 auto 仅通过使用构建证明

    基本策略的折中：自反性、假设和应用。该策略

    eauto 还可以利用 eapply。策略 jauto 扩展

    通过 eauto 能够打开与

    发生在上下文中。策略 iauto 能够处理

    与否定相当聪明地处理与否定相反的情况；

    然而，它无法从上下文中打开存在量化。

    另外，当目标涉及到时，iauto 通常会变得非常慢

    几个析取。

    请注意，证明搜索策略永远不会执行任何重写

    步骤（策略 rewrite，subst），也不是在一个上进行案例分析

    任意数据结构或属性（策略 destruct 和

    inversion），也不是任何归纳证明（tactic induction）。所以，

    证明搜索实际上是为了自动化最后几步

    一个证明的各个分支。它不能发现

    证明的总体结构。

```

## Basics

    The tactic auto is able to solve a goal that can be proved
    using a sequence of intros, apply, assumption, and reflexivity.
    Two examples follow. The first one shows the ability for
    auto to call reflexivity at any time. In fact, calling
    reflexivity is always the first thing that auto tries to do.

```

引理 solving_by_reflexivity：

2 + 3 = 5。

证明。auto。Qed。

```

    The second example illustrates a proof where a sequence of
    two calls to apply are needed. The goal is to prove that
    if Q n implies P n for any n and if Q n holds for any n,
    then P 2 holds.

```

引理 solving_by_apply：∀(P Q：nat→Prop），

(∀n，Q n → P n）→

(∀n，Q n）→

P 2。

证明。auto。Qed。

```

    If we are interested to see which proof auto came up with,
    one possibility is to look at the generated proof-term,
    using the command:

    Print solving_by_apply. 

    The proof term is:

    fun (P Q : nat → Prop) (H : ∀ n : nat, Q n → P n) (H[0] : ∀ n : nat, Q n) ⇒ H 2 (H[0] 2) 

    This essentially means that auto applied the hypothesis H
   (the first one), and then applied the hypothesis H[0] (the
   second one).

    The tactic auto can invoke apply but not eapply. So, auto
    cannot exploit lemmas whose instantiation cannot be directly
    deduced from the proof goal. To exploit such lemmas, one needs to
    invoke the tactic eauto, which is able to call eapply.

    In the following example, the first hypothesis asserts that P n
    is true when Q m is true for some m, and the goal is to prove
    that Q 1 implies P 2.  This implication follows direction from
    the hypothesis by instantiating m as the value 1.  The
    following proof script shows that eauto successfully solves the
    goal, whereas auto is not able to do so.

```

引理 solving_by_eapply：∀(P Q：nat→Prop），

(∀n m，Q m → P n）→

Q 1 → P 2。

证明。auto。eauto。Qed。

```

## Conjunctions

    So far, we've seen that eauto is stronger than auto in the
    sense that it can deal with eapply. In the same way, we are going
    to see how jauto and iauto are stronger than auto and eauto
    in the sense that they provide better support for conjunctions. 

    The tactics auto and eauto can prove a goal of the form
    F ∧ F', where F and F' are two propositions, as soon as
    both F and F' can be proved in the current context.
    An example follows.

```

引理 solving_conj_goal：∀(P：nat→Prop）（F：Prop），

(∀n，P n）→ F → F ∧ P 2。

证明。auto。Qed。

```

    However, when an assumption is a conjunction, auto and eauto
    are not able to exploit this conjunction. It can be quite
    surprising at first that eauto can prove very complex goals but
    that it fails to prove that F ∧ F' implies F. The tactics
    iauto and jauto are able to decompose conjunctions from the context.
    Here is an example.

```

引理 solving_conj_hyp：∀(F F'：Prop），

F ∧ F' → F。

证明。auto。eauto。jauto。(* 或者 iauto *) Qed。

```

    The tactic jauto is implemented by first calling a
    pre-processing tactic called jauto_set, and then calling
    eauto. So, to understand how jauto works, one can directly
    call the tactic jauto_set.

```

引理 solving_conj_hyp'：∀(F F'：Prop），

F ∧ F' → F。

证明。intros。jauto_set。eauto。Qed。

```

    Next is a more involved goal that can be solved by iauto and
    jauto.

```

引理 solving_conj_more：∀(P Q R：nat→Prop)（F：Prop），

(F ∧ (∀n m，(Q m ∧ R n) → P n)) →

(F → R 2) →

Q 1 →

P 2 ∧ F。

证明。jauto。(* 或者 iauto *) Qed。

```

    The strategy of iauto and jauto is to run a global analysis of
    the top-level conjunctions, and then call eauto.  For this
    reason, those tactics are not good at dealing with conjunctions
    that occur as the conclusion of some universally quantified
    hypothesis. The following example illustrates a general weakness
    of Coq proof search mechanisms.

```

引理 solving_conj_hyp_forall：∀(P Q：nat→Prop），

(∀n，P n ∧ Q n）→ P 2。

证明。

auto。eauto。iauto。jauto。

(* 没有任何方法有效，所以我们必须手动做一些工作 *)

intros。destruct（H 2）。auto。

Qed。

```

    This situation is slightly disappointing, since automation is
    able to prove the following goal, which is very similar. The
    only difference is that the universal quantification has been
    distributed over the conjunction.

```

引理 solved_by_jauto：∀(P Q：nat→Prop）（F：Prop），

(∀n，P n）∧（∀n，Q n）→ P 2。

证明。jauto。(* 或者 iauto *) Qed。

```

## Disjunctions

    The tactics auto and eauto can handle disjunctions that
    occur in the goal.

```

解决 disj_goal 的引理：∀(F F'：Prop)，

F → F ∨ F'。

证明。auto。证毕。

```

    However, only iauto is able to automate reasoning on the
    disjunctions that appear in the context. For example, iauto can
    prove that F ∨ F' entails F' ∨ F.

```

解决 disj_hyp 的引理：∀(F F'：Prop)，

F ∨ F' → F' ∨ F。

证明。auto。eauto。jauto。iauto。证毕。

```

    More generally, iauto can deal with complex combinations of
    conjunctions, disjunctions, and negations. Here is an example.

```

解决 tauto 的引理：∀(F[1] F[2] F[3]：Prop)，

((¬F[1] ∧ F[3]) ∨ (F[2] ∧ ¬F[3])) →

（F[2] → F[1]）→

（F[2] → F[3]）→

¬F[2]。

证明。iauto。证毕。

```

    However, the ability of iauto to automatically perform a case
    analysis on disjunctions comes with a downside: iauto may be
    very slow. If the context involves several hypotheses with
    disjunctions, iauto typically generates an exponential number of
    subgoals on which eauto is called. One major advantage of jauto
    compared with iauto is that it never spends time performing this
    kind of case analyses.

```

## 存在

    策略 eauto、iauto 和 jauto 可以证明目标，其

    结论是存在的。例如，如果目标是 ∃ x，f x，则策略 eauto 引入一个存在变量，

    说?25，而不是 x。剩余目标是 f ?25，和

    eauto 尝试解决此目标，允许自身实例化

    ?25 与任何适当的值。例如，如果存在假设 f 2，则变量?25 被实例化为

    2，目标解决如下所示。

```
Lemma solving_exists_goal : ∀(f : nat→Prop),
  f 2 → ∃x, f x.
Proof.
  auto. (* observe that auto does not deal with existentials, *)
  eauto. (* whereas eauto, iauto and jauto solve the goal *)
Qed.

```

    jauto 相对于其他证明搜索策略的一个主要优势是

    它能够利用存在量化

    假设，即形式为∃ x，P 的那些。

```
Lemma solving_exists_hyp : ∀(f g : nat→Prop),
  (∀x, f x → g x) →
  (∃a, f a) →
  (∃a, g a).
Proof.
  auto. eauto. iauto. (* All of these tactics fail, *)
  jauto. (* whereas jauto succeeds. *)
  (* For the details, run intros. jauto_set. eauto *)
Qed.

```

## 否定

    策略 auto 和 eauto 在处理中存在一些局限性

    就否定的处理而言，它们在很大程度上与

    否定的事实，写作 ¬ P，被定义为 P → False，但

    定义的展开不会执行

    自动地。考虑以下示例。

```
Lemma negation_study_1 : ∀(P : nat→Prop),
  P 0 → (∀x, ¬ P x) → False.
Proof.
  intros P H[0] HX.
  eauto. (* It fails to see that HX applies *)
  unfold not in *. eauto.
Qed.

```

    由于这个原因，策略 iauto 和 jauto 系统地

    在其预处理的一部分中调用解除 not。所以，

    他们能够立即解决之前的目标。

```
Lemma negation_study_2 : ∀(P : nat→Prop),
  P 0 → (∀x, ¬ P x) → False.
Proof. jauto. (* or iauto *) Qed.

```

    我们稍后会回到与证明搜索行为有关的问题

    关于定义展开的尊重。

```

## Equalities

    Coq's proof-search feature is not good at exploiting equalities.
    It can do very basic operations, like exploiting reflexivity
    and symmetry, but that's about it. Here is a simple example
    that auto can solve, by first calling symmetry and then
    applying the hypothesis.

```

equality_by_auto 的引理：∀(f g：nat→Prop)，

(∀x，f x = g x) → g 2 = f 2。

证明。auto。证毕。

```

    To automate more advanced reasoning on equalities, one should
    rather try to use the tactic congruence, which is presented at
    the end of this chapter in the "Decision Procedures" section.

```

# 证明搜索如何工作

```

## Search Depth

    The tactic auto works as follows.  It first tries to call
    reflexivity and assumption. If one of these calls solves the
    goal, the job is done. Otherwise auto tries to apply the most
    recently introduced assumption that can be applied to the goal
    without producing and error. This application produces
    subgoals. There are two possible cases. If the sugboals produced
    can be solved by a recursive call to auto, then the job is done.
    Otherwise, if this application produces at least one subgoal that
    auto cannot solve, then auto starts over by trying to apply
    the second most recently introduced assumption. It continues in a
    similar fashion until it finds a proof or until no assumption
    remains to be tried.

    It is very important to have a clear idea of the backtracking
    process involved in the execution of the auto tactic; otherwise
    its behavior can be quite puzzling. For example, auto is not
    able to solve the following triviality.

```

搜索深度 _0：

真 ∧ 真 ∧ 真 ∧ 真 ∧ 真 ∧ 真。

证明。

auto。

放弃。

```

    The reason auto fails to solve the goal is because there are
    too many conjunctions. If there had been only five of them, auto
    would have successfully solved the proof, but six is too many.
    The tactic auto limits the number of lemmas and hypotheses
    that can be applied in a proof, so as to ensure that the proof
    search eventually terminates. By default, the maximal number
    of steps is five. One can specify a different bound, writing
    for example auto 6 to search for a proof involving at most
    six steps. For example, auto 6 would solve the previous lemma.
    (Similarly, one can invoke eauto 6 or intuition eauto 6.)
    The argument n of auto n is called the "search depth."
    The tactic auto is simply defined as a shorthand for auto 5.

    The behavior of auto n can be summarized as follows. It first
    tries to solve the goal using reflexivity and assumption. If
    this fails, it tries to apply a hypothesis (or a lemma that has
    been registered in the hint database), and this application
    produces a number of sugoals. The tactic auto (n-1) is then
    called on each of those subgoals. If all the subgoals are solved,
    the job is completed, otherwise auto n tries to apply a
    different hypothesis.

    During the process, auto n calls auto (n-1), which in turn
    might call auto (n-2), and so on. The tactic auto 0 only
    tries reflexivity and assumption, and does not try to apply
    any lemma. Overall, this means that when the maximal number of
    steps allowed has been exceeded, the auto tactic stops searching
    and backtracks to try and investigate other paths. 

    The following lemma admits a unique proof that involves exactly
    three steps. So, auto n proves this goal iff n is greater than
    three.

```

搜索深度 _1 的引理：∀(P：nat→Prop)，

P 0 →

（P 0 → P 1）→

（P 1 → P 2）→

（P 2）。

证明。

auto 0\.（*找不到证明*）

auto 1\.（*找不到证明*）

auto 2\.（*找不到证明*）

auto 3\.（*找到证明*）

（*更一般地，如果 n ≥ 3，则 auto n 解决目标*）

证毕。

```

    We can generalize the example by introducing an assumption
    asserting that P k is derivable from P (k-1) for all k,
    and keep the assumption P 0. The tactic auto, which is the
    same as auto 5, is able to derive P k for all values of k
    less than 5\. For example, it can prove P 4.

```

搜索深度 _3 的引理：∀(P：nat→Prop)，

（*假设 H[1]：*）（P 0）→

（*假设 H[2]：*）（∀k，P (k-1) → P k）→

（*目标：*）（P 4）。

证明。auto。证毕。

```

    However, to prove P 5, one needs to call at least auto 6.

```

搜索深度 _4 的引理：∀(P：nat→Prop)，

（*假设 H[1]：*）（P 0）→

（*假设 H[2]：*）（∀k，P (k-1) → P k）→

（*目标：*）（P 5）。

证明。auto。auto 6\. 证毕。

```

    Because auto looks for proofs at a limited depth, there are
    cases where auto can prove a goal F and can prove a goal
    F' but cannot prove F ∧ F'. In the following example,
    auto can prove P 4 but it is not able to prove P 4 ∧ P 4,
    because the splitting of the conjunction consumes one proof step.
    To prove the conjunction, one needs to increase the search depth,
    using at least auto 6.

```

搜索深度 _5 的引理：∀(P：nat→Prop)，

（*假设 H[1]：*）（P 0）→

（*假设 H[2]：*）（∀k，P (k-1) → P k）→

（*目标：*）（P 4 ∧ P 4）。

证明。auto。auto 6\. 证毕。

```

## Backtracking

    In the previous section, we have considered proofs where
    at each step there was a unique assumption that auto
    could apply. In general, auto can have several choices
    at every step. The strategy of auto consists of trying all
    of the possibilities (using a depth-first search exploration).

    To illustrate how automation works, we are going to extend the
    previous example with an additional assumption asserting that
    P k is also derivable from P (k+1). Adding this hypothesis
    offers a new possibility that auto could consider at every step.

    There exists a special command that one can use for tracing
    all the steps that proof-search considers. To view such a
    trace, one should write debug eauto. (For some reason, the
    command debug auto does not exist, so we have to use the
    command debug eauto instead.)

```

搜索深度 _1 的引理：∀(P：nat→Prop)，

（*假设 H[1]：*）（P 0）→

（*假设 H[2]：*）（∀k，P (k-1) → P k）→

（*假设 H[3]：*）（∀k，P (k+1) → P k）→

（*目标：*）（P 2）。

（取消注释以下行中的“debug”以查看调试跟踪：）

证明。intros P H[1] H[2] H[3]。（*调试*）eauto。证毕。

```

    The output message produced by debug eauto is as follows.

```

    深度=5

    深度=4 应用 H2

    深度=3 应用 H2

    深度=3 确切 H1

```

    The depth indicates the value of n with which eauto n is
    called. The tactics shown in the message indicate that the first
    thing that eauto has tried to do is to apply H[2]. The effect of
    applying H[2] is to replace the goal P 2 with the goal P 1.
    Then, again, H[2] has been applied, changing the goal P 1 into
    P 0. At that point, the goal was exactly the hypothesis H[1].

    It seems that eauto was quite lucky there, as it never even
    tried to use the hypothesis H[3] at any time. The reason is that
    auto always tried to use the H[2] first. So, let's permute
    the hypotheses H[2] and H[3] and see what happens.

```

引理 auto_2 的工作原理：∀(P：nat→Prop)，

（*假设 H[1]：*）（P 0）→

(* 假设 H[3]： *) (∀k，P (k+1) → P k) →

(* 假设 H[2]： *) (∀k，P (k-1) → P k) →

(* 目标： *) (P 2)。

证明。intros P H[1] H[3] H[2]。（调试）eauto。Qed。

```

    This time, the output message suggests that the proof search
    investigates many possibilities. If we print the proof term:

    Print working_of_auto_2. 

    we observe that the proof term refers to H[3]. Thus the proof
    is not the simplest one, since only H[2] and H[1] are needed.

    In turns out that the proof goes through the proof obligation P 3, 
    even though it is not required to do so. The following tree drawing
    describes all the goals that eauto has been going through.

```

    |5||4||3||2||1||0| -- 下面，制表符表示深度

    [P 2]

    -> [P 3]

    -> [P 4]

        -> [P 5]

            -> [P 6]

                -> [P 7]

                -> [P 5]

            -> [P 4]

                -> [P 5]

                -> [P 3]

        --> [P 3]

            -> [P 4]

                -> [P 5]

                -> [P 3]

            -> [P 2]

                -> [P 3]

                -> [P 1]

    -> [P 2]

        -> [P 3]

            -> [P 4]

                -> [P 5]

                -> [P 3]

            -> [P 2]

                -> [P 3]

                -> [P 1]

        -> [P 1]

            -> [P 2]

                -> [P 3]

                -> [P 1]

            -> [P 0]

                -> !! 完成 !!

```

    The first few lines read as follows. To prove P 2, eauto 5
    has first tried to apply H[3], producing the subgoal P 3.
    To solve it, eauto 4 has tried again to apply H[3], producing
    the goal P 4. Similarly, the search goes through P 5, P 6
    and P 7. When reaching P 7, the tactic eauto 0 is called
    but as it is not allowed to try and apply any lemma, it fails.
    So, we come back to the goal P 6, and try this time to apply
    hypothesis H[2], producing the subgoal P 5. Here again,
    eauto 0 fails to solve this goal.

    The process goes on and on, until backtracking to P 3 and trying
    to apply H[3] three times in a row, going through P 2 and P 1
    and P 0. This search tree explains why eauto came up with a
    proof term starting with an application of H[3].

```

## 添加提示

    默认情况下，auto（和 eauto）只尝试应用

    出现在证明上下文中的假设。有两个

    告诉 auto 利用引理的可能性有两种

    之前已经被证明：要么将引理添加为假设

    在调用 auto 前，或将引理添加为提示，以便

    它可以被每个调用自动的调用使用。

    第一种可能性对于让 auto 利用引理很有用

    只在这个特定点起作用。要将引理添加为

    假设，可以输入 generalize mylemma; intros，或者简单地

    lets：mylemma（后者需要 LibTactics.v）。

    第二种可能性对于需要的引理很有用

    多次利用。将引理添加为提示的语法

    是 Hint Resolve mylemma。例如，断言的引理

    任何数小于或等于自身，∀ x，x ≤ x，

    在 Coq 标准库中称为 Le.le_refl，可以作为

    提示如下。

```
Hint Resolve Le.le_refl.

```

    添加一个归纳的方便简写是

    作为提示的归纳数据类型是命令 Hint Constructors mydatatype。

    警告：某些引理，如传递性结果，应该

    不要添加提示，因为它们会严重影响

    证明搜索的性能。对此问题的描述

    以及对传递性的一般解决方法的展示

    引理会进一步出现。

```

## Integration of Automation in Tactics

    The library "LibTactics" introduces a convenient feature for
    invoking automation after calling a tactic. In short, it suffices
    to add the symbol star (*) to the name of a tactic. For example,
    apply* H is equivalent to apply H; auto_star, where auto_star
    is a tactic that can be defined as needed.

    The definition of auto_star, which determines the meaning of the
    star symbol, can be modified whenever needed. Simply write:

```

Ltac auto_star ::= 一个新的定义。

    注意使用 ::= 而不是 :=，这表示

    策略被重新绑定到一个新的定义。所以，默认

    定义如下。

```
Ltac auto_star ::= try solve [ jauto ].

```

    几乎所有标准 Coq 策略和所有来自

    "LibTactics" 可以用星号调用。例如，一个

    可以调用 subst*，destruct* H，inverts* H，lets* I: H x，

    specializes* H x，等等... 有两个值得注意的例外。

    策略 auto* 只是策略的另一个名称

    auto_star。而策略 apply* H 调用 eapply H（或

    更强大的应用 H（如果需要），然后调用 auto_star。

    请注意，没有 eapply* H 策略，使用 apply* H

    相反。

    在大型开发中，使用两个程度可能会更方便

    自动化。通常，人们会使用快速策略，如 auto，

    和一个更慢但更强大的策略，比如 jauto。为了允许

    两种形式的自动化之间的平滑共存，LibTactics.v

    还定义了策略的 "波浪" 版本，比如 apply¬ H，

    destruct¬ H，subst¬，auto¬ 等等。策略的含义

    波浪符号由 auto_tilde 策略描述，其

    默认实现是 auto。

```
Ltac auto_tilde ::= auto.

```

    在接下来的示例中，只需要 auto_star。

    auto_star 的另一种可能更有效的版本是

    以下是接下来的示例":

    Ltac auto_star ::= try solve eassumption | auto | jauto .

    有了上面的定义，auto_star 首先尝试解决

    使用假设;如果失败，它尝试使用 auto，

    并且如果这仍然失败，则调用 jauto。即使

    jauto 严格比 eassumption 和 auto 更强大，它

    是有意义的首先调用这些策略，因为当

    成功，它们节省了大量时间，当它们无法证明时

    目标，它们很快就失败了。”。

```

# Examples of Use of Automation

    Let's see how to use proof search in practice on the main theorems
    of the "Software Foundations" course, proving in particular
    results such as determinism, preservation and progress.

```

## 确定性

```
Module DeterministicImp.
  Require Import Imp.

```

    回想一下 IMP 的确定性引理的原始证明

    语言，如下所示。

```
Theorem ceval_deterministic: ∀c st st[1] st[2],
  c / st ⇓ st[1] →
  c / st ⇓ st[2] →
  st[1] = st[2].
Proof.
  intros c st st[1] st[2] E[1] E[2].
  generalize dependent st[2].
  (induction E[1]); intros st[2] E[2]; inversion E[2]; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ[1].
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b[1] reduces to true *)
    apply IHE1. assumption.
  - (* b[1] reduces to false (contradiction) *)
    rewrite H in H[5]. inversion H[5].
  (* E_IfFalse *)
  - (* b[1] reduces to true (contradiction) *)
    rewrite H in H[5]. inversion H[5].
  - (* b[1] reduces to false *)
      apply IHE1. assumption.
  (* E_WhileEnd *)
  - (* b[1] reduces to true *)
    reflexivity.
  - (* b[1] reduces to false (contradiction) *)
    rewrite H in H[2]. inversion H[2].
  (* E_WhileLoop *)
  - (* b[1] reduces to true (contradiction) *)
    rewrite H in H[4]. inversion H[4].
  - (* b[1] reduces to false *)
    assert (st' = st'0) as EQ[1].
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
Qed.

```

    练习：尽可能使用 auto 重写此证明。

    （解决方案使用 auto 9 次。）

```
Theorem ceval_deterministic': ∀c st st[1] st[2],
  c / st ⇓ st[1] →
  c / st ⇓ st[2] →
  st[1] = st[2].
Proof.
  (* FILL IN HERE *) admit.
Admitted.

```

    实际上，使用自动化不仅仅是调用自动

    代替其他一个或两个策略。使用自动化是关于

    重新考虑策略序列的组织以便

    最小化编写和维护证明所涉及的工作。

    这个过程得益于使用来自的策略

    LibTactics.v。所以，在尝试优化自动化方式之前

    被使用，让我们首先重写确定性的证明：

+   使用 introv H 而不是 intros x H，

+   使用 gen x 而不是 generalize dependent x，

+   使用 inverts H 而不是 inversion H;subst，

+   使用 tryfalse 处理矛盾，并且消除出现在上下文中的 beval st b[1] = true 和 beval st b[1] = false 两者都出现的情况，

+   停止使用 ceval_cases 来标记子案例。

```
Theorem ceval_deterministic'': ∀c st st[1] st[2],
  c / st ⇓ st[1] →
  c / st ⇓ st[2] →
  st[1] = st[2].
Proof.
  introv E[1] E[2]. gen st[2].
  induction E[1]; intros; inverts E[2]; tryfalse.
  - auto.
  - auto.
  - assert (st' = st'0). auto. subst. auto.
  - auto.
  - auto.
  - auto.
  - assert (st' = st'0). auto. subst. auto.
Qed.

```

    要获得一个干净的漂亮的证明脚本，我们必须删除调用

    断言（st' = st'0）。这样的策略调用不好

    因为它涉及到一些变量，它们的名称已经

    自动生成。这种策略往往是非常

    脆弱。断言（st' = st'0）的策略用于断言

    我们想从归纳中推导出的结论

    假设。所以，我们不是明确陈述这个结论，我们

    我们将要求 Coq 实例化归纳假设，

    使用自动化来确定如何实例化它。战术

    forwards，在 LibTactics.v 中精确描述了如何帮助

    实例化一个事实。所以，让我们看看它在我们的上的运行情况

    例子。

```
Theorem ceval_deterministic''': ∀c st st[1] st[2],
  c / st ⇓ st[1] →
  c / st ⇓ st[2] →
  st[1] = st[2].
Proof.
  (* Let's replay the proof up to the assert tactic. *)
  introv E[1] E[2]. gen st[2].
  induction E[1]; intros; inverts E[2]; tryfalse.
  - auto.
  - auto.
  (* We duplicate the goal for comparing different proofs. *)
  - dup 4.

  (* The old proof: *)
  + assert (st' = st'0). apply IHE1_1. apply H[1].
    (* produces H: st' = st'0. *) skip.

  (* The new proof, without automation: *)
  + forwards: IHE1_1. apply H[1].
    (* produces H: st' = st'0. *) skip.

  (* The new proof, with automation: *)
  + forwards: IHE1_1. eauto.
    (* produces H: st' = st'0. *) skip.

  (* The new proof, with integrated automation: *)
  + forwards*: IHE1_1.
    (* produces H: st' = st'0. *) skip.

Abort.

```

    为了完善证明脚本，仍然需要合并调用

    到 `auto`，使用星号符号。确定性的证明可以

    只需用四行重新编写，包括不超过 10 个策略。

```
Theorem ceval_deterministic'''': ∀c st st[1] st[2],
  c / st ⇓ st[1]  →
  c / st ⇓ st[2] →
  st[1] = st[2].
Proof.
  introv E[1] E[2]. gen st[2].
  induction E[1]; intros; inverts* E[2]; tryfalse.
  - forwards*: IHE1_1. subst*.
  - forwards*: IHE1_1. subst*.
Qed.

End DeterministicImp.

```

## STLC 的保留

```
Module PreservationProgressStlc.
  Require Import StlcProp.
  Import STLC.
  Import STLCProp.

```

    考虑 STLC 的保存证明，如下所示。

    这个证明已经通过了通过三个点的 eauto

    机制。

```
Theorem preservation : ∀t t' T,
  has_type empty t T  →
  t ⇒ t'  →
  has_type empty t' T.
Proof with eauto.
  remember (@empty ty) as Γ.
  intros t t' T HT. generalize dependent t'.
  (induction HT); intros t' HE; subst Γ.
  - (* T_Var *)
    inversion HE.
  - (* T_Abs *)
    inversion HE.
  - (* T_App *)
    inversion HE; subst...
    (* The ST_App1 and ST_App2 cases are immediate by induction, and        auto takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T[11]...
      inversion HT[1]...
  - (* T_True *)
    inversion HE.
  - (* T_False *)
    inversion HE.
  - (* T_If *)
    inversion HE; subst...
Qed.

```

    练习：使用 LibTactics 中的策略重写此证明

    并且使用星号符号调用自动化而不是

    三点符号。更准确地说，利用策略

    inverts*和 applys*在调用 auto*之后调用

    invert 或者应用。解决方案只有三行长。

```
Theorem preservation' : ∀t t' T,
  has_type empty t T  →
  t ⇒ t'  →
  has_type empty t' T.
Proof.
  (* FILL IN HERE *) admit.
Admitted.

```

## STLC 的进展

    考虑进步定理的证明。

```
Theorem progress : ∀t T,
  has_type empty t T →
  value t ∨ ∃t', t ⇒ t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Γ.
  (induction Ht); subst Γ...
  - (* T_Var *)
    inversion H.
  - (* T_App *)
    right. destruct IHHt1...
    + (* t[1] is a value *)
      destruct IHHt2...
      * (* t[2] is a value *)
        inversion H; subst; try solve_by_invert.
        ∃([x[0]:=t[2]]t)...
      * (* t[2] steps *)
       destruct H[0] as [t[2]' Hstp]. ∃(tapp t[1] t[2]')...
    + (* t[1] steps *)
      destruct H as [t[1]' Hstp]. ∃(tapp t[1]' t[2])...
  - (* T_If *)
    right. destruct IHHt1...
    destruct t[1]; try solve_by_invert...
    inversion H. ∃(tif x[0] t[2] t[3])...
Qed.

```

    练习：优化以上证明。

    提示：利用 destruct*和 inverts*。

    解决方案由 10 行短代码组成。

```
Theorem progress' : ∀t T,
  has_type empty t T →
  value t ∨ ∃t', t ⇒ t'.
Proof.
  (* FILL IN HERE *) admit.
Admitted.

End PreservationProgressStlc.

```

## 大步和小步

```
Module Semantics.
Require Import Smallstep.

```

    考虑与小步减少判断相关的证明

    到一个大步减少判断。

```
Theorem multistep__eval : ∀t v,
  normal_form_of t v → ∃n, v = C n ∧ t ⇓ n.
Proof.
  intros t v Hnorm.
  unfold normal_form_of in Hnorm.
  inversion Hnorm as [Hs Hnf]; clear Hnorm.
  rewrite nf_same_as_value in Hnf. inversion Hnf. clear Hnf.
  ∃n. split. reflexivity.
  induction Hs; subst.
  - (* multi_refl *)
    apply E_Const.
  - (* multi_step *)
    eapply step__eval. eassumption. apply IHHs. reflexivity.
Qed.

```

    我们的目标是优化上述证明。通常

    更容易将归纳隔离到单独的引理中。所以，

    我们将首先证明一个中间结果

    包括归纳的判断。

    正在执行。

    练习：使用策略证明以下结果

    introv，归纳和替换，并应用*。

    解决方案为 3 行。

```
Theorem multistep_eval_ind : ∀t v,
  t ⇒* v → ∀n, C n = v → t ⇓ n.
Proof.
  (* FILL IN HERE *) admit.
Admitted.

```

    练习：使用上述引理，简��

    结果 multistep__eval。你应该使用策略

    introv，inverts，split* 和 apply*。

    解决方案为 2 行。

```
Theorem multistep__eval' : ∀t v,
  normal_form_of t v → ∃n, v = C n ∧ t ⇓ n.
Proof.
  (* FILL IN HERE *) admit.
Admitted.

```

    如果我们试图将两个证明合并为一个，

    我们很可能会失败，因为有一个限制

    归纳策略。实际上，这个策略会丢失

    应用于参数的属性时的信息

    没有简化为变量，例如 t ⇒* (C n)。

    因此，您需要使用更强大的策略称为

    依赖归纳。此策略仅在

    导入 Program 库，如下所示。

```
Require Import Program.

```

    练习：证明引理 multistep__eval 而不调用

    引理 multistep_eval_ind，即通过内联证明

    通过涉及 multistep_eval_ind 中的归纳

    依赖归纳而不是归纳的策略。

    解决方案为 5 行。

```
Theorem multistep__eval'' : ∀t v,
  normal_form_of t v → ∃n, v = C n ∧ t ⇓ n.
Proof.
  (* FILL IN HERE *) admit.
Admitted.

End Semantics.

```

## STLCRef 的保留

```
Module PreservationProgressReferences.
  Require Import Coq.omega.Omega.
  Require Import References.
  Import STLCRef.
  Hint Resolve store_weakening extends_refl.

```

    STLCRef 的保留证明可以在第章中找到

    参考文献。优化后的证明脚本是原来的两倍多

    更短。以下材料解释了如何构建

    优化后的证明脚本。最终的优化后的证明脚本为

    保留定理随后出现。

```
Theorem preservation : ∀ST t t' T st st',
  has_type empty ST t T →
  store_well_typed ST st →
  t / st ⇒ t' / st' →
  ∃ST',
    (extends ST' ST ∧
     has_type empty ST' t' T ∧
     store_well_typed ST' st').
Proof.
  (* old: Proof. with eauto using store_weakening, extends_refl.      new: Proof., and the two lemmas are registered as hints      before the proof of the lemma, possibly inside a section in      order to restrict the scope of the hints. *)

  remember (@empty ty) as Γ. introv Ht. gen t'.
  (induction Ht); introv HST Hstep;
    (* old: subst; try solve_by_invert; inversion Hstep; subst; try (eauto using store_weakening, extends_refl)        new: subst Γ; inverts Hstep; eauto.        We want to be more precise on what exactly we substitute,        and we do not want to call try solve_by_invert which        is way to slow. *)
   subst Γ; inverts Hstep; eauto.

  (* T_App *)
  - (* ST_AppAbs *)
  (* old:       exists ST. inversion Ht[1]; subst.       split; try split... eapply substitution_preserves_typing... *)
  (* new: we use inverts in place of inversion and splits to      split the conjunction, and applys* in place of eapply... *)
  ∃ST. inverts Ht[1]. splits*. applys* substitution_preserves_typing.

  - (* ST_App1 *)
  (* old:       eapply IHHt1 in H[0]...       inversion H[0] as ST' [Hext [Hty Hsty]].       exists ST'... *)
  (* new: The tactic eapply IHHt1 in H[0]... applies IHHt1 to H[0].      But H[0] is only thing that IHHt1 could be applied to, so      there eauto can figure this out on its own. The tactic      forwards is used to instantiate all the arguments of IHHt1,      producing existential variables and subgoals when needed. *)
  forwards: IHHt1. eauto. eauto. eauto.
  (* At this point, we need to decompose the hypothesis H that has      just been created by forwards. This is done by the first part      of the preprocessing phase of jauto. *)
  jauto_set_hyps; intros.
  (* It remains to decompose the goal, which is done by the second      part of the preprocessing phase of jauto. *)
  jauto_set_goal; intros.
  (* All the subgoals produced can then be solved by eauto. *)
  eauto. eauto. eauto.

  -(* ST_App2 *)
  (* old:       eapply IHHt2 in H[5]...       inversion H[5] as ST' [Hext [Hty Hsty]].       exists ST'... *)
  (* new: this time, we need to call forwards on IHHt2,      and we call jauto right away, by writing forwards*,      proving the goal in a single tactic! *)
  forwards*: IHHt2.

  (* The same trick works for many of the other subgoals. *)
  - forwards*: IHHt.
  - forwards*: IHHt.
  - forwards*: IHHt1.
  - forwards*: IHHt2.
  - forwards*: IHHt1.

  - (* T_Ref *)
  + (* ST_RefValue *)
    (* old:          exists (ST ++ T[1]::nil).          inversion HST; subst.          split.            apply extends_app.          split.            replace (TRef T[1])              with (TRef (store_Tlookup (length st) (ST ++ T[1]::nil))).            apply T_Loc.            rewrite <- H. rewrite app_length, plus_comm. simpl. omega.            unfold store_Tlookup. rewrite <- H. rewrite app_nth2; try omega.            rewrite minus_diag. simpl. reflexivity.            apply store_well_typed_app; assumption. *)
    (* new: In this proof case, we need to perform an inversion        without removing the hypothesis. The tactic inverts keep        serves exactly this purpose. *)
    ∃(ST ++ T[1]::nil). inverts keep HST. splits.
    (* The proof of the first subgoal needs no change *)
      apply extends_app.
    (* For the second subgoal, we use the tactic applys_eq to avoid        a manual replace before T_loc can be applied. *)
      applys_eq T_Loc 1.
    (* To justify the inequality, there is no need to call rewrite ← H,        because the tactic omega is able to exploit H on its own.        So, only the rewriting of app_length and the call to the        tactic omega remain, with a call to simpl to unfold the        definition of app. *)
        rewrite app_length. simpl. omega.
    (* The next proof case is hard to polish because it relies on the        lemma app_nth1 whose statement is not automation-friendly.        We'll come back to this proof case further on. *)
      unfold store_Tlookup. rewrite ← H. rewrite* app_nth2.
    (* Last, we replace apply ..; assumption with apply* .. *)
    rewrite minus_diag. simpl. reflexivity.
    apply* store_well_typed_app.

  - forwards*: IHHt.

  - (* T_Deref *)
  + (* ST_DerefLoc *)
  (* old:       exists ST. split; try split...       destruct HST as _ Hsty.       replace T[11] with (store_Tlookup l ST).       apply Hsty...       inversion Ht; subst... *)
  (* new: we start by calling ∃ ST and splits*. *)
  ∃ST. splits*.
  (* new: we replace destruct HST as [_ Hsty] by the following *)
  lets [_ Hsty]: HST.
  (* new: then we use the tactic applys_eq to avoid the need to      perform a manual replace before applying Hsty. *)
  applys_eq* Hsty 1.
  (* new: we then can call inverts in place of inversion;subst *)
  inverts* Ht.

  - forwards*: IHHt.

  - (* T_Assign *)
  + (* ST_Assign *)
  (* old:       exists ST. split; try split...       eapply assign_pres_store_typing...       inversion Ht[1]; subst... *)
  (* new: simply using nicer tactics *)
  ∃ST. splits*. applys* assign_pres_store_typing. inverts* Ht[1].

  - forwards*: IHHt1.
  - forwards*: IHHt2.
Qed.

```

    让我们回到难以优化的证明案例。

    困难来自于 nth_eq_last 的陈述，其中

    采用形式 nth (length l) (l ++ x::nil) d = x。这个引理是

    难以利用，因为它的第一个参数，长度 l，提到

    一个列表 l，必须与出现在 l 中的 l 完全相同

    snoc l x。实际上，第一个参数通常是一个自然数

    可证明等于长度 l 但不是

    语法上等于长度 l。有一个简单的修复方法

    使 nth_eq_last 易于应用：引入中间

    明确变量 n，使得目标变为

    nth n (snoc l x) d = x，前提断言 n = length l。

```
Lemma nth_eq_last' : ∀(A : Type) (l : list A) (x d : A) (n : nat),
  n = length l → nth n (l ++ x::nil) d = x.
Proof. intros. subst. apply nth_eq_last. Qed.

```

    从保留定理的证明案例然后

    变得更容易证明，因为重写 nth_eq_last'

    现在成功。

```
Lemma preservation_ref : ∀(st:store) (ST : store_ty) T[1],
  length ST = length st →
  TRef T[1] = TRef (store_Tlookup (length st) (ST ++ T[1]::nil)).
Proof.
  intros. dup.

  (* A first proof, with an explicit unfold *)
  unfold store_Tlookup. rewrite* nth_eq_last'.

  (* A second proof, with a call to fequal *)
  fequal. symmetry. apply* nth_eq_last'.
Qed.

```

    保留的证明总结如下。

```
Theorem preservation' : ∀ST t t' T st st',
  has_type empty ST t T →
  store_well_typed ST st →
  t / st ⇒ t' / st' →
  ∃ST',
    (extends ST' ST ∧
     has_type empty ST' t' T ∧
     store_well_typed ST' st').
Proof.
  remember (@empty ty) as Γ. introv Ht. gen t'.
  induction Ht; introv HST Hstep; subst Γ; inverts Hstep; eauto.
  - ∃ST. inverts Ht[1]. splits*. applys* substitution_preserves_typing.
  - forwards*: IHHt1.
  - forwards*: IHHt2.
  - forwards*: IHHt.
  - forwards*: IHHt.
  - forwards*: IHHt1.
  - forwards*: IHHt2.
  - forwards*: IHHt1.
  - ∃(ST ++ T[1]::nil). inverts keep HST. splits.
    apply extends_app.
    applys_eq T_Loc 1.
      rewrite app_length. simpl. omega.
      unfold store_Tlookup. rewrite* nth_eq_last'.
    apply* store_well_typed_app.
  - forwards*: IHHt.
  - ∃ST. splits*. lets [_ Hsty]: HST.
    applys_eq* Hsty 1\. inverts* Ht.
  - forwards*: IHHt.
  - ∃ST. splits*. applys* assign_pres_store_typing. inverts* Ht[1].
  - forwards*: IHHt1.
  - forwards*: IHHt2.
Qed.

```

## STLCRef 的进展

    STLCRef 的进展证明可以在第章中找到

    参考文献。优化后的证明脚本是，再次，关于

    长度的一半。

```
Theorem progress : ∀ST t T st,
  has_type empty ST t T →
  store_well_typed ST st →
  (value t ∨ ∃t', ∃st', t / st ⇒ t' / st').
Proof.
  introv Ht HST. remember (@empty ty) as Γ.
  induction Ht; subst Γ; tryfalse; try solve [left*].
  - right. destruct* IHHt1 as [K|].
    inverts K; inverts Ht[1].
     destruct* IHHt2.
  - right. destruct* IHHt as [K|].
    inverts K; try solve [inverts Ht]. eauto.
  - right. destruct* IHHt as [K|].
    inverts K; try solve [inverts Ht]. eauto.
  - right. destruct* IHHt1 as [K|].
    inverts K; try solve [inverts Ht[1]].
     destruct* IHHt2 as [M|].
      inverts M; try solve [inverts Ht[2]]. eauto.
  - right. destruct* IHHt1 as [K|].
    inverts K; try solve [inverts Ht[1]]. destruct* n.
  - right. destruct* IHHt.
  - right. destruct* IHHt as [K|].
    inverts K; inverts Ht as M.
      inverts HST as N. rewrite* N in M.
  - right. destruct* IHHt1 as [K|].
    destruct* IHHt2.
     inverts K; inverts Ht[1] as M.
     inverts HST as N. rewrite* N in M.
Qed.

End PreservationProgressReferences.

```

## 子类型

```
Module SubtypingInversion.
  Require Import Sub.

```

    考虑类型判断的反演引理

    在具有子类型的类型系统中的抽象。

```
Lemma abs_arrow : ∀x S[1] s[2] T[1] T[2],
  has_type empty (tabs x S[1] s[2]) (TArrow T[1] T[2]) →
     subtype T[1] S[1]
  ∧ has_type (update empty x S[1]) s[2] T[2].
Proof with eauto.
  intros x S[1] s[2] T[1] T[2] Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S[2] [Hsub Hty]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U[1] [U[2] [Heq [Hsub1 Hsub2]]]].
  inversion Heq; subst...
Qed.

```

    练习：优化证明脚本，使用

    introv，lets 和 inverts*。特别地，

    您会发现将模式替换为有用

    在 H 中应用 K。将 H 解构为 I，使用 lets I: K H。

    解决方案是 4 行。

```
Lemma abs_arrow' : ∀x S[1] s[2] T[1] T[2],
  has_type empty (tabs x S[1] s[2]) (TArrow T[1] T[2]) →
     subtype T[1] S[1]
  ∧ has_type (update empty x S[1]) s[2] T[2].
Proof.
  (* FILL IN HERE *) admit.
Admitted.

```

    引理 substitution_preserves_typing 已经被用于

    说明了在章节中 lets 和 applys 的工作原理

    UseTactics。使用自动化进一步优化这个证明

    星号符号），并使用 tactic cases_if'。解决方案

    是 33 行）。

```
Lemma substitution_preserves_typing : ∀Γ x U v t S,
  has_type (update Γ x U) t S →
  has_type empty v U →
  has_type Γ ([x:=v]t) S.
Proof.
  (* FILL IN HERE *) admit.
Admitted.

End SubtypingInversion.

```

# 证明搜索中的高级主题

```

## Stating Lemmas in the Right Way

    Due to its depth-first strategy, eauto can get exponentially
    slower as the depth search increases, even when a short proof
    exists. In general, to make proof search run reasonably fast, one
    should avoid using a depth search greater than 5 or 6\. Moreover,
    one should try to minimize the number of applicable lemmas, and
    usually put first the hypotheses whose proof usefully instantiates
    the existential variables.

    In fact, the ability for eauto to solve certain goals actually
    depends on the order in which the hypotheses are stated. This point
    is illustrated through the following example, in which P is
    a property of natural numbers. This property is such that
    P n holds for any n as soon as P m holds for at least one m
    different from zero. The goal is to prove that P 2 implies P 1.
    When the hypothesis about P is stated in the form
    ∀ n m, P m → m ≠ 0 → P n, then eauto works. However, with
    ∀ n m, m ≠ 0 → P m → P n, the tactic eauto fails.

```

引理 order_matters_1：∀(P：nat→Prop)，

(∀n m, P m → m ≠ 0 → P n) → P 2 → P 1。

证明。

eauto。 （*成功*）

（*证明：引入 P H K。eapply H。应用 K。auto。*）

完成。

引理 order_matters_2：∀(P：nat→Prop)，

(∀n m, m ≠ 0 → P m → P n) → P 5 → P 1。

证明。

eauto。 （*失败*）

（*为了理解为什么，让我们重播上一个证明*）

引入 P H K。

eapply H。

（*应用 eapply 后留下了两个子目标，?X ≠ 0 和 P ?X，其中?X 是一个存在变量。*）

（*对于 eauto 来说，解决第一个子目标很容易：只需将?X 实例化为值 1，这是满足?X ≠ 0 的最简单值。*）

eauto。

（*但是第二个目标变成了 P 1，这就是我们开始的地方。所以，eauto 在这一点上卡住了。*）

放弃。

```

    It is very important to understand that the hypothesis ∀ n m, P m → m ≠ 0 → P n is eauto-friendly, whereas ∀ n m, m ≠ 0 → P m → P n really isn't.  Guessing a value of m for
    which P m holds and then checking that m ≠ 0 holds works well
    because there are few values of m for which P m holds. So, it
    is likely that eauto comes up with the right one. On the other
    hand, guessing a value of m for which m ≠ 0 and then checking
    that P m holds does not work well, because there are many values
    of m that satisfy m ≠ 0 but not P m.

```

## 在证明搜索期间展开定义

    通常鼓励使用中间定义

    形式化发展，因为通常会导致更简洁��更

    可读性的陈述。然而，定义可能会使事情变得有点困难

    自动化证明。问题在于对于一个

    证明搜索机制知道何时需要展开定义

    展开。请注意，一个简单的策略是展开

    在调用证明搜索之前展开所有定义并不适用于

    大型证明，所以我们避免它。本节介绍了一些

    避免在

    调用证明搜索。

    为了说明定义的处理，让 P 是一个抽象

    自然数的属性，并让 myFact 是一个定义

    表示命题 P x 对任何小于或等于 x 的 x 成立

    等于 3。

```
Axiom P : nat → Prop.

Definition myFact := ∀x, x ≤ 3 → P x.

```

    证明 myFact 在假设 P x 成立的情况下

    任何 x 都应该是微不足道的。然而，auto 无法证明它，除非我们

    明确展开 myFact 的定义。

```
Lemma demo_hint_unfold_goal_1 :
  (∀x, P x) → myFact.
Proof.
  auto. (* Proof search doesn't know what to do, *)
  unfold myFact. auto. (* unless we unfold the definition. *)
Qed.

```

    为了自动展开出现在证明中的定义

    义务，可以使用命令 Hint Unfold myFact 告诉

    Coq 应该总是尝试展开 myFact 当 myFact

    出现在目标中。

```
Hint Unfold myFact.

```

    这一次，自动化能够看穿定义

    of myFact。

```
Lemma demo_hint_unfold_goal_2 :
  (∀x, P x) → myFact.
Proof. auto. Qed.

```

    然而，Hint Unfold 机制仅适用于展开

    出现在目标中的定义。一般来说，证明搜索会

    不要从上下文中展开定义。例如，假设我们

    想要证明在 True → myFact 的假设下 P 3 成立。

```
Lemma demo_hint_unfold_context_1 :
  (True → myFact) → P 3.
Proof.
  intros.
  auto. (* fails *)
  unfold myFact in *. auto. (* succeeds *)
Qed.

```

    实际上有一个例外：一个常数

    如果出现在假设中的命题 P x 会自动展开

    假设可以直接应用于当前目标。例如，

    auto 可以证明 myFact → P 3，如下所示。

```
Lemma demo_hint_unfold_context_2 :
  myFact → P 3.
Proof. auto. Qed.

```

## 用于证明荒谬目标的自动化

    在本节中，我们将看到结论为否定的引理

    通常不是有用的提示，而那些

    结论是 False 可能是有用的提示，但有太多

    它们使证明搜索效率低下。我们还将看到一个实际的

    解决效率问题的解决方法。

    考虑以下引理，它断言一个数字

    小于或等于 3 不大于 3。

```
Parameter le_not_gt : ∀x,
  (x ≤ 3) → ¬ (x > 3).

```

    或者，可以陈述大于三的数字是

    不小于或等于 3。

```
Parameter gt_not_le : ∀x,
  (x > 3) → ¬ (x ≤ 3).

```

    实际上，这两个陈述等价于第三个陈述

    x ≤ 3 和 x > 3 是矛盾的，意思是

    它们暗示 False。

```
Parameter le_gt_false : ∀x,
  (x ≤ 3) → (x > 3) → False.

```

    以下调查旨在弄清楚三者中的哪一个

    陈述是最方便的，关于证明

    自动化。以下材料被包含在一个部分内，

    以限制我们添加的提示的范围。在

    换句话说，在章节结束后，添加的提示

    该章节将不再处于活动状态。

```
Section DemoAbsurd1.

```

    让我们尝试添加第一个引理 le_not_gt 作为提示，

    看看我们是否可以证明这个命题

    ∃ x，x ≤ 3 ∧ x > 3 是荒谬的。

```
Hint Resolve le_not_gt.

Lemma demo_auto_absurd_1 :
  (∃x, x ≤ 3 ∧ x > 3) → False.
Proof.
  intros. jauto_set. (* decomposes the assumption *)
  (* debug *) eauto. (* does not see that le_not_gt could apply *)
  eapply le_not_gt. eauto. eauto.
Qed.

```

    引理 gt_not_le 对 le_not_gt 是对称的，因此不会

    也不会更好。第三个引理 le_gt_false 更有用

    提示，因为它的结论是 False，所以证明搜索将尝试

    当当前目标为 False 时应用它。

```
Hint Resolve le_gt_false.

Lemma demo_auto_absurd_2 :
  (∃x, x ≤ 3 ∧ x > 3) → False.
Proof.
  dup.

  (* detailed version: *)
  intros. jauto_set. (* debug *) eauto.

  (* short version: *)
  jauto.
Qed.

```

    总之，形式为 H[1] → H[2] → False 的引理要好得多

    比 H[1] → ¬ H[2]更有效的提示，尽管这两个陈述

    在否定符号¬的定义上等效。

    也就是说，应该小心添加那些引理

    结论为 False 的提示。原因是每当

    达到目标 False 时，证明搜索机制将

    可能尝试应用所有结论为 False 的提示

    在应用适当的提示之前。

```
End DemoAbsurd1.

```

    将结论为 False 的引理作为提示添加可能在局部起作用，

    一个非常有效的解决方案。但是，这种方法不会扩展

    用于全局提示。对于大多数实际应用，它是

    给出要利用的引理的名称是最方便的

    推导出矛盾。提供的 false H 策略

    LibTactics 服务于此目的：false H 替换目标

    与 False 一起工作并调用 eapply H。其行为将在下面描述。

    注意任何三个陈述 le_not_gt，gt_not_le

    或者可以使用 le_gt_false。

```
Lemma demo_false : ∀x,
  (x ≤ 3) → (x > 3) → 4 = 5.
Proof.
  intros. dup 4.

  (* A failed proof: *)
  - false. eapply le_gt_false.
    + auto. (* here, auto does not prove ?x ≤ 3 by using H but              by using the lemma le_refl : ∀ x, x ≤ x. *)
    (* The second subgoal becomes 3 > 3, which is not provable. *)
    + skip.

  (* A correct proof: *)
  - false. eapply le_gt_false.
    + eauto. (* here, eauto uses H, as expected, to prove ?x ≤ 3 *)
    + eauto. (* so the second subgoal becomes x > 3 *)

  (* The same proof using false: *)
  - false le_gt_false. eauto. eauto.

  (* The lemmas le_not_gt and gt_not_le work as well *)
  - false le_not_gt. eauto. eauto.
Qed.

```

    在上面的示例中，false le_gt_false; eauto 证明了���标，

    但 false le_gt_false; auto 不起作用，因为 auto 不

    正确实例化存在变量。注意，false* le_gt_false 也不起作用，因为星号符号尝试

    首先调用 auto。因此，有两种可能性

    完成证明：要么调用 false le_gt_false; eauto，要么

    调用 false* (le_gt_false 3)。

```

## Automation for Transitivity Lemmas

    Some lemmas should never be added as hints, because they would
    very badly slow down proof search. The typical example is that of
    transitivity results. This section describes the problem and
    presents a general workaround.

    Consider a subtyping relation, written subtype S T, that relates
    two object S and T of type typ. Assume that this relation
    has been proved reflexive and transitive. The corresponding lemmas
    are named subtype_refl and subtype_trans.

```

参数 typ：Type。

参数 subtype：typ → typ → Prop。

参数 subtype_refl：∀T，

subtype T T。

参数 subtype_trans：∀S T U，

subtype S T → subtype T U → subtype S U。

```

    Adding reflexivity as hint is generally a good idea,
    so let's add reflexivity of subtyping as hint.

```

提示解决 subtype_refl。

```

    Adding transitivity as hint is generally a bad idea.  To
    understand why, let's add it as hint and see what happens.
    Because we cannot remove hints once we've added them, we are going
    to open a "Section," so as to restrict the scope of the
    transitivity hint to that section.

```

章节 HintsTransitivity。

提示解决 subtype_trans。

```

    Now, consider the goal ∀ S T, subtype S T, which clearly has
    no hope of being solved. Let's call eauto on this goal.

```

引理 transitivity_bad_hint_1：∀S T，

subtype S T。

证明。

intros. (* debug *) eauto. (* 调查 106 次应用... *)

中止。

```

    Note that after closing the section, the hint subtype_trans
    is no longer active.

```

结束 HintsTransitivity。

```

    In the previous example, the proof search has spent a lot of time
    trying to apply transitivity and reflexivity in every possible
    way.  Its process can be summarized as follows. The first goal is
    subtype S T. Since reflexivity does not apply, eauto invokes
    transitivity, which produces two subgoals, subtype S ?X and
    subtype ?X T. Solving the first subgoal, subtype S ?X, is
    straightforward, it suffices to apply reflexivity. This unifies
    ?X with S. So, the second sugoal, subtype ?X T,
    becomes subtype S T, which is exactly what we started from...

    The problem with the transitivity lemma is that it is applicable
    to any goal concluding on a subtyping relation. Because of this,
    eauto keeps trying to apply it even though it most often doesn't
    help to solve the goal. So, one should never add a transitivity
    lemma as a hint for proof search. 

    There is a general workaround for having automation to exploit
    transitivity lemmas without giving up on efficiency. This workaround
    relies on a powerful mechanism called "external hint." This
    mechanism allows to manually describe the condition under which
    a particular lemma should be tried out during proof search.

    For the case of transitivity of subtyping, we are going to tell
    Coq to try and apply the transitivity lemma on a goal of the form
    subtype S U only when the proof context already contains an
    assumption either of the form subtype S T or of the form
    subtype T U. In other words, we only apply the transitivity
    lemma when there is some evidence that this application might
    help.  To set up this "external hint," one has to write the
    following.

```

Hint Extern 1 (subtype ?S ?U) ⇒

匹配目标，有

| H: subtype S ?T ⊢ _ ⇒ 应用 (@subtype_trans S T U)

| H: subtype ?T U ⊢ _ ⇒ 应用 (@subtype_trans S T U)

结束。

```

    This hint declaration can be understood as follows.

*   "Hint Extern" introduces the hint.

*   The number "1" corresponds to a priority for proof search. It doesn't matter so much what priority is used in practice.

*   The pattern subtype ?S ?U describes the kind of goal on which the pattern should apply. The question marks are used to indicate that the variables ?S and ?U should be bound to some value in the rest of the hint description.

*   The construction match goal with ... end tries to recognize patterns in the goal, or in the proof context, or both.

*   The first pattern is H: subtype S ?T ⊢ _. It indices that the context should contain an hypothesis H of type subtype S ?T, where S has to be the same as in the goal, and where ?T can have any value.

*   The symbol ⊢ _ at the end of H: subtype S ?T ⊢ _ indicates that we do not impose further condition on how the proof obligation has to look like.

*   The branch ⇒ apply (@subtype_trans S T U) that follows indicates that if the goal has the form subtype S U and if there exists an hypothesis of the form subtype S T, then we should try and apply transitivity lemma instantiated on the arguments S, T and U. (Note: the symbol @ in front of subtype_trans is only actually needed when the "Implicit Arguments" feature is activated.)

*   The other branch, which corresponds to an hypothesis of the form H: subtype ?T U is symmetrical.

    Note: the same external hint can be reused for any other transitive
    relation, simply by renaming subtype into the name of that relation. 

    Let us see an example illustrating how the hint works.

```

引理 transitivity_workaround_1 : ∀T[1] T[2] T[3] T[4],

subtype T[1] T[2] T[3] T[4] → subtype T[1] T[4].

证明。

intros. (* debug *) eauto. (* 跟踪显示外部提示被使用 *)

Qed。

```

    We may also check that the new external hint does not suffer from the
    complexity blow up.

```

引理 transitivity_workaround_2 : ∀S T,

subtype S T。

证明。

intros. (* debug *) eauto. (* 调查 0 次应用 *)

中止。

```

# Decision Procedures

    A decision procedure is able to solve proof obligations whose
    statement admits a particular form. This section describes three
    useful decision procedures. The tactic omega handles goals
    involving arithmetic and inequalities, but not general
    multiplications.  The tactic ring handles goals involving
    arithmetic, including multiplications, but does not support
    inequalities. The tactic congruence is able to prove equalities
    and inequalities by exploiting equalities available in the proof
    context.

```

## Omega

    策略 omega 支持自然数（类型 nat）以及

    整数（类型 Z，通过包含模块 ZArith 可用）。

    它支持加法，减法，相等性和不等式。

    在使用 omega 之前，需要导入模块 Omega，

    如下。

```
Require Import Omega.

```

    这是一个例子。设 x 和 y 为两个自然数

    （它们不能为负）。假设 y 小于 4，假设

    x+x+1 小于 y，并假设 x 不为零。那么，

    必须是 x 等于一的情况。

```
Lemma omega_demo_1 : ∀(x y : nat),
  (y ≤ 4) → (x + x + 1 ≤ y) → (x ≠ 0) → (x = 1).
Proof. intros. omega. Qed.

```

    另一个示例：如果 z 是 x 和 y 的均值，并且如果

    x 和 y 的差异最多为 4，则差异

    x 和 z 之间的差异最多为 2。

```
Lemma omega_demo_2 : ∀(x y z : nat),
  (x + y = z + z) → (x - y ≤ 4) → (x - z ≤ 2).
Proof. intros. omega. Qed.

```

    一个可以使用 omega 证明 False 的数学事实

    从上下文中是矛盾的。在以下示例中，

    上下文中的值 x 和 y 的约束不能全部

    同时满足。

```
Lemma omega_demo_3 : ∀(x y : nat),
  (x + 5 ≤ y) → (y - x < 3) → False.
Proof. intros. omega. Qed.

```

    注意：omega 只能在其证明目标可通过矛盾证明时证明目标。

    结论化简为 False。策略 omega 总是失败

    当结论是任意命题 P 时，即使

    False 可以推出任何命题 P（通过 ex_falso_quodlibet）。

```
Lemma omega_demo_4 : ∀(x y : nat) (P : Prop),
  (x + 5 ≤ y) → (y - x < 3) → P.
Proof.
  intros.
  (* Calling omega at this point fails with the message:     "Omega: Can't solve a goal with proposition variables" *)
  (* So, one needs to replace the goal by False first. *)
  false. omega.
Qed.

```

## 环

    与 omega 相比，策略 ring 添加了对

    乘法，但它放弃了在

    不等式。此外，它仅支持整数（类型 Z）和

    不是自然数（类型 nat）。以下是一个示例，显示了如何

    使用 ring。

```
Module RingDemo.
  Require Import ZArith.
  Open Scope Z_scope.
  (* Arithmetic symbols are now interpreted in Z *)

Lemma ring_demo : ∀(x y z : Z),
    x * (y + z) - z * 3 * x
  = x * y - 2 * x * z.
Proof. intros. ring. Qed.

End RingDemo.

```

## Congruence

    策略 congruence 能够利用来自

    证明上下文以便自动执行重写

    建立目标所需的操作。它略微更多

    强大于策略 subst，后者只能处理相等式

    形式为 x = e 其中 x 是变量，e 是

    表达式。

```
Lemma congruence_demo_1 :
   ∀(f : nat→nat→nat) (g h : nat→nat) (x y z : nat),
   f (g x) (g y) = z →
   2 = g x →
   g y = h z →
   f 2 (h z) = z.
Proof. intros. congruence. Qed.

```

    此外，congruence 能够利用普遍量化的

    相等式，例如 ∀ a，g a = h a。

```
Lemma congruence_demo_2 :
   ∀(f : nat→nat→nat) (g h : nat→nat) (x y z : nat),
   (∀a, g a = h a) →
   f (g x) (g y) = z →
   g x = 2 →
   f 2 (h y) = z.
Proof. congruence. Qed.

```

    接下来是一个 congruence 非常有用的示例。

```
Lemma congruence_demo_4 : ∀(f g : nat→nat),
  (∀a, f a = g a) →
  f (g (g 2)) = g (f (f 2)).
Proof. congruence. Qed.

```

    策略 congruence 能够证明矛盾，如果

    目标导致的相等性与可用的不等式相矛盾

    在证明上下文中。

```
Lemma congruence_demo_3 :
   ∀(f g h : nat→nat) (x : nat),
   (∀a, f a = h a) →
   g x = f x →
   g x ≠ h x →
   False.
Proof. congruence. Qed.

```

    Congruence 的一项优点是它非常快

    策略。因此，无论何时都应该调用它

    帮助。

```

# Summary

    Let us summarize the main automation tactics available.

*   auto automatically applies reflexivity, assumption, and apply. 

*   eauto moreover tries eapply, and in particular can instantiate existentials in the conclusion. 

*   iauto extends eauto with support for negation, conjunctions, and disjunctions. However, its support for disjunction can make it exponentially slow. 

*   jauto extends eauto with support for negation, conjunctions, and existential at the head of hypothesis. 

*   congruence helps reasoning about equalities and inequalities. 

*   omega proves arithmetic goals with equalities and inequalities, but it does not support multiplication. 

*   ring proves arithmetic goals with multiplications, but does not support inequalities.

    In order to set up automation appropriately, keep in mind the following
    rule of thumbs:

*   automation is all about balance: not enough automation makes proofs not very robust on change, whereas too much automation makes proofs very hard to fix when they break. 

*   if a lemma is not goal directed (i.e., some of its variables do not occur in its conclusion), then the premises need to be ordered in such a way that proving the first premises maximizes the chances of correctly instantiating the variables that do not occur in the conclusion. 

*   a lemma whose conclusion is False should only be added as a local hint, i.e., as a hint within the current section. 

*   a transitivity lemma should never be considered as hint; if automation of transitivity reasoning is really necessary, an Extern Hint needs to be set up. 

*   a definition usually needs to be accompanied with a Hint Unfold.

    Becoming a master in the black art of automation certainly requires
    some investment, however this investment will pay off very quickly.

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
