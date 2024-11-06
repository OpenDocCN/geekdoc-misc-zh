# IndPropInductively Defined Propositions

```

```

需要导出逻辑。

```

# Inductively Defined Propositions

    In the Logic chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and quantifiers.
    In this chapter, we bring a new tool into the mix: *inductive definitions*.

    Recall that we have seen two ways of stating that a number n is
    even: We can say (1) evenb n = true, or (2) ∃ k, n = double k.  Yet another possibility is to say that n is even if
    we can establish its evenness from the following rules:

*   Rule ev_0: The number 0 is even.

*   Rule ev_SS: If n is even, then S (S n) is even.

    To illustrate how this definition of evenness works, let's
    imagine using it to show that 4 is even. By rule ev_SS, it
    suffices to show that 2 is even. This, in turn, is again
    guaranteed by rule ev_SS, as long as we can show that 0 is
    even. But this last fact follows directly from the ev_0 rule. 

    We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  *Inference rules* are one such notation: 

           |

                        (ev_0)  
           |

* * *

           |

                        ev 0
           |

                     |

                        ev n
           |

                        (ev_SS)  
           |

* * *

           |

                        ev (S (S n))
           |

                     |

    Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the *premises*
    above the line all hold, then the *conclusion* below the line
    follows.  For example, the rule ev_SS says that, if n
    satisfies ev, then S (S n) also does.  If a rule has no
    premises above the line, then its conclusion holds
    unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a *proof tree*. Here's how we might transcribe
    the above proof that 4 is even: 

```

------  (ev_0)

ev 0

------ (ev_SS)

ev 2

------ (ev_SS)

ev 4

    为什么称之为“树”（而不是“栈”，例如）？

    因为一般来说，推断规则可以有多个前提。

    我们将在下面看到示例。

    将所有这些放在一起，我们可以将 ev 的定义翻译为

    使用归纳定义将偶数性（evenness）形式化为 Coq 定义。

    声明，其中每个构造函数对应于一个推断

    规则：

```
Inductive ev : nat → Prop :=
| ev_0 : ev 0
| ev_SS : ∀n : nat, ev n → ev (S (S n)).

```

    这个定义在一个关键方面与之不同

    Inductive 的先前用法：其结果不是一个 Type，而是

    而是 nat 到 Prop 的函数 —— 也就是，一个属性

    数字。请注意，我们已经看到其他归纳定义

    导致函数的结果，例如 list，其类型为 Type → Type。这里的新内容是，因为

    ev 出现为*未命名*，在冒号的*右侧*，允许

    在不同构造函数的类型中取不同的值：

    ev_0 的类型中为 0，ev_SS 的类型中为 S (S n)。

    相比之下，list 的定义将 X 参数命名为

    *全局*，在冒号的*左侧*，强制结果为

    nil 和 cons 被视为相同（list X）。如果我们尝试将

    在定义 ev 时将 nat 放在左侧，我们会看到一个错误：

```
Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : ∀n, wrong_ev n → wrong_ev (S (S n)).
(* ===> Error: A parameter of an inductive type n is not         allowed to be used as a bound variable in the type         of its constructor. *)

```

    （这里的“参数”是 Coq 术语，表示冒号左侧的参数

    在归纳定义中使用冒号；“index”用于引用

    冒号右侧的参数。）

    我们可以将 ev 的定义看作是在 Coq 中定义一个属性

    ev：nat → Prop，连同定理 ev_0：ev 0 和

    ev_SS：∀ n，ev n → ev (S (S n))。这样的“构造函���

    定理”与已证明的定理具有相同的地位。特别是，

    我们可以使用 Coq 的 apply 策略与规则名称来证明 ev

    对于特定的数字...

```
Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

```

    ... 或者我们可以使用函数应用语法：

```
Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

```

    我们还可以证明具有涉及 ev 的假设的定理。

```
Theorem ev_plus4 : ∀n, ev n → ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

```

    更一般地，我们可以证明任何数乘以 2 都是偶数：

#### 练习：1 星（ev_double）

```
Theorem ev_double : ∀n,
  ev (double n).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

# Using Evidence in Proofs

    Besides *constructing* evidence that numbers are even, we can also
    *reason about* such evidence.

    Introducing ev with an Inductive declaration tells Coq not
    only that the constructors ev_0 and ev_SS are valid ways to
    build evidence that some number is even, but also that these two
    constructors are the *only* ways to build evidence that numbers
    are even (in the sense of ev). 

    In other words, if someone gives us evidence E for the assertion
    ev n, then we know that E must have one of two shapes:

*   E is ev_0 (and n is O), or

*   E is ev_SS n' E' (and n is S (S n'), where E' is evidence for ev n').

    This suggests that it should be possible to analyze a hypothesis
    of the form ev n much as we do inductively defined data
    structures; in particular, it should be possible to argue by
    *induction* and *case analysis* on such evidence.  Let's look at a
    few examples to see what this means in practice. 

## Inversion on Evidence

    Suppose we are proving some fact involving a number n, and we
    are given ev n as a hypothesis.  We already know how to perform
    case analysis on n using the inversion tactic, generating
    separate subgoals for the case where n = O and the case where n = S n' for some n'.  But for some proofs we may instead want to
    analyze the evidence that ev n *directly*.

    By the definition of ev, there are two cases to consider:

*   If the evidence is of the form ev_0, we know that n = 0. 

*   Otherwise, the evidence must have the form ev_SS n' E', where n = S (S n') and E' is evidence for ev n'.

    We can perform this kind of reasoning in Coq, again using
    the inversion tactic.  Besides allowing us to reason about
    equalities involving constructors, inversion provides a
    case-analysis principle for inductively defined propositions.
    When used in this way, its syntax is similar to destruct: We
    pass it a list of identifiers separated by | characters to name
    the arguments to each of the possible constructors.

```

定理 ev_minus2：∀n，

ev n → ev (pred (pred n))。

证明。

引入 n E。

反演 E 为 [| n' E']。

- (* E = ev_0 *) 简化。应用 ev_0。

- (* E = ev_SS n' E' *) 简化。应用 E'。完成。

```

    In words, here is how the inversion reasoning works in this proof:

*   If the evidence is of the form ev_0, we know that n = 0. Therefore, it suffices to show that ev (pred (pred 0)) holds. By the definition of pred, this is equivalent to showing that ev 0 holds, which directly follows from ev_0. 

*   Otherwise, the evidence must have the form ev_SS n' E', where n = S (S n') and E' is evidence for ev n'. We must then show that ev (pred (pred (S (S n')))) holds, which, after simplification, follows directly from E'.

    This particular proof also works if we replace inversion by
    destruct:

```

定理 ev_minus2'：∀n，

ev n → ev (pred (pred n))。

证明。

引入 n E。

将 E 解构为 [| n' E']。

- (* E = ev_0 *) 简化。应用 ev_0。

- (* E = ev_SS n' E' *) 简化。应用 E'。完成。

```

    The difference between the two forms is that inversion is more
    convenient when used on a hypothesis that consists of an inductive
    property applied to a complex expression (as opposed to a single
    variable).  Here's is a concrete example.  Suppose that we wanted
    to prove the following variation of ev_minus2:

```

定理 evSS_ev：∀n，

ev (S (S n)) → ev n。

```

    Intuitively, we know that evidence for the hypothesis cannot
    consist just of the ev_0 constructor, since O and S are
    different constructors of the type nat; hence, ev_SS is the
    only case that applies.  Unfortunately, destruct is not smart
    enough to realize this, and it still generates two subgoals.  Even
    worse, in doing so, it keeps the final goal unchanged, failing to
    provide any useful information for completing the proof.

```

证明。

引入 n E。

将 E 解构为 [| n' E']。

- (* E = ev_0。*)

(* 我们必须证明没有任何假设的情况下 n 是偶数！*)

放弃。

```

    What happened, exactly?  Calling destruct has the effect of
    replacing all occurrences of the property argument by the values
    that correspond to each constructor.  This is enough in the case
    of ev_minus2' because that argument, n, is mentioned directly
    in the final goal. However, it doesn't help in the case of
    evSS_ev since the term that gets replaced (S (S n)) is not
    mentioned anywhere. 

    The inversion tactic, on the other hand, can detect (1) that the
    first case does not apply, and (2) that the n' that appears on
    the ev_SS case must be the same as n.  This allows us to
    complete the proof:

```

定理 evSS_ev：∀n，

ev (S (S n)) → ev n。

证明。

引入 n E。

反演 E 为 [| n' E']。

(* 我们现在处于 E = ev_SS n' E' 情况下。*)

应用 E'。

完成。

```

    By using inversion, we can also apply the principle of explosion
    to "obviously contradictory" hypotheses involving inductive
    properties. For example:

```

定理 one_not_even：¬ ev 1。

证明。

引入 H。反演 H。完成。

```

#### Exercise: 1 star (inversion_practice)

    Prove the following results using inversion.

```

定理 SSSSev__even：∀n，

ev (S (S (S (S n)))) → ev n。

证明。

(* 在此填写内容 *) 已承认。

定理 even5_nonsense：

ev 5 → 2 + 2 = 9。

证明。

(* 在此填写内容 *) 已承认。

```

    ☐ 

    The way we've used inversion here may seem a bit
    mysterious at first.  Until now, we've only used inversion on
    equality propositions, to utilize injectivity of constructors or
    to discriminate between different constructors.  But we see here
    that inversion can also be applied to analyzing evidence for
    inductively defined propositions.

    Here's how inversion works in general.  Suppose the name I
    refers to an assumption P in the current context, where P has
    been defined by an Inductive declaration.  Then, for each of the
    constructors of P, inversion I generates a subgoal in which
    I has been replaced by the exact, specific conditions under
    which this constructor could have been used to prove P.  Some of
    these subgoals will be self-contradictory; inversion throws
    these away.  The ones that are left represent the cases that must
    be proved to establish the original goal.  For those, inversion
    adds all equations into the proof context that must hold of the
    arguments given to P (e.g., S (S n') = n in the proof of
    evSS_ev). 

    The ev_double exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    even_bool_prop in chapter Logic, we already know that
    those are equivalent to each other). To show that all three
    coincide, we just need the following lemma:

```

引理 ev_even_firsttry：∀n，

ev n → ∃k，n = double k。

证明。

(* 在课堂上运行 *)

```

    We could try to proceed by case analysis or induction on n.  But
    since ev is mentioned in a premise, this strategy would probably
    lead to a dead end, as in the previous section.  Thus, it seems
    better to first try inversion on the evidence for ev.  Indeed,
    the first case can be solved trivially.

```

intros n E. inversion E as [| n' E'].

- (* E = ev_0 *)

∃0\. reflexivity.

- (* E = ev_SS n' E' *) simpl.

```

    Unfortunately, the second case is harder.  We need to show ∃ k, S (S n') = double k, but the only available assumption is
    E', which states that ev n' holds.  Since this isn't directly
    useful, it seems that we are stuck and that performing case
    analysis on E was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on E, we were able to reduce the original result to an similar
    one that involves a *different* piece of evidence for ev: E'.
    More formally, we can finish our proof by showing that

```

∃k', n' = double k',

    which is the same as the original statement, but with n' instead

    of n.  Indeed, it is not difficult to convince Coq that this

    intermediate result suffices.

```
    assert (I : (∃k', n' = double k') →
                (∃k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. ∃(S k'). reflexivity. }
    apply I. (* reduce the original goal to the new one *)

Admitted.

```

## Induction on Evidence

    If this looks familiar, it is no coincidence: We've encountered

    similar problems in the Induction chapter, when trying to use

    case analysis to prove results that required induction.  And once

    again the solution is... induction!

    The behavior of induction on evidence is the same as its

    behavior on  It causes Coq to generate one subgoal for each

    constructor that could have used to build that evidence, while

    providing an induction hypotheses for each recursive occurrence of

    the property in question.

    Let's try our current lemma again:

```
Lemma ev_even : ∀n,
  ev n → ∃k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    ∃0\. reflexivity.
  - (* E = ev_SS n' E'        with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. ∃(S k'). reflexivity.
Qed.

```

    Here, we can see that Coq produced an IH that corresponds to

    E', the single recursive occurrence of ev in its own

    definition.  Since E' mentions n', the induction hypothesis

    talks about n', as opposed to n or some other number.

    The equivalence between the second and third definitions of

    evenness now follows.

```
Theorem ev_even_iff : ∀n,
  ev n ↔ ∃k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

```

    As we will see in later chapters, induction on evidence is a

    recurring technique across many areas, and in particular when

    formalizing the semantics of programming languages, where many

    properties of interest are defined inductively.

    The following exercises provide simple examples of this

    technique, to help you familiarize yourself with it.

#### Exercise: 2 stars (ev_sum)

```
Theorem ev_sum : ∀n m, ev n → ev m → ev (n + m).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### Exercise: 4 stars, advanced, optional (ev_alternate)

    In general, there may be multiple ways of defining a

    property inductively.  For example, here's a (slightly contrived)

    alternative definition for ev:

```
Inductive ev' : nat → Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : ∀n m, ev' n → ev' m → ev' (n + m).

```

    Prove that this definition is logically equivalent to the old

    one.  (You may want to look at the previous theorem when you get

    to the induction step.)

```
Theorem ev'_ev : ∀n, ev' n ↔ ev n.
Proof.
 (* FILL IN HERE *) Admitted.

```

    ☐

#### Exercise: 3 stars, advanced, recommended (ev_ev__ev)

    Finding the appropriate thing to do induction on is a

    bit tricky here:

```
Theorem ev_ev__ev : ∀n m,
  ev (n+m) → ev n → ev m.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### Exercise: 3 stars, optional (ev_plus_plus)

    This exercise just requires applying existing lemmas.  No

    induction or even case analysis is needed, though some of the

    rewriting may be tedious.

```
Theorem ev_plus_plus : ∀n m p,
  ev (n+m) → ev (n+p) → ev (m+p).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

# Inductive Relations

    A proposition parameterized by a number (such as ev)
    can be thought of as a *property* — i.e., it defines
    a subset of nat, namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a *relation* — i.e., it defines a set of pairs for
    which the proposition is provable.

```

Module Playground.

```

    One useful example is the "less than or equal to" relation on
    numbers. 

    The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second.

```

Inductive le : nat → nat → Prop :=

| le_n : ∀n, le n n

| le_S : ∀n m, (le n m) → (le n (S m)).

Notation "m ≤ n" := (le m n).

```

    Proofs of facts about ≤ using the constructors le_n and
    le_S follow the same patterns as proofs about properties, like
    ev above. We can apply the constructors to prove ≤
    goals (e.g., to show that 3≤3 or 3≤6), and we can use
    tactics like inversion to extract information from ≤
    hypotheses in the context (e.g., to prove that (2 ≤ 1) → 2+2=5.) 

    Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly — simpl and
    reflexivity don't do the job, because the proofs aren't just a
    matter of simplifying computations.)

```

Theorem test_le[1] :

3 ≤ 3.

Proof.

(* WORKED IN CLASS *)

apply le_n. Qed.

Theorem test_le[2] :

3 ≤ 6.

Proof.

(* WORKED IN CLASS *)

apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le[3] :

(2 ≤ 1) → 2 + 2 = 5.

Proof.

(* WORKED IN CLASS *)

intros H. inversion H. inversion H[2]. Qed.

```

    The "strictly less than" relation n < m can now be defined
    in terms of le.

```

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

```

    Here are a few more simple relations on numbers:

```

Inductive square_of : nat → nat → Prop :=

| sq : ∀n:nat, square_of n (n * n).

Inductive next_nat : nat → nat → Prop :=

| nn : ∀n:nat, next_nat n (S n).

Inductive next_even : nat → nat → Prop :=

| ne_1 : ∀n, ev (S n) → next_even n (S n)

| ne_2 : ∀n, ev (S (S n)) → next_even n (S (S n)).

```

#### Exercise: 2 stars, optional (total_relation)

    Define an inductive binary relation total_relation that holds
    between every pair of natural numbers.

```

(* 在这里填写*)

```

    ☐ 

#### Exercise: 2 stars, optional (empty_relation)

    Define an inductive binary relation empty_relation (on numbers)
    that never holds.

```

(* 在这里填写*)

```

    ☐ 

#### Exercise: 3 stars, optional (le_exercises)

    Here are a number of facts about the ≤ and < relations that
    we are going to need later in the course.  The proofs make good
    practice exercises.

```

引理 le_trans : ∀m n o，m ≤ n → n ≤ o → m ≤ o。

证明。

(* 在这里填写*) 已证明。

定理 O_le_n : ∀n，

0 ≤ n。

证明。

(* 在这里填写*) 已证明。

定理 n_le_m__Sn_le_Sm : ∀n m，

n ≤ m → S n ≤ S m。

证明。

(* 在这里填写*) 已证明。

定理 Sn_le_Sm__n_le_m : ∀n m，

S n ≤ S m → n ≤ m。

证明。

(* 在这里填写*) 已证明。

定理 le_plus_l : ∀a b，

a ≤ a + b。

证明。

(* 在这里填写*) 已证明。

定理 plus_lt : ∀n[1] n[2] m，

n[1] + n[2] < m →

n[1] < m ∧ n[2] < m。

证明。

展开 lt.

(* 在这里填写*) 已证明。

定理 lt_S : ∀n m，

n < m →

n < S m。

证明。

(* 在这里填写*) 已证明。

定理 leb_complete : ∀n m，

leb n m = true → n ≤ m。

证明。

(* 在这里填写*) 已证明。

```

    Hint: The next one may be easiest to prove by induction on m.

```

定理 leb_correct : ∀n m，

n ≤ m →

leb n m = true。

证明。

(* 在这里填写*) 已证明。

```

    Hint: This theorem can easily be proved without using induction.

```

定理 leb_true_trans : ∀n m o，

leb n m = true → leb m o = true → leb n o = true。

证明。

(* 在这里填写*) 已证明。

```

#### Exercise: 2 stars, optional (leb_iff)

```

定理 leb_iff : ∀n m，

leb n m = true ↔ n ≤ m。

证明。

(* 在这里填写*) 已证明。

```

    ☐

```

模块 R。

```

#### Exercise: 3 stars, recommendedM (R_provability)

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers:

```

归纳定义 R：nat → nat → nat → Prop :=

| c[1] : R 0 0 0

| c[2] : ∀m n o, R m n o → R (S m) n (S o)

| c[3] : ∀m n o, R m n o → R m (S n) (S o)

| c[4] : ∀m n o, R (S m) (S n) (S (S o)) → R m n o

| c[5] : ∀m n o, R m n o → R n m o。

```

*   Which of the following propositions are provable? 

    *   R 1 1 2

    *   R 2 2 6 

*   If we dropped constructor c[5] from the definition of R, would the set of provable propositions change? Briefly (1 sentence) explain your answer. 

*   If we dropped constructor c[4] from the definition of R, would the set of provable propositions change? Briefly (1 sentence) explain your answer.

    (* FILL IN HERE *)

    ☐ 

#### Exercise: 3 stars, optional (R_fact)

    The relation R above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq?

```

定义 fR : nat → nat → nat

(* 用":= _your_definition_ ." 替换这一行*）已证明。

定理 R_equiv_fR : ∀m n o, R m n o ↔ fR m n = o。

证明。

(* 在这里填写*) 已证明。

```

    ☐

```

结束 R。

```

#### Exercise: 4 stars, advanced (subsequence)

    A list is a *subsequence* of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

```

[1;2;3]

    是每个列表的子序列

```
      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is *not* a subsequence of any of the lists

```

[1;2]

[1;3]

[5;6;2;1;7;3;8].

+   定义一个关于自然数列表的归纳命题 subseq，捕捉什么是子序列的含义。（提示：你需要三种情况。）

+   证明 subseq_refl，即子序列是自反的，即任何列表都是其自身的子序列。

+   证明 subseq_app，对于任意列表 l[1]、l[2] 和 l[3]，如果 l[1] 是 l[2] 的子序列，则 l[1] 也是 l[2] ++ l[3] 的子序列。

+   （可选，更难）证明 subseq_trans，即子序列是传递的 — 即，如果 l[1] 是 l[2] 的子序列，而 l[2] 是 l[3] 的子序列，则 l[1] 是 l[3] 的子序列。提示：谨慎选择你的归纳方式！

```
(* FILL IN HERE *)

```

    ☐

#### 练习：2 星，可选 M（R_provability2）

    假设我们给 Coq 下面的定义：

```
    Inductive R : nat → list nat → Prop :=
      | c[1] : R 0 []
      | c[2] : ∀n l, R n l → R (S n) (n :: l)
      | c[3] : ∀n l, R (S n) l → R n l.

    Which of the following propositions are provable?

*   R 2 [1;0]

*   R 1 [1;2;1;0]

*   R 6 [3;2;1;0]

    ☐

```

# 案例研究：正则表达式

    ev 属性提供了一个简单的例子来说明

    归纳定义和关于推理的基本技术

    但这并不是非常令人兴奋 — 毕竟，它是

    等同于我们之前有的两种非归纳的偶数性质

    已经看到，并且似乎没有提供任何具体的好处

    他们。为了更好地展示归纳的力量

    定义，我们现在展示如何使用它们来建模一个经典的

    计算机科学中的概念：*正则表达式*。

    正则表达式是一种描述字符串的简单语言，

    如下定义：

```
Inductive reg_exp (T : Type) : Type :=
| EmptySet : reg_exp T
| EmptyStr : reg_exp T
| Char : T → reg_exp T
| App : reg_exp T → reg_exp T → reg_exp T
| Union : reg_exp T → reg_exp T → reg_exp T
| Star : reg_exp T → reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

```

    注意这个定义是*多态的*：正则

    reg_exp T 中的表达式描述了由字符组成的字符串

    从 T 中 - 即 T 元素的列表。

    （我们略微偏离标准做法，因为我们不这样做

    需要 T 类型是有限的。 这导致了一种

    正则表达式的不同理论，但区别并不大

    对于我们的目的很重要。）

    我们通过以下方式连接正则表达式和字符串

    定义了正则表达式何时与某些

    字符串：

+   表达式 EmptySet 不匹配任何字符串。

+   表达式 EmptyStr 匹配空字符串[]。

+   表达式 Char x 匹配一个字符的字符串[x]。

+   如果 re[1]匹配 s[1]，并且 re[2]匹配 s[2]，那么 App re[1] re[2]匹配 s[1] ++ s[2]。

+   如果 re[1]和 re[2]中至少有一个与 s 匹配，则 Union re[1] re[2]与 s 匹配。

+   最后，如果我们可以将某个字符串 s 写成一系列字符串 s = s_1 ++ ... ++ s_k 的连接，并且表达式 re 匹配每个字符串 s_i，则 Star re 匹配 s。

    作为一种特殊情况，字符串序列可能为空，因此无论 re 是什么，Star re 始终匹配空字符串[]。

    我们可以很容易地将这个非正式定义转换为一个

    通过以下方式归纳一个：

```
Inductive exp_match {T} : list T → reg_exp T → Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : ∀x, exp_match [x] (Char x)
| MApp : ∀s[1] re[1] s[2] re[2],
           exp_match s[1] re[1] →
           exp_match s[2] re[2] →
           exp_match (s[1] ++ s[2]) (App re[1] re[2])
| MUnionL : ∀s[1] re[1] re[2],
              exp_match s[1] re[1] →
              exp_match s[1] (Union re[1] re[2])
| MUnionR : ∀re[1] s[2] re[2],
              exp_match s[2] re[2] →
              exp_match s[2] (Union re[1] re[2])
| MStar0 : ∀re, exp_match [] (Star re)
| MStarApp : ∀s[1] s[2] re,
               exp_match s[1] re →
               exp_match s[2] (Star re) →
               exp_match (s[1] ++ s[2]) (Star re).

```

    同样，为了可读性，我们还可以使用

    推理规则符号。 与此同时，让我们引入一个更多

    可读的中缀表示法。

```
Notation "s =~ re" := (exp_match s re) (at level 80).

```

        |

                        （MEmpty）

        |

* * *

        |

                        [] =~ EmptyStr

        |

                    |

        |

                        (MChar)

        |

* * *

        |

                        [x] =~ Char x

        |

                    |

                        s[1] =~ re[1]    s[2] =~ re[2]

        |

                        （MApp）

        |

* * *

        |

                        s[1] ++ s[2] =~ App re[1] re[2]

        |

                    |

                        s[1] =~ re[1]

        |

                        （MUnionL）

        |

* * *

        |

                        s[1] =~ Union re[1] re[2]

        |

                    |

                        s[2] =~ re[2]

        |

                        （MUnionR）

        |

* * *

        |

                        s[2] =~ Union re[1] re[2]

        |

                    |

        |

                        （MStar0）

        |

* * *

        |

                        [] =~ Star re

        |

                    |

                        s[1] =~ re    s[2] =~ Star re

        |

                        （MStarApp）

        |

* * *

        |

                        s[1] ++ s[2] =~ Star re

        |

                    |

    注意，这些规则与非正式规则并不完全相同

    我们在本节开头给出的那些。首先，

    不需要显式包括一个规则声明没有字符串

    匹配 EmptySet; 我们只是碰巧没有包括任何规则

    会导致某些字符串匹配 EmptySet。（实际上，

    不允许我们的归纳定义的语法

    给出这样的“负规则”。）

    其次，Union 和 Star 的非正式规则对应

    对于每个两个构造函数：MUnionL / MUnionR，和 MStar0 /

    MStarApp。 结果在逻辑上等价于原始

    规则但在 Coq 中更方便使用，因为递归

    出现 exp_match 的情况被直接作为参数提供给

    构造函数，使得在证据上执行归纳更容易。

    （下面的 exp_match_ex[1]和 exp_match_ex[2]练习要求您

    要证明在归纳声明中给出的构造函数

    以及从更直接的转录中产生的那些

    非正式规则确实是等价的。）

    让我们用一些例子来说明这些规则。

```
Example reg_exp_ex[1] : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex[2] : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

```

    （注意最后一个例子如何应用 MApp 到字符串[1]

    和[2]直接。 由于目标提到了[1; 2]而不是

    [1] ++ [2]，Coq 将无法确定如何拆分

    字符串本身。）

    使用反演，我们还可以展示某些字符串*不*

    匹配一个正则表达式：

```
Example reg_exp_ex[3] : ¬ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

```

    我们可以定义辅助函数来帮助编写正则

    表达式中获得。reg_exp_of_list 函数构造一个正则

    与其接收的列表完全匹配的表达式

    参数：

```
Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] ⇒ EmptyStr
  | x :: l' ⇒ App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex[4] : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

```

    我们还可以证明关于 exp_match 的一般事实。例如，

    以下引理表明，每个与 re 匹配的字符串 s

    也与 Star re 匹配。

```
Lemma MStar1 :
  ∀T s (re : reg_exp T) ,
    s =~ re →
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite ← (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

```

    （注意使用 app_nil_r 将定理的目标更改为

    与 MStarApp 预期的形状完全相同。）

#### 练习：3 星（exp_match_ex[1]）

    以下引理表明，给出的非正式匹配规则

    章节开头可以从正式

    归纳定义。

```
Lemma empty_is_empty : ∀T (s : list T),
  ¬ (s =~ EmptySet).
Proof.
  (* FILL IN HERE *) Admitted.

Lemma MUnion' : ∀T (s : list T) (re[1] re[2] : reg_exp T),
  s =~ re[1] ∨ s =~ re[2] →
  s =~ Union re[1] re[2].
Proof.
  (* FILL IN HERE *) Admitted.

```

    下一个引理是根据来自

    Poly 章节：如果 ss：list（list T）表示一个序列

    字符串 s[1]，...，sn，然后折叠 app ss []的结果是

    将它们全部连接在一起。

```
Lemma MStar' : ∀T (ss : list (list T)) (re : reg_exp T),
  (∀s, In s ss → s =~ re) →
  fold app ss [] =~ Star re.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：4 星（reg_exp_of_list）

    证明 reg_exp_of_list 满足以下

    规范：

```
Lemma reg_exp_of_list_spec : ∀T (s[1] s[2] : list T),
  s[1] =~ reg_exp_of_list s[2] ↔ s[1] = s[2].
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    由于 exp_match 的定义具有递归

    结构，我们可能期望涉及正则的证明

    表达式通常需要对证据进行归纳。对于

    例如，假设我们想要证明以下直观的

    结果：如果正则表达式 re 匹配某个字符串 s，则

    s 的所有元素必须在 re 中的某处出现。为了陈述这一点

    定理，我们首先定义一个列出所有

    出现在正则表达式中的字符：

```
Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet ⇒ []
  | EmptyStr ⇒ []
  | Char x ⇒ [x]
  | App re[1] re[2] ⇒ re_chars re[1] ++ re_chars re[2]
  | Union re[1] re[2] ⇒ re_chars re[1] ++ re_chars re[2]
  | Star re ⇒ re_chars re
  end.

```

    然后我们可以将我们的定理表述如下：

```
Theorem in_re_match : ∀T (s : list T) (re : reg_exp T) (x : T),
  s =~ re →
  In x s →
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [
        |x'
        |s[1] re[1] s[2] re[2] Hmatch1 IH[1] Hmatch2 IH[2]
        |s[1] re[1] re[2] Hmatch IH|re[1] s[2] re[2] Hmatch IH
        |re|s[1] s[2] re Hmatch1 IH[1] Hmatch2 IH[2]].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite in_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s[1] *)
      left. apply (IH[1] Hin).
    + (* In x s[2] *)
      right. apply (IH[2] Hin).
  - (* MUnionL *)
    simpl. rewrite in_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite in_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.

```

    在 MStarApp 情况下会发生一些有趣的事情。我们获得

    *两个*归纳假设：一个适用于 x 出现在

    s[1]（与 re 匹配），第二个适用于 x

    出现在 s[2]中（与 Star re 匹配）。这是一个很好的

    说明为什么我们需要对 exp_match 的证据进行归纳

    与 re 相反：后者只会提供归纳

    与 re 匹配的字符串的假设，这将不允许我们

    推理 In x s[2]的情况

```
  - (* MStarApp *)
    simpl. rewrite in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s[1] *)
      apply (IH[1] Hin).
    + (* In x s[2] *)
      apply (IH[2] Hin).
Qed.

```

#### 练习：4 星（re_not_empty）

    编写一个测试 re_not_empty 的递归函数，测试是否

    正则表达式匹配某个字符串。证明你的函数

    是正确的。

```
Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma re_not_empty_correct : ∀T (re : reg_exp T),
  (∃s, s =~ re) ↔ re_not_empty re = true.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

## 记住策略

    归纳策略中一个可能令人困惑的特点是

    它很高兴地让你尝试设置一个关于术语的归纳

    这并不够通用。这样做的效果是失去

    信息（就像 destruct 可以做的那样），让你无法

    完成证明。这里有一个例子：

```
Lemma star_app: ∀T (s[1] s[2] : list T) (re : reg_exp T),
  s[1] =~ Star re →
  s[2] =~ Star re →
  s[1] ++ s[2] =~ Star re.
Proof.
  intros T s[1] s[2] re H[1].

```

    仅仅对 H[1]进行反演并不能让我们走得很远

    递归情况。（试试看！）。所以我们需要归纳。这是一个天真的

    第一次尝试：

```
  induction H[1]
    as [|x'|s[1] re[1] s[2]' re[2] Hmatch1 IH[1] Hmatch2 IH[2]
        |s[1] re[1] re[2] Hmatch IH|re[1] s[2]' re[2] Hmatch IH
        |re''|s[1] s[2]' re'' Hmatch1 IH[1] Hmatch2 IH[2]].

```

    但现在，尽管我们得到了七种情况（正如我们从中期望的那样

    exp_match 的定义），我们失去了一个非常重要的部分

    从 H[1]中获取信息：s[1]匹配了 s 中的某个内容的事实

    形式 Star re。这意味着我们必须为*所有*

    这个定义的七个构造，尽管除了两个之外的所有构造

    它们（MStar0 和 MStarApp）是矛盾的。我们仍然可以

    使证明通过一些构造函数，例如

    MEmpty...

```
  - (* MEmpty *)
    simpl. intros H. apply H.

```

    ...但大多数情况都卡住了。例如，对于 MChar，我们

    必须展示

```
    s[2] =~ Char x' → x' :: s[2] =~ Char x',

    which is clearly impossible.

```

- （* MChar。卡住了... *）

中止。

```

    The problem is that induction over a Prop hypothesis only works
    properly with hypotheses that are completely general, i.e., ones
    in which all the arguments are variables, as opposed to more
    complex expressions, such as Star re.

    (In this respect, induction on evidence behaves more like
    destruct than like inversion.)

    We can solve this problem by generalizing over the problematic
    expressions with an explicit equality:

```

Lemma star_app: ∀T（s[1] s[2]：列表 T）（re re'：reg_exp T），

s[1] =~ re' →

re' = 星星 re →

s[2] =~ 星星 re →

s[1] ++ s[2] =~ 星星 re。

```

    We can now proceed by performing induction over evidence directly,
    because the argument to the first hypothesis is sufficiently
    general, which means that we can discharge most cases by inverting
    the re' = Star re equality in the context.

    This idiom is so common that Coq provides a tactic to
    automatically generate such equations for us, avoiding thus the
    need for changing the statements of our theorems. 

    Invoking the tactic remember e as x causes Coq to (1) replace
    all occurrences of the expression e by the variable x, and (2)
    add an equation x = e to the context.  Here's how we can use it
    to show the above result:

```

中止。

Lemma star_app: ∀T（s[1] s[2]：列表 T）（re：reg_exp T），

s[1] =~ 星星 re →

s[2] =~ 星星 re →

s[1] ++ s[2] =~ 星星 re。

Proof。

intros T s[1] s[2] re H[1]。

记住（星星 re）作为 re'。

```

    We now have Heqre' : re' = Star re.

```

泛化依赖于 s[2]。

对 H[1] 进行归纳

如[ | x' | s[1] re[1] s[2]' re[2] Hmatch1 IH[1] Hmatch2 IH[2]

|s[1] re[1] re[2] Hmatch IH|re[1] s[2]' re[2] Hmatch IH

|re''|s[1] s[2]' re'' Hmatch1 IH[1] Hmatch2 IH[2]]。

```

    The Heqre' is contradictory in most cases, which allows us to
    conclude immediately.

```

- （* MEmpty *）反演 Heqre'。

- （* MChar *）反演 Heqre'。

- （* MApp *）反演 Heqre'。

- （* MUnionL *）反演 Heqre'。

- （* MUnionR *）反演 Heqre'。

```

    The interesting cases are those that correspond to Star.  Note
    that the induction hypothesis IH[2] on the MStarApp case
    mentions an additional premise Star re'' = Star re', which
    results from the equality generated by remember.

```

- （* MStar0 *）

反演 Heqre'。intros s H。应用 H。

- （* MStarApp *）

反演 Heqre'。在 IH[2]，Hmatch1 中重写 H[0]。

intros s[2] H[1]。重写 ← app_assoc。

应用 MStarApp。

+ 应用 Hmatch1。

+ 应用 IH[2]。

* 一致性。

* 应用 H[1]。

Qed。

```

#### Exercise: 4 stars (exp_match_ex[2])

    The MStar'' lemma below (combined with its converse, the
    MStar' exercise above), shows that our definition of exp_match
    for Star is equivalent to the informal one given previously.

```

Lemma MStar''：∀T（s：列表 T）（re：reg_exp T），

s =~ 星星 re →

∃ss：列表（列表 T），

s = 折叠 app ss []。

∧ ∀s'，In s' ss → s' =~ re。

Proof。

（* 填写这里 *）已承认。

```

    ☐ 

#### Exercise: 5 stars, advanced (pumping)

    One of the first really interesting theorems in the theory of
    regular expressions is the so-called *pumping lemma*, which
    states, informally, that any sufficiently long string s matching
    a regular expression re can be "pumped" by repeating some middle
    section of s an arbitrary number of times to produce a new
    string also matching re.

    To begin, we need to define "sufficiently long."  Since we are
    working in a constructive logic, we actually need to be able to
    calculate, for each regular expression re, the minimum length
    for strings s to guarantee "pumpability."

```

模块泵。

固定泵定数 {T}（re：reg_exp T）：自然数 :=

匹配 re 与

| EmptySet ⇒ 0

| EmptyStr ⇒ 1

| 字符 _ ⇒ 2

| App re[1] re[2] ⇒

泵定数 re[1] + 泵定数 re[2]

| 联合 re[1] re[2] ⇒

泵定数 re[1] + 泵定数 re[2]

| 星星 _ ⇒ 1

结束。

```

    Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times.

```

固定点 napp {T}（n：自然数）（l：列表 T）：列表 T :=

匹配 n 与

| 0 ⇒ []

| S n' ⇒ l ++ napp n' l

结束。

Lemma napp_plus: ∀T（n m：自然数）（l：列表 T），

napp（n + m）l = napp n l ++ napp m l。

Proof。

intros T n m l。

对 n 进行归纳作为 [|n IHn]。

- 一致性。

- 简化。重写 IHn，app_assoc。一致性。

Qed。

```

    Now, the pumping lemma itself says that, if s =~ re and if the
    length of s is at least the pumping constant of re, then s
    can be split into three substrings s[1] ++ s[2] ++ s[3] in such a way
    that s[2] can be repeated any number of times and the result, when
    combined with s[1] and s[3] will still match re.  Since s[2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching re that are
    as long as we like.

```

Lemma pumping：∀T（re：reg_exp T）s，

s =~ re →

泵定数 re ≤ s 的长度 →

∃s[1] s[2] s[3]，

s = s[1] ++ s[2] ++ s[3] ∧

s[2] ≠ [] ∧

∀m，s[1] ++ napp m s[2] ++ s[3] =~ re。

```

    To streamline the proof (which you are to fill in), the omega
    tactic, which is enabled by the following Require, is helpful in
    several places for automatically completing tedious low-level
    arguments involving equalities or inequalities over natural
    numbers.  We'll return to omega in a later chapter, but feel
    free to experiment with it now if you like.  The first case of the
    induction gives an example of how it is used.

```

Require Import Coq.omega.Omega。

Proof。

intros T re s Hmatch。

对 Hmatch 进行归纳

如[ | x | s[1] re[1] s[2] re[2] Hmatch1 IH[1] Hmatch2 IH[2]

| s[1] re[1] re[2] Hmatch IH | re[1] s[2] re[2] Hmatch IH

| re | s[1] s[2] re Hmatch1 IH[1] Hmatch2 IH[2] ]。

- （* MEmpty *）

简化。omega。

（* 填写这里 *）已承认。

结束泵。

```

    ☐

```

# 案例研究：改进反射

    我们在 Logic 章节中看到，我们经常需要

    将布尔计算与 Prop 中的语句相关联。但

    执行这种转换的方式可能导致

    在繁琐的证明脚本中。考虑以下证明的证明

    定理：

```
Theorem filter_not_empty_In : ∀n l,
  filter (beq_nat n) l ≠ [] →
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_nat n m) eqn:H.
    + (* beq_nat n m = true *)
      intros _. rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + (* beq_nat n m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed. 
```

    在 destruct 后的第一个分支中，我们明确应用

    由 beq_nat_true_iff 引理生成的方程式到

    解构 beq_nat n m，将假设 beq_nat n m = true 转换为假设 n = m；然后我们必须重写

    使用这个假设来完成这种情况。

    我们可以通过定义一个归纳命题来简化这个过程

    为 beq_nat n m 提供更好的案例分析原则。

    而不是生成一个等式如 beq_nat n m = true，

    这通常不直接有用，这个原则给了我们

    我们真正需要的假设：n = m。

    实际上我们会定义一些更一般的东西，可以

    用于任意属性（而不仅仅是相等）：

```
Module FirstTry.

Inductive reflect : Prop → bool → Prop :=
| ReflectT : ∀(P:Prop), P → reflect P true
| ReflectF : ∀(P:Prop), ¬ P → reflect P false.

```

    在解释这个之前，让我们稍微重新排列一下：由于

    ReflectT 和 ReflectF 类型的开始都是

    ∀ (P:Prop)，我们可以使定义更易读一些

    通过使 P 成为整个参数的一部分更容易处理

    归纳声明。

```
End FirstTry.

Inductive reflect (P : Prop) : bool → Prop :=
| ReflectT : P → reflect P true
| ReflectF : ¬ P → reflect P false.

```

    反射属性接受两个参数：一个命题

    P 和一个布尔值 b。直觉上，它陈述了属性

    P 在（即等价于）布尔值 b 中*反映*：P

    当且仅当 b = true 时成立。要看到这一点，请注意，通过

    定义，我们能够产生证据表明 reflect P true 成立的唯一方法是通过显示 P 为真并使用

    ReflectT 构造函数。如果我们反转这个陈述，这意味着

    应该能够从一个中提取证据证明 P

    reflect P true 的证明。反之，显示的唯一方法

    反映 P false 是通过将证据组合为 ¬ P 与

    ReflectF 构造函数。

    很容易形式化这种直觉并展示这两个

    陈述确实是等价的：

```
Theorem iff_reflect : ∀P b, (P ↔ b = true) → reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

```

#### 练习：2 星，推荐（reflect_iff）

```
Theorem reflect_iff : ∀P b, reflect P b → (P ↔ b = true).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    Reflect 相对于正常的“当且仅当”的优势

    连接词是，通过析构一个假设或引理

    形式 reflect P b，我们可以对 b 进行案例分析��时

    同时在两个中生成适当的假设

    分支（第一个子目标中的 P 和第二个子目标中的 ¬ P）。

```
Lemma beq_natP : ∀n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m.
  apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

```

    filter_not_empty_In 的新证明现在如下。

    注意将析构和应用的调用组合成一个

    单次调用析构。

    （要清楚地看到这一点，请看两个证明

    使用 Coq 中的 filter_not_empty_In 并观察

    证明状态在第一个案例的开始处

    析构。）

```
Theorem filter_not_empty_In' : ∀n l,
  filter (beq_nat n) l ≠ [] →
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_natP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed. 
```

#### 练习：3 星，推荐（beq_natP_practice）

    使用 beq_natP 如上所述来证明以下内容：

```
Fixpoint count n l :=
  match l with
  | [] ⇒ 0
  | m :: l' ⇒ (if beq_nat n m then 1 else 0) + count n l'
  end.

Theorem beq_natP_practice : ∀n l,
  count n l = 0 → ~(In n l).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    这种技术只为我们带来了一点方便，用于

    我们在这里看到的证明，但是一致使用 reflect 经常

    导致明显更短更清晰的脚本，随着证明的进行

    更大。我们将在后面的章节中看到更多例子。

    反射属性的使用被*SSReflect*所推广，

    一个 Coq 库已被用来形式化重要结果

    数学，包括四色定理和

    菲特-汤普森定理。SSReflect 的名称代表*小规模反射*，即，广泛使用反射来简化

    通过布尔计算进行小的证明步骤。

```

# Additional Exercises

#### Exercise: 3 stars, recommended (nostutter)

    Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  The property "nostutter mylist" means that
    mylist does not stutter.  Formulate an inductive definition for
    nostutter.  (This is different from the NoDup property in the
    exercise above; the sequence 1;4;1 repeats but does not
    stutter.)

```

归纳无重复 {X:Type}：列表 X → 命题 :=

(* 在这里填写 *)

。

```

    Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining nostutter.  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)

```

例子 test_nostutter_1: nostutter [3;1;4;1;5;6]。

(* 在这里填写 *) 已承认。

(*    证明。重复构造函数；应用 beq_nat_false_iff；自动。   完成。*)

示例 test_nostutter_2:  nostutter (@nil nat)。

(* 在此填写*) 已承认。

(*    证明。重复构造; 应用 beq_nat_false_iff; 自动。Qed。*)

示例 test_nostutter_3:  nostutter [5]。

(* 在此填写*) 已承认。

(*    证明。重复构造; 应用 beq_nat_false; 自动。Qed。*)

示例 test_nostutter_4:      不是 (nostutter [3;1;1;4])。

(* 在此填写*) 已承认。

(*    证明。介绍。 重复匹配目标  h: nostutter _ |- _ => 反转 h; 清除 h; 替换  结束。 反驳 H[1]; 自动。Qed。*)

```

    ☐ 

#### Exercise: 4 stars, advanced (filter_challenge)

    Let's prove that our definition of filter from the Poly
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list l is an "in-order merge" of l[1] and l[2] if it contains
    all the same elements as l[1] and l[2], in the same order as l[1]
    and l[2], but possibly interleaved.  For example,

```

[1;4;6;2;3]

    是一个顺序合并的

```
    [1;6;2]

    and

```

[4;3]。

    现在，假设我们有一个集合 X，一个函数 test：X→bool，和一个

    类型为 list X 的列表 l。进一步假设 l 是一个

    对两个列表 l[1]和 l[2]进行顺序合并，使得每个项目

    在 l[1]中满足测试且在 l[2]中没有项目满足测试。然后

    filter test l = l[1]。

    将此规范转化为一个 Coq 定理并证明

    它。（你需要开始定义一个列表的含义

    被另外两个合并。用一个归纳关系来做到这一点，

    不是一个 Fixpoint。）

```
(* FILL IN HERE *)

```

    ☐

#### 练习：5 星，高级，可选（filter_challenge_2）

    另一种描述 filter 行为的方式是

    这个：在所有具有测试属性的 l 子序列中

    对它们的所有成员求值为 true，filter test l 是

    最长。形式化这个声明并证明它。

```
(* FILL IN HERE *)

```

    ☐

#### 练习：4 星，可选（palindromes）

    回文是一个反向读取相同的序列

    向前。

+   定义一个关于列表 X 的归纳命题 pal，捕捉回文的含义。（提示：你需要三种情况。你的定义应基于列表的结构；不仅仅是一个单一的构造函数，就像

    ```
      c : ∀l, l = rev l → pal l

     may seem obvious, but will not work very well.) 

    ```

+   证明（pal_app_rev）

    ```
     ∀l, pal (l ++ rev l).

    ```

+   证明（pal_rev）

    ```
     ∀l, pal l → l = rev l.

    ```

```
(* FILL IN HERE *)

```

    ☐

#### 练习：5 星，可选（palindrome_converse）

    再次，由于

    缺乏证据。使用你从中定义的 pal

    前一个练习，证明

```
     ∀l, l = rev l → pal l.

```

(* 在此填写*)

```

    ☐ 

#### Exercise: 4 stars, advanced, optional (NoDup)

    Recall the definition of the In property from the Logic
    chapter, which asserts that a value x appears at least once in a
    list l:

```

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=    match l with    |  => False    | x' :: l' => x' = x \/ In A x l'    end *)

```

    Your first task is to use In to define a proposition disjoint X l[1] l[2], which should be provable exactly when l[1] and l[2] are
    lists (with elements of type X) that have no elements in
    common.

```

(* 在此填写*)

```

    Next, use In to define an inductive proposition NoDup X l, which should be provable exactly when l is a list (with
    elements of type X) where every member is different from every
    other.  For example, NoDup nat [1;2;3;4] and NoDup bool [] should be provable, while NoDup nat [1;2;1] and
    NoDup bool [true;true] should not be.

```

(* 在此填写*)

```

    Finally, state and prove one or more interesting theorems relating
    disjoint, NoDup and ++ (list append).

```

(* 在此填写*)

```

    ☐ 

#### Exercise: 4 stars, advanced, optional (pigeonhole principle)

    The *pigeonhole principle* states a basic fact about counting: if
   we distribute more than n items into n pigeonholes, some
   pigeonhole must contain at least two items.  As often happens, this
   apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... 

    First prove an easy useful lemma.

```

引理 in_split: ∀(X:Type) (x:X) (l:list X)，

在 x l 中→

∃l[1] l[2]，l = l[1] ++ x :: l[2]。

证明。

(* 在此填写*) 已承认。

```

    Now define a property repeats such that repeats X l asserts
    that l contains at least one repeated element (of type X).

```

归纳重复{X:Type}：列表 X 的重复。

(* 在此填写*)

。

```

    Now, here's a way to formalize the pigeonhole principle.  Suppose
    list l[2] represents a list of pigeonhole labels, and list l[1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label — i.e., list l[1] must contain repeats.

    This proof is much easier if you use the excluded_middle
    hypothesis to show that In is decidable, i.e., ∀ x l, (In x l) ∨ ¬ (In x l).  However, it is also possible to make the proof
    go through *without* assuming that In is decidable; if you
    manage to do this, you will not need the excluded_middle
    hypothesis.

```

鸽巢原理：∀(X:Type) (l[1]  l[2]:list X)，

排除中间→

(∀x, In x l[1] → In x l[2]) →

长度 l[2] < 长度 l[1] →

重复 l[1]。

证明。

intros X l[1]。对 l[1]进行归纳，如同 [|x l[1]' IHl1']。

(* 在此填写*) 已承认。

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

```
