# SmallstepSmall-step Operational Semantics

```

```

Require Import Coq.Arith.Arith.

Require Import Coq.Arith.EqNat.

Require Import Coq.omega.Omega.

Require Import Coq.Lists.List.

Import ListNotations.

Require Import Maps.

Require Import Imp.

```

    The evaluators we have seen so far (for aexps, bexps,
    commands, ...) have been formulated in a "big-step" style: they
    specify how a given expression can be evaluated to its final
    value (or a command plus a store to a final store) "all in one big
    step."

    This style is simple and natural for many purposes — indeed,
    Gilles Kahn, who popularized it, called it *natural semantics*.
    But there are some things it does not do well.  In particular, it
    does not give us a natural way of talking about *concurrent*
    programming languages, where the semantics of a program — i.e.,
    the essence of how it behaves — is not just which input states
    get mapped to which output states, but also includes the
    intermediate states that it passes through along the way, since
    these states can also be observed by concurrently executing code.

    Another shortcoming of the big-step style is more technical, but
    critical in many situations.  Suppose we want to define a variant
    of Imp where variables could hold *either* numbers *or* lists of
    numbers.  In the syntax of this extended language, it will be
    possible to write strange expressions like 2 + nil, and our
    semantics for arithmetic expressions will then need to say
    something about how such expressions behave.  One possibility is
    to maintain the convention that every arithmetic expressions
    evaluates to some number by choosing some way of viewing a list as
    a number — e.g., by specifying that a list should be interpreted
    as 0 when it occurs in a context expecting a number.  But this
    is really a bit of a hack.

    A much more natural approach is simply to say that the behavior of
    an expression like 2+nil is *undefined* — i.e., it doesn't
    evaluate to any result at all.  And we can easily do this: we just
    have to formulate aeval and beval as Inductive propositions
    rather than Fixpoints, so that we can make them partial functions
    instead of total ones.

    Now, however, we encounter a serious deficiency.  In this
    language, a command might fail to map a given starting state to
    any ending state for *two quite different reasons*: either because
    the execution gets into an infinite loop or because, at some
    point, the program tries to do an operation that makes no sense,
    such as adding a number to a list, so that none of the evaluation
    rules can be applied.

    These two outcomes — nontermination vs. getting stuck in an
    erroneous configuration — are quite different.  In particular, we
    want to allow the first (permitting the possibility of infinite
    loops is the price we pay for the convenience of programming with
    general looping constructs like while) but prevent the
    second (which is just wrong), for example by adding some form of
    *typechecking* to the language.  Indeed, this will be a major
    topic for the rest of the course.  As a first step, we need a way
    of presenting the semantics that allows us to distinguish
    nontermination from erroneous "stuck states."

    So, for lots of reasons, we'd like to have a finer-grained way of
    defining and reasoning about program behaviors.  This is the topic
    of the present chapter.  We replace the "big-step" eval relation
    with a "small-step" relation that specifies, for a given program,
    how the "atomic steps" of computation are performed.

```

# 一个玩具语言

    为了节省空间，讨论让我们回到一个

    极其简单的语言仅包含常数和

    加法。（我们使用单个字母 —— C 和 P（对于命令和

    Plus） —— 作为构造器名称，简洁起见。）在

    章节，我们将看到如何将相同的技术应用到完整

    Imp 语言。

```
Inductive tm : Type :=
  | C : nat → tm         (* Constant *)
  | P : tm → tm → tm. (* Plus *)

```

    这是这种语言的标准求值器，编写于

    到目前为止我们一直在使用的大步骤样式。

```
Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n ⇒ n
  | P a[1] a[2] ⇒ evalF a[1] + evalF a[2]
  end.

```

    这是相同的求值器，完全相同地编写

    样式，但被规定为归纳定义的关系。再次，

    我们使用符号 t ⇓ n 表示“t 评估为 n”。

        |

                        （E_Const）

        |

* * *

        |

                        C n ⇓ n

        |

                    |

                        t[1] ⇓ n[1]

        |

                    |

                        t[2] ⇓ n[2]

        |

                        （E_Plus）

        |

* * *

        |

                        P t[1] t[2] ⇓ n[1] + n[2]

        |

                    |

```
Reserved Notation " t '⇓' n " (at level 50, left associativity).

Inductive eval : tm → nat → Prop :=

      | E_Const : ∀n,
      C n ⇓ n
  | E_Plus : ∀t[1] t[2] n[1] n[2],
      [t[1]](Smallstep.html#t<sub>1</sub>) ⇓ [n[1]](Smallstep.html#n<sub>1</sub>) →
      [t[2]](Smallstep.html#t<sub>2</sub>) ⇓ [n[2]](Smallstep.html#n<sub>2</sub>) →
      P [t[1]](Smallstep.html#t<sub>1</sub>) [t[2]](Smallstep.html#t<sub>2</sub>) ⇓ ([n[1]](Smallstep.html#n<sub>1</sub>) + [n[2]](Smallstep.html#n<sub>2</sub>))

  where " t '⇓' n " := (eval t n).

Module SimpleArith1.

```

    现在，这是相应的 *小步* 评估关系。

        |

                        （ST_PlusConstConst）

        |

* * *

        |

                        P (C n[1]) (C n[2]) ⇒ C (n[1] + n[2])

        |

                    |

                        t[1] ⇒ t[1]'

        |

                        （ST_Plus1）

        |

* * *

        |

                        P t[1] t[2] ⇒ P t[1]' t[2]

        |

                    |

                        t[2] ⇒ t[2]'

        |

                        （ST_Plus2）

        |

* * *

        |

                        P (C n[1]) t[2] ⇒ P (C n[1]) t[2]'

        |

                    |

```
Reserved Notation " t '⇒' t' " (at level 40).

Inductive step : tm → tm → Prop :=
  | ST_PlusConstConst : ∀n[1] n[2],
      P (C n[1]) (C n[2]) ⇒ C (n[1] + n[2])
  | ST_Plus1 : ∀t[1] t[1]' t[2],
      t[1] ⇒ t[1]' →
      P t[1] t[2] ⇒ P t[1]' t[2]
  | ST_Plus2 : ∀n[1] t[2] t[2]',
      t[2] ⇒ t[2]' →
      P (C n[1]) t[2] ⇒ P (C n[1]) t[2]'

  where " t '⇒' t' " := (step t t').

```

    注意事项：

+   我们只定义了一个单个的减少步骤，其中一个 P 节点被其值替换。

+   每一步都找到最左边的准备好的 P 节点（其两个操作数都是常量）并就地重写它。第一条规则告诉如何重写此 P 节点本身；另外两条规则告诉如何找到它。

+   一个仅是常量的术语不能走一步。

    让我们暂停一下，检查一下几个推理示例

    步骤关系…

    如果 t[1] 可以向 t[1]' 步进，则 P t[1] t[2] 步

    对 P t[1]' t[2]：

```
Example test_step_1 :
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
      ⇒
      P
        (C (0 + 3))
        (P (C 2) (C 4)).

    Proof.
  apply ST_Plus1. apply ST_PlusConstConst. Qed.

```

#### 练习：1 星（test_step_2）

    和的右手边只有当

    左侧已完成：如果 t[2] 可以向 t[2]' 步进，

    那么 P (C n) t[2] 步至 P (C n) t[2]':

```
Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      ⇒
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```
End SimpleArith1.

```

# 关系

    我们将使用几种不同的单步关系，

    因此，泛化并声明一些定义会很有帮助

    和关于关系的定理。 （可选章节

    Rel.v 在更详细地开发了一些这些想法；它可能会

    如果这里的处理过于密集，可能会有用。）

    关于集合 X 的 *二元关系* 是一组命题

    参数化由 X 的两个元素 —— 即关于

    由 X 的元素对。

```
Definition relation (X: Type) := X→X→Prop.

```

    在本章中，这些关系的主要示例将是

    单步减少关系，⇒，及其多步

    变种，⇒*（下面定义），但还有许多其他

    例如 —— 例如，“等于”，“小于”，“小于等于”

    至，”以及“是的平方”的关系，以及“前缀

    在列表和字符串上的"之间关系。

    ⇒ 关系的一个简单性质是，就像

    Imp 的大步评估关系是 *确定的*。

    *定理*：对于每个 t，最多有一个 t'，使得 t

    步骤到 t'（t ⇒ t' 是可证明的）。形式上，这是

    相当于说⇒是确定性的。

    *证明概述*：我们证明如果 x 同时步进到 y[1]和

    y[2]，那么 y[1]和 y[2]相等，通过对推导进行归纳

    步骤 x y[1]。有几种情况需要考虑，取决于

    在这个推导中使用的最后一个规则和最后一个规则

    给定步骤 x y[2]的推导。

+   如果两者都是 ST_PlusConstConst，结果是显而易见的。

+   当两个推导都以 ST_Plus1 或 ST_Plus2 结尾时，遵循归纳假设。

+   不可能一个是 ST_PlusConstConst，另一个是 ST_Plus1 或 ST_Plus2，因为这将意味着 x 具有形式 P t[1] t[2]，其中 t[1]和 t[2]都是常数（通过 ST_PlusConstConst）*并且* t[1]或 t[2]中的一个具有形式 P _。

+   同样，不可能发生一个是 ST_Plus1，另一个是 ST_Plus2，因为这将意味着 x 具有形式 P t[1] t[2]，其中 t[1]既具有形式 P t[11] t[12]，也具有形式 C n。☐

    形式上：

```
Definition deterministic {X: Type} (R: relation X) :=
  ∀x y[1] y[2] : X, R x y[1] → R x y[2] → y[1] = y[2].

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y[1] y[2] Hy[1] Hy[2].
  generalize dependent y[2].
  induction Hy[1]; intros y[2] Hy[2].
    - (* ST_PlusConstConst *) inversion Hy[2].
      + (* ST_PlusConstConst *) reflexivity.
      + (* ST_Plus1 *) inversion H[2].
      + (* ST_Plus2 *) inversion H[2].
    - (* ST_Plus1 *) inversion Hy[2].
      + (* ST_PlusConstConst *)
        rewrite ← H[0] in Hy[1]. inversion Hy[1].
      + (* ST_Plus1 *)
        rewrite ← (IHHy1 t[1]'0).
        reflexivity. assumption.
      + (* ST_Plus2 *)
        rewrite ← H in Hy[1]. inversion Hy[1].
    - (* ST_Plus2 *) inversion Hy[2].
      + (* ST_PlusConstConst *)
        rewrite ← H[1] in Hy[1]. inversion Hy[1].
      + (* ST_Plus1 *) inversion H[2].
      + (* ST_Plus2 *)
        rewrite ← (IHHy1 t[2]'0).
        reflexivity. assumption.
Qed.

End SimpleArith2.

```

    这个证明中有一些令人讨厌的重复。每次使用

    对 Hy[2]进行反演会导致三个子情况，只有一个是

    相关的（与归纳中的当前情况匹配的那个

    在 Hy[1]上）。其他两种情况需要通过找到来解决

    假设之间的矛盾并对其进行反演。

    以下自定义策略，称为 solve_by_inverts，可以

    在这种情况下很有帮助。如果可以解决，它将解决目标

    通过反演一些假设；否则，它会失败。

```
Ltac solve_by_inverts n :=
  match goal with | H : ?T ⊢ _ ⇒ 
  match type of T with Prop ⇒
    solve [ 
      inversion H; 
      match n with S (S (?n')) ⇒ subst; solve_by_inverts (S n') end ]
  end end.

```

    这是如何工作的细节现在并不重要，但是它

    展示了 Coq 的 Ltac 语言的强大之处

    以编程方式定义特定目的的策略。看起来

    通过当前证明状态查找假设 H（第一个

    匹配）的类型 Prop（第二个匹配），使得执行

    H 上的反演（后跟对相同的递归调用

    策略，如果其参数 n 大于一）完全解决

    当前目标。如果不存在这样的假设，它会失败。

    我们通常会想要调用带有参数的 solve_by_inverts

    1（特别是因为较大的参数可能导致非常缓慢的证明

    检查），因此我们将 solve_by_invert 定义为这个的简写

    情况。

```
Ltac solve_by_invert :=
  solve_by_inverts 1.

```

    让我们看看如何简化前一个定理的证明

    使用这个策略...

```
Module SimpleArith3.
Import SimpleArith1.

Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y[1] y[2] Hy[1] Hy[2].
  generalize dependent y[2].
  induction Hy[1]; intros y[2] Hy[2];
    inversion Hy[2]; subst; try solve_by_invert.
  - (* ST_PlusConstConst *) reflexivity.
  - (* ST_Plus1 *)
    apply IHHy1 in H[2]. rewrite H[2]. reflexivity.
  - (* ST_Plus2 *)
    apply IHHy1 in H[2]. rewrite H[2]. reflexivity.
Qed.

End SimpleArith3.

```

## 值

    接下来，稍微重新制定将会很有用

    通过以单步减���的方式来定义它，以术语形式陈述

    “值”。

    将⇒关系视为定义一个

    *抽象机器*：

+   在任何时刻，机器的*状态*是一个术语。

+   机器的*步骤*是计算的原子单位 — 这里是单个“add”操作。

+   机器的*停机状态*是没有更多计算要做的状态。

    然后我们可以执行一个术语 t 如下：

+   将 t 作为机器的起始状态。

+   反复使用⇒关系找到一系列机器状态，从 t 开始，每个状态都步进到下一个。

+   当没有更多的规约时，“读取”机器的最终状态作为执行的结果。

    直观上，最终状态的

    机器始终是形式为 C n 的术语。

    我们称这样的术语为*值*。

```
Inductive value : tm → Prop :=
  | v_const : ∀n, value (C n).

```

    引入了值的概念后，我们可以在其中使用它

    定义 ⇒ 关系的 ST_Plus2 规则的形式化版本

    稍微更加优雅的方式：

        |

                        (ST_PlusConstConst)

        |

* * *

        |

                        P (C n[1]) (C n[2]) ⇒ C (n[1] + n[2])

        |

                    |

                        t[1] ⇒ t[1]'

        |

                        (ST_Plus1)

        |

* * *

        |

                        P t[1] t[2] ⇒ P t[1]' t[2]

        |

                    |

                        值 v[1]

        |

                    |

                        t[2] ⇒ t[2]'

        |

                        (ST_Plus2)

        |

* * *

        |

                        P v[1] t[2] ⇒ P v[1] t[2]'

        |

                    |

    再次，这里的变量名携带重要信息：

    按照惯例，v[1] 仅限于值，而 t[1] 和 t[2]

    范围涵盖任意术语。（鉴于这一约定，显式

    值假设可能是多余的。我们暂时保留它，

    保持非正式和 Coq 之间的密切对应

    规则的版本，但后来我们会在非正式的情况下放弃它

    简洁起见的规则。）

    这里是正式规则：

```
Reserved Notation " t '⇒' t' " (at level 40).

Inductive step : tm → tm → Prop :=
  | ST_PlusConstConst : ∀n[1] n[2],
          P (C n[1]) (C n[2])
      ⇒ C (n[1] + n[2])
  | ST_Plus1 : ∀t[1] t[1]' t[2],
        t[1] ⇒ t[1]' →
        P t[1] t[2] ⇒ P t[1]' t[2]
  | ST_Plus2 : ∀v[1] t[2] t[2]',
        value v[1] →                     (* <----- n.b. *)
        t[2] ⇒ t[2]' →
        P v[1] t[2] ⇒ P v[1] t[2]'

  where " t '⇒' t' " := (step t t').

```

#### 练习：3 星，推荐（redo_determinism）

    作为对这一变化的健全性检查，让我们重新验证确定性。

    *证明概述*：我们必须证明如果 x 同时步进到 y[1] 和

    y[2]，那么 y[1] 和 y[2] 是相等的。考虑使用的最终规则

    在步骤 x y[1] 和步骤 x y[2] 的推导中。

+   如果两者都是 ST_PlusConstConst，结果是显而易见的。

+   不可能出现一个是 ST_PlusConstConst 而另一个是 ST_Plus1 或 ST_Plus2 的情况，因为这将意味着 x 具有形式 P t[1] t[2]，其中 t[1] 和 t[2] 都是常数（通过 ST_PlusConstConst）*并且* t[1] 或 t[2] 中的一个具有形式 P _。

+   同样，不可能出现一个是 ST_Plus1 而另一个是 ST_Plus2 的情况，因为这将意味着 x 具有形式 P t[1] t[2]，其中 t[1] 既具有形式 P t[11] t[12] 又是一个值（因此具有形式 C n）。

+   当两个推导都以 ST_Plus1 或 ST_Plus2 结束时，根据归纳假设即可得出结论。☐

    大部分证明与上面的证明相同。但为了得到

    从练习中获得最大的收益，你应该尝试写下你的

    从头开始形式化版本，如果你只需使用之前的一个

    卡住了。

```
Theorem step_deterministic :
  deterministic step.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

## Strong Progress and Normal Forms

    The definition of single-step reduction for our toy language
    is fairly simple, but for a larger language it would be easy to
    forget one of the rules and accidentally create a situation where
    some term cannot take a step even though it has not been
    completely reduced to a value.  The following theorem shows that
    we did not, in fact, make such a mistake here. 

    *Theorem* (*Strong Progress*): If t is a term, then either t
    is a value or else there exists a term t' such that t ⇒ t'. 

    *Proof*: By induction on t.

*   Suppose t = C n. Then t is a value. 

*   Suppose t = P t[1] t[2], where (by the IH) t[1] either is a value or can step to some t[1]', and where t[2] is either a value or can step to some t[2]'. We must show P t[1] t[2] is either a value or steps to some t'. 

    *   If t[1] and t[2] are both values, then t can take a step, by ST_PlusConstConst. 

    *   If t[1] is a value and t[2] can take a step, then so can t, by ST_Plus2. 

    *   If t[1] can take a step, then so can t, by ST_Plus1. ☐

    Or, formally:

```

定理 strong_progress：∀t，

值 t ∨ (∃t'，t ⇒ t')。

    证明。

对 t 进行归纳。

- (* C *) 左。应用 v_const。

- (* P *) 右。反演 IHt1。

+ (* l *) 反演 IHt2。

* (* l *) 反演 H。反演 H[0]。

∃(C (n + n[0]))。

应用 ST_PlusConstConst。

* (* r *) 反演 H[0] 得到 [t' H[1]]。

∃(P t[1] t')。

应用 ST_Plus2。应用 H。应用 H[1]。

+ (* r *) 反演 H 得到 [t' H[0]]。

∃(P t' t[2])。

应用 ST_Plus1。应用 H[0]。Qed。

```

    This important property is called *strong progress*, because
    every term either is a value or can "make progress" by stepping to
    some other term.  (The qualifier "strong" distinguishes it from a
    more refined version that we'll see in later chapters, called
    just *progress*.) 

    The idea of "making progress" can be extended to tell us something
    interesting about values: in this language, values are exactly the
    terms that *cannot* make progress in this sense.

    To state this observation formally, let's begin by giving a name
    to terms that cannot make progress.  We'll call them *normal forms*.

```

定义 normal_form {X:Type} (R:relation X) (t:X) : Prop :=

¬ ∃t'，R t t'。

```

    Note that this definition specifies what it is to be a normal form
    for an *arbitrary* relation R over an arbitrary set X, not
    just for the particular single-step reduction relation over terms
    that we are interested in at the moment.  We'll re-use the same
    terminology for talking about other relations later in the
    course. 

    We can use this terminology to generalize the observation we made
    in the strong progress theorem: in this language, normal forms and
    values are actually the same thing.

```

引理 value_is_nf：∀v，

值 v → 步骤 v 的正规形式。

    证明。

展开 normal_form。引入 v H。反演 H。

引入 contra。反演 contra。反演 H[1]。

    Qed。

引理 nf_is_value：∀t，

步骤 t 的正规形式 → 值 t。

    证明。 (* 一个强进展的推论... *)

展开 normal_form。引入 t H。

断言（G：value t ∨ ∃t'，t ⇒ t'）。

{ 应用 strong_progress。 }

反转 G。

+ (* l *) 应用 H[0]。

+ (* r *) 反证法。应用 H。假设成立。证毕。

推论 nf_same_as_value：∀t，

normal_form step t ↔ value t。

    ��明。

分裂。应用 nf_is_value。应用 value_is_nf。证毕。

```

    Why is this interesting?

    Because value is a syntactic concept — it is defined by looking
    at the form of a term — while normal_form is a semantic one —
    it is defined by looking at how the term steps.  It is not obvious
    that these concepts should coincide!  Indeed, we could easily have
    written the definitions so that they would *not* coincide. 

#### Exercise: 3 stars, optional (value_not_same_as_normal_form1)

    We might, for example, mistakenly define value so that it
    includes some terms that are not finished reducing.  (Even if you don't work this exercise and the following ones
    in Coq, make sure you can think of an example of such a term.)

```

模块 Temp1。

归纳值：tm → Prop :=

| v_const：∀n，值 (C n)

| v_funny：∀t[1] n[2]，                       (* <---- *)

值 (P t[1] (C n[2]))。

保留符号 " t '⇒' t' "（在级别 40）。

归纳步骤：tm → tm → Prop :=

| ST_PlusConstConst：∀n[1] n[2]，

P (C n[1]) (C n[2]) ⇒ C (n[1] + n[2])

| ST_Plus1：∀t[1] t[1]' t[2]，

t[1] ⇒ t[1]' →

P t[1] t[2] ⇒ P t[1]' t[2]

| ST_Plus2：∀v[1] t[2] t[2]'，

值 v[1] →

t[2] ⇒ t[2]' →

P v[1] t[2] ⇒ P v[1] t[2]'

其中 " t '⇒' t' " := (step t t')。

引理 value_not_same_as_normal_form：

∃v，值 v ∧ ¬ normal_form step v。

证明。

(* 填写此处*) 已承认。

结束 Temp1。

```

    ☐

```

#### 练习：2 星，可选（value_not_same_as_normal_form2）

    或者，我们可能错误地定义步骤，以便它

    允许某些被指定为值的东西进一步减少。

```
Module Temp2.

Inductive value : tm → Prop :=
| v_const : ∀n, value (C n).

Reserved Notation " t '⇒' t' " (at level 40).

Inductive step : tm → tm → Prop :=
  | ST_Funny : ∀n,                         (* <---- *)
      C n ⇒ P (C n) (C 0)
  | ST_PlusConstConst : ∀n[1] n[2],
      P (C n[1]) (C n[2]) ⇒ C (n[1] + n[2])
  | ST_Plus1 : ∀t[1] t[1]' t[2],
      t[1] ⇒ t[1]' →
      P t[1] t[2] ⇒ P t[1]' t[2]
  | ST_Plus2 : ∀v[1] t[2] t[2]',
      value v[1] →
      t[2] ⇒ t[2]' →
      P v[1] t[2] ⇒ P v[1] t[2]'

  where " t '⇒' t' " := (step t t').

Lemma value_not_same_as_normal_form :
  ∃v, value v ∧ ¬ normal_form step v.

    Proof.
  (* FILL IN HERE *) Admitted.

End Temp2.

```

    ☐

#### 练习：3 星，可选（value_not_same_as_normal_form3）

    最后，我们可以定义值和步骤，以便存在一些

    不是值但在步骤中无法进行进一步的术语

    关系。这些术语被称为*卡住*。在这种情况下，这是

    由语义错误引起，但我们也会看到

    有些情况下，即使在正确的语言定义中，也会出现

    允许一些术语卡住是有意义的。

```
Module Temp3.

Inductive value : tm → Prop :=
  | v_const : ∀n, value (C n).

Reserved Notation " t '⇒' t' " (at level 40).

Inductive step : tm → tm → Prop :=
  | ST_PlusConstConst : ∀n[1] n[2],
      P (C n[1]) (C n[2]) ⇒ C (n[1] + n[2])
  | ST_Plus1 : ∀t[1] t[1]' t[2],
      t[1] ⇒ t[1]' →
      P t[1] t[2] ⇒ P t[1]' t[2]

  where " t '⇒' t' " := (step t t').

```

    （请注意 ST_Plus2 缺失。）

```
Lemma value_not_same_as_normal_form :
  ∃t, ¬ value t ∧ normal_form step t.
Proof.
  (* FILL IN HERE *) Admitted.

End Temp3.

```

    ☐

```

### Additional Exercises

```

模块 Temp4。

```

    Here is another very simple language whose terms, instead of being
    just addition expressions and numbers, are just the booleans true
    and false and a conditional expression...

```

归纳定义 tm：Type :=

| ttrue：tm

| tfalse：tm

| tif：tm → tm → tm → tm。

归纳值：tm → Prop :=

| v_true：值 ttrue

| v_false：值 tfalse。

保留符号 " t '⇒' t' "（在级别 40）。

归纳步骤：tm → tm → Prop :=

| ST_IfTrue：∀t[1] t[2]，

如果 ttrue t[1] t[2] ⇒ t[1]

| ST_IfFalse：∀t[1] t[2]，

如果 tfalse t[1] t[2] ⇒ t[2]

| ST_If：∀t[1] t[1]' t[2] t[3]，

t[1] ⇒ t[1]' →

如果 t[1] t[2] t[3] ⇒ tif t[1]' t[2] t[3]

其中 " t '⇒' t' " := (step t t')。

```

#### Exercise: 1 starM (smallstep_bools)

    Which of the following propositions are provable?  (This is just a
    thought exercise, but for an extra challenge feel free to prove
    your answers in Coq.)

```

定义 bool_step_prop1 :=

tfalse ⇒ tfalse。

(* 填写此处*)

定义 bool_step_prop2 :=

如果

ttrue

(如果 ttrue ttrue ttrue)

(如果 tfalse tfalse tfalse)

⇒

ttrue。

(* 填写此处*)

定义 bool_step_prop3 :=

如果

(如果 ttrue ttrue ttrue)

(如果 ttrue ttrue ttrue)

tfalse

⇒

如果

ttrue

(如果 ttrue ttrue ttrue)

tfalse。

(* 填写此处*)

```

    ☐ 

#### Exercise: 3 stars, optional (progress_bool)

    Just as we proved a progress theorem for plus expressions, we can
    do so for boolean expressions, as well.

```

定理 strong_progress：∀t，

值 t ∨ (∃t'，t ⇒ t')。

证明。

(* 填写此处*) 已承认。

```

    ☐ 

#### Exercise: 2 stars, optional (step_deterministic)

```

定理 step_deterministic：

确定性步骤。

证明。

(* 填写此处*) 已承认。

```

    ☐

```

模块 Temp5。

```

#### Exercise: 2 stars (smallstep_bool_shortcut)

    Suppose we want to add a "short circuit" to the step relation for
    boolean expressions, so that it can recognize when the then and
    else branches of a conditional are the same value (either
    ttrue or tfalse) and reduce the whole conditional to this
    value in a single step, even if the guard has not yet been reduced
    to a value. For example, we would like this proposition to be
    provable:

```

如果

(如果 ttrue ttrue ttrue)

tfalse

tfalse

⇒

tfalse。

    为步骤关系编写一个额外的子句，以实现这一点

    效果并证明 bool_step_prop4。

```
Reserved Notation " t '⇒' t' " (at level 40).

Inductive step : tm → tm → Prop :=
  | ST_IfTrue : ∀t[1] t[2],
      tif ttrue t[1] t[2] ⇒ t[1]
  | ST_IfFalse : ∀t[1] t[2],
      tif tfalse t[1] t[2] ⇒ t[2]
  | ST_If : ∀t[1] t[1]' t[2] t[3],
      t[1] ⇒ t[1]' →
      tif t[1] t[2] t[3] ⇒ tif t[1]' t[2] t[3]
  (* FILL IN HERE *)

  where " t '⇒' t' " := (step t t').

Definition bool_step_prop4 :=
         tif
            (tif ttrue ttrue ttrue)
            tfalse
            tfalse
     ⇒
         tfalse.

Example bool_step_prop4_holds :
  bool_step_prop4.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星，可选（properties_of_altered_step）

    可以证明决定性和强进展定理

    对于讲义中的步骤关系也适用于

    上述给出的步骤的定义。在我们添加子句之后

    ST_ShortCircuit...

+   步骤关系仍然是确定性的吗？写下是或否，并简要（1 句话）解释你的答案。

    可选：在 Coq 中证明你的答案正确。

```
(* FILL IN HERE *)

```

+   强进展定理成立吗？写下是或否，并简要（1 句话）解释你的答案。

    可选：在 Coq 中证明你的答案正确。

```
(* FILL IN HERE *)

```

+   一般来说，如果我们从原始步骤关系中去掉一个或多个构造器，是否有任何方法可以导致强进展失败？写下是或否，并简要（1 句话）解释你的答案。

    （* 填写此处 *）

    ☐

```
End Temp5.
End Temp4.

```

# 多步减少

    到目前为止，我们一直在使用*单步减少*

    关系 ⇒，它形式化了一个

    用于执行程序的抽象机器。

    我们可以使用相同的机器将程序减少到完成——到

    找出它们产生的最终结果。这可以形式化为

    如下：

+   首先，我们定义了一个*多步减少关系* ⇒*，它将项 t 和 t' 相关联，如果 t 可以通过任意数量（包括零）的单次减少步骤达到 t'。

+   然后我们将一个项 t 的“结果”定义为 t 可以通过多步减少达到的正常形式。

```

    Since we'll want to reuse the idea of multi-step reduction many
    times, let's take a little extra trouble and define it
    generically.

    Given a relation R, we define a relation multi R, called the
    *multi-step closure of R* as follows.

```

归纳多 {X:Type} (R: 关系 X) : 关系 X :=

| multi_refl  : ∀(x : X), multi R x x

| multi_step : ∀(x y z : X)，

R x y →

multi R y z →

multi R x z。

```

    (In the Rel chapter and the Coq standard library, this relation
    is called clos_refl_trans_1n.  We give it a shorter name here
    for the sake of readability.)

    The effect of this definition is that multi R relates two
    elements x and y if 

*   x = y, or

*   R x y, or

*   there is some nonempty sequence z[1], z[2], ..., zn such that 

    ```

    R x z[1]

    R z[1] z[2]

    ...

    R zn y。

    ```

    Thus, if R describes a single-step of computation, then z[1]...zn 
    is the sequence of intermediate steps of computation between x and 
    y. 

    We write ⇒* for the multi step relation on terms.

```

符号 " t '⇒*' t' " := (multi step t t') (在级别 40)。

```

    The relation multi R has several crucial properties.

    First, it is obviously *reflexive* (that is, ∀ x, multi R x x).  In the case of the ⇒* (i.e., multi step) relation, the
    intuition is that a term can execute to itself by taking zero
    steps of execution.

    Second, it contains R — that is, single-step executions are a
    particular case of multi-step executions.  (It is this fact that
    justifies the word "closure" in the term "multi-step closure of
    R.")

```

定理 multi_R: ∀(X:Type) (R:关系 X) (x y : X)，

R x y → (multi R) x y。

    证明

引入 X R x y H。

应用 multi_step 与 y。应用 H。应用 multi_refl。Qed。

```

    Third, multi R is *transitive*.

```

定理 multi_trans：

∀(X:Type) (R: 关系 X) (x y z : X)，

multi R x y  →

multi R y z →

multi R x z。

    证明

引入 X R x y z G H。

归纳 G。

- （* multi_refl *）假设。

- （* multi_step *）

应用 multi_step 与 y。假设。

应用 IHG。假设。Qed。

```

    In particular, for the multi step relation on terms, if
    t[1]⇒*t[2] and t[2]⇒*t[3], then t[1]⇒*t[3].

```

## 例子

    这里是多步关系的一个具体实例：

```
Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   ⇒*
      C ((0 + 3) + (2 + 4)).
Proof.
  apply multi_step with
            (P (C (0 + 3))
               (P (C 2) (C 4))).
  apply ST_Plus1. apply ST_PlusConstConst.
  apply multi_step with
            (P (C (0 + 3))
               (C (2 + 4))).
  apply ST_Plus2. apply v_const.
  apply ST_PlusConstConst.
  apply multi_R.
  apply ST_PlusConstConst. Qed.

```

    这里是相同事实的另一种证明，使用 eapply

    避免显式构造所有中间项。

```
Lemma test_multistep_1':
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
  ⇒*
      C ((0 + 3) + (2 + 4)).
Proof.
  eapply multi_step. apply ST_Plus1. apply ST_PlusConstConst.
  eapply multi_step. apply ST_Plus2. apply v_const.
  apply ST_PlusConstConst.
  eapply multi_step. apply ST_PlusConstConst.
  apply multi_refl. Qed.

```

#### 练习：1 星，可选（test_multistep_2）

```
Lemma test_multistep_2:
  C 3 ⇒* C 3.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：1 星，可选（test_multistep_3）

```
Lemma test_multistep_3:
      P (C 0) (C 3)
   ⇒*
      P (C 0) (C 3).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：2 星（test_multistep_4）

```
Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  ⇒*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

## Normal Forms Again

    If t reduces to t' in zero or more steps and t' is a
    normal form, we say that "t' is a normal form of t."

```

定义 step_normal_form := normal_form step。

定义 normal_form_of (t t' : tm) :=

（t ⇒* t' ∧ step_normal_form t'）。

```

    We have already seen that, for our language, single-step reduction is
    deterministic — i.e., a given term can take a single step in
    at most one way.  It follows from this that, if t can reach
    a normal form, then this normal form is unique.  In other words, we
    can actually pronounce normal_form t t' as "t' is *the*
    normal form of t." 

#### Exercise: 3 stars, optional (normal_forms_unique)

```

定理 normal_forms_unique:

确定性 normal_form_of。

证明

（* 我们建议保持此初始设置不变！*）

展开确定性。展开 normal_form_of。

引入 x y[1] y[2] P[1] P[2]。

反演 P[1] 为 [P[11] P[12]]; 清除 P[1]。

反演 P[2] 为 [P[21] P[22]]; 清除 P[2]。

泛化相关的 y[2]。

（* 填写此处 *）已承认。

```

    ☐ 

    Indeed, something stronger is true for this language (though not
    for all languages): the reduction of *any* term t will
    eventually reach a normal form — i.e., normal_form_of is a
    *total* function.  Formally, we say the step relation is
    *normalizing*.

```

定义 normalizing {X:Type} (R:关系 X) :=

∀t, ∃t'，

（multi R）t t' ∧ normal_form R t'。

```

    To prove that step is normalizing, we need a couple of lemmas.

    First, we observe that, if t reduces to t' in many steps, then
    the same sequence of reduction steps within t is also possible
    when t appears as the left-hand child of a P node, and
    similarly when t appears as the right-hand child of a P
    node whose left-hand child is a value.

```

引理 multistep_congr_1: ∀t[1] t[1]' t[2]，

t[1] ⇒* t[1]' →

P t[1] t[2] ⇒* P t[1]' t[2]。

    证明。

对 t[1] t[1]' t[2] H 进行归纳。

-（* multi_refl *）应用 multi_refl。

-（* multi_step *）使用 multi_step 和 (P y t[2]) 进行应用。

应用 ST_Plus1。应用 H。

应用 IHmulti。证毕。

```

#### Exercise: 2 stars (multistep_congr_2)

```

引理 multistep_congr_2：对于所有的 t[1]、t[2] 和 t[2]'，

值 t[1] →

t[2] ⇒* t[2]' →

P t[1] t[2] ⇒* P t[1] t[2]'。

证明。

（* 在此填写 *）已承��。

```

    ☐ 

    With these lemmas in hand, the main proof is a straightforward
    induction.

    *Theorem*: The step function is normalizing — i.e., for every
    t there exists some t' such that t steps to t' and t' is
    a normal form.

    *Proof sketch*: By induction on terms.  There are two cases to
    consider:

*   t = C n for some n. Here t doesn't take a step, and we have t' = t. We can derive the left-hand side by reflexivity and the right-hand side by observing (a) that values are normal forms (by nf_same_as_value) and (b) that t is a value (by v_const). 

*   t = P t[1] t[2] for some t[1] and t[2]. By the IH, t[1] and t[2] have normal forms t[1]' and t[2]'. Recall that normal forms are values (by nf_same_as_value); we know that t[1]' = C n[1] and t[2]' = C n[2], for some n[1] and n[2]. We can combine the ⇒* derivations for t[1] and t[2] using multi_congr_1 and multi_congr_2 to prove that P t[1] t[2] reduces in many steps to C (n[1] + n[2]). 

     It is clear that our choice of t' = C (n[1] + n[2]) is a value, which is in turn a normal form. ☐

```

定理 step_normalizing：

规范化步骤。

    证明。

展开 normalizing。

对 t 进行归纳。

-（* C *）

∃（C n）。

分割。

+（* l *）应用 multi_refl。

+（* r *）

（* 我们可以使用“iff”语句进行重写，而不仅仅是相等关系：*）

重写 nf_same_as_value。应用 v_const。

-（* P *）

将 IHt1 分解�� [t[1]' [H[11] H[12]]]。

将 IHt2 分解为 [t[2]' [H[21] H[22]]]。

在 H[12] 中重写 nf_same_as_value。在 H[22] 中重写 nf_same_as_value。

将 H[12] 反演为 [n[1] H]。将 H[22] 反演为 [n[2] H']。

在 H 中重写 ← H[11]。

在 H' 中重写 ← H[21]。

∃（C（n[1] + n[2])）。

分割。

+（* l *）

使用 multi_trans 和 (P (C n[1]) t[2]) 进行应用。

* 应用 multistep_congr_1。应用 H[11]。

* 使用 multi_trans 和

（P（C n[1]）（C n[2])）。

{ 应用 multistep_congr_2。应用 v_const。应用 H[21]。 }

{ 应用 multi_R。应用 ST_PlusConstConst。 }

+（* r *）

重写 nf_same_as_value。应用 v_const。证毕。

```

## Equivalence of Big-Step and Small-Step

    Having defined the operational semantics of our tiny programming
    language in two different ways (big-step and small-step), it makes
    sense to ask whether these definitions actually define the same
    thing!  They do, though it takes a little work to show it.  The
    details are left as an exercise. 

#### Exercise: 3 stars (eval__multistep)

```

定理 eval__multistep：对于所有的 t 和 n，

t ⇓ n → t ⇒* C n.

```

    The key ideas in the proof can be seen in the following picture:

```

P t[1] t[2] ⇒            （通过 ST_Plus1）

P t[1]' t[2] ⇒           （通过 ST_Plus1）

P t[1]'' t[2] ⇒          （通过 ST_Plus1）

...

P（C n[1]）t[2] ⇒        （通过 ST_Plus2）

P（C n[1]）t[2]' ⇒       （通过 ST_Plus2）

P（C n[1]）t[2]'' ⇒      （通过 ST_Plus2）

...

P（C n[1]）（C n[2]） ⇒    （通过 ST_PlusConstConst）

C（n[1] + n[2]）

    换句话说，形式为 P t[1] t[2] 的项的多步规约

    分为三个阶段：

+   首先，我们使用一定次数的 ST_Plus1 将 t[1] 减少到一个正常形式，这必须（通过 nf_same_as_value）是形式为 C n[1] 的项，其中 n[1] 是某个数。

+   接下来，我们使用一定次数的 ST_Plus2 将 t[2] 减少到一个正常形式，这必须再次是形式为 C n[2] 的项，其中 n[2] 是某个数。

+   最后，我们使用一次 ST_PlusConstConst 将 P（C n[1]）（C n[2]） 减少为 C（n[1] + n[2]）。

    要形式化这种直觉，你需要使用等价关系

    上述引理（你可能现在想要复习它们，以便

    你将能够识别它们何时有用），再加上一些基本的

    ⇒* 的性质：它是自反的、传递的和

    包括 ⇒。

```
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 颗星，高级（eval__multistep_inf）

    写出 eval__multistep 证明的详细非正式版本。

    (* 在此填写 *)

    ☐

    对于另一个方向，我们需要一个引理，该引理建立了一个

    单步简化和大步评估之间的关系。

#### 练习：3 颗星（step__eval）

```
Lemma step__eval : ∀t t' n,
     t ⇒ t' →
     t' ⇓ n →
     t ⇓ n.
Proof.
  intros t t' n Hs. generalize dependent n.
  (* FILL IN HERE *) Admitted.

```

    ☐

    小步简化蕴含大步评估的事实是

    现在，一旦正确陈述，证明就变得直截了当。

    证明通过对多步简化进行归纳进行。

    嵌入在假设 normal_form_of t t' 中的序列。

    在开始证明之前，请确保您理解了该陈述

    证明。

#### 练习：3 颗星（multistep__eval）

```
Theorem multistep__eval : ∀t t',
  normal_form_of t t' → ∃n, t' = C n ∧ t ⇓ n.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

## Additional Exercises

#### Exercise: 3 stars, optional (interp_tm)

    Remember that we also defined big-step evaluation of terms as a
    function evalF.  Prove that it is equivalent to the existing
    semantics.  (Hint: we just proved that eval and multistep are
    equivalent, so logically it doesn't matter which you choose.
    One will be easier than the other, though!)

```

定理 evalF_eval：∀t n，

evalF t = n ↔ t ⇓ n。

证明。

(* 在此填写 *)

```

    ☐ 

#### Exercise: 4 starsM (combined_properties)

    We've considered arithmetic and conditional expressions
    separately.  This exercise explores how the two interact.

```

Combined 模块。

归纳 tm：Type :=

| C : nat → tm

| P : tm → tm → tm

| ttrue : tm

| tfalse : tm

| tif : tm → tm → tm → tm。

归纳值：tm → Prop :=

| v_const : ∀n, 值 (C n)

| v_true : 值 ttrue

| v_false : 值 tfalse。

保留记法 " t '⇒' t' "（在级别 40）。

归纳步骤：tm → tm → Prop :=

| ST_PlusConstConst : ∀n[1] n[2],

P (C n[1]) (C n[2]) ⇒ C (n[1] + n[2])

| ST_Plus1 : ∀t[1] t[1]' t[2],

t[1] ⇒ t[1]' →

P t[1] t[2] ⇒ P t[1]' t[2]

| ST_Plus2 : ∀v[1] t[2] t[2]',

值 v[1] →

t[2] ⇒ t[2]' →

P v[1] t[2] ⇒ P v[1] t[2]'

| ST_IfTrue : ∀t[1] t[2],

tif ttrue t[1] t[2] ⇒ t[1]

| ST_IfFalse : ∀t[1] t[2],

tif tfalse t[1] t[2] ⇒ t[2]

| ST_If : ∀t[1] t[1]' t[2] t[3],

t[1] ⇒ t[1]' →

tif t[1] t[2] t[3] ⇒ tif t[1]' t[2] t[3]

其中 " t '⇒' t' " := (step t t')。

```

    Earlier, we separately proved for both plus- and if-expressions...

*   that the step relation was deterministic, and 

*   a strong progress lemma, stating that every term is either a value or can take a step.

    Prove or disprove these two properties for the combined language.

```

(* 在此填写 *)

结束组合。

```

    ☐

```

# 小步 Imp

    现在，举一个更严肃的例子：Imp 的小步版本

    操作语义。

    算术和小步简化关系

    布尔表达式是微小

    到目前为止我们一直在努力的语言。为了使它们更容易

    阅读，我们引入符号表示 ⇒[a] 和 ⇒[b] 用于

    算术和布尔步骤关系。

```
Inductive aval : aexp → Prop :=
  | av_num : ∀n, aval (ANum n).

```

    我们实际上不打算定义布尔值

    值，因为它们在 ⇒[b] 的定义中不需要。

    下面（为什么？），尽管如果我们的语言稍微

    更大（为什么？）。

```
Reserved Notation " t '/' st '⇒a' t' "
                  (at level 40, st at level 39).

Inductive astep : state → aexp → aexp → Prop :=
  | AS_Id : ∀st i,
      AId i / st ⇒[a] ANum (st i)
  | AS_Plus : ∀st n[1] n[2],
      APlus (ANum n[1]) (ANum n[2]) / st ⇒[a] ANum (n[1] + n[2])
  | AS_Plus1 : ∀st a[1] a[1]' a[2],
      a[1] / st ⇒[a] a[1]' →
      (APlus a[1] a[2]) / st ⇒[a] (APlus a[1]' a[2])
  | AS_Plus2 : ∀st v[1] a[2] a[2]',
      aval v[1] →
      a[2] / st ⇒[a] a[2]' →
      (APlus v[1] a[2]) / st ⇒[a] (APlus v[1] a[2]')
  | AS_Minus : ∀st n[1] n[2],
      (AMinus (ANum n[1]) (ANum n[2])) / st ⇒[a] (ANum (minus n[1] n[2]))
  | AS_Minus1 : ∀st a[1] a[1]' a[2],
      a[1] / st ⇒[a] a[1]' →
      (AMinus a[1] a[2]) / st ⇒[a] (AMinus a[1]' a[2])
  | AS_Minus2 : ∀st v[1] a[2] a[2]',
      aval v[1] →
      a[2] / st ⇒[a] a[2]' →
      (AMinus v[1] a[2]) / st ⇒[a] (AMinus v[1] a[2]')
  | AS_Mult : ∀st n[1] n[2],
      (AMult (ANum n[1]) (ANum n[2])) / st ⇒[a] (ANum (mult n[1] n[2]))
  | AS_Mult1 : ∀st a[1] a[1]' a[2],
      a[1] / st ⇒[a] a[1]' →
      (AMult a[1] a[2]) / st ⇒[a] (AMult a[1]' a[2])
  | AS_Mult2 : ∀st v[1] a[2] a[2]',
      aval v[1] →
      a[2] / st ⇒[a] a[2]' →
      (AMult v[1] a[2]) / st ⇒[a] (AMult v[1] a[2]')

    where " t '/' st '⇒a' t' " := (astep st t t').

Reserved Notation " t '/' st '⇒b' t' "
                  (at level 40, st at level 39).

Inductive bstep : state → bexp → bexp → Prop :=
| BS_Eq : ∀st n[1] n[2],
    (BEq (ANum n[1]) (ANum n[2])) / st ⇒[b]
    (if (beq_nat n[1] n[2]) then BTrue else BFalse)
| BS_Eq[1] : ∀st a[1] a[1]' a[2],
    a[1] / st ⇒[a] a[1]' →
    (BEq a[1] a[2]) / st ⇒[b] (BEq a[1]' a[2])
| BS_Eq[2] : ∀st v[1] a[2] a[2]',
    aval v[1] →
    a[2] / st ⇒[a] a[2]' →
    (BEq v[1] a[2]) / st ⇒[b] (BEq v[1] a[2]')
| BS_LtEq : ∀st n[1] n[2],
    (BLe (ANum n[1]) (ANum n[2])) / st ⇒[b]
             (if (leb n[1] n[2]) then BTrue else BFalse)
| BS_LtEq1 : ∀st a[1] a[1]' a[2],
    a[1] / st ⇒[a] a[1]' →
    (BLe a[1] a[2]) / st ⇒[b] (BLe a[1]' a[2])
| BS_LtEq2 : ∀st v[1] a[2] a[2]',
    aval v[1] →
    a[2] / st ⇒[a] a[2]' →
    (BLe v[1] a[2]) / st ⇒[b] (BLe v[1] a[2]')
| BS_NotTrue : ∀st,
    (BNot BTrue) / st ⇒[b] BFalse
| BS_NotFalse : ∀st,
    (BNot BFalse) / st ⇒[b] BTrue
| BS_NotStep : ∀st b[1] b[1]',
    b[1] / st ⇒[b] b[1]' →
    (BNot b[1]) / st ⇒[b] (BNot b[1]')
| BS_AndTrueTrue : ∀st,
    (BAnd BTrue BTrue) / st ⇒[b] BTrue
| BS_AndTrueFalse : ∀st,
    (BAnd BTrue BFalse) / st ⇒[b] BFalse
| BS_AndFalse : ∀st b[2],
    (BAnd BFalse b[2]) / st ⇒[b] BFalse
| BS_AndTrueStep : ∀st b[2] b[2]',
    b[2] / st ⇒[b] b[2]' →
    (BAnd BTrue b[2]) / st ⇒[b] (BAnd BTrue b[2]')
| BS_AndStep : ∀st b[1] b[1]' b[2],
    b[1] / st ⇒[b] b[1]' →
    (BAnd b[1] b[2]) / st ⇒[b] (BAnd b[1]' b[2])

where " t '/' st '⇒b' t' " := (bstep st t t').

```

    命令的语义是有趣的部分。我们需要两个

    一些小技巧使其正常工作：

+   我们使用 SKIP 作为“命令值” — 即，已达到正常形式的命令。

    +   赋值命令简化为 SKIP（和更新后的状态）。

    +   顺序命令等待其左侧子命令简化为 SKIP，然后将其丢弃，以便继续使用右侧子命令进行简化。

+   我们通过将 WHILE 命令转换为条件命令，然后跟着相同的 WHILE 来减少 WHILE 命令。

    （有其他方法可以实现后者的效果

    技巧，但它们都具有一个共同特征，即原始 WHILE

    需要保存命令，而循环的单个副本

    正在被简化。）

```
Reserved Notation " t '/' st '⇒' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) → (com * state) → Prop :=
  | CS_AssStep : ∀st i a a',
      a / st ⇒[a] a' →
      (i ::= a) / st ⇒ (i ::= a') / st
  | CS_Ass : ∀st i n,
      (i ::= (ANum n)) / st ⇒ SKIP / (t_update st i n)
  | CS_SeqStep : ∀st c[1] c[1]' st' c[2],
      c[1] / st ⇒ c[1]' / st' →
      (c[1] ;; c[2]) / st ⇒ (c[1]' ;; c[2]) / st'
  | CS_SeqFinish : ∀st c[2],
      (SKIP ;; c[2]) / st ⇒ c[2] / st
  | CS_IfTrue : ∀st c[1] c[2],
      IFB BTrue THEN c[1] ELSE c[2] FI / st ⇒ c[1] / st
  | CS_IfFalse : ∀st c[1] c[2],
      IFB BFalse THEN c[1] ELSE c[2] FI / st ⇒ c[2] / st
  | CS_IfStep : ∀st b b' c[1] c[2],
      b / st ⇒[b] b' →
          IFB b THEN c[1] ELSE c[2] FI / st 
      ⇒ (IFB b' THEN c[1] ELSE c[2] FI) / st
  | CS_While : ∀st b c[1],
          (WHILE b DO c[1] END) / st
      ⇒ (IFB b THEN (c[1];; (WHILE b DO c[1] END)) ELSE SKIP FI) / st

  where " t '/' st '⇒' t' '/' st' " := (cstep (t,st) (t',st')).

```

# 并发 Imp

    最后，为了展示这种定义风格的强大之处，让我们

    用一个新的命令形式丰富 Imp，该命令在两个子命令中运行

    并行，并在两者都终止时终止。为了反映

    调度的不可预测性，子命令的操作可能

    以任何顺序交错进行，但它们共享相同的内存和

    可以通过读写相同的变量进行通信。

```
Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com
  (* New: *)
  | CPar : com → com → com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c[1] c[2]) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c[1] c[2]) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c[1] c[2]) (at level 80, right associativity).

Inductive cstep : (com * state)  → (com * state) → Prop :=
    (* Old part *)
  | CS_AssStep : ∀st i a a',
      a / st ⇒[a] a' →
      (i ::= a) / st ⇒ (i ::= a') / st
  | CS_Ass : ∀st i n,
      (i ::= (ANum n)) / st ⇒ SKIP / (t_update st i n)
  | CS_SeqStep : ∀st c[1] c[1]' st' c[2],
      c[1] / st ⇒ c[1]' / st' →
      (c[1] ;; c[2]) / st ⇒ (c[1]' ;; c[2]) / st'
  | CS_SeqFinish : ∀st c[2],
      (SKIP ;; c[2]) / st ⇒ c[2] / st
  | CS_IfTrue : ∀st c[1] c[2],
      (IFB BTrue THEN c[1] ELSE c[2] FI) / st ⇒ c[1] / st
  | CS_IfFalse : ∀st c[1] c[2],
      (IFB BFalse THEN c[1] ELSE c[2] FI) / st ⇒ c[2] / st
  | CS_IfStep : ∀st b b' c[1] c[2],
      b /st ⇒[b] b' →
          (IFB b THEN c[1] ELSE c[2] FI) / st 
      ⇒ (IFB b' THEN c[1] ELSE c[2] FI) / st
  | CS_While : ∀st b c[1],
          (WHILE b DO c[1] END) / st 
      ⇒ (IFB b THEN (c[1];; (WHILE b DO c[1] END)) ELSE SKIP FI) / st
    (* New part: *)
  | CS_Par1 : ∀st c[1] c[1]' c[2] st',
      c[1] / st ⇒ c[1]' / st' →
      (PAR c[1] WITH c[2] END) / st ⇒ (PAR c[1]' WITH c[2] END) / st'
  | CS_Par2 : ∀st c[1] c[2] c[2]' st',
      c[2] / st ⇒ c[2]' / st' →
      (PAR c[1] WITH c[2] END) / st ⇒ (PAR c[1] WITH c[2]' END) / st'
  | CS_ParDone : ∀st,
      (PAR SKIP WITH SKIP END) / st ⇒ SKIP / st
  where " t '/' st '⇒' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '⇒*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

```

    这种语言的许多有趣特性之一是事实

    以下程序可以以变量 X 设置为终止

    对于任何值。

```
Definition par_loop : com :=
  PAR
    Y ::= ANum 1
  WITH
    WHILE BEq (AId Y) (ANum 0) DO
      X ::= APlus (AId X) (ANum 1)
    END
  END.

```

    特别是，它可以以 X 设置为 0 终止：

```
Example par_loop_example_0:
  ∃st',
       par_loop / empty_state  ⇒* SKIP / st'
    ∧ st' X = 0.

    Proof.
  eapply [ex_intro](http://coq.inria.fr/library/Coq.Init.Logic.html#ex_intro). split.
  unfold par_loop.
  eapply multi_step. apply CS_Par1.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply [BS_Eq[1]](Smallstep.html#CImp.BS_Eq<sub>1</sub>). apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

```

    它也可以以 X 设置为 2 终止：

```
Example par_loop_example_2:
  ∃st',
       par_loop / empty_state ⇒* SKIP / st'
    ∧ st' X = 2.

    Proof.
  eapply [ex_intro](http://coq.inria.fr/library/Coq.Init.Logic.html#ex_intro). split.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply [BS_Eq[1]](Smallstep.html#CImp.BS_Eq<sub>1</sub>). apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.

  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply [BS_Eq[1]](Smallstep.html#CImp.BS_Eq<sub>1</sub>). apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply [BS_Eq[1]](Smallstep.html#CImp.BS_Eq<sub>1</sub>). apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

```

    更一般地说...

#### 练习：3 星，可选（par_body_n__Sn）

```
Lemma par_body_n__Sn : ∀n st,
  st X = n ∧ st Y = 0 →
  par_loop / st ⇒* par_loop / (t_update st X (S n)).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星，可选（par_body_n）

```
Lemma par_body_n : ∀n st,
  st X = 0 ∧ st Y = 0 →
  ∃st',
    par_loop / st ⇒*  par_loop / st' ∧ st' X = n ∧ st' Y = 0.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    ...上述循环可以以 X 具有任何值退出

    丝毫没有。

```
Theorem par_loop_any_X:
  ∀n, ∃st',
    par_loop / empty_state ⇒*  SKIP / st'
    ∧ st' X = n.

    Proof.
  intros n.
  destruct (par_body_n n empty_state).
    split; unfold t_update; reflexivity.

  rename x into st.
  inversion H as [H' [HX HY]]; clear H.
  ∃(t_update st Y 1). split.
  eapply multi_trans with (par_loop,st). apply H'.
  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply [BS_Eq[1]](Smallstep.html#CImp.BS_Eq<sub>1</sub>). apply AS_Id. rewrite t_update_eq.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  apply multi_refl.

  rewrite t_update_neq. assumption. intro X; inversion X.
    Qed.

End CImp.

```

# 一个小步栈机器

    我们的最后一个示例是栈机器的小步语义

    来自 Imp 章节的示例。

```
Definition stack := list nat.
Definition prog  := list sinstr.

Inductive stack_step : state → prog * stack → prog * stack → Prop :=
  | SS_Push : ∀st stk n p',
    stack_step st (SPush n :: p', stk)      (p', n :: stk)
  | SS_Load : ∀st stk i p',
    stack_step st (SLoad i :: p', stk)      (p', st i :: stk)
  | SS_Plus : ∀st stk n m p',
    stack_step st (SPlus :: p', n::m::stk)  (p', (m+n)::stk)
  | SS_Minus : ∀st stk n m p',
    stack_step st (SMinus :: p', n::m::stk) (p', (m-n)::stk)
  | SS_Mult : ∀st stk n m p',
    stack_step st (SMult :: p', n::m::stk)  (p', (m*n)::stk).

Theorem stack_step_deterministic : ∀st,
  deterministic (stack_step st).

    Proof.
  unfold deterministic. intros st x y[1] y[2] H[1] H[2].
  induction H[1]; inversion H[2]; reflexivity.
    Qed.

Definition stack_multistep st := multi (stack_step st).

```

#### 练习：3 星，高级（compiler_is_correct）

    记住给出 aexp 编译的定义

    Imp 章节。我们现在想证明编译正确性

    到栈机器。

    说明编译器正确的含义是什么

    栈机器的小步语义，然后证明它。

```
Definition compiler_is_correct_statement : Prop 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem compiler_is_correct : compiler_is_correct_statement.
Proof.
(* FILL IN HERE *) Admitted.

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
