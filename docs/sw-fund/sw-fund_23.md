# 类型系统

```

    Our next major topic is *type systems* — static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of the simplest
    imaginable language, to introduce the basic ideas of types and
    typing rules and the fundamental theorems about type systems:
    *type preservation* and *progress*.  In chapter Stlc we'll move
    on to the *simply typed lambda-calculus*, which lives at the core
    of every modern functional programming language (including
    Coq!).

```

导入 Coq.Arith.Arith。

导入 Maps。

导入 Imp。

导入 Smallstep。

提示 构造子 multi。

```

# Typed Arithmetic Expressions

    To motivate the discussion of type systems, let's begin as
    usual with a tiny toy language.  We want it to have the potential
    for programs to go wrong because of runtime type errors, so we
    need something a tiny bit more complex than the language of
    constants and addition that we used in chapter Smallstep: a
    single kind of data (e.g., numbers) is too simple, but just two
    kinds (numbers and booleans) gives us enough material to tell an
    interesting story.

    The language definition is completely routine.

```

## 语法

    这是语法，非正式地：

```
    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t

    And here it is formally:

```

归纳 tm：Type :=

| ttrue : tm

| tfalse : tm

| tif : tm → tm → tm → tm

| tzero : tm

| tsucc : tm → tm

| tpred : tm → tm

| tiszero : tm → tm。

```

    *Values* are true, false, and numeric values...

```

归纳 bvalue：tm → Prop :=

| bv_true : bvalue ttrue

| bv_false : bvalue tfalse。

归纳 nvalue：tm → Prop :=

| nv_zero : nvalue tzero

| nv_succ : ∀t, nvalue t → nvalue (tsucc t).

定义 值（t:tm）:= bvalue t ∨ nvalue t。

提示 构造子 bvalue nvalue。

提示 展开值。

提示 展开更新。

```

## Operational Semantics

    Here is the single-step relation, first informally... 

           |

                        (ST_IfTrue)  
           |

* * *

           |

                        if true then t[1] else t[2] ⇒ t[1]
           |

                     |

           |

                        (ST_IfFalse)  
           |

* * *

           |

                        if false then t[1] else t[2] ⇒ t[2]
           |

                     |

                        t[1] ⇒ t[1]'
           |

                        (ST_If)  
           |

* * *

           |

                        if t[1] then t[2] else t[3] ⇒ if t[1]' then t[2] else t[3]
           |

                     |

                        t[1] ⇒ t[1]'
           |

                        (ST_Succ)  
           |

* * *

           |

                        succ t[1] ⇒ succ t[1]'
           |

                     |

           |

                        (ST_PredZero)  
           |

* * *

           |

                        pred 0 ⇒ 0
           |

                     |

                        numeric value v[1]
           |

                        (ST_PredSucc)  
           |

* * *

           |

                        pred (succ v[1]) ⇒ v[1]
           |

                     |

                        t[1] ⇒ t[1]'
           |

                        (ST_Pred)  
           |

* * *

           |

                        pred t[1] ⇒ pred t[1]'
           |

                     |

           |

                        (ST_IszeroZero)  
           |

* * *

           |

                        iszero 0 ⇒ true
           |

                     |

                        numeric value v[1]
           |

                        (ST_IszeroSucc)  
           |

* * *

           |

                        iszero (succ v[1]) ⇒ false
           |

                     |

                        t[1] ⇒ t[1]'
           |

                        (ST_Iszero)  
           |

* * *

           |

                        iszero t[1] ⇒ iszero t[1]'
           |

                     |

    ... and then formally:

```

保留符号 "t1 '⇒' t2"（在级别 40）。

归纳步骤：tm → tm → Prop :=

| ST_IfTrue : ∀t[1] t[2],

(tif ttrue t[1] t[2]) ⇒ t[1]

| ST_IfFalse : ∀t[1] t[2],

(tif tfalse t[1] t[2]) ⇒ t[2]

| ST_If : ∀t[1] t[1]' t[2] t[3],

t[1] ⇒ t[1]' →

(tif t[1] t[2] t[3]) ⇒ (tif t[1]' t[2] t[3])

| ST_Succ : ∀t[1] t[1]',

t[1] ⇒ t[1]' →

(tsucc t[1]) ⇒ (tsucc t[1]')

| ST_PredZero：

(tpred tzero) ⇒ tzero

| ST_PredSucc : ∀t[1],

nvalue t[1] →

(tpred (tsucc t[1])) ⇒ t[1]

| ST_Pred : ∀t[1] t[1]',

t[1] ⇒ t[1]' →

(tpred t[1]) ⇒ (tpred t[1]')

| ST_IszeroZero：

(tiszero tzero) ⇒ ttrue

| ST_IszeroSucc : ∀t[1],

nvalue t[1] →

(tiszero (tsucc t[1])) ⇒ tfalse

| ST_Iszero : ∀t[1] t[1]',

t[1] ⇒ t[1]' →

(tiszero t[1]) ⇒ (tiszero t[1]')

其中“t1 '⇒' t2” := (step t[1] t[2])。

提示 构造子 step。

```

    Notice that the step relation doesn't care about whether
    expressions make global sense — it just checks that the operation
    in the *next* reduction step is being applied to the right kinds
    of operands.  For example, the term succ true (i.e., 
    tsucc ttrue in the formal syntax) cannot take a step, but the
    almost as obviously nonsensical term

```

succ (if true then true else true)

    可以进行一步（一次，然后卡住）。

```

## Normal Forms and Values

    The first interesting thing to notice about this step relation
    is that the strong progress theorem from the Smallstep chapter
    fails here.  That is, there are terms that are normal forms (they
    can't take a step) but not values (because we have not included
    them in our definition of possible "results of reduction").  Such
    terms are *stuck*.

```

正常形式步骤 := (normal_form step)。

定义 卡住（t:tm）：Prop :=

步骤正常形式 t ∧ ¬ 值 t。

提示 展开卡住。

```

#### Exercise: 2 stars (some_term_is_stuck)

```

例如 某些项卡住：

∃t，卡住 t。

证明

(* 在此填写*) 已承认。

```

    ☐ 

    However, although values and normal forms are *not* the same in this
    language, the set of values is included in the set of normal
    forms.  This is important because it shows we did not accidentally
    define things so that some value could still take a step. 

#### Exercise: 3 stars (value_is_nf)

```

引理 value_is_nf : ∀t,

值 t → 步骤正常形式 t。

    证明。

(* 在此填写*) 已承认。

```

    (Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways.)  ☐ 

#### Exercise: 3 stars, optional (step_deterministic)

    Use value_is_nf to show that the step relation is also
    deterministic.

```

定理 step_deterministic:

确定性步骤。

证明 使用 eauto。

(* 在此填写*) 已承认。

```

    ☐

```

## 类型

    下一个关键观察是，尽管这样

    语言有卡住的项，它们总是毫无意义，混合

    布尔值和数字的方式，我们甚至 *不想* 有一个

    意义。我们可以通过定义一个轻松排除这种类型不正确的项

    *类型关系* 将项与类型（数字或布尔值）相关联

    或布尔值）的最终结果。

```
Inductive ty : Type :=
  | TBool : ty
  | TNat : ty.

```

    在非正式表示中，类型关系通常写作

    ⊢ t ∈ T 并发音为 "t 的类型为 T。" 符号 ⊢

    被称为“转角线”。下面，我们将看到更丰富的类型

    具有一个或多个额外的“上下文”参数的关系

    写在转角线的左边。目前，上下文

    总是空的。

        |

                        (T_True)

        |

* * *

        |

                        ⊢ true ∈ Bool

        |

                    |

        |

                        (T_False)

        |

* * *

        |

                        ⊢ false ∈ Bool

        |

                    |

                        ⊢ t[1] ∈ Bool    ⊢ t[2] ∈ T    ⊢ t[3] ∈ T

        |

                        (T_If)

        |

* * *

        |

                        ⊢ if t[1] then t[2] else t[3] ∈ T

        |

                    |

        |

                        (T_Zero)

        |

* * *

        |

                        ⊢ 0 ∈ Nat

        |

                    |

                        ⊢ t[1] ∈ Nat

        |

                        (T_Succ)

        |

* * *

        |

                        ⊢ succ t[1] ∈ Nat

        |

                    |

                        ⊢ t[1] ∈ Nat

        |

                        (T_Pred)

        |

* * *

        |

                        ⊢ pred t[1] ∈ Nat

        |

                    |

                        ⊢ t[1] ∈ Nat

        |

                        (T_IsZero)

        |

* * *

        |

                        ⊢ iszero t[1] ∈ Bool

        |

                    |

```
Reserved Notation "'⊢' t '∈' T" (at level 40).

Inductive has_type : tm → ty → Prop :=
  | T_True :
       ⊢ ttrue ∈ TBool
  | T_False :
       ⊢ tfalse ∈ TBool
  | T_If : ∀t[1] t[2] t[3] T,
       ⊢ t[1] ∈ TBool →
       ⊢ t[2] ∈ T →
       ⊢ t[3] ∈ T →
       ⊢ tif t[1] t[2] t[3] ∈ T
  | T_Zero :
       ⊢ tzero ∈ TNat
  | T_Succ : ∀t[1],
       ⊢ t[1] ∈ TNat →
       ⊢ tsucc t[1] ∈ TNat
  | T_Pred : ∀t[1],
       ⊢ t[1] ∈ TNat →
       ⊢ tpred t[1] ∈ TNat
  | T_Iszero : ∀t[1],
       ⊢ t[1] ∈ TNat →
       ⊢ tiszero t[1] ∈ TBool

where "'⊢' t '∈' T" := (has_type t T).

Hint Constructors has_type.

Example has_type_1 :
  ⊢ tif tfalse tzero (tsucc tzero) ∈ TNat.
Proof.
  apply T_If.
    - apply T_False.
    - apply T_Zero.
    - apply T_Succ.
       + apply T_Zero.
Qed.

```

    （因为我们已经包含了类型关系的所有构造函数

    在提示数据库中，auto 策略实际上可以找到这个

    自动证明。）

    重要的是要意识到类型关系是一个

    *保守*（或*静态*）逼近：它不考虑

    当项被减少时会发生什么 — 特别是，它不

    不计算其正常形式的类型。

```
Example has_type_not :
  ¬ (⊢ tif tfalse tzero ttrue ∈ TBool).

    Proof.
  intros Contra. solve_by_inverts 2\. Qed.

```

#### 练习：1 星，可选（succ_hastype_nat__hastype_nat）

```
Example succ_hastype_nat__hastype_nat : ∀t,
  ⊢ tsucc t ∈ TNat →
  ⊢ t ∈ TNat.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

### Canonical forms

    The following two lemmas capture the fundamental property that the
    definitions of boolean and numeric values agree with the typing
    relation.

```

引理 bool_canonical：∀t，

⊢ t ∈ TBool → value t → bvalue t.

    证明。

intros t HT HV。

inversion HV; auto.

induction H; inversion HT; auto。

    完成。

引理 nat_canonical：∀t，

⊢ t ∈ TNat → value t → nvalue t。

    证明。

intros t HT HV。

inversion HV。

inversion H; subst; inversion HT。

auto。

    完成。

```

## Progress

    The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are not stuck — or conversely, if a
    term is well typed, then either it is a value or it can take at
    least one step.  We call this *progress*. 

#### Exercise: 3 stars (finish_progress)

```

定理进展：∀t T，

⊢ t ∈ T →

value t ∨ ∃t'，t ⇒ t'。

```

    Complete the formal proof of the progress property.  (Make sure
    you understand the parts we've given of the informal proof in the
    following exercise before starting — this will save you a lot of
    time.)

```

    证明与 auto。

intros t T HT。

归纳 HT...

（*显然是值的情况，如 T_True 和 T_False，立即被 auto 消除*）

-（* T_If *）

right. inversion IHHT1; clear IHHT1.

+（* t[1] 是一个值*）

apply (bool_canonical t[1] HT[1]) in H.

inversion H; subst; clear H.

∃t[2]...

∃t[3]...

+（* t[1] 可以进行一步*）

inversion H as [t[1]' H[1]]。

∃(tif t[1]' t[2] t[3])...

（*在这里填写*）已承认。

```

    ☐ 

#### Exercise: 3 stars, advancedM (finish_progress_informal)

    Complete the corresponding informal proof: 

    *Theorem*: If ⊢ t ∈ T, then either t is a value or else
    t ⇒ t' for some t'. 

    *Proof*: By induction on a derivation of ⊢ t ∈ T.

*   If the last rule in the derivation is T_If, then t = if t[1] then t[2] else t[3], with ⊢ t[1] ∈ Bool, ⊢ t[2] ∈ T and ⊢ t[3] ∈ T. By the IH, either t[1] is a value or else t[1] can step to some t[1]'. 

    *   If t[1] is a value, then by the canonical forms lemmas and the fact that ⊢ t[1] ∈ Bool we have that t[1] is a bvalue — i.e., it is either true or false. If t[1] = true, then t steps to t[2] by ST_IfTrue, while if t[1] = false, then t steps to t[3] by ST_IfFalse. Either way, t can step, which is what we wanted to show. 

    *   If t[1] itself can take a step, then, by ST_If, so can t. 

*   (* FILL IN HERE *)

    ☐ 

    This theorem is more interesting than the strong progress theorem
    that we saw in the Smallstep chapter, where *all* normal forms
    were values.  Here a term can be stuck, but only if it is ill
    typed.

```

## 类型保持

    类型的第二个关键属性是，当一个良好类型的

    项进行一步，结果也是一个良好类型的项。

#### 练习：2 星（finish_preservation）

```
Theorem preservation : ∀t t' T,
  ⊢ t ∈ T →
  t ⇒ t' →
  ⊢ t' ∈ T.

```

    完成保持性质的形式证明。（再次，

    确保你理解了上面的非正式证明片段

    首先完成以下练习。）

```

    Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible             cases all at once *)
         try solve_by_invert.
    - (* T_If *) inversion HE; subst; clear HE.
      + (* ST_IFTrue *) assumption.
      + (* ST_IfFalse *) assumption.
      + (* ST_If *) apply T_If; try assumption.
        apply IHHT1; assumption.
    (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星，高级 M（finish_preservation_informal）

    完成以下非正式证明：

    *定理*：如果 ⊢ t ∈ T 并且 t ⇒ t'，那么 ⊢ t' ∈ T。

    *证明*：通过 ⊢ t ∈ T 的推导归纳。

+   如果推导中的最后一条规则是 T_If，则 t = if t[1] then t[2] else t[3]，其中 ⊢ t[1] ∈ Bool，⊢ t[2] ∈ T，⊢ t[3] ∈ T。

    检查小步减少关系的规则，并记住 t 的形式是 if ...，我们看到可以用来证明 t ⇒ t' 的唯一规则是 ST_IfTrue、ST_IfFalse 或 ST_If。

    +   如果最后一条规则是 ST_IfTrue，则 t' = t[2]。但我们知道 ⊢ t[2] ∈ T，所以我们完成了。

    +   如果最后一条规则是 ST_IfFalse，则 t' = t[3]。但我们知道 ⊢ t[3] ∈ T，所以我们完成了。

    +   如果最后一条规则是 ST_If，则 t' = if t[1]' then t[2] else t[3]，其中 t[1] ⇒ t[1]'。我们知道 ⊢ t[1] ∈ Bool，所��根据 IH，⊢ t[1]' ∈ Bool。然后 T_If 规则给出 ⊢ if t[1]' then t[2] else t[3] ∈ T，符合要求。

+   （*在这里填写*）

    ☐

#### 练习：3 星（preservation_alternate_proof）

    现在通过对

    *评估*推导而不是类型推导的归纳。

    从仔细阅读和思考前几行开始

    上述证明的行，确保你理解了什么

    每个人都在做什么。这个证明的设置类似，但是

    不完全相同。

```
Theorem preservation' : ∀t t' T,
  ⊢ t ∈ T →
  t ⇒ t' →
  ⊢ t' ∈ T.
Proof with eauto.
  (* FILL IN HERE *) Admitted.

```

    ☐

    保持定理通常被称为*主题约简*，

    因为它告诉我们当类型的"主语"发生时会发生什么

    关系被简化。这个术语来源于思考

    将语句作为句子，其中术语是主语和

    类型是谓词。

```

## Type Soundness

    Putting progress and preservation together, we see that a
    well-typed term can never reach a stuck state.

```

定义 multistep := (multi step)。

符号 "t1 '⇒*' t2" := (multistep t[1] t[2])（在 40 级处）。

推论 合理性：∀t t' T，

⊢ t ∈ T →

t ⇒* t' →

~(stuck t')。

    证明

对于每个 P，归纳 P；对于每个 [R S]，归纳 P。

破坏 (progress x T HT)；自动。

应用 IHP。应用 (preservation x y T HT H)。

展开 stuck。分割；自动。Qed。

```

# Aside: the normalize Tactic

    When experimenting with definitions of programming languages
    in Coq, we often want to see what a particular concrete term steps
    to — i.e., we want to find proofs for goals of the form t ⇒* t', where t is a completely concrete term and t' is unknown.
    These proofs are quite tedious to do by hand.  Consider, for
    example, reducing an arithmetic expression using the small-step
    relation astep.

```

模块 NormalizePlayground。

导入 Smallstep。

例子 step_example1：

(P (C 3) (P (C 3) (C 4)))

⇒* (C 10)。

证明

应用 multi_step with (P (C 3) (C 7))。

应用 ST_Plus2。

应用 v_const。

应用 ST_PlusConstConst。

应用 multi_step with (C 10)。

应用 ST_PlusConstConst。

apply multi_refl。

Qed。

```

    The proof repeatedly applies multi_step until the term reaches a
    normal form.  Fortunately The sub-proofs for the intermediate
    steps are simple enough that auto, with appropriate hints, can
    solve them.

```

提示 构造函数 step value。

例子 step_example1'：

(P (C 3) (P (C 3) (C 4)))

⇒* (C 10)。

证明。

eapply multi_step。自动。简化。

eapply multi_step。自动。简化。

apply multi_refl。

Qed。

```

    The following custom Tactic Notation definition captures this
    pattern.  In addition, before each step, we print out the current
    goal, so that we can follow how the term is being reduced.

```

策略标记 "print_goal" :=

匹配目标，其中 ⊢ ?x ⇒ idtac x。

策略标记 "normalize" :=

重复（打印目标；应用 multi_step；

[ (eauto 10; fail) | (instantiate; simpl)]);

apply multi_refl.

例子 step_example1''：

(P (C 3) (P (C 3) (C 4)))

⇒* (C 10)。

证明

normalize。

(* normalize 策略中的 print_goal 显示了表达式如何简化...          (P (C 3) (P C 3) (C 4)) ==>* C 10)          (P (C 3) (C 7) ==>* C 10)          (C 10 ==>* C 10)                         *)

Qed。

```

    The normalize tactic also provides a simple way to calculate the
    normal form of a term, by starting with a goal with an existentially
    bound variable.

```

例子 step_example1'''：∃e'，

(P (C 3) (P (C 3) (C 4)))

⇒* e'。

证明。

eapply ex_intro。normalize。

(* 这一次，追踪是：        (P (C 3) (P C 3) (C 4)) ==>* ?e')        (P (C 3) (C 7) ==>* ?e')        (C 10 ==>* ?e')    其中 ?e' 是 eapply "猜测"的变量。*)

Qed.

```

#### Exercise: 1 star (normalize_ex)

```

定理 normalize_ex：∃e'，

(P (C 3) (P (C 2) (C 1)))

⇒* e'。

证明

(* 在这里填写 *) 已承认。

```

    ☐ 

#### Exercise: 1 star, optional (normalize_ex')

    For comparison, prove it using apply instead of eapply.

```

定理 normalize_ex'：∃e'，

(P (C 3) (P (C 2) (C 1)))

⇒* e'。

证明

(* 在这里填写 *) 已承认。

```

    ☐

```

结束 NormalizePlayground。

策略标记 "print_goal" :=

匹配目标，其中 ⊢ ?x ⇒ idtac x。

策略标记 "normalize" :=

重复（打印目标；应用 multi_step；

[ (eauto 10; fail) | (instantiate; simpl)]);

apply multi_refl.

```

## Additional Exercises

#### Exercise: 2 stars, recommendedM (subject_expansion)

    Having seen the subject reduction property, one might
    wonder whether the opposity property — subject *expansion* —
    also holds.  That is, is it always the case that, if t ⇒ t'
    and ⊢ t' ∈ T, then ⊢ t ∈ T?  If so, prove it.  If
    not, give a counter-example.  (You do not need to prove your
    counter-example in Coq, but feel free to do so.)

    (* FILL IN HERE *)

    ☐ 

#### Exercise: 2 starsM (variation1)

    Suppose, that we add this new rule to the typing relation:

```

| T_SuccBool : ∀t，

⊢ t ∈ TBool →

⊢ tsucc t ∈ TBool

    以下哪些属性在...的情况下保持真实

这个规则？对于每一个，写出"保持真实"或

否则"变为假。"如果一个属性变为假，给出一个

反例。

+   步骤的确定性

+   进展

+   保持性质

    ☐

#### 练习：2 星 M（变体 2）

    假设，相反，我们将这个新规则添加到步骤关系中：

```
      | ST_Funny1 : ∀t[2] t[3],
           (tif ttrue t[2] t[3]) ⇒ t[3]

    Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

    ☐ 

#### Exercise: 2 stars, optional (variation3)

    Suppose instead that we add this rule:

```

| ST_Funny2 : ∀t[1] t[2] t[2]' t[3]，

t[2] ⇒ t[2]' →

(tif t[1] t[2] t[3]) ⇒ (tif t[1] t[2]' t[3])

    以上哪些属性在...的情况下变为假

这个规则？对于每一个，给出一个反例。

    ☐

#### 练习：2 星，可选（变体 4）

    假设我们添加这条规则：

```
      | ST_Funny3 :
          (tpred tfalse) ⇒ (tpred (tpred tfalse))

    Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

    ☐ 

#### Exercise: 2 stars, optional (variation5)

    Suppose instead that we add this rule:

```

| T_Funny4 :

⊢ tzero ∈ TBool

    在这条规则存在的情况下，上述哪些属性变为假？

对于每一个变为假的属性，给出一个反例。

    ☐

#### 练习：2 星，可选（变体 6）

    假设我们添加这条规则：

```
      | T_Funny5 :
            ⊢ tpred tzero ∈ TBool

    Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

    ☐ 

#### Exercise: 3 stars, optional (more_variations)

    Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties — i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
    ☐ 

#### Exercise: 1 starM (remove_predzero)

    The reduction rule E_PredZero is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of zero to
    be undefined, rather than being defined to be zero.  Can we
    achieve this simply by removing the rule from the definition of
    step?  Would doing so create any problems elsewhere?

    (* FILL IN HERE *)

    ☐ 

#### Exercise: 4 stars, advancedM (prog_pres_bigstep)

    Suppose our evaluation relation is defined in the big-step style.
    What are the appropriate analogs of the progress and preservation
    properties?  (You do not need to prove them.)

    (* FILL IN HERE *)

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
