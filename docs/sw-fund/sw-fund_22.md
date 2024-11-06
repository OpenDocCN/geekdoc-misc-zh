# AutoMore 自动化

```

```

导入 Coq.omega.Omega。

导入映射。

导入 Imp。

```

    Up to now, we've used the more manual part of Coq's tactic
    facilities.  In this chapter, we'll learn more about some of Coq's
    powerful automation features: proof search via the auto tactic,
    automated forward reasoning via the Ltac hypothesis matching
    machinery, and deferred instantiation of existential variables
    using eapply and eauto.  Using these features together with
    Ltac's scripting facilities will enable us to make our proofs
    startlingly short!  Used properly, they can also make proofs more
    maintainable and robust to changes in underlying definitions.  A
    deeper treatment of auto and eauto can be found in the
    UseAuto chapter.

    There's another major category of automation we haven't discussed
    much yet, namely built-in decision procedures for specific kinds
    of problems: omega is one example, but there are others.  This
    topic will be deferred for a while longer.

    Our motivating example will be this proof, repeated with just a
    few small changes from the Imp chapter.  We will simplify
    this proof in several stages.

```

Ltac inv H := inversion H；替换；清除 H。

定理 ceval_deterministic: ∀c st st[1] st[2]，

c / st ⇓ st[1] →

c / st ⇓ st[2] →

st[1] = st[2]。

证明。

intros c st st[1] st[2] E[1] E[2]；

推广依赖于 st[2]；

对 E[1] 进行归纳；intros st[2] E[2]；inv E[2]。

- (* E_Skip *) 反射性。

- (* E_Ass *) 反射性。

- (* E_Seq *)

断言 (st' = st'0) 如 EQ[1]。

{ (* 断言的证明 *) 应用 IHE1_1；假设。 }

替换 st'0。

应用 IHE1_2。假设。

(* E_IfTrue *)

- (* b 评估为 true *)

应用 IHE1。假设。

- (* b 评估为 false（矛盾） *)

在 H[5] 中重写 H。反演 H[5]。

(* E_IfFalse *)

- (* b 评估为 true（矛盾） *)

在 H[2] 中重写 H。反演 H[2]。

- (* b 评估为 false *)

应用 IHE1。假设。

(* E_WhileEnd *)

- (* b 评估为 false *)

反射性。

- (* b 评估为 true（矛盾） *)

在 H[2] 中重写 H。反演 H[2]。

(* E_WhileLoop *)

- (* b 评估为 false（矛盾） *)

在 H[4] 中重写 H。反演 H[4]。

- (* b 评估为 true *)

断言 (st' = st'0) 如 EQ[1]。

{ (* 断言的证明 *) 应用 IHE1_1；假设。 }

替换 st'0。

应用 IHE1_2。假设。Qed。

```

# The auto Tactic

    Thus far, our proof scripts mostly apply relevant hypotheses or
    lemmas by name, and one at a time.

```

例子 auto_example_1: ∀(P Q R：命��)，

(P → Q) → (Q → R) → P → R。

证明。

intros P Q R H[1] H[2] H[3].

应用 H[2]。应用 H[1]。假设。

Qed。

```

    The auto tactic frees us from this drudgery by *searching* for a
    sequence of applications that will prove the goal

```

例子 auto_example_1'：∀(P Q R：命题)，

(P → Q) → (Q → R) → P → R。

证明。

intros P Q R H[1] H[2] H[3]。

auto。

Qed。

```

    The auto tactic solves goals that are solvable by any combination of

*   intros and

*   apply (of hypotheses from the local context, by default).

    Using auto is always "safe" in the sense that it will never fail
    and will never change the proof state: either it completely solves
    the current goal, or it does nothing. 

    Here is a more interesting example showing auto's power:

```

例子 auto_example_2: ∀P Q R S T U：命题，

(P → Q) →

(P → R) →

(T → R) →

(S → T → U) →

((P→Q) → (P→S)) →

T →

P →

U。

证明。auto。Qed。

```

    Proof search could, in principle, take an arbitrarily long time,
    so there are limits to how far auto will search by default.

```

例子 auto_example_3: ∀(P Q R S T U：命题)，

(P → Q) →

(Q → R) →

(R → S) →

(S → T) →

(T → U) →

P →

U。

证明。

(* 当它无法解决目标时，auto 什么也不做 *)

auto。

(* 可选参数表示搜索的深度（默认为 5） *)

auto 6。

Qed。

```

    When searching for potential proofs of the current goal,
    auto considers the hypotheses in the current context together
    with a *hint database* of other lemmas and constructors.  Some
    common lemmas about equality and logical operators are installed
    in this hint database by default.

```

例子 auto_example_4: ∀P Q R：命题，

Q →

(Q → R) →

P ∨ (Q ∧ R)。

证明。auto。Qed。

```

    We can extend the hint database just for the purposes of one
    application of auto by writing auto using ....

```

引理 le_antisym: ∀n m：自然数，(n ≤ m ∧ m ≤ n) → n = m。

证明。intros。omega。Qed。

例子 auto_example_6: ∀n m p：自然数，

(n ≤ p → (n ≤ m ∧ m ≤ n)) →

n ≤ p →

n = m。

证明。

intros。

auto。(* 什么也不做：auto 不会分解假设！ *)

使用 le_antisym 自动。

Qed。

```

    Of course, in any given development there will probably be
    some specific constructors and lemmas that are used very often in
    proofs.  We can add these to the global hint database by writing

```

Hint Resolve T。

    在顶层，其中 T 是顶层定理或

    一个归纳定义命题的构造函数（即，任何东西

    其类型是一个蕴含）。作为简写，我们可以写

```
      Hint Constructors c.

    to tell Coq to do a Hint Resolve for *all* of the constructors
    from the inductive definition of c.

    It is also sometimes necessary to add

```

Hint Unfold d。

    其中 d 是一个定义的符号，因此 auto 知道要展开使用

    的 d，从而为应用引理打开进一步的可能性

    它知道的。

```
Hint Resolve le_antisym.

Example auto_example_6' : ∀n m p : nat,
  (n≤ p → (n ≤ m ∧ m ≤ n)) →
  n ≤ p →
  n = m.
Proof.
  intros.
  auto. (* picks up hint from database *)
Qed.

Definition is_fortytwo x := x = 42.

Example auto_example_7: ∀x, (x ≤ 42 ∧ 42 ≤ x) → is_fortytwo x.
Proof.
  auto. (* does nothing *)
Abort.

Hint Unfold is_fortytwo.

Example auto_example_7' : ∀x, (x ≤ 42 ∧ 42 ≤ x) → is_fortytwo x.
Proof. auto. Qed.

```

    现在让我们首先简化 ceval_deterministic

    证明脚本。

```
Theorem ceval_deterministic': ∀c st st[1] st[2],
     c / st ⇓ st[1]  →
     c / st ⇓ st[2] →
     st[1] = st[2].
Proof.
  intros c st st[1] st[2] E[1] E[2].
  generalize dependent st[2];
       induction E[1]; intros st[2] E[2]; inv E[2]; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ[1] by auto.
    subst st'0.
    auto.
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rewrite H in H[5]. inversion H[5].
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H[5]. inversion H[5].
  - (* E_WhileEnd *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H[2]. inversion H[2].
  (* E_WhileLoop *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H[4]. inversion H[4].
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ[1] by auto.
    subst st'0.
    auto.
Qed.

```

    当我们在证明中多次使用特定策略时

    可以使用 Proof 命令的变体将该策略转换为

    在证明中的默认。说 Proof with t（其中 t 是

    任意策略）允许我们使用 t[1]... 作为 t 的缩写

    t[1];t 在证明中。 作为示例，这里是一个替代

    先前证明的版本，使用 Proof with auto。

```
Theorem ceval_deterministic'_alt: ∀c st st[1] st[2],
     c / st ⇓ st[1]  →
     c / st ⇓ st[2] →
     st[1] = st[2].

    Proof with auto.
  intros c st st[1] st[2] E[1] E[2];
  generalize dependent st[2];
  induction E[1];
           intros st[2] E[2]; inv E[2]...
  - (* E_Seq *)
    assert (st' = st'0) as EQ[1]...
    subst st'0...
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rewrite H in H[5]. inversion H[5].
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H[5]. inversion H[5].
  - (* E_WhileEnd *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H[2]. inversion H[2].
  (* E_WhileLoop *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H[4]. inversion H[4].
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ[1]...
    subst st'0...
    Qed.

```

# 寻找假设

    证明变得更简单了，但仍然有一个恼人的

    重复的数量。让我们从解决矛盾开始

    情况。每种情况发生在我们同时拥有

```
      H[1]: beval st b = false

    and

```

H[2]: beval st b = true

    作为假设。矛盾是显而易见的，但证明它

    有点复杂：我们必须找到两个假设 H[1]

    和 H[2]并进行重写，然后进行反演。我们会

    喜欢自动化这个过程。

    （事实上，Coq 有一个内置的 tactic congruence，可以做到

    在这种情况下完成��这项工作。但我们将忽略这个 tactic 的存在

    目前，为了演示如何构建前向搜索

    手动 tactics。）

    作为第一步，我们可以将脚本中的一部分抽象出来

    通过在 Coq 的 tactic 编程中编写一个小函数来回答

    语言，Ltac。

```
Ltac rwinv H[1] H[2] := rewrite H[1] in H[2]; inv H[2].

Theorem ceval_deterministic'': ∀c st st[1] st[2],
     c / st ⇓ st[1]  →
     c / st ⇓ st[2] →
     st[1] = st[2].
Proof.
  intros c st st[1] st[2] E[1] E[2].
  generalize dependent st[2];
  induction E[1]; intros st[2] E[2]; inv E[2]; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ[1] by auto.
    subst st'0.
    auto.
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rwinv H H[5].
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rwinv H H[5].
  - (* E_WhileEnd *)
    + (* b evaluates to true (contradiction) *)
      rwinv H H[2].
  (* E_WhileLoop *)
  - (* b evaluates to false (contradiction) *)
    rwinv H H[4].
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ[1] by auto.
    subst st'0.
    auto. Qed.

```

    那是有点好一点，但不多。我们真的希望 Coq 能够

    为我们发现相关的假设。我们可以通过使用

    Ltac 的 match goal 功能。

```
Ltac find_rwinv :=
  match goal with
    H[1]: ?E = true,
    H[2]: ?E = false
    ⊢ _ ⇒ rwinv H[1] H[2]
  end.

```

    match goal tactic 寻找两个不同的假设

    具有相同任意表达式的等式形式

    E 在左边，右边有冲突的布尔值。

    如果找到这样的假设，它将把 H[1]和 H[2]绑定到它们的

    名称并将 rwinv tactic 应用于 H[1]和 H[2]。

    将这个 tactic 添加到我们在每种情况下调用的 tactic 中

    归纳处理所有矛盾情况。

```
Theorem ceval_deterministic''': ∀c st st[1] st[2],
     c / st ⇓ st[1]  →
     c / st ⇓ st[2] →
     st[1] = st[2].
Proof.
  intros c st st[1] st[2] E[1] E[2].
  generalize dependent st[2];
  induction E[1]; intros st[2] E[2]; inv E[2]; try find_rwinv; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ[1] by auto.
    subst st'0.
    auto.
  - (* E_WhileLoop *)
    + (* b evaluates to true *)
      assert (st' = st'0) as EQ[1] by auto.
      subst st'0.
      auto. Qed.

```

    让我们看看剩下的情况。每种情况都涉及

    应用条件假设来提取一个等式。

    目前我们已经将这些表述为断言，所以我们必须

    预测结果的等式将是什么（尽管我们可以

    使用 auto 来证明它）。另一种方法是选择相关的

    使用的假设，然后按照以下方式重写：

```
Theorem ceval_deterministic'''': ∀c st st[1] st[2],
     c / st ⇓ st[1]  →
     c / st ⇓ st[2] →
     st[1] = st[2].
Proof.
  intros c st st[1] st[2] E[1] E[2].
  generalize dependent st[2];
  induction E[1]; intros st[2] E[2]; inv E[2]; try find_rwinv; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H[1]) in *. auto.
  - (* E_WhileLoop *)
    + (* b evaluates to true *)
      rewrite (IHE1_1 st'0 H[3]) in *. auto. Qed.

```

    现在我们可以自动化找到相关假设的任务

    重写。

```
Ltac find_eqn :=
  match goal with
    H[1]: ∀x, ?P x → ?L = ?R,
    H[2]: ?P ?X
    ⊢ _ ⇒ rewrite (H[1] X H[2]) in *
  end.

```

    模式∀ x，?P x → ?L = ?R 匹配任何假设

    形式为“对于所有 x，*x 的某个属性*意味着*某个相等*。” x 的属性绑定到模式变量

    P，等式的左右两侧被绑定

    到 L 和 R。这个假设的名称绑定到 H[1]。

    然后模式?P ?X 匹配任何提供

    证据表明 P 对某个具体 X 成立。如果两种模式

    成功，我们应用重写 tactic（实例化

    用 X 量化 x 并提供 H[2]作为所需的

    证据 P X)在所有假设和目标中。

    一个问题仍然存在：一般来说，可能有几对

    具有正确一般形式的假设，看起来很棘手

    选择我们实际需要的那些。一个关键技巧是意识到

    我们可以*尝试它们全部*！这是它的工作原理：

+   每次执行 match goal 都会继续尝试找到一对有效的假设，直到 match 右侧的 tactic 成功为止；如果没有这样的对，它就会失败；

+   重写将失败，给出形式为 X = X 的平凡方程；

+   我们可以将整个事情包装在一个重复中，这将一直进行有用的重写，直到只剩下琐碎的重写。

```
Theorem ceval_deterministic''''': ∀c st st[1] st[2],
     c / st ⇓ st[1]  →
     c / st ⇓ st[2] →
     st[1] = st[2].
Proof.
  intros c st st[1] st[2] E[1] E[2].
  generalize dependent st[2];
  induction E[1]; intros st[2] E[2]; inv E[2]; try find_rwinv;
    repeat find_eqn; auto.
Qed.

```

    这种方法的巨大回报是我们的证明脚本

    应该在我们的语言面对适度变化时具有鲁棒性。

    例如，我们可以向语言添加一个 REPEAT 命令。

```
Module Repeat.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com
  | CRepeat : com → bexp → com.

```

    REPEAT 的行为类似于 WHILE，只是循环保护是

    在每次执行主体之后检查*，循环

    只要保持*false*，就重复。由于这个原因，

    主体将始终至少执行一次。

```
Notation "'SKIP'" :=
  CSkip.
Notation "c1 ; c2" :=
  (CSeq c[1] c[2]) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e[1] e[2] e[3]) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e[1] b[2]) (at level 80, right associativity).

Inductive ceval : state → com → state → Prop :=
  | E_Skip : ∀st,
      ceval st SKIP st
  | E_Ass  : ∀st a[1] n X,
      aeval st a[1] = n →
      ceval st (X ::= a[1]) (t_update st X n)
  | E_Seq : ∀c[1] c[2] st st' st'',
      ceval st c[1] st' →
      ceval st' c[2] st'' →
      ceval st (c[1] ; c[2]) st''
  | E_IfTrue : ∀st st' b[1] c[1] c[2],
      beval st b[1] = true →
      ceval st c[1] st' →
      ceval st (IFB b[1] THEN c[1] ELSE c[2] FI) st'
  | E_IfFalse : ∀st st' b[1] c[1] c[2],
      beval st b[1] = false →
      ceval st c[2] st' →
      ceval st (IFB b[1] THEN c[1] ELSE c[2] FI) st'
  | E_WhileEnd : ∀b[1] st c[1],
      beval st b[1] = false →
      ceval st (WHILE b[1] DO c[1] END) st
  | E_WhileLoop : ∀st st' st'' b[1] c[1],
      beval st b[1] = true →
      ceval st c[1] st' →
      ceval st' (WHILE b[1] DO c[1] END) st'' →
      ceval st (WHILE b[1] DO c[1] END) st''
  | E_RepeatEnd : ∀st st' b[1] c[1],
      ceval st c[1] st' →
      beval st' b[1] = true →
      ceval st (CRepeat c[1] b[1]) st'
  | E_RepeatLoop : ∀st st' st'' b[1] c[1],
      ceval st c[1] st' →
      beval st' b[1] = false →
      ceval st' (CRepeat c[1] b[1]) st'' →
      ceval st (CRepeat c[1] b[1]) st''.

Notation "c1 '/' st '⇓' st'" := (ceval st c[1] st')
                                 (at level 40, st at level 39).

```

    我们对证明的第一次尝试令人失望：E_RepeatEnd

    和 E_RepeatLoop 情况不被我们之前处理

    自动化。

```
Theorem ceval_deterministic: ∀c st st[1] st[2],
     c / st ⇓ st[1]  →
     c / st ⇓ st[2] →
     st[1] = st[2].
Proof.
  intros c st st[1] st[2] E[1] E[2].
  generalize dependent st[2];
  induction E[1];
    intros st[2] E[2]; inv E[2]; try find_rwinv; repeat find_eqn; auto.
  - (* E_RepeatEnd *)
    + (* b evaluates to false (contradiction) *)
       find_rwinv.
       (* oops: why didn't find_rwinv solve this for us already?           answer: we did things in the wrong order. *)
  - (* E_RepeatLoop *)
     + (* b evaluates to true (contradiction) *)
        find_rwinv.
Qed.

```

    要解决这个问题，我们只需交换 find_eqn 的调用

    和 find_rwinv。

```
Theorem ceval_deterministic': ∀c st st[1] st[2],
     c / st ⇓ st[1]  →
     c / st ⇓ st[2] →
     st[1] = st[2].
Proof.
  intros c st st[1] st[2] E[1] E[2].
  generalize dependent st[2];
  induction E[1];
    intros st[2] E[2]; inv E[2]; repeat find_eqn; try find_rwinv; auto.
Qed.

End Repeat.

```

    这些例子只是展示了“超自动化”可以做什么

    在 Coq 中实现。match goal 的细节有点棘手，而且

    使用它调试脚本，坦率地说，不是很愉快。但是

    值得至少将简单用法添加到您的证明中，以便

    避免枯燥和“未来证明”它们。

### eapply 和 eauto

    为了结束本章，我们将介绍一个更方便的功能

    Coq 的一个特点：它能够延迟量词的实例化。为了

    为了激发这一特性，回想一下来自 Imp 的例子

    章节：

```
Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   ⇓ (t_update (t_update empty_state X 2) Z 4).
Proof.
  (* We supply the intermediate state st'... *)
  apply E_Seq with (t_update empty_state X 2).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse. reflexivity. apply E_Ass. reflexivity.
Qed.

```

    在证明的第一步中，我们不得不明确提供一个

    较长的表达式帮助 Coq 实例化一个“隐藏”的参数

    E_Seq 构造函数。这是必要的，因为定义

    E_Seq 的...

```
          E_Seq : ∀c[1] c[2] st st' st'',
            c[1] / st  ⇓ st' →
            c[2] / st' ⇓ st'' →
            (c[1] ;; c[2]) / st ⇓ st''

    is quantified over a variable, st', that does not appear in its
   conclusion, so unifying its conclusion with the goal state doesn't
   help Coq find a suitable value for this variable.  If we leave
   out the with, this step fails ("Error: Unable to find an
   instance for the variable st'").

    What's silly about this error is that the appropriate value for st'
   will actually become obvious in the very next step, where we apply
   E_Ass.  If Coq could just wait until we get to this step, there
   would be no need to give the value explicitly.  This is exactly what
   the eapply tactic gives us:

```

例子 ceval'_example1：

(X ::= ANum 2;;

IFB BLe（AId X）（ANum 1）

然后 Y ::= ANum 3

ELSE Z ::= ANum 4

FI)

/ 空状态

⇓ (t_update (t_update empty_state X 2) Z 4)。

证明。

eapply E_Seq。(* 1 *)

- 应用 E_Ass。(* 2 *)

一致性。(* 3 *)

- (* 4 *) 应用 E_IfFalse。一致性。应用 E_Ass。一致性。

Qed.

```

    The tactic eapply H tactic behaves just like apply H except
    that, after it finishes unifying the goal state with the
    conclusion of H, it does not bother to check whether all the
    variables that were introduced in the process have been given
    concrete values during unification.

    If you step through the proof above, you'll see that the goal
    state at position 1 mentions the *existential variable* ?st'
    in both of the generated subgoals.  The next step (which gets us
    to position 2) replaces ?st' with a concrete value.  This new
    value contains a new existential variable ?n, which is
    instantiated in its turn by the following reflexivity step,
    position 3.  When we start working on the second
    subgoal (position 4), we observe that the occurrence of ?st'
    in this subgoal has been replaced by the value that it was given
    during the first subgoal. 

    Several of the tactics that we've seen so far, including ∃,
    constructor, and auto, have e... variants.  For example,
    here's a proof using eauto:

```

Hint 构造者 ceval。

Hint 透明状态。

Hint 透明 total_map。

定义 st[12] := t_update（t_update empty_state X 1）Y 2。

定义 st[21] := t_update（t_update empty_state X 2）Y 1。

例子 auto_example_8：∃s'，

（IFB（BLe（AId X）（AId Y））

然后（Z ::= AMinus（AId Y）（AId X））

ELSE（Y ::= APlus（AId X）（AId Z））

FI）/ st[21] ⇓ s'。

证明。eauto。Qed。

```

    The eauto tactic works just like auto, except that it uses
    eapply instead of apply. 

```

```

```

```

```

```

```
