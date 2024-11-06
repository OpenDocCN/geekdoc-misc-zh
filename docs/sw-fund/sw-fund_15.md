# ImpCEvalFunEvaluation Function for Imp

```

    We saw in the Imp chapter how a naive approach to defining a
    function representing evaluation for Imp runs into difficulties.
    There, we adopted the solution of changing from a functional to a
    relational definition of evaluation.  In this optional chapter, we
    consider strategies for getting the functional approach to
    work.

```

# 一个破碎的评估器

```
(* IMPORTS *)
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Arith.
Require Import Imp.
Require Import Maps.
(* /IMPORTS *)

```

    这是我们为命令编写的评估函数的第一次尝试，

    省略 WHILE。

```
Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | SKIP ⇒
        st
    | l ::= a[1] ⇒
        t_update st l (aeval st a[1])
    | c[1] ;; c[2] ⇒
        let st' := ceval_step1 st c[1] in
        ceval_step1 st' c[2]
    | IFB b THEN c[1] ELSE c[2] FI ⇒
        if (beval st b)
          then ceval_step1 st c[1]
          else ceval_step1 st c[2]
    | WHILE b[1] DO c[1] END ⇒
        st  (* bogus *)
  end.

```

    正如我们在章节 Imp 中所述，在传统的功能性

    programming language like ML or Haskell we could write the WHILE

    case as follows:

```
    | WHILE b1 DO c1 END => if (beval st b1) then ceval_step1 st (c1;;
        WHILE b1 DO c1 END) else st

```

    Coq 不接受这样的定义（错误：无法猜测 fix 的递减参数），因为我们想要的函数

    定义不能保证终止。实际上，改变

    ceval_step1 function applied to the loop program from Imp.v

    永远不会终止。由于 Coq 不仅仅是一个功能性的

    programming language, but also a consistent logic, any potentially

    非终止函数需要被拒绝。这里是一个

    无效的(!) Coq 程序，展示了如果 Coq 允许

    非终止递归函数会出现什么问题：

```
     Fixpoint loop_false (n : nat) : False := loop_false n.

```

    换句话说，像 False 这样的命题会变成

    provable (e.g., loop_false 0 would be a proof of False), which

    对 Coq 的逻辑一致性将是一场灾难。

    因此，因为它不会在所有输入上终止，完整版本

    ceval_step1 的情况不能在 Coq 中写出 — 至少不会终止

    另一个额外的技巧...

```

# A Step-Indexed Evaluator

    The trick we need is to pass an *additional* parameter to the
    evaluation function that tells it how long to run.  Informally, we
    start the evaluator with a certain amount of "gas" in its tank,
    and we allow it to run until either it terminates in the usual way
    *or* it runs out of gas, at which point we simply stop evaluating
    and say that the final result is the empty memory.  (We could also
    say that the result is the current state at the point where the
    evaluator runs out fo gas — it doesn't really matter because the
    result is going to be wrong in either case!)

```

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=

match i with

| O ⇒ empty_state

| S i' ⇒

match c with

| SKIP ⇒

st

| l ::= a[1] ⇒

t_update st l (aeval st a[1])

| c[1] ;; c[2] ⇒

let st' := ceval_step2 st c[1] i' in

ceval_step2 st' c[2] i'

| IFB b THEN c[1] ELSE c[2] FI ⇒

if (beval st b)

然后 ceval_step2 st c[1] i'

else ceval_step2 st c[2] i'

| WHILE b[1] DO c[1] END ⇒

if (beval st b[1])

then let st' := ceval_step2 st c[1] i' in

ceval_step2 st' c i'

else st

end

end。

```

    *Note*: It is tempting to think that the index i here is
    counting the "number of steps of evaluation."  But if you look
    closely you'll see that this is not the case: for example, in the
    rule for sequencing, the same i is passed to both recursive
    calls.  Understanding the exact way that i is treated will be
    important in the proof of ceval__ceval_step, which is given as
    an exercise below.

    One thing that is not so nice about this evaluator is that we
    can't tell, from its result, whether it stopped because the
    program terminated normally or because it ran out of gas.  Our
    next version returns an option state instead of just a state,
    so that we can distinguish between normal and abnormal
    termination.

```

Fixpoint ceval_step3 (st : state) (c : com) (i : nat)

: option state :=

match i with

| O ⇒ None

| S i' ⇒

match c with

| SKIP ⇒

Some st

| l ::= a[1] ⇒

Some (t_update st l (aeval st a[1]))

| c[1] ;; c[2] ⇒

match (ceval_step3 st c[1] i') with

| Some st' ⇒ ceval_step3 st' c[2] i'

| None ⇒ None

end

| IFB b THEN c[1] ELSE c[2] FI ⇒

if (beval st b)

then ceval_step3 st c[1] i'

else ceval_step3 st c[2] i'

| WHILE b[1] DO c[1] END ⇒

if (beval st b[1])

then match (ceval_step3 st c[1] i') with

| Some st' ⇒ ceval_step3 st' c i'

| None ⇒ None

end

else Some st

end

end.

```

    We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states.

```

Notation "'LETOPT' x <== e1 'IN' e2"

:= (match e[1] with

| Some x ⇒ e[2]

| None ⇒ None

end)

(右结合性，在级别 60)。

Fixpoint ceval_step (st : state) (c : com) (i : nat)

: option state :=

match i with

| O ⇒ None

| S i' ⇒

match c with

| SKIP ⇒

Some st

| l ::= a[1] ⇒

Some (t_update st l (aeval st a[1]))

| c[1] ;; c[2] ⇒

LETOPT st' <== ceval_step st c[1] i' IN

ceval_step st' c[2] i'

| IFB b THEN c[1] ELSE c[2] FI ⇒

if (beval st b)

then ceval_step st c[1] i'

else ceval_step st c[2] i'

| WHILE b[1] DO c[1] END ⇒

if (beval st b[1])

then LETOPT st' <== ceval_step st c[1] i' IN

ceval_step st' c i'

else Some st

end

end。

定义 test_ceval (st:state) (c:com) :=

match ceval_step st c 500 with

| None    ⇒ None

| Some st ⇒ Some (st X, st Y, st Z)

end。

(* 计算 （test_ceval empty_state （X ::= ANum 2;; IFB BLe （AId X）（ANum 1） THEN Y ::= ANum 3 ELSE Z ::= ANum 4 FI））。 ===》 Some（2，0，4） *)

```

#### Exercise: 2 stars, recommended (pup_to_n)

    Write an Imp program that sums the numbers from 1 to
   X (inclusive: 1 + 2 + ... + X) in the variable Y.  Make sure
   your solution satisfies the test that follows.

```

pup_to_n 的定义：com

(* 用“:= _your_definition_.” 替换此行 *）。已证明。

(* 示例 pup_to_n_1 ： test_ceval（t_update empty_state X 5）pup_to_n = Some（0，15，0）。 证明。 reflexivity。 Qed。 *)

```

    ☐ 

#### Exercise: 2 stars, optional (peven)

    Write a While program that sets Z to 0 if X is even and
    sets Z to 1 otherwise.  Use ceval_test to test your
    program.

```

(* 在此填写 *)

```

    ☐

```

# 关系与步骤索引评估

    至于算术和布尔表达式，我们希望

    两种替代定义的评估是否实际上

    最终归结于同一件事。本节显示了这一点

    是情况。

```
Theorem ceval_step__ceval: ∀c st st',
      (∃i, ceval_step st c i = Some st') →
      c / st ⇓ st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  - (* i = 0 -- contradictory *)
    intros c st st' H. inversion H.

  - (* i = S i' *)
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      + (* SKIP *) apply E_Skip.
      + (* ::= *) apply E_Ass. reflexivity.

      + (* ;; *)
        destruct (ceval_step st c[1] i') eqn:Heqr1.
        * (* Evaluation of r[1] terminates normally *)
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H[1]. assumption.
        * (* Otherwise -- contradiction *)
          inversion H[1].

      + (* IFB *)
        destruct (beval st b) eqn:Heqr.
        * (* r = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* r = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      + (* WHILE *) destruct (beval st b) eqn :Heqr.
        * (* r = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* r[1] = Some s *)
           apply E_WhileLoop with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. simpl in H[1]. assumption. }
         { (* r[1] = None *) inversion H[1]. }
        * (* r = false *)
          inversion H[1].
          apply E_WhileEnd.
          rewrite ← Heqr. subst. reflexivity. Qed.

```

#### 练习：4 星（ceval_step__ceval_inf）

    按照非正式证明 ceval_step__ceval 的方式写出证明

    常规模板。（关于对归纳的情况分析的模板

    定义的值看起来应该与归纳相同，只是

    没有归纳假设。）确保你的证明清晰易懂

    主要思想传达给读者；不要简单地转录

    正式证明的步骤。

    (* 在此填写 *)

    ☐

```
Theorem ceval_step_more: ∀i[1] i[2] st st' c,
  i[1] ≤ i[2] →
  ceval_step st c i[1] = Some st' →
  ceval_step st c i[2] = Some st'.
Proof.
induction i[1] as [|i[1]']; intros i[2] st st' c Hle Hceval.
  - (* i[1] = 0 *)
    simpl in Hceval. inversion Hceval.
  - (* i[1] = S i[1]' *)
    destruct i[2] as [|i[2]']. inversion Hle.
    assert (Hle': i[1]' ≤ i[2]') by omega.
    destruct c.
    + (* SKIP *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ::= *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ;; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c[1] i[1]') eqn:Heqst1'o.
      * (* st[1]'o = Some *)
        apply (IHi1' i[2]') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i[2]') in Hceval; try assumption.
      * (* st[1]'o = None *)
        inversion Hceval.

    + (* IFB *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i[2]') in Hceval;
        assumption.

    + (* WHILE *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i[1]') eqn: Heqst1'o.
      * (* st[1]'o = Some *)
        apply (IHi1' i[2]') in Heqst1'o; try assumption.
        rewrite → Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i[2]') in Hceval; try assumption.
      * (* i[1]'o = None *)
        simpl in Hceval. inversion Hceval. Qed.

```

#### 练习：3 星，建议（ceval__ceval_step）

    完成下面的证明。 你将需要在几个地方使用 ceval_step_more

    一些基本事实，以及一些关于 ≤ 和 plus 的基本事实。

```
Theorem ceval__ceval_step: ∀c st st',
      c / st ⇓ st' →
      ∃i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  (* FILL IN HERE *) Admitted.

```

    ☐

```
Theorem ceval_and_ceval_step_coincide: ∀c st st',
      c / st ⇓ st'
  ↔ ∃i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

```

# 再次评估的确定性

    利用关系和步数索引定义的事实

    评估相同，我们可以给出一个更简洁的证明

    评估 *关系* 是确定性的。

```
Theorem ceval_deterministic' : ∀c st st[1] st[2],
     c / st ⇓ st[1]  →
     c / st ⇓ st[2] →
     st[1] = st[2].
Proof.
  intros c st st[1] st[2] He[1] He[2].
  apply ceval__ceval_step in He[1].
  apply ceval__ceval_step in He[2].
  inversion He[1] as [i[1] E[1]].
  inversion He[2] as [i[2] E[2]].
  apply ceval_step_more with (i[2] := i[1] + i[2]) in E[1].
  apply ceval_step_more with (i[2] := i[1] + i[2]) in E[2].
  rewrite E[1] in E[2]. inversion E[2]. reflexivity.
  omega. omega. Qed.

```

```

```

```

```
