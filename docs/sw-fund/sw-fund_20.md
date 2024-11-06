# HoareAsLogicHoare 逻辑作为逻辑

```

    The presentation of Hoare logic in chapter Hoare could be
    described as "model-theoretic": the proof rules for each of the
    constructors were presented as *theorems* about the evaluation
    behavior of programs, and proofs of program correctness (validity
    of Hoare triples) were constructed by combining these theorems
    directly in Coq.

    Another way of presenting Hoare logic is to define a completely
    separate proof system — a set of axioms and inference rules that
    talk about commands, Hoare triples, etc. — and then say that a
    proof of a Hoare triple is a valid derivation in *that* logic.  We
    can do this by giving an inductive definition of *valid derivations* in this new logic.

    This chapter is optional.  Before reading it, you'll want to read
    the ProofObjects chapter.

```

需要导入 Imp。

导入 Hoare。

```

# Definitions

```

Inductive hoare_proof：断言→ com → 断言→ 类型 :=

| H_Skip : ∀P，

hoare_proof P（SKIP）P

| H_Asgn : ∀Q V a，

hoare_proof（assn_sub V a Q）（V :: = a）Q

| H_Seq  : ∀P c Q d R，

hoare_proof P c Q → hoare_proof Q d R → hoare_proof P（c;;d）R

| H_If：∀P Q b c[1] c[2]，

hoare_proof（fun st ⇒ P st ∧ bassn b st）c[1] Q →

hoare_proof（fun st ⇒ P st ∧ ~（bassn b st））c[2] Q →

hoare_proof P（如果 b THEN c[1] ELSE c[2] FI）Q

| H_While：∀P b c，

hoare_proof（fun st ⇒ P st ∧ bassn b st）c P →

hoare_proof P（WHILE b DO c END）（fun st ⇒ P st ∧ ¬（bassn b st））

| H_Consequence  : ∀（P Q P' Q'：断言）c，

hoare_proof P' c Q' →

（∀st，P st → P' st）→

（∀st，Q' st → Q st）→

hoare_proof P c Q。

```

    We don't need to include axioms corresponding to
    hoare_consequence_pre or hoare_consequence_post, because 
    these can be proven easily from H_Consequence.

```

引理 H_Consequence_pre: ∀（P Q P'：断言）c，

hoare_proof P' c Q →

（∀st，P st → P' st）→

hoare_proof P c Q。

    证明。

介绍。采用 H_Consequence。

应用 X。应用 H。介绍。应用 H[0]。证明结束。

引理 H_Consequence_post  : ∀（P Q Q'：断言）c，

hoare_proof P c Q' →

（∀st，Q' st → Q st）→

hoare_proof P c Q。

    证明。

介绍。采用 H_Consequence。

应用 X。介绍。应用 H[0]。应用 H。证明结束。

```

    As an example, let's construct a proof object representing a
    derivation for the hoare triple

```

{{assn_sub X (X+1) (assn_sub X (X+2) (X=3))}}

X::=X+1 ;; X::=X+2

{{X=3}}。

    我们可以使用 Coq 的策略来帮助我们构造证明对象。

```
Example sample_proof :
  hoare_proof
    (assn_sub X (APlus (AId X) (ANum 1))
              (assn_sub X (APlus (AId X) (ANum 2))
                        (fun st ⇒ st X = 3) ))
    (X ::= APlus (AId X) (ANum 1);; (X ::= APlus (AId X) (ANum 2)))
    (fun st ⇒ st X = 3).
Proof.
  eapply H_Seq; apply H_Asgn.
Qed.

(* Print sample_proof. ====>   H_Seq     (assn_sub X (APlus (AId X) (ANum 1))        (assn_sub X (APlus (AId X) (ANum 2))                 (fun st : state => st X = VNat 3)))     (X ::= APlus (AId X) (ANum 1))     (assn_sub X (APlus (AId X) (ANum 2))                (fun st : state => st X = VNat 3))     (X ::= APlus (AId X) (ANum 2))        (fun st : state => st X = VNat 3)     (H_Asgn        (assn_sub X (APlus (AId X) (ANum 2))                     (fun st : state => st X = VNat 3))        X (APlus (AId X) (ANum 1)))     (H_Asgn (fun st : state => st X = VNat 3) X              (APlus (AId X) (ANum 2))) *)

```

# 属性

#### 练习：2 星（hoare_proof_sound）

    证明这样的证明对象代表真实的断言。

```
Theorem hoare_proof_sound : ∀P c Q,
  hoare_proof P c Q → {{P}} c {{Q}}.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    我们还可以使用 Coq 的推理工具来证明元定理

    关于 Hoare 逻辑。例如，这是两个的类比

    我们在第 Hoare 章节中看到的定理 —— 这次用术语来表达

    语法的 Hoare 逻辑推导（可证性）而不是

    直接基于 Hoare 三元组的语义。

    第一个说，对于每个 P 和 c，断言

    {{P}} c {{True}} 在 Hoare 逻辑中是 *可证明的*。注意

    证明比 Hoare 中的语义证明更复杂：我们

    实际上需要对结构进行归纳

    命令 c。

```
Theorem H_Post_True_deriv:
  ∀c P, hoare_proof P c (fun _ ⇒ True).
Proof.
  intro c.
  induction c; intro P.
  - (* SKIP *)
    eapply H_Consequence.
    apply H_Skip.
    intros. apply H.
    (* Proof of True *)
    intros. apply I.
  - (* ::= *)
    eapply H_Consequence_pre.
    apply H_Asgn.
    intros. apply I.
  - (* ;; *)
    eapply H_Consequence_pre.
    eapply H_Seq.
    apply (IHc1 (fun _ ⇒ True)).
    apply IHc2.
    intros. apply I.
  - (* IFB *)
    apply H_Consequence_pre with (fun _ ⇒ True).
    apply H_If.
    apply IHc1.
    apply IHc2.
    intros. apply I.
  - (* WHILE *)
    eapply H_Consequence.
    eapply H_While.
    eapply IHc.
    intros; apply I.
    intros; apply I.
Qed.

```

    同样，我们可以证明对于{{False}} c {{Q}} 是可证明的

    任何 c 和 Q。

```
Lemma False_and_P_imp: ∀P Q,
  False ∧ P → Q.
Proof.
  intros P Q [CONTRA HP].
  destruct CONTRA.
Qed.

Tactic Notation "pre_false_helper" constr(CONSTR) :=
  eapply H_Consequence_pre;
    [eapply CONSTR | intros ? CONTRA; destruct CONTRA].

Theorem H_Pre_False_deriv:
  ∀c Q, hoare_proof (fun _ ⇒ False) c Q.
Proof.
  intros c.
  induction c; intro Q.
  - (* SKIP *) pre_false_helper H_Skip.
  - (* ::= *) pre_false_helper H_Asgn.
  - (* ;; *) pre_false_helper H_Seq. apply IHc1. apply IHc2.
  - (* IFB *)
    apply H_If; eapply H_Consequence_pre.
    apply IHc1. intro. eapply False_and_P_imp.
    apply IHc2. intro. eapply False_and_P_imp.
  - (* WHILE *)
    eapply H_Consequence_post.
    eapply H_While.
    eapply H_Consequence_pre.
      apply IHc.
      intro. eapply False_and_P_imp.
    intro. simpl. eapply False_and_P_imp.
Qed.

```

    作为最后一步，我们可以展示 hoare_proof 公理集

    足以证明关于（部分）正确性的任何真实事实。

    更确切地说，我们可以证明的任何语义 Hoare 三元组都可以

    也可以从这些公理中证明出来。这样一组公理被称为

    是*相对完备*。我们的证明受到这个的启发：

    [http://www.ps.uni-saarland.de/courses/sem-ws[11]/script/Hoare.html](http://www.ps.uni-saarland.de/courses/sem-ws<sub>11</sub>/script/Hoare.html)

    为了进行证明，我们需要想出一些中间值

    使用一个称为 *最弱前置条件* 的技术装置来断言。给定一个命令 c 和一个期望的后置条件

    断言 Q，最弱前置条件 wp c Q 是一个断言

    P 这样的{{P}} c {{Q}}保持，而且，对于任何其他

    断言 P'，如果 {{P'}} c {{Q}} 成立，则 P' → P。我们可以

    更直接地定义如下：

```
Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s ⇒ ∀s', c / s ⇓ s' → Q s'.

```

#### 练习：1 星（wp_is_precondition）

```
Lemma wp_is_precondition: ∀c Q,
  {{wp c Q}} c {{Q}}.
(* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：1 星（wp_is_weakest）

```
Lemma wp_is_weakest: ∀c Q P',
   {{P'}} c {{Q}} → ∀st, P' st → wp c Q st.
(* FILL IN HERE *) Admitted.

```

    以下的实用引理也会很有用。

```
Lemma bassn_eval_false : ∀b st, ¬ bassn b st → beval st b = false.
Proof.
  intros b st H. unfold bassn in H. destruct (beval st b).
    exfalso. apply H. reflexivity.
    reflexivity.
Qed.

```

    ☐

#### 练习：5 星（hoare_proof_complete）

    完成定理的证明。

```
Theorem hoare_proof_complete: ∀P c Q,
  {{P}} c {{Q}} → hoare_proof P c Q.
Proof.
  intros P c. generalize dependent P.
  induction c; intros P Q HT.
  - (* SKIP *)
    eapply H_Consequence.
     eapply H_Skip.
      intros. eassumption.
      intro st. apply HT. apply E_Skip.
  - (* ::= *)
    eapply H_Consequence.
      eapply H_Asgn.
      intro st. apply HT. econstructor. reflexivity.
      intros; assumption.
  - (* ;; *)
    apply H_Seq with (wp c[2] Q).
     eapply IHc1.
       intros st st' E[1] H. unfold wp. intros st'' E[2].
         eapply HT. econstructor; eassumption. assumption.
     eapply IHc2. intros st st' E[1] H. apply H; assumption.
  (* FILL IN HERE *) Admitted.

```

    ☐

    最后，我们可能希望我们的公理化的 Hoare 逻辑是

    *可判定*的角度来看，存在一个（终止的）算法（一个

    *决策过程*)，可以确定给定的

    Hoare 三元组是有效的（可推导的）。但这样的决策过程

    无法存在！

    考虑三元组{{True}} c {{False}}。这个三元组是有效的

    当且仅当 c 是非终止的。所以任何算法

    可以确定任意三元组的有效性可以解决

    停机问题。

    同样，三元组{{True} SKIP {{P}}是有效的当且仅当

    ∀ s，P s 是有效的，其中 P 是任意断言

    Coq 的逻辑。但已知不能有决策

    这种逻辑的过程。

    总的来说，这种公理化的展示风格更清晰

    是什么意思“在 Hoare 逻辑中给出证明”。

    然而，从

    在实践中写下这样的证明：非常冗长。这

    章节 Hoare2 上关于形式化装饰程序

    展示了我们如何做得更好。

```

```
