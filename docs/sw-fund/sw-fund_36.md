# 部分求值

```

```

(* 由 Chung-chieh Shan 撰写和维护的章节 *)

```

    The Equiv chapter introduced constant folding as an example of a
    program transformation and proved that it preserves the meaning of
    programs.  Constant folding operates on manifest constants such as
    ANum expressions.  For example, it simplifies the command Y ::= APlus (ANum 3) (ANum 1) to the command Y ::= ANum 4.  However,
    it does not propagate known constants along data flow.  For
    example, it does not simplify the sequence

```

X ::= ANum 3;; Y ::= APlus (AId X) (ANum 1)

    to

```
      X ::= ANum 3;; Y ::= ANum 4

    because it forgets that X is 3 by the time it gets to Y.

    We might naturally want to enhance constant folding so that it
    propagates known constants and uses them to simplify programs.
    Doing so constitutes a rudimentary form of *partial evaluation*.
    As we will see, partial evaluation is so called because it is like
    running a program, except only part of the program can be
    evaluated because only part of the input to the program is known.
    For example, we can only simplify the program

```

X ::= ANum 3;; Y ::= AMinus (APlus (AId X) (ANum 1)) (AId Y)

    to

```
      X ::= ANum 3;; Y ::= AMinus (ANum 4) (AId Y)

    without knowing the initial value of Y.

```

需要导入 Coq.Bool.Bool。

需要导入 Coq.Arith.Arith。

需要导入 Coq.Arith.EqNat。

需要导入 Coq.omega.Omega。

需要导入 Coq.Logic.FunctionalExtensionality。

需要导入 Coq.Lists.List。

导入 ListNotations。

需要导入 Maps。

需要导入 Imp。

需要导入 Smallstep。

```

# Generalizing Constant Folding

    The starting point of partial evaluation is to represent our
    partial knowledge about the state.  For example, between the two
    assignments above, the partial evaluator may know only that X is
    3 and nothing about any other variable. 

## Partial States

    Conceptually speaking, we can think of such partial states as the
    type id → option nat (as opposed to the type id → nat of
    concrete, full states).  However, in addition to looking up and
    updating the values of individual variables in a partial state, we
    may also want to compare two partial states to see if and where
    they differ, to handle conditional control flow.  It is not possible
    to compare two arbitrary functions in this way, so we represent
    partial states in a more concrete format: as a list of id * nat
    pairs.

```

定义 pe_state := list (id * nat)。

```

    The idea is that a variable id appears in the list if and only
    if we know its current nat value.  The pe_lookup function thus
    interprets this concrete representation.  (If the same variable
    id appears multiple times in the list, the first occurrence
    wins, but we will define our partial evaluator to never construct
    such a pe_state.)

```

定义 pe_lookup 函数（pe_st:pe_state）(V:id) : option nat :=

匹配 pe_st 结果

| [] ⇒ None

| (V',n')::pe_st ⇒ 如果 beq_id V V' 则返回 Some n'

否则 pe_lookup pe_st V

结束。

```

    For example, empty_pe_state represents complete ignorance about
    every variable — the function that maps every id to None.

```

定义空的 pe_state：empty_pe_state := []。

```

    More generally, if the list representing a pe_state does not
    contain some id, then that pe_state must map that id to
    None.  Before we prove this fact, we first define a useful
    tactic for reasoning with id equality.  The tactic

```

比较 V 和 V'

    意味着通过 beq_id V V' 对 V V' 进行情况推理。

    在 V = V' 的情况下，策略

    用 V 替换 V'。

```
Tactic Notation "compare" ident(i) ident(j) :=
  let H := fresh "Heq" i j in
  destruct (beq_idP i j);
  [ subst j | ].

Theorem pe_domain: ∀pe_st V n,
  pe_lookup pe_st V = Some n →
  In V (map (@fst _ _) pe_st).
Proof. intros pe_st V n H. induction pe_st as [| [V' n'] pe_st].
  - (*  *) inversion H.
  - (* :: *) simpl in H. simpl. compare V V'; auto. Qed. 
```

    在接下来的内容中，我们将大量使用来自

    标准库中也定义在 Logic.v 中：

```
Print In.
(* ===> Fixpoint In {A:Type} (a: A) (l:list A) : Prop :=            match l with            |  => False            | b :: m => b = a \/ In a m             end         : forall A : Type, A -> list A -> Prop *) 
```

    除了我们已经知道的关于 In 的各种引理

    跨越，下一个（取自标准库）将

    也会很有用：

```
Check filter_In.
(* ===> filter_In : forall (A : Type) (f : A -> bool) (x : A) (l : list A),             In x (filter f l) <-> In x l /\ f x = true  *)

```

    如果类型 A 有一个用于测试其相等性的操作符 beq

    元素，我们可以计算一个布尔值 inb beq a l 用于测试

    是否 In a l 成立或不成立。

```
Fixpoint inb {A : Type} (beq : A → A → bool) (a : A) (l : list A) :=
  match l with
  | [] ⇒ false
  | a'::l' ⇒ beq a a' || inb beq a l'
  end.

```

    将 inb 与 In 关联起来很容易，使用 reflect 属性：

```
Lemma inbP : ∀A : Type, ∀beq : A→A→bool,
  (∀a[1] a[2], reflect (a[1] = a[2]) (beq a[1] a[2])) →
  ∀a l, reflect (In a l) (inb beq a l).
Proof.
  intros A beq beqP a l.
  induction l as [|a' l' IH].
  - constructor. intros [].
  - simpl. destruct (beqP a a').
    + subst. constructor. left. reflexivity.
    + simpl. destruct IH; constructor.
      * right. trivial.
      * intros [H[1] | H[2]]; congruence.
Qed.

```

## 算术表达式

    算术表达式的部分求值很简单 — 基本上是

    与常量折叠相同，fold_constants_aexp，只是

    有时部分状态告诉我们一个

    变量，我们可以用一个常量表达式替换它。

```
Fixpoint pe_aexp (pe_st : pe_state) (a : aexp) : aexp :=
  match a with
  | ANum n ⇒ ANum n
  | AId i ⇒ match pe_lookup pe_st i with (* <----- NEW *)
             | Some n ⇒ ANum n
             | None ⇒ AId i
             end
  | APlus a[1] a[2] ⇒
      match (pe_aexp pe_st a[1], pe_aexp pe_st a[2]) with
      | (ANum n[1], ANum n[2]) ⇒ ANum (n[1] + n[2])
      | (a[1]', a[2]') ⇒ APlus a[1]' a[2]'
      end
  | AMinus a[1] a[2] ⇒
      match (pe_aexp pe_st a[1], pe_aexp pe_st a[2]) with
      | (ANum n[1], ANum n[2]) ⇒ ANum (n[1] - n[2])
      | (a[1]', a[2]') ⇒ AMinus a[1]' a[2]'
      end
  | AMult a[1] a[2] ⇒
      match (pe_aexp pe_st a[1], pe_aexp pe_st a[2]) with
      | (ANum n[1], ANum n[2]) ⇒ ANum (n[1] * n[2])
      | (a[1]', a[2]') ⇒ AMult a[1]' a[2]'
      end
  end.

```

    这个部分求值器折叠常量但不应用

    加法的结合性。

```
Example test_pe_aexp1:
  pe_aexp [(X,3)] (APlus (APlus (AId X) (ANum 1)) (AId Y))
  = APlus (ANum 4) (AId Y).

    Proof. reflexivity. Qed.

Example text_pe_aexp2:
  pe_aexp [(Y,3)] (APlus (APlus (AId X) (ANum 1)) (AId Y))
  = APlus (APlus (AId X) (ANum 1)) (ANum 3).

    Proof. reflexivity. Qed.

```

    现在，pe_aexp 是正确的意义上？合理的

    定义 pe_aexp 的正确性如下：每当一个完整的

    状态 st:state 是与部分状态一致的

    pe_st:pe_state（换句话说，pe_st 中的每个变量

    通过 st 分配一个值，st 中相同的值被赋予。

    a 并在 st 中评估 pe_aexp pe_st a 得到相同的

    结果。这个陈述确实是正确的。

```
Definition pe_consistent (st:state) (pe_st:pe_state) :=
  ∀V n, Some n = pe_lookup pe_st V → st V = n.

Theorem pe_aexp_correct_weak: ∀st pe_st, pe_consistent st pe_st →
  ∀a, aeval st a = aeval st (pe_aexp pe_st a).
Proof. unfold pe_consistent. intros st pe_st H a.
  induction a; simpl;
    try reflexivity;
    try (destruct (pe_aexp pe_st a[1]);
         destruct (pe_aexp pe_st a[2]);
         rewrite IHa1; rewrite IHa2; reflexivity).
  (* Compared to fold_constants_aexp_sound,      the only interesting case is AId *)
  - (* AId *)
    remember (pe_lookup pe_st i) as l. destruct l.
    + (* Some *) rewrite H with (n:=n) by apply Heql. reflexivity.
    + (* None *) reflexivity.
Qed.

```

    然而，我们很快会希望我们的部分求值器去除

    赋值。例如，它将简化

```
    X ::= ANum 3;; Y ::= AMinus (AId X) (AId Y);; X ::= ANum 4

    to just

```

Y ::= AMinus (ANum 3) (AId Y);; X ::= ANum 4

    通过延迟对 X 的赋值直到最后。为了实现

    这种简化，我们需要部分求值的结果

```
    pe_aexp [(X,3)] (AMinus (AId X) (AId Y))

    to be equal to AMinus (ANum 3) (AId Y) and *not* the original
    expression AMinus (AId X) (AId Y).  After all, it would be
    incorrect, not just inefficient, to transform

```

X ::= ANum 3;; Y ::= AMinus (AId X) (AId Y);; X ::= ANum 4

    to

```
    Y ::= AMinus (AId X) (AId Y);; X ::= ANum 4

    even though the output expressions AMinus (ANum 3) (AId Y) and
    AMinus (AId X) (AId Y) both satisfy the correctness criterion
    that we just proved.  Indeed, if we were to just define pe_aexp pe_st a = a then the theorem pe_aexp_correct' would already
    trivially hold.

    Instead, we want to prove that the pe_aexp is correct in a
    stronger sense: evaluating the expression produced by partial
    evaluation (aeval st (pe_aexp pe_st a)) must not depend on those
    parts of the full state st that are already specified in the
    partial state pe_st.  To be more precise, let us define a
    function pe_override, which updates st with the contents of
    pe_st.  In other words, pe_override carries out the
    assignments listed in pe_st on top of st.

```

定义 pe_update 函数 (st:state) (pe_st:pe_state) : state :=

匹配 pe_st 结果

| [] ⇒ st

| (V,n)::pe_st ⇒ t_update (pe_update st pe_st) V n

结束。

示例 test_pe_update:

pe_update (t_update empty_state Y 1) [(X,3);(Z,2)]

= t_update (t_update (t_update empty_state Y 1) Z 2) X 3.

    证明。反射性。Qed.

```

    Although pe_update operates on a concrete list representing
    a pe_state, its behavior is defined entirely by the pe_lookup
    interpretation of the pe_state.

```

定理 pe_update_correct: ∀st pe_st V[0],

pe_update st pe_st V[0] =

匹配 pe_lookup pe_st V[0] 结果

| 一些 n ⇒ n

| None ⇒ st V[0]

结束。

证明。intros。对 pe_st 进行归纳。reflexivity。

在 *. 中简化。展开 t_update。

比较 V[0] V;自动。重写 ← beq_id_refl;自动。重写 false_beq_id;自动。Qed。

```

    We can relate pe_consistent to pe_update in two ways.
    First, overriding a state with a partial state always gives a
    state that is consistent with the partial state.  Second, if a
    state is already consistent with a partial state, then overriding
    the state with the partial state gives the same state.

```

定理 pe_update_consistent: ∀st pe_st，

pe_consistent (pe_update st pe_st) pe_st。

证明。引入 st pe_st V n H。重写 pe_update_correct。

破坏（pe_lookup pe_st V）;反演 H。一致性。Qed。

定理 pe_consistent_update: ∀st pe_st，

pe_consistent st pe_st → ∀V, st V = pe_update st pe_st V。

证明。引入 st pe_st H V。重写 pe_update_correct。

记住（pe_lookup pe_st V）作为 l。破坏 l;自动。Qed。

```

    Now we can state and prove that pe_aexp is correct in the
    stronger sense that will help us define the rest of the partial
    evaluator.

    Intuitively, running a program using partial evaluation is a
    two-stage process.  In the first, *static* stage, we partially
    evaluate the given program with respect to some partial state to
    get a *residual* program.  In the second, *dynamic* stage, we
    evaluate the residual program with respect to the rest of the
    state.  This dynamic state provides values for those variables
    that are unknown in the static (partial) state.  Thus, the
    residual program should be equivalent to *prepending* the
    assignments listed in the partial state to the original program.

```

定理 pe_aexp_correct: ∀(pe_st:pe_state) (a:aexp) (st:state),

aeval（pe_update st pe_st）a = aeval st（pe_aexp pe_st a）。

证明。

引入 pe_st a st。

归纳 a;简化;

尝试一致性;

尝试（破坏（pe_aexp pe_st a[1]）;

破坏（pe_aexp pe_st a[2]）;

重写 IHa1;重写 IHa2;一致性）。

（与 fold_constants_aexp_sound 相比，唯一有趣的情况是 AId。）

重写 pe_update_correct。破坏（pe_lookup pe_st i）;一致性。

Qed。

```

## Boolean Expressions

    The partial evaluation of boolean expressions is similar.  In
    fact, it is entirely analogous to the constant folding of boolean
    expressions, because our language has no boolean variables.

```

Fixpoint pe_bexp (pe_st : pe_state) (b : bexp) : bexp :=

匹配 b 与

| BTrue        ⇒ BTrue

| BFalse       ⇒ BFalse

| BEq a[1] a[2] ⇒

匹配（pe_aexp pe_st a[1]，pe_aexp pe_st a[2]）与

| (ANum n[1], ANum n[2]) ⇒ if beq_nat n[1] n[2] then BTrue else BFalse

| (a[1]', a[2]') ⇒ BEq a[1]' a[2]'

结束

| BLe a[1] a[2] ⇒

匹配（pe_aexp pe_st a[1]，pe_aexp pe_st a[2]）与

| (ANum n[1], ANum n[2]) ⇒ if leb n[1] n[2] then BTrue else BFalse

| (a[1]', a[2]') ⇒ BLe a[1]' a[2]'

结束

| BNot b[1] ⇒

匹配（pe_bexp pe_st b[1]）与

| BTrue ⇒ BFalse

| BFalse ⇒ BTrue

| b[1]' ⇒ BNot b[1]'

结束

| BAnd b[1] b[2] ⇒

匹配（pe_bexp pe_st b[1]，pe_bexp pe_st b[2]）与

| (BTrue, BTrue) ⇒ BTrue

| (BTrue, BFalse) ⇒ BFalse

| (BFalse, BTrue) ⇒ BFalse

| (BFalse, BFalse) ⇒ BFalse

| (b[1]', b[2]') ⇒ BAnd b[1]' b[2]'

结束

结束。

示例 test_pe_bexp1:

pe_bexp [(X,3)] (BNot (BLe (AId X) (ANum 3)))

= BFalse。

    证明。一致性。Qed。

示例 test_pe_bexp2: ∀b，

b = BNot (BLe (AId X) (APlus (AId X) (ANum 1))) →

pe_bexp [] b = b。

证明。引入 b H。重写 → H。一致性。Qed。

```

    The correctness of pe_bexp is analogous to the correctness of
    pe_aexp above.

```

定理 pe_bexp_correct: ∀(pe_st:pe_state) (b:bexp) (st:state),

beval（pe_update st pe_st）b = beval st（pe_bexp pe_st b）。

证明。

引入 pe_st b st。

归纳 b;简化;

尝试一致性;

尝试（记住（pe_aexp pe_st a）作为 a';

记住（pe_aexp pe_st a[0]）作为 a[0]';

断言（Ha：aeval（pe_update st pe_st）a = aeval st a'）;

断言（Ha[0]：aeval（pe_update st pe_st）a[0] = aeval st a[0]'）;

尝试（替换;应用 pe_aexp_correct）;

破坏 a';破坏 a[0]';重写 Ha;重写 Ha[0];

简化;尝试破坏（beq_nat n n[0]）;

尝试破坏（leb n n[0]）;一致性）;

尝试（破坏（pe_bexp pe_st b）;重写 IHb;一致性）;

尝试（破坏（pe_bexp pe_st b[1]）;

破坏（pe_bexp pe_st b[2]）;

重写 IHb1;重写 IHb2;一致性）。

Qed。

```

# Partial Evaluation of Commands, Without Loops

    What about the partial evaluation of commands?  The analogy
    between partial evaluation and full evaluation continues: Just as
    full evaluation of a command turns an initial state into a final
    state, partial evaluation of a command turns an initial partial
    state into a final partial state.  The difference is that, because
    the state is partial, some parts of the command may not be
    executable at the static stage.  Therefore, just as pe_aexp
    returns a residual aexp and pe_bexp returns a residual bexp
    above, partially evaluating a command yields a residual command.

    Another way in which our partial evaluator is similar to a full
    evaluator is that it does not terminate on all commands.  It is
    not hard to build a partial evaluator that terminates on all
    commands; what is hard is building a partial evaluator that
    terminates on all commands yet automatically performs desired
    optimizations such as unrolling loops.  Often a partial evaluator
    can be coaxed into terminating more often and performing more
    optimizations by writing the source program differently so that
    the separation between static and dynamic information becomes more
    apparent.  Such coaxing is the art of *binding-time improvement*.
    The binding time of a variable tells when its value is known —
    either "static", or "dynamic."

    Anyway, for now we will just live with the fact that our partial
    evaluator is not a total function from the source command and the
    initial partial state to the residual command and the final
    partial state.  To model this non-termination, just as with the
    full evaluation of commands, we use an inductively defined
    relation.  We write

```

c[1] / st ⇓ c[1]' / st'

    意味着部分地评估源命令 c[1] 在

    初始部分状态 st 产生剩余命令 c[1]' 和

    最终部分状态 st'。例如，我们想要类似于

```
      (X ::= ANum 3 ;; Y ::= AMult (AId Z) (APlus (AId X) (AId X)))
      / [] ⇓ (Y ::= AMult (AId Z) (ANum 6)) / [(X,3)]

    to hold.  The assignment to X appears in the final partial state,
    not the residual command. 

## Assignment

    Let's start by considering how to partially evaluate an
    assignment.  The two assignments in the source program above needs
    to be treated differently.  The first assignment X ::= ANum 3,
    is *static*: its right-hand-side is a constant (more generally,
    simplifies to a constant), so we should update our partial state
    at X to 3 and produce no residual code.  (Actually, we produce
    a residual SKIP.)  The second assignment Y ::= AMult (AId Z) (APlus (AId X) (AId X)) is *dynamic*: its right-hand-side does
    not simplify to a constant, so we should leave it in the residual
    code and remove Y, if present, from our partial state.  To
    implement these two cases, we define the functions pe_add and
    pe_remove.  Like pe_update above, these functions operate on
    a concrete list representing a pe_state, but the theorems
    pe_add_correct and pe_remove_correct specify their behavior by
    the pe_lookup interpretation of the pe_state.

```

定理 pe_add_correct: ∀pe_st V n V[0],

匹配 pe_st，结束。

| [] ⇒ []

证明。intros pe_st V V[0]. 对 pe_st 进行归纳，作为 [| [V' n'] pe_st]。

简化代码。在 ELSE 分支上，我们仍然不知道

| (V',n')::pe_st ⇒ 若 beq_id V V' 则 pe_remove pe_st V

证明。intros st pe_st V n. 应用 functional_extensionality。intros V[0]。

否则 (V',n') :: pe_remove pe_st V

+ (* 相等 *) 重写 IHpe_st。

* (* 相等 *) 重写 false_beq_id; 自动。

重写 false_beq_id; 自动。

t_update (pe_update st pe_st) V n =

递归 pe_remove (pe_st:pe_state) (V:id) : pe_state :=

destruct (beq_idP V V[0]). 返回。

ELSE SKIP FI

定理 pe_update_update_remove: ∀st pe_st V n，

pe_update st (pe_add pe_st V n).

完成。

- (* 相等 *) 重写 ← beq_id_refl; 自动。

定义 pe_add (pe_st:pe_state) (V:id) (n:[nat](http://coq.inria.fr/library/Coq.Init.Datatypes.html#nat)) : pe_state :=

pe_lookup (pe_remove pe_st V) V[0]

- (*  *) 分解 (beq_id V V[0]); 返回。

* (* 不相等 *) 重写 IHpe_st。返回。

完成。

+ (* 不相等 *) 简化。比较 V[0] V'。

静态地了解 Y 与 4 的比较，因此我们必须部分评估

重复重写 false_beq_id; 自动。

知道最终 Y 的确切值。最终的

X ::= ANum 3;;

- (* :: *) 简化。比较 V V'。

```

    We will use the two theorems below to show that our partial
    evaluator correctly deals with dynamic assignments and static
    assignments, respectively.

```

intros V[0]。展开 t_update。重写 !pe_update_correct。

t_update (pe_update st pe_st) V n =

= 若 beq_id V V[0] 则 None 否则 pe_lookup pe_st V[0]。

证明。intros st pe_st V n. 应用 functional_extensionality。

比较 V V[0]。

分解 (beq_id V V[0]); 返回。完成。

假设初始部分状态为空。我们不知道

定理 pe_update_update_add: ∀st pe_st V n,

- (* 不相等 *) 重写 pe_remove_correct。

IFB BEq (AId X) (AId Y) THEN Y ::= ANum 999 ELSE SKIP FI

完成。

展开 t_update。重写 !pe_update_correct。重写 pe_add_correct。

pe_update (t_update st V n) (pe_remove pe_st V)。

```

## Conditional

    Trickier than assignments to partially evaluate is the
    conditional, IFB b[1] THEN c[1] ELSE c[2] FI.  If b[1] simplifies to
    BTrue or BFalse then it's easy: we know which branch will be
    taken, so just take that branch.  If b[1] does not simplify to a
    constant, then we need to take both branches, and the final
    partial state may differ between the two branches!

    The following program illustrates the difficulty:

```

(V,n) :: pe_remove pe_st V。

IFB BLe (AId Y) (ANum 4) THEN

部分状态和剩余程序是什么？

定理 pe_remove_correct: ∀pe_st V V[0],

pe_lookup (pe_add pe_st V n) [V[0]](PE.html#V<sub>0</sub>)

    重写 pe_remove_correct。分解 (beq_id V V[0]); 返回。

    Y ::= ANum 4;;

    证明。intros pe_st V n V[0]。展开 pe_add。简化。

    我们知道 Y 被设置为 4，甚至可以利用这个知识来

    = 若 beq_id V [V[0]](PE.html#V<sub>0</sub>) 则 [Some](http://coq.inria.fr/library/Coq.Init.Datatypes.html#Some) n 否则 pe_lookup pe_st [V[0]](PE.html#V<sub>0</sub>)。

    外部条件的两个分支。在 THEN 分支上，

    -

    处理这样一个动态条件的一种方法是采取

    两个分支的最终部分状态的交集。在

    这个例子中，我们取 (Y,4),(X,3) 的交集和

    (X,3)，所以整体最终部分状态是 (X,3)。为了

    补偿忘记 Y 是 4，我们需要添加一个

    将 Y 赋值为 ANum 4 添加到 THEN 分支的末尾。所以，

    残余程序将会是这样的

```
      SKIP;;
      IFB BLe (AId Y) (ANum 4) THEN
          SKIP;;
          SKIP;;
          Y ::= ANum 4
      ELSE SKIP FI

    Programming this case in Coq calls for several auxiliary
    functions: we need to compute the intersection of two pe_states
    and turn their difference into sequences of assignments.

    First, we show how to compute whether two pe_states to disagree
    at a given variable.  In the theorem pe_disagree_domain, we
    prove that two pe_states can only disagree at variables that
    appear in at least one of them.

```

定义 pe_disagree_at (pe_st[1] pe_st[2] : pe_state) (V:id) : bool :=

匹配 pe_lookup pe_st[1] V, pe_lookup pe_st[2] V 与

| Some x, Some y ⇒ negb (beq_nat x y)

| None, None ⇒ false

| _, _ ⇒ true

结束。

定理 pe_disagree_domain: ∀(pe_st[1] pe_st[2] : pe_state) (V:id),

true = pe_disagree_at pe_st[1] pe_st[2] V →

在 (map (@fst _ _) pe_st[1] ++ map (@fst _ _) pe_st[2]) 中 V。

证明。展开 pe_disagree_at。引入 pe_st[1] pe_st[2] V H。

应用 in_app_iff。

记住 (pe_lookup pe_st[1] V) 为 lookup1。

将 lookup1 分解为 [n[1]|]。左。应用 pe_domain 与 n[1]。自动。

记住 (pe_lookup pe_st[2] V) 为 lookup2。

分解 lookup2 为 [n[2]|]。右。应用 pe_domain 与 n[2]。自动。

反演 H。完毕。

```

    We define the pe_compare function to list the variables where
    two given pe_states disagree.  This list is exact, according to
    the theorem pe_compare_correct: a variable appears on the list
    if and only if the two given pe_states disagree at that
    variable.  Furthermore, we use the pe_unique function to
    eliminate duplicates from the list.

```

pe_unique (l : list id) : list id :=

匹配 l 与

| [] ⇒ []

| x::l ⇒

x :: filter (fun y ⇒ if beq_id x y then false else true) (pe_unique l)

结束。

定理 pe_unique_correct: ∀l x,

在 l 中 x ↔ 在 (pe_unique l) 中 x。

证明。引入 l x。对 l 进行归纳，作为 [| h t]。反射性。

简化。分割。

- (* -> *)

引入。反演 H；清除 H。

左。假设成立。

分解 (beq_idP h x)。

左。假设成立。

右。应用 filter_In。分割。

应用 IHt。假设成立。

重写 false_beq_id；自动。

- (* <- *)

引入。反演 H；清除 H。

左。假设成立。

apply filter_In in H[0]。反演 H[0]。右。应用 IHt。假设成立。

完毕。

定义 pe_compare (pe_st[1] pe_st[2] : pe_state) : list id :=

pe_unique (filter (pe_disagree_at pe_st[1] pe_st[2])

(map (@fst _ _) pe_st[1] ++ map (@fst _ _) pe_st[2])。

定理 pe_compare_correct: ∀pe_st[1] pe_st[2] V,

pe_lookup pe_st[1] V = pe_lookup pe_st[2] V ↔

¬ 在 V 中 (pe_compare pe_st[1] pe_st[2])。

证明。引入 pe_st[1] pe_st[2] V。

展开 pe_compare。重写 ← pe_unique_correct。重写 filter_In。

分割；引入 Heq。

- (* -> *)

引入。分解 H。展开 pe_disagree_at 中的 H[0]。重写 Heq 在 H[0] 中。

分解 (pe_lookup pe_st[2] V)。

重写 ← beq_nat_refl in H[0]。反演 H[0]。

反演 H[0]。

- (* <- *)

断言 (Hagree: pe_disagree_at pe_st[1] pe_st[2] V = false)。

{ (* 断言的证明*)

记住 (pe_disagree_at pe_st[1] pe_st[2] V) 为 disagree。

匹配 disagree；[| 反射性]。

应用 pe_disagree_domain 在 Heqdisagree 中。

矛盾。应用 Heq。分割。假设成立。}

展开 pe_disagree_at 中的 Hagree。

将 (pe_lookup pe_st[1] V) 分解为 [n[1]|]；

分解 (pe_lookup pe_st[2] V) 为 [n[2]|]；

尝试反射性；尝试通过反转解决。

在 Hagree 中重写 negb_false_iff。

在 Hagree 中应用 beq_nat_true。替换。完毕。

```

    The intersection of two partial states is the result of removing
    from one of them all the variables where the two disagree.  We
    define the function pe_removes, in terms of pe_remove above,
    to perform such a removal of a whole list of variables at once.

    The theorem pe_compare_removes testifies that the pe_lookup
    interpretation of the result of this intersection operation is the
    same no matter which of the two partial states we remove the
    variables from.  Because pe_update only depends on the
    pe_lookup interpretation of partial states, pe_update also
    does not care which of the two partial states we remove the
    variables from; that theorem pe_compare_update is used in the
    correctness proof shortly.

```

pe_removes (pe_st:pe_state) (ids : list id) : pe_state :=

匹配 ids 与

| [] ⇒ pe_st

| V::ids ⇒ pe_remove (pe_removes pe_st ids) V

完毕。

定理 pe_removes_correct: ∀pe_st ids V，

pe_lookup (pe_removes pe_st ids) V =

if inb beq_id V ids then None else pe_lookup pe_st V。

证明。intros pe_st ids V。induction ids as [| V' ids]。reflexivity。

simpl。rewrite pe_remove_correct。rewrite IHids。

compare V' V。

- rewrite ← beq_id_refl. reflexivity.

- rewrite false_beq_id; try congruence。reflexivity。

Qed。

定理 pe_compare_removes: ∀pe_st[1] pe_st[2] V，

pe_lookup (pe_removes pe_st[1] (pe_compare pe_st[1] pe_st[2])) V =

pe_lookup (pe_removes pe_st[2] (pe_compare pe_st[1] pe_st[2])) V。

证明。

intros pe_st[1] pe_st[2] V。rewrite !pe_removes_correct。

destruct (inbP _ _ beq_idP V (pe_compare pe_st[1] pe_st[2])).

- reflexivity。

- apply pe_compare_correct。auto。Qed。

定理 pe_compare_update: ∀pe_st[1] pe_st[2] st，

pe_update st (pe_removes pe_st[1] (pe_compare pe_st[1] pe_st[2])) =

pe_update st (pe_removes pe_st[2] (pe_compare pe_st[1] pe_st[2]))。

证明。intros。apply functional_extensionality。intros V。

rewrite !pe_update_correct。rewrite pe_compare_removes。reflexivity。

Qed。

```

    Finally, we define an assign function to turn the difference
    between two partial states into a sequence of assignment commands.
    More precisely, assign pe_st ids generates an assignment command
    for each variable listed in ids.

```

固定 assign (pe_st : pe_state) (ids : list id) : com :=

match ids with

| [] ⇒ SKIP

| V::ids ⇒ match pe_lookup pe_st V with

| Some n ⇒ (assign pe_st ids;; V ::= ANum n)

| None ⇒ assign pe_st ids

end

end。

```

    The command generated by assign always terminates, because it is
    just a sequence of assignments.  The (total) function assigned
    below computes the effect of the command on the (dynamic state).
    The theorem assign_removes then confirms that the generated
    assignments perfectly compensate for removing the variables from
    the partial state.

```

定义 assigned (pe_st:pe_state) (ids : list id) (st:state) : state :=

fun V ⇒ if inb beq_id V ids then

match pe_lookup pe_st V with

| Some n ⇒ n

| None ⇒ st V

end

else st V。

定理 assign_removes: ∀pe_st ids st，

pe_update st pe_st =

pe_update (assigned pe_st ids st) (pe_removes pe_st ids)。

证明。intros pe_st ids st。apply functional_extensionality。intros V。

rewrite !pe_update_correct。rewrite pe_removes_correct。unfold assigned。

destruct (inbP _ _ beq_idP V ids)；destruct (pe_lookup pe_st V)；reflexivity。

Qed。

引理 ceval_extensionality: ∀c st st[1] st[2]，

c / st ⇓ st[1] → (∀V, st[1] V = st[2] V) → c / st ⇓ st[2].

证明。intros c st st[1] st[2] H Heq。

apply functional_extensionality in Heq。rewrite ← Heq。apply H。Qed。

定理 eval_assign: ∀pe_st ids st，

assign pe_st ids / st ⇓ assigned pe_st ids st。

证明。intros pe_st ids st。induction ids as [| V ids]；simpl。

- (*  *) eapply ceval_extensionality。apply E_Skip。reflexivity。

- (* V::ids *)

remember (pe_lookup pe_st V) as lookup。destruct lookup。

+ (* Some *) eapply E_Seq。apply IHids。unfold assigned。simpl。

eapply ceval_extensionality。apply E_Ass。simpl。reflexivity。

intros V[0]. unfold t_update. compare V V[0].

* (* equal *) rewrite ← Heqlookup。rewrite ← beq_id_refl。reflexivity。

* (* not equal *) rewrite false_beq_id；simpl；congruence。

+ (* None *) eapply ceval_extensionality。apply IHids。

unfold assigned。intros V[0]。simpl。compare V V[0]。

* (* equal *) rewrite ← Heqlookup。

重写 ← beq_id_refl。

destruct (inbP _ _ beq_idP V ids); 反射性。

* (* not equal *) 重写 false_beq_id；简化；恒等。

证毕。

```

## The Partial Evaluation Relation

    At long last, we can define a partial evaluator for commands
    without loops, as an inductive relation!  The inequality
    conditions in PE_AssDynamic and PE_If are just to keep the
    partial evaluator deterministic; they are not required for
    correctness.

```

保留记号 "c1 '/' st '⇓' c1' '/' st'"

(at level 40, st at level 39, c[1]' at level 39)。

归纳 pe_com : com → pe_state → com → pe_state → Prop :=

| PE_Skip : ∀pe_st,

SKIP / pe_st ⇓ SKIP / pe_st

| PE_AssStatic : ∀pe_st a[1] n[1] l,

当 pe_aexp pe_st a[1] = ANum n[1] 时 →

(l ::= a[1]) / pe_st ⇓ SKIP / pe_add pe_st l n[1]

| PE_AssDynamic : ∀pe_st a[1] a[1]' l,

当 pe_aexp pe_st a[1] = a[1]' 时 →

(∀n, a[1]' ≠ ANum n) →

(l ::= a[1]) / pe_st ⇓ (l ::= a[1]') / pe_remove pe_st l

| PE_Seq : ∀pe_st pe_st' pe_st'' c[1] c[2] c[1]' c[2]',

c[1] / pe_st  ⇓ c[1]' / pe_st' →

c[2] / pe_st' ⇓ c[2]' / pe_st'' →

(c[1] ;; c[2]) / pe_st ⇓ (c[1]' ;; c[2]') / pe_st''

| PE_IfTrue : ∀pe_st pe_st' b[1] c[1] c[2] c[1]',

当 pe_bexp pe_st b[1] = BTrue 时 →

c[1] / pe_st ⇓ c[1]' / pe_st' →

(IFB b[1] THEN c[1] ELSE c[2] FI) / pe_st ⇓ c[1]' / pe_st'

| PE_IfFalse : ∀pe_st pe_st' b[1] c[1] c[2] c[2]',

当 pe_bexp pe_st b[1] = BFalse 时 →

c[2] / pe_st ⇓ c[2]' / pe_st' →

(IFB b[1] THEN c[1] ELSE c[2] FI) / pe_st ⇓ c[2]' / pe_st'

| PE_If : ∀pe_st pe_st[1] pe_st[2] b[1] c[1] c[2] c[1]' c[2]',

当 pe_bexp pe_st b[1] ≠ BTrue 时 →

当 pe_bexp pe_st b[1] ≠ BFalse 时 →

c[1] / pe_st ⇓ c[1]' / pe_st[1] →

c[2] / pe_st ⇓ c[2]' / pe_st[2] →

(IFB b[1] THEN c[1] ELSE c[2] FI) / pe_st

⇓ (IFB pe_bexp pe_st b[1]

然后 c[1]' ;; assign pe_st[1] (pe_compare pe_st[1] pe_st[2])

否则 c[2]' ;; assign pe_st[2] (pe_compare pe_st[1] pe_st[2]) FI)

/ pe_removes pe_st[1] (pe_compare pe_st[1] pe_st[2])

其中 "c1 '/' st '⇓' c1' '/' st'" := (pe_com c[1] st c[1]' st')。

Hint 构造函数 pe_com。

Hint 构造函数 ceval。

```

## Examples

    Below are some examples of using the partial evaluator.  To make
    the pe_com relation actually usable for automatic partial
    evaluation, we would need to define more automation tactics in
    Coq.  That is not hard to do, but it is not needed here.

```

示例 pe_example1：

(X ::= ANum 3 ;; Y ::= AMult (AId Z) (APlus (AId X) (AId X)))

/ [] ⇓ (SKIP;; Y ::= AMult (AId Z) (ANum 6)) / [(X,3)]。

证明。使用 eapply PE_Seq。使用 eapply PE_AssStatic。反射性。

使用 eapply PE_AssDynamic。反射性。intros n H。反演 H。证毕。

示例 pe_example2：

(X ::= ANum 3 ;; IFB BLe (AId X) (ANum 4) THEN X ::= ANum 4 ELSE SKIP FI)

/ [] ⇓ (SKIP;; SKIP) / [(X,4)]。

证明。使用 eapply PE_Seq。使用 eapply PE_AssStatic。反射性。

使用 eapply PE_IfTrue。反射性。

使用 eapply PE_AssStatic。反射性。证毕。

示例 pe_example3：

(X ::= ANum 3;;

IFB BLe (AId Y) (ANum 4) THEN

Y ::= ANum 4;;

IFB BEq (AId X) (AId Y) THEN Y ::= ANum 999 ELSE SKIP FI

ELSE SKIP FI) / []

⇓ (SKIP;;

IFB BLe (AId Y) (ANum 4) THEN

(SKIP;; SKIP);; (SKIP;; Y ::= ANum 4)

ELSE SKIP;; SKIP FI)

/ [(X,3)]。

证明。 使用 erewrite f_equal2 with (f := fun c st ⇒ _ / _ ⇓ c / st)。

使用 eapply PE_Seq。使用 eapply PE_AssStatic。反射性。

使用 eapply PE_If；直觉 eauto；尝试 solve_by_invert。

使用 eapply。使用 eapply PE_AssStatic。反射性。

使用 eapply PE_IfFalse。反射性。应用构造函数。

反射性。反射性。证毕。

```

## Correctness of Partial Evaluation

    Finally let's prove that this partial evaluator is correct!

```

保留记号 "c' '/' pe_st' '/' st '⇓' st''"

(at level 40, pe_st' at level 39, st at level 39)。

归纳 pe_ceval

（c':com）（pe_st':pe_state）（st:state）（st'':state）：命题 :=

| pe_ceval_intro：对于所有 st'，

c' / st ⇓ st' →

pe_update st' pe_st' = st'' →

c' / pe_st' / st ⇓ st''

其中 "c' '/' pe_st' '/' st '⇓' st''" := (pe_ceval c' pe_st' st st'')。

提示 构造子 pe_ceval。

定理 pe_com_complete：

对于所有 c pe_st pe_st' c'，c / pe_st ⇓ c' / pe_st' →

对于所有 st st''，

（c / pe_update st pe_st ⇓ st''）→

（c' / pe_st' / st ⇓ st''）。

证明。引入 c pe_st pe_st' c' Hpe。

对 Hpe 进行归纳；引入 st st'' Heval；

尝试（反演 Heval; 替换；

尝试（在 * 中重写 → pe_bexp_correct, → H; 通过反演解决）；

[]）；

自动。

- (* PE_AssStatic *) 构造子。构造子。

重写 → pe_aexp_correct。重写 ← pe_update_update_add。

重写 → H。一致性。

- (* PE_AssDynamic *) 构造子。构造子。一致性。

重写 → pe_aexp_correct。重写 ← pe_update_update_remove。

一致性。

- (* PE_Seq *)

对 IHHpe1 进行 edestruct。假设。替换。

对 IHHpe2 进行 edestruct。假设。

自动。

- (* PE_If *) 反演 Heval; 替换。

+ (* E'IfTrue *) 对 IHHpe1 进行 edestruct。假设。

构造子。应用 E_IfTrue。重写 ← pe_bexp_correct。假设。

应用 E_Seq。假设。应用 eval_assign。

重写 ← assign_removes。假设。

+ (* E_IfFalse *) 对 IHHpe2 进行 edestruct。假设。

构造子。应用 E_IfFalse。重写 ← pe_bexp_correct。假设。

应用 E_Seq。假设。应用 eval_assign。

重写 → pe_compare_update。

重写 ← assign_removes。假设。

完成。

定理 pe_com_sound：

对于所有 c pe_st pe_st' c'，c / pe_st ⇓ c' / pe_st' →

对于所有 st st''，

（c' / pe_st' / st ⇓ st''）→

（c / pe_update st pe_st ⇓ st''）。

证明。引入 c pe_st pe_st' c' Hpe。

对 Hpe 进行归纳；

引入 st st'' [st' Heval Heq]；

尝试（反演 Heval; []; 替换）；自动。

- (* PE_AssStatic *) 重写 ← pe_update_update_add。应用 E_Ass。

重写 → pe_aexp_correct。重写 → H。一致性。

- (* PE_AssDynamic *) 重写 ← pe_update_update_remove。应用 E_Ass。

重写 ← pe_aexp_correct。一致性。

- (* PE_Seq *) 应用 E_Seq；自动。

- (* PE_IfTrue *) 应用 E_IfTrue。

重写 → pe_bexp_correct。重写 → H。一致性。自动。

- (* PE_IfFalse *) 应用 E_IfFalse。

重写 → pe_bexp_correct。重写 → H。一致性。自动。

- (* PE_If *)

反演 Heval; 替换；反演 H[7]；

（应用 ceval_deterministic 在 H[8] 中；[| 应用 eval_assign]）；替换。

+ (* E_IfTrue *)

应用 E_IfTrue。重写 → pe_bexp_correct。假设。

重写 ← assign_removes。自动。

+ (* E_IfFalse *)

重写 → pe_compare_update。

应用 E_IfFalse。重写 → pe_bexp_correct。假设。

重写 ← assign_removes。自动。

完成。

```

    The main theorem. Thanks to David Menendez for this formulation!

```

推论 pe_com_correct：

对于所有 c pe_st pe_st' c'，c / pe_st ⇓ c' / pe_st' →

对于所有 st st''，

（c / pe_update st pe_st ⇓ st''）↔

（c' / pe_st' / st ⇓ st''）。

证明。引入 c pe_st pe_st' c' H st st''。分割。

- (* -> *) 应用 pe_com_complete。应用 H。

- (* <- *) 应用 pe_com_sound。应用 H。

完成。

```

# Partial Evaluation of Loops

    It may seem straightforward at first glance to extend the partial
    evaluation relation pe_com above to loops.  Indeed, many loops
    are easy to deal with.  Considered this repeated-squaring loop,
    for example:

```

WHILE BLe (ANum 1) (AId X) DO

Y ::= AMult (AId Y) (AId Y)；

X ::= AMinus (AId X) (ANum 1)

END

    如果我们静态地都不知道 X 和 Y，那么整个循环就是

    动态和剩余命令应该是相同的。如果我们知道

    X 而不是 Y，那么循环可以完全展开，而

    残余命令应该是，例如，

```
      Y ::= AMult (AId Y) (AId Y);;
      Y ::= AMult (AId Y) (AId Y);;
      Y ::= AMult (AId Y) (AId Y)

    if X is initially 3 (and finally 0).  In general, a loop is
    easy to partially evaluate if the final partial state of the loop
    body is equal to the initial state, or if its guard condition is
    static.

    But there are other loops for which it is hard to express the
    residual program we want in Imp.  For example, take this program
    for checking whether Y is even or odd:

```

X ::= ANum 0;;

WHILE BLe (ANum 1) (AId Y) DO

Y ::= AMinus (AId Y) (ANum 1);;

X ::= AMinus (ANum 1) (AId X)

END

    X 的值在循环期间在 0 和 1 之间交替。

    理想情况下，我们希望展开这个循环，但不是全部展开，而是

    *两倍*，变成类似于

```
      WHILE BLe (ANum 1) (AId Y) DO
          Y ::= AMinus (AId Y) (ANum 1);;
          IF BLe (ANum 1) (AId Y) THEN
              Y ::= AMinus (AId Y) (ANum 1)
          ELSE
              X ::= ANum 1;; EXIT
          FI
      END;;
      X ::= ANum 0

    Unfortunately, there is no EXIT command in Imp.  Without
    extending the range of control structures available in our
    language, the best we can do is to repeat loop-guard tests or add
    flag variables.  Neither option is terribly attractive.

    Still, as a digression, below is an attempt at performing partial
    evaluation on Imp commands.  We add one more command argument
    c'' to the pe_com relation, which keeps track of a loop to
    roll up.

```

模块 循环。

保留记法 "c1 '/' st '⇓' c1' '/' st' '/' c''"

(at level 40, st at level 39, c[1]' at level 39, st' at level 39).

归纳 pe_com : com → pe_state → com → pe_state → com → Prop :=

| PE_Skip : ∀pe_st,

SKIP / pe_st ⇓ SKIP / pe_st / SKIP

| PE_AssStatic : ∀pe_st a[1] n[1] l,

pe_aexp pe_st a[1] = ANum n[1] →

(l ::= a[1]) / pe_st ⇓ SKIP / pe_add pe_st l n[1] / SKIP

| PE_AssDynamic : ∀pe_st a[1] a[1]' l,

pe_aexp pe_st a[1] = a[1]' →

(∀n, a[1]' ≠ ANum n) →

(l ::= a[1]) / pe_st ⇓ (l ::= a[1]') / pe_remove pe_st l / SKIP

| PE_Seq : ∀pe_st pe_st' pe_st'' c[1] c[2] c[1]' c[2]' c'',

c[1] / pe_st  ⇓ c[1]' / pe_st' / SKIP →

c[2] / pe_st' ⇓ c[2]' / pe_st'' / c'' →

(c[1] ;; c[2]) / pe_st ⇓ (c[1]' ;; c[2]') / pe_st'' / c''

| PE_IfTrue : ∀pe_st pe_st' b[1] c[1] c[2] c[1]' c'',

pe_bexp pe_st b[1] = BTrue →

c[1] / pe_st ⇓ c[1]' / pe_st' / c'' →

(IFB b[1] THEN c[1] ELSE c[2] FI) / pe_st ⇓ c[1]' / pe_st' / c''

| PE_IfFalse : ∀pe_st pe_st' b[1] c[1] c[2] c[2]' c'',

pe_bexp pe_st b[1] = BFalse →

c[2] / pe_st ⇓ c[2]' / pe_st' / c'' →

(IFB b[1] THEN c[1] ELSE c[2] FI) / pe_st ⇓ c[2]' / pe_st' / c''

| PE_If : ∀pe_st pe_st[1] pe_st[2] b[1] c[1] c[2] c[1]' c[2]' c'',

pe_bexp pe_st b[1] ≠ BTrue →

pe_bexp pe_st b[1] ≠ BFalse →

c[1] / pe_st ⇓ c[1]' / pe_st[1] / c'' →

c[2] / pe_st ⇓ c[2]' / pe_st[2] / c'' →

(IFB b[1] THEN c[1] ELSE c[2] FI) / pe_st

⇓ (IFB pe_bexp pe_st b[1]

THEN c[1]' ;; assign pe_st[1] (pe_compare pe_st[1] pe_st[2])

ELSE c[2]' ;; assign pe_st[2] (pe_compare pe_st[1] pe_st[2]) FI)

/ pe_removes pe_st[1] (pe_compare pe_st[1] pe_st[2])

/ c''

| PE_WhileEnd : ∀pe_st b[1] c[1],

pe_bexp pe_st b[1] = BFalse →

(WHILE b[1] DO c[1] END) / pe_st ⇓ SKIP / pe_st / SKIP

| PE_WhileLoop : ∀pe_st pe_st' pe_st'' b[1] c[1] c[1]' c[2]' c[2]'',

pe_bexp pe_st b[1] = BTrue →

c[1] / pe_st ⇓ c[1]' / pe_st' / SKIP →

(WHILE b[1] DO c[1] END) / pe_st' ⇓ c[2]' / pe_st'' / c[2]'' →

pe_compare pe_st pe_st'' ≠ [] →

(WHILE b[1] DO c[1] END) / pe_st ⇓ (c[1]';;c[2]') / pe_st'' / c[2]''

| PE_While : ∀pe_st pe_st' pe_st'' b[1] c[1] c[1]' c[2]' c[2]'',

pe_bexp pe_st b[1] ≠ BFalse →

pe_bexp pe_st b[1] ≠ BTrue →

c[1] / pe_st ⇓ c[1]' / pe_st' / SKIP →

(WHILE b[1] DO c[1] END) / pe_st' ⇓ c[2]' / pe_st'' / c[2]'' →

pe_compare pe_st pe_st'' ≠ [] →

(c[2]'' = SKIP ∨ c[2]'' = WHILE b[1] DO c[1] END) →

(WHILE b[1] DO c[1] END) / pe_st

⇓ (IFB pe_bexp pe_st b[1]

THEN c[1]';; c[2]';; assign pe_st'' (pe_compare pe_st pe_st'')

ELSE assign pe_st (pe_compare pe_st pe_st'') FI)

/ pe_removes pe_st (pe_compare pe_st pe_st'')

/ c[2]''

| PE_WhileFixedEnd : ∀pe_st b[1] c[1],

pe_bexp pe_st b[1] ≠ BFalse →

(WHILE b[1] DO c[1] END) / pe_st ⇓ SKIP / pe_st / (WHILE b[1] DO c[1] END)

| PE_WhileFixedLoop : ∀pe_st pe_st' pe_st'' b[1] c[1] c[1]' c[2]',

pe_bexp pe_st b[1] = BTrue →

c[1] / pe_st ⇓ c[1]' / pe_st' / SKIP →

(WHILE b[1] DO c[1] END) / pe_st'

⇓ c[2]' / pe_st'' / (WHILE b[1] DO c[1] END) →

pe_compare pe_st pe_st'' = [] →

(WHILE b[1] DO c[1] END) / pe_st

⇓ (WHILE BTrue DO SKIP END) / pe_st / SKIP

(* 因为我们有一个无限循环，实际上我们应该开始抛弃程序的其余部分：(WHILE b[1] DO c[1] END) / pe_st \\ SKIP / pe_st / (WHILE BTrue DO SKIP END) *)

| PE_WhileFixed : ∀pe_st pe_st' pe_st'' b[1] c[1] c[1]' c[2]',

pe_bexp pe_st b[1] ≠ BFalse →

pe_bexp pe_st b[1] ≠ BTrue →

c[1] / pe_st ⇓ c[1]' / pe_st' / SKIP →

(WHILE b[1] DO c[1] END) / pe_st'

⇓ c[2]' / pe_st'' / (WHILE b[1] DO c[1] END) →

pe_compare pe_st pe_st'' = [] →

(WHILE b[1] DO c[1] END) / pe_st

⇓ (WHILE pe_bexp pe_st b[1] DO c[1]';; c[2]' END) / pe_st / SKIP

where "c1 '/' st '⇓' c1' '/' st' '/' c''" := (pe_com c[1] st c[1]' st' c'').

Hint Constructors pe_com.

```

## Examples

```

Ltac step i :=

(eapply i; intuition eauto; try solve_by_invert);

repeat (try eapply PE_Seq;

try (eapply PE_AssStatic; simpl; reflexivity);

try (eapply PE_AssDynamic;

[ simpl; reflexivity

| intuition eauto; solve_by_invert])).

Definition square_loop: com :=

WHILE BLe (ANum 1) (AId X) DO

Y ::= AMult (AId Y) (AId Y);;

X ::= AMinus (AId X) (ANum 1)

END.

Example pe_loop_example1:

square_loop / []

⇓ (WHILE BLe (ANum 1) (AId X) DO

(Y ::= AMult (AId Y) (AId Y);;

X ::= AMinus (AId X) (ANum 1));; SKIP

END) / [] / SKIP.

Proof. erewrite f_equal2 with (f := fun c st ⇒ _ / _ ⇓ c / st / SKIP).

step PE_WhileFixed. step PE_WhileFixedEnd. reflexivity.

reflexivity. reflexivity. Qed.

Example pe_loop_example2:

(X ::= ANum 3;; square_loop) / []

⇓ (SKIP;;

(Y ::= AMult (AId Y) (AId Y);; SKIP);;

(Y ::= AMult (AId Y) (AId Y);; SKIP);;

(Y ::= AMult (AId Y) (AId Y);; SKIP);;

SKIP) / [(X,0)] / SKIP.

Proof. erewrite f_equal2 with (f := fun c st ⇒ _ / _ ⇓ c / st / SKIP).

eapply PE_Seq. eapply PE_AssStatic. reflexivity.

step PE_WhileLoop.

step PE_WhileLoop.

step PE_WhileLoop.

step PE_WhileEnd.

inversion H. inversion H. inversion H.

reflexivity. reflexivity. Qed.

Example pe_loop_example3:

(Z ::= ANum 3;; subtract_slowly) / []

⇓ (SKIP;;

IFB BNot (BEq (AId X) (ANum 0)) THEN

(SKIP;; X ::= AMinus (AId X) (ANum 1));;

IFB BNot (BEq (AId X) (ANum 0)) THEN

(SKIP;; X ::= AMinus (AId X) (ANum 1));;

IFB BNot (BEq (AId X) (ANum 0)) THEN

(SKIP;; X ::= AMinus (AId X) (ANum 1));;

WHILE BNot (BEq (AId X) (ANum 0)) DO

(SKIP;; X ::= AMinus (AId X) (ANum 1));; SKIP

END;;

SKIP;; Z ::= ANum 0

ELSE SKIP;; Z ::= ANum 1 FI;; SKIP

ELSE SKIP;; Z ::= ANum 2 FI;; SKIP

ELSE SKIP;; Z ::= ANum 3 FI) / [] / SKIP.

Proof. erewrite f_equal2 with (f := fun c st ⇒ _ / _ ⇓ c / st / SKIP).

eapply PE_Seq. eapply PE_AssStatic. reflexivity.

step PE_While.

step PE_While.

step PE_While.

step PE_WhileFixed.

step PE_WhileFixedEnd.

一致性。反演 H。反演 H。反演 H。

一致性。一致性。Qed。

示例 pe_loop_example4:

(X ::= ANum 0;;

当 BLe (AId X) (ANum 2) 时

X ::= AMinus (ANum 1) (AId X)

END) / [] ⇓ (SKIP;; WHILE BTrue DO SKIP END) / [(X,0)] / SKIP。

证明。重写 f_equal2 为 (fun c st ⇒ _ / _ ⇓ c / st / SKIP)。

应用 PE_Seq。应用 PE_AssStatic。一致性。

步骤 PE_WhileFixedLoop。

步骤 PE_WhileLoop。

步骤 PE_WhileFixedEnd。

反演 H。一致性。一致性。一致性。Qed。

```

## Correctness

    Because this partial evaluator can unroll a loop n-fold where n is
    a (finite) integer greater than one, in order to show it correct
    we need to perform induction not structurally on dynamic
    evaluation but on the number of times dynamic evaluation enters a
    loop body.

```

保留的符号 "c1 '/' st '⇓' st' '#' n"

(在级别 40，st 在级别 39，st' 在级别 39)。

归纳定义 ceval_count : com → state → state → nat → 属性：

| E'Skip : ∀st，

SKIP / st ⇓ st # 0

| E'Ass  : ∀st a[1] n l，

aeval st a[1] = n →

(l ::= a[1]) / st ⇓ (t_update st l n) # 0

| E'Seq : ∀c[1] c[2] st st' st'' n[1] n[2]，

c[1] / st  ⇓ st'  # n[1] →

c[2] / st' ⇓ st'' # n[2] →

(c[1] ;; c[2]) / st ⇓ st'' # (n[1] + n[2])

| E'IfTrue : ∀st st' b[1] c[1] c[2] n，

beval st b[1] = true →

c[1] / st ⇓ st' # n →

(IFB b[1] THEN c[1] ELSE c[2] FI) / st ⇓ st' # n

| E'IfFalse : ∀st st' b[1] c[1] c[2] n，

beval st b[1] = false →

c[2] / st ⇓ st' # n →

(IFB b[1] THEN c[1] ELSE c[2] FI) / st ⇓ st' # n

| E'WhileEnd : ∀b[1] st c[1],

beval st b[1] = false →

(WHILE b[1] DO c[1] END) / st ⇓ st # 0

| E'WhileLoop : ∀st st' st'' b[1] c[1] n[1] n[2]，

beval st b[1] = true →

c[1] / st ⇓ st' # n[1] →

(WHILE b[1] DO c[1] END) / st' ⇓ st'' # n[2] →

(WHILE b[1] DO c[1] END) / st ⇓ st'' # S (n[1] + n[2])

其中 "c1 '/' st '⇓' st' # n" := (ceval_count c[1] st st' n)。

提示 构造函数 ceval_count。

定理 ceval_count_complete: ∀c st st'，

c / st ⇓ st' → 存在 n，c / st ⇓ st' # n。

证明。引入 c st st' Heval。

对 Heval 进行归纳；

尝试反演 IHHeval1；

尝试反演 IHHeval2；

尝试反演 IHHeval；

自动。Qed。

定理 ceval_count_sound: ∀c st st' n，

c / st ⇓ st' # n → c / st ⇓ st'。

证明。引入 c st st' n Heval。对 Heval 进行归纳；自动。Qed。

定理 pe_compare_nil_lookup: ∀pe_st[1] pe_st[2]，

pe_compare pe_st[1] pe_st[2] = [] →

∀V，pe_lookup pe_st[1] V = pe_lookup pe_st[2] V。

证明。引入 pe_st[1] pe_st[2] H V。

在 (pe_compare_correct pe_st[1] pe_st[2] V) 中应用。

重写 H。引入。反演 H[0]。Qed。

定理 pe_compare_nil_update: ∀pe_st[1] pe_st[2]，

pe_compare pe_st[1] pe_st[2] = [] →

∀st, pe_update st pe_st[1] = pe_update st pe_st[2]。

证明。引入 pe_st[1] pe_st[2] H st。

应用 functional_extensionality。引入 V。

重写 !pe_update_correct。

在 H 中应用 pe_compare_nil_lookup (V:=V)。

重写 H。一致性。Qed。

保留的符号 "c' '/' pe_st' '/' c'' '/' st '⇓' st'' '#' n"

(在级别 40，pe_st' 在级别 39，c'' 在级别 39，

st 在级别 39，st'' 在级别 39)。

归纳定义 pe_ceval_count (c':com) (pe_st':pe_state) (c'':com)

(st:state) (st'':state) (n:nat) : 属性 :=

| pe_ceval_count_intro : ∀st' n'，

c' / st ⇓ st' →

c'' / pe_update st' pe_st' ⇓ st'' # n' →

n' ≤ n →

c' / pe_st' / c'' / st ⇓ st'' # n

其中 "c' '/' pe_st' '/' c'' '/' st '⇓' st'' '#' n" :=

(pe_ceval_count c' pe_st' c'' st st'' n)。

提示 构造子 pe_ceval_count。

引理 pe_ceval_count_le: ∀c' pe_st' c'' st st'' n n',

n' ≤ n →

c' / pe_st' / c'' / st ⇓ st'' # n' →

c' / pe_st' / c'' / st ⇓ st'' # n。

证明。介绍 c' pe_st' c'' st st'' n n' Hle H。反演 H。

构造子；尝试假设。omega。Qed。

定理 pe_com_complete:

∀c pe_st pe_st' c' c''，c / pe_st ⇓ c' / pe_st' / c'' →

∀st st'' n，

（c / pe_update st pe_st ⇓ st'' # n）→

(c' / pe_st' / c'' / st ⇓ st'' # n)。

证明。介绍 c pe_st pe_st' c' c'' Hpe。

对 Hpe 进行归纳；对 st st'' n Heval；

尝试（反演 Heval；替换；

尝试（重写 → pe_bexp_correct，→ H 在 *；通过反演解决）；

[]；

自动。

- (* PE_AssStatic *) 构造子。构造子。

重写 → pe_aexp_correct。重写 ← pe_update_update_add。

重写 → H。应用 E'Skip。自动。

- (* PE_AssDynamic *) 构造子。构造子。一致性。

重写 → pe_aexp_correct。重写 ← pe_update_update_remove。

应用 E'Skip。自动。

- (* PE_Seq *)

应用 IHHpe1 作为 [? ? ? Hskip ?]。假设。

反演 Hskip。替换。

应用 IHHpe2。假设。

构造子；自动。omega。

- (* PE_If *) 反演 Heval；替换。

+ (* E'IfTrue *) 应用 IHHpe1。假设。

构造子。应用 E_IfTrue。重写 ← pe_bexp_correct。假设。

应用 E_Seq。假设。应用 eval_assign。

重写 ← assign_removes。假设。假设。

+ (* E_IfFalse *) 应用 IHHpe2。假设。

构造子。应用 E_IfFalse。重写 ← pe_bexp_correct。假设。

应用 E_Seq。假设。应用 eval_assign。

重写 → pe_compare_update。

重写 ← assign_removes。假设。假设。

- (* PE_WhileLoop *)

应用 IHHpe1 作为 [? ? ? Hskip ?]。假设。

反演 Hskip。替换。

应用 IHHpe2。假设。

构造子；自动。omega。

- (* PE_While *) 反演 Heval；替换。

+ (* E_WhileEnd *) 构造子。应用 E_IfFalse。

重写 ← pe_bexp_correct。假设。

应用 eval_assign。

重写 ← assign_removes。反演 H[2]；替换；自动。

自动。

+ (* E_WhileLoop *)

应用 IHHpe1 作为 [? ? ? Hskip ?]。假设。

反演 Hskip。替换。

应用 IHHpe2。假设。

构造子。应用 E_IfTrue。

重写 ← pe_bexp_correct。假设。

重复应用 E_Seq；自动。应用 eval_assign。

重写 → pe_compare_update，← assign_removes。假设。

omega。

- (* PE_WhileFixedLoop *) 矛盾。

推广相关的 (S (n[1] + n[2]))。介绍 n。

清除 - H H[0] IHHpe1 IHHpe2。推广相关的 st。

通过 lt_wf_ind 进行 n 的归纳；对 st Heval 进行介绍。反演 Heval；替换。

+ (* E'WhileEnd *) 重写 pe_bexp_correct，H 在 H[7] 中。反演 H[7]。

+ (* E'WhileLoop *)

应用 IHHpe1 作为 [? ? ? Hskip ?]。假设。

反演 Hskip。替换。

应用 IHHpe2。假设。

重写 ← (pe_compare_nil_update _ _ H[0]) 在 H[7] 中。

在 H[1] 中应用 H[7]；[| omega]。反演 H[7]。

- (* PE_WhileFixed *) 推广相关的 st。

通过 lt_wf_ind 进行 n 的归纳；对 st Heval 进行介绍。反演 Heval；替换。

+ (* E'WhileEnd *) 在 H[8] 中重写 pe_bexp_correct。自动。

+ (* E'WhileLoop *) 在 H[5] 中重写 pe_bexp_correct。

利用 IHHpe1 得到 [? ? ? Hskip ?]。假设。

反演 Hskip。替换。

利用 IHHpe2。假设。

重写 ← (pe_compare_nil_update _ _ H[1]) 在 H[8] 中。

应用 H[2] 在 H[8] 中；[| omega]。反演 H[8]。

构造子；[ 应用 E_WhileLoop；自动 | 假设 | omega]。

完毕。

定理 pe_com_sound：

∀c pe_st pe_st' c' c''，c / pe_st ⇓ c' / pe_st' / c'' →

∀st st'' n，

(c' / pe_st' / c'' / st ⇓ st'' # n) →

(c / pe_update st pe_st ⇓ st'')。

证明。指出 c pe_st pe_st' c' c'' Hpe。

对 Hpe 进行归纳；

指出 st st'' n [st' n' Heval Heval' Hle]；

尝试 (反演 Heval；[]；替换)；

尝试 (反演 Heval'；[]；替换)；自动。

- (* PE_AssStatic *) 重写 ← pe_update_update_add。应用 E_Ass。

重写 → pe_aexp_correct。重写 → H。反射性。

- (* PE_AssDynamic *) 重写 ← pe_update_update_remove。应用 E_Ass。

重写 ← pe_aexp_correct。反射性。

- (* PE_Seq *) 应用 E_Seq；自动。

- (* PE_IfTrue *) 应用 E_IfTrue。

重写 → pe_bexp_correct。重写 → H。反射性。

应用 IHHpe。自动。

- (* PE_IfFalse *) 应用 E_IfFalse。

重写 → pe_bexp_correct。重写 → H。反射性。

应用 IHHpe。自动。

- (* PE_If *) 反演 Heval；替换；反演 H[7]；替换；清除 H[7]。

+ (* E_IfTrue *)

应用 ceval_deterministic 在 H[8] 中；[| 应用 eval_assign]。替换。

重写 ← assign_removes 在 Heval' 中。

应用 E_IfTrue。重写 → pe_bexp_correct。假设。

应用 IHHpe1。自动。

+ (* E_IfFalse *)

应用 ceval_deterministic 在 H[8] 中；[| 应用 eval_assign]。替换。

重写 → pe_compare_update 在 Heval' 中。

重写 ← assign_removes 在 Heval' 中。

应用 E_IfFalse。重写 → pe_bexp_correct。假设。

应用 IHHpe2。自动。

- (* PE_WhileEnd *) 应用 E_WhileEnd。

重写 → pe_bexp_correct。重写 → H。反射性。

- (* PE_WhileLoop *) 应用 E_WhileLoop。

重写 → pe_bexp_correct。重写 → H。反射性。

应用 IHHpe1。自动。应用 IHHpe2。自动。

- (* PE_While *) 反演 Heval；替换。

+ (* E_IfTrue *)

反演 H[9]。替换。清除 H[9]。

反演 H[10]。替换。清除 H[10]。

应用 ceval_deterministic 在 H[11] 中；[| 应用 eval_assign]。替换。

重写 → pe_compare_update 在 Heval' 中。

重写 ← assign_removes 在 Heval' 中。

应用 E_WhileLoop。重写 → pe_bexp_correct。假设。

应用 IHHpe1。自动。

应用 IHHpe2。自动。

+ (* E_IfFalse *) 应用 ceval_count_sound 在 Heval' 中。

应用 ceval_deterministic 在 H[9] 中；[| 应用 eval_assign]。替换。

重写 ← assign_removes 在 Heval' 中。

反演 H[2]；替换。

* (* c[2]'' = SKIP *) 反演 Heval'。替换。应用 E_WhileEnd。

重写 → pe_bexp_correct。假设。

* (* c[2]'' = WHILE b[1] DO c[1] END *) 假设。

- (* PE_WhileFixedEnd *) 应用 ceval_count_sound。应用 Heval'。

- (* PE_WhileFixedLoop *)

应用 loop_never_stops 在 Heval 中。反演 Heval。

- (* PE_WhileFixed *) 

清除 - H[1] IHHpe1 IHHpe2 Heval。

记住 (WHILE pe_bexp pe_st b[1] DO c[1]';; c[2]' END) 作为 c'。

对 Heval 进行归纳；

反演 Heqc'；替换；清除 Heqc'。

+ (* E_WhileEnd *) 应用 E_WhileEnd。

重写 pe_bexp_correct。假设。

+ (* E_WhileLoop *) 

断言 (IHHeval2' := IHHeval2 (refl_equal _))。

在 IHHeval2' 中应用 ceval_count_complete。反演 IHHeval2'。

清除 IHHeval1 IHHeval2 IHHeval2'。

反演 Heval1。替换。

应用 E_WhileLoop。重写 pe_bexp_correct。假设。自动。

在 IHHpe2 中应用。构造者。假设。

重写 ←（pe_compare_nil_update _ _ H[1]）。假设。应用 le_n。

Qed。

推论 pe_com_correct：

∀c pe_st pe_st' c'，c / pe_st ⇓ c' / pe_st' / SKIP →

∀st st''，

（c / pe_update st pe_st ⇓ st''）↔

（∃st'，c' / st ⇓ st' ∧ pe_update st' pe_st' = st''）。

证明。介绍 c pe_st pe_st' c' H st st''。分裂。

- (* -> *) intros Heval。

在 Heval 中应用 ceval_count_complete。反演 Heval 作为 [n Heval']。

在 H 中应用 pe_com_complete，其中（st:=st）（st'':=st''）（n:=n）。

反演 H 作为 [? ? ? Hskip ?]。反演 Hskip。替换。自动。

假设。

- (* <- *) intros [st' [Heval Heq]]. 替换 st''。

在 H 中应用 pe_com_sound。应用 H。

构造者。应用 Heval。应用 E'Skip。应用 le_n。

Qed。

结束 循环。

```

# Partial Evaluation of Flowchart Programs

    Instead of partially evaluating WHILE loops directly, the
    standard approach to partially evaluating imperative programs is
    to convert them into *flowcharts*.  In other words, it turns out
    that adding labels and jumps to our language makes it much easier
    to partially evaluate.  The result of partially evaluating a
    flowchart is a residual flowchart.  If we are lucky, the jumps in
    the residual flowchart can be converted back to WHILE loops, but
    that is not possible in general; we do not pursue it here. 

## Basic blocks

    A flowchart is made of *basic blocks*, which we represent with the
    inductive type block.  A basic block is a sequence of
    assignments (the constructor Assign), concluding with a
    conditional jump (the constructor If) or an unconditional jump
    (the constructor Goto).  The destinations of the jumps are
    specified by *labels*, which can be of any type.  Therefore, we
    parameterize the block type by the type of labels.

```

块（Label:Type）：= 

| 跳转：Label → 块 Label

| 如果：bexp → Label → Label → 块 Label

| 赋值：id → aexp → 块 Label → 块 Label。

参数 跳转 {Label} _。

参数 如果   {Label} _ _ _。

参数 赋值 {Label} _ _ _。

```

    We use the "even or odd" program, expressed above in Imp, as our
    running example.  Converting this program into a flowchart turns
    out to require 4 labels, so we define the following type.

```

奇偶标签归纳类型：

| 入口：奇偶标签

| 循环：奇偶标签

| 体：奇偶标签

| 完成：奇偶标签。

```

    The following block is the basic block found at the body label
    of the example program.

```

定义奇偶体：= 块 奇偶标签。

赋值 Y (AMinus (AId Y) (ANum 1))

（赋值 X (AMinus (ANum 1) (AId X))

（跳转 循环））。

```

    To evaluate a basic block, given an initial state, is to compute
    the final state and the label to jump to next.  Because basic
    blocks do not *contain* loops or other control structures,
    evaluation of basic blocks is a total function — we don't need to
    worry about non-termination.

```

递归 keval {L:Type}（st:state）（k : block L）：state * L :=

匹配 k 与

| 跳转 l ⇒（st，l）

| 如果 b l[1] l[2] ⇒（st，如果 beval st b 则 l[1] 否则 l[2]）

| 赋值 i a k ⇒ keval（t_update st i（aeval st a））k

结束。

例 keval_example：

keval 空状态 奇偶体

=（t_update（t_update empty_state Y 0）X 1，循环）。

    证明。一致性。Qed。

```

## Flowchart programs

    A flowchart program is simply a lookup function that maps labels
    to basic blocks.  Actually, some labels are *halting states* and
    do not map to any basic block.  So, more precisely, a flowchart
    program whose labels are of type L is a function from L to
    option (block L).

```

定义程序（L:Type）：= L → 选项（块 L）。

定义奇偶：程序奇偶标签：= fun l ⇒

匹配 l 与

| 入口 ⇒ 一些（赋值 X（ANum 0）（跳转 循环））

| 循环 ⇒ 一些（如果（BLe（ANum 1）（AId Y））体 完成）

| 体 ⇒ 一些奇偶体

| 完成 ⇒ 无（* 停止 *）

结束。

```

    Unlike a basic block, a program may not terminate, so we model the
    evaluation of programs by an inductive relation peval rather
    than a recursive function.

```

奇偶 peval {L:Type}（p : program L）

：状态 → L → 状态 → L → 属性：=

| E_None: ∀st l，

p l = None →

peval p st l st l

| E_Some: ∀st l k st' l' st'' l'',

p l = Some k →

keval st k =（st'，l'）→

peval p st' l' st'' l'' →

peval p st l st'' l''。

例奇偶评估：peval 奇偶 空状态 入口 空状态 完成。

证明。重写 f_equal with (f := fun st ⇒ peval _ _ _ st _)。

在 E_Some 中应用。一致性。一致性。

在 E_Some 中应用。一致性。一致性。

应用 E_None。一致性。

应用 functional_extensionality。介绍 i。重写 t_update_same；自动。

证毕。

```

## Partial Evaluation of Basic Blocks and Flowchart Programs

    Partial evaluation changes the label type in a systematic way: if
    the label type used to be L, it becomes pe_state * L.  So the
    same label in the original program may be unfolded, or blown up,
    into multiple labels by being paired with different partial
    states.  For example, the label loop in the parity program
    will become two labels: ([(X,0)], loop) and ([(X,1)], loop).
    This change of label type is reflected in the types of pe_block
    and pe_program defined presently.

```

递归 pe_block {L:Type}（pe_st:pe_state）（k : block L）

：块（pe_state * L）:=

匹配 k 与

| 跳转 l ⇒ 跳转（pe_st，l）

| 如果 b l[1] l[2] ⇒

匹配 pe_bexp pe_st b 与

| BTrue ⇒ 跳转（pe_st，l[1]）

| BFalse ⇒ 跳转（pe_st，l[2]）

| b' ⇒ 如果 b'（pe_st，l[1]）（pe_st，l[2]）

结束

| 赋值 i a k ⇒

匹配 pe_aexp pe_st a 与

| ANum n ⇒ pe_block（pe_add pe_st i n）k

| a' ⇒ 赋值 i a' (pe_block (pe_remove pe_st i) k)

结束

结束。

示例 pe_block_example:

pe_block [(X,0)] parity_body

= 赋值 Y (AMinus (AId Y) (ANum 1)) (Goto ([(X,1)], loop))。

    证明。反射性。完成。

定理 pe_block_correct: ∀(L:Type) st pe_st k st' pe_st' (l':L),

keval st (pe_block pe_st k) = (st', (pe_st', l')) →

keval (pe_update st pe_st) k = (pe_update st' pe_st', l')。

进入。推广 pe_st。推广 st。

对 k 进行归纳 [l | b l[1] l[2] | i a k];

进入 st pe_st H。

- (* Goto *) 反转 H; 反射性。

- (* If *)

替换 (keval st (pe_block pe_st (If b l[1] l[2]))

与 (keval st (If (pe_bexp pe_st b) (pe_st, l[1]) (pe_st, l[2])) 一起

在 H 中 (简化; 分解 (pe_bexp pe_st b); 反射性)。

简化。重写 pe_bexp_correct。

分解 (beval st (pe_bexp pe_st b)); 反转 H; 反射性。

- (* Assign *)

简化。重写 pe_aexp_correct。

对 (pe_aexp pe_st a) 进行分解; 简化;

尝试解决 [rewrite pe_update_update_add; apply IHk; apply H];

解决 [rewrite pe_update_update_remove; apply IHk; apply H]。

完成。

定义 pe_program {L:Type} (p : program L)

: 程序 (pe_state * L) :=

函数 pe_l ⇒ 匹配 pe_l，| (pe_st, l) ⇒

option_map (pe_block pe_st) (p l)

结束。

归纳 pe_peval {L:Type} (p : program L)

(st:state) (pe_st:pe_state) (l:L) (st'o:state) (l':L) : 属性 :=

| pe_peval_intro : ∀st' pe_st',

peval (pe_program p) st (pe_st, l) st' (pe_st', l') →

pe_update st' pe_st' = st'o →

pe_peval p st pe_st l st'o l'。

定理 pe_program_correct:

∀(L:Type) (p : program L) st pe_st l st'o l'，

peval p (pe_update st pe_st) l st'o l' ↔

pe_peval p st pe_st l st'o l'。

证明。进入。

分割。

- (* -> *) 进入 Heval。

记住 (pe_update st pe_st) 作为 sto。

推广 pe_st。推广 st。

对 Heval 进行归纳

[ sto l Hlookup | sto l k st'o l' st''o l'' Hlookup Hkeval Heval ];

进入 st pe_st Heqsto; 替换 sto。

+ (* E_None *) 应用 pe_peval_intro。应用 E_None。

简化。重写 Hlookup。反射性。反射性。

+ (* E_Some *)

记住 (keval st (pe_block pe_st k)) 作为 x。

分解 x 作为 [st' [pe_st' l'_]]。

对称于 Heqx。通过应用 Heqx，用 pe_block_correct 重写 Hkeval。

反转 Hkeval。替换 st'o l'_. 清除 Hkeval。

edestruct IHHeval. reflexivity. subst st''o. clear IHHeval.

应用 pe_peval_intro; [| 反射性]。应用 E_Some; 自动。

简化。重写 Hlookup。反射性。

- (* <- *) 进入 [st' pe_st' Heval Heqst'o]。

记住 (pe_st, l) 作为 pe_st_l。

记住 (pe_st', l') 作为 pe_st'_l'。

推广 pe_st。推广 l。

对 Heval 进行归纳

[ st [pe_st_ l_] Hlookup

| st [pe_st_ l_] pe_k st' [pe_st'_ l'_] st'' [pe_st'' l'']

Hlookup Hkeval Heval ];

进入 l pe_st Heqpe_st_l;

反转 Heqpe_st_l; 反转 Heqpe_st'_l'; 重复替换。

+ (* E_None *) 应用 E_None。简化 Hlookup。

分解 (p l'); [ 解决 [ 反转 Hlookup ] | 反射性 ]。

+ (* E_Some *)

简化 Hlookup。记住 (p l) 作为 k。

对 k 进行分解 [k|]; 反转 Hlookup; 替换。

应用 E_Some; 自动。应用 pe_block_correct。应用 Hkeval。

完成。

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
