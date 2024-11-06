# 策略更基本的策略

```

    This chapter introduces several additional proof strategies
    and tactics that allow us to begin proving more interesting
    properties of functional programs.  We will see:

*   how to use auxiliary lemmas in both "forward-style" and "backward-style" proofs;

*   how to reason about data constructors (in particular, how to use the fact that they are injective and disjoint);

*   how to strengthen an induction hypothesis (and when such strengthening is required); and

*   more details on how to reason by case analysis.

```

需要导出 Poly。

```

# The apply Tactic

    We often encounter situations where the goal to be proved is
    *exactly* the same as some hypothesis in the context or some
    previously proved lemma.

```

定理 silly1：∀(n m o p : nat)，

n = m →

[n;o] = [n;p] →

[n;o] = [m;p]。

证明。

intros n m o p eq[1] eq[2]。

重写 ← eq[1]。

```

    Here, we could finish with "rewrite → eq[2]. reflexivity." as we
    have done several times before.  We can achieve the same effect in
    a single step by using the apply tactic instead:

```

应用 eq[2]。Qed。

```

    The apply tactic also works with *conditional* hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved.

```

定理 silly2：∀(n m o p : nat)，

n = m →

(∀(q r : nat), q = r → [q;o] = [r;p]) →

[n;o] = [m;p]。

证明。

intros n m o p eq[1] eq[2]。

应用 eq[2]。应用 eq[1]。Qed。

```

    You may find it instructive to experiment with this proof
    and see if there is a way to complete it using just rewrite
    instead of apply. 

    Typically, when we use apply H, the statement H will
    begin with a ∀ that binds some *universal variables*.  When
    Coq matches the current goal against the conclusion of H, it
    will try to find appropriate values for these variables.  For
    example, when we do apply eq[2] in the following proof, the
    universal variable q in eq[2] gets instantiated with n and r
    gets instantiated with m.

```

定理 silly2a：∀(n m : nat)，

(n,n) = (m,m) →

(∀(q r : nat), (q,q) = (r,r) → [q] = [r]) →

[n] = [m]。

证明。

intros n m eq[1] eq[2]。

应用 eq[2]。应用 eq[1]。Qed。

```

#### Exercise: 2 stars, optional (silly_ex)

    Complete the following proof without using simpl.

```

定理 silly_ex：

(∀n, evenb n = true → oddb (S n) = true) →

evenb 3 = true →

oddb 4 = true。

证明。

(* 填写此处 *) 已承认。

```

    ☐ 

    To use the apply tactic, the (conclusion of the) fact
    being applied must match the goal exactly — for example, apply
    will not work if the left and right sides of the equality are
    swapped.

```

定理 silly3_firsttry：∀(n : nat)，

true = beq_nat n 5 →

beq_nat (S (S n)) 7 = true。

证明。

intros n H。

简化。

```

    Here we cannot use apply directly, but we can use the symmetry
    tactic, which switches the left and right sides of an equality in
    the goal.

```

对称性。

简化。(* （这个简化是可选的，因为如果需要，apply 将执行             简化。*)

应用 H。Qed。

```

#### Exercise: 3 stars (apply_exercise1)

    (*Hint*: You can use apply with previously defined lemmas, not
    just hypotheses in the context.  Remember that Search is
    your friend.)

```

定理 rev_exercise1：∀(l l' : list nat)，

l = rev l' →

l' = rev l。

证明。

(* 填写此处 *) 已承认。

```

    ☐ 

#### Exercise: 1 star, optionalM (apply_rewrite)

    Briefly explain the difference between the tactics apply and
    rewrite.  What are the situations where both can usefully be
    applied?

    (* FILL IN HERE *)

    ☐

```

# 应用... with... 策略

    以下愚蠢的例子使用两次重写来

    从 [a,b] 到 [e,f]。

```
Example trans_eq_example : ∀(a b c d e f : nat),
     [a;b] = [c;d] →
     [c;d] = [e;f] →
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq[1] eq[2].
  rewrite → eq[1]. rewrite → eq[2]. reflexivity. Qed.

```

    由于这是一个常见模式，我们可能想将其提取出来

    作为一个引理记录，一劳永逸地记录相等性是

    传递性。

```
Theorem trans_eq : ∀(X:Type) (n m o : X),
  n = m → m = o → n = o.
Proof.
  intros X n m o eq[1] eq[2]. rewrite → eq[1]. rewrite → eq[2].
  reflexivity. Qed.

```

    现在，我们应该能够使用 trans_eq 来证明上述

    例子。然而，为了做到这一点，我们需要对

    应用策略。

```
Example trans_eq_example' : ∀(a b c d e f : nat),
     [a;b] = [c;d] →
     [c;d] = [e;f] →
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq[1] eq[2].

```

    如果我们简单地告诉 Coq 在这一点上应用 trans_eq，它可以

    告诉（通过将目标与引理的结论进行匹配）

    应该实例化 X 为 [nat]，n 为 [a,b]，和

    o with [e,f]。然而，匹配过程并不确定

    m 的实例化：我们必须明确提供一个

    添加 with (m:=[c,d]) 到 apply 的调用。

```
  apply trans_eq with (m:=[c;d]).
  apply eq[1]. apply eq[2]. Qed.

```

    实际上，我们通常不必在

    with 子句；Coq 通常足够聪明，可以弄清楚哪个

    我们给出的实例化。我们可以改为：应用 trans_eq with [c;d]。

#### 练习：3 星，可选（apply_with_exercise）

```
Example trans_eq_exercise : ∀(n m o p : nat),
     m = (minustwo o) →
     (n + p) = m →
     (n + p) = (minustwo o).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

# The inversion Tactic

    Recall the definition of natural numbers:

```

归纳 nat：Type :=

| O : nat

| S : nat → nat。

    从这个定义很明显，每个数字都有一个

    两种形式：要么是构造子 O，要么是通过

    将构造子 S 应用于另一个数字。但还有更多

    这里比眼睛看到的更多：在定义中（以及在我们的

    对其他数据类型声明的工作原理有一个非正式的理解

    编程语言）还有两个事实：

+   构造子 S 是*单射*的。也就是说，如果 S n = S m，则必须是 n = m。

+   构造子 O 和 S 是*不相交*的。也就是说，对于任何 n，O 都不等于 S n。

    类似的原则适用于所有归纳定义的类型：所有

    构造子是单射的，并且从不同的值构建的值

    构造子从不相等。对于列表，cons 构造子

    是单射的，nil 与每个非空列表都不同。

    对于布尔值，true 和 false 是不同的。（因为 true 和 false 都不

    true 也不接受任何参数，它们的单射性不是

    有趣的。）等等。

    Coq 提供了一个称为 inversion 的策略，允许我们

    利用这些原则进行证明。为了看如何使用它，让我们

    明确显示 S 构造函数是单射的：

```
Theorem S_injective : ∀(n m : nat),
  S n = S m →
  n = m.
Proof.
  intros n m H.

```

    通过在这一点写入 inversion H，我们要求 Coq

    生成它可以从 H 推断出的所有方程作为额外的

    假设，替换目标中的变量。在

    现在的例子，这相当于添加一个新的假设 H[1]：n = m 并将 n 替换为 m 在目标中。

```
  inversion H.
  reflexivity.
Qed.

```

    这里有一个更有趣的例子，展示了如何多个

    方程可以一次推导出来。

```
Theorem inversion_ex[1] : ∀(n m o : nat),
  [n; m] = [o; o] →
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

```

    我们可以用一个名字命名反演生成的方程

    如...子句：

```
Theorem inversion_ex[2] : ∀(n m : nat),
  [n] = [m] →
  n = m.
Proof.
  intros n m H. inversion H as [Hnm]. reflexivity. Qed.

```

#### 练习：1 星（inversion_ex[3]）

```
Example inversion_ex[3] : ∀(X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j →
  y :: l = x :: j →
  x = y.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    当用于涉及等式的假设时

    *不同*构造函数（例如，S n = O），反演解决了

    立即目标。考虑以下证明：

```
Theorem beq_nat_0_l : ∀n,
   beq_nat 0 n = true → n = 0.
Proof.
  intros n.

```

    我们可以通过对 n 进行案例分析来继续。第一种情况是

    琐碎的。

```
  destruct n as [| n'].
  - (* n = 0 *)
    intros H. reflexivity.

```

    但是，第二个看起来并不那么简单：假设

    beq_nat 0（S n'）= true，我们必须展示 S n' = 0，但后者

    明显矛盾！前进的道路在于假设。

    简化目标状态后，我们看到 beq_nat 0（S n'）= true 已变为 false = true：

```
  - (* n = S n' *)
    simpl.

```

    如果我们在这个假设上使用 inversion，Coq 会注意到

    我们正在处理的子目标是不可能的，因此移除

    从进一步考虑中删除它。

```
    intros H. inversion H. Qed.

```

    这是一个逻辑原理的实例，被称为*爆炸原理*，它断言一个矛盾的假设

    意味着任何事情，甚至是虚假的事情！

```
Theorem inversion_ex[4] : ∀(n : nat),
  S n = O →
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem inversion_ex[5] : ∀(n m : nat),
  false = true →
  [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

```

    如果你觉得爆炸原理令人困惑，请记住

    这些证明实际上并没有显示结论

    陈述成立。他们认为，如果

    前提描述的荒谬情况确实发生了，

    那么荒谬的结论就会得出。我们将探讨

    更详细的爆炸原理原则将在下一章中介绍。

#### 练习：1 星（inversion_ex[6]）

```
Example inversion_ex[6] : ∀(X : Type)
                          (x y z : X) (l j : list X),
  x :: y :: l = [] →
  y :: l = z :: j →
  x = z.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    总结一下，假设 H 是一个假设

    上下文或形式为的先前证明的引理

```
        c a[1] a[2] ... an = d b[1] b[2] ... bm

    for some constructors c and d and arguments a[1] ... an and
    b[1] ... bm.  Then inversion H has the following effect:

*   If c and d are the same constructor, then, by the injectivity of this constructor, we know that a[1] = b[1], a[2] = b[2], etc. The inversion H adds these facts to the context and tries to use them to rewrite the goal. 

*   If c and d are different constructors, then the hypothesis H is contradictory, and the current goal doesn't have to be considered at all. In this case, inversion H marks the current goal as completed and pops it off the goal stack.

    The injectivity of constructors allows us to reason that
    ∀ (n m : nat), S n = S m → n = m.  The converse of this
    implication is an instance of a more general fact about both
    constructors and functions, which we will find useful in a few
    places below:

```

定理 f_equal：∀（A B：Type）（f：A→B）（x y：A），

x = y → f x = f y。

证明。intros A B f x y eq. rewrite eq. reflexivity. Qed.

```

# Using Tactics on Hypotheses

    By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic simpl in H performs simplification in
    the hypothesis named H in the context.

```

定理 S_inj：∀（n m：nat）（b：bool），

beq_nat（S n）（S m）= b  →

beq_nat n m = b。

证明。

intros n m b H。在 H 中简化。应用 H。Qed。

```

    Similarly, apply L in H matches some conditional statement
    L (of the form L[1] → L[2], say) against a hypothesis H in the
    context.  However, unlike ordinary apply (which rewrites a goal
    matching L[2] into a subgoal L[1]), apply L in H matches H
    against L[1] and, if successful, replaces it with L[2].

    In other words, apply L in H gives us a form of "forward
    reasoning": from L[1] → L[2] and a hypothesis matching L[1], it
    produces a hypothesis matching L[2].  By contrast, apply L is
    "backward reasoning": it says that if we know L[1]→L[2] and we are
    trying to prove L[2], it suffices to prove L[1].

    Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning.

```

定理 silly3'：∀（n：nat），

（beq_nat n 5 = true → beq_nat（S（S n））7 = true）→

true = beq_nat n 5  →

true = beq_nat（S（S n））7。

证明。

intros n eq H.

H 中的对称性。在 H 中应用 eq。在 H 中对称。

应用 H。Qed.

```

    Forward reasoning starts from what is *given* (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the *goal*, and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.
    If you've seen informal proofs before (for example, in a math or
    computer science class), they probably used forward reasoning.  In
    general, idiomatic use of Coq tends to favor backward reasoning,
    but in some situations the forward style can be easier to think
    about.  

#### Exercise: 3 stars, recommended (plus_n_n_injective)

    Practice using "in" variants in this exercise.  (Hint: use
    plus_n_Sm.)

```

定理 plus_n_n_injective：∀n m，

n + n = m + m →

n = m。

证明。

intros n. induction n as [| n'].

(* 填写此处 *) Admitted.

```

    ☐

```

# 变化归纳假设

    有时重要的是控制

    在 Coq 中进行归纳证明时使用归纳假设。

    特别是，我们需要小心选择哪个

    我们移动的假设的确切形式（使用 intros）从目标到上下文

    在调用归纳策略之前。例如，假设

    我们想要证明 double 函数是单射 — 即，

    它将不同的参数映射到不同的结果：

```
    Theorem double_injective: ∀n m,
      double n = double m → n = m.

    The way we *start* this proof is a bit delicate: if we begin with

```

引入 n。对 n 进行归纳。

    一切顺利。但是如果我们以此开始

```
      intros n m. induction n.

    we get stuck in the middle of the inductive case...

```

定理 double_injective_FAILED：∀n m，

double n = double m →

n = m。

证明。

引入 n m。对 n 进行归纳。

- (* n = O *) 简化。引入 eq。将 m 分解为 [| m']。

+ (* m = O *) 反射。

+ (* m = S m' *) 反演 eq。

- (* n = S n' *) 引入 eq。将 m 分解为 [| m']。

+ (* m = O *) 反演 eq。

+ (* m = S m' *) 应用 f_equal。

```

    At this point, the induction hypothesis, IHn', does *not* give us
    n' = m' — there is an extra S in the way — so the goal is
    not provable.

```

放弃。

```

    What went wrong? 

    The problem is that, at the point we invoke the induction
    hypothesis, we have already introduced m into the context —
    intuitively, we have told Coq, "Let's consider some particular n
    and m..." and we now have to prove that, if double n = double m for *these particular* n and m, then n = m.

    The next tactic, induction n says to Coq: We are going to show
    the goal by induction on n.  That is, we are going to prove, for
    *all* n, that the proposition

*   P n = "if double n = double m, then n = m"

    holds, by showing

*   P O 

     (i.e., "if double O = double m then O = m") and 

*   P n → P (S n) 

     (i.e., "if double n = double m then n = m" implies "if double (S n) = double m then S n = m").

    If we look closely at the second statement, it is saying something
    rather strange: it says that, for a *particular* m, if we know

*   "if double n = double m then n = m"

    then we can prove

*   "if double (S n) = double m then S n = m".

    To see why this is strange, let's think of a particular m —
    say, 5.  The statement is then saying that, if we know

*   Q = "if double n = 10 then n = 5"

    then we can prove

*   R = "if double (S n) = 10 then S n = 5".

    But knowing Q doesn't give us any help at all with proving
    R!  (If we tried to prove R from Q, we would start with
    something like "Suppose double (S n) = 10..." but then we'd be
    stuck: knowing that double (S n) is 10 tells us nothing about
    whether double n is 10, so Q is useless.) 

    Trying to carry out this proof by induction on n when m is
    already in the context doesn't work because we are then trying to
    prove a relation involving *every* n but just a *single* m. 

    The successful proof of double_injective leaves m in the goal
    statement at the point where the induction tactic is invoked on
    n:

```

定理 double_injective：∀n m，

double n = double m →

n = m。

证明。

引入 n。对 n 进行归纳，分为 [| n']。

- (* n = O *) 简化。引入 m eq。将 m 分解为 [| m']。

+ (* m = O *) 反射。

+ (* m = S m' *) 反演 eq。

- (* n = S n' *) 简化。

```

    Notice that both the goal and the induction hypothesis are
    different this time: the goal asks us to prove something more
    general (i.e., to prove the statement for *every* m), but the IH
    is correspondingly more flexible, allowing us to choose any m we
    like when we apply the IH.

```

引入 m eq。

```

    Now we've chosen a particular m and introduced the assumption
    that double n = double m.  Since we are doing a case analysis on
    n, we also need a case analysis on m to keep the two "in sync."

```

将 m 分解为 [| m']。

+ (* m = O *) 简化。

```

    The 0 case is trivial:

```

反演 eq。

+ (* m = S m' *)

应用 f_equal。

```

    At this point, since we are in the second branch of the destruct m, the m' mentioned in the context is the predecessor of the
    m we started out talking about.  Since we are also in the S
    branch of the induction, this is perfect: if we instantiate the
    generic m in the IH with the current m' (this instantiation is
    performed automatically by the apply in the next step), then
    IHn' gives us exactly what we need to finish the proof.

```

应用 IHn'。反演 eq。反射。完成。

```

    What you should take away from all this is that we need to be
    careful about using induction to try to prove something too
    specific: To prove a property of n and m by induction on n,
    it is sometimes important to leave m generic. 

    The following exercise requires the same pattern. 

#### Exercise: 2 stars (beq_nat_true)

```

定理 beq_nat_true：∀n m，

beq_nat n m = true → n = m。

证明。

(* 在此填写*) 放弃。

```

    ☐ 

#### Exercise: 2 stars, advancedM (beq_nat_true_informal)

    Give a careful informal proof of beq_nat_true, being as explicit
    as possible about quantifiers.

```

(* 在此填写*) 放弃。

```

    ☐ 

    The strategy of doing fewer intros before an induction to
    obtain a more general IH doesn't always work by itself; sometimes
    some *rearrangement* of quantified variables is needed.  Suppose,
    for example, that we wanted to prove double_injective by
    induction on m instead of n.

```

定理 double_injective_take2_FAILED：∀n m，

double n = double m →

n = m。

证明。

引入 n m。对 m 进行归纳，分为 [| m']。

- (* m = O *) 简化。引入 eq。将 n 分解为 [| n']。

+ (* n = O *) 反射。

+ (* n = S n' *) 反演 eq。

- (* m = S m' *) 引入 eq。将 n 分解为 [| n']。

+ (* n = O *) 反演 eq。

+ (* n = S n' *) 应用 f_equal。

(* 再次卡在这里，就像之前一样。*)

放弃。

```

    The problem is that, to do induction on m, we must first
    introduce n.  (If we simply say induction m without
    introducing anything first, Coq will automatically introduce n
    for us!)  

    What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that m is quantified before n.  This
    works, but it's not nice: We don't want to have to twist the
    statements of lemmas to fit the needs of a particular strategy for
    proving them!  Rather we want to state them in the clearest and
    most natural way. 

    What we can do instead is to first introduce all the quantified
    variables and then *re-generalize* one or more of them,
    selectively taking variables out of the context and putting them
    back at the beginning of the goal.  The generalize dependent
    tactic does this.

```

定理 double_injective_take2：∀n m，

double n = double m →

n = m。

证明。

引入 n m。

(* n 和 m 都在上下文中*)

推广 n。

(* 现在 n 回到目标中，我们可以对 m 进行归纳，得到��个足够通用的 IH。*)

对 m 进行归纳，分为 [| m']。

- (* m = O *) 简化。引入 n eq。将 n 分解为 [| n']。

+ (* n = O *) 反射。

+ (* n = S n' *) 反演 eq。

- (* m = S m' *) 引入 n eq。将 n 分解为 [| n']。

+ (* n = O *) 反演 eq。

+ (* n = S n' *) 应用 f_equal。

应用 IHm'。反演 eq。反射。完成。

```

    Let's look at an informal proof of this theorem.  Note that
    the proposition we prove by induction leaves n quantified,
    corresponding to the use of generalize dependent in our formal
    proof.

    *Theorem*: For any nats n and m, if double n = double m, then
      n = m.

    *Proof*: Let m be a nat. We prove by induction on m that, for
      any n, if double n = double m then n = m.

*   First, suppose m = 0, and suppose n is a number such that double n = double m. We must show that n = 0. 

     Since m = 0, by the definition of double we have double n = 0. There are two cases to consider for n. If n = 0 we are done, since m = 0 = n, as required. Otherwise, if n = S n' for some n', we derive a contradiction: by the definition of double, we can calculate double n = S (S (double n')), but this contradicts the assumption that double n = 0. 

*   Second, suppose m = S m' and that n is again a number such that double n = double m. We must show that n = S m', with the induction hypothesis that for every number s, if double s = double m' then s = m'. 

     By the fact that m = S m' and the definition of double, we have double n = S (S (double m')). There are two cases to consider for n. 

     If n = 0, then by definition double n = 0, a contradiction. 

     Thus, we may assume that n = S n' for some n', and again by the definition of double we have S (S (double n')) = S (S (double m')), which implies by inversion that double n' = double m'. Instantiating the induction hypothesis with n' thus allows us to conclude that n' = m', and it follows immediately that S n' = S m'. Since S n' = n and S m' = m, this is just what we wanted to show. ☐

    Before we close this section and move on to some exercises,
    let's digress briefly and use beq_nat_true to prove a similar
    property of identifiers that we'll need in later chapters:

```

定理 beq_id_true：∀x y，

beq_id x y = true → x = y。

证明。

引入 [m] [n]。简化。引入 H。

断言 (H' : m = n)。{ 应用 beq_nat_true。应用 H。 }

重写 H'。反射。

完成。

```

#### Exercise: 3 stars, recommended (gen_dep_practice)

    Prove this by induction on l.

```

定理 nth_error_after_last：∀(n : nat) (X : Type) (l : list X)，

长度 l = n →

nth_error l n = None。

证明。

(* 在此填写*) 放弃。

```

    ☐

```

# 展开定义

    有时我们需要手动展开一个定义

    以便我们可以操作其右侧。例如，如果我们

    定义...

```
Definition square n := n * n.

```

    ... 并尝试证明关于 square 的一个简单事实...

```
Lemma square_mult : ∀n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.

```

    ... 我们卡住了：此时简化不会简化任何内容，

    因为我们还没有证明关于 square 的其他事实，

    没有我们可以应用或重写的内容。

    为了取得进展，我们可以手动展开

    平方：

```
  unfold square.

```

    现在我们有很多可以使用的内容：等式的两边都是

    涉及乘法的表达式，我们有很多事实

    关于乘法的。特别是，我们知道

    它是可交换和可结合的，从这些事实中我们知道

    很难完成证明。

```
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

```

    此时，对展开和简化进行更深入的讨论

    是必要的。

    你可能已经注意到像 simpl 这样的策略，

    反射，apply 通常会展开

    当函数自动执行时，如果这使它们取得进展。对于

    例如，如果我们将 foo m 定义为常数 5...

```
Definition foo (x: nat) := 5.

```

    然后在以下证明中简化（或者反射，如果

    我们省略 simpl）将 foo m 展开为 (fun x ⇒ 5) m 和

    然后进一步简化这个表达式为只有 5。

```
Fact silly_fact_1 : ∀m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

```

    然而，这种自动展开相当保守。对于

    例如，如果我们定义一个稍微复杂的函数

    涉及模式匹配的...

```
Definition bar x :=
  match x with
  | O ⇒ 5
  | S _ ⇒ 5
  end.

```

    ...那么类似的证明将会陷入困境：

```
Fact silly_fact_2_FAILED : ∀m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

```

    simpl 在这里无法取得进展的原因是

    注意到，在暂时展开 bar m 后，它留下了

    一个匹配项的被检验者，m，是一个变量，所以匹配不能

    不能进一步简化。（它不够聪明，无法注意到这一点

    匹配的两个分支是相同的。）因此，它放弃了

    展开 bar m 并将其保持不变。同样地，暂时

    展开 bar (m+1) 留下一个匹配项，其案例分析的被检验者是一个

    函数应用（它本身无法简化，甚至

    在展开 + 的定义后，所以 simpl 将其留下

    单独。

    此时，有两种方法可以取得进展。一种是使用

    destruct m 将证明分成两种情况，每种情况都专注于一个

    更具体的 m 的选择（O vs S _）。在每种情况下，这个

    bar 中的匹配现在可以取得进展，证明也是

    完成起来很容易。

```
Fact silly_fact_2 : ∀m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

```

    这种方法有效，但它取决于我们认识到

    bar 中隐藏的匹配项是阻止我们取得进展的原因

    进展。

    更直接的方法是明确告诉

    Coq 展开 bar。

```
Fact silly_fact_2' : ∀m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.

```

    现在很明显我们卡在匹配表达式上。

    等号的两边，我们可以使用 destruct 完成

    在不费力地思考的情况下完成证明。

```
  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

```

# 使用 destruct 处理复合表达式

    我们已经看到许多示例，其中 destruct 被用来

    执行某个变量的值的案例分析。但是

    有时我们需要根据某些结果的情况进行推理

    *表达式*。我们也可以用 destruct 来做这个。

    以下是一些例子：

```
Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : ∀(n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    - (* beq_nat n 3 = true *) reflexivity.
    - (* beq_nat n 3 = false *) destruct (beq_nat n 5).
      + (* beq_nat n 5 = true *) reflexivity.
      + (* beq_nat n 5 = false *) reflexivity. Qed.

```

    在上述证明中展开 sillyfun 后，我们发现

    如果我们卡在 if (beq_nat n 3) then ... else .... 上。但是任一

    n 等于 3 或者不等于 3，所以我们可以使用 destruct (beq_nat n 3) 来让我们推理这两种情况。

    一般来说，destruct 策略可用于执行案例

    对任意计算结果进行分析。如果 e 是一个

    其类型为归纳定义的类型 T 的表达式，那么

    对于 T 的每个构造函数 c，destruct e 生成一个子目标

    在所有 e 的出现（在目标和上下文中）

    被 c 替换。

#### 练习：3 星，可选（combine_split）

```
Theorem combine_split : ∀X Y (l : list (X * Y)) l[1] l[2],
  split l = (l[1], l[2]) →
  combine l[1] l[2] = l.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    然而，对复合表达式进行 destruct 需要一点

    要小心，因为这样的 destruct 有时会擦除我们需要的信息

    完成证明。例如，假设我们定义一个类似 sillyfun1 的函数

    这样：

```
Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

```

    现在假设我们想说服 Coq（相当

    显而易见）的事实，即 sillyfun1 n 仅在 n 为真时产生

    奇数。类比我们在上面与 sillyfun 一起做的证明，它

    自然地开始证明如下：

```
Theorem sillyfun1_odd_FAILED : ∀(n : nat),
     sillyfun1 n = true →
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Abort.

```

    我们在这一点上陷入困境，因为上下文不

    包含足够的信息来证明目标！问题在于

    destruct 执行的替换太过激烈 — 它抛出了

    消除每个出现的 beq_nat n 3，但我们需要保留一些

    这个表达式及其如何被破坏的记忆，因为我们

    需要能够推断，因为在这种情况下 beq_nat n 3 = true

    案例分析的分支，必须是 n = 3，从中

    随后 n 为奇数。

    我们真正想要的是替换掉所有现有的

    出现的 beq_nat n 3，但同时添加一个方程

    记录我们处于哪种情况的上下文。等式：

    限定符允许我们引入这样一个方程，给它一个

    我们选择的名称。

```
Theorem sillyfun1_odd : ∀(n : nat),
     sillyfun1 n = true →
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got      stuck above, except that the context contains an extra      equality assumption, which is exactly what we need to      make progress. *)
    - (* e[3] = true *) apply beq_nat_true in Heqe3.
      rewrite → Heqe3. reflexivity.
    - (* e[3] = false *)
     (* When we come to the second equality test in the body         of the function we are reasoning about, we can use         eqn: again in the same way, allow us to finish the         proof. *)
      destruct (beq_nat n 5) eqn:Heqe5.
        + (* e[5] = true *)
          apply beq_nat_true in Heqe5.
          rewrite → Heqe5. reflexivity.
        + (* e[5] = false *) inversion eq. Qed.

```

#### 练习：2 星（destruct_eqn_practice）

```
Theorem bool_fn_applied_thrice :
  ∀(f : bool → bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

# Review

    We've now seen many of Coq's most fundamental tactics.  We'll
    introduce a few more in the coming chapters, and later on we'll
    see some more powerful *automation* tactics that make Coq help us
    with low-level details.  But basically we've got what we need to
    get work done.

    Here are the ones we've seen:

*   intros: move hypotheses/variables from goal to context 

*   reflexivity: finish the proof (when the goal looks like e = e) 

*   apply: prove goal using a hypothesis, lemma, or constructor 

*   apply... in H: apply a hypothesis, lemma, or constructor to a hypothesis in the context (forward reasoning) 

*   apply... with...: explicitly specify values for variables that cannot be determined by pattern matching 

*   simpl: simplify computations in the goal 

*   simpl in H: ... or a hypothesis 

*   rewrite: use an equality hypothesis (or lemma) to rewrite the goal 

*   rewrite ... in H: ... or a hypothesis 

*   symmetry: changes a goal of the form t=u into u=t 

*   symmetry in H: changes a hypothesis of the form t=u into u=t 

*   unfold: replace a defined constant by its right-hand side in the goal 

*   unfold... in H: ... or a hypothesis 

*   destruct... as...: case analysis on values of inductively defined types 

*   destruct... eqn:...: specify the name of an equation to be added to the context, recording the result of the case analysis 

*   induction... as...: induction on values of inductively defined types 

*   inversion: reason by injectivity and distinctness of constructors 

*   assert (H: e) (or assert (e) as H): introduce a "local lemma" e and call it H 

*   generalize dependent x: move the variable x (and anything else that depends on it) from the context back to an explicit hypothesis in the goal formula

```

# 附加练习

#### 练习：3 星（beq_nat_sym）

```
Theorem beq_nat_sym : ∀(n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星，高级 M？（beq_nat_sym_informal）

    给出与您对应的此引理的非正式证明

    上述形式化证明：

    定理：对于任何 nats n m，beq_nat n m = beq_nat m n。

    证明：

（*在这里填写*）

    ☐

#### 练习：3 星，可选（beq_nat_trans）

```
Theorem beq_nat_trans : ∀n m p,
  beq_nat n m = true →
  beq_nat m p = true →
  beq_nat n p = true.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星，高级 M（split_combine）

    我们在上面的一个练习中证明了，对于所有的成对列表，

    combine 是 split 的逆。您如何形式化

    声明 split 是 combine 的逆？这是什么时候

    属性为真？

    用下面的 split_combine_statement 完成定义

    声明 split 是的逆。

    combine。然后，证明该属性成立。（确保留下

    通过不在更多的 intros 上进行使您的归纳假设更一般

    比必要的更多的事情。提示：你需要 l[1]的什么属性

    和 l[2]用于 split combine l[1] l[2] = (l[1],l[2])是否为真?)

```
Definition split_combine_statement : Prop
  (* (": Prop" means that we are giving a name to a      logical proposition here.) *)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem split_combine : split_combine_statement.
Proof.
(* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星，高级（filter_exercise）

    这个有点具有挑战性。注意您的形式

    归纳假设。

```
Theorem filter_exercise : ∀(X : Type) (test : X → bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf →
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：4 星，高级，推荐（forall_exists_challenge）

    定义两个递归 Fixpoints，forallb 和 existsb。该

    首先检查列表中的每个元素是否满足给定的

    断言：

```
      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true

      forallb evenb [0;2;4;5] = false

      forallb (beq_nat 5) [] = true

    The second checks whether there exists an element in the list that
    satisfies a given predicate:

```

existsb (beq_nat 5) [0;2;3;6] = false

existsb (andb true) [true;true;false] = true

existsb oddb [1;0;0;0;0;3] = true

existsb evenb [] = false

    接下来，定义*非递归*版本的 existsb — 称之为

    existsb' — 使用 forallb 和 negb。

    最后，证明一个定理 existsb_existsb'，陈述

    existsb'和 existsb 具有相同的行为。

```
(* FILL IN HERE *)

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
