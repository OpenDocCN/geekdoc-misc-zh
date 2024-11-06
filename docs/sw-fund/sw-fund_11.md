# 归纳原则归纳原则

```

    With the Curry-Howard correspondence and its realization in Coq in
    mind, we can now take a deeper look at induction principles.

```

需要导出证明对象。

```

# Basics

    Every time we declare a new Inductive datatype, Coq
    automatically generates an *induction principle* for this type.
    This induction principle is a theorem like any other: If t is
    defined inductively, the corresponding induction principle is
    called t_ind.  Here is the one for natural numbers:

```

检查 nat_ind。

(* ===> nat_ind : forall P : nat -> Prop, P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n *)

```

    The induction tactic is a straightforward wrapper that, at its
    core, simply performs apply t_ind.  To see this more clearly,
    let's experiment with directly using apply nat_ind, instead of
    the induction tactic, to carry out some proofs.  Here, for
    example, is an alternate proof of a theorem that we saw in the
    Basics chapter.

```

定理 mult_0_r' : ∀n:nat，

n * 0 = 0。

证明。

应用 nat_ind。

- (* n = O *) reflexivity。

- (* n = S n' *) 简化。 引入 n'。 重写 → IHn'。

reflexivity。Qed。

```

    This proof is basically the same as the earlier one, but a
    few minor differences are worth noting.

    First, in the induction step of the proof (the "S" case), we
    have to do a little bookkeeping manually (the intros) that
    induction does automatically.

    Second, we do not introduce n into the context before applying
    nat_ind — the conclusion of nat_ind is a quantified formula,
    and apply needs this conclusion to exactly match the shape of
    the goal state, including the quantifier.  By contrast, the
    induction tactic works either with a variable in the context or
    a quantified variable in the goal.

    These conveniences make induction nicer to use in practice than
    applying induction principles like nat_ind directly.  But it is
    important to realize that, modulo these bits of bookkeeping,
    applying nat_ind is what we are really doing. 

#### Exercise: 2 stars, optional (plus_one_r')

    Complete this proof without using the induction tactic.

```

定理 plus_one_r' : ∀n:nat，

n + 1 = S n。

证明。

(* 在此填入 *) 已证明。

```

    ☐ 

    Coq generates induction principles for every datatype defined with
    Inductive, including those that aren't recursive.  Although of
    course we don't need induction to prove properties of
    non-recursive datatypes, the idea of an induction principle still
    makes sense for them: it gives a way to prove that a property
    holds for all values of the type.

    These generated principles follow a similar pattern. If we define
    a type t with constructors c[1] ... cn, Coq generates a
    theorem with this shape:

```

t_ind ：∀P：t→Prop，

... 对于 c[1] 的情况 ... →

... 对于 c[2] 的情况 ... → ...

... 对于 cn 的情况 ... →

∀n : t, P n

    每种情况的具体形式取决于参数的数量

    相应的构造函数。 在尝试写下一般规则之前

    规则，让我们看一些更多的例子。 首先是一个例子

    构造函数不带参数：

```
Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.
(* ===> yesno_ind : forall P : yesno -> Prop,                       P yes  ->                       P no  ->                       forall y : yesno, P y *)

```

#### 练习：1 星，可选（rgb）

    写出 Coq 将为以下定义生成的归纳原理

    接下来的数据类型。 （同样，请在纸上写下或

    将其键入注释中，然后与 Coq 的输出进行比较。

```
Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.

```

    ☐

    这里是另一个例子，这次使用其中一个构造函数

    采取一些参数。

```
Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat → natlist → natlist.

Check natlist_ind.
(* ===> (modulo a little variable renaming)    natlist_ind :       forall P : natlist -> Prop,          P nnil  ->          (forall (n : nat) (l : natlist),             P l -> P (ncons n l)) ->          forall n : natlist, P n *)

```

#### 练习：1 星，可选（natlist1）

    假设我们稍微修改了上述定义

不同地：

```
Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 → nat → natlist1.

```

    现在归纳原理会是什么样子呢？ ☐

    从这些例子中，我们可以提取出这个通用规则：

+   类型声明提供了几个构造函数； 每个对应于归纳原理的一个子句。

+   每个构造函数 c 都带有参数类型 a[1] ... an。

+   每个 ai 可以是正在定义的数据类型 t，也可以是其他类型 s。

+   相应的归纳原理的情况是：

    +   “对于类型 a[1]...an 的所有值 x[1]...xn，如果 P 对归纳参数（每个类型为 t 的 xi）都成立，则 P 对 c x[1] ... xn 也成立”。

#### 练习：1 星，可选（byntree_ind）

    写出 Coq 将为以下定义生成的归纳原理

    接下来的数据类型。 （再次，请在纸上写下或

    将其键入注释中，然后与 Coq 的输出进行比较

    输出）

```
Inductive byntree : Type :=
 | bempty : byntree
 | bleaf  : yesno → byntree
 | nbranch : yesno → byntree → byntree → byntree.

```

    ☐

#### 练习：1 星，可选（ex_set）

    这是一个归纳原理，适用于一个归纳定义的

    集。

```
      ExSet_ind :
         ∀P : ExSet → Prop,
             (∀b : bool, P (con1 b)) →
             (∀(n : nat) (e : ExSet), P e → P (con2 n e)) →
             ∀e : ExSet, P e

    Give an Inductive definition of ExSet:

```

归纳 ExSet : Type :=

(* 在此填入 *)

。

```

    ☐ 

# Polymorphism

    Next, what about polymorphic datatypes?

    The inductive definition of polymorphic lists

```

形式化列表（X:Type）：类型 :=

| nil : list X

| cons : X → list X → list X.

    与 natlist 非常相似。 主要区别在于

    即，这里整个定义是在集合 X 上 *参数化* 的：

    也就是说，我们正在定义一个 *族* 的归纳类型 list X，

    每个 X 都有一个。 （请注意，在构造函数中出现 list 的地方

    在声明的情况下，它总是应用于参数 X。）

    归纳原理也是在 X 上 *参数化* 的：

```
      list_ind :
        ∀(X : Type) (P : list X → Prop),
           P [] →
           (∀(x : X) (l : list X), P l → P (x :: l)) →
           ∀l : list X, P l

    Note that the *whole* induction principle is parameterized on
    X.  That is, list_ind can be thought of as a polymorphic
    function that, when applied to a type X, gives us back an
    induction principle specialized to the type list X. 

#### Exercise: 1 star, optional (tree)

    Write out the induction principle that Coq will generate for
   the following datatype.  Compare your answer with what Coq
   prints.

```

归纳 tree（X：Type）：Type :=

| leaf : X → tree X

| node : tree X → tree X → tree X。

检查 tree_ind。

```

    ☐ 

#### Exercise: 1 star, optional (mytype)

    Find an inductive definition that gives rise to the
    following induction principle:

```

mytype_ind :

∀（X：Type）（P：mytype X → Prop），

(∀x : X, P (constr1 X x)) →

(∀n : nat, P (constr2 X n)) →

(∀m : mytype X, P m →

∀n : nat, P (constr3 X m n)) →

∀m : mytype X, P m

    ☐

#### 练习：1 星，可选（foo）

    找到导致

    以下是归纳原理：

```
      foo_ind :
        ∀(X Y : Type) (P : foo X Y → Prop),
             (∀x : X, P (bar X Y x)) →
             (∀y : Y, P (baz X Y y)) →
             (∀f[1] : nat → foo X Y,
               (∀n : nat, P (f[1] n)) → P (quux X Y f[1])) →
             ∀f[2] : foo X Y, P f[2]

    ☐ 

#### Exercise: 1 star, optional (foo')

    Consider the following inductive definition:

```

Inductive foo' (X:Type) : Type :=

| C[1] : list X → foo' X → foo' X

| C[2] : foo' X。

```

    What induction principle will Coq generate for foo'?  Fill
   in the blanks, then check your answer with Coq.)

```

foo'_ind :

∀(X : Type) (P : foo' X → Prop),

(∀(l : list X) (f : foo' X),

_______________________ →

_______________________   ) →

___________________________________________ →

∀f : foo' X, ________________________

    ☐

```

# Induction Hypotheses

    Where does the phrase "induction hypothesis" fit into this story?

    The induction principle for numbers

```

∀P : nat → Prop,

P 0  →

(∀n : nat, P n → P (S n))  →

∀n : nat, P n

    是一个适用于所有命题的通用陈述

P（或者更准确地说，对于所有的命题族

命题 P 以数字 n 为索引）。每次我们

使用这个原理，我们选择 P 为一个特定的

类型为 nat→Prop 的表达式。

    我们可以通过给出更明确的归纳原理来使归纳证明更加明确

给这个表达式一个名称。例如，不是陈述

定理 mult_0_r 为“∀ n, n * 0 = 0”，我们可以

将其写为“∀ n, P_m0r n”，其中 P_m0r 被定义为

如...

```
Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

```

    ...或者等价地：

```
Definition P_m0r' : nat→Prop :=
  fun n ⇒ n * 0 = 0.

```

    现在更容易看到 P_m0r 在证明中的出现位置。

```
Theorem mult_0_r'' : ∀n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* Note the proof state at this point! *)
    intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.

```

    这个额外的命名步骤并不是我们在

    正常的证明，但对于一个例子来说，明确地这样做是有用的

    或两个，因为这样可以让我们准确地看到归纳的过程

    假设是。如果我们通过对 n 进行归纳证明∀ n, P_m0r n

    n（使用归纳或应用 nat_ind），我们看到

    第一个子目标要求我们证明 P_m0r 0（“P 对 0 成立”）。

    zero”），而第二个子目标要求我们证明∀ n'，P_m0r n' → P_m0r (S n')（即“如果 P 对 S n'成立，则 P 对 n'成立”）。每次我们

    对 n 成立”或者更优雅地说“P 被 S 保持”）。

    归纳假设是后者的前提

    蕴含关系 —— 假设 P 对 n'成立，我们

    在证明 P 对 S n'成立时允许使用

```

# More on the induction Tactic

    The induction tactic actually does even more low-level
    bookkeeping for us than we discussed above.

    Recall the informal statement of the induction principle for
    natural numbers:

*   If P n is some proposition involving a natural number n, and we want to show that P holds for *all* numbers n, we can reason like this: 

    *   show that P O holds

    *   show that, if P n' holds, then so does P (S n')

    *   conclude that P n holds for all n.

    So, when we begin a proof with intros n and then induction n,
    we are first telling Coq to consider a *particular* n (by
    introducing it into the context) and then telling it to prove
    something about *all* numbers (by using induction).

    What Coq actually does in this situation, internally, is to
    "re-generalize" the variable we perform induction on.  For
    example, in our original proof that plus is associative...

```

定理 plus_assoc'：∀n m p：nat，

n + (m + p) = (n + m) + p.

证明。

(* ...我们首先将所有 3 个变量引入上下文，这相当于说“考虑任意的 n，m 和 p...”*)

intros n m p.

(* ...现在我们使用归纳策略证明 P n（即，n + (m + p) = (n + m) + p）对所有 n 成立，因此也对此刻上下文中的特定 n 成立。*)

对 n 进行归纳，如 [| n']。

- (* n = O *) reflexivity.

- (* n = S n' *)

(* 在归纳生成的第二个子目标中，即“归纳步骤”中，我们必须证明对所有 n'，P n' 蕴含 P (S n')。归纳策略会自动将 n'和 P n'引入上下文，只留下 P (S n')作为目标。*)

简化。rewrite → IHn'。reflexivity。Qed。

```

    It also works to apply induction to a variable that is
    quantified in the goal.

```

定理 plus_comm'：∀n m：nat，

n + m = m + n。

证明。

对 n 进行归纳，如 [| n']。

- (* n = O *) intros m. rewrite ← plus_n_O. reflexivity.

- (* n = S n' *) intros m. simpl. rewrite → IHn'.

rewrite ← plus_n_Sm. reflexivity. Qed.

```

    Note that induction n leaves m still bound in the goal —
    i.e., what we are proving inductively is a statement beginning
    with ∀ m.

    If we do induction on a variable that is quantified in the goal
    *after* some other quantifiers, the induction tactic will
    automatically introduce the variables bound by these quantifiers
    into the context.

```

定理 plus_comm''：∀n m：nat，

n + m = m + n.

证明。

(* 这次我们对 m 进行归纳，而不是 n...*)

对 m 进行归纳，如 [| m']。

- (* m = O *) simpl. rewrite ← plus_n_O。reflexivity。

- (* m = S m' *) simpl. rewrite ← IHm'.

rewrite ← plus_n_Sm。reflexivity。Qed。

```

#### Exercise: 1 star, optional (plus_explicit_prop)

    Rewrite both plus_assoc' and plus_comm' and their proofs in
    the same style as mult_0_r'' above — that is, for each theorem,
    give an explicit Definition of the proposition being proved by
    induction, and state the theorem and proof in terms of this
    defined proposition.

```

(* 在这里填写*)

```

    ☐

```

# Proposition 中的归纳原理

    早些时候，我们详细研究了 Coq 的归纳原理

    生成用于归纳定义的*集合*的。归纳

    用于归纳定义的*命题*的原则如 ev 是 a

    稍微复杂一些。与所有归纳原理一样

    想要使用 ev 的归纳原理来证明事实

    归纳考虑了 ev 中的可能形状

    可以有。直觉上讲，但我们要证明的是

    不是关于*证据*的陈述，而是关于

    *数字*：因此，我们希望一个归纳原理

    我们通过证据归纳来证明数字的属性。

    例如，从我们到目前为止所说的，您可能会期望

    ev 的归纳定义...

```
      Inductive ev : nat → Prop :=
      | ev_0 : ev 0
      | ev_SS : ∀n : nat, ev n → ev (S (S n)).

    ...to give rise to an induction principle that looks like this...

```

ev_ind_max：∀P：（∀n：nat，ev n → Prop），

P O ev_0 →

（∀（m ： nat）（E ：ev m），

P m E →

P（S（S m））（ev_SS m E））→

∀（n ： nat）（E ：ev n），

P n E

    ...因为：

+   由于 ev 由数字 n 索引（每个 ev 对象 E 是某个特定数字 n 为偶数的证据），所以命题 P 参数化为 n 和 E 两者-也就是说，归纳原理可用于证明涉及偶数和证据的断言。

+   由于有两种提供偶数证据的方法（ev 有两个构造函数），应用归纳原理会生成两个子目标：

    +   我们必须证明 P 适用于 O 和 ev_0。

    +   我们必须证明，无论何时 n 是一个偶数，E 是其偶数性的证据，如果 P 对 n 和 E 成立，则它也对 S（S n）和 ev_SS n E 成立。

+   如果这些子目标可以证明，那么归纳原则告诉我们，P 对*所有*偶数 n 及其偶数性的证据 E 都成立。

    这比我们通常需要或想要的灵活性更大：

    给我们一种证明逻辑断言的方式

    涉及某些偶数证据的性质，而不是

    我们真正关心的只是证明*数字*的属性

    是偶数-我们对数字的断言感兴趣，而不是

    关于证据。因此，更方便的是

    用于证明命题 P 的归纳原理

    参数化只是通过 n 并且其结论为 P

    所有偶数 n：

```
       ∀P : nat → Prop,
       ... →
       ∀n : nat,
       even n → P n

    For this reason, Coq actually generates the following simplified
    induction principle for ev:

```

检查 ev_ind。

（* ===> ev_ind ：对于所有 P：nat -> Prop，P 0 -> （对于所有 n：nat，ev n -> P n -> P（S（S n）））-> 对于所有 n：nat，ev n -> P n *）

```

    In particular, Coq has dropped the evidence term E as a
    parameter of the the proposition P. 

    In English, ev_ind says:

*   Suppose, P is a property of natural numbers (that is, P n is a Prop for every n). To show that P n holds whenever n is even, it suffices to show: 

    *   P holds for 0, 

    *   for any n, if n is even and P holds for n, then P holds for S (S n).

    As expected, we can apply ev_ind directly instead of using
    induction.  For example, we can use it to show that ev' (the
    slightly awkward alternate definition of evenness that we saw in
    an exercise in the λchap{IndProp} chapter) is equivalent to the
    cleaner inductive definition ev:

```

定理 ev_ev'：∀n，ev n → ev' n。

证明。

应用 ev_ind。

- （* ev_0 *）

应用 ev'_0。

- （* ev_SS *）

intros m Hm IH。

应用（ev'_sum 2 m）。

+ 应用 ev'_2。

+ 应用 IH。

Qed。

```

    The precise form of an Inductive definition can affect the
    induction principle Coq generates.

    For example, in chapter IndProp, we defined ≤ as:

```

（* Inductive le：nat -> nat -> Prop：= | le_n：forall n，le n n | le_S：forall n m，（le n m）→（le n（S m））。*）

```

    This definition can be streamlined a little by observing that the
    left-hand argument n is the same everywhere in the definition,
    so we can actually make it a "general parameter" to the whole
    definition, rather than an argument to each constructor.

```

归纳 le（n：nat）：nat → Prop：=

| le_n：le n n

| le_S：∀m，（le n m）→（le n（S m））。

符号“m ≤ n”：=（le m n）。

```

    The second one is better, even though it looks less symmetric.
    Why?  Because it gives us a simpler induction principle.

```

检查 le_ind。

（* === >  forall（n：nat）（P：nat -> Prop），P n -> （对于所有 m：nat，n <= m -> P m -> P（S m））-> 对于所有 n [0]：nat，n <= n [0] -> P n [0] *）

```

# Formal vs. Informal Proofs by Induction

    Question: What is the relation between a formal proof of a
    proposition P and an informal proof of the same proposition P?

    Answer: The latter should *teach* the reader how to produce the
    former.

    Question: How much detail is needed??

    Unfortunately, there is no single right answer; rather, there is a
    range of choices.

    At one end of the spectrum, we can essentially give the reader the
    whole formal proof (i.e., the "informal" proof will amount to just
    transcribing the formal one into words).  This may give the reader
    the ability to reproduce the formal one for themselves, but it
    probably doesn't *teach* them anything much.

    At the other end of the spectrum, we can say "The theorem is true
   and you can figure out why for yourself if you think about it hard
   enough."  This is also not a good teaching strategy, because often
   writing the proof requires one or more significant insights into
   the thing we're proving, and most readers will give up before they
   rediscover all the same insights as we did.

    In the middle is the golden mean — a proof that includes all of
   the essential insights (saving the reader the hard work that we
   went through to find the proof in the first place) plus high-level
   suggestions for the more routine parts to save the reader from
   spending too much time reconstructing these (e.g., what the IH says
   and what must be shown in each case of an inductive proof), but not
   so much detail that the main ideas are obscured.

    Since we've spent much of this chapter looking "under the hood" at
   formal proofs by induction, now is a good moment to talk a little
   about *informal* proofs by induction.

    In the real world of mathematical communication, written proofs
   range from extremely longwinded and pedantic to extremely brief and
   telegraphic.  Although the ideal is somewhere in between, while one
   is getting used to the style it is better to start out at the
   pedantic end.  Also, during the learning phase, it is probably
   helpful to have a clear standard to compare against.  With this in
   mind, we offer two templates — one for proofs by induction over
   *data* (i.e., where the thing we're doing induction on lives in
   Type) and one for proofs by induction over *evidence* (i.e.,
   where the inductively defined thing lives in Prop). 

## Induction Over an Inductively Defined Set

    *Template*:

*   *Theorem*: <Universally quantified proposition of the form "For all n:S, P(n)," where S is some inductively defined set.> 

    *Proof*: By induction on n. 

     <one case for each constructor c of S...> 

    *   Suppose n = c a[1] ... ak, where <...and here we state the IH for each of the a's that has type S, if any>. We must show <...and here we restate P(c a[1] ... ak)>. 

         <go on and prove P(n) to finish the case...> 

    *   <other cases similarly...> ☐

    *Example*:

*   *Theorem*: For all sets X, lists l : list X, and numbers n, if length l = n then index (S n) l = None. 

    *Proof*: By induction on l. 

    *   Suppose l = []. We must show, for all numbers n, that, if length [] = n, then index (S n) [] = None. 

         This follows immediately from the definition of index. 

    *   Suppose l = x :: l' for some x and l', where length l' = n' implies index (S n') l' = None, for any number n'. We must show, for all n, that, if length (x::l') = n then index (S n) (x::l') = None. 

         Let n be a number with length l = n. Since 

        ```

        长度 l = 长度 (x::l') = S (长度 l')，

        只需证明

        ```
          index (S (length l')) l' = None.

         But this follows directly from the induction hypothesis, picking n' to be length l'. ☐
        ```

        ```

## Induction Over an Inductively Defined Proposition

    Since inductively defined proof objects are often called
    "derivation trees," this form of proof is also known as *induction on derivations*.

    *Template*:

*   *Theorem*: <Proposition of the form "Q → P," where Q is some inductively defined proposition (more generally, "For all x y z, Q x y z → P x y z")> 

    *Proof*: By induction on a derivation of Q. <Or, more generally, "Suppose we are given x, y, and z. We show that Q x y z implies P x y z, by induction on a derivation of Q x y z"...> 

     <one case for each constructor c of Q...> 

    *   Suppose the final rule used to show Q is c. Then <...and here we state the types of all of the a's together with any equalities that follow from the definition of the constructor and the IH for each of the a's that has type Q, if there are any>. We must show <...and here we restate P>. 

         <go on and prove P to finish the case...> 

    *   <other cases similarly...> ☐

    *Example* 

*   *Theorem*: The ≤ relation is transitive — i.e., for all numbers n, m, and o, if n ≤ m and m ≤ o, then n ≤ o. 

    *Proof*: By induction on a derivation of m ≤ o. 

    *   Suppose the final rule used to show m ≤ o is le_n. Then m = o and we must show that n ≤ m, which is immediate by hypothesis. 

    *   Suppose the final rule used to show m ≤ o is le_S. Then o = S o' for some o' with m ≤ o'. We must show that n ≤ S o'. By induction hypothesis, n ≤ o'. 

         But then, by le_S, n ≤ S o'. ☐

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
