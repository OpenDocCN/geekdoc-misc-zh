# STLC 的 NormNormalization

```

```

（由 Andrew Tolmach 撰写和维护的章节）

```

    This optional chapter is based on chapter 12 of *Types and Programming Languages* (Pierce).  It may be useful to look at the
    two together, as that chapter includes explanations and informal
    proofs that are not repeated here.

    In this chapter, we consider another fundamental theoretical
    property of the simply typed lambda-calculus: the fact that the
    evaluation of a well-typed program is guaranteed to halt in a
    finite number of steps—-i.e., every well-typed term is
    *normalizable*.

    Unlike the type-safety properties we have considered so far, the
    normalization property does not extend to full-blown programming
    languages, because these languages nearly always extend the simply
    typed lambda-calculus with constructs, such as general
    recursion (see the MoreStlc chapter) or recursive types, that
    can be used to write nonterminating programs.  However, the issue
    of normalization reappears at the level of *types* when we
    consider the metatheory of polymorphic versions of the lambda
    calculus such as System F-omega: in this system, the language of
    types effectively contains a copy of the simply typed
    lambda-calculus, and the termination of the typechecking algorithm
    will hinge on the fact that a "normalization" operation on type
    expressions is guaranteed to terminate.

    Another reason for studying normalization proofs is that they are
    some of the most beautiful—-and mind-blowing—-mathematics to be
    found in the type theory literature, often (as here) involving the
    fundamental proof technique of *logical relations*.

    The calculus we shall consider here is the simply typed
    lambda-calculus over a single base type bool and with
    pairs. We'll give most details of the development for the basic
    lambda-calculus terms treating bool as an uninterpreted base
    type, and leave the extension to the boolean operators and pairs
    to the reader.  Even for the base calculus, normalization is not
    entirely trivial to prove, since each reduction of a term can
    duplicate redexes in subterms. 

#### Exercise: 2 starsM (norm_fail)

    Where do we fail if we attempt to prove normalization by a
    straightforward induction on the size of a well-typed term?

```

(* 在此填写 *)

```

    ☐ 

#### Exercise: 5 stars, recommended (norm)

    The best ways to understand an intricate proof like this is
    are (1) to help fill it in and (2) to extend it.  We've left out some
    parts of the following development, including some proofs of lemmas
    and the all the cases involving products and conditionals.  Fill them
    in.  ☐

```

# 语言

    我们首先重复相关的语言定义，即

    类似于 MoreStlc 章节中的内容，还支持

    包括类型保持和步骤确定性的结果。 （我们

    不需���进展。）您可能只希望跳到

    规范化部分...

```

### Syntax and Operational Semantics

```

引入 Coq.Lists.List。

导入 ListNotations。

引入 Maps。

引入 Smallstep。

提示 Constructors multi。

归纳 ty：类型 :=

| TBool : 类型

| TArrow : 类型 → 类型 → 类型

| TProd  : 类型 → 类型 → 类型

。

归纳 tm：类型 :=

(* 纯 STLC *)

| tvar : id → 项

| tapp : 项 → 项 → 项

| tabs : id → 类型 → 项 → 项

(* 对 *)

| tpair : 项 → 项 → 项

| tfst : 项 → 项

| tsnd : 项 → 项

(* 布尔值 *)

| ttrue : 项

| tfalse : 项

| tif : 项 → 项 → 项 → 项。

(* 即，如果 t[0] then t[1] else t[2] *)

```

### Substitution

```

递归替换（x:id）（s:tm）（t:tm）：tm :=

匹配 t 与

| tvar y ⇒ 如果 beq_id x y then s else t

| tabs y T t[1] ⇒

tabs y T（如果 beq_id x y then t[1] else（subst x s t[1]））

| tapp t[1] t[2] ⇒ tapp (subst x s t[1]) (subst x s t[2])

| tpair t[1] t[2] ⇒ tpair（subst x s t[1]）（subst x s t[2]）

| tfst t[1] ⇒ tfst（subst x s t[1]）

| tsnd t[1] ⇒ tsnd（subst x s t[1]）

| ttrue ⇒ ttrue

| tfalse ⇒ tfalse

| tif t[0] t[1] t[2] ⇒

tif（subst x s t[0]）（subst x s t[1]）（subst x s t[2]）

结束。

记号 "'[' x ':=' s ']' t" := (subst x s t) (在 20 级)。

```

### Reduction

```

归纳值：tm → Prop :=

| v_abs : ∀x T[11] t[12],

值（tabs x T[11] t[12]）

| v_pair : ∀v[1] v[2],

值 v[1] →

值 v[2] →

值（tpair v[1] v[2]）

| v_true : value ttrue

| v_false : value tfalse

。

提示 Constructors value。

保留记号 "t1 '⇒' t2"（在 40 级）。

归纳步骤：tm → tm → Prop :=

| ST_AppAbs : ∀x T[11] t[12] v[2],

值 v[2] →

(tapp (tabs x T[11] t[12]) v[2]) ⇒ [x:=v[2]]t[12]

| ST_App1 : ∀t[1] t[1]' t[2],

t[1] ⇒ t[1]' →

（tapp t[1] t[2]）⇒（tapp t[1]' t[2]）

| ST_App2 : ∀v[1] t[2] t[2]',

值 v[1] →

t[2] ⇒ t[2]' →

（tapp v[1] t[2]）⇒（tapp v[1] t[2]'）

(* 对 *)

| ST_Pair1 : ∀t[1] t[1]' t[2],

t[1] ⇒ t[1]' →

（tpair t[1] t[2]）⇒（tpair t[1]' t[2]）

| ST_Pair2 : ∀v[1] t[2] t[2]',

值 v[1] →

t[2] ⇒ t[2]' →

（tpair v[1] t[2]）⇒（tpair v[1] t[2]'）

| ST_Fst : ∀t[1] t[1]',

t[1] ⇒ t[1]' →

（tfst t[1]）⇒（tfst t[1]'）

| ST_FstPair : ∀v[1] v[2],

值 v[1] →

值 v[2] →

(tfst（tpair v[1] v[2]）) ⇒ v[1]

| ST_Snd : ∀t[1] t[1]',

t[1] ⇒ t[1]' →

（tsnd t[1]）⇒（tsnd t[1]'）

| ST_SndPair : ∀v[1] v[2],

值 v[1] →

值 v[2] →

（tsnd（tpair v[1] v[2]））⇒ v[2]

(* 布尔值 *)

| ST_IfTrue : ∀t[1] t[2],

（tif ttrue t[1] t[2]）⇒ t[1]

| ST_IfFalse : ∀t[1] t[2],

(tif tfalse t[1] t[2]) ⇒ t[2]

| ST_If : ∀t[0] t[0]' t[1] t[2],

t[0] ⇒ t[0]' →

(tif t[0] t[1] t[2]) ⇒ (tif t[0]' t[1] t[2])

其中 "t1 '⇒' t2" := (step t[1] t[2])。

记号 multistep := (multi step)。

记号 "t1 '⇒*' t2" := (multistep t[1] t[2]) (在 40 级)。

提示 Constructors step。

记号 step_normal_form := (normal_form step)。

引理 value__normal : ∀t, value t → step_normal_form t。

    Proof with eauto.

intros t H; induction H; intros [t' ST]; inversion ST...

    Qed.

```

### Typing

```

定义上下文 := partial_map ty.

Inductive has_type : context → tm → ty → Prop :=

(* proper terms 的类型规则*)

| T_Var : ∀Γ x T,

Γ x = Some T →

has_type Γ (tvar x) T

| T_Abs : ∀Γ x T[11] T[12] t[12],

has_type (update Γ x T[11]) t[12] T[12] →

has_type Γ (tabs x T[11] t[12]) (TArrow T[11] T[12])

| T_App : ∀T[1] T[2] Γ t[1] t[2],

has_type Γ t[1] (TArrow T[1] T[2]) →

has_type Γ t[2] T[1] →

has_type Γ (tapp t[1] t[2]) T[2]

(* pairs *)

| T_Pair : ∀Γ t[1] t[2] T[1] T[2],

has_type Γ t[1] T[1] →

has_type Γ t[2] T[2] →

has_type Γ (tpair t[1] t[2]) (TProd T[1] T[2])

| T_Fst : ∀Γ t T[1] T[2],

has_type Γ t (TProd T[1] T[2]) →

has_type Γ (tfst t) T[1]

| T_Snd : ∀Γ t T[1] T[2],

has_type Γ t (TProd T[1] T[2]) →

has_type Γ (tsnd t) T[2]

(* booleans *)

| T_True : ∀Γ,

has_type Γ ttrue TBool

| T_False : ∀Γ,

has_type Γ tfalse TBool

| T_If : ∀Γ t[0] t[1] t[2] T,

has_type Γ t[0] TBool →

has_type Γ t[1] T →

has_type Γ t[2] T →

has_type Γ (tif t[0] t[1] t[2]) T

.

Hint Constructors has_type.

Hint Extern 2 (has_type _ (tapp _ _) _) ⇒ eapply T_App; auto.

Hint Extern 2 (_ = _) ⇒ compute; reflexivity.

```

### Context Invariance

```

Inductive appears_free_in : id → tm → Prop :=

| afi_var : ∀x,

appears_free_in x (tvar x)

| afi_app1 : ∀x t[1] t[2],

appears_free_in x t[1] → appears_free_in x (tapp t[1] t[2])

| afi_app2 : ∀x t[1] t[2],

appears_free_in x t[2] → appears_free_in x (tapp t[1] t[2])

| afi_abs : ∀x y T[11] t[12],

y ≠ x  →

appears_free_in x t[12] →

appears_free_in x (tabs y T[11] t[12])

(* pairs *)

| afi_pair1 : ∀x t[1] t[2],

appears_free_in x t[1] →

appears_free_in x (tpair t[1] t[2])

| afi_pair2 : ∀x t[1] t[2],

appears_free_in x t[2] →

appears_free_in x (tpair t[1] t[2])

| afi_fst : ∀x t,

appears_free_in x t →

appears_free_in x (tfst t)

| afi_snd : ∀x t,

appears_free_in x t →

appears_free_in x (tsnd t)

(* booleans *)

| afi_if[0] : ∀x t[0] t[1] t[2],

appears_free_in x t[0] →

appears_free_in x (tif t[0] t[1] t[2])

| afi_if[1] : ∀x t[0] t[1] t[2],

appears_free_in x t[1] →

appears_free_in x (tif t[0] t[1] t[2])

| afi_if[2] : ∀x t[0] t[1] t[2],

appears_free_in x t[2] →

appears_free_in x (tif t[0] t[1] t[2])

.

Hint Constructors appears_free_in.

定义闭合（t:tm） :=

∀x, ¬ appears_free_in x t.

Lemma context_invariance : ∀Γ Γ' t S,

has_type Γ t S  →

(∀x, appears_free_in x t → Γ x = Γ' x)  →

has_type Γ' t S.

    Proof with eauto.

intros. generalize dependent Γ'.

induction H;

intros Γ' Heqv...

- (* T_Var *)

apply T_Var... rewrite ← Heqv...

- (* T_Abs *)

apply T_Abs... apply IHhas_type. intros y Hafi.

unfold update, t_update. destruct (beq_idP x y)...

- (* T_Pair *)

apply T_Pair...

- (* T_If *)

eapply T_If...

    Qed.

Lemma free_in_context : ∀x t T Γ,

appears_free_in x t →

has_type Γ t T →

∃T', Γ x = Some T'.

    Proof with eauto.

intros x t T Γ Hafi Htyp.

induction Htyp; inversion Hafi; subst...

- (* T_Abs *)

destruct IHHtyp as [T' Hctx]... ∃T'.

unfold update, t_update in Hctx.

rewrite false_beq_id in Hctx...

    Qed.

Corollary typable_empty__closed : ∀t T,

has_type empty t T  →

closed t.

    Proof.

intros. unfold closed. intros x H[1].

destruct (free_in_context _ _ _ _ H[1] H) as [T' C].

inversion C. Qed.

```

### Preservation

```

Lemma substitution_preserves_typing : ∀Γ x U v t S,

has_type (update Γ x U) t S  →

has_type empty v U   →

has_type Γ ([x:=v]t) S.

    Proof with eauto.

(* 定理：如果 Gamma,x:U |- t : S 且 empty |- v : U，则 Gamma |- (x:=vt) S。 *)

intros Γ x U v t S Htypt Htypv.

generalize dependent Γ. generalize dependent S.

(* 证明：通过 对 项 t 进行 归纳。 大多数 情况 直接 遵循 IH，除了 tvar 和 tabs。 前者 不是 自动 的，因为 我们 必须 推理 变量 如何 相互 作用。 *)

induction t;

intros S Γ Htypt; simpl; inversion Htypt; subst...

- (* tvar *)

simpl. rename i into y.

(* 如果 t = y，则 我们 知道 empty ⊢ v : U 且 Γ,x:U ⊢ y : S 并且，通过 反演，update Γ x U y = Some S。 我们 想要 展示 Γ ⊢ [x:=v]y : S。 有 两种 情况 要考虑：要么 x=y 要么 x≠y。 *)

unfold update, t_update in H[1].

destruct (beq_idP x y).

+ (* x=y *)

(* 如果 x = y，则 我们 知道 U = S，且 [x:=v]y = v。 所以 我们 真正 需要 展示 的 是 如果 empty ⊢ v : U 则 Γ ⊢ v : U。 我们 已经 证明 了 一个 更 一般 的 定理，称为��上下文 不变性。 *)

subst.

inversion H[1]; subst. clear H[1].

eapply context_invariance...

intros x Hcontra.

destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...

inversion HT'.

+ (* x<>y *)

(* 如果 x ≠ y，则 Γ y = Some S 且 替换 没有 效果。 我们 可以 通过 T_Var 展示 Γ ⊢ y : S。 *)

apply T_Var...

- (* tabs *)

rename i into y. rename t into T[11].

(* 如果 t = tabs y T[11] t[0]，则 我们 知道 Γ,x:U ⊢ tabs y T[11] t[0] : T[11]→T[12] Γ,x:U,y:T[11] ⊢ t[0] : T[12] empty ⊢ v : U 根据 我们 的 IH，我们 知道 对于 所有 S Gamma， Γ,x:U ⊢ t[0] : S → Γ ⊢ [x:=v]t[0] S 我们 可以 计算 x:=vt = tabs y T[11] (if beq_id x y then t[0] else x:=vt[0]) 并且 我们 必须 展示 Γ ⊢ [x:=v]t : T[11]→T[12]。 我们 知道 我们 将 使用 T_Abs 来 做 到 这一点，所以 仍然 需要 展示： Γ,y:T[11] ⊢ if beq_id x y then t[0] else [x:=v]t[0] : T[12] 我们 考虑 两种 情况：x = y 和 x ≠ y。 *)

apply T_Abs...

destruct (beq_idP x y).

+ (* x=y *)

(* 如果 x = y，则替换没有影响。上下文不变性表明 Γ,y:U,y:T[11] 和 Γ,y:T[11] 是等价的。由于前者上下文表明 t[0] : T[12]，所以后者也是。*)

应用 context_invariance...

替换。

对 x Hafi 进行引入。展开 update，t_update。

分情况讨论 (beq_id y x)...

+ (* x<>y *)

(* 如果 x ≠ y，则 IH 和上下文不变性允许我们展示          Γ,x:U,y:T[11] ⊢ t[0] : T[12]       =>          Γ,y:T[11],x:U ⊢ t[0] : T[12]       =>          Γ,y:T[11] ⊢ [x:=v]t[0] : T[12] *)

应用 IHt。应用 context_invariance...

对 z Hafi 进行引入。展开 update，t_update。

分情况讨论 (beq_idP y z)...

替换。重写 false_beq_id...

    证毕。

定理保持性质：∀t t' T，

有类型 empty t T →

t ⇒ t' →

有类型 empty t' T。

    证明与 eauto。

对于 t t' T HT。

(* 定理：如果 empty ⊢ t : T 并且 t ⇒ t'，那么 empty ⊢ t' : T。*)

记住 (@empty ty) 为 Γ。推广 HeqGamma。

推广 t'。

(* 证明：对给定的类型推导进行归纳。许多情况是矛盾的（T_Var，T_Abs）。我们只展示有趣的情况。*)

对 HT 进行归纳；

引入 t' HeqGamma HE；替换；反演 HE；替换...

- (* T_App *)

(* 如果最后使用的规则是 T_App，则 t = t[1] t[2]，并且有三个规则可以用来展示 t ⇒ t'：ST_App1，ST_App2 和 ST_AppAbs。在前两种情况下，结果直接从 IH 得出。*)

反演 HE；替换...

+ (* ST_AppAbs *)

(* 对于第三种情况，假设            t[1] = tabs x T[11] t[12]          且            t[2] = v[2]。          我们必须证明 empty ⊢ [x:=v[2]]t[12] : T[2]。          根据假设我们知道              empty ⊢ tabs x T[11] t[12] : T[1]→T[2]          并且根据反演              x:T[1] ⊢ t[12] : T[2]          我们已经证明了替换保持类型和              empty ⊢ v[2] : T[1]          所以我们完成了。*)

应用 substitution_preserves_typing with T[1]...

反演 HT[1]...

- (* T_Fst *)

反演 HT...

- (* T_Snd *)

反演 HT...

    证毕。

```

### Determinism

```

引理步骤唯一性：

唯一性步骤。

    证明与 eauto。

展开 deterministic。

对 t t' t'' E[1] E[2]。

推广 t''。

对 E[1] 进行归纳；引入 t'' E[2]；反演 E[2]；替换；清除 E[2]...

(* ST_AppAbs *)

- 反演 H[3]。

- 反证法；在 H 中应用 value__normal...

(* ST_App1 *)

- 反演 E[1]。

- 相等...

- 反证法；在 H[1] 中应用 value__normal...

(* ST_App2 *)

- 反证法；在 H[3] 中应用 value__normal...

- 反证法；在 H 中应用 value__normal...

- 相等...

(* ST_Pair1 *)

- 相等...

- 矛盾；应用 value__normal 到 H[1]...

(* ST_Pair2 *)

- 矛盾；应用 value__normal 到 H...

- 相等...

(* ST_Fst *)

- 相等...

- 矛盾。

反转 E[1]；替换。

+ 应用 value__normal 到 H[0]...

+ 应用 value__normal 到 H[1]...

(* ST_FstPair *)

- 矛盾。

反转 H[2]；替换。

+ 应用 value__normal 到 H...

+ 应用 value__normal 到 H[0]...

(* ST_Snd *)

- 相等...

- 矛盾。

反转 E[1]；替换。

+ 应用 value__normal 到 H[0]...

+ 应用 value__normal 到 H[1]...

(* ST_SndPair *)

- 矛盾。

反转 H[2]；替换。

+ 应用 value__normal 到 H...

+ 应用 value__normal 到 H[0]...

- (* ST_IfTrue *)

反转 H[3]。

- (* ST_IfFalse *)

反转 H[3]。

(* ST_If *)

- 反转 E[1]。

- 反转 E[1]。

- 相等...

    完成。

```

# Normalization

    Now for the actual normalization proof.

    Our goal is to prove that every well-typed term reduces to a
    normal form.  In fact, it turns out to be convenient to prove
    something slightly stronger, namely that every well-typed term
    reduces to a *value*.  This follows from the weaker property
    anyway via Progress (why?) but otherwise we don't need Progress,
    and we didn't bother re-proving it above.

    Here's the key definition:

```

定义终止（t:tm）：Prop :=  ∃t'，t ⇒* t' ∧  value t'。

```

    A trivial fact:

```

引理 value_halts : ∀v, value v → v 终止。

    证明。

intros v H. 展开 halts。

∃v. 分割。

应用 multi_refl。

假设。

    完成。

```

    The key issue in the normalization proof (as in many proofs by
    induction) is finding a strong enough induction hypothesis.  To
    this end, we begin by defining, for each type T, a set R_T of
    closed terms of type T.  We will specify these sets using a
    relation R and write R T t when t is in R_T. (The sets
    R_T are sometimes called *saturated sets* or *reducibility candidates*.)

    Here is the definition of R for the base language:

*   R bool t iff t is a closed term of type bool and t halts in a value 

*   R (T[1] → T[2]) t iff t is a closed term of type T[1] → T[2] and t halts in a value *and* for any term s such that R T[1] s, we have R T[2] (t s).

    This definition gives us the strengthened induction hypothesis that we
    need.  Our primary goal is to show that all *programs* —-i.e., all
    closed terms of base type—-halt.  But closed terms of base type can
    contain subterms of functional type, so we need to know something
    about these as well.  Moreover, it is not enough to know that these
    subterms halt, because the application of a normalized function to a
    normalized argument involves a substitution, which may enable more
    reduction steps.  So we need a stronger condition for terms of
    functional type: not only should they halt themselves, but, when
    applied to halting arguments, they should yield halting results.

    The form of R is characteristic of the *logical relations* proof
    technique.  (Since we are just dealing with unary relations here, we
    could perhaps more properly say *logical properties*.)  If we want to
    prove some property P of all closed terms of type A, we proceed by
    proving, by induction on types, that all terms of type A *possess*
    property P, all terms of type A→A *preserve* property P, all
    terms of type (A→A)->(A→A) *preserve the property of preserving*
    property P, and so on.  We do this by defining a family of
    properties, indexed by types.  For the base type A, the property is
    just P.  For functional types, it says that the function should map
    values satisfying the property at the input type to values satisfying
    the property at the output type.

    When we come to formalize the definition of R in Coq, we hit a
    problem.  The most obvious formulation would be as a parameterized
    Inductive proposition like this:

```

归纳 R : ty → tm → Prop :=

| R_bool : ∀b t，has_type empty t TBool →

t 终止 →

R TBool t

| R_arrow : ∀T[1] T[2] t，has_type empty t (TArrow T[1] T[2]) →

t 终止 →

(∀s，R T[1] s → R T[2] (tapp t s)) →

R (TArrow T[1] T[2]) t。

    不幸的是，Coq 拒绝这个定义，因为它违反了

    *严格的正性要求*对于归纳定义，它说

    被定义的类型不能出现在箭头的左边

    构造函数参数的类型。在这里，它是第三个参数

    R_arrow，即 (∀ s, R T[1] s → R TS (tapp t s))，以及

    具体来说，R T[1] s 部分，这违反了这个规则。（该

    最外层的箭头分隔构造函数参数不计算

    应用此规则；否则我们永远无法真正归纳

    任何性质！）规则的原因是，定义的类型

    与非正递归一起可用于构建非终止

    函数，正如我们所知，这对于 Coq 的逻辑

    正当性。即使在这种情况下我们想要的关系可能是

    完全无辜，Coq 仍然拒绝它，因为它违反了

    正性测试。

    幸运的是，事实证明我们*可以*使用

    Fixpoint：

```
Fixpoint R (T:ty) (t:tm) {struct T} : Prop :=
  has_type empty t T ∧ halts t ∧
  (match T with
   | TBool  ⇒ True
   | TArrow T[1] T[2] ⇒ (∀s, R T[1] s → R T[2] (tapp t s))

   (* ... edit the next line when dealing with products *)
   | TProd T[1] T[2] ⇒ False 
   end).

```

    作为这个定义的直接结果，我们有每个

    每个集合 R_T 的元素在一个值中终止��且具有类型

    t：

```
Lemma R_halts : ∀{T} {t}, R T t → halts t.

    Proof.
  intros. destruct T; unfold R in H; inversion H; inversion H[1];  assumption.
    Qed.

Lemma R_typable_empty : ∀{T} {t}, R T t → has_type empty t T.

    Proof.
  intros. destruct T; unfold R in H; inversion H; inversion H[1]; assumption.
    Qed.

```

    现在我们继续展示主要结果，即每个

    类型为 T 的良型项是 R_T 的元素。连同

    R 终止，这将展示每个良型项在

    value。

```

## Membership in R_T Is Invariant Under Reduction

    We start with a preliminary lemma that shows a kind of strong
    preservation property, namely that membership in R_T is *invariant*
    under reduction. We will need this property in both directions,
    i.e., both to show that a term in R_T stays in R_T when it takes a
    forward step, and to show that any term that ends up in R_T after a
    step must have been in R_T to begin with.

    First of all, an easy preliminary lemma. Note that in the forward
    direction the proof depends on the fact that our language is
    determinstic. This lemma might still be true for nondeterministic
    languages, but the proof would be harder!

```

引理 step_preserves_halting : ∀t t'，(t ⇒ t') → (t 终止 ↔ t' 终止)。

    证明。

intros t t' ST. 展开 halts.

分割。

- (* -> *)

intros [t'' [STM V]]。

反转 STM；替换。

矛盾。应用 value__normal 中的 V。在 V 中展开 normal_form。应用 V。∃t'。自动。

重写(step_deterministic _ _ _ ST H)。∃t''。分裂；假设。

- (* <- *)

intros [t'0 [STM V]]。

∃t'0。分裂；自动。

    完成。

```

    Now the main lemma, which comes in two parts, one for each
    direction.  Each proceeds by induction on the structure of the type
    T. In fact, this is where we make fundamental use of the
    structure of types.

    One requirement for staying in R_T is to stay in type T. In the
    forward direction, we get this from ordinary type Preservation.

```

引理 step_preserves_R : ∀T t t'，(t ⇒ t') → R T t → R T t'。

    证明。

对 T 进行归纳；intros t t' E Rt；展开 R；折叠 R；在 Rt 中展开 R；在 Rt 中折叠 R；

将 Rt 分解为[typable_empty_t [halts_t RRt]]。

(* TBool *)

分裂。应用 preservation；自动。

分裂。应用(step_preserves_halting _ _ E)；自动。

自动。

(* TArrow *)

分裂。应用 preservation；自动。

分裂。应用(step_preserves_halting _ _ E)；自动。

intros。

应用 IHT2。

应用 ST_App1。应用 E。

应用 RRt；自动。

(* 填写此处 *) 已留空。

```

    The generalization to multiple steps is trivial:

```

引理 multistep_preserves_R : ∀T t t'，

(t ⇒* t') → R T t → R T t'。

    证明。

intros T t t' STM；对 STM 进行归纳；intros。

假设。

应用 IHSTM。应用 step_preserves_R。应用 H。假设。

    完成。

```

    In the reverse direction, we must add the fact that t has type
   T before stepping as an additional hypothesis.

```

引理 step_preserves_R' : ∀T t t'，

has_type empty t T → (t ⇒ t') → R T t' → R T t。

    证明。

(* 填写此处 *) 已留空。

引理 multistep_preserves_R' : ∀T t t'，

has_type empty t T → (t ⇒* t') → R T t' → R T t。

    证明。

intros T t t' HT STM。

对 STM 进行归纳；intros。

假设。

应用 step_preserves_R'。假设。应用 H。应用 IHSTM。

应用 preservation；自动。自动。

    完成。

```

## Closed Instances of Terms of Type t Belong to R_T

    Now we proceed to show that every term of type T belongs to
    R_T.  Here, the induction will be on typing derivations (it would be
    surprising to see a proof about well-typed terms that did not
    somewhere involve induction on typing derivations!).  The only
    technical difficulty here is in dealing with the abstraction case.
    Since we are arguing by induction, the demonstration that a term
    tabs x T[1] t[2] belongs to R_(T[1]→T[2]) should involve applying the
    induction hypothesis to show that t[2] belongs to R_(T[2]).  But
    R_(T[2]) is defined to be a set of *closed* terms, while t[2] may
    contain x free, so this does not make sense.

    This problem is resolved by using a standard trick to suitably
    generalize the induction hypothesis: instead of proving a statement
    involving a closed term, we generalize it to cover all closed
    *instances* of an open term t.  Informally, the statement of the
    lemma will look like this:

    If x[1]:T[1],..xn:Tn ⊢ t : T and v[1],...,vn are values such that
    R T[1] v[1], R T[2] v[2], ..., R Tn vn, then
    R T ([x[1]:=v[1]][x[2]:=v[2]]...[xn:=vn]t).

    The proof will proceed by induction on the typing derivation
    x[1]:T[1],..xn:Tn ⊢ t : T; the most interesting case will be the one
    for abstraction.

```

### 多次替换，多次扩展和实例化

    然而，在我们继续正式陈述之前

    证明引理，我们需要构建一些（相当乏味的）

    处理我们正在执行*多次*

    对项 t 进行替换和*多次*扩展的

    上下文。特别是，我们必须准确说明

    替换发生以及它们如何相互作用。通常这些

    在非正式的论文证明中，细节通常被省略，但当然 Coq

    不会让我们这样做。因为这里我们正在替换闭合项，我们

    不需要担心一个替换如何影响项

    由另一个放置。但我们仍然需要担心

    *替换的顺序*，因为同一个

    标识符在 x[1],...xn 中多次出现

    不同的相关 vi 和 Ti。

    为了使一切准确，我们将假设环境是

    从左到右扩展，并执行多次替换

    从右到左。为了看到这是一致的，假设我们有

    一个环境写为...,y:bool,...,y:nat,... 和一个

    对应项替换写为...[y:=(tbool true)]...[y:=(tnat 3)]...t。由于环境是从

    从左到右，绑定 y:nat 隐藏了绑定 y:bool；因为

    替换是从右向左执行的，我们对替换

    首先执行 y:=(tnat 3)，因此替换 y:=(tbool true) 无效。

    没有影响。因此，替换正确地保留了术语的类型。

    牢记这些要点，以下定义应该就会有意义。

    *多重替换* 是应用列表的结果

    称之为 *环境* 的替换。

```
Definition env := list (id * tm).

Fixpoint msubst (ss:env) (t:tm) {struct ss} : tm :=
match ss with
| nil ⇒ t
| ((x,s)::ss') ⇒ msubst ss' ([x:=s]t)
end.

```

    我们需要类似的机制来讨论重复扩展

    使用一个 (标识符，类型) 对列表构建的类型上下文，我们

    称为 *类型赋值*。

```
Definition tass := list (id * ty).

Fixpoint mupdate (Γ : context) (xts : tass) :=
  match xts with
  | nil ⇒ Γ
  | ((x,v)::xts') ⇒ update (mupdate Γ xts') x v
  end.

```

    我们需要一些简单的操作，它们在

    环境和类型赋值

```
Fixpoint lookup {X:Set} (k : id) (l : list (id * X)) {struct l}
              : option X :=
  match l with
    | nil ⇒ None
    | (j,x) :: l' ⇒
      if beq_id j k then Some x else lookup k l'
  end.

Fixpoint drop {X:Set} (n:id) (nxs:list (id * X)) {struct nxs}
            : list (id * X) :=
  match nxs with
    | nil ⇒ nil
    | ((n',x)::nxs') ⇒
        if beq_id n' n then drop n nxs'
        else (n',x)::(drop n nxs')
  end.

```

    *实例化* 结合了类型赋值和值

    具有相同域的环境，在对应元素上

    在 R 中。

```
Inductive instantiation :  tass → env → Prop :=
| V_nil :
    instantiation nil nil
| V_cons : ∀x T v c e,
    value v → R T v →
    instantiation c e →
    instantiation ((x,T)::c) ((x,v)::e).

```

    现在我们继续证明这些定义的各种属性。

```

### More Substitution Facts

    First we need some additional lemmas on (ordinary) substitution.

```

Lemma vacuous_substitution : ∀ t x,

若 x 不出现在 t 中 →

∀t', [x:=t']t = t.

    证明，使用 eauto。

(* 在此填写内容 *) 已略过。

Lemma subst_closed: ∀t,

closed t  →

∀x t', [x:=t']t = t.

    证明。

intros。应用 vacuous_substitution。应用 H。证毕。

Lemma subst_not_afi : ∀t x v,

closed v →  x 不出现在 ([x:=v]t) 中。

    证明，使用 eauto。 (* 这种方式相对较慢 *)

展开 closed，[not](http://coq.inria.fr/library/Coq.Init.Logic.html#not)。

对 t 进行归纳；对 x v P A 进行引入；A 简化。

- (* tvar *)

destruct (beq_idP x i)...

对 A 进行反演；替换。自动。

- (* tapp *)

对 A 进行反演；替换...

- (* 标签 *)

destruct (beq_idP x i)...

+ 对 A 进行反演；替换...

+ 对 A 进行反演；替换...

- (* tpair *)

对 A 进行反演；替换...

- (* tfst *)

对 A 进行反演；替换...

- (* tsnd *)

对 A 进行反演；替换...

- (* ttrue *)

对 A 进行反演。

- (* tfalse *)

对 A 进行反演。

- (* tif *)

对 A 进行反演；替换...

    证毕。

Lemma duplicate_subst : ∀t' x t v,

closed v → x:=t = [x:=v]t'。

    证明。

intros。应用 vacuous_substitution。应用 subst_not_afi。自动。

    证毕。

Lemma swap_subst : ∀t x x[1] v v[1],

x ≠ x[1] →

closed v → closed v[1] →

[x[1]:=v[1]]([x:=v]t) = x:=v.

    证明，使用 eauto。

对 t 进行归纳；引入；简化。

- (* tvar *)

destruct (beq_idP x i); destruct (beq_idP x[1] i).

+ 替换。矛盾...

+ 替换。简化。重写 ← beq_id_refl。应用 subst_closed...

+ 替换。简化。重写 ← beq_id_refl。重写 subst_closed...

+ 简化。重写 false_beq_id... 重写 false_beq_id...

(* 在此填写内容 *) 已略过。

```

### Properties of Multi-Substitutions

```

Lemma msubst_closed: ∀t, closed t → ∀ss, msubst ss t = t.

    证明。

对 ss 进行归纳。

自反性。

destruct a. 简化。重写 subst_closed; 假设成立。

    证毕。

```

    Closed environments are those that contain only closed terms.

```

Fixpoint closed_env (env:env) {struct env} :=

匹配 env 。

| nil ⇒ True

| (x,t)::env' ⇒ closed t ∧ closed_env env'

结束。

```

    Next come a series of lemmas charcterizing how msubst of closed terms
    distributes over subst and over each term form

```

Lemma subst_msubst: ∀env x v t, 闭合 v → 闭合环境 env →

msubst env ([x:=v]t) = x:=v t)。

    Proof.

归纳 env0；引入；自动。

分解 a。简化。

推导 H[0]。在 H[2] 中重写 closed_env。

分解 (beq_idP i x)。

- 替换。重写 duplicate_subst；自动。

- 简化。重写 swap_subst；自动。

    Qed。

Lemma msubst_var:  ∀ss x, 闭合环境 ss →

msubst ss (tvar x) =

匹配查找 x ss。

| Some t ⇒ t

| None ⇒ tvar x

end。

    Proof.

归纳 ss；引入。

反射性。

分解 a。

简化。分解 (beq_id i x)。

应用 msubst_closed。推导 H；自动。

应用 IHss。推导 H；自动。

    Qed.

Lemma msubst_abs: ∀ss x T t,

msubst ss (tabs x T t) = tabs x T (msubst (drop x ss) t)。

    Proof。

归纳 ss；引入。

反射性。

分解 a。

简化。分解 (beq_id i x)；简化；自动。

    Qed。

Lemma msubst_app : ∀ss t[1] t[2], msubst ss (tapp t[1] t[2]) = tapp (msubst ss t[1]) (msubst ss t[2]).

    Proof。

归纳 ss；引入。

自反性。

分解 a。

简化。重写 ← IHss。自动。

    Qed.

```

    You'll need similar functions for the other term constructors.

```

(* 在此填写内容 *)

```

### Properties of Multi-Extensions

    We need to connect the behavior of type assignments with that of
    their corresponding contexts.

```

Lemma mupdate_lookup : ∀(c : tass) (x:id),

查找 x c = (mupdate empty c) x。

    Proof.

归纳 c；引入。

自动。

分解 a。展开 lookup，mupdate，update，t_update。分解 (beq_id i x)；自动。

    Qed.

Lemma mupdate_drop : ∀(c: tass) Γ x x'，

mupdate Γ (drop x c) x'。

= 若 beq_id x x' 则 Γ x' 否则 mupdate Γ c x'。

    Proof。

归纳 c；引入。

- 分解 (beq_idP x x')；自动。

- 分解 a。简化。

分解 (beq_idP i x)。

+ 替换。重写 IHc。

展开 update，t_update。分解 (beq_idP x x')；自动。

+ 简化。展开 update，t_update。分解 (beq_idP i x')；自动。

替换。重写 false_beq_id；一致性。

    Qed。

```

### Properties of Instantiations

    These are strightforward.

```

Lemma instantiation_domains_match: ∀{c} {e},

实例化 c e →

∀{x} {T}，

查找 x c = Some T → ∃t, 查找 x e = Some t。

    Proof.

引入 c e V。归纳 V；引入 x[0] T[0] C。

解决反转。

简化。

分解 (beq_id x x[0])；自动。

    Qed.

Lemma instantiation_env_closed : ∀c e，

实例化 c e → 闭合环境 e.

    Proof.

引入 c e V；归纳 V；引入。

构造者。

展开 closed_env。重写 closed_env。

分割。应用 typable_empty__closed。应用 R_typable_empty。自动。

自动。

    Qed.

Lemma instantiation_R : ∀c e，

实例化 c e →

∀x t T，

查找 x c = Some T →

查找 x e = Some t → R T t。

    Proof.

引入 c e V。归纳 V；引入 x' t' T' G E。

解决反转。

展开 lookup。分解 (beq_id x x')。

推导 G；推导 E；替换。自动。

自动。

    Qed。

引理 instantiation_drop: ∀c env，

实例化 c env →

∀x，实例化 (drop x c) (drop x env)。

    证明。

intros c e V。对 V 进行归纳。

intros。简化。构造。

intros。展开 drop。解构 (beq_id x x[0]); 自动。构造; 自动。

    完成。

```

### Congruence Lemmas on Multistep

    We'll need just a few of these; add them as the demand arises.

```

引理 multistep_App2: ∀v t t'，

值 v → (t ⇒* t') → (tapp v t) ⇒* (tapp v t')。

    证明。

intros v t t' V STM。对 STM 进行归纳。

应用 multi_refl。

应用 multi_step。

应用 ST_App2; 自动。自动。

    完成。

(* 在此填写内容 *)

```

### The R Lemma.

    We can finally put everything together.

    The key lemma about preservation of typing under substitution can
    be lifted to multi-substitutions:

```

引理 msubst_preserves_typing: ∀c e,

实例化 c e →

∀Γ t S，有类型 (mupdate Γ c) t S →

有类型 Γ (msubst e t) S。

    证明。

对 1 进行归纳；intros。

简化 H。简化。自动。

H[2] 简化。简化。

应用 IHinstantiation。

应用 substitution_preserves_typing; 自动。

应用 (R_typable_empty H[0])。

    完成。

```

    And at long last, the main lemma.

```

引理 msubst_R: ∀c env t T，

有类型的 (mupdate empty c) t T →

实例化 c env →

R T (msubst env t)。

    证明。

intros c env0 t T HT V。

推广 env0。

(* 我们需要在进行归纳之前稍微概括一下假设。 *)

记住 (mupdate empty c) 为 Γ。

断言 (∀x, Γ x = lookup x c)。

intros。重写 HeqGamma。重写 mupdate_lookup。自动。

清除 HeqGamma。

推广 c。

对 HT 进行归纳；intros。

- (* T_Var *)

在 H 中重写 H[0]。将 (instantiation_domains_match V H) 解构为 [t P]。

应用 instantiation_R; 自动。

重写 msubst_var。重写 P。自动。应用 instantiation_env_closed; 自动。

- (* T_Abs *)

重写 msubst_abs。

(* 我们将需要以下事实的变体多次，因此最好只建立一次。 *)

断言 (WT: has_type empty (tabs x T[11] (msubst (drop x env0) t[12])) (TArrow T[11] T[12])).

{ 应用 T_Abs。应用 msubst_preserves_typing。

{ 应用 instantiation_drop; 自动。 }

应用 context_invariance。

{ 应用 HT。 }

intros。

展开 update, t_update。重写 mupdate_drop。解构 (beq_idP x x[0])。

+ 自动。

+ 重写 H。

清除 - c n。对 c 进行归纳。

简化。重写 false_beq_id; 自动。

简化。解构 a。展开 update, t_update。

解构 (beq_id i x[0]); 自动。}

展开 R。折叠 R。分割。

自动。

分解。应用 value_halts。应用 v_abs。

引入。

将(R_halts H[0])分解为[v [P Q]]。

引入证明(multistep_preserves_R _ _ _ P H[0])。

应用 multistep_preserves_R'，使用(msubst ((x,v)::env0) t[12])。

应用 T_App。自动。

应用 R_typable_empty; 自动。

应用 multi_trans。应用 multistep_App2; 自动。

应用 multi_R。

简化。重写 subst_msubst。

应用 ST_AppAbs; 自动。

应用 typable_empty__closed。

应用(R_typable_empty H[1])。

应用 instantiation_env_closed; 自动。

应用(IHHT ((x,T[11])::c))。

引入。展开 update，t_update，lookup。分解(beq_id x x[0]); 自动。

构造者; 自动。

- (* T_App *)

重写 msubst_app。

将 IHHT1 c H env0 V 的证明分解为[_ [_ P[1]]]。

将 IHHT2 c H env0 V 的证明命名为 P[2]。在 P[1]中折叠 R。自动。

(* 在此填写 *) 已承认。

```

### Normalization Theorem

```

定理规范化：∀t T，has_type empty t T → halts t。

    证明。

引入。

用(msubst [nil](http://coq.inria.fr/library/Coq.Init.Datatypes.html#nil) t)替换 t，通过反射性。

应用(@R_halts T)。

应用(msubst_R [nil](http://coq.inria.fr/library/Coq.Init.Datatypes.html#nil)); 自动。

应用 V_nil。

    完成。

```

```

```

```

```

```

```

```
