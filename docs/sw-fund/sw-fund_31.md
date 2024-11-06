# 记录子子类型与记录

```

    In this chapter, we combine two significant extensions of the pure
    STLC — records (from chapter Records) and subtyping (from
    chapter Sub) — and explore their interactions.  Most of the
    concepts have already been discussed in those chapters, so the
    presentation here is somewhat terse.  We just comment where things
    are nonstandard.

```

导入 Maps。

导入 Smallstep。

导入 MoreStlc。

```

# Core Definitions

```

### 语法

```
Inductive ty : Type :=
  (* proper types *)
  | TTop   : ty
  | TBase  : id → ty
  | TArrow : ty → ty → ty
  (* record types *)
  | TRNil : ty
  | TRCons : id → ty → ty → ty.

Inductive tm : Type :=
  (* proper terms *)
  | tvar : id → tm
  | tapp : tm → tm → tm
  | tabs : id → ty → tm → tm
  | tproj : tm → id → tm
  (* record terms *)
  | trnil :  tm
  | trcons : id → tm → tm → tm.

```

### 良好形式性

    术语和类型的语法有点太松散，意思是

    它允许像记录类型一样的东西，其最终的“尾部”是

    顶部或某个箭头类型而不是 Nil。为了避免这种情况，

    假设所有记录类型和术语都是

    看看是否遵守一些简单的良好形式性条件。

    一个有趣的技术问题是，如果我们放弃这些条件，系统的基本属性 -- 进展和保留 -- 是否仍然成立。我相信它们是成立的，并鼓励有动力的读者尝试通过从类型和子类型的定义中删除这些条件，并相应地调整本章中的证明来验证这一点。这不是一个琐碎的练习（否则我会做的！），但不应涉及更改证明的基本结构。如果有人这样做了，请告诉我。--BCP 5/16.

```
Inductive record_ty : ty → Prop :=
  | RTnil :
        record_ty TRNil
  | RTcons : ∀i T[1] T[2],
        record_ty (TRCons i T[1] T[2]).

Inductive record_tm : tm → Prop :=
  | rtnil :
        record_tm trnil
  | rtcons : ∀i t[1] t[2],
        record_tm (trcons i t[1] t[2]).

Inductive well_formed_ty : ty → Prop :=
  | wfTTop :
        well_formed_ty TTop
  | wfTBase : ∀i,
        well_formed_ty (TBase i)
  | wfTArrow : ∀T[1] T[2],
        well_formed_ty T[1] →
        well_formed_ty T[2] →
        well_formed_ty (TArrow T[1] T[2])
  | wfTRNil :
        well_formed_ty TRNil
  | wfTRCons : ∀i T[1] T[2],
        well_formed_ty T[1] →
        well_formed_ty T[2] →
        record_ty T[2] →
        well_formed_ty (TRCons i T[1] T[2]).

Hint Constructors record_ty record_tm well_formed_ty.

```

### 替换

    替换和减少与以前一样。

```
Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar y ⇒ if beq_id x y then s else t
  | tabs y T t[1] ⇒  tabs y T (if beq_id x y then t[1]
                             else (subst x s t[1]))
  | tapp t[1] t[2] ⇒ tapp (subst x s t[1]) (subst x s t[2])
  | tproj t[1] i ⇒ tproj (subst x s t[1]) i
  | trnil ⇒ trnil
  | trcons i t[1] tr[2] ⇒ trcons i (subst x s t[1]) (subst x s tr[2])
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

```

### 减少

```
Inductive value : tm → Prop :=
  | v_abs : ∀x T t,
      value (tabs x T t)
  | v_rnil : value trnil
  | v_rcons : ∀i v vr,
      value v →
      value vr →
      value (trcons i v vr).

Hint Constructors value.

Fixpoint Tlookup (i:id) (Tr:ty) : option ty :=
  match Tr with
  | TRCons i' T Tr' ⇒
      if beq_id i i' then Some T else Tlookup i Tr'
  | _ ⇒ None
  end.

Fixpoint tlookup (i:id) (tr:tm) : option tm :=
  match tr with
  | trcons i' t tr' ⇒
      if beq_id i i' then Some t else tlookup i tr'
  | _ ⇒ None
  end.

Reserved Notation "t1 '⇒' t2" (at level 40).

Inductive step : tm → tm → Prop :=
  | ST_AppAbs : ∀x T t[12] v[2],
         value v[2] →
         (tapp (tabs x T t[12]) v[2]) ⇒ [x:=v[2]]t[12]
  | ST_App1 : ∀t[1] t[1]' t[2],
         t[1] ⇒ t[1]' →
         (tapp t[1] t[2]) ⇒ (tapp t[1]' t[2])
  | ST_App2 : ∀v[1] t[2] t[2]',
         value v[1] →
         t[2] ⇒ t[2]' →
         (tapp v[1] t[2]) ⇒ (tapp v[1]  t[2]')
  | ST_Proj1 : ∀tr tr' i,
        tr ⇒ tr' →
        (tproj tr i) ⇒ (tproj tr' i)
  | ST_ProjRcd : ∀tr i vi,
        value tr →
        tlookup i tr = Some vi    →
       (tproj tr i) ⇒ vi
  | ST_Rcd_Head : ∀i t[1] t[1]' tr[2],
        t[1] ⇒ t[1]' →
        (trcons i t[1] tr[2]) ⇒ (trcons i t[1]' tr[2])
  | ST_Rcd_Tail : ∀i v[1] tr[2] tr[2]',
        value v[1] →
        tr[2] ⇒ tr[2]' →
        (trcons i v[1] tr[2]) ⇒ (trcons i v[1] tr[2]')

where "t1 '⇒' t2" := (step t[1] t[2]).

Hint Constructors step.

```

# 子类型

    现在我们来到有趣的部分，在这里我们

    添加开始进行交互。我们首先通过定义子类型来开始

    关系并发展一些重要的技术

    属性。

```

## Definition

    The definition of subtyping is essentially just what we sketched
    in the discussion of record subtyping in chapter Sub, but we
    need to add well-formedness side conditions to some of the rules.
    Also, we replace the "n-ary" width, depth, and permutation
    subtyping rules by binary rules that deal with just the first
    field.

```

保留的符号“T '<:' U”（在级别 40 处）。

形成子类型关系：ty → ty → Prop :=

(* 适当类型之间的子类型关系 *)

| S_Refl : ∀T,

良好形式性 T →

T <: T

| S_Trans : ∀S U T,

S <: U →

U <: T →

S <: T

| S_Top : ∀S，

良好形式性 S →

S <: TTop

| S_Arrow : ∀S[1] S[2] T[1] T[2]，

T[1] <: S[1] →

S[2] <: T[2] →

S[1] S[2] <: T[1] T[2]

(* 记录类型之间的子类型关系 *)

| S_RcdWidth : ∀i T[1] T[2]，

良好形式性（TRCons i T[1] T[2]）→

TRCons i T[1] T[2] <: TRNil

| S_RcdDepth : ∀i S[1] T[1] Sr[2] Tr[2]，

S[1] <: T[1] →

Sr[2] <: Tr[2] →

记录类型 Sr[2] →

记录类型 Tr[2] →

TRCons i S[1] Sr[2] <: TRCons i T[1] Tr[2]

| S_RcdPerm : ∀i[1] i[2] T[1] T[2] Tr[3]，

良好形式性（TRCons i[1] T[1]（TRCons i[2] T[2] Tr[3]））→

i[1] ≠ i[2] →

TRCons i[1] T[1] (TRCons i[2] T[2] Tr[3])

<: TRCons i[2] T[2] (TRCons i[1] T[1] Tr[3])

其中“T '<:' U” :=（subtype T U）。

提示构造子子类型。

```

## Examples

```

模块示例。

定义 x := (Id "x")。

定义 y := (Id "y")。

定义 z := (Id "z")。

定义 j := (Id "j")。

定义 k := (Id "k")。

定义 i := (Id "i")。

定义 A := (TBase (Id "A")).

定义 B := (TBase (Id "B")).

定义 C := (TBase（Id "C"））。

定义 TRcd_j  :=

（TRCons j（TArrow B B）TRNil）。（{j:B->B}）

定义 TRcd_kj :=

TRCons k（TArrow A A）TRcd_j。 （{k:C->C,j:B->B}）

示例子类型示例 _0：

subtype (TArrow C TRcd_kj)

（TArrow C TRNil）。

(* C->{k:A->A,j:B->B} <: C->{} *)

证明。

应用 S_Arrow。

应用 S_Refl。auto.

展开 TRcd_kj，TRcd_j。应用 S_RcdWidth; auto.

完成。

```

    The following facts are mostly easy to prove in Coq.  To get full
    benefit, make sure you also understand how to prove them on
    paper! 

#### Exercise: 2 stars (subtyping_example_1)

```

示例子类型示例 _1：

subtype TRcd_kj TRcd_j。

(* {k:A->A,j:B->B} <: {j:B->B} *)

使用 eauto 进行证明。

(* 在此填写 *) 已承认。

```

    ☐ 

#### Exercise: 1 star (subtyping_example_2)

```

示例子类型示例 _2：

subtype (TArrow TTop TRcd_kj)

（TArrow（TArrow C C）TRcd_j）。

（Top->{k:A->A,j:B->B} <: (C->C)->{j:B->B}）

Proof with eauto.

（填写此处） Admitted。

```

    ☐ 

#### Exercise: 1 star (subtyping_example_3)

```

举例 subtyping_example_3：

subtype (TArrow TRNil (TRCons j A TRNil))

（TArrow (TRCons k B TRNil) TRNil）。

（{}->{j:A} <: {k:B}->{}）

Proof with eauto。

（填写此处） Admitted.

```

    ☐ 

#### Exercise: 2 stars (subtyping_example_4)

```

举例 subtyping_example_4：

subtype (TRCons x A (TRCons y B (TRCons z C TRNil)))

（TRCons z C (TRCons y B (TRCons x A TRNil))）。

（{x:A,y:B,z:C} <: {z:C,y:B,x:A}）

Proof with eauto.

（填写此处） Admitted。

```

    ☐

```

结束示例。

```

## Properties of Subtyping

### Well-Formedness

    To get started proving things about subtyping, we need a couple of
    technical lemmas that intuitively (1) allow us to extract the
    well-formedness assumptions embedded in subtyping derivations
    and (2) record the fact that fields of well-formed record types
    are themselves well-formed types.

```

引理 subtype__wf：∀S T，

subtype S T →

well_formed_ty T ∧ well_formed_ty S.

    Proof with eauto。

intros S T Hsub.

induction Hsub;

intros; try (destruct IHHsub1; destruct IHHsub2)...

- （S_RcdPerm）

split... inversion H. subst. inversion H[5]... Qed.

引理 wf_rcd_lookup：∀i T Ti，

well_formed_ty T →

Tlookup i T = Some Ti →

well_formed_ty Ti.

    Proof with eauto。

intros i T。

IHT; intros; try solve_by_invert。

- （TRCons）

inversion H。subst。在 H[0] 中展开 Tlookup。

destruct (beq_id i i[0])... inversion H[0]; subst... Qed。

```

### Field Lookup

    The record matching lemmas get a little more complicated in the
    presence of subtyping, for two reasons.  First, record types no
    longer necessarily describe the exact structure of the
    corresponding terms.  And second, reasoning by induction on typing
    derivations becomes harder in general, because typing is no longer
    syntax directed.

```

引理 rcd_types_match：∀S T i Ti，

subtype S T →

Tlookup i T = Some Ti →

∃Si，Tlookup i S = Some Si ∧ subtype Si Ti。

    Proof with (eauto using wf_rcd_lookup).

intros S T i Ti Hsub Hget. generalize dependent Ti.

induction Hsub; intros Ti Hget;

try solve_by_invert。

- （S_Refl）

∃Ti...

- （S_Trans）

destruct (IHHsub2 Ti) as [Ui Hui]... destruct Hui.

destruct (IHHsub1 Ui) as [Si Hsi]... destruct Hsi.

∃Si...

- （S_RcdDepth）

将 i[0] 重命名为 k。

展开 Tlookup。在 Hget 中展开 Tlookup。

destruct (beq_id i k)...

+ （i = k -- 我们正在查找第一个字段）

inversion Hget. subst. ∃S[1]...

- （S_RcdPerm）

∃Ti. split.

+ （查找）

展开 Tlookup。在 Hget 中展开 Tlookup。

destruct (beq_idP i i[1])...

* （i = i[1] -- 我们正在查找第一个字段）

destruct (beq_idP i i[2])...

（i = i[2] -- 矛盾）

destruct H[0].

subst...

+ （subtype）

inversion H. subst. inversion H[5]. subst... Qed.

```

#### Exercise: 3 stars (rcd_types_match_informal)

    Write a careful informal proof of the rcd_types_match
    lemma.

```

（填写此处）

```

    ☐ 

### Inversion Lemmas

#### Exercise: 3 stars, optional (sub_inversion_arrow)

```

引理 sub_inversion_arrow：∀U V[1] V[2]，

subtype U (TArrow V[1] V[2]) →

∃U[1], ∃U[2]，

（U=(TArrow U[1] U[2])) ∧ (subtype V[1] U[1]) ∧ (subtype U[2] V[2])。

    Proof with eauto.

intros U V[1] V[2] Hs。

remember (TArrow V[1] V[2]) as V。

generalize dependent V[2]。generalize dependent V[1]。

（填写此处） Admitted。

    ☐

# 输入

```
Definition context := partial_map ty.

Reserved Notation "Gamma '⊢' t '∈' T" (at level 40).

Inductive has_type : context → tm → ty → Prop :=
  | T_Var : ∀Γ x T,
      Γ x = Some T →
      well_formed_ty T →
      Γ ⊢ tvar x ∈ T
  | T_Abs : ∀Γ x T[11] T[12] t[12],
      well_formed_ty T[11] →
      update Γ x T[11] ⊢ t[12] ∈ T[12] →
      Γ ⊢ tabs x T[11] t[12] ∈ TArrow T[11] T[12]
  | T_App : ∀T[1] T[2] Γ t[1] t[2],
      Γ ⊢ t[1] ∈ TArrow T[1] T[2] →
      Γ ⊢ t[2] ∈ T[1] →
      Γ ⊢ tapp t[1] t[2] ∈ T[2]
  | T_Proj : ∀Γ i t T Ti,
      Γ ⊢ t ∈ T →
      Tlookup i T = Some Ti →
      Γ ⊢ tproj t i ∈ Ti
  (* Subsumption *)
  | T_Sub : ∀Γ t S T,
      Γ ⊢ t ∈ S →
      subtype S T →
      Γ ⊢ t ∈ T
  (* Rules for record terms *)
  | T_RNil : ∀Γ,
      Γ ⊢ trnil ∈ TRNil
  | T_RCons : ∀Γ i t T tr Tr,
      Γ ⊢ t ∈ T →
      Γ ⊢ tr ∈ Tr →
      record_ty Tr →
      record_tm tr →
      Γ ⊢ trcons i t tr ∈ TRCons i T Tr

where "Gamma '⊢' t '∈' T" := (has_type Γ t T).

Hint Constructors has_type.

```

## 类型示例

```
Module Examples2.
Import Examples.

```

#### 练习：1 星（typing_example_0）

```
Definition trcd_kj :=
  (trcons k (tabs z A (tvar z))
           (trcons j (tabs z B (tvar z))
                      trnil)).

Example typing_example_0 :
  has_type empty
           (trcons k (tabs z A (tvar z))
                     (trcons j (tabs z B (tvar z))
                               trnil))
           TRcd_kj.
(* empty |- {k=(λz:A.z), j=(λz:B.z)} : {k:A->A,j:B->B} *)

    Proof.
  (* FILL IN HERE *) Admitted.

    ☐

#### Exercise: 2 stars (typing_example_1)

```

举例 typing_example_1：

has_type empty

（tapp (tabs x TRcd_j (tproj (tvar x) j))

（trcd_kj）

（TArrow B B）。

（empty |- (λx:{k:A->A,j:B->B}. x.j)   {k=(λz:A.z), j=(λz:B.z)} : B->B）

    Proof with eauto.

（填写此处） Admitted.

    ☐

#### 练习：2 星，可选（typing_example_2）

```
Example typing_example_2 :
  has_type empty
           (tapp (tabs z (TArrow (TArrow C C) TRcd_j)
                           (tproj (tapp (tvar z)
                                            (tabs x C (tvar x)))
                                    j))
                   (tabs z (TArrow C C) trcd_kj))
           (TArrow B B).
(* empty |- (λz:(C->C)->{j:B->B}. (z (λx:C.x)).j)               (λz:C->C. {k=(λz:A.z), j=(λz:B.z)})            : B->B *)

    Proof with eauto.
  (* FILL IN HERE *) Admitted.

    ☐

End Examples2.

## Properties of Typing

### Well-Formedness

```

引理 has_type__wf：∀Γ t T。

has_type Γ t T → well_formed_ty T.

    Proof with eauto。

引言 Γ t T Htyp。

对 Htyp 进行归纳...

- (* T_App *)

反演 IHHtyp1...

- (* T_Proj *)

应用 wf_rcd_lookup...

- (* T_Sub *)

应用 subtype__wf 到 H。

解构 H...

    完毕。

引理 步骤保持记录项: ∀tr tr',

记录项 tr →

tr ⇒ tr' →

记录项 tr'。

    证明。

引言 tr tr' Hrt Hstp。

反演 Hrt; 替换; 反演 Hstp; 替换; eauto。

    完毕。

```

### Field Lookup

```

引理 在值中查找字段: ∀v T i Ti,

value v →

has_type empty v T →

Tlookup i T = Some Ti →

∃vi, tlookup i v = Some vi ∧ has_type empty vi Ti。

    证明与 eauto。

记住 empty 为 Γ。

引言 t T i Ti Hval Htyp。 反转 Ti HeqGamma Hval。

对 Htyp 进行归纳; 引言; 替换; 尝试通过反演解决。

- (* T_Sub *)

应用 (rcd_types_match S) 到 H[0]...

解构 H[0] 为 [Si [HgetSi Hsub]]。

解构 (IHHtyp Si) 为 [vi [Hget Htyvi]]...

- (* T_RCons *)

在 H[0] 中简化。 简化。 在 H[1] 中简化。

解构 (beq_id i i[0])。

+ (* i 首先出现 *)

反演 H[1]。 替换。 ∃t...

+ (* i 在尾部 *)

解构 (IHHtyp2 Ti) 为 [vi [get Htyvi]]...

反演 Hval... 完毕。

```

### Progress

#### Exercise: 3 stars (canonical_forms_of_arrow_types)

```

引理 箭头类型的规范形式: ∀Γ s T[1] T[2],

has_type Γ s (TArrow T[1] T[2]) →

value s →

∃x, ∃S[1], ∃s[2],

s = tabs x S[1] s[2]。

    证明与 eauto。

(* 在此填写 *) 仍需完成。

    ☐

定理 进展: ∀t T,

has_type empty t T →

value t ∨ ∃t', t ⇒ t'。

    证明与 eauto。

引言 t T Ht。

记住 empty 为 Γ。

反转 HeqGamma。

对 Ht 进行归纳;

引言 HeqGamma; 替换...

- (* T_Var *)

反演 H。

- (* T_App *)

正确。

解构 IHHt1; 替换...

+ (* t[1] 是一个值 *)

解构 IHHt2; 替换...

* (* t[2] 是一个值 *)

解构 (canonical_forms_of_arrow_types empty t[1] T[1] T[2])

如 [x [S[1] [t[12] Heqt1]]]...

替换。 ∃([x:=t[2]]t[12])...

* (* t[2] 步骤 *)

解构 H[0] 为 [t[2]' Hstp]。 ∃(tapp t[1] t[2]')...

+ (* t[1] 步骤 *)

解构 H 为 [t[1]' Hstp]。 ∃(tapp t[1]' t[2])...

- (* T_Proj *)

正确。 解构 IHHt...

+ (* rcd 是值 *)

解构 (lookup_field_in_value t T i Ti)

为 [t' [Hget Ht']]...

+ (* rcd_steps *)

解构 H[0] 为 [t' Hstp]。 ∃(tproj t' i)...

- (* T_RCons *)

解构 IHHt1...

+ (* 头部 是一个值 *)

解构 IHHt2...

* (* 尾部 步骤 *)

正确。 解构 H[2] 为 [tr' Hstp]。

∃(trcons i t tr')...

+ (* 头部 步骤 *)

正确。 解构 H[1] 为 [t' Hstp]。

∃(trcons i t' tr)... 完毕。

    *定理* : 对于任意项 t 和类型 T，如果 empty ⊢ t : T

    那么 t 是一个值或者 t ⇒ t' 对于某个项 t'。

    *证明*: 设 t 和 T 给定，使得 empty ⊢ t : T。 我们

    根据给定的类型推导进行归纳。

+   在类型推导的最后一步是 T_Abs 或 T_RNil 的情况下是显而易见的，因为抽象和{}总是值。对于 T_Var 的情况是无效的，因为变量不能在空上下文中被类型化。

+   如果在类型推导中的最后一步是通过 T_App，则存在项 t[1] t[2]和类型 T[1] T[2]，使得 t = t[1] t[2]，T = T[2]，empty ⊢ t[1] : T[1] → T[2]和 empty ⊢ t[2] : T[1]。

    这些类型推导的归纳假设表明 t[1]是一个值或步骤，t[2]是一个值或步骤。

    +   假设对于某个项 t[1]'，t[1] ⇒ t[1]'。那么 t[1] t[2] ⇒ t[1]' t[2]通过 ST_App1。

    +   否则 t[1]是一个值。

        +   假设对于某个项 t[2]'，t[2] ⇒ t[2]'。那么由于 t[1]是一个值，所以 t[1] t[2] ⇒ t[1] t[2]'通过 ST_App2。

        +   否则，t[2]是一个值。根据引理 canonical_forms_for_arrow_types，t[1] = \x:S[1].s2，其中 x，S[1]和 s[2]。但是由于 t[2]是一个值，所以(λx:S[1].s2) t[2] ⇒ [x:=t[2]]s[2]通过 ST_AppAbs。

+   如果推导的最后一步是通过 T_Proj，则存在一个项 tr，一个类型 Tr 和一个标签 i，使得 t = tr.i，empty ⊢ tr : Tr，以及 Tlookup i Tr = Some T。

    通过 IH，tr 要么是一个值，要么是一个步骤。如果对于某个项 tr'，tr ⇒ tr'，那么通过规则 ST_Proj1，tr.i ⇒ tr'.i。

    如果 tr 是一个值，则引理 lookup_field_in_value 表明存在一个项 ti，使得 tlookup i tr = Some ti。由此可知 tr.i ⇒ ti 通过规则 ST_ProjRcd。

+   如果推导的最后一步是通过 T_Sub，则存在一个类型 S，使得 S <: T 且 empty ⊢ t : S。所需的结果正是类型子推导的归纳假设。

+   如果推导的最后一步是通过 T_RCons，则存在一些项 t[1] tr，类型 T[1] Tr 和一个标签 t，使得 t = {i=t[1], tr}，T = {i:T[1], Tr}，record_tm tr，record_tm Tr，empty ⊢ t[1] : T[1]和 empty ⊢ tr : Tr。

    这些类型推导的归纳假设表明 t[1]是一个值或步骤，tr 是一个值或步骤。我们考虑每种情况：

    +   假设对于某个项 t[1]'，t[1] ⇒ t[1]'。那么由于 t[1]是一个值，所以{i=t[1], tr} ⇒ {i=t[1]', tr}通过规则 ST_Rcd_Head。

    +   否则 t[1]是一个值。

        +   假设对于某个项 tr'，tr ⇒ tr'。那么由于 t[1]是一个值，所以{i=t[1], tr} ⇒ {i=t[1], tr'}通过规则 ST_Rcd_Tail。

        +   否则，tr 也是一个值。因此，{i=t[1], tr}也是一个值，根据 v_rcons。

```

### Inversion Lemmas

```

引理 typing_inversion_var：对于所有Γ x T，

在Γ（tvar x）T 下有类型 →

∃S。

Γ x = Some S ∧ subtype S T。

    Proof with eauto.

intros Γ x T Hty。

记住(tvar x)为 t。

对归纳 Hty; intros;

反演 Heqt; 替换; 尝试通过反演解决。

- (* T_Var *)

∃T...

- (* T_Sub *)

将 IHHty 解构为[U [Hctx HsubU]]... 完成。

引理 typing_inversion_app：对于所有Γ t[1] t[2] T[2]，

在Γ（tapp t[1] t[2]）T[2]下有类型 →

∃T[1]，

在Γ t[1] (TArrow T[1] T[2])下有类型 ∧

在Γ t[2] T[1]下有类型。

    Proof with eauto.

intros Γ t[1] t[2] T[2] Hty.

记住(tapp t[1] t[2])为 t。

对于归纳 Hty; intros;

反演 Heqt; 替换; 尝试通过反演解决。

- (* T_App *)

∃T[1]...

- (* T_Sub *)

将 IHHty 解构为[U[1] [Hty1 Hty2]]...

断言 Hwf := has_type__wf _ _ _ Hty2。

∃U[1]... Qed。

引理 typing_inversion_abs：∀Γ x S[1] t[2] T，

Γ（tabs x S[1] t[2]）T 有类型 →

（∃S[2]，subtype（TArrow S[1] S[2]）T

∧ Γ（update Γ x S[1]）t[2] 有类型 S[2]）。

    证明与 eauto。

intros Γ x S[1] t[2] T H。

记住 (tabs x S[1] t[2]) 为 t。

对 H 进行归纳。

反转 Heqt；替换；intros；尝试通过反转解决。

- （* T_Abs *）

断言 Hwf := has_type__wf _ _ _ H[0]。

∃T[12]...

- （* T_Sub *）

将 IHhas_type 分解为 [S[2] [Hsub Hty]]...

Qed。

引理 typing_inversion_proj：∀Γ i t[1] Ti，

Γ（tproj t[1] i）Ti 有类型 →

∃T，∃Si，

查找 i T = Some Si ∧ subtype Si Ti ∧ Γ t[1] 有类型 T。

    证明与 eauto。

intros Γ i t[1] Ti H。

记住 (tproj t[1] i) 为 t。

对 I 进行归纳；

反转 Heqt；替换；intros；尝试通过反转解决。

- （* T_Proj *）

断言 well_formed_ty Ti 为 Hwf。

{（* 断言的证明 *）

应用 (wf_rcd_lookup i T Ti)...

在 H 中应用 has_type__wf... }

∃T。∃Ti...

- （* T_Sub *）

在 Hty 中将 IHhas_type 分解为 [U [Ui [Hget [Hsub Hty]]]]...

∃U。∃Ui... Qed。

引理 typing_inversion_rcons：∀Γ i ti tr T，

Γ（trcons i ti tr）T 有类型 →

∃Si，∃Sr，

subtype（TRCons i Si Sr）T ∧ Γ ti 有类型 Si ∧

记录项 tr ∧ Γ tr 有类型 Sr。

    证明与 eauto。

对 Γ i ti tr T Hty 进行归纳。

记住 (trcons i ti tr) 为 t。

对 Hty 进行归纳；

反转 Heqt；替换...

- （* T_Sub *）

在 H[0] 中应用 IHHty。

将 H[0] 分解为 [Ri [Rr [HsubRS [HtypRi HtypRr]]]]。

∃Ri。∃Rr...

- （* T_RCons *）

断言 well_formed_ty (TRCons i T Tr) 为 Hwf。

{（* 断言的证明 *）

在 Hty1 中应用 has_type__wf。

在 Hty2 中应用 has_type__wf...

∃T。∃Tr... Qed。

引理 abs_arrow：∀x S[1] s[2] T[1] T[2]，

empty（tabs x S[1] s[2]）有类型（TArrow T[1] T[2]）→

subtype T[1] S[1]

∧ Γ（update empty x S[1]）s[2] 有类型 T[2]。

    证明与 eauto。

intros x S[1] s[2] T[1] T[2] Hty。

在 Hty 中应用 typing_inversion_abs。

将 Hty 分解为 [S[2] [Hsub Hty]]。

在 Hsub 中应用 子反转箭头。

将 Hsub 分解为 [U[1] [U[2] [Heq [Hsub1 Hsub2]]]]。

反转 Heq；替换... Qed。

```

### Context Invariance

```

归纳出现自由变量：id → tm → Prop :=

| afi_var：∀x，

appears_free_in x（tvar x）。

| afi_app1：∀x t[1] t[2]，

appears_free_in x t[1] → appears_free_in x（tapp t[1] t[2]）

| afi_app2：∀x t[1] t[2]，

appears_free_in x t[2] → appears_free_in x（tapp t[1] t[2]）

| afi_abs：∀x y T[11] t[12]，

y ≠ x  →

appears_free_in x t[12] →

appears_free_in x（tabs y T[11] t[12]）中。

| afi_proj：∀x t i，

appears_free_in x t →

appears_free_in x（tproj t i）。

| afi_rhead：∀x i t tr，

appears_free_in x t →

appears_free_in x（trcons i t tr）。

| afi_rtail：∀x i t tr，

appears_free_in x tr →

appears_free_in x（trcons i t tr）。

提示 Constructors appears_free_in。

引理上下文不变性：∀Γ Γ' t S，

具有类型 Γ t S  →

(∀x, 在 x t 中出现自由 → Γ x = Γ' x)  →

具有类型 Γ' t S。

    证明与 eauto。

intros。推广 Γ'。

对 I 进行归纳；

intros Γ' Heqv...

- (* T_Var *)

应用 T_Var... 重写 ← Heqv...

- (* T_Abs *)

应用 T_Abs... 应用 IHhas_type。intros x[0] Hafi。

展开 update, t_update。分解(beq_idP x x[0])...

- (* T_App *)

应用 T_App 与 T[1]...

- (* T_RCons *)

应用 T_RCons... 完成。

引理自由出现在上下文中：∀x t T Γ，

在 x t 中出现自由的 →

具有类型 Γ t T →

∃T'，Γ x = Some T'。

    证明与 eauto。

intros x t T Γ Hafi Htyp。

对 Htyp 进行归纳；替换；反演 Hafi；替换...

- (* T_Abs *)

将 IHHtyp H[5] 分解为[T Hctx]。 ∃T。

在 Hctx 中展开 update, t_update。

在 Hctx 中重写 false_beq_id... 完成。

```

### Preservation

```

替换保持类型：∀Γ x U v t S，

具有类型 (update Γ x U) t S  →

具有类型 empty v U →

具有类型 Γ ([x:=v]t) S.

    证明与 eauto。

intros Γ x U v t S Htypt Htypv。

推广 S。推广 Γ。

对 t 进行归纳；intros；简化。

- (* tvar *)

将 i 重命名为 y。

分解(typing_inversion_var _ _ _ Htypt)为[T [Hctx Hsub]]。

在 Hctx 中展开 update, t_update。

分解(beq_idP x y)...

+ (* x=y *)

替换。

反演 Hctx；替换。清除 Hctx。

应用 context_invariance 与 empty...

intros x Hcontra。

分解(free_in_context _ _ S empty Hcontra)为[T' HT']...

反演 HT'。

+ (* x<>y *)

分解(subtype__wf _ _ Hsub)...

- (* tapp *)

分解(typing_inversion_app _ _ _ _ Htypt)

作为[T[1] [Htypt1 Htypt2]]。

应用 T_App...

- (* tabs *)

将 i 重命名为 y。将 t 重命名为 T[1]。

分解(typing_inversion_abs _ _ _ _ _ Htypt)

作为[T[2] [Hsub Htypt2]]。

分解(subtype__wf _ _ Hsub)为[Hwf1 Hwf2]。

反演 Hwf2。替换。

应用 T_Sub 与(TArrow T[1] T[2])... 应用 T_Abs...

分解(beq_idP x y)。

+ (* x=y *)

应用 context_invariance...

替换。

intros x Hafi. 展开 update, t_update。

分解(beq_id y x)...

+ (* x<>y *)

应用 IHt。应用 context_invariance...

intros z Hafi。展开 update, t_update。

分解(beq_idP y z)...

替换。重写 false_beq_id...

- (* tproj *)

解构（typing_inversion_proj _ _ _ _ Htypt）

作为 [T [Ti [Hget [Hsub Htypt1]]]]...

- (* trnil *)

应用 context_invariance...

推断 y Hcontra。反演 Hcontra。

- (* trcons *)

解构（typing_inversion_rcons _ _ _ _ _ Htypt）为

[Ti [Tr [Hsub [HtypTi [Hrcdt2 HtypTr]]]]]。

应用 T_Sub 与 (TRCons i Ti Tr)...

应用 T_RCons...

+ (* 记录类型 Tr *)

应用 subtype__wf 在 Hsub 中。解构 Hsub。反演 H[0]...

+ (* 记录项 (x:=vt[2]) *)

反演 Hrcdt2；替换；简化... 完成。

定理保持性：∀t t' T，

有类型 empty t T  →

t ⇒ t'  →

有类型 empty t' T。

    证明与自动完成。

推断 t t' T HT。

记住 empty 为 Γ。推广依赖于 HeqGamma。

推广依赖于 t'。

归纳 HT；

推断 t' HeqGamma HE；替换；反演 HE；替换...

- (* T_App *)

反演 HE；替换...

+ (* ST_AppAbs *)

解构（abs_arrow _ _ _ _ _ HT[1]）为 [HA[1] HA[2]]。

应用 substitution_preserves_typing 与 T...

- (* T_Proj *)

解构（lookup_field_in_value _ _ _ _ H[2] HT H）

作为 [vi [Hget Hty]]。

在 H[4] 中重写 Hget。反演 Hget。替换...

- (* T_RCons *)

使用 step_preserves_record_tm 自动完成。完成。

```

    *Theorem*: If t, t' are terms and T is a type such that
     empty ⊢ t : T and t ⇒ t', then empty ⊢ t' : T.

    *Proof*: Let t and T be given such that empty ⊢ t : T.  We go
     by induction on the structure of this typing derivation, leaving
     t' general.  Cases T_Abs and T_RNil are vacuous because
     abstractions and {} don't step.  Case T_Var is vacuous as well,
     since the context is empty.

*   If the final step of the derivation is by T_App, then there are terms t[1] t[2] and types T[1] T[2] such that t = t[1] t[2], T = T[2], empty ⊢ t[1] : T[1] → T[2] and empty ⊢ t[2] : T[1]. 

     By inspection of the definition of the step relation, there are three ways t[1] t[2] can step. Cases ST_App1 and ST_App2 follow immediately by the induction hypotheses for the typing subderivations and a use of T_App. 

     Suppose instead t[1] t[2] steps by ST_AppAbs. Then t[1] = \x:S.t12 for some type S and term t[12], and t' = [x:=t[2]]t[12]. 

     By Lemma abs_arrow, we have T[1] <: S and x:S[1] ⊢ s[2] : T[2]. It then follows by lemma substitution_preserves_typing that empty ⊢ [x:=t[2]] t[12] : T[2] as desired. 

*   If the final step of the derivation is by T_Proj, then there is a term tr, type Tr and label i such that t = tr.i, empty ⊢ tr : Tr, and Tlookup i Tr = Some T. 

     The IH for the typing derivation gives us that, for any term tr', if tr ⇒ tr' then empty ⊢ tr' Tr. Inspection of the definition of the step relation reveals that there are two ways a projection can step. Case ST_Proj1 follows immediately by the IH. 

     Instead suppose tr.i steps by ST_ProjRcd. Then tr is a value and there is some term vi such that tlookup i tr = Some vi and t' = vi. But by lemma lookup_field_in_value, empty ⊢ vi : Ti as desired. 

*   If the final step of the derivation is by T_Sub, then there is a type S such that S <: T and empty ⊢ t : S. The result is immediate by the induction hypothesis for the typing subderivation and an application of T_Sub. 

*   If the final step of the derivation is by T_RCons, then there exist some terms t[1] tr, types T[1] Tr and a label t such that t = {i=t[1], tr}, T = {i:T[1], Tr}, record_tm tr, record_tm Tr, empty ⊢ t[1] : T[1] and empty ⊢ tr : Tr. 

     By the definition of the step relation, t must have stepped by ST_Rcd_Head or ST_Rcd_Tail. In the first case, the result follows by the IH for t[1]'s typing derivation and T_RCons. In the second case, the result follows by the IH for tr's typing derivation, T_RCons, and a use of the step_preserves_record_tm lemma.

```

```

```

```

```

```

```

```

```
