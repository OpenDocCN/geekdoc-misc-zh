# TypecheckingA Typechecker for STLC

```

    The has_type relation of the STLC defines what it means for a
    term to belong to a type (in some context).  But it doesn't, by
    itself, tell us how to *check* whether or not a term is well
    typed.

    Fortunately, the rules defining has_type are *syntax directed*
    — that is, for every syntactic form of the language, there is
    just one rule that can be used to give a type to terms of that
    form.  This makes it straightforward to translate the typing rules
    into clauses of a typechecking *function* that takes a term and a
    context and either returns the term's type or else signals that
    the term is not typable.

```

(* This short chapter constructs such a function and proves it    correct. *)

Require Import Coq.Bool.Bool.

Require Import Maps.

Require Import Smallstep.

Require Import Stlc.

Module STLCChecker.

Import STLC.

```

# Comparing Types

    First, we need a function to compare two types for equality...

```

Fixpoint beq_ty (T[1] T[2]:ty) : bool :=

match T[1],T[2] with

| TBool, TBool ⇒

true

| TArrow T[11] T[12], TArrow T[21] T[22] ⇒

andb (beq_ty T[11] T[21]) (beq_ty T[12] T[22])

| _,_ ⇒

false

end.

```

    ... and we need to establish the usual two-way connection between
    the boolean result returned by beq_ty and the logical
    proposition that its inputs are equal.

```

Lemma beq_ty_refl : ∀T[1],

beq_ty T[1] T[1] = true.

    Proof.

intros T[1]. induction T[1]; simpl.

reflexivity.

rewrite IHT1_1. rewrite IHT1_2. reflexivity. Qed.

Lemma beq_ty__eq : ∀T[1] T[2],

beq_ty T[1] T[2] = true → T[1] = T[2].

    Proof with auto.

intros T[1]. induction T[1]; intros T[2] Hbeq; destruct T[2]; inversion Hbeq.

- (* T[1]=TBool *)

reflexivity.

- (* T[1]=TArrow T1_1 T1_2 *)

rewrite [andb_true_iff](http://coq.inria.fr/library/Coq.Bool.Bool.html#andb_true_iff) in H[0]. inversion H[0] as [Hbeq1 Hbeq2].

apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst... Qed.

```

# The Typechecker

    The typechecker works by walking over the structure of the given
    term, returning either Some T or None.  Each time we make a
    recursive call to find out the types of the subterms, we need to
    pattern-match on the results to make sure that they are not
    None.  Also, in the tapp case, we use pattern matching to
    extract the left- and right-hand sides of the function's arrow
    type (and fail if the type of the function is not TArrow T[11] T[12]
    for some T[1] and T[2]).

```

Fixpoint type_check (Γ:context) (t:tm) : option ty :=

match t with

| tvar x ⇒

Γ x

| tabs x T[11] t[12] ⇒

match type_check (update Γ x T[11]) t[12] with

| Some T[12] ⇒ Some (TArrow T[11] T[12])

| _ ⇒ None

end

| tapp t[1] t[2] ⇒

match type_check Γ t[1], type_check Γ t[2] with

| Some (TArrow T[11] T[12]),Some T[2] ⇒

if beq_ty T[11] T[2] then Some T[12] else None

| _,_ ⇒ None

end

| ttrue ⇒

Some TBool

| tfalse ⇒

Some TBool

| tif guard t f ⇒

match type_check Γ guard with

| Some TBool ⇒

match type_check Γ t, type_check Γ f with

| Some T[1], Some T[2] ⇒

if beq_ty T[1] T[2] then Some T[1] else None

| _,_ ⇒ None

end

| _ ⇒ None

end

end.

```

# Properties

    To verify that this typechecking algorithm is correct, we show
    that it is *sound* and *complete* for the original has_type
    relation — that is, type_check and has_type define the same
    partial function.

```

Theorem type_checking_sound : ∀Γ t T,

type_check Γ t = Some T → has_type Γ t T.

    Proof with eauto.

intros Γ t. generalize dependent Γ.

induction t; intros Γ T Htc; inversion Htc.

- (* tvar *) eauto.

- (* tapp *)

remember (type_check Γ t[1]) as TO[1].

remember (type_check Γ t[2]) as TO[2].

destruct TO[1] as [T[1]|]; try solve_by_invert;

destruct T[1] as [|T[11] T[12]]; try solve_by_invert.

destruct TO[2] as [T[2]|]; try solve_by_invert.

destruct (beq_ty T[11] T[2]) eqn: Heqb;

try solve_by_invert.

apply beq_ty__eq in Heqb.

inversion H[0]; subst...

- (* tabs *)

rename i into y. rename t into T[1].

remember (update Γ y T[1]) as G'.

remember (type_check G' t[0]) as TO[2].

destruct TO[2]; try solve_by_invert.

inversion H[0]; subst...

- (* ttrue *) eauto.

- (* tfalse *) eauto.

- (* tif *)

remember (type_check Γ t[1]) as TOc.

remember (type_check Γ t[2]) as TO[1].

remember (type_check Γ t[3]) as TO[2].

destruct TOc as [Tc|]; try solve_by_invert.

destruct Tc; try solve_by_invert.

对 TO[1] 进行分析得到 [T[1]|]; 尝试通过反演解决。

对 TO[2] 进行分析得到 [T[2]|]; 尝试通过反演解决。

对 (beq_ty T[1] T[2]) 进行分析得到 Heqb;

尝试通过反演解决。

应用 beq_ty__eq 在 Heqb 中。

反演 H[0]。替换。替换...

    完成。

定理 type_checking_complete : ∀Γ t T,

在 Γ t T 下有类型 t T → type_check Γ t = Some T。

    证明使用自动化。

引入 Γ t T Hty。

对 Hty 进行归纳; 简化。

- (* T_Var *) eauto。

- (* T_Abs *) 重写 IHHty...

- (* T_App *)

重写 IHHty1。重写 IHHty2。

重写 (beq_ty_refl T[11])...

- (* T_True *) eauto。

- (* T_False *) eauto.

- (* T_If *) 重写 IHHty1。重写 IHHty2。

重写 IHHty3。重写 (beq_ty_refl T)...

    完成。

结束 STLCChecker。

```

# Exercises

#### Exercise: 5 stars (typechecker_extensions)

    In this exercise we'll extend the typechecker to deal with the
    extended features discussed in chapter MoreStlc.  Your job
    is to fill in the omitted cases in the following.

```

模块 TypecheckerExtensions。

导入 MoreStlc。

导入 STLCExtended。

递归 beq_ty (T[1] T[2]: ty) : bool :=

匹配 T[1],T[2] 的情况与

| TNat, TNat ⇒

true

| TUnit, TUnit ⇒

true

| TArrow T[11] T[12], TArrow T[21] T[22] ⇒

andb (beq_ty T[11] T[21]) (beq_ty T[12] T[22])

| TProd T[11] T[12], TProd T[21] T[22] ⇒

andb (beq_ty T[11] T[21]) (beq_ty T[12] T[22])

| TSum T[11] T[12], TSum T[21] T[22] ⇒

andb (beq_ty T[11] T[21]) (beq_ty T[12] T[22])

| TList T[11], TList T[21] ⇒

beq_ty T[11] T[21]

| _,_ ⇒

false

结束。

引理 beq_ty_refl : ∀T[1],

beq_ty T[1] T[1] = true。

证明。

引入 T[1]。

对 T[1] 进行归纳; 简化;

尝试反射;

尝试 (重写 IHT1_1; 重写 IHT1_2; 反射);

尝试 (重写 IHT1; 反射). 完成。

引理 beq_ty__eq : ∀T[1] T[2],

当 beq_ty T[1] T[2] = true 时，T[1] = T[2]。

证明。

引入 T[1]。

对 T[1] 进行归纳; 引入 T[2] Hbeq; 对 T[2] 进行分析; 反演 Hbeq;

尝试反射;

尝试 (在 H[0] 中重写 andb_true_iff; 反演 H[0] 得到 [Hbeq1 Hbeq2];

apply IHT1_1 在 Hbeq1 中; apply IHT1_2 在 Hbeq2 中; 替换; 自动);

尝试 (应用 IHT1 在 Hbeq; 替换; 自动).

完成。

递归类型检查 (Γ:context) (t:tm) : option ty :=

匹配 t 与

| tvar x ⇒

Γ x

| tabs x T[11] t[12] ⇒

匹配 type_check (update Γ x T[11]) t[12] 的结果与

| Some T[12] ⇒ Some (TArrow T[11] T[12])

| _ ⇒ None

结束

| tapp t[1] t[2] ⇒

匹配 type_check Γ t[1], type_check Γ t[2] 的结果与

| Some (TArrow T[11] T[12]),Some T[2] ⇒

如果 beq_ty T[11] T[2] 然后返回 Some T[12] 否则返回 None

| _,_ ⇒ None

结束

| tnat _ ⇒

Some TNat

| tsucc t[1] ⇒

匹配 type_check Γ t[1] 的结果与

| Some TNat ⇒ Some TNat

| _ ⇒ None

结束

| tpred t[1] ⇒

匹配 type_check Γ t[1] 的结果与

| Some TNat ⇒ Some TNat

| _ ⇒ None

结束

| tmult t[1] t[2] ⇒

匹配 type_check Γ t[1], type_check Γ t[2] 的结果与

| Some TNat, Some TNat ⇒ Some TNat

| _,_ ⇒ None

结束

| tif0 guard t f ⇒

匹配 type_check Γ guard 的结果与

| Some TNat ⇒

匹配 type_check Γ t, type_check Γ f 的结果与

| Some T[1], Some T[2] ⇒

如果 beq_ty T[1] T[2] 然后返回 Some T[1] 否则返回 None

| _,_ ⇒ None

结束

| _ ⇒ None

结束

(* 在此填写 *)

| tlcase t[0] t[1] x[21] x[22] t[2] ⇒

匹配 type_check Γ t[0] 的结果与

| Some (TList T) ⇒

匹配 type_check Γ t[1],

type_check (update (update Γ x[22] (TList T)) x[21] T) t[2] 的结果与

| Some T[1]', Some T[2]' ⇒

如果 beq_ty T[1]' T[2]' 然后 Some T[1]' else 无

| _,_ ⇒ 无

结束

| _ ⇒ 无

结束

(* 在此填写 *)

| _ ⇒ 无  (* ... 并删除此行 *)

结束。

(* 仅仅为了好玩，我们将使用比上面稍微更多的自动化来进行完备性证明，使用这些“超级策略”：*)

Ltac 反演类型检查 Γ t T :=

记住（type_check Γ t）为 TO;

将 TO 视为 [T|]；

尝试解决反演；尝试（反演 H[0]; 自动）; 尝试（替换; 自动）。

Ltac 完全反演类型检查 Γ t T T[1] T[2] :=

让 TX := 新 T in

记住（type_check Γ t）为 TO;

将 TO 视为 [TX|]；尝试解决反演；

将 TX 视为 [T[1] T[2]| | | T[1] T[2]| T[1] T[2]| T[1]]；

尝试解决反演；尝试（反演 H[0]; 自动）; 尝试（替换; 自动）。

Ltac 情况相等 S T :=

分解（beq_ty S T）等式为：Heqb;

反演 H[0]; 应用 beq_ty__eq 在 Heqb 中; 替换; 替换; 自动。

定理类型检查声音：∀Γ t T，

type_check Γ t = Some T → Γ t T。

证明与自动。

输入 Γ t。泛化 Γ。

对 t 进行归纳; 对 Γ T Htc 进行反演。

- (* tvar *) 自动。

- (* tapp *)

完全反演类型检查 Γ t[1] T[1] T[11] T[12]。

反演类型检查 Γ t[2] T[2]。

情况相等 T[11] T[2]。

- (* tabs *)

将 i 重命名为 x。将 t 重命名为 T[1]。

记住（更新 Γ x T[1]）为 Γ'。

反演类型检查 Γ' t[0] T[0]。

- (* tnat *) 自动。

- (* tsucc *)

将 t 重命名为 t[1]。

完全反演类型检查 Γ t[1] T[1] T[11] T[12]。

- (* tpred *)

将 t 重命名为 t[1]。

完全反演类型检查 Γ t[1] T[1] T[11] T[12]。

- (* tmult *)

完全反演类型检查 Γ t[1] T[1] T[11] T[12]。

完全反演类型检查 Γ t[2] T[2] T[21] T[12]。

- (* tif0 *)

完全反演类型检查 Γ t[1] T[1] T[11] T[12]。

反演类型检查 Γ t[2] T[2]。

反演类型检查 Γ t[3] T[3]。

情况相等 T[2] T[3]。

(* 在此填写 *)

- (* tlcase *)

将 i 视为 x[31]。将 i[0] 视为 x[32]。

完全反演类型检查 Γ t[1] T[1] T[11] T[12]。

反演类型检查 Γ t[2] T[2]。

记住（更新（更新 Γ x[32]（TList T[11]））x[31] T[11]）为 Gamma'2。

反演类型检查 Gamma'2 t[3] T[3]。

情况相等 T[2] T[3]。

(* 在此填写 *)

完成。

定理类型检查完整性：∀Γ t T，

Γ t T → type_check Γ t = Some T。

证明。

输入 Γ t T Hty。

对 Hty 进行归纳; 简化;

尝试（重写 IHHty）;

尝试（重写 IHHty1）;

尝试（重写 IHHty2）;

尝试（重写 IHHty3）;

尝试（重写（beq_ty_refl T））;

尝试（重写（beq_ty_refl T[1]））;

尝试（重写（beq_ty_refl T[2]））;

自动。

已批准。 (* ... 并删除此行 *)

(*  完成。(* ... 并取消注释此行 *) *)

结束 TypecheckerExtensions。

```

    ☐ 

#### Exercise: 5 stars, optional (stlc_step_function)

    Above, we showed how to write a typechecking function and prove it
    sound and complete for the typing relation.  Do the same for the
    operational semantics — i.e., write a function stepf of type
    tm → option tm and prove that it is sound and complete with
    respect to step from chapter MoreStlc.

```

模块 StepFunction。

导入 TypecheckerExtensions。

(* 在此填写 *)

结束 StepFunction。

```

    ☐ 

#### Exercise: 5 stars, optional (stlc_impl)

    Using the Imp parser described in the ImpParser chapter as
    a guide, build a parser for extended Stlc programs.  Combine it
    with the typechecking and stepping functions from above to yield a
    complete typechecker and interpreter for this language.

```

模块 StlcImpl。

导入 StepFunction。

(* 在此填写 *)

结束 StlcImpl。

```

    ☐ 

```
