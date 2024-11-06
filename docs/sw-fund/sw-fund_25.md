# STLC 的 StlcProp 属性

```

```

Require Import Maps.

Require Import Types。

Require Import Stlc.

Require Import Smallstep.

模块 STLCProp。

导入 STLC。

```

    In this chapter, we develop the fundamental theory of the Simply
    Typed Lambda Calculus — in particular, the type safety
    theorem.

```

# 规范形式

    正如我们在类型章节中看到的简单微积分一样，

    建立基本的规约和类型属性的第一步

    是识别可能的*规范形式*（即，良好类型

    封闭值）属于每种类型。对于 Bool，这些是布尔值

    值为 ttrue 和 tfalse。对于箭头类型，规范形式

    是 lambda 抽象。

```
Lemma canonical_forms_bool : ∀t,
  empty ⊢ t ∈ TBool →
  value t →
  (t = ttrue) ∨ (t = tfalse).

    Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
    Qed.

Lemma canonical_forms_fun : ∀t T[1] T[2],
  empty ⊢ t ∈ (TArrow T[1] T[2]) →
  value t →
  ∃x u, t = tabs x T[1] u.

    Proof.
  intros t T[1] T[2] HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  ∃x[0]. ∃t[0]. auto.
    Qed.

```

# 进展

    *进展*定理告诉我们，封闭的、良好类型的

    项不会被卡住：一个良好类型的项要么是一个值，要么

    可以进行一步规约。证明相对较为

    我们在进展证明中看到的直接扩展。

    类型章节。我们将首先用英语给出证明，然后

    形式版本。

```
Theorem progress : ∀t T,
     empty ⊢ t ∈ T →
     value t ∨ ∃t', t ⇒ t'.

```

    *证明*：通过 ⊢ t ∈ T 推导的归纳。

+   推导的最后一条规则不能是 T_Var，因为在空上下文中变量永远不会被良好地类型化。

+   T_True、T_False 和 T_Abs 情况是微不足道的，因为在这些情况下，我们可以通过检查规则来看出 t 是一个值。

+   如果推导的最后一条规则是 T_App，那么 t 的形式为 t[1] t[2]，其中 ⊢ t[1] ∈ T[2] → T 和 ⊢ t[2] ∈ T[2] 对于某个类型 T[2]。根据归纳假设，t[1]要么是一个值，要么可以进行一步规约。

    +   如果 t[1]是一个值，那么考虑 t[2]，根据另一个归纳假设，t[2]也要么是一个值，要么迈出��步。

        +   假设 t[2]是一个值。由于 t[1]是一个带有箭头类型的值，它必须是一个 lambda 抽象；因此 t[1] t[2]可以通过 ST_AppAbs 迈出一步。

        +   否则，t[2]可以迈出一步，因此 t[1] t[2]也可以通过 ST_App2 迈出一步。

    +   如果 t[1]可以迈出一步，那么 t[1] t[2]也可以通过 ST_App1 迈出一步。

+   如果推导的最后一条规则是 T_If，那么 t = if t[1] then t[2] else t[3]，其中 t[1]具有类型 Bool。根据 IH，t[1]要么是一个值，要么迈出一步。

    +   如果 t[1]是一个值，那么由于它具有 Bool 类型，它必须是 true 或 false。如果是 true，则 t 迈向 t[2]；否则迈向 t[3]。

    +   否则，t[1]迈出一步，因此 t 也会迈出一步（通过 ST_If）。

```

    Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Γ.
  induction Ht; subst Γ...
  - (* T_Var *)
    (* contradictory: variables cannot be typed in an        empty context *)
    inversion H.

  - (* T_App *)
    (* t = t[1] t[2].  Proceed by cases on whether t[1] is a        value or steps... *)
    right. destruct IHHt1...
    + (* t[1] is a value *)
      destruct IHHt2...
      * (* t[2] is also a value *)
        assert (∃x[0] t[0], t[1] = tabs [x[0]](StlcProp.html#x<sub>0</sub>) T[11] [t[0]](StlcProp.html#t<sub>0</sub>)).
        eapply canonical_forms_fun; eauto.
        destruct H[1] as [x[0] [t[0] Heq]]. subst.
        ∃([x[0]:=t[2]]t[0])...

      * (* t[2] steps *)
        inversion H[0] as [t[2]' Hstp]. ∃(tapp t[1] t[2]')...

    + (* t[1] steps *)
      inversion H as [t[1]' Hstp]. ∃(tapp t[1]' t[2])...

  - (* T_If *)
    right. destruct IHHt1...

    + (* t[1] is a value *)
      destruct (canonical_forms_bool t[1]); subst; eauto.

    + (* t[1] also steps *)
      inversion H as [t[1]' Hstp]. ∃(tif t[1]' t[2] t[3])...
    Qed.

```

#### 练习：3 星，高级（progress_from_term_ind）

    显示进展也可以通过对项进行归纳来证明

    而不是对类型推导进行归纳。

```
Theorem progress' : ∀t T,
     empty ⊢ t ∈ T →
     value t ∨ ∃t', t ⇒ t'.
Proof.
  intros t.
  induction t; intros T Ht; auto.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

# Preservation

    The other half of the type soundness property is the
    preservation of types during reduction.  For this part, we'll need
    to develop some technical machinery for reasoning about variables
    and substitution.  Working from top to bottom (from the high-level
    property we are actually interested in to the lowest-level
    technical lemmas that are needed by various cases of the more
    interesting proofs), the story goes like this:

*   The *preservation theorem* is proved by induction on a typing derivation, pretty much as we did in the Types chapter. The one case that is significantly different is the one for the ST_AppAbs rule, whose definition uses the substitution operation. To see that this step preserves typing, we need to know that the substitution itself does. So we prove a... 

*   *substitution lemma*, stating that substituting a (closed) term s for a variable x in a term t preserves the type of t. The proof goes by induction on the form of t and requires looking at all the different cases in the definition of substitition. This time, the tricky cases are the ones for variables and for function abstractions. In both, we discover that we need to take a term s that has been shown to be well-typed in some context Γ and consider the same term s in a slightly different context Γ'. For this we prove a... 

*   *context invariance* lemma, showing that typing is preserved under "inessential changes" to the context Γ — in particular, changes that do not affect any of the free variables of the term. And finally, for this, we need a careful definition of... 

*   the *free variables* of a term — i.e., those variables mentioned in a term and not in the scope of an enclosing function abstraction binding a variable of the same name.

    To make Coq happy, we need to formalize the story in the opposite
   order...

```

## 自由出现

    如果一个变量 x 在一个项 t 中*自由出现*，那么 t 包含一些

    不在标记为 x 的抽象下的 x 的出现。

    例如：

+   y 自由出现，但 x 不在\x:T→U. x y

+   在(λx:T→U. x y) x 中，x 和 y 都自由出现

+   在\x:T→U. \y:T. x y 中，y 自由出现，但 x 不出现

    形式上：

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
  | afi_if[1] : ∀x t[1] t[2] t[3],
      appears_free_in x t[1] →
      appears_free_in x (tif t[1] t[2] t[3])
  | afi_if[2] : ∀x t[1] t[2] t[3],
      appears_free_in x t[2] →
      appears_free_in x (tif t[1] t[2] t[3])
  | afi_if[3] : ∀x t[1] t[2] t[3],
      appears_free_in x t[3] →
      appears_free_in x (tif t[1] t[2] t[3]).

Hint Constructors appears_free_in.

```

    一个项的*自由变量*就是出现的变量

    在其中没有自由变量。一个没有自由变量的项被称为

    *封闭*。

```
Definition closed (t:tm) :=
  ∀x, ¬ appears_free_in x t.

```

    *开放*项是指不是封闭的项（或者不知道是

    封闭）。

#### 练习：1 星 M（afi）

    在下面的空格中，写出出现自由变量的规则

    非正式推理规则符号化的关系。（使用任何

    你喜欢的符号约定 —— 这个练习的重点是

    只是为了让你思考一下每个规则的意义。)

    尽管这是一个相当低级别、技术性的定义，

    理解它对于理解替换及其

    性质，这实际上是 lambda 演算的关键。

```
(* FILL IN HERE *)

```

    ☐

```

## Substitution

    To prove that substitution preserves typing, we first need a
    technical lemma connecting free variables and typing contexts: If
    a variable x appears free in a term t, and if we know t is
    well typed in context Γ, then it must be the case that
    Γ assigns a type to x.

```

引理 free_in_context：∀x t T Γ，

appear_free_in x t →

Γ ⊢ t ∈ T →

∃T'，Γ x = Some T'。

```

    *Proof*: We show, by induction on the proof that x appears free
      in t, that, for all contexts Γ, if t is well typed
      under Γ, then Γ assigns some type to x.

*   If the last rule used is afi_var, then t = x, and from the assumption that t is well typed under Γ we have immediately that Γ assigns a type to x. 

*   If the last rule used is afi_app1, then t = t[1] t[2] and x appears free in t[1]. Since t is well typed under Γ, we can see from the typing rules that t[1] must also be, and the IH then tells us that Γ assigns x a type. 

*   Almost all the other cases are similar: x appears free in a subterm of t, and since t is well typed under Γ, we know the subterm of t in which x appears is well typed under Γ as well, and the IH gives us exactly the conclusion we want. 

*   The only remaining case is afi_abs. In this case t = \y:T[11].t12 and x appears free in t[12], and we also know that x is different from y. The difference from the previous cases is that, whereas t is well typed under Γ, its body t[12] is well typed under (Γ, y:T[11]), so the IH allows us to conclude that x is assigned some type by the extended context (Γ, y:T[11]). To conclude that Γ assigns a type to x, we appeal to lemma update_neq, noting that x and y are different variables.

```

    证明。

引入 x t T Γ H H[0]。推广 Γ。

推广对 T 的依赖。

对 H 进行归纳；

引入；尝试解决 [inversion H[0]; eauto]。

- (* afi_abs *)

对 H[1] 进行反演；代入。

将 IHappears_free_in 应用于 H[7]。

在 H[7] 中使用 update_neq 进行重写；假设成立。

    完毕。

```

    Next, we'll need the fact that any term t that is well typed in
    the empty context is closed (it has no free variables). 

#### Exercise: 2 stars, optional (typable_empty__closed)

```

推论 typable_empty__closed：∀t T，

空 ⊢ t ∈ T →

闭合的 t。

    证明。

(* 此处填写 *) 已承认。

    ☐

    有时，当我们有一个证明 Γ ⊢ t : T 时，我们将需要

    用 Γ' 替换不同的上下文 Γ。什么时候是安全的

    做这个？直觉上，至少必须是这样的情况

    Γ' 将所有变量分配给与 Γ 相同的类型

    出现在 t 中的自由变量。事实上，这是唯一的条件

    是必要的。

```
Lemma context_invariance : ∀Γ Γ' t T,
     Γ ⊢ t ∈ T  →
     (∀x, appears_free_in x t → Γ x = Γ' x) →
     Γ' ⊢ t ∈ T.

```

    *证明*：对推导进行归纳

    Γ ⊢ t ∈ T。

+   如果推导中的最后一个规则是 T_Var，则 t = x 且 Γ x = T。根据假设，Γ' x = T，因此根据 T_Var，Γ' ⊢ t ∈ T。

+   如果最后一个规则是 T_Abs，则 t = \y:T[11]. t[12]，其中 T = T[11] → T[12] 且 Γ, y:T[11] ⊢ t[12] ∈ T[12]。归纳假设是，对于任何上下文 Γ''，如果 Γ, y:T[11] 和 Γ'' 将 t[12] 中的所有自由变量分配给相同的类型，则 t[12] 在 Γ'' 下具有类型 T[12]。让 Γ' 是一个与 t 中的自由变量在 Γ 上一致的上下文；我们必须证明 Γ' ⊢ \y:T[11]. t[12] ∈ T[11] → T[12]。

    根据 T_Abs，我们只需证明 Γ', y:T[11] ⊢ t[12] ∈ T[12]。根据 IH（设置 Γ'' = Γ', y:T[11]），我们只需证明 Γ, y:T[11] 和 Γ', y:T[11] 在出现在 t[12] 中的所有变量上达成一致。

    任何在 t[12] 中出现的自由变量必须是 y 或其他某个变量。Γ, y:T[11] 和 Γ', y:T[11] 显然在 y 上达成一致。否则，注意到在 t[12] 中出现的除了 y 之外的任何变量也在 t = \y:T[11] 中出现，且根据假设 Γ 和 Γ' 在所有这些变量上达成一致；因此 Γ, y:T[11] 和 Γ', y:T[11] 也是如此。

+   如果最后一个规则是 T_App，则 t = t[1] t[2]，其中 Γ ⊢ t[1] ∈ T[2] → T 和 Γ ⊢ t[2] ∈ T[2]。一个归纳假设陈述对于所有上下文 Γ'，如果 Γ' 在 t[1] 的自由变量上与 Γ 一致，则 t[1] 在 Γ' 下有类型 T[2] → T；t[2] 也有类似的 IH。我们必须证明 t[1] t[2] 在 Γ' 下也具有类型 T，假设 Γ' 在 t[1] t[2] 的所有自由变量上与 Γ 一致。根据 T_App，我们只需证明 t[1] 和 t[2] 在 Γ' 下与在 Γ 下具有相同的类型。但是 t[1] 中的所有自由变量在 t[1] t[2] 中也是自由的，t[2] 也是如此；因此，所需的结果由归纳假设得出。

```

    Proof with eauto.
  intros.
  generalize dependent Γ'.
  induction H; intros; auto.
  - (* T_Var *)
    apply T_Var. rewrite ← H[0]...
  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type. intros x[1] Hafi.
    (* the only tricky step... the Γ' we use to        instantiate is update Γ x T[11] *)
    unfold update. unfold t_update. destruct (beq_id x[0] x[1]) eqn: Hx0x[1]...
    rewrite beq_id_false_iff in Hx0x[1]. auto.
  - (* T_App *)
    apply T_App with T[11]...
    Qed.

```

    现在我们来到了归约证明的概念核心

    保持类型——即 *替换* 的观察

    保持类型。

    形式上，所谓的*替换引理*如下所述：

    假设我们有一个带有自由变量 x 的项 t，并假设

    我们在假设 x 具有类型 T 的情况下为 t 分配了类型 T。

    一些类型 U。另外，假设我们有另一个项 v 并且

    我们已经证明 v 具有类型 U。然后，由于 v 满足

    我们在对 t 进行类型时所做的假设，我们可以

    替换 v 到 t 中 x 的每个出现并

    获得一个仍然具有类型 T 的新项。

    *引理*：如果 Γ, x:U ⊢ t ∈ T 并且 ⊢ v ∈ U，则 Γ ⊢ [x:=v]t ∈ T。

```
Lemma substitution_preserves_typing : ∀Γ x U t v T,
     update Γ x U ⊢ t ∈ T →
     empty ⊢ v ∈ U   →
     Γ ⊢ [x:=v]t ∈ T.

```

    引入了一个技术细微之处在引理的陈述中，即

    我们在*空*上下文中为 v 分配类型 — 其他

    换句话说，我们假设 v 是封闭的。这个假设极大地

    简化了证明的 T_Abs 情况（与假设相比

    Γ ⊢ v ∈ U，这将是另一个合理的假设

    在这一点上）因为上下文不变性引理告诉我们

    v 在任何上下���中都具有类型 U — 我们不必

    担心 v 中的自由变量与正在

    由 T_Abs 引入到上下文中。

    替换引理可以看作是一种交换

    属性。直观地说，它表示替换和类型可以

    可以按任何顺序执行：我们可以先为项分配类型

    分别为 t 和 v 分配类型（在适当的上下文中），然后组合

    使用替换，或者我们可以先替换然后

    为 [x:=v] t 分配一个类型 — 结果无论是

    方式。

    *证明*：我们通过对 t 进行归纳，证明对于所有的 T 和

    Γ, 如果 Γ, x:U ⊢ t ∈ T 并且 ⊢ v ∈ U，则 Γ ⊢ [x:=v]t ∈ T。

+   如果 t 是一个变量，有两种情况要考虑，取决于 t 是否为 x 或其他变量。

    +   如果 t = x，则由于 Γ, x:U ⊢ x ∈ T，我们得出 U = T。我们必须展示 [x:=v]x = v 具有类型 T 在 Γ 下，假设 v 在空上下文中具有类型 U = T。这可以从上下文不变性得出：如果一个封闭项在空上下文中具有类型 T，则在任何上下文中都具有该类型。

    +   如果 t 是一个不等于 x 的变量 y，那么我们只需要注意到在 Γ, x:U 下，y 与在 Γ 下的类型相同。

+   如果 t 是一个抽象 \y:T[11]. t[12]，那么 IH 告诉我们，对于所有的 Γ' 和 T'，如果 Γ', x:U ⊢ t[12] ∈ T' 并且 ⊢ v ∈ U，则 Γ' ⊢ [x:=v]t[12] ∈ T'。

    结论中的替换行为取决于 x 和 y 是否为相同变量。

    首先，假设 x = y。然后，根据替换的定义，[x:=v]t = t，所以我们只需要展示 Γ ⊢ t ∈ T。但我们知道 Γ, x:U ⊢ t : T，并且，由于 y 在 \y:T[11]. t[12] 中不自由出现，上下文不变性引理得出 Γ ⊢ t ∈ T。

    其次，假设 x ≠ y。我们知道 Γ, x:U, y:T[11] ⊢ t[12] ∈ T[12] 通过对类型关系进行反演，从中 Γ, y:T[11], x:U ⊢ t[12] ∈ T[12] 通过上下文不变性引理得出，因此 IH 适用，给出了 Γ, y:T[11] ⊢ [x:=v]t[12] ∈ T[12]。通过 T_Abs， Γ ⊢ \y:T[11]. [x:=v]t[12] ∈ T[11]→T[12]，并通过替换的定义（注意 x ≠ y）， Γ ⊢ \y:T[11]. [x:=v]t[12] ∈ T[11]→T[12] 如所需。

+   如果 t 是一个应用 t[1] t[2]，结果直接由替换的定义和归纳假设得出。

+   剩下的情况与应用情况类似。

    *技术说明*：这个证明是一个罕见的情况，其中

    对项进行归纳，而不是类型推导，得到一个

    更简单的论点。原因是假设

    更新Γ x U ⊢ t ∈ T 并不是完全通用的，在

    意味着类型关系中的一个“槽” — 即

    上下文-不仅仅是一个变量，这意味��Coq 的

    本地归纳策略不会给我们归纳假设

    我们想要的。可以解决这个问题，但需要

    泛化有点棘手。另一方面的项 t

    手，是完全通用的。

```

    Proof with eauto.
  intros Γ x U t v T Ht Ht'.
  generalize dependent Γ. generalize dependent T.
  induction t; intros T Γ H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  - (* tvar *)
    rename i into y. destruct (beq_idP x y) as [Hxy|Hxy].
    + (* x=y *)
      subst.
      rewrite update_eq in H[2].
      inversion H[2]; subst.
      eapply context_invariance. eassumption.
      apply typable_empty__closed in Ht'. unfold closed in Ht'.
      intros. apply (Ht' x[0]) in H[0]. inversion H[0].
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H[2]...
  - (* tabs *)
    rename i into y. rename t into T. apply T_Abs.
    destruct (beq_idP x y) as [Hxy | Hxy].
    + (* x=y *)
      subst. rewrite update_shadow in H[5]. apply H[5].
    + (* x<>y *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (beq_idP y z) as [Hyz | Hyz]; subst; trivial.
      rewrite ← beq_id_false_iff in Hxy.
      rewrite Hxy...
    Qed.

```

## 主定理

    现在我们有了证明保持性所需的工具：如果一个封闭

    项 t 具有类型 T 并且步骤到 t'，那么 t'

    也是一个具有类型 T 的封闭项。换句话说，小步

    缩减关系保持类型。

```
Theorem preservation : ∀t t' T,
     empty ⊢ t ∈ T  →
     t ⇒ t'  →
     empty ⊢ t' ∈ T.

```

    *证明*：通过对 ⊢ t ∈ T 的推导进行归纳。

+   我们可以立即排除 T_Var、T_Abs、T_True 和 T_False 作为推导中的最终规则，因为在这些情况下 t 无法进行步骤。

+   如果推导中的最后一个规则是 T_App，则 t = t[1] t[2]。有三种情况需要考虑，每种情况对应一个用于显示 t[1] t[2]步骤到 t'的规则。

    +   如果 t[1] t[2]通过 ST_App1 步骤，其中 t[1]步骤到 t[1]'，那么根据 IH，t[1]'与 t[1]具有相同类型，因此 t[1]' t[2]与 t[1] t[2]具有相同类型。

    +   ST_App2 情况类似。

    +   如果 t[1] t[2]通过 ST_AppAbs 步骤，则 t[1] = \x:T[11].t12，t[1] t[2]步骤到[x:=t[2]]t[12]；现在所需的结果由于替换保持类型的事实而得出。

+   如果推导中的最后一个规则是 T_If，则 t = if t[1] then t[2] else t[3]，并且根据 t 的步骤有三种情况。

    +   如果 t 步骤到 t[2]或 t[3]，结果是显而易见的，因为 t[2]和 t[3]与 t 具有相同的类型。

    +   否则，通过 ST_If，t 步骤，所需结论直接由归纳假设得出。

```

    Proof with eauto.
  remember (@empty ty) as Γ.
  intros t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE; subst Γ; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,        and eauto takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T[11]...
      inversion HT[1]...
    Qed.

```

#### 练习：2 星，推荐 M（subject_expansion_stlc）

    类型章节中的一个练习询问算术简单语言的*主题扩展*属性

    布尔表达式。STLC 是否满足这个属性？也就是说，

    如果 t ⇒ t'并且 has_type t' T，

    然后 empty ⊢ t ∈ T？如果是这样，请证明。如果不是，请给出一个

    不涉及条件的反例。

    (* 在这里填写 *)

    ☐

```

# Type Soundness

#### Exercise: 2 stars, optional (type_soundness)

    Put progress and preservation together and show that a well-typed
    term can *never* reach a stuck state.

```

定义卡住（t:tm）：Prop =

（normal_form step）t ∧ ¬ value t。

推论正确性：∀t t' T，

empty ⊢ t ∈ T →

t ⇒* t' →

~(卡住 t')。

    证明。

intros t t' T Hhas_type Hmulti. 展开卡住。

intros [Hnf Hnot_val]。在 Hnf 中展开 normal_form。

对 Hmulti 进行归纳。

(* 在这里填写 *) 已承认。

```

    ☐

```

# 类型的唯一性

#### 练习：3 星 M（types_unique）

    STLC 的另一个好处是类型是唯一的：

    给定术语（在给定上下文中）最多只有一个类型。形式化这个陈述并证明它。

```
(* FILL IN HERE *)

```

    ☐

```

# Additional Exercises

#### Exercise: 1 starM (progress_preservation_statement)

    Without peeking at their statements above, write down the progress
    and preservation theorems for the simply typed lambda-calculus (as 
    Coq theorems).

```

(* 在这里填写 *)

```

    ☐ 

#### Exercise: 2 starsM (stlc_variation1)

    Suppose we add a new term zap with the following reduction rule

           |

                        (ST_Zap)  
           |

* * *

           |

                        t ⇒ zap
           |

                     |

    and the following typing rule:

           |

                        (T_Zap)  
           |

* * *

           |

                        Γ ⊢ zap : T
           |

                     |

    Which of the following properties of the STLC remain true in
    the presence of these rules?  For each property, write either
    "remains true" or "becomes false." If a property becomes
    false, give a counterexample.

*   Determinism of step

    (* FILL IN HERE *)

*   Progress

    (* FILL IN HERE *)

*   Preservation

    (* FILL IN HERE *)

    ☐ 

#### Exercise: 2 starsM (stlc_variation2)

    Suppose instead that we add a new term foo with the following 
    reduction rules:

           |

                        (ST_Foo1)  
           |

* * *

           |

                        (λx:A. x) ⇒ foo
           |

                     |

           |

                        (ST_Foo2)  
           |

* * *

           |

                        foo ⇒ true
           |

                     |

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

*   Determinism of step

    (* FILL IN HERE *)

*   Progress

    (* FILL IN HERE *)

*   Preservation

    (* FILL IN HERE *)

    ☐ 

#### Exercise: 2 starsM (stlc_variation3)

    Suppose instead that we remove the rule ST_App1 from the step
    relation. Which of the following properties of the STLC remain
    true in the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

*   Determinism of step

    (* FILL IN HERE *)

*   Progress

    (* FILL IN HERE *)

*   Preservation

    (* FILL IN HERE *)

    ☐ 

#### Exercise: 2 stars, optional (stlc_variation4)

    Suppose instead that we add the following new rule to the 
    reduction relation:

           |

                        (ST_FunnyIfTrue)  
           |

* * *

           |

                        (if true then t[1] else t[2]) ⇒ true
           |

                     |

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

*   Determinism of step

    (* FILL IN HERE *)

*   Progress

    (* FILL IN HERE *)

*   Preservation

    (* FILL IN HERE *)

    ☐ 

#### Exercise: 2 stars, optional (stlc_variation5)

    Suppose instead that we add the following new rule to the typing 
    relation:

                        Γ ⊢ t[1] ∈ Bool->Bool->Bool
           |

                     |

                        Γ ⊢ t[2] ∈ Bool
           |

                        (T_FunnyApp)  
           |

* * *

           |

                        Γ ⊢ t[1] t[2] ∈ Bool
           |

                     |

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

*   Determinism of step

    (* FILL IN HERE *)

*   Progress

    (* FILL IN HERE *)

*   Preservation

    (* FILL IN HERE *)

    ☐ 

#### Exercise: 2 stars, optional (stlc_variation6)

    Suppose instead that we add the following new rule to the typing 
    relation:

                        Γ ⊢ t[1] ∈ Bool
           |

                     |

                        Γ ⊢ t[2] ∈ Bool
           |

                        (T_FunnyApp')  
           |

* * *

           |

                        Γ ⊢ t[1] t[2] ∈ Bool
           |

                     |

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

*   Determinism of step

    (* FILL IN HERE *)

*   Progress

    (* FILL IN HERE *)

*   Preservation

    (* FILL IN HERE *)

    ☐ 

#### Exercise: 2 stars, optional (stlc_variation7)

    Suppose we add the following new rule to the typing relation 
    of the STLC:

           |

                        (T_FunnyAbs)  
           |

* * *

           |

                        ⊢ \x:Bool.t ∈ Bool
           |

                     |

    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

*   Determinism of step

    (* FILL IN HERE *)

*   Progress

    (* FILL IN HERE *)

*   Preservation

    (* FILL IN HERE *)

    ☐

```

结束 STLCProp。

```

## Exercise: STLC with Arithmetic

    To see how the STLC might function as the core of a real
    programming language, let's extend it with a concrete base
    type of numbers and some constants and primitive
    operators.

```

模块 STLCArith。

导入 STLC。

```

    To types, we add a base type of natural numbers (and remove
    booleans, for brevity).

```

归纳定义 ty : Type :=

| TArrow : ty → ty → ty

| TNat   : ty.

```

    To terms, we add natural number constants, along with
    successor, predecessor, multiplication, and zero-testing.

```

归纳定义 tm : Type :=

| tvar : id → tm

| tapp : tm → tm → tm

| tabs : id → ty → tm → tm

| tnat  : nat → tm

| tsucc : tm → tm

| tpred : tm → tm

| tmult : tm → tm → tm

| tif0  : tm → tm → tm → tm.

```

#### Exercise: 4 starsM (stlc_arith)

    Finish formalizing the definition and properties of the STLC
    extended with arithmetic.  Specifically:

*   Copy the core definitions and theorems for STLC that we went through above (from the definition of values through the Preservation theorem, inclusive), and paste it into the file at this point. Do not copy examples, exercises, etc. (In particular, make sure you don't copy any of the ☐ comments at the end of exercises, to avoid confusing the autograder.) 

*   Extend the definitions of the subst operation and the step relation to include appropriate clauses for the arithmetic operators. 

*   Extend the proofs of all the properties (up to preservation) of the original STLC to deal with the new syntactic forms. Make sure Coq accepts the whole file.

```

(* 在这里填写 *)

```

    ☐

```

结束 STLCArith。

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
