# 向 STLC 添加记录

```

```

导入 Maps。

导入 Imp。

导入 Smallstep。

导入 Stlc。

```

# Adding Records

    We saw in chapter MoreStlc how records can be treated as just
    syntactic sugar for nested uses of products.  This is OK for
    simple examples, but the encoding is informal (in reality, if we
    actually treated records this way, it would be carried out in the
    parser, which we are eliding here), and anyway it is not very
    efficient.  So it is also interesting to see how records can be
    treated as first-class citizens of the language.  This chapter
    shows how.

    Recall the informal definitions we gave before: 

    Syntax:

```

    t ::=                          项：

        | {i1=t1, ..., in=tn}         记录

        | t.i                         投影

        | ...

    v ::=                          值：

        | {i1=v1, ..., in=vn}         记录值

        | ...

    T ::=                          类型：

        | {i1:T1, ..., in:Tn}         记录类型

        | ...

```

    Reduction:

                        ti ⇒ ti'                            (ST_Rcd)
           |

           |

* * *

           |

                        {i[1]=v[1], ..., im=vm, in=tn, ...} ⇒ {i[1]=v[1], ..., im=vm, in=tn', ...}
           |

                     |

                        t[1] ⇒ t[1]'
           |

                        (ST_Proj1)  
           |

* * *

           |

                        t[1].i ⇒ t[1]'.i
           |

                     |

           |

                        (ST_ProjRcd)  
           |

* * *

           |

                        {..., i=vi, ...}.i ⇒ vi
           |

                     |

    Typing:

                        Γ ⊢ t[1] : T[1]     ...     Γ ⊢ tn : Tn
           |

                        (T_Rcd)  
           |

* * *

           |

                        Γ ⊢ {i[1]=t[1], ..., in=tn} : {i[1]:T[1], ..., in:Tn}
           |

                     |

                        Γ ⊢ t : {..., i:Ti, ...}
           |

                        (T_Proj)  
           |

* * *

           |

                        Γ ⊢ t.i : Ti
           |

                     |

```

# 形式化记录

```
Module STLCExtendedRecords.

```

### 语法和操作语义

    形式化记录类型的语法最明显的方法是

    可能是这样的：

```
Module FirstTry.

Definition alist (X : Type) := list (id * X).

Inductive ty : Type :=
  | TBase     : id → ty
  | TArrow    : ty → ty → ty
  | TRcd      : (alist ty) → ty.

```

    不幸的是，在 Coq 中遇到了一个限制：这种类型

    不会自动给我们期望的归纳原理：

    TRcd 案例中的归纳假设并没有给我们

    任何关于列表的 ty 元素的信息，使其

    对我们想要进行的证明没有用处。

```
(* Check ty_ind.    ====>     ty_ind :       forall P : ty -> Prop,         (forall i : id, P (TBase i)) ->         (forall t : ty, P t -> forall t[0] : ty, P t[0]                              -> P (TArrow t t[0])) ->         (forall a : alist ty, P (TRcd a)) ->    (* ??? *)         forall t : ty, P t *)

End FirstTry.

```

    可以从 Coq 中获得更好的归纳原理，但

    如何完成这个任务的细节并不是很美观，而且

    我们得到的原则并不像 Coq 中的那些直观易用。

    为简单的归纳定义自动生成。

    幸运的是，有一种不同的形式化记录的方法

    在某种程度上，更简单更自然：而不是使用

    标准的 Coq 列表类型，我们基本上可以将其

    构造子（“nil” 和 “cons”）的语法中。

```
Inductive ty : Type :=
  | TBase : id → ty
  | TArrow : ty → ty → ty
  | TRNil : ty
  | TRCons : id → ty → ty → ty.

```

    同样，在项的层面上，我们有构造子 trnil，

    对于空记录，和 trcons，它添加一个字段到

    列字段的前面。

```
Inductive tm : Type :=
  | tvar : id → tm
  | tapp : tm → tm → tm
  | tabs : id → ty → tm → tm
  (* records *)
  | tproj : tm → id → tm
  | trnil :  tm
  | trcons : id → tm → tm → tm.

```

    一些例子...

```
Notation a := (Id "a").
Notation f := (Id "f").
Notation g := (Id "g").
Notation l := (Id "l").
Notation A := (TBase (Id "A")).
Notation B := (TBase (Id "B")).
Notation k := (Id "k").
Notation i[1] := (Id "i1").
Notation i[2] := (Id "i2").

```

    { i[1]:A }

```
(* Check (TRCons i[1] A TRNil). *)

```

    { i[1]:A→B, i[2]:A }

```
(* Check (TRCons i[1] (TArrow A B)            (TRCons i[2] A TRNil)). *)

```

### 合法性

    从一般化记录的抽象语法存在一个问题

    将列表转换为 nil/cons 表示法的原因是它引入了

    写出像这样奇怪的类型的可能性...

```
Definition weird_type := TRCons X A B.

```

    其中记录类型的“尾部”实际上不是记录类型！

    我们将构造我们的类型判断，以便没有不合法的类型

    像 weird_type 这样的类型从未分配给项。为了支持这一点，我们

    定义谓词 record_ty 和 record_tm，用于识别

    记录类型和项，以及 well_formed_ty，它排除了

    不合法的类型。

    首先，如果只使用 TRNil 构造一个类型，则该类型是记录类型

    和 TRCons 在最外层。

```
Inductive record_ty : ty → Prop :=
  | RTnil :
        record_ty TRNil
  | RTcons : ∀i T[1] T[2],
        record_ty (TRCons i T[1] T[2]).

```

    有了这个，我们可以定义良好形成的类型。

```
Inductive well_formed_ty : ty → Prop :=
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

Hint Constructors record_ty well_formed_ty.

```

    注意 record_ty 和 record_tm 不是递归的 —— 它们

    只需检查最外层的构造子。well_formed_ty

    另一方面，该属性验证整个类型是否良好形成

    在 TRcd 案例中，整个类型都是良好形成的。

    TRCons 的参数）是一个记录。

    当然，我们也应该关注不合法的项，而不是

    只是类型；但是类型检查可以排除这些，而不需要帮助

    由于它已经有了额外的 well_formed_tm 定义

    检查项的结构。我们只需要一个类似于

    record_ty 表示一个项是记录项，如果它是由

    使用 trnil 和 trcons。

```
Inductive record_tm : tm → Prop :=
  | rtnil :
        record_tm trnil
  | rtcons : ∀i t[1] t[2],
        record_tm (trcons i t[1] t[2]).

Hint Constructors record_tm.

```

### 替换

    替换很容易扩展。

```
Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar y ⇒ if beq_id x y then s else t
  | tabs y T t[1] ⇒ tabs y T
                     (if beq_id x y then t[1] else (subst x s t[1]))
  | tapp t[1] t[2] ⇒ tapp (subst x s t[1]) (subst x s t[2])
  | tproj t[1] i ⇒ tproj (subst x s t[1]) i
  | trnil ⇒ trnil
  | trcons i t[1] tr[1] ⇒ trcons i (subst x s t[1]) (subst x s tr[1])
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

```

### 规约

    如果所有字段都是，则记录是一个值。

```
Inductive value : tm → Prop :=
  | v_abs : ∀x T[11] t[12],
      value (tabs x T[11] t[12])
  | v_rnil : value trnil
  | v_rcons : ∀i v[1] vr,
      value v[1] →
      value vr →
      value (trcons i v[1] vr).

Hint Constructors value.

```

    为了定义规约，我们需要一个用于提取的实用函数

    one field from record term:

```
Fixpoint tlookup (i:id) (tr:tm) : option tm :=
  match tr with
  | trcons i' t tr' ⇒ if beq_id i i' then Some t else tlookup i tr'
  | _ ⇒ None
  end.

```

    The step function uses this term-level lookup function in the

    projection rule.

```
Reserved Notation "t1 '⇒' t2" (at level 40).

Inductive step : tm → tm → Prop :=
  | ST_AppAbs : ∀x T[11] t[12] v[2],
         value v[2] →
         (tapp (tabs x T[11] t[12]) v[2]) ⇒ ([x:=v[2]]t[12])
  | ST_App1 : ∀t[1] t[1]' t[2],
         t[1] ⇒ t[1]' →
         (tapp t[1] t[2]) ⇒ (tapp t[1]' t[2])
  | ST_App2 : ∀v[1] t[2] t[2]',
         value v[1] →
         t[2] ⇒ t[2]' →
         (tapp v[1] t[2]) ⇒ (tapp v[1] t[2]')
  | ST_Proj1 : ∀t[1] t[1]' i,
        t[1] ⇒ t[1]' →
        (tproj t[1] i) ⇒ (tproj t[1]' i)
  | ST_ProjRcd : ∀tr i vi,
        value tr →
        tlookup i tr = Some vi →
        (tproj tr i) ⇒ vi
  | ST_Rcd_Head : ∀i t[1] t[1]' tr[2],
        t[1] ⇒ t[1]' →
        (trcons i t[1] tr[2]) ⇒ (trcons i t[1]' tr[2])
  | ST_Rcd_Tail : ∀i v[1] tr[2] tr[2]',
        value v[1] →
        tr[2] ⇒ tr[2]' →
        (trcons i v[1] tr[2]) ⇒ (trcons i v[1] tr[2]')

where "t1 '⇒' t2" := (step t[1] t[2]).

Notation multistep := (multi step).
Notation "t1 '⇒*' t2" := (multistep t[1] t[2]) (at level 40).

Hint Constructors step.

```

### Typing

    Next we define the typing rules.  These are nearly direct

    transcriptions of the inference rules shown above: the only

    significant difference is the use of well_formed_ty.  In the

    informal presentation we used a grammar that only allowed

    well-formed record types, so we didn't have to add a separate

    check.

    One sanity condition that we'd like to maintain is that, whenever

    has_type Γ t T holds, will also be the case that

    well_formed_ty T, so that has_type never assigns ill-formed

    types to terms.  In fact, we prove this theorem below.  However,

    we don't want to clutter the definition of has_type with

    unnecessary uses of well_formed_ty.  Instead, we place

    well_formed_ty checks only where needed: where an inductive call

    to has_type won't already be checking the well-formedness of a

    type.  For example, we check well_formed_ty T in the T_Var

    case, because there is no inductive has_type call that would

    enforce this.  Similarly, in the T_Abs case, we require a proof

    of well_formed_ty T[11] because the inductive call to has_type

    only guarantees that T[12] is well-formed.

```
Fixpoint Tlookup (i:id) (Tr:ty) : option ty :=
  match Tr with
  | TRCons i' T Tr' ⇒
      if beq_id i i' then Some T else Tlookup i Tr'
  | _ ⇒ None
  end.

Definition context := partial_map ty.

Reserved Notation "Gamma '⊢' t '∈' T" (at level 40).

Inductive has_type : context → tm → ty → Prop :=
  | T_Var : ∀Γ x T,
      Γ x = Some T →
      well_formed_ty T →
      Γ ⊢ (tvar x) ∈ T
  | T_Abs : ∀Γ x T[11] T[12] t[12],
      well_formed_ty T[11] →
      (update Γ x T[11]) ⊢ t[12] ∈ T[12] →
      Γ ⊢ (tabs x T[11] t[12]) ∈ (TArrow T[11] T[12])
  | T_App : ∀T[1] T[2] Γ t[1] t[2],
      Γ ⊢ t[1] ∈ (TArrow T[1] T[2]) →
      Γ ⊢ t[2] ∈ T[1] →
      Γ ⊢ (tapp t[1] t[2]) ∈ T[2]
  (* records: *)
  | T_Proj : ∀Γ i t Ti Tr,
      Γ ⊢ t ∈ Tr →
      Tlookup i Tr = Some Ti →
      Γ ⊢ (tproj t i) ∈ Ti
  | T_RNil : ∀Γ,
      Γ ⊢ trnil ∈ TRNil
  | T_RCons : ∀Γ i t T tr Tr,
      Γ ⊢ t ∈ T →
      Γ ⊢ tr ∈ Tr →
      record_ty Tr →
      record_tm tr →
      Γ ⊢ (trcons i t tr) ∈ (TRCons i T Tr)

where "Gamma '⊢' t '∈' T" := (has_type Γ t T).

Hint Constructors has_type.

```

## Examples

#### Exercise: 2 stars (examples)

    Finish the proofs below.  Feel free to use Coq's automation

    features in this proof.  However, if you are not confident about

    how the type system works, you may want to carry out the proofs

    first using the basic features (apply instead of eapply, in

    particular) and then perhaps compress it using automation.  Before

    starting to prove anything, make sure you understand what it is

    saying.

```
Lemma typing_example_2 :
  empty ⊢
    (tapp (tabs a (TRCons i[1] (TArrow A A)
                      (TRCons i[2] (TArrow B B)
                       TRNil))
              (tproj (tvar a) i[2]))
            (trcons i[1] (tabs a A (tvar a))
            (trcons i[2] (tabs a B (tvar a))
             trnil))) ∈
    (TArrow B B).
Proof.
  (* FILL IN HERE *) Admitted.

Example typing_nonexample :
  ¬ ∃T,
      (update empty a (TRCons i[2] (TArrow A A)
                                TRNil)) ⊢
               (trcons i[1] (tabs a B (tvar a)) (tvar a)) ∈
               T.
Proof.
  (* FILL IN HERE *) Admitted.

Example typing_nonexample_2 : ∀y,
  ¬ ∃T,
    (update empty y A) ⊢
           (tapp (tabs a (TRCons i[1] A TRNil)
                     (tproj (tvar a) i[1]))
                   (trcons i[1] (tvar y) (trcons i[2] (tvar y) trnil))) ∈
           T.
Proof.
  (* FILL IN HERE *) Admitted.

```

## Properties of Typing

    The proofs of progress and preservation for this system are

    essentially the same as for the pure simply typed lambda-calculus,

    but we need to add some technical lemmas involving records.

```

### Well-Formedness

```

Lemma wf_rcd_lookup : ∀i T Ti,

well_formed_ty T →

Tlookup i T = Some Ti →

well_formed_ty Ti.

    Proof with eauto.

intros i T.

induction T; intros; try solve_by_invert.

- (* TRCons *)

inversion H. subst. unfold Tlookup in H[0].

destruct (beq_id i i[0])...

inversion H[0]. subst... Qed.

Lemma step_preserves_record_tm : ∀tr tr',

record_tm tr →

tr ⇒ tr' →

record_tm tr'.

    Proof.

intros tr tr' Hrt Hstp.

inversion Hrt; subst; inversion Hstp; subst; auto.

    Qed.

Lemma has_type__wf : ∀Γ t T,

Γ ⊢ t ∈ T → well_formed_ty T.

    Proof with eauto.

intros Γ t T Htyp.

induction Htyp...

- (* T_App *)

inversion IHHtyp1...

- (* T_Proj *)

eapply wf_rcd_lookup...

    Qed.

```

### Field Lookup

    Lemma: If empty ⊢ v : T and Tlookup i T returns Some Ti,
     then tlookup i v returns Some ti for some term ti such
     that empty ⊢ ti ∈ Ti.

    Proof: By induction on the typing derivation Htyp.  Since
      Tlookup i T = Some Ti, T must be a record type, this and
      the fact that v is a value eliminate most cases by inspection,
      leaving only the T_RCons case.

    If the last step in the typing derivation is by T_RCons, then
      t = trcons i[0] t tr and T = TRCons i[0] T Tr for some i[0],
      t, tr, T and Tr.

    This leaves two possiblities to consider - either i[0] = i or
      not.

*   If i = i[0], then since Tlookup i (TRCons i[0] T Tr) = Some Ti we have T = Ti. It follows that t itself satisfies the theorem. 

*   On the other hand, suppose i ≠ i[0]. Then 

    ```

    Tlookup i T = Tlookup i Tr

    and

    ```
    tlookup i t = tlookup i tr,

     so the result follows from the induction hypothesis. ☐
    ```

    ```

    Here is the formal statement:

```

Lemma lookup_field_in_value : ∀v T i Ti,

value v →

empty ⊢ v ∈ T →

Tlookup i T = Some Ti →

∃ti, tlookup i v = Some ti ∧ empty ⊢ ti ∈ Ti.

    Proof with eauto.

intros v T i Ti Hval Htyp Hget.

remember (@empty ty) as Γ.

induction Htyp; subst; try solve_by_invert...

- (* T_RCons *)

在 Hget 中简化。简化。将 (beq_id i i[0]) 解构为...

+ (* i 是第一个 *)

简化。反演 Hget。替换。

∃t...

+ (* 获取尾部 *)

将 IHHtyp2 解构为 [vi [Hgeti Htypi]]...

反演 Hval... 完成。

```

### Progress

```

定理 progress：对于所有的 t 和 T，

empty ⊢ t ∈ T →

值 t 或 ∃t'，t ⇒ t'。

    证明使用 eauto。

(* 定理：假设 empty |- t : T。  那么要么        1. t 是一个值，要么        2. 存在某个 t' 使得 t ==> t'。       证明：通过对给定的类型推导进行归纳。 *)

对于 t 和 T，引入 Ht。

记住 (@empty ty）作为 Γ。

推广 HeqGamma。

对 Ht 进行归纳；引入 HeqGamma；替换。

- (* T_Var *)

(* 给定的类型推导中最后一条规则不能是 T_Var，因为永远不可能出现        empty ⊢ x : T（因为上下文为空）。 *)

反演 H。

- (* T_Abs *)

(* 如果最后使用的规则是 T_Abs，那么     ��  t = tabs x T[11] t[12]，这是一个值。 *)

left...

- (* T_App *)

(* 如果应用的最后一条规则是 T_App，那么 t = t[1] t[2]，        并且根据规则的形式我们知道          empty ⊢ t[1] : T[1] → T[2]          empty ⊢ t[2] : T[1]        根据归纳假设，t[1] 和 t[2] 要么是值，要么可以进行一步操作。 *)

right。

将 IHHt1 解构；替换...

+ (* t[1] 是值 *)

将 IHHt2 解构；替换...

* (* t[2] 是值 *)

(* 如果 t[1] 和 t[2] 都是值，那么我们知道          t[1] = tabs x T[11] t[12]，因为抽象是唯一          可能具有箭头类型的值。  但          (tabs x T[11] t[12]) t[2] ⇒ [x:=t[2]]t[12] 通过 ST_AppAbs。 *)

反演 H；替换；尝试通过反演解决。

∃([x:=t[2]]t[12])...

* (* t[2] 步骤 *)

(* 如果 t[1] 是一个值且 t[2] ⇒ t[2]'，那么            t[1] t[2] ⇒ t[1] t[2]' 通过 ST_App2。 *)

将 H[0] 解构为 [t[2]' Hstp]。∃(tapp t[1] t[2]')...

+ (* t[1] 步骤 *)

(* 最后，如果 t[1] ⇒ t[1]'，那么 t[1] t[2] ⇒ t[1]' t[2]           通过 ST_App1。 *)

将 H 解构为 [t[1]' Hstp]. ∃(tapp t[1]' t[2])...

- (* T_Proj *)

(* 如果给定推导中最后一条规则是 T_Proj，那么        t = tproj t i 且            empty ⊢ t : (TRcd Tr)        根据 IH，t 要么是一个值，要么会进行一步操作。 *)

right。将 IHHt 解构为...

+ (* rcd 是值 *)

(* 如果 t 是一个值，那么我们可以使用引理          lookup_field_in_value 来展示 tlookup i t = Some ti           对于某个 ti，这给我们 tproj i t ⇒ ti 通过          ST_ProjRcd。 *)

将 (lookup_field_in_value _ _ _ _ H[0] Ht H) 解构为...

将 [ti [Hlkup _]] 作为右值。

∃ti...

+ (* rcd 步骤 *)

(* 另一方面，如果 t ⇒ t'，那么          tproj t i ⇒ tproj t' i 通过 ST_Proj1。 *)

将 H[0] 解构为 [t' Hstp]。∃(tproj t' i)...

- (* T_RNil *)

(* 如果给定推导中最后一条规则是 T_RNil，        那么 t = trnil，这是一个值。 *)

left...

- (* T_RCons *)

(* 如果最后一条规则是 T_RCons，那么 t = trcons i t tr 并且 empty ⊢ t : T empty ⊢ tr : Tr 通过 IH，t 和 tr 中的每一个要么是一个值，要么可以进行一步操作。*)

destruct IHHt1...

+ (* 头是一个值*)

destruct IHHt2; try reflexivity.

* (* 尾部是一个值*)

(* 如果 t 和 tr 都是值，那么 trcons i t tr 也是一个值。*)

左边...

* (* 尾部步骤*)

(* 如果 t 是一个值，并且 tr ⇒ tr'，那么 trcons i t tr ⇒ trcons i t tr' 通过 ST_Rcd_Tail。*)

right. destruct H[2] as [tr' Hstp].

∃(trcons i t tr')...

+ (* 头步骤*)

(* 如果 t ⇒ t'，那么 trcons i t tr ⇒ trcons i t' tr 通过 ST_Rcd_Head。*)

right. destruct H[1] as [t' Hstp].

∃(trcons i t' tr)... 完成。

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

| afi_proj : ∀x t i,

appears_free_in x t →

appears_free_in x (tproj t i)

| afi_rhead : ∀x i ti tr,

appears_free_in x ti →

appears_free_in x (trcons i ti tr)

| afi_rtail : ∀x i ti tr,

appears_free_in x tr →

appears_free_in x (trcons i ti tr).

使用 Hint Constructors appears_free_in。

Lemma context_invariance : ∀Γ Γ' t S,

Γ ⊢ t ∈ S  →

(∀x, appears_free_in x t → Γ x = Γ' x)  →

Γ' ⊢ t ∈ S.

    Proof with eauto.

intros. generalize dependent Γ'.

对 H 进行归纳；

intros Γ' Heqv...

- (* T_Var *)

应用 T_Var... 重写 ← Heqv...

- (* T_Abs *)

应用 T_Abs... 应用 IHhas_type。intros y Hafi。

展开 update, t_update。对 (beq_idP x y) 进行分析...

- (* T_App *)

应用 T_App with T[1]...

- (* T_RCons *)

应用 T_RCons... 完成。

Lemma free_in_context : ∀x t T Γ,

appears_free_in x t →

Γ ⊢ t ∈ T →

∃T', Γ x = Some T'.

    Proof with eauto.

intros x t T Γ Hafi Htyp.

对 Htyp 进行归纳；反演 Hafi；替换...

- (* T_Abs *)

destruct IHHtyp as [T' Hctx]... ∃T'.

在 Hctx 中展开 update, t_update。

在 Hctx 中重写 false_beq_id...

    完成。

```

### Preservation

```

Lemma substitution_preserves_typing : ∀Γ x U v t S,

(update Γ x U) ⊢ t ∈ S  →

empty ⊢ v ∈ U   →

Γ ⊢ ([x:=v]t) ∈ S.

Proof with eauto.

(* 定理：如果 Gamma,x:U |- t : S 并且 empty |- v : U，则 Gamma |- (x:=vt) S。*)

intros Γ x U v t S Htypt Htypv.

generalize dependent Γ. generalize dependent S.

(* 证明：通过对项 t 进行归纳。大多数情况都可以      直接从 IH 推导出来，除了 tvar，      tabs，trcons。前者不是自动的，因为我们      必须推理变量如何相互作用。在      trcons 的情况下，我们必须做一些额外的工作来展示      替换一个项不会改变它是否      是一个记录项。*)

对 t 进行归纳;

推理 S Γ Htypt; 简化; 反演 Htypt; 替换...

- (* tvar *)

简化。将 i 重命名为 y。

(* 如果 t = y，我们知道          empty ⊢ v : U 和          Γ,x:U ⊢ y : S        ��且，通过反演，update Γ x U y = Some S。          我们想要展示 Γ ⊢ [x:=v]y : S。        有两种情况要考虑：要么 x=y，要么 x≠y。*)

展开 update, t_update 在 H[0] 中。

分解 (beq_idP x y) 得到 [Hxy|Hxy]。

+ (* x=y *)

(* 如果 x = y，那么我们知道 U = S，并且        [x:=v]y = v。所以我们真正需要展示的是        如果 empty ⊢ v : U，则 Γ ⊢ v : U。我们已经        证明了这个定理的一个更一般的版本，        称为上下文不变性！*)

替换。

反演 H[0]; 替换。清除 H[0]。

应用 context_invariance...

推理 x Hcontra。

分解 (free_in_context _ _ S empty Hcontra)

作为 [T' HT']...

反演 HT'。

+ (* x<>y *)

(* 如果 x ≠ y，那么 Γ y = Some S，替换        没有影响。我们可以展示 Γ ⊢ y : S 通过        T_Var。*)

应用 T_Var...

- (* tabs *)

将 i 重命名为 y。将 t 重命名为 T[11]。

(* 如果 t = tabs y T[11] t[0]，那么我们知道          Γ,x:U ⊢ tabs y T[11] t[0] : T[11]→T[12]          Γ,x:U,y:T[11] ⊢ t[0] : T[12]          empty ⊢ v : U        根据我们的 IH，我们知道对于所有的 S 和 Gamma，          Γ,x:U ⊢ t[0] : S → Γ ⊢ [x:=v]t[0] S。        我们可以计算出         [x:=v]t = tabs y T[11] (if beq_id x y then t[0] else [x:=v]t[0]) ，        我们必须展示 Γ ⊢ [x:=v]t : T[11]→T[12]。  我们知道        我们将使用 T_Abs 来做到这一点，所以我们还需要展示：          Γ,y:T[11] ⊢ if beq_id x y then t[0] else [x:=v]t[0] : T[12]        我们考虑两种情况：x = y 和 x ≠ y。*)

应用 T_Abs...

分解 (beq_idP x y) 得到 [Hxy|Hxy]。

+ (* x=y *)

(* 如果 x = y，那么替换没有影响。        上下文不变性表明 Γ,y:U,y:T[11] 和 Γ,y:T[11] 是        等价的。由于 t[0] : T[12] 在前者的上下文下，        在后者的上下文下也是如此。*)

应用 context_invariance...

替换。

推理 x Hafi。展开 update，t_update。

分解 (beq_id y x)...

+ (* x<>y *)

(* 如果 x ≠ y，那么 IH 和上下文不变性允许        我们展示          Γ,x:U,y:T[11] ⊢ t[0] : T[12]       =>          Γ,y:T[11],x:U ⊢ t[0] : T[12]       =>          Γ,y:T[11] ⊢ [x:=v]t[0] : T[12] *)

应用 IHt。应用 context_invariance...

引入 z Hafi。展开 update，t_update。

分解 (beq_idP y z)...

替换。重写 false_beq_id...

- (* trcons *)

应用 T_RCons... 反演 H[7]；替换；简化...

完成。

定理保持性：∀t t' T，

空 ⊢ t ∈ T  →

t ⇒ t'  →

空 ⊢ t' ∈ T。

证明与 eauto。

引入 t t' T HT。

(* 定理：如果 empty ⊢ t : T 并且 t ⇒ t'，那么 empty ⊢ t' : T。*)

记住 (@empty ty) 作为 Γ。泛化依赖于 HeqGamma。

泛化依赖于 t'。

(* 证明：根据给定的类型推导进行归纳。许多情况是矛盾的（T_Var，T_Abs），或直接从归纳假设中得出（T_RCons）。我们只展示有趣的情况。*)

对 HT 进行归纳；

引入 t' HeqGamma HE；替换；反演 HE；替换...

- (* T_App *)

(* 如果最后使用的规则是 T_App，则 t = t[1] t[2]，并且有三条规则可以用来展示 t ⇒ t'：ST_App1，ST_App2 和 ST_AppAbs。在前两种情况下，结果直接从归纳假设中得出。*)

反演 HE；替换...

+ (* ST_AppAbs *)

(* 对于第三种情况，假设            t[1] = tabs x T[11] t[12]          并且            t[2] = v[2]。我们必须展示 empty ⊢ [x:=v[2]]t[12] : T[2]。根据假设，我们知道              empty ⊢ tabs x T[11] t[12] : T[1]→T[2]          并且通过反演              x:T[1] ⊢ t[12] : T[2]。我们已经证明了 substitution_preserves_typing，并且              empty ⊢ v[2] : T[1]。因此，我们完成了。*)

应用 substitution_preserves_typing 与 T[1]...

反演 HT[1]...

- (* T_Proj *)

(* 如果最后一条规则是 T_Proj，则 t = tproj t[1] i。两条规则可能导致 t ⇒ t'：T_Proj1 和 T_ProjRcd。在前一种情况中，t' 的类型遵循自归纳假设，因此我们只考虑 T_ProjRcd。在这里，我们知道 t 是一个记录值。由于使用了规则 T_Proj，我们知道 empty ⊢ t ∈ Tr，并且对于某个 i 和 Tr，Tlookup i Tr = Some Ti。因此，我们可以应用引理 lookup_field_in_value 找到此投影步骤到的记录元素。*)

分解 (lookup_field_in_value _ _ _ _ H[2] HT H)

作为 [vi [Hget Htyp]]。

重写 H[4] 在 Hget 中。反演 Hget。替换...

- (* T_RCons *)

(* 如果最后一条规则是 T_RCons，则 t = trcons i t tr，其中存在某个 i、t 和 tr，使得 record_tm tr 成立。如果步骤是通过 ST_Rcd_Head，结果立即由归纳假设得出。如果步骤是通过 ST_Rcd_Tail，tr ⇒ tr[2]'，对于某个 tr[2]'，我们还必须使用引理 step_preserves_record_tm 来展示 record_tm tr[2]'。*)

应用 T_RCons... 应用 step_preserves_record_tm...

QED。

```

    ☐

```

结束 STLCExtendedRecords。

```

```

```

```
