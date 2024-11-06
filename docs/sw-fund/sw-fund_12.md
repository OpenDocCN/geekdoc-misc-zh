# 关系的关系属性

```

    This short (and optional) chapter develops some basic definitions
    and a few theorems about binary relations in Coq.  The key
    definitions are repeated where they are actually used (in the
    Smallstep chapter), so readers who are already comfortable with
    these ideas can safely skim or skip this chapter.  However,
    relations are also a good source of exercises for developing
    facility with Coq's basic reasoning facilities, so it may be
    useful to look at this material just after the IndProp
    chapter.

```

导出 IndProp。

```

    A binary *relation* on a set X is a family of propositions
    parameterized by two elements of X — i.e., a proposition about
    pairs of elements of X.

```

定义关系（X：Type）：= X → X → Prop。

```

    Confusingly, the Coq standard library hijacks the generic term
    "relation" for this specific instance of the idea. To maintain
    consistency with the library, we will do the same.  So, henceforth
    the Coq identifier relation will always refer to a binary
    relation between some set and itself, whereas the English word
    "relation" can refer either to the specific Coq concept or the
    more general concept of a relation between any number of possibly
    different sets.  The context of the discussion should always make
    clear which is meant. 

    An example relation on nat is le, the less-than-or-equal-to
    relation, which we usually write n[1] ≤ n[2].

```

打印 le。

(* ====> 归纳 le（n：nat）：nat -> Prop :=              le_n：n <= n            | le_S：forall m：nat，n <= m -> n <= S m *)

检查 le：nat → nat → Prop。

检查 le：关系 nat。

```

    (Why did we write it this way instead of starting with Inductive le : relation nat...?  Because we wanted to put the first nat
    to the left of the :, which makes Coq generate a somewhat nicer
    induction principle for reasoning about ≤.)

```

# 基本属性

    任何上过本科离散数学的人都知道

    课程，关于一般关系有很多可以说的，

    包括对关系进行分类的方法（作为反射性，传递性，

    等等），可以通用地证明关于某些类型的定理

    关系的构造，从另一个构建一个关系的构造，

    等等。���如...

### 部分函数

    集合 X 上的关系 R 是*部分函数*，如果对于每个

    x，最多只有一个 y 满足 R x y — 即，R x y[1]

    和 R x y[2]一起暗示 y[1] = y[2]。

```
Definition partial_function {X: Type} (R: relation X) :=
  ∀x y[1] y[2] : X, R x y[1] → R x y[2] → y[1] = y[2].

```

    例如，先前定义的 next_nat 关系是一个部分

    函数。

```
Print next_nat.
(* ====> Inductive next_nat (n : nat) : nat -> Prop :=            nn : next_nat n (S n) *)
Check next_nat : relation nat.

Theorem next_nat_partial_function :
   partial_function next_nat.

    Proof.
  unfold partial_function.
  intros x y[1] y[2] H[1] H[2].
  inversion H[1]. inversion H[2].
  reflexivity. Qed.

```

    然而，数字上的≤关系不是一个部分

    函数。（假设，为了矛盾，≤是一个部分

    函数。但是，由于 0 ≤ 0 和 0 ≤ 1，所以

    0 = 1。这是荒谬的，所以我们的假设是

    矛盾。）

```
Theorem le_not_a_partial_function :
  ¬ (partial_function le).

    Proof.
  unfold [not](http://coq.inria.fr/library/Coq.Init.Logic.html#not). unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. { 
    apply Hc with (x := 0).
    - apply [le_n](http://coq.inria.fr/library/Coq.Init.Peano.html#le_n).
    - apply [le_S](http://coq.inria.fr/library/Coq.Init.Peano.html#le_S). apply [le_n](http://coq.inria.fr/library/Coq.Init.Peano.html#le_n). }
  inversion Nonsense. Qed.

```

#### 练习：2 星，可选

    显示先前定义的 total_relation 不是一个部分

    函数。

```
(* FILL IN HERE *)

```

    ☐

#### 练习：2 星，可选

    显示我们先前定义的 empty_relation 是一个

    部分函数。

```
(* FILL IN HERE *)

```

    ☐

### 反射关系

    集合 X 上的*反射*关系是每个元素都是这样的关系

    X 的元素与自身相关联。

```
Definition reflexive {X: Type} (R: relation X) :=
  ∀a : X, R a a.

Theorem le_reflexive :
  reflexive le.

    Proof.
  unfold reflexive. intros n. apply [le_n](http://coq.inria.fr/library/Coq.Init.Peano.html#le_n). Qed.

```

### 传递关系

    如果 R a b 和 R a c 成立，则关系 R 是*传递*的。

    和 R b c。

```
Definition transitive {X: Type} (R: relation X) :=
  ∀a b c : X, (R a b) → (R b c) → (R a c).

Theorem le_trans :
  transitive le.

    Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply [le_S](http://coq.inria.fr/library/Coq.Init.Peano.html#le_S). apply IHHmo. Qed.

Theorem lt_trans:
  transitive lt.

    Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply [le_S](http://coq.inria.fr/library/Coq.Init.Peano.html#le_S) in Hnm.
  apply le_trans with (a := ([S](http://coq.inria.fr/library/Coq.Init.Datatypes.html#S) n)) (b := ([S](http://coq.inria.fr/library/Coq.Init.Datatypes.html#S) m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

```

#### 练习：2 星，可选

    我们也可以通过归纳更费力地证明 lt_trans，

    不使用 le_trans。做到这一点。

```
Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：2 星，可选

    再次通过对 o 的归纳证明相同的事情。

```
Theorem lt_trans'' :
  transitive lt.

    Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  (* FILL IN HERE *) Admitted.

```

    ☐

    le 的传递性，反过来，可以用来证明一些事实

    这将在以后有用（例如，用于证明反对称性的证明

    下面）...

```
Theorem le_Sn_le : ∀n m, S n ≤ m → n ≤ m.

    Proof.
  intros n m H. apply le_trans with ([S](http://coq.inria.fr/library/Coq.Init.Datatypes.html#S) n).
  - apply [le_S](http://coq.inria.fr/library/Coq.Init.Peano.html#le_S). apply [le_n](http://coq.inria.fr/library/Coq.Init.Peano.html#le_n).
  - apply H.
    Qed.

```

#### 练习：1 星，可选

```
Theorem le_S_n : ∀n m,
  (S n ≤ S m) → (n ≤ m).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：2 星，可选（le_Sn_n_inf）

    提供以下定理的非正式证明：

    定理：对于每个 n，¬（S n ≤ n）

    这个的正式证明是下面的一个可选练习，但是尝试

    写一个非正式证明而不先进行形式证明。

    证明：

    (* 在这里填写 *)

    ☐

#### 练习：1 星，可选

```
Theorem le_Sn_n : ∀n,
  ¬ (S n ≤ n).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    反射性和传递性是我们将需要的主要概念

    后面的章节，但是，为了额外练习处理

    Coq 中的关系，让我们看看其他一些常见的...

### 对称和反对称关系

    如果 R a b 暗示 R b a，则关系 R 是*对称*的。

```
Definition symmetric {X: Type} (R: relation X) :=
  ∀a b : X, (R a b) → (R b a).

```

#### 练习：2 星，可选

```
Theorem le_not_symmetric :
  ¬ (symmetric le).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    如果 R a b 和 R b a 一起

    暗示 a = b — 也就是说，如果 R 中唯一的“循环”是平凡的

    一个。

```
Definition antisymmetric {X: Type} (R: relation X) :=
  ∀a b : X, (R a b) → (R b a) → a = b.

```

#### 练习：2 星，可选

```
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：2 星，可选

```
Theorem le_step : ∀n m p,
  n < m →
  m ≤ S p →
  n ≤ p.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

### 等价关系

    如果它是反射性，对称性和

    传递的。

```
Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) ∧ (symmetric R) ∧ (transitive R).

```

### 部分顺序和前序

    当它是反射性时，关系是*部分顺序*，

    *反*-对称和传递。在 Coq 标准库中

    简称为“order”。

```
Definition order {X:Type} (R: relation X) :=
  (reflexive R) ∧ (antisymmetric R) ∧ (transitive R).

```

    预序几乎类似于偏序，但不必

    反对称的。

```
Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) ∧ (transitive R).

Theorem le_order :
  order le.

    Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans. Qed.

```

# 自反传递闭包

    关系 R 的*自反传递闭包*是

    包含 R 并且既是自反的又是最小关系

    传递性。形式上，它是这样在 Relations 中定义的

    Coq 标准库的模块：

```
Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step : ∀x y, R x y → clos_refl_trans R x y
    | rt_refl : ∀x, clos_refl_trans R x x
    | rt_trans : ∀x y z,
          clos_refl_trans R x y →
          clos_refl_trans R y z →
          clos_refl_trans R x z.

```

    例如，关系的自反传递闭包

    next_nat 关系与 le 关系一致。

```
Theorem next_nat_closure_is_le : ∀n m,
  (n ≤ m) ↔ ((clos_refl_trans next_nat) n m).

    Proof.
  intros n m. split.
  - (* -> *)
    intro H. induction H.
    + (* le_n *) apply rt_refl.
    + (* le_S *)
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  - (* <- *)
    intro H. induction H.
    + (* rt_step *) inversion H. apply [le_S](http://coq.inria.fr/library/Coq.Init.Peano.html#le_S). apply [le_n](http://coq.inria.fr/library/Coq.Init.Peano.html#le_n).
    + (* rt_refl *) apply [le_n](http://coq.inria.fr/library/Coq.Init.Peano.html#le_n).
    + (* rt_trans *)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.

```

    上述自反传递闭包的定义是自然的：

    明确表示，关系 R 的自反传递闭包是

    R 是包含 R 并且是封闭的最小关系

    在自反性和传递性规则下。但事实证明

    这个定义并不是做证明很方便，

    由于 rt_trans 规则的“非确定性”有时候

    导致棘手的归纳。这里是一个更有用的定义：

```
Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A → Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A) :
      R x y → clos_refl_trans_1n R y z →
      clos_refl_trans_1n R x z.

```

    我们的新定义的自反传递闭包“捆绑”

    将 rt_step 和 rt_trans 规则合并为单一规则 step。

    这一步的左侧前提是 R 的单次使用，

    导致了一个更简单的归纳原理。

    在继续之前，我们应该检查一下这两个定义

    确实定义了相同的关系...

    首先，我们证明两个引理，表明 clos_refl_trans_1n 模拟

    两个“缺失”的 clos_refl_trans 的行为

    构造函数。

```
Lemma rsc_R : ∀(X:Type) (R:relation X) (x y : X),
       R x y → clos_refl_trans_1n R x y.

    Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl. Qed.

```

#### 练习：2 星，可选（rsc_trans）

```
Lemma rsc_trans :
  ∀(X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y  →
      clos_refl_trans_1n R y z →
      clos_refl_trans_1n R x z.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    然后我们利用这些事实证明了两个定义

    自反传递闭包确实定义了相同的

    关系。

#### 练习：3 星，可选（rtc_rsc_coincide）

```
Theorem rtc_rsc_coincide :
         ∀(X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y ↔ clos_refl_trans_1n R x y.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

```
