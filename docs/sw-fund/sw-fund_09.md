# MapsTotal 和 Partial Maps

```

    Maps (or dictionaries) are ubiquitous data structures both
    generally and in the theory of programming languages in
    particular; we're going to need them in many places in the coming
    chapters.  They also make a nice case study using ideas we've seen
    in previous chapters, including building data structures out of
    higher-order functions (from Basics and Poly) and the use of
    reflection to streamline proofs (from IndProp).

    We'll define two flavors of maps: *total* maps, which include a
    "default" element to be returned when a key being looked up
    doesn't exist, and *partial* maps, which return an option to
    indicate success or failure.  The latter is defined in terms of
    the former, using None as the default element.

```

# Coq 标准库

    在我们讨论映射之前稍作偏离。

    与我们迄今为止看到的章节不同，这一章不

    需要导入之前的章节（以及传递性地，所有

    早期章节）。相反，在这一章以及以后

    我们将导入我们需要的定义和定理

    直接从 Coq 的标准库中导入。你不应该注意到

    很大的区别，因为我们已经小心地命名了我们��

    自定义定义和定理与标准库中的对应物相同

    标准库中找到，无论它们是否重叠。

```
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

```

    标准库的文档可以在

    [`coq.inria.fr/library/`](http://coq.inria.fr/library/).

    使用搜索命令是查找涉及定理的好方法

    特定类型的对象。现在花一分钟来尝试一下。

```

# Identifiers

    First, we need a type for the keys that we use to index into our
    maps.  For this purpose, we again use the type id from the
    Lists chapter.  To make this chapter self contained, we repeat
    its definition here, together with the equality comparison
    function for ids and its fundamental property.

```

归纳 id : Type :=

| Id : string → id。

定义 beq_id x y =

匹配 x,y，

| Id n[1], Id n[2] ⇒ 如果 string_dec n[1] n[2] 则返回 true，否则返回 false。

end.

```

    (The function string_dec comes from Coq's string library.
    If you check its result type, you'll see that it does not actually
    return a bool, but rather a type that looks like {x = y} + {x ≠ y}, called a sumbool, which can be thought of as an
    "evidence-carrying boolean."  Formally, an element of sumbool is
    either a proof that two things are equal or a proof that they are
    unequal, together with a tag indicating which.  But for present
    purposes you can think of it as just a fancy bool.)

```

Theorem beq_id_refl : ∀id, true = beq_id id id。

    Proof.

intros [n]. 简化。 destruct ([string_dec](http://coq.inria.fr/library/Coq.Strings.String.html#string_dec) n n).

- reflexivity.

- destruct n[0]. reflexivity.

    Qed。

```

    The following useful property of beq_id follows from an
    analogous lemma about strings:

```

Theorem beq_id_true_iff : ∀x y : id，

beq_id x y = true ↔ x = y。

    Proof.

intros [n[1]] [n[2]]。

展开 beq_id。

destruct ([string_dec](http://coq.inria.fr/library/Coq.Strings.String.html#string_dec) n[1] n[2])。

- 替换。分割。 reflexivity。 reflexivity。

- 分割。

+ intros contra. 反演 contra。

+ intros H. inversion H. subst. destruct n. reflexivity.

    Qed.

```

    Similarly:

```

Theorem beq_id_false_iff : ∀x y : id，

beq_id x y = false

↔ x ≠ y.

    Proof.

intros x y. 重写 ← beq_id_true_iff。

rewrite [not_true_iff_false](http://coq.inria.fr/library/Coq.Bool.Bool.html#not_true_iff_false). reflexivity. Qed.

```

    This useful variant follows just by rewriting:

```

Theorem false_beq_id : ∀x y : id，

x ≠ y

→ beq_id x y = false。

    Proof。

intros x y. rewrite beq_id_false_iff.

intros H. 应用 H. Qed.

```

# Total Maps

    Our main job in this chapter will be to build a definition of
    partial maps that is similar in behavior to the one we saw in the
    Lists chapter, plus accompanying lemmas about its behavior.

    This time around, though, we're going to use *functions*, rather
    than lists of key-value pairs, to build maps.  The advantage of
    this representation is that it offers a more *extensional* view of
    maps, where two maps that respond to queries in the same way will
    be represented as literally the same thing (the very same function),
    rather than just "equivalent" data structures.  This, in turn,
    simplifies proofs that use maps.

    We build partial maps in two steps.  First, we define a type of
    *total maps* that return a default value when we look up a key
    that is not present in the map.

```

定义 total_map (A:Type) := id → A。

```

    Intuitively, a total map over an element type A is just a
    function that can be used to look up ids, yielding As.

    The function t_empty yields an empty total map, given a default
    element; this map always returns the default element when applied
    to any id.

```

Definition t_empty {A:Type} (v : A) : total_map A :=

(fun _ ⇒ v)。

```

    More interesting is the update function, which (as before) takes
    a map m, a key x, and a value v and returns a new map that
    takes x to v and takes every other key to whatever m does.

```

Definition t_update {A:Type} (m : total_map A)

(x : id) (v : A) =

fun x' ⇒ 如果 beq_id x x' 则返回 v，否则返回 m x'。

```

    This definition is a nice example of higher-order programming:
    t_update takes a *function* m and yields a new function 
    fun x' ⇒ ... that behaves like the desired map.

    For example, we can build a map taking ids to bools, where Id 3 is mapped to true and every other key is mapped to false,
    like this:

```

Definition examplemap :=

t_update (t_update (t_empty false) (Id "foo") false)

(Id "bar") true。

```

    This completes the definition of total maps.  Note that we don't
    need to define a find operation because it is just function
    application!

```

Example update_example1 : examplemap (Id "baz") = false.

    Proof. reflexivity. Qed。

Example update_example2 : examplemap (Id "foo") = false.

    Proof. reflexivity. Qed。

Example update_example3 : examplemap (Id "quux") = false。

    Proof. reflexivity. Qed。

Example update_example4 : examplemap (Id "bar") = true。

    Proof. reflexivity. Qed.

```

    To use maps in later chapters, we'll need several fundamental
    facts about how they behave.  Even if you don't work the following
    exercises, make sure you thoroughly understand the statements of
    the lemmas!  (Some of the proofs require the functional
    extensionality axiom, which is discussed in the Logic
    chapter.) 

#### Exercise: 1 star, optional (t_apply_empty)

    First, the empty map returns its default element for all keys:

```

Lemma t_apply_empty:  ∀A x v, @t_empty A v x = v.

Proof.

(* 在这里填写内容 *) Admitted.

```

    ☐ 

#### Exercise: 2 stars, optional (t_update_eq)

    Next, if we update a map m at a key x with a new value v
    and then look up x in the map resulting from the update, we
    get back v:

```

Lemma t_update_eq : ∀A (m: total_map A) x v，

(t_update m x v) x = v。

Proof。

(* 在这里填写内容 *) Admitted。

```

    ☐ 

#### Exercise: 2 stars, optional (t_update_neq)

    On the other hand, if we update a map m at a key x[1] and then
    look up a *different* key x[2] in the resulting map, we get the
    same result that m would have given:

```

Theorem t_update_neq : ∀(X:Type) v x[1] x[2]

（m : total_map X），

x[1] ≠ x[2] →

(t_update m x[1] v) x[2] = m x[2]。

Proof.

(* 在这里填写内容 *) Admitted.

```

    ☐ 

#### Exercise: 2 stars, optional (t_update_shadow)

    If we update a map m at a key x with a value v[1] and then
    update again with the same key x and another value v[2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second update on m:

```

引理 t_update_shadow：∀A（m：完全映射 A）v[1] v[2] x，

t_update (t_update m x v[1]) x v[2]

= t_update m x v[2]。

证明。

(* 在此填写 *) 已承认。

```

    ☐ 

    For the final two lemmas about total maps, it's convenient to use
    the reflection idioms introduced in chapter IndProp.  We begin
    by proving a fundamental *reflection lemma* relating the equality
    proposition on ids with the boolean function beq_id. 

#### Exercise: 2 stars, optional (beq_idP)

    Use the proof of beq_natP in chapter IndProp as a template to
    prove the following:

```

引理 beq_idP：∀x y，reflect (x = y) (beq_id x y)。

证明。

(* 在此填写 *) 已承认。

```

    ☐ 

    Now, given ids x[1] and x[2], we can use the destruct (beq_idP x[1] x[2]) to simultaneously perform case analysis on the result of
    beq_id x[1] x[2] and generate hypotheses about the equality (in the
    sense of =) of x[1] and x[2]. 

#### Exercise: 2 stars (t_update_same)

    With the example in chapter IndProp as a template, use
    beq_idP to prove the following theorem, which states that if we
    update a map to assign key x the same value as it already has in
    m, then the result is equal to m:

```

定理 t_update_same：∀X x（m：完全映射 X），

t_update m x (m x) = m.

证明。

(* 在此填写 *) 已承认。

```

    ☐ 

#### Exercise: 3 stars, recommended (t_update_permute)

    Use beq_idP to prove one final property of the update
    function: If we update a map m at two distinct keys, it doesn't
    matter in which order we do the updates.

```

定理 t_update_permute：∀（X：类型）v[1] v[2] x[1] x[2]

（m：完全映射 X），

x[2] ≠ x[1] →

（t_update (t_update m x[2] v[2]) x[1] v[1])

=（t_update (t_update m x[1] v[1]) x[2] v[2]）。

证明。

(* 在此填写 *) 已承认。

```

    ☐

```

# 部分映射

    最后，我们定义了*部分映射*在完全映射之上。

    具有类型 A 元素的映射简单地是具有元素的完全映射。

    具有选项 A 类型和默认元素 None 的类型。

```
Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A)
                  (x : id) (v : A) :=
  t_update m x (Some v).

```

    现在我们直接推广所有关于完全映射的基本引理

    映射到部分映射。

```
Lemma apply_empty : ∀A x, @empty A x = None.

    Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
    Qed.

Lemma update_eq : ∀A (m: partial_map A) x v,
  (update m x v) x = Some v.

    Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
    Qed.

Theorem update_neq : ∀(X:Type) v x[1] x[2]
                       (m : partial_map X),
  x[2] ≠ x[1] →
  (update m x[2] v) x[1] = m x[1].

    Proof.
  intros X v x[1] x[2] m H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : ∀A (m: partial_map A) v[1] v[2] x,
  update (update m x v[1]) x v[2] = update m x v[2].

    Proof.
  intros A m v[1] v[2] x[1]. unfold update. rewrite t_update_shadow.
  reflexivity.
    Qed.

Theorem update_same : ∀X v x (m : partial_map X),
  m x = Some v →
  update m x v = m.

    Proof.
  intros X v x m H. unfold update. rewrite ← H.
  apply t_update_same.
    Qed.

Theorem update_permute : ∀(X:Type) v[1] v[2] x[1] x[2]
                                (m : partial_map X),
  x[2] ≠ x[1] →
    (update (update m x[2] v[2]) x[1] v[1])
  = (update (update m x[1] v[1]) x[2] v[2]).

    Proof.
  intros X v[1] v[2] x[1] x[2] m. unfold update.
  apply t_update_permute.
    Qed.

```

```

```

```

```
