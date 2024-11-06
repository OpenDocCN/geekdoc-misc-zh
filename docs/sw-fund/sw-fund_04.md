# 处理结构化数据列表

```

```

需要导出 Induction。

模块 NatList。

```

# Pairs of Numbers

    In an Inductive type definition, each constructor can take
    any number of arguments — none (as with true and O), one (as
    with S), or more than one, as here:

```

归纳 natprod : 类型 :=

| pair : nat → nat → natprod.

```

    This declaration can be read: "There is just one way to
    construct a pair of numbers: by applying the constructor pair to
    two arguments of type nat."

```

检查 (pair 3 5).

```

    Here are two simple functions for extracting the first and
    second components of a pair.  The definitions also illustrate how
    to do pattern matching on two-argument constructors.

```

定义 fst (p : natprod) : nat :=

匹配 p 与

| pair x y ⇒ x

结束。

定义 snd (p : natprod) : nat :=

匹配 p 与

| pair x y ⇒ y

结束。

计算 (fst (pair 3 5)).

(* ===> 3 *)

```

    Since pairs are used quite a bit, it is nice to be able to
    write them with the standard mathematical notation (x,y) instead
    of pair x y.  We can tell Coq to allow this with a Notation
    declaration.

```

符号 "( x , y )" := (pair x y).

```

    The new pair notation can be used both in expressions and in
    pattern matches (indeed, we've actually seen this already in the
    previous chapter, in the definition of the minus function —
    this works because the pair notation is also provided as part of
    the standard library):

```

计算 (fst (3,5)).

定义 fst' (p : natprod) : nat :=

匹配 p 与

| (x,y) ⇒ x

结束。

定义 snd' (p : natprod) : nat :=

匹配 p 与

| (x,y) ⇒ y

结束。

定义 swap_pair (p : natprod) : natprod :=

匹配 p 与

| (x,y) ⇒ (y,x)

结束。

```

    Let's try to prove a few simple facts about pairs.

    If we state things in a particular (and slightly peculiar) way, we
    can complete proofs with just reflexivity (and its built-in
    simplification):

```

定理 surjective_pairing' : ∀(n m : nat),

(n,m) = (fst (n,m), snd (n,m)).

证明。

反射性。结束。

```

    But reflexivity is not enough if we state the lemma in a more
    natural way:

```

定理 surjective_pairing_stuck : ∀(p : natprod),

p = (fst p, snd p).

证明。

简化。(* 不会减少任何东西！*)

放弃。

```

    We have to expose the structure of p so that simpl can
    perform the pattern match in fst and snd.  We can do this with
    destruct.

```

定理 surjective_pairing : ∀(p : natprod),

p = (fst p, snd p).

证明。

intros p. destruct p as [n m]. 简化。反射性。结束。

```

    Notice that, unlike its behavior with nats, destruct
    generates just one subgoal here.  That's because natprods can
    only be constructed in one way. 

#### Exercise: 1 star (snd_fst_is_swap)

```

定理 snd_fst_is_swap : ∀(p : natprod),

(snd p, fst p) = swap_pair p.

证明。

(* 在这里填写 *) 放弃。

```

    ☐ 

#### Exercise: 1 star, optional (fst_swap_is_snd)

```

定理 fst_swap_is_snd : ∀(p : natprod),

fst (swap_pair p) = snd p.

证明。

(* 在这里填写 *) 放弃。

```

    ☐

```

# 数字列表

    推广对的定义，我们可以描述

    类型为*数字*列表的形式： "列表要么为空

    列表或者一个数字和另一个列表的对。"

```
Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat → natlist → natlist.

```

    例如，这是一个三元素列表：

```
Definition mylist := cons 1 (cons 2 (cons 3 nil)).

```

    与对偶一样，更方便地写列表

    熟悉的编程符号。以下声明

    允许我们使用 :: 作为中缀 cons 运算符和方括号

    方括号作为构造列表的“外部”符号。

```
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

```

    不需要理解这些细节

    声明，但如果您感兴趣，这是大致

    发生了什么。右结合性注释告诉 Coq

    如何括号化涉及多次使用 :: 的表达式

    例如，接下来的三个声明确切地意味着

    同样的事情：

```
Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

```

    at level 60 部分告诉 Coq 如何括号化

    涉及 :: 和其他中缀运算符的表达式。

    例如，由于我们将 + 定义为加法的中缀符号

    函数级别为 50，

```
  Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

    the + operator will bind tighter than ::, so 1 + 2 :: [3]
   will be parsed, as we'd expect, as (1 + 2) :: [3] rather than 1 + (2 :: [3]).

    (Expressions like "1 + 2 :: [3]" can be a little confusing when
   you read them in a .v file.  The inner brackets, around 3, indicate
   a list, but the outer brackets, which are invisible in the HTML
   rendering, are there to instruct the "coqdoc" tool that the bracketed
   part should be displayed as Coq code rather than running text.)

    The second and third Notation declarations above introduce the
   standard square-bracket notation for lists; the right-hand side of
   the third one illustrates Coq's syntax for declaring n-ary
   notations and translating them to nested sequences of binary
   constructors. 

### Repeat

    A number of functions are useful for manipulating lists.
    For example, the repeat function takes a number n and a
    count and returns a list of length count where every element
    is n.

```

递归重复 (n count : nat) : natlist :=

匹配 count 与

| O ⇒ nil

| S count' ⇒ n :: (repeat n count')

结束。

```

### Length

    The length function calculates the length of a list.

```

递归长度 (l:natlist) : nat :=

匹配 l 与

| nil ⇒ O

| h :: t ⇒ S (length t)

结束。

```

### Append

    The app function concatenates (appends) two lists.

```

递归 app (l[1] l[2] : natlist) : natlist :=

匹配 l[1] 与

| nil    ⇒ l[2]

| h :: t ⇒ h :: (app t l[2])

结束。

```

    Actually, app will be used a lot in some parts of what
    follows, so it is convenient to have an infix operator for it.

```

符号 "x ++ y" := (app x y)

(右结合性，级别为 60)。

例如测试 _app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].

证明。反射性。结束。

例如测试 _app2:             nil ++ [4;5] = [4;5].

证明。反射性。结束。

例如测试 _app3:             [1;2;3] ++ nil = [1;2;3].

证明。反射性。结束。

```

### Head (with default) and Tail

    Here are two smaller examples of programming with lists.
    The hd function returns the first element (the "head") of the
    list, while tl returns everything but the first
    element (the "tail").
    Of course, the empty list has no first element, so we
    must pass a default value to be returned in that case.

```

定义 hd (default:nat) (l:natlist) : nat :=

匹配 l 与

| nil ⇒ default

| h :: t ⇒ h

结束。

定义 tl (l:natlist) : natlist :=

匹配 l 与

| nil ⇒ nil

| h :: t ⇒ t

结束。

示例 test_hd[1]:             hd 0 [1;2;3] = 1。

证明。反射性。完成。

示例 test_hd[2]:             hd 0 [] = 0。

证明。反射性。完成。

示例 test_tl:              tl [1;2;3] = [2;3]。

证明。反射性。完成。

```

### Exercises

#### Exercise: 2 stars, recommended (list_funs)

    Complete the definitions of nonzeros, oddmembers and
    countoddmembers below. Have a look at the tests to understand
    what these functions should do.

```

Fixpoint nonzeros (l:natlist) : natlist

(* 用你的定义替换这一行 *). 已承认。

示例 test_nonzeros:

nonzeros [0;1;0;2;3;0;0] = [1;2;3]。

(* 在这里填写 *) 已承认。

Fixpoint oddmembers (l:natlist) : natlist

(* 用你的定义替换这一行 *). 已承认。

示例 test_oddmembers:

oddmembers [0;1;0;2;3;0;0] = [1;3].

(* 在这里填写 *) 已承认。

定义 countoddmembers (l:natlist) : nat

(* 用你的定义替换这一行 *). 已承认。

示例 test_countoddmembers1:

countoddmembers [1;0;3;1;4;5] = 4。

(* 在这里填写 *) 已承认。

示例 test_countoddmembers2:

countoddmembers [0;2;4] = 0。

(* 在这里填写 *) 已承认。

示例 test_countoddmembers3:

countoddmembers nil = 0。

(* 在这里填写 *) 已承认。

```

    ☐ 

#### Exercise: 3 stars, advanced (alternate)

    Complete the definition of alternate, which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.

    Note: one natural and elegant way of writing alternate will fail
    to satisfy Coq's requirement that all Fixpoint definitions be
    "obviously terminating."  If you find yourself in this rut, look
    for a slightly more verbose solution that considers elements of
    both lists at the same time.  (One possible solution requires
    defining a new kind of pairs, but this is not the only way.)

```

Fixpoint alternate (l[1] l[2] : natlist) : natlist

(* 用你的定义替换这一行 *). 已承认。

示例 test_alternate1:

alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6]。

(* 在这里填写 *) 已承认。

示例 test_alternate2:

alternate [1] [4;5;6] = [1;4;5;6]。

(* 在这里填写 *) 已承认。

示例 test_alternate3:

alternate [1;2;3] [4] = [1;4;2;3]。

(* 在这里填写 *) 已承认。

示例 test_alternate4:

alternate [] [20;30] = [20;30]。

(* 在这里填写 *) 已承认。

```

    ☐

```

### 通过列表实现袋子

    一个袋子（或多重集）类似于一个集合，只是每个元素

    可以出现多次而不仅仅一次。一个可能的

    实现是将一个数字袋表示为一个列表。

```
Definition bag := natlist.

```

#### 练习：3 星，推荐（bag_functions）

    完成以下函数的定义

    计数，求和，添加和成员对于袋子。

```
Fixpoint count (v:nat) (s:bag) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

```

    所有这些证明都可以通过反射性完成。

```
Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 (* FILL IN HERE *) Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
 (* FILL IN HERE *) Admitted.

```

    多重集和类似于集合并：sum a b 包含

    a 和 b 的所有元素。（数学家通常

    在多重集上定义联合有点不同，这

    这就是为什么我们不使用该名称来表示此操作的原因。）

    对于 sum，我们给出了一个不提供明确的标题

    参数的名称。此外，它使用了关键字

    定义而不是 Fixpoint，所以即使你有名字

    参数，你将无法递归处理它们。

    以这种方式陈述问题的重点是鼓励你

    思考一下是否可以用另一种方式实现 sum —

    也许通过使用已经定义的函数。

```
Definition sum : bag → bag → bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.

Definition add (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.

Definition member (v:nat) (s:bag) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_member1:             member 1 [1;4;1] = true.
 (* FILL IN HERE *) Admitted.

Example test_member2:             member 2 [1;4;1] = false.
 (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星，可选（bag_more_functions）

    这里有一些更多的袋子函数让你练习。

    当 remove_one 应用于一个没有��移除的数字的袋子时，

它应该返回相同的袋子不变。

```
Fixpoint remove_one (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  (* FILL IN HERE *) Admitted.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  (* FILL IN HERE *) Admitted.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  (* FILL IN HERE *) Admitted.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  (* FILL IN HERE *) Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* FILL IN HERE *) Admitted.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* FILL IN HERE *) Admitted.

Fixpoint subset (s[1]:bag) (s[2]:bag) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
 (* FILL IN HERE *) Admitted.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
 (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星，推荐 M（bag_theorem）

    写下一个关于袋子的有趣定理

    涉及计数和添加函数，并加以证明。注意

    由于这个问题有点开放，所以可能

    你可能会得出一个真实的定理，但其证明

    需要你尚未学会的技巧。随时可以寻求帮助！

    如果你卡住了，寻求帮助！

```
(* Theorem bag_theorem : ... Proof.   ... Qed. *)

```

    ☐

```

# Reasoning About Lists

    As with numbers, simple facts about list-processing
    functions can sometimes be proved entirely by simplification.  For
    example, the simplification performed by reflexivity is enough
    for this theorem...

```

定理 nil_app : ∀l:natlist,

[] ++ l = l.

Proof. reflexivity. Qed.

```

    ... because the [] is substituted into the
    "scrutinee" (the value being "scrutinized" by the match) in the
    definition of app, allowing the match itself to be
    simplified. 

    Also, as with numbers, it is sometimes helpful to perform case
    analysis on the possible shapes (empty or non-empty) of an unknown
    list.

```

定理 tl_length_pred : ∀l:natlist,

pred (length l) = length (tl l).

Proof.

对 l 进行析取 as [| n l']。

- (* l = nil *)

reflexivity.

- (* l = cons n l' *)

reflexivity. Qed.

```

    Here, the nil case works because we've chosen to define
    tl nil = nil. Notice that the as annotation on the destruct
    tactic here introduces two names, n and l', corresponding to
    the fact that the cons constructor for lists takes two
    arguments (the head and tail of the list it is constructing). 

    Usually, though, interesting theorems about lists require
    induction for their proofs.

```

### 微讲道

    仅仅阅读例子证明脚本是不会让你走得太远的！

    重要的是要详细处理每一个细节，使用 Coq

    并思考每个步骤达到的目的。否则，它更

    或许可以肯定的是，当你

    获得它们。就这样。

```

## Induction on Lists

    Proofs by induction over datatypes like natlist are a
    little less familiar than standard natural number induction, but
    the idea is equally simple.  Each Inductive declaration defines
    a set of data values that can be built up using the declared
    constructors: a boolean can be either true or false; a number
    can be either O or S applied to another number; a list can be
    either nil or cons applied to a number and a list.

    Moreover, applications of the declared constructors to one another
    are the *only* possible shapes that elements of an inductively
    defined set can have, and this fact directly gives rise to a way
    of reasoning about inductively defined sets: a number is either
    O or else it is S applied to some *smaller* number; a list is
    either nil or else it is cons applied to some number and some
    *smaller* list; etc. So, if we have in mind some proposition P
    that mentions a list l and we want to argue that P holds for
    *all* lists, we can reason as follows:

*   First, show that P is true of l when l is nil. 

*   Then show that P is true of l when l is cons n l' for some number n and some smaller list l', assuming that P is true for l'.

    Since larger lists can only be built up from smaller ones,
    eventually reaching nil, these two arguments together establish
    the truth of P for all lists l.  Here's a concrete example:

```

定理 app_assoc : ∀l[1] l[2] l[3] : natlist,

(l[1] ++ l[2]) ++ l[3] = l[1] ++ (l[2] ++ l[3]).

Proof.

对 l[1] l[2] l[3] 进行析取。对 l[1] 进行归纳 as [| n l[1]' IHl1']。

- (* l[1] = nil *)

reflexivity.

- (* l[1] = cons n l[1]' *)

简化。rewrite → IHl1'。reflexivity. Qed.

```

    Notice that, as when doing induction on natural numbers, the
    as... clause provided to the induction tactic gives a name to
    the induction hypothesis corresponding to the smaller list l[1]'
    in the cons case. Once again, this Coq proof is not especially
    illuminating as a static written document — it is easy to see
    what's going on if you are reading the proof in an interactive Coq
    session and you can see the current goal and context at each
    point, but this state is not visible in the written-down parts of
    the Coq proof.  So a natural-language proof — one written for
    human readers — will need to include more explicit signposts; in
    particular, it will help the reader stay oriented if we remind
    them exactly what the induction hypothesis is in the second
    case. 

    For comparison, here is an informal proof of the same theorem. 

    *Theorem*: For all lists l[1], l[2], and l[3],
   (l[1] ++ l[2]) ++ l[3] = l[1] ++ (l[2] ++ l[3]).

    *Proof*: By induction on l[1].

*   First, suppose l[1] = []. We must show 

    ```

    ([] ++ l[2]) ++ l[3] = [] ++ (l[2] ++ l[3]),

    这直接来源于++的定义。

    ```

*   Next, suppose l[1] = n::l[1]', with 

    ```

    (l[1]' ++ l[2]) ++ l[3] = l[1]' ++ (l[2] ++ l[3])

    （归纳假设）。我们必须证明

    ```
      ((n :: l[1]') ++ l[2]) ++ l[3] = (n :: l[1]') ++ (l[2] ++ l[3]).

     By the definition of ++, this follows from 

    ```

    n :: ((l[1]' ++ l[2]) ++ l[3]) = n :: (l[1]' ++ (l[2] ++ l[3])),

    这是立即从归纳假设得到的。 ☐

    ```

    ```

    ```

### Reversing a List

    For a slightly more involved example of inductive proof over
    lists, suppose we use app to define a list-reversing function
    rev:

```

定义 rev (l:natlist) : natlist :=

匹配 l，有

| nil    ⇒ nil

| h :: t ⇒ rev t ++ [h]

end.

示例 test_rev1:            rev [1;2;3] = [3;2;1].

Proof. reflexivity. Qed.

示例 test_rev2:            rev nil = nil.

Proof. reflexivity. Qed.

```

### Properties of rev

    Now let's prove some theorems about our newly defined rev.
    For something a bit more challenging than what we've seen, let's
    prove that reversing a list does not change its length.  Our first
    attempt gets stuck in the successor case...

```

定理 rev_length_firsttry : ∀l : natlist,

length (rev l) = length l.

Proof.

对 l 进行归纳 as [| n l' IHl']。

- (* l =  *)

reflexivity.

- (* l = n :: l' *)

(* 这是棘手的情况。 让我们像往常一样开始简化。*)

简化。

(* 现在我们似乎卡住了：目标是一个涉及 ++ 的等式，但是我们在当前上下文或全局环境中没有任何有用的等式！我们可以通过使用归纳假设来重写目标，稍微取得一点进展...*)

rewrite ← IHl'.

(* ... 但是我们无法再继续下去了。 *)

放弃。

```

    So let's take the equation relating ++ and length that
    would have enabled us to make progress and prove it as a separate
    lemma.

```

定理 app_length : ∀l[1] l[2] : natlist,

length (l[1] ++ l[2]) = (length l[1]) + (length l[2]).

Proof.

(* 课上的工作 *)

对 l[1] l[2] 进行归纳。对 l[1] 进行归纳 as [| n l[1]' IHl1']。

- (* l[1] = nil *)

reflexivity.

- (* l[1] = cons *)

简化。rewrite → IHl1'。reflexivity. Qed.

```

    Note that, to make the lemma as general as possible, we
    quantify over *all* natlists, not just those that result from an
    application of rev.  This should seem natural, because the truth
    of the goal clearly doesn't depend on the list having been
    reversed.  Moreover, it is easier to prove the more general
    property. 

    Now we can complete the original proof.

```

定理 rev_length : ∀l : natlist,

length (rev l) = length l.

Proof.

对 l 进行归纳 as [| n l' IHl']。

- (* l = nil *)

reflexivity.

- (* l = cons *)

简化。rewrite → app_length, plus_comm。

简化。rewrite → IHl'。reflexivity. Qed.

```

    For comparison, here are informal proofs of these two theorems:

    *Theorem*: For all lists l[1] and l[2],
       length (l[1] ++ l[2]) = length l[1] + length l[2].

    *Proof*: By induction on l[1].

*   First, suppose l[1] = []. We must show 

    ```

    length ([] ++ l[2]) = length [] + length l[2],

    这直接来源于 length 和 ++ 的定义。

    ```

*   Next, suppose l[1] = n::l[1]', with 

    ```

    length (l[1]' ++ l[2]) = length l[1]' + length l[2].

    我们必须证明

    ```
      length ((n::l[1]') ++ l[2]) = length (n::l[1]') + length l[2]).

     This follows directly from the definitions of length and ++ together with the induction hypothesis. ☐
    ```

    ```

    *Theorem*: For all lists l, length (rev l) = length l.

    *Proof*: By induction on l.

*   First, suppose l = []. We must show 

    ```

    length (rev []) = length [],

    这直接来源于 length 和 rev 的定义。

    ```

*   Next, suppose l = n::l', with 

    ```

    length (rev l') = length l'.

    我们必须证明

    ```
      length (rev (n :: l')) = length (n :: l').

     By the definition of rev, this follows from 

    ```

    length ((rev l') ++ [n]) = S (length l')

    这样，根据前面的引理，是一样的

    ```
      length (rev l') + length [n] = S (length l').

     This follows directly from the induction hypothesis and the definition of length. ☐
    ```

    ```

    ```

    ```

    The style of these proofs is rather longwinded and pedantic.
    After the first few, we might find it easier to follow proofs that
    give fewer details (which can easily work out in our own minds or
    on scratch paper if necessary) and just highlight the non-obvious
    steps.  In this more compressed style, the above proof might look
    like this: 

    *Theorem*:
     For all lists l, length (rev l) = length l.

    *Proof*: First, observe that length (l ++ [n]) = S (length l)
     for any l (this follows by a straightforward induction on l).
     The main property again follows by induction on l, using the
     observation together with the induction hypothesis in the case
     where l = n'::l'. ☐ 

    Which style is preferable in a given situation depends on
    the sophistication of the expected audience and how similar the
    proof at hand is to ones that the audience will already be
    familiar with.  The more pedantic style is a good default for our
    present purposes.

```

## 搜索

    我们已经看到证明可以利用我们已经

    已经证明，例如，使用 rewrite。但是为了引用

    定理，我们需要知道它的名称！实际上，甚至很难

    要记住已经证明了哪些定理，更不用说它们

    被称为。

    Coq 的 Search 命令在这方面非常有帮助。输入

    搜索 foo 将导致 Coq 显示所有定理的列表

    涉及 foo。例如，尝试取消注释以下行

    要查看我们已经证明的关于 rev 的定理列表：

```
(*  Search rev. *)

```

    在做以下练习时请记住搜索

    在本书的其余部分中；它可以节省您很多时间！

    如果你正在使用 ProofGeneral，你可以用 C-c C-a C-a 运行搜索。将其响应粘贴到您的缓冲区中可能会

    用 C-c C-;完成。

```

## List Exercises, Part 1

#### Exercise: 3 starsM (list_exercises)

    More practice with lists:

```

定理 app_nil_r：∀l：natlist，

l ++ [] = l。

证明。

(* 在这里填写*) 已承认。

定理 rev_app_distr：∀l[1] l[2]：natlist，

rev（l[1] ++ l[2]）= rev l[2] ++ rev l[1]。

证明。

(* 在这里填写*) 已承认。

定理 rev_involutive：∀l：natlist，

rev（rev l）= l。

证明。

(* 在这里填写*) 已承认。

```

    There is a short solution to the next one.  If you find yourself
    getting tangled up, step back and try to look for a simpler
    way.

```

定理 app_assoc4：∀l[1] l[2] l[3] l[4]：natlist，

l[1] ++（l[2] ++（l[3] ++ l[4]））=（（l[1] ++ l[2]）++ l[3]）++ l[4]。

证明。

(* 在这里填写*) 已承认。

```

    An exercise about your implementation of nonzeros:

```

引理 nonzeros_app：∀l[1] l[2]：natlist，

非零（l[1] ++ l[2]）=（nonzeros l[1]）++（nonzeros l[2]）。

证明。

(* 在这里填写*) 已承认。

```

    ☐ 

#### Exercise: 2 stars (beq_natlist)

    Fill in the definition of beq_natlist, which compares
    lists of numbers for equality.  Prove that beq_natlist l l
    yields true for every list l.

```

Fixpoint beq_natlist（l[1] l[2]：natlist）：bool

(* 用":= _your_definition_ ." 替换此行*）。已承认。

示例 test_beq_natlist1：

（beq_natlist nil nil = true）。

(* 在这里填写*) 已承认。

示例 test_beq_natlist2：

beq_natlist [1;2;3] [1;2;3] = true。

(* 在这里填写*) 已承认。

示例 test_beq_natlist3：

beq_natlist [1;2;3] [1;2;4] = false。

(* 在这里填写*) 已承认。

定理 beq_natlist_refl：∀l：natlist，

true = beq_natlist l l。

证明。

(* 在这里填写*) 已承认。

```

    ☐

```

## 列表练习，第 2 部分

#### 练习：3 星，高级（bag_proofs）

    这里有几个关于你的小定理要证明

    上面关于 bags 的定义。

```
Theorem count_member_nonzero : ∀(s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

```

    下面关于 leb 的引理可能会在下一个证明中帮助你。

```
Theorem ble_n_Sn : ∀n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_decreases_count: ∀(s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星，可选 M（bag_count_sum）

    写下一个有趣的关于 bags 的定理 bag_count_sum

    涉及函数 count 和 sum，并证明它。（您可以

    发现证明的难度取决于你如何定义

    计数！

```
(* FILL IN HERE *)

```

    ☐

#### 练习：4 星，高级 M（rev_injective）

    证明 rev 函数是单射的-也就是说，

```
    ∀(l[1] l[2] : natlist), rev l[1] = rev l[2] → l[1] = l[2].

    (There is a hard way and an easy way to do this.)

```

(* 在这里填写*)

```

    ☐

```

# 选项

    假设我们想要编写��个返回第 n 个的函数

    一些列表的元素。如果我们给它类型 nat → natlist → nat，

    然后我们将不得不选择一个数字返回，当列表是

    太短了...

```
Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil ⇒ 42  (* arbitrary! *)
  | a :: l' ⇒ match beq_nat n O with
               | true ⇒ a
               | false ⇒ nth_bad l' (pred n)
               end
  end.

```

    这个解决方案不太好：如果 nth_bad 返回 42，我们

    无法确定该值是否实际出现在输入中

    无需进一步处理。更好的选择是更改

    返回 nth_bad 的类型包括一个错误值作为可能的

    结果。我们称这种类型为 natoption。

```
Inductive natoption : Type :=
  | Some : nat → natoption
  | None : natoption.

```

    然后我们可以改变 nth_bad 的上述定义为

    当列表太短时返回 None，并在

    列表有足够的成员，并且 a 出现在位置 n。我们叫

    这个新函数 nth_error 来指示它可能会导致一个

    错误。

```
Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil ⇒ None
  | a :: l' ⇒ match beq_nat n O with
               | true ⇒ Some a
               | false ⇒ nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.

    Proof. reflexivity. Qed.

Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.

    Proof. reflexivity. Qed.

Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.

    Proof. reflexivity. Qed.

```

    （在 HTML 版本中，这些的样板证明

    示例已省略。如果要查看，请单击框。）

    这个例子也是介绍另一个小的机会

    Coq 的编程语言的特征：条件

    表达式…

```
Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil ⇒ None
  | a :: l' ⇒ if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end.

```

    Coq 的条件语句与其他任何地方找到的条件语句完全相同

    语言，具有一个小的概括。由于布尔类型

    不是内置的，Coq 实际上支持条件表达式

    *任何*归纳定义类型，有两个构造函数。这个

    如果 guard 求值为第一个构造函数，则被视为 true。

    在归纳定义中，如果求值为 false，则返回

    第二。

    下面的函数从 natoption 中提取 nat，返回

    在 None 情况下提供默认值。

```
Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' ⇒ n'
  | None ⇒ d
  end.

```

#### 练习：2 星（hd_error）

    使用相同的思想，修复早期的 hd 函数，以便我们不会

    必须为 nil 情况传递一个默认元素。

```
Definition hd_error (l : natlist) : natoption
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_hd_error1 : hd_error [] = None.
 (* FILL IN HERE *) Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
 (* FILL IN HERE *) Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
 (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：1 星，可选（option_elim_hd）

    这个练习将您的新 hd_error 与旧 hd 相关联。

```
Theorem option_elim_hd : ∀(l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```
End NatList.

```

# 部分映射

    作为数据结构可以在最后一个示例中如何定义的最后一个示例

    Coq，这是一个简单的 *部分映射* 数据类型，类似于

    在大多数编程中找到的映射或字典数据结构

    语言。

    首先，我们定义一个新的归纳数据类型 id 来充当

    我们的部分映射的“键”。

```
Inductive id : Type :=
  | Id : nat → id.

```

    内部，id 只是一个数字。引入一个单独的类型

    通过用标签 Id 包装每个 nat 来使定义更加

    可读性，并为我们提供更改表示的灵活性

    以后如果我们希望的话。

    我们还需要一个 id 的相等性测试：

```
Definition beq_id (x[1] x[2] : id) :=
  match x[1], x[2] with
  | Id n[1], Id n[2] ⇒ beq_nat n[1] n[2]
  end.

```

#### 练习：1 星（beq_id_refl）

```
Theorem beq_id_refl : ∀x, true = beq_id x x.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    现在我们定义部分映射的类型：

```
Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id → nat → partial_map → partial_map.

```

    这个声明可以这样读：“构造

    partial_map：使用构造函数 empty 表示一个

    空部分映射，或通过将构造函数记录应用于

    一个键，一个值和一个现有的 partial_map 来构造一个

    带有附加键值映射的 partial_map。”

    更新函数覆盖了给定键的条目

    部分映射（如果给定键尚未存在，则添加新条目

    存在）。

```
Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

```

    最后，find 函数在 partial_map 中搜索给定的

    键。如果找不到键，则返回 None，如果找到则返回 Some val

    键与 val 关联。如果同一个键映射到

    多个值，find 将返回第一个找到的值

    遇到。

```
Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         ⇒ None
  | record y v d' ⇒ if beq_id x y
                     then Some v
                     else find x d'
  end.

```

#### 练习：1 星（update_eq）

```
Theorem update_eq :
  ∀(d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
 (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：1 星（update_neq）

```
Theorem update_neq :
  ∀(d : partial_map) (x y : id) (o: nat),
    beq_id x y = false → find x (update d y o) = find x d.
Proof.
 (* FILL IN HERE *) Admitted.

```

    ☐

```
End PartialMap.

```

#### 练习：2 星 M（baz_num_elts）

    考虑以下归纳定义：

```
Inductive baz : Type :=
  | Baz1 : baz → baz
  | Baz2 : baz → bool → baz.

```

    类型 baz 有多少个元素？（英文回答

    或您选择的自然语言。）

    （在这里填充）

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
