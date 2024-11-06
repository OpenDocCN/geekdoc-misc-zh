# 程序等价

```

```

(* 导入 *)

导入 Coq.Bool.Bool。

导入 Coq.Arith.Arith。

导入 Coq.Arith.EqNat。

导入 Coq.omega.Omega。

导入 Coq.Lists.List。

导入 Coq.Logic.FunctionalExtensionality。

导入 ListNotations。

导入映射。

导入 Imp。

(* /导入 *)

```

### Some Advice for Working on Exercises:

*   Most of the Coq proofs we ask you to do are similar to proofs that we've provided. Before starting to work on exercises problems, take the time to work through our proofs (both informally, on paper, and in Coq) and make sure you understand them in detail. This will save you a lot of time. 

*   The Coq proofs we're doing now are sufficiently complicated that it is more or less impossible to complete them simply by random experimentation or "following your nose." You need to start with an idea about why the property is true and how the proof is going to go. The best way to do this is to write out at least a sketch of an informal proof on paper — one that intuitively convinces you of the truth of the theorem — before starting to work on the formal one. Alternately, grab a friend and try to convince them that the theorem is true; then try to formalize your explanation. 

*   Use automation to save work! The proofs in this chapter's exercises can get pretty long if you try to write out all the cases explicitly.

```

# 行为等价

    在早期章节中，我们调查了一个非常

    简单的程序转换：optimize_0plus 函数。该

    我们考虑的编程语言是第一个版本

    算术表达式的语言 - 没有变量 - 因此

    在那种情况下，定义程序转换的正确性非常容易

    程序转换正确：它应该始终产生一个

    评估为与原始数字相同的程序。

    谈论程序转换的正确性

    完整的 Imp 语言，包括赋值和其他命令，我们

    需要考虑变量和状态的作用。

```

## Definitions

    For aexps and bexps with variables, the definition we want is
    clear.  We say that two aexps or bexps are *behaviorally equivalent* if they evaluate to the same result in every state.

```

定义 aequiv (a[1] a[2] : aexp) : 命题 =

∀(st:状态),

aeval st a[1] = aeval st a[2]。

定义 bequiv (b[1] b[2] : bexp) : 命题 =

∀(st:状态),

在 st 中 beval b[1] = beval b[2]。

```

    Here are some simple examples of equivalences of arithmetic
    and boolean expressions.

```

定理 aequiv_example:

aequiv (AMinus (AId X) (AId X)) (ANum 0).

    证明。

intros st。简化。omega。

    已承认。

定理 bequiv_example:

bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue。

    证明。

intros st。展开 beval。

重写 aequiv_example。一致性。

    已承认。

```

    For commands, the situation is a little more subtle.  We can't
    simply say "two commands are behaviorally equivalent if they
    evaluate to the same ending state whenever they are started in the
    same initial state," because some commands, when run in some
    starting states, don't terminate in any final state at all!  What
    we need instead is this: two commands are behaviorally equivalent
    if, for any given starting state, they either (1) both diverge
    or (2) both terminate in the same final state.  A compact way to
    express this is "if the first one terminates in a particular state
    then so does the second, and vice versa."

```

定义 cequiv (c[1] c[2] : com) : 命题 =

∀(st st' : 状态),

(c[1] / st ⇓ st') ↔ (c[2] / st ⇓ st')。

```

## Simple Examples

    For examples of command equivalence, let's start by looking at
    some trivial program transformations involving SKIP:

```

定理 skip_left: ∀c,

cequiv

(跳过;; c)

c。

证明。

(* 在课堂上运行 *)

intros c st st'.

分割; intros H。

- (* -> *)

反转 H。替换。

反转 H[2]。替换。

假设。

- (* <- *)

应用 E_Seq with st。

应用 E_Skip。

假设。

已承认。

```

#### Exercise: 2 stars (skip_right)

    Prove that adding a SKIP after a command results in an
    equivalent program

```

定理 skip_right: ∀c,

cequiv

(c ;; 跳过)

c。

证明。

(* 在这里填写 *) 已承认。

```

    ☐ 

    Similarly, here is a simple transformation that optimizes IFB
    commands:

```

定理 IFB_true_simple: ∀c[1] c[2],

cequiv

(IFB BTrue THEN c[1] ELSE c[2] FI)

c[1].

    证明。

intros c[1] c[2]。

分割; intros H。

- (* -> *)

反�� H; 替换。假设。反转 H[5]。

- (* <- *)

应用 E_IfTrue。一致性。假设。已证明。

```

    Of course, few programmers would be tempted to write a conditional
    whose guard is literally BTrue.  A more interesting case is when
    the guard is *equivalent* to true:  *Theorem*: If b is equivalent to BTrue, then IFB b THEN c[1] ELSE c[2] FI is equivalent to c[1]. 

    *Proof*:

*   (→) We must show, for all st and st', that if IFB b THEN c[1] ELSE c[2] FI / st ⇓ st' then c[1] / st ⇓ st'. 

     Proceed by cases on the rules that could possibly have been used to show IFB b THEN c[1] ELSE c[2] FI / st ⇓ st', namely E_IfTrue and E_IfFalse. 

    *   Suppose the final rule rule in the derivation of IFB b THEN c[1] ELSE c[2] FI / st ⇓ st' was E_IfTrue. We then have, by the premises of E_IfTrue, that c[1] / st ⇓ st'. This is exactly what we set out to prove. 

    *   On the other hand, suppose the final rule in the derivation of IFB b THEN c[1] ELSE c[2] FI / st ⇓ st' was E_IfFalse. We then know that beval st b = false and c[2] / st ⇓ st'. 

         Recall that b is equivalent to BTrue, i.e., forall st, beval st b = beval st BTrue. In particular, this means that beval st b = true, since beval st BTrue = true. But this is a contradiction, since E_IfFalse requires that beval st b = false. Thus, the final rule could not have been E_IfFalse. 

*   (←) We must show, for all st and st', that if c[1] / st ⇓ st' then IFB b THEN c[1] ELSE c[2] FI / st ⇓ st'. 

     Since b is equivalent to BTrue, we know that beval st b = beval st BTrue = true. Together with the assumption that c[1] / st ⇓ st', we can apply E_IfTrue to derive IFB b THEN c[1] ELSE c[2] FI / st ⇓ st'. ☐

    Here is the formal version of this proof:

```

定理 IFB_true: ∀b c[1] c[2],

bequiv b BTrue  →

cequiv

(IFB b THEN c[1] ELSE c[2] FI)

c[1]。

    证明。

intros b c[1] c[2] Hb.

分割; intros H。

- (* -> *)

反转 H; 替换。

+ (* b 评估为真 *)

假设。

+ (* b 评估为假 (矛盾) *)

在 Hb 中展开 bequiv。在 Hb 中简化。

在 H[5] 中重写 Hb。

反转 H[5]。

- (* <- *)

应用 E_IfTrue; 尝试假设。

在 Hb 中展开 bequiv。在 Hb 中简化。

重写 Hb。一致性。已证明。

```

#### Exercise: 2 stars, recommended (IFB_false)

```

定理 IFB_false: ∀b c[1] c[2],

bequiv b BFalse  →

cequiv

(IFB b THEN c[1] ELSE c[2] FI)

c[2]。

证明。

(* 在这里填写 *) 已承认。

```

    ☐ 

#### Exercise: 3 stars (swap_if_branches)

    Show that we can swap the branches of an IF if we also negate its
    guard.

```

定理 swap_if_branches: ∀b e[1] e[2],

cequiv

(IFB b THEN e[1] ELSE e[2] FI)

(IFB BNot b THEN e[2] ELSE e[1] FI)。

证明。

(* 在这里填写 *) 已承认。

```

    ☐ 

    For WHILE loops, we can give a similar pair of theorems.  A loop
    whose guard is equivalent to BFalse is equivalent to SKIP,
    while a loop whose guard is equivalent to BTrue is equivalent to
    WHILE BTrue DO SKIP END (or any other non-terminating program).
    The first of these facts is easy.

```

定理 WHILE_false: ∀b c,

bequiv b BFalse →

cequiv

(WHILE b DO c END)

跳过。

    证明。

假设 b c Hb。分割；假设 H。

- (* -> *)

反演 H; 替换。

+ (* E_WhileEnd *)

应用 E_Skip。

+ (* E_WhileLoop *)

在 Hb 中重写 H[2]。反演 H[2]。

- (* <- *)

反演 H; 替换。

应用 E_WhileEnd。

重写 Hb。

一致性。证明。

```

#### Exercise: 2 stars, advanced, optional (WHILE_false_informal)

    Write an informal proof of WHILE_false.

    (* FILL IN HERE *)

    ☐ 

    To prove the second fact, we need an auxiliary lemma stating that
    WHILE loops whose guards are equivalent to BTrue never
    terminate. 

    *Lemma*: If b is equivalent to BTrue, then it cannot be the
    case that (WHILE b DO c END) / st ⇓ st'.

    *Proof*: Suppose that (WHILE b DO c END) / st ⇓ st'.  We show,
    by induction on a derivation of (WHILE b DO c END) / st ⇓ st',
    that this assumption leads to a contradiction.

*   Suppose (WHILE b DO c END) / st ⇓ st' is proved using rule E_WhileEnd. Then by assumption beval st b = false. But this contradicts the assumption that b is equivalent to BTrue. 

*   Suppose (WHILE b DO c END) / st ⇓ st' is proved using rule E_WhileLoop. Then we are given the induction hypothesis that (WHILE b DO c END) / st ⇓ st' is contradictory, which is exactly what we are trying to prove! 

*   Since these are the only rules that could have been used to prove (WHILE b DO c END) / st ⇓ st', the other cases of the induction are immediately contradictory. ☐

```

引理 WHILE_true_nonterm: ∀b c st st'，

bequiv b BTrue →

~( (WHILE b DO c END) / st ⇓ st' )。

证明。

(* 在课堂上运行 *)

假设 b c st st' Hb。

假设 H。

记住 (WHILE b DO c END) 为 cw，等式为 Heqcw。

归纳 H;

(* 大多数规则不适用，我们可以通过反演来排除它们 *)

反演 Heqcw; 替换；清除 Heqcw。

(* 两个有趣的情况是 WHILE 循环的情况： *)

- (* E_WhileEnd *) (* 矛盾 -- b 总是为真！ *)

在 Hb 中展开 bequiv。

(* rewrite 能够实例化 st 中的量词 *)

在 H 中重写 Hb。反演 H。

- (* E_WhileLoop *) (* 立即由 IH 推出 *)

应用 IHceval2。一致性。已证明。

```

#### Exercise: 2 stars, optional (WHILE_true_nonterm_informal)

    Explain what the lemma WHILE_true_nonterm means in English.

    (* FILL IN HERE *)

    ☐ 

#### Exercise: 2 stars, recommended (WHILE_true)

    Prove the following theorem. *Hint*: You'll want to use
    WHILE_true_nonterm here.

```

定理 WHILE_true: ∀b c，

bequiv b BTrue →

cequiv

(WHILE b DO c END)

(WHILE BTrue DO SKIP END)。

证明。

(* 在此填写 *) 已承认。

```

    ☐ 

    A more interesting fact about WHILE commands is that any finite
    number of copies of the body can be "unrolled" without changing
    meaning.  Unrolling is a common transformation in real compilers.

```

定理 loop_unrolling: ∀b c，

cequiv

(WHILE b DO c END)

(IFB b THEN (c ;; WHILE b DO c END) ELSE SKIP FI)。

证明。

(* 在课堂上运行 *)

    假设 b c st st'。

分割；假设 Hce。

- (* -> *)

反演 Hce; 替换。

+ (* 循环不运行 *)

应用 E_IfFalse。假设。应用 E_Skip。

+ (* 循环运行 *)

应用 E_IfTrue。假设。

应用 E_Seq 与 (st' := st'0)。假设。假设。

- (* <- *)

反演 Hce; 替换。

+ (* 循环运行 *)

反演 H[5]; 替换。

应用 E_WhileLoop 与 (st' := st'0)。

假设。假设。假设。

+ (* 循环不运行 *)

反演 H[5]; 替换。应用 E_WhileEnd。假设。已证明。

```

#### Exercise: 2 stars, optional (seq_assoc)

```

定理 seq_assoc: ∀c[1] c[2] c[3]，

cequiv ((c[1];;c[2]);;c[3]) (c[1];;(c[2];;c[3])。

证明。

(* 在此填写 *) 已承认。

```

    ☐ 

    Proving program properties involving assignments is one place
    where the Functional Extensionality axiom often comes in handy.

```

定理 identity_assignment: ∀(X:id)，

cequiv

(X ::= AId X)

跳过。

    证明。

intros。分割；引入 H。

- (* -> *)

反演 H; 替换。简化。

用 (t_update st X (st X)) 替换 st。

+ 构造者。

+ 应用 [functional_extensionality](http://coq.inria.fr/library/Coq.Logic.FunctionalExtensionality.html#functional_extensionality)。介绍。

重写 t_update_same；一致性。

- (* <- *)

用 (t_update st' X (aeval st' (AId X))) 替换 st'。

+ 反演 H。替换。应用 E_Ass。一致性。

+ 应用 [functional_extensionality](http://coq.inria.fr/library/Coq.Logic.FunctionalExtensionality.html#functional_extensionality)。介绍。

重写 t_update_same。一致性。

    已承认。

```

#### Exercise: 2 stars, recommended (assign_aequiv)

```

定理 assign_aequiv: ∀X e，

aequiv (AId X) e →

cequiv SKIP (X ::= e)。

证明。

(* 在此填写 *) 已承认。

```

    ☐ 

#### Exercise: 2 stars (equiv_classes)

    Given the following programs, group together those that are
    equivalent in Imp. Your answer should be given as a list of lists,
    where each sub-list represents a group of equivalent programs. For
    example, if you think programs (a) through (h) are all equivalent
    to each other, but not to (i), your answer should look like this:

```

[ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;

[prog_i] ]

    在下面的定义中写下你的答案

    等价类。

```
Definition prog_a : com :=
  WHILE BNot (BLe (AId X) (ANum 0)) DO
    X ::= APlus (AId X) (ANum 1)
  END.

Definition prog_b : com :=
  IFB BEq (AId X) (ANum 0) THEN
    X ::= APlus (AId X) (ANum 1);;
    Y ::= ANum 1
  ELSE
    Y ::= ANum 0
  FI;;
  X ::= AMinus (AId X) (AId Y);;
  Y ::= ANum 0.

Definition prog_c : com :=
  SKIP.

Definition prog_d : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= APlus (AMult (AId X) (AId Y)) (ANum 1)
  END.

Definition prog_e : com :=
  Y ::= ANum 0.

Definition prog_f : com :=
  Y ::= APlus (AId X) (ANum 1);;
  WHILE BNot (BEq (AId X) (AId Y)) DO
    Y ::= APlus (AId X) (ANum 1)
  END.

Definition prog_g : com :=
  WHILE BTrue DO
    SKIP
  END.

Definition prog_h : com :=
  WHILE BNot (BEq (AId X) (AId X)) DO
    X ::= APlus (AId X) (ANum 1)
  END.

Definition prog_i : com :=
  WHILE BNot (BEq (AId X) (AId Y)) DO
    X ::= APlus (AId Y) (ANum 1)
  END.

Definition equiv_classes : list (list com)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

```

    ☐

```

# Properties of Behavioral Equivalence

    We next consider some fundamental properties of the program
    equivalence relations.

```

## 行为等价是一个等价关系

    首先，我们验证 aexps、bexps 和的等价性

    coms 确实是*等价* — 即，它们是自反的，

    对称的，且传递的。所有证明都很容易。

```
Lemma refl_aequiv : ∀(a : aexp), aequiv a a.

    Proof.
  intros a st. reflexivity. Qed.

Lemma sym_aequiv : ∀(a[1] a[2] : aexp),
  aequiv a[1] a[2] → aequiv a[2] a[1].

    Proof.
  intros a[1] a[2] H. intros st. symmetry. apply H. Qed.

Lemma trans_aequiv : ∀(a[1] a[2] a[3] : aexp),
  aequiv a[1] a[2] → aequiv a[2] a[3] → aequiv a[1] a[3].

    Proof.
  unfold aequiv. intros a[1] a[2] a[3] H[12] H[23] st.
  rewrite (H[12] st). rewrite (H[23] st). reflexivity. Qed.

Lemma refl_bequiv : ∀(b : bexp), bequiv b b.

    Proof.
  unfold bequiv. intros b st. reflexivity. Qed.

Lemma sym_bequiv : ∀(b[1] b[2] : bexp),
  bequiv b[1] b[2] → bequiv b[2] b[1].

    Proof.
  unfold bequiv. intros b[1] b[2] H. intros st. symmetry. apply H. Qed.

Lemma trans_bequiv : ∀(b[1] b[2] b[3] : bexp),
  bequiv b[1] b[2] → bequiv b[2] b[3] → bequiv b[1] b[3].

    Proof.
  unfold bequiv. intros b[1] b[2] b[3] H[12] H[23] st.
  rewrite (H[12] st). rewrite (H[23] st). reflexivity. Qed.

Lemma refl_cequiv : ∀(c : com), cequiv c c.

    Proof.
  unfold cequiv. intros c st st'. apply [iff_refl](http://coq.inria.fr/library/Coq.Init.Logic.html#iff_refl). Qed.

Lemma sym_cequiv : ∀(c[1] c[2] : com),
  cequiv c[1] c[2] → cequiv c[2] c[1].

    Proof.
  unfold cequiv. intros c[1] c[2] H st st'.
  assert (c[1] / st ⇓ st' ↔ c[2] / st ⇓ st') as H'.
  { (* Proof of assertion *) apply H. }
  apply [iff_sym](http://coq.inria.fr/library/Coq.Init.Logic.html#iff_sym). assumption.
    Qed.

Lemma iff_trans : ∀(P[1] P[2] P[3] : Prop),
  (P[1] ↔ P[2]) → (P[2] ↔ P[3]) → (P[1] ↔ P[3]).

    Proof.
  intros P[1] P[2] P[3] H[12] H[23].
  inversion H[12]. inversion H[23].
  split; intros A.
    apply H[1]. apply H. apply A.
    apply H[0]. apply H[2]. apply A. Qed.

Lemma trans_cequiv : ∀(c[1] c[2] c[3] : com),
  cequiv c[1] c[2] → cequiv c[2] c[3] → cequiv c[1] c[3].

    Proof.
  unfold cequiv. intros c[1] c[2] c[3] H[12] H[23] st st'.
  apply iff_trans with (c[2] / st ⇓ st'). apply H[12]. apply H[23]. Qed.

```

## 行为等价是一个同余关系

    更不明显的是，行为等价也是一个*同余关系*。

    也就是说，两个子程序的等价性意味着

    它们嵌入的较大程序的等价性：

                        aequiv a[1] a[1]'

        |

        |

* * *

        |

                        cequiv (i ::= a[1]) (i ::= a[1]')

        |

                    |

                        cequiv c[1] c[1]'

        |

                    |

                        cequiv c[2] c[2]'

        |

        |

* * *

        |

                        cequiv (c[1];;c[2]) (c[1]';;c[2]')

        |

                    |

    ...等等其他形式的命令。

    （请注意，这里我们使用推理规则符号，而不是

    作为定义的一部分，而只是写下一些有效的

    以可读的格式证明这些含义。我们证明这些含义

    下文。 

    我们将看到为什么这些同余性的具体示例

    这些属性在以下部分中很重要（在证明中

    fold_constants_com_sound），但主要思想是它们允许

    我们可以用一个等价的小部分替换大程序的一部分

    微小部分，并知道整个大程序是等价的

    *而不是*对于不变部分进行显式证明 —

    即，对于大程序的微小更改的“证明负担”是

    与更改的大小成比例，而不是程序的大小。

```
Theorem CAss_congruence : ∀i a[1] a[1]',
  aequiv a[1] a[1]' →
  cequiv (CAss i a[1]) (CAss i a[1]').

    Proof.
  intros i a[1] a[2] Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity. Qed.

```

    循环的同余性质更有趣，

    因为它需要归纳。

    *定理*：对于 WHILE，等价是一个同余关系 — 即，如果

    b[1] 等价于 b[1]'，c[1] 等价于 c[1]'，那么

    WHILE b[1] DO c[1] END 等价于 WHILE b[1]' DO c[1]' END。

    *证明*：假设 b[1] 等价于 b[1]'，c[1] 等价于

    等价于 c[1]'。我们必须证明，对于每个 st 和 st'，都有

    WHILE b[1] DO c[1] END / st ⇓ st' 当且仅当 WHILE b[1]' DO c[1]' END / st ⇓ st'。我们分别考虑这两个方向。

+   （→）我们通过对 WHILE b[1] DO c[1] END / st ⇓ st' 的推导进行归纳，证明 WHILE b[1] DO c[1] END / st ⇓ st' 意味着 WHILE b[1]' DO c[1]' END / st ⇓ st'，推导的最终规则是 E_WhileEnd 或 E_WhileLoop 时，这是唯一的非平凡情况。

    +   E_WhileEnd：在这种情况下，规则的形式给出 beval st b[1] = false 和 st = st'。但是，由于 b[1] 和 b[1]' 是等价的，我们有 beval st b[1]' = false，然后 E-WhileEnd 应用，给出 WHILE b[1]' DO c[1]' END / st ⇓ st'，如所需。

    +   E_WhileLoop：现在规则的形式给出 beval st b[1] = true，其中 c[1] / st ⇓ st'0，且 WHILE b[1] DO c[1] END / st'0 ⇓ st' 对于某个状态 st'0，根据归纳假设 WHILE b[1]' DO c[1]' END / st'0 ⇓ st'。

        由于 c[1] 和 c[1]' 是等价的，我们知道 c[1]' / st ⇓ st'0。由于 b[1] 和 b[1]' 是等价的，我们有 beval st b[1]' = true。现在 E-WhileLoop 应用，给出 WHILE b[1]' DO c[1]' END / st ⇓ st'，如所需。

+   （←）类似。☐

```
Theorem CWhile_congruence : ∀b[1] b[1]' c[1] c[1]',
  bequiv b[1] b[1]' → cequiv c[1] c[1]' →
  cequiv (WHILE b[1] DO c[1] END) (WHILE b[1]' DO c[1]' END).
Proof.
  (* WORKED IN CLASS *)
  unfold bequiv,cequiv.
  intros b[1] b[1]' c[1] c[1]' Hb1e Hc1e st st'.
  split; intros Hce.
  - (* -> *)
    remember (WHILE b[1] DO c[1] END) as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileEnd *)
      apply E_WhileEnd. rewrite ← Hb1e. apply H.
    + (* E_WhileLoop *)
      apply E_WhileLoop with (st' := st').
      * (* show loop runs *) rewrite ← Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st'). apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.
  - (* <- *)
    remember (WHILE b[1]' DO c[1]' END) as c'while
      eqn:Heqc'while.
    induction Hce; inversion Heqc'while; subst.
    + (* E_WhileEnd *)
      apply E_WhileEnd. rewrite → Hb1e. apply H.
    + (* E_WhileLoop *)
      apply E_WhileLoop with (st' := st').
      * (* show loop runs *) rewrite → Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st'). apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity. Qed.

```

#### 练习：3 星，可选（CSeq_congruence）

```
Theorem CSeq_congruence : ∀c[1] c[1]' c[2] c[2]',
  cequiv c[1] c[1]' → cequiv c[2] c[2]' →
  cequiv (c[1];;c[2]) (c[1]';;c[2]').
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星（CIf_congruence）

```
Theorem CIf_congruence : ∀b b' c[1] c[1]' c[2] c[2]',
  bequiv b b' → cequiv c[1] c[1]' → cequiv c[2] c[2]' →
  cequiv (IFB b THEN c[1] ELSE c[2] FI)
         (IFB b' THEN c[1]' ELSE c[2]' FI).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

    例如，这里有两个等价的程序及其证明

    equivalence...

```
Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (* Program 2: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X)   (* <--- changed here *)
     ELSE
       Y ::= ANum 42
     FI).
Proof.
  apply CSeq_congruence.
    apply refl_cequiv.
    apply CIf_congruence.
      apply refl_bequiv.
      apply CAss_congruence. unfold aequiv. simpl.
        symmetry. apply minus_diag.
      apply refl_cequiv.
Qed.

```

#### Exercise: 3 stars, advanced, optional (not_congr)

    We've shown that the cequiv relation is both an equivalence and

    a congruence on commands.  Can you think of a relation on commands

    that is an equivalence but *not* a congruence?

```
(* FILL IN HERE *)

```

    ☐

```

# Program Transformations

    A *program transformation* is a function that takes a program as
    input and produces some variant of the program as output.
    Compiler optimizations such as constant folding are a canonical
    example, but there are many others. 

    A program transformation is *sound* if it preserves the
    behavior of the original program.

```

Definition atrans_sound (atrans : aexp → aexp) : Prop :=

∀(a : aexp),

aequiv a (atrans a).

Definition btrans_sound (btrans : bexp → bexp) : Prop :=

∀(b : bexp),

bequiv b (btrans b).

Definition ctrans_sound (ctrans : com → com) : Prop :=

∀(c : com),

cequiv c (ctrans c).

```

## The Constant-Folding Transformation

    An expression is *constant* when it contains no variable
    references.

    Constant folding is an optimization that finds constant
    expressions and replaces them by their values.

```

Fixpoint fold_constants_aexp (a : aexp) : aexp :=

match a with

| ANum n       ⇒ ANum n

| AId i        ⇒ AId i

| APlus a[1] a[2]  ⇒

match (fold_constants_aexp a[1], fold_constants_aexp a[2])

with

| (ANum n[1], ANum n[2]) ⇒ ANum (n[1] + n[2])

| (a[1]', a[2]') ⇒ APlus a[1]' a[2]'

end

| AMinus a[1] a[2] ⇒

match (fold_constants_aexp a[1], fold_constants_aexp a[2])

with

| (ANum n[1], ANum n[2]) ⇒ ANum (n[1] - n[2])

| (a[1]', a[2]') ⇒ AMinus a[1]' a[2]'

end

| AMult a[1] a[2]  ⇒

match (fold_constants_aexp a[1], fold_constants_aexp a[2])

with

| (ANum n[1], ANum n[2]) ⇒ ANum (n[1] * n[2])

| (a[1]', a[2]') ⇒ AMult a[1]' a[2]'

end

end.

Example fold_aexp_ex[1] :

fold_constants_aexp

(AMult (APlus (ANum 1) (ANum 2)) (AId X))

= AMult (ANum 3) (AId X).

    Proof. reflexivity. Qed.

```

    Note that this version of constant folding doesn't eliminate
    trivial additions, etc. — we are focusing attention on a single
    optimization for the sake of simplicity.  It is not hard to
    incorporate other ways of simplifying expressions; the definitions
    and proofs just get longer.

```

Example fold_aexp_ex[2] :

fold_constants_aexp

(AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6))

(AId Y)))

= AMinus (AId X) (APlus (ANum 0) (AId Y)).

    Proof. reflexivity. Qed.

```

    Not only can we lift fold_constants_aexp to bexps (in the
    BEq and BLe cases); we can also look for constant *boolean*
    expressions and evaluate them in-place.

```

Fixpoint fold_constants_bexp (b : bexp) : bexp :=

match b with

| BTrue        ⇒ BTrue

| BFalse       ⇒ BFalse

| BEq a[1] a[2]  ⇒

match (fold_constants_aexp a[1], fold_constants_aexp a[2]) with

| (ANum n[1], ANum n[2]) ⇒

if beq_nat n[1] n[2] then BTrue else BFalse

| (a[1]', a[2]') ⇒

BEq a[1]' a[2]'

end

| BLe a[1] a[2]  ⇒

match (fold_constants_aexp a[1], fold_constants_aexp a[2]) with

| (ANum n[1], ANum n[2]) ⇒

if leb n[1] n[2] then BTrue else BFalse

| (a[1]', a[2]') ⇒

BLe a[1]' a[2]'

end

| BNot b[1]  ⇒

match (fold_constants_bexp b[1]) with

| BTrue ⇒ BFalse

| BFalse ⇒ BTrue

| b[1]' ⇒ BNot b[1]'

end

| BAnd b[1] b[2]  ⇒

match (fold_constants_bexp b[1], fold_constants_bexp b[2]) with

| (BTrue, BTrue) ⇒ BTrue

| (BTrue, BFalse) ⇒ BFalse

| (BFalse, BTrue) ⇒ BFalse

| (BFalse, BFalse) ⇒ BFalse

| (b[1]', b[2]') ⇒ BAnd b[1]' b[2]'

end

end.

Example fold_bexp_ex[1] :

fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))

= BTrue.

    Proof. reflexivity. Qed.

Example fold_bexp_ex[2] :

fold_constants_bexp

(BAnd (BEq (AId X) (AId Y))

(BEq (ANum 0)

(AMinus (ANum 2) (APlus (ANum 1)

(ANum 1)))))

= BAnd (BEq (AId X) (AId Y)) BTrue.

    Proof. reflexivity. Qed.

```

    To fold constants in a command, we apply the appropriate folding
    functions on all embedded expressions.

```

Fixpoint fold_constants_com (c : com) : com :=

match c with

| SKIP      ⇒

SKIP

| i ::= a  ⇒

CAss i (fold_constants_aexp a)

| c[1] ;; c[2]  ⇒

(fold_constants_com c[1]) ;; (fold_constants_com c[2])

| IFB b THEN c[1] ELSE c[2] FI ⇒

match fold_constants_bexp b with

| BTrue ⇒ fold_constants_com c[1]

| BFalse ⇒ fold_constants_com c[2]

| b' ⇒ IFB b' THEN fold_constants_com c[1]

ELSE fold_constants_com c[2] FI

end

| WHILE b DO c END ⇒

匹配 fold_constants_bexp b with

| BTrue ⇒ WHILE BTrue DO SKIP END

| BFalse ⇒ SKIP

| b' ⇒ WHILE b' DO (fold_constants_com c) END

end

end.

例如 fold_com_ex[1]：

fold_constants_com

(* 原始程序： *)

(X ::= APlus (ANum 4) (ANum 5);;

Y ::= AMinus (AId X) (ANum 3);;

IFB BEq (AMinus (AId X) (AId Y))

(APlus (ANum 2) (ANum 4)) 然后

SKIP

ELSE

Y ::= ANum 0

FI;;

IFB BLe (ANum 0)

(AMinus (ANum 4) (APlus (ANum 2) (ANum 1)))

然后

Y ::= ANum 0

ELSE

SKIP

FI;;

当 BEq (AId Y) (ANum 0) 时

X ::= APlus (AId X) (ANum 1)

END)

= (* 常量折叠后： *)

(X ::= ANum 9;;

Y ::= AMinus (AId X) (ANum 3);;

IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN

SKIP

否则

(Y ::= ANum 0)

FI;;

Y ::= ANum 0;;

当 BEq (AId Y) (ANum 0) 时

X ::= APlus (AId X) (ANum 1)

END).

    证明。反射性。证毕。

```

## Soundness of Constant Folding

    Now we need to show that what we've done is correct. 

    Here's the proof for arithmetic expressions:

```

定理 fold_constants_aexp_sound：

atrans_sound fold_constants_aexp.

    证明。

展开 [atrans_sound](https://wiki.example.org/atrans_sound)。intros a. 展开 [aequiv](https://wiki.example.org/aequiv)。intros st.

归纳 a; 简化;

(* ANum 和 AId 立即得出 *)

尝试反射性;

(* APlus，AMinus 和 AMult 遵循 IH 和观察到的 aeval st (APlus a[1] a[2]) = ANum ((aeval st a[1]) + (aeval st a[2])) = aeval st (ANum ((aeval st a[1]) + (aeval st a[2])))（对于 AMinus/减法 和 AMult/乘法也是类似的） *)

尝试 (destruct ([fold_constants_aexp](https://wiki.example.org/fold_constants_aexp) a[1]);

destruct ([fold_constants_aexp](https://wiki.example.org/fold_constants_aexp) a[2]);

重写 IHa1; 重写 IHa2; 反射性）。���毕。

```

#### Exercise: 3 stars, optional (fold_bexp_Eq_informal)

    Here is an informal proof of the BEq case of the soundness
    argument for boolean expression constant folding.  Read it
    carefully and compare it to the formal proof that follows.  Then
    fill in the BLe case of the formal proof (without looking at the
    BEq case, if possible).

    *Theorem*: The constant folding function for booleans,
   fold_constants_bexp, is sound.

    *Proof*: We must show that b is equivalent to fold_constants_bexp,
   for all boolean expressions b.  Proceed by induction on b.  We
   show just the case where b has the form BEq a[1] a[2].

    In this case, we must show

```

beval st (BEq a[1] a[2])

= beval st (fold_constants_bexp (BEq a[1] a[2])).

    有两种情况需要考虑：

+   首先，假设 fold_constants_aexp a[1] = ANum n[1]，fold_constants_aexp a[2] = ANum n[2]，其中 n[1] 和 n[2] 是一些数。

    在这种情况下，我们有

    ```
        fold_constants_bexp (BEq a[1] a[2])
      = if beq_nat n[1] n[2] then BTrue else BFalse

     and 

    ```

    beval st (BEq a[1] a[2])

    = beq_nat (aeval st a[1]) (aeval st a[2]).

    通过算术表达式的常量折叠的正确性（引理 fold_constants_aexp_sound），我们知道

    ```
        aeval st a[1]
      = aeval st (fold_constants_aexp a[1])
      = aeval st (ANum n[1])
      = n[1]

     and 

    ```

    aeval st a[2]

    = aeval st (fold_constants_aexp a[2])

    = aeval st (ANum n[2])

    = n[2],

    所以

    ```
        beval st (BEq a[1] a[2])
      = beq_nat (aeval a[1]) (aeval a[2])
      = beq_nat n[1] n[2].

     Also, it is easy to see (by considering the cases n[1] = n[2] and n[1] ≠ n[2] separately) that 

    ```

    beval st (if beq_nat n[1] n[2] then BTrue else BFalse)

    = if beq_nat n[1] n[2] then beval st BTrue else beval st BFalse

    = if beq_nat n[1] n[2] then true else false

    = beq_nat n[1] n[2].

    所以

    ```
        beval st (BEq a[1] a[2])
      = beq_nat n[1] n[2].
      = beval st (if beq_nat n[1] n[2] then BTrue else BFalse),

     as required. 

    ```

    ```

    ```

    ```

    ```

    ```

    ```

+   否则，fold_constants_aexp a[1] 和 fold_constants_aexp a[2] 中的一个不是常数。在这种情况下，我们必须展示

    ```
        beval st (BEq a[1] a[2])
      = beval st (BEq (fold_constants_aexp a[1])
                      (fold_constants_aexp a[2])),

     which, by the definition of beval, is the same as showing 

    ```

    beq_nat (aeval st a[1]) (aeval st a[2])

    = beq_nat (aeval st (fold_constants_aexp a[1]))

    (aeval st (fold_constants_aexp a[2])).

    但是算术表达式的常量折叠的正确性（fold_constants_aexp_sound）告诉我们

    ```
      aeval st a[1] = aeval st (fold_constants_aexp a[1])
      aeval st a[2] = aeval st (fold_constants_aexp a[2]),

     completing the case. ☐
    ```

    ```

    ```

```
Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* BTrue and BFalse are immediate *)
    try reflexivity.
  - (* BEq *)
    rename a into a[1]. rename a[0] into a[2]. simpl.

```

    （当有很多构造函数时进行归纳会变得困难）

    指定变量名是一项繁琐的工作，但 Coq 并不总是

    选择好的变量名。我们可以重命名条目

    使用重命名策略的上下文：将 a 重命名为 a[1] 将

    将当前目标和上下文中的 a 更改为 a[1]。）

```
    remember (fold_constants_aexp a[1]) as a[1]' eqn:Heqa1'.
    remember (fold_constants_aexp a[2]) as a[2]' eqn:Heqa2'.
    replace (aeval st a[1]) with (aeval st a[1]') by
       (subst a[1]'; rewrite ← fold_constants_aexp_sound; reflexivity).
    replace (aeval st a[2]) with (aeval st a[2]') by
       (subst a[2]'; rewrite ← fold_constants_aexp_sound; reflexivity).
    destruct a[1]'; destruct a[2]'; try reflexivity.

    (* The only interesting case is when both a[1] and a[2]        become constants after folding *)
      simpl. destruct (beq_nat n n[0]); reflexivity.
  - (* BLe *)
    (* FILL IN HERE *) admit.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b[1]) as b[1]' eqn:Heqb1'.
    remember (fold_constants_bexp b[2]) as b[2]' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b[1]'; destruct b[2]'; reflexivity.
(* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星（fold_constants_com_sound）

    完成以下证明中的 WHILE 情况。

```
Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* SKIP *) apply refl_cequiv.
  - (* ::= *) apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - (* ;; *) apply CSeq_congruence; assumption.
  - (* IFB *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the           result is easy to prove from the IH and           fold_constants_bexp_sound.) *)
    + (* b always true *)
      apply trans_cequiv with c[1]; try assumption.
      apply IFB_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c[2]; try assumption.
      apply IFB_false; assumption.
  - (* WHILE *)
    (* FILL IN HERE *) Admitted.

```

    ☐

```

### Soundness of (0 + n) Elimination, Redux

#### Exercise: 4 stars, advanced, optional (optimize_0plus)

    Recall the definition optimize_0plus from the Imp chapter:

```

Fixpoint optimize_0plus (e:aexp) : aexp :=

匹配 e 与

| ANum n ⇒

ANum n

| APlus (ANum 0) e[2] ⇒

optimize_0plus e[2]

| APlus e[1] e[2] ⇒

APlus (optimize_0plus e[1]) (optimize_0plus e[2])

| AMinus e[1] e[2] ⇒

AMinus (optimize_0plus e[1]) (optimize_0plus e[2])

| AMult e[1] e[2] ⇒

AMult (optimize_0plus e[1]) (optimize_0plus e[2])

结束。

    请注意，此函数是针对旧的 aexp 定义的，

没有状态。

    编写一个考虑变量的新版本的此函数，

以及布尔表达式和命令的类似情况：

```
     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com

    Prove that these three functions are sound, as we did for
   fold_constants_*.  Make sure you use the congruence lemmas in
   the proof of optimize_0plus_com — otherwise it will be *long*!

    Then define an optimizer on commands that first folds
   constants (using fold_constants_com) and then eliminates 0 + n
   terms (using optimize_0plus_com).

*   Give a meaningful example of this optimizer's output. 

*   Prove that the optimizer is sound. (This part should be *very* easy.)

```

(* 在这里填写 *)

```

    ☐

```

# 证明程序*不*等价的方法

    假设 c[1] 是形如 X ::= a[1];; Y ::= a[2] 的命令

    而 c[2] 是命令 X ::= a[1];; Y ::= a[2]', 其中 a[2]' 是

    通过将 a[1] 替换为 a[2] 中所有出现的 X 而形成。

    例如，c[1] 和 c[2] 可能是：

```
       c[1]  =  (X ::= 42 + 53;;
               Y ::= Y + X)
       c[2]  =  (X ::= 42 + 53;;
               Y ::= Y + (42 + 53))

    Clearly, this *particular* c[1] and c[2] are equivalent.  Is this
    true in general? 

    We will see in a moment that it is not, but it is worthwhile
    to pause, now, and see if you can find a counter-example on your
    own. 

    More formally, here is the function that substitutes an arithmetic
    expression for each occurrence of a given variable in another
    expression:

```

Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=

匹配 a 与

| ANum n       ⇒

ANum n

| AId i'       ⇒

如果 beq_id i i' 则 u 否则 AId i'

| APlus a[1] a[2]  ⇒

APlus (subst_aexp i u a[1]) (subst_aexp i u a[2])

| AMinus a[1] a[2] ⇒

AMinus (subst_aexp i u a[1]) (subst_aexp i u a[2])

| AMult a[1] a[2]  ⇒

AMult (subst_aexp i u a[1]) (subst_aexp i u a[2])

结束。

例如 subst_aexp_ex：

subst_aexp X (APlus (ANum 42) (ANum 53))

(APlus (AId Y) (AId X))

= (APlus (AId Y) (APlus (ANum 42) (ANum 53))).

    证明。反射性。Qed.

```

    And here is the property we are interested in, expressing the
    claim that commands c[1] and c[2] as described above are
    always equivalent.

```

定义 subst_equiv_property := ∀i[1] i[2] a[1] a[2],

cequiv (i[1] ::= a[1];; i[2] ::= a[2])

(i[1] ::= a[1];; i[2] ::= subst_aexp i[1] a[1] a[2]).

```

    Sadly, the property does *not* always hold — i.e., it is not the
    case that, for all i[1], i[2], a[1], and a[2],

```

cequiv (i[1] ::= a[1];; i[2] ::= a[2])

(i[1] ::= a[1];; i[2] ::= subst_aexp i[1] a[1] a[2]).

    为了看到这一点，假设（为了推导出矛盾）对于所有 i[1], i[2]，

    a[1] 和 a[2]，我们有

```
      cequiv (i[1] ::= a[1];; i[2] ::= a[2])
             (i[1] ::= a[1];; i[2] ::= subst_aexp i[1] a[1] a[2]).

    Consider the following program:

```

X ::= APlus (AId X) (ANum 1);; Y ::= AId X

    注意

```
       (X ::= APlus (AId X) (ANum 1);; Y ::= AId X)
       / empty_state ⇓ st[1],

    where st[1] = { X ↦ 1, Y ↦ 1 }.

    By assumption, we know that

```

cequiv (X ::= APlus (AId X) (ANum 1);;

Y ::= AId X)

(X ::= APlus (AId X) (ANum 1);;

Y ::= APlus (AId X) (ANum 1))

    因此，根据 cequiv 的定义，我们有

```
      (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))
      / empty_state ⇓ st[1].

    But we can also derive

```

(X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))

/ empty_state ⇓ st[2],

    其中 st[2] = { X ↦ 1, Y ↦ 2 }。但 st[1] ≠ st[2]，这是一个

    矛盾，因为 ceval 是确定性的！ ☐

```
Theorem subst_inequiv :
  ¬ subst_equiv_property.

    Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that subst_equiv_property      holds allows us to prove that these two programs are      equivalent... *)
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= AId X)
      as c[1].
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= APlus (AId X) (ANum 1))
      as c[2].
  assert (cequiv c[1] c[2]) by (subst; apply Contra).

  (* ... allows us to show that the command c[2] can terminate      in two different final states:         st[1] = {X |-> 1, Y |-> 1}         st[2] = {X |-> 1, Y |-> 2}. *)
  remember (t_update (t_update empty_state X 1) Y 1) as st[1].
  remember (t_update (t_update empty_state X 1) Y 2) as st[2].
  assert (H[1]: c[1] / empty_state ⇓ st[1]);
  assert (H[2]: c[2] / empty_state ⇓ st[2]);
  try (subst;
       apply E_Seq with (st' := (t_update empty_state X 1));
       apply E_Ass; reflexivity).
  apply H in H[1].

  (* Finally, we use the fact that evaluation is deterministic      to obtain a contradiction. *)
  assert (Hcontra: st[1] = st[2])
    by (apply (ceval_deterministic c[2] empty_state); assumption).
  assert (Hcontra': st[1] Y = st[2] Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'. Qed.

```

#### 练习：4 星，可选（better_subst_equiv）

    我们上面所考虑的等价性并非完全胡说八道 —

    实际上几乎是正确的。要使其正确，我们只需要

    排除变量 X 出现在

    第一个赋值语句的右侧。

```
Inductive var_not_used_in_aexp (X:id) : aexp → Prop :=
  | VNUNum: ∀n, var_not_used_in_aexp X (ANum n)
  | VNUId: ∀Y, X ≠ Y → var_not_used_in_aexp X (AId Y)
  | VNUPlus: ∀a[1] a[2],
      var_not_used_in_aexp X a[1] →
      var_not_used_in_aexp X a[2] →
      var_not_used_in_aexp X (APlus a[1] a[2])
  | VNUMinus: ∀a[1] a[2],
      var_not_used_in_aexp X a[1] →
      var_not_used_in_aexp X a[2] →
      var_not_used_in_aexp X (AMinus a[1] a[2])
  | VNUMult: ∀a[1] a[2],
      var_not_used_in_aexp X a[1] →
      var_not_used_in_aexp X a[2] →
      var_not_used_in_aexp X (AMult a[1] a[2]).

Lemma aeval_weakening : ∀i st a ni,
  var_not_used_in_aexp i a →
  aeval (t_update st i ni) a = aeval st a.
Proof.
  (* FILL IN HERE *) Admitted.

```

    使用 var_not_used_in_aexp，形式化并证明一个正确的版本

    subst_equiv_property 的证明。

```
(* FILL IN HERE *)

```

    ☐

#### 练习���3 星（inequiv_exercise）

    证明无限循环不等价于 SKIP

```
Theorem inequiv_exercise:
  ¬ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

# Extended Exercise: Nondeterministic Imp

    As we have seen (in theorem ceval_deterministic in the Imp
    chapter), Imp's evaluation relation is deterministic.  However,
    *non*-determinism is an important part of the definition of many
    real programming languages. For example, in many imperative
    languages (such as C and its relatives), the order in which
    function arguments are evaluated is unspecified.  The program
    fragment

```

x = 0;;

f(++x, x)

    可能会调用 f 时传入参数 (1, 0) 或 (1, 1)，取决于

    编译器选择排列事物的方式。这可能有点

    对程序员来说可能会有些困惑，但对编译器编写者来说却很有用

    自由。

    在这个练习中，我们将用一个简单的 Imp 扩展 Imp

    非确定性命令并研究这种变化如何影响

    程序等价性。新命令的语法是 HAVOC X，

    其中 X 是一个标识符。执行 HAVOC X 的效果是

    给变量 X 分配一个*任意*数字，

    非确定性地。例如，在执行程序后：

```
      HAVOC Y;;
      Z ::= Y * 2

    the value of Y can be any number, while the value of Z is
    twice that of Y (so Z is always even). Note that we are not
    saying anything about the *probabilities* of the outcomes — just
    that there are (infinitely) many different outcomes that can
    possibly happen after executing this nondeterministic code.

    In a sense, a variable on which we do HAVOC roughly corresponds
    to an unitialized variable in a low-level language like C.  After
    the HAVOC, the variable holds a fixed but arbitrary number.  Most
    sources of nondeterminism in language definitions are there
    precisely because programmers don't care which choice is made (and
    so it is good to leave it open to the compiler to choose whichever
    will run faster).

    We call this new language *Himp* (``Imp extended with HAVOC'').

```

模块 Himp。

```

    To formalize Himp, we first add a clause to the definition of
    commands.

```

归纳定义 com：Type :=

| CSkip : com

| CAss : id → aexp → com

| CSeq : com → com → com

| CIf : bexp → com → com → com

| CWhile : bexp → com → com

| CHavoc : id → com。 (* <---- 新的 *)

记号 "'SKIP'" :=

CSkip。

记号 "'X ::= a'" :=

(CAss X a)（优先级为 60）。

记号 "c1 ;; c2" :=

(CSeq c[1] c[2])（优先级为 80，右结合性）。

记号 "'WHILE' b 'DO' c 'END'" :=

(CWhile b c)（优先级为 80，右结合性）。

记号 "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=

(CIf e[1] e[2] e[3])（优先级为 80，右结合性）。

记号 "'HAVOC' l" := (CHavoc l)（优先级为 60）。

```

#### Exercise: 2 stars (himp_ceval)

    Now, we must extend the operational semantics. We have provided
   a template for the ceval relation below, specifying the big-step
   semantics. What rule(s) must be added to the definition of ceval
   to formalize the behavior of the HAVOC command?

```

保留记号 "c1 '/' st '⇓' st'"。

（优先级为 40，st 优先级为 39）。

归纳定义 ceval：com → state → state → Prop :=

| E_Skip : ∀st : state, SKIP / st ⇓ st

| E_Ass : ∀(st : state) (a[1] : aexp) (n : nat) (X : id)，

aeval st a[1] = n →

(X ::= a[1]) / st ⇓ t_update st X n

| E_Seq : ∀(c[1] c[2] : com) (st st' st'' : state)，

c[1] / st ⇓ st' →

c[2] / st' ⇓ st'' →

(c[1] ;; c[2]) / st ⇓ st''。

| E_IfTrue : ∀(st st' : state) (b[1] : bexp) (c[1] c[2] : com),

beval st b[1] = true →

c[1] / st ⇓ st' →

(IFB b[1] THEN c[1] ELSE c[2] FI) / st ⇓ st'

| E_IfFalse : ∀(st st' : state) (b[1] : bexp) (c[1] c[2] : com)，

beval st b[1] = false →

c[2] / st ⇓ st' →

(IFB b[1] THEN c[1] ELSE c[2] FI) / st ⇓ st'

| E_WhileEnd : ∀(b[1] : bexp) (st : state) (c[1] : com)，

beval st b[1] = false。

(WHILE b[1] DO c[1] END) / st ⇓ st

| E_WhileLoop : ∀(st st' st'' : state) (b[1] : bexp) (c[1] : com),

beval st b[1] = true →

c[1] / st ⇓ st' →

(WHILE b[1] DO c[1] END) / st' ⇓ st'' →

(WHILE b[1] DO c[1] END) / st ⇓ st''

(* 在此填写 *)

其中 "c1 '/' st '⇓' st'" := (ceval c[1] st st')。

```

    As a sanity check, the following claims should be provable for
    your definition:

```

示例 havoc_example1：（HAVOC X）/ empty_state ⇓ t_update empty_state X 0。

证明。

(* 在此填写 *) 已被承认。

示例 havoc_example2：

(SKIP;; HAVOC Z) / empty_state ⇓ t_update empty_state Z 42。

证明。

(* 在此填写 *) 已被承认。

```

    ☐ 

    Finally, we repeat the definition of command equivalence from above:

```

定义 cequiv (c[1] c[2] : com) : Prop := ∀st st' : state，

c[1] / st ⇓ st' ↔ c[2] / st ⇓ st'。

```

    Let's apply this definition to prove some nondeterministic
    programs equivalent / inequivalent. 

#### Exercise: 3 stars (havoc_swap)

    Are the following two programs equivalent?

```

定义 pXY :=

HAVOC X;; HAVOC Y。

定义 pYX :=

HAVOC Y;; HAVOC X。

```

    If you think they are equivalent, prove it. If you think they are
    not, prove that.

```

定理 pXY_cequiv_pYX：

cequiv pXY pYX ∨ ¬cequiv pXY pYX。

证明。 (* 在此填写 *) 已被承认。

```

    ☐ 

#### Exercise: 4 stars, optional (havoc_copy)

    Are the following two programs equivalent?

```

定义 ptwice :=

HAVOC X;; HAVOC Y。

定义 pcopy :=

HAVOC X;; Y ::= AId X。

```

    If you think they are equivalent, then prove it. If you think they
    are not, then prove that.  (Hint: You may find the assert tactic
    useful.)

```

定理 ptwice_cequiv_pcopy：

cequiv ptwice pcopy ∨ ¬cequiv ptwice pcopy。

证明。 (* 在此填写 *) 已被承认。

```

    ☐ 

    The definition of program equivalence we are using here has some
    subtle consequences on programs that may loop forever.  What
    cequiv says is that the set of possible *terminating* outcomes
    of two equivalent programs is the same. However, in a language
    with nondeterminism, like Himp, some programs always terminate,
    some programs always diverge, and some programs can
    nondeterministically terminate in some runs and diverge in
    others. The final part of the following exercise illustrates this
    phenomenon.

#### Exercise: 4 stars, advanced (p1_p2_term)

    Consider the following commands:

```

定义 p[1]：com :=

WHILE (BNot (BEq (AId X) (ANum 0))) DO

HAVOC Y;;

X ::= APlus (AId X) (ANum 1)

END。

定义 p[2]：com :=

WHILE (BNot (BEq (AId X) (ANum 0))) DO

SKIP

END。

```

    Intuitively, p[1] and p[2] have the same termination behavior:
    either they loop forever, or they terminate in the same state they
    started in.  We can capture the termination behavior of p[1] and
    p[2] individually with these lemmas:

```

引理 p1_may_diverge：∀st st'，st X ≠ 0 →

¬ p[1] / st ⇓ st'。

证明。 (* 在此填写 *) 已被承认。

引理 p2_may_diverge：∀st st'，st X ≠ 0 →

¬ p[2] / st ⇓ st'。

证明。

(* 在此填写 *) 已被承认。

```

    ☐ 

#### Exercise: 4 stars, advanced (p1_p2_equiv)

    Use these two lemmas to prove that p[1] and p[2] are actually
    equivalent.

```

定理 p1_p2_equiv：cequiv p[1] p[2]。

证明。 (* 在此填写 *) 已被承认。

```

    ☐ 

#### Exercise: 4 stars, advancedM (p3_p4_inequiv)

    Prove that the following programs are *not* equivalent.  (Hint:
    What should the value of Z be when p[3] terminates?  What about
    p[4]?)

```

定义 p[3]：com :=

Z ::= ANum 1;;

WHILE (BNot (BEq (AId X) (ANum 0))) DO

HAVOC X;;

HAVOC Z

END.

定义 p[4] : com :=

X ::= (ANum 0);;

Z ::= (ANum 1).

定理 p3_p4_inequiv : ¬ cequiv p[3] p[4].

证明。 (* 在这里填写 *) 已承认。

```

    ☐ 

#### Exercise: 5 stars, advanced, optional (p5_p6_equiv)

    Prove that the following commands are equivalent.  (Hint: As
    mentioned above, our definition of cequiv for Himp only takes
    into account the sets of possible terminating configurations: two
    programs are equivalent if and only if when given a same starting
    state st, the set of possible terminating states is the same for
    both programs. If p[5] terminates, what should the final state be?
    Conversely, is it always possible to make p[5] terminate?)

```

定义 p[5] : com :=

WHILE (BNot (BEq (AId X) (ANum 1))) DO

HAVOC X

END.

定义 p[6] : com :=

X ::= ANum 1.

定理 p5_p6_equiv : cequiv p[5] p[6].

证明。 (* 在这里填写 *) 已承认。

```

    ☐

```

结束 Himp.

```

# Additional Exercises

#### Exercise: 4 stars, optional (for_while_equiv)

    This exercise extends the optional add_for_loop exercise from
    the Imp chapter, where you were asked to extend the language
    of commands with C-style for loops.  Prove that the command:

```

对于 (c[1] ; b ; c[2]) {

c[3]

}

    等同于：

```
       c[1] ;
       WHILE b DO
         c[3] ;
         c[2]
       END

```

(* 在这里填写 *)

```

    ☐ 

#### Exercise: 3 stars, optional (swap_noninterfering_assignments)

    (Hint: You'll need functional_extensionality for this one.)

```

定理 swap_noninterfering_assignments: ∀l[1] l[2] a[1] a[2],

l[1] ≠ l[2] →

var_not_used_in_aexp l[1] a[2] →

var_not_used_in_aexp l[2] a[1] →

cequiv

(l[1] ::= a[1];; l[2] ::= a[2])

(l[2] ::= a[2];; l[1] ::= a[1]).

证明。

(* 在这里填写 *) 已承认。

```

    ☐ 

#### Exercise: 4 stars, advanced, optional (capprox)

    In this exercise we define an asymmetric variant of program
    equivalence we call *program approximation*. We say that a
    program c[1] *approximates* a program c[2] when, for each of
    the initial states for which c[1] terminates, c[2] also terminates
    and produces the same final state. Formally, program approximation
    is defined as follows:

```

定义 capprox (c[1] c[2] : com) : Prop := ∀(st st' : state),

c[1] / st ⇓ st' → c[2] / st ⇓ st'.

```

    For example, the program c[1] = WHILE X ≠ 1 DO X ::= X - 1 END
    approximates c[2] = X ::= 1, but c[2] does not approximate c[1]
    since c[1] does not terminate when X = 0 but c[2] does.  If two
    programs approximate each other in both directions, then they are
    equivalent. 

    Find two programs c[3] and c[4] such that neither approximates
    the other.

```

定义 c[3] : com (* 用":= _your_definition_ ."替换此行 *). 已承认。

定义 c[4] : com (* 用":= _your_definition_ ."替换此行 *). 已承认。

定理 c3_c4_different : ¬ capprox c[3] c[4] ∧ ¬ capprox c[4] c[3].

证明。 (* 在这里填写 *) 已承认。

```

    Find a program cmin that approximates every other program.

```

定义 cmin : com

(* 用":= _your_definition_ ."替换此行 *). 已承认。

定理 cmin_minimal : ∀c, capprox cmin c.

证明。 (* 在这里填写 *) 已承认。

```

    Finally, find a non-trivial property which is preserved by
    program approximation (when going from left to right).

```

定义 zprop (c : com) : Prop

(* 用":= _your_definition_ ."替换此行 *). 已承认。

定理 zprop_preserving : ∀c c',

zprop c → capprox c c' → zprop c'.

证明。 (* 在这里填写 *) 已承认。

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
