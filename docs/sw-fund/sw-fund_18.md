# 霍尔逻辑，第一部分

```

```

Require Import Coq.Bool.Bool。

Require Import Coq.Arith.Arith。

Require Import Coq.Arith.EqNat。

Require Import Coq.omega.Omega。

Require Import Imp。

Require Import Maps.

```

    In the past couple of chapters, we've begun applying the
    mathematical tools developed in the first part of the course to
    studying the theory of a small programming language, Imp.

*   We defined a type of *abstract syntax trees* for Imp, together with an *evaluation relation* (a partial function on states) that specifies the *operational semantics* of programs. 

     The language we defined, though small, captures some of the key features of full-blown languages like C, C++, and Java, including the fundamental notion of mutable state and some common control structures. 

*   We proved a number of *metatheoretic properties* — "meta" in the sense that they are properties of the language as a whole, rather than of particular programs in the language. These included: 

    *   determinism of evaluation 

    *   equivalence of some different ways of writing down the definitions (e.g., functional and relational definitions of arithmetic expression evaluation) 

    *   guaranteed termination of certain classes of programs 

    *   correctness (in the sense of preserving meaning) of a number of useful program transformations 

    *   behavioral equivalence of programs (in the Equiv chapter).

    If we stopped here, we would already have something useful: a set
    of tools for defining and discussing programming languages and
    language features that are mathematically precise, flexible, and
    easy to work with, applied to a set of key properties.  All of
    these properties are things that language designers, compiler
    writers, and users might care about knowing.  Indeed, many of them
    are so fundamental to our understanding of the programming
    languages we deal with that we might not consciously recognize
    them as "theorems."  But properties that seem intuitively obvious
    can sometimes be quite subtle (sometimes also subtly wrong!).

    We'll return to the theme of metatheoretic properties of whole
    languages later in the book when we discuss *types* and *type soundness*.  In this chapter, though, we turn to a different set
    of issues.

    Our goal is to carry out some simple examples of *program verification* — i.e., to use the precise definition of Imp to
    prove formally that particular programs satisfy particular
    specifications of their behavior.  We'll develop a reasoning
    system called *Floyd-Hoare Logic* — often shortened to just
    *Hoare Logic* — in which each of the syntactic constructs of Imp
    is equipped with a generic "proof rule" that can be used to reason
    compositionally about the correctness of programs involving this
    construct.

    Hoare Logic originated in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a multitude of tools that are being used in
    academia and industry to specify and verify real software
    systems. 

    Hoare Logic combines two beautiful ideas: a natural way of
    writing down *specifications* of programs, and a *compositional proof technique* for proving that programs are correct with
    respect to such specifications — where by "compositional" we mean
    that the structure of proofs directly mirrors the structure of the
    programs that they are about. 

    This chapter:

*   A systematic method for reasoning about the correctness of particular programs in Imp

    Goals:

*   a natural notation for *program specifications* and

*   a *compositional* proof technique for program correctness

    Plan:

*   assertions (Hoare Triples)

*   proof rules

*   decorated programs

*   loop invariants

*   examples

```

# 断言

    要谈论程序的规范，第一件事

    需要的是一种对在

    程序执行期间的特定点 — 即，声明

    当执行到达那时，关于内存的当前状态

    点。形式上，一个断言只是一组命题

    由状态索引。

```
Definition Assertion := state → Prop.

```

#### 练习：1 星，可选（断言）

    用英语（或您喜欢的语言）改写以下断言

    自然语言）。

```
Module ExAssertions.
Definition as[1] : Assertion := fun st ⇒ st X = 3.
Definition as[2] : Assertion := fun st ⇒ st X ≤ st Y.
Definition as[3] : Assertion :=
  fun st ⇒ st X = 3 ∨ st X ≤ st Y.
Definition as[4] : Assertion :=
  fun st ⇒ st Z * st Z ≤ st X ∧
            ¬ (((S (st Z)) * (S (st Z))) ≤ st X).
Definition as[5] : Assertion := fun st ⇒ True.
Definition as[6] : Assertion := fun st ⇒ False.
(* FILL IN HERE *)
End ExAssertions.

```

    ☐

    这种写断言的方式可能有点繁重，

    出于两个原因：（1）我们写的每个断言都是

    开始 fun st ⇒；和（2）这个状态 st 是

    我们唯一用来查找断言中变量的方法（我们

    永远不需要谈论两个不同的内存状态

    同时）。为了非正式讨论示例，我们将采用一些

    简化约定：我们会省略初始的 fun st ⇒，和

    我们只写 X 来表示 st X。因此，而不是写

```
      fun st ⇒ (st Z) * (st Z) ≤ m ∧
                ¬ ((S (st Z)) * (S (st Z)) ≤ m)

    we'll write just

```

Z * Z ≤ m ∧ ~((S Z) * (S Z) ≤ m)。

    这个例子还说明了我们将使用的一个约定

    在霍尔逻辑章节中始终：在非正式断言中，

    像{X]，Y 和 Z 这样的大写字母是 Imp 变量，而

    小写字母如 x，y，m 和 n 是普通的 Coq

    变量（类型为 nat）。这就是为什么在从

    从非正式到正式，我们用 st X 替换 X，但保留 m

    单独。

    给定两个断言 P 和 Q，我们说 P *蕴含* Q，

    写作 P ⇾ Q（在 ASCII 中，P ->> Q），如果每当 P

    在某个状态 st 中成立，Q 也成立。

```
Definition assert_implies (P Q : Assertion) : Prop :=
  ∀st, P st → Q st.

Notation "P ⇾ Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

```

    （hoare_spec_scope 注释告诉 Coq 这

    表示不是全局的，而是打算在特定情况下使用

    上下文。Open Scope 告诉 Coq 这是这样一个

    上下文。）

    我们还希望在

    断言：

```
Notation "P ⇿ Q" :=
  (P ⇾ Q ∧ Q ⇾ P) (at level 80) : hoare_spec_scope.

```

# 霍尔三元组

    接下来，我们需要一种对

    命令的行为。

    一般来说，命令的行为是将一个状态转换为

    另一个，因此自然地表达关于命令的声明

    在命令之前和之后为真的断言条件

    执行：

+   “如果命令 c 在满足断言 P 的状态下启动，并且如果 c 最终在某个最终状态中终止，那么这个最终状态将满足断言 Q。”

    这样的声明称为*霍尔三元组*。属性 P 是

    称为 c 的*前置条件*，而 Q 是

    *后置条件*。形��上：

```
Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  ∀st st',
     c / st ⇓ st'  →
     P st  →
     Q st'.

```

    由于我们将大量使用霍尔三元组，因此有用的是

    有一个紧凑的表示法：

```
       {{P}} c {{Q}}.

    (The traditional notation is {P} c {Q}, but single braces
    are already used for other things in Coq.)

```

符号 "{{ P }}  c  {{ Q }}" :=

（hoare_triple P c Q）（在级别 90 处，下一个级别的 c）

：hoare_spec_scope。

```

#### Exercise: 1 star, optional (triples)

    Paraphrase the following Hoare triples in English.

```

1) {{True}} c {{X = 5}}

2) {{X = m}} c {{X = m + 5)}}

3) {{X ≤ Y}} c {{Y ≤ X}}

4) {{True}} c {{False}}

5) {{X = m}}

c

{{Y = real_fact m}}

6) {{True}}

c

{{(Z * Z) ≤ m ∧ ¬ (((S Z) * (S Z)) ≤ m)}}

    ☐

#### 练习：1 星，可选（有效三元组）

    以下哪些霍尔三元组是*有效*的 — 即，这些

    声称的 P、c 和 Q 之间的关系是真实的吗？

```
   1) {{True}} X ::= 5 {{X = 5}}

   2) {{X = 2}} X ::= X + 1 {{X = 3}}

   3) {{True}} X ::= 5; Y ::= 0 {{X = 5}}

   4) {{X = 2 ∧ X = 3}} X ::= 5 {{X = 0}}

   5) {{True}} SKIP {{False}}

   6) {{False}} SKIP {{True}}

   7) {{True}} WHILE True DO SKIP END {{False}}

   8) {{X = 0}}
      WHILE X == 0 DO X ::= X + 1 END
      {{X = 1}}

   9) {{X = 1}}
      WHILE X ≠ 0 DO X ::= X + 1 END
      {{X = 100}}

    ☐ 

    (Note that we're using informal mathematical notations for
   expressions inside of commands, for readability, rather than their
   formal aexp and bexp encodings.  We'll continue doing so
   throughout the chapter.) 

    To get us warmed up for what's coming, here are two simple
   facts about Hoare triples.

```

定理 hoare_post_true：∀(P Q：断言) c，

（∀st，Q st）→

{{P}} c {{Q}}。

    证明。

intros P Q c H. unfold hoare_triple.

intros st st' Heval HP。

应用 H。已证明。

定理 hoare_pre_false：∀(P Q：断言) c，

（∀st, ~(P st)）→

{{P}} c {{Q}}。

    证明。

intros P Q c H. unfold hoare_triple.

intros st st' Heval HP。

在 H 中展开[not](http://coq.inria.fr/library/Coq.Init.Logic.html#not)。将 H 应用于 HP。

反演 HP。已证明。

```

# Proof Rules

    The goal of Hoare logic is to provide a *compositional*
    method for proving the validity of specific Hoare triples.  That
    is, we want the structure of a program's correctness proof to
    mirror the structure of the program itself.  To this end, in the
    sections below, we'll introduce a rule for reasoning about each of
    the different syntactic forms of commands in Imp — one for
    assignment, one for sequencing, one for conditionals, etc. — plus
    a couple of "structural" rules for gluing things together.  We
    will then be able to prove programs correct using these proof
    rules, without ever unfolding the definition of hoare_triple.

```

## 赋值

    赋值的规则是霍尔逻辑中最基本的规则

    证明规则。这是它的工作原理。

    考虑这个有效的霍尔三元组：

```
       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}

    In English: if we start out in a state where the value of Y
    is 1 and we assign Y to X, then we'll finish in a
    state where X is 1.  
    That is, the property of being equal to 1 gets transferred 
    from Y to X. 

    Similarly, in

```

{{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}

    相同的属性（等于一）被转移到

    从右侧的表达式 Y + Z 转移到 X

    赋值。

    更一般地说，如果 a 是*任何*算术表达式，那么

```
       {{ a = 1 }}  X ::= a {{ X = 1 }}

    is a valid Hoare triple. 

    This can be made even more general. To conclude that an
    arbitrary property Q holds after X ::= a, we need to assume
    that Q holds before X ::= a, but *with all occurrences of* X
    replaced by a in Q. This leads to the Hoare rule for
    assignment

```

{{ Q [X ↦ a] }} X ::= a {{ Q }}

    其中“Q [X ↦ a]”发音为“Q 其中 a 被替换

    对于 X”。

    例如，这些是赋值的有效应用

    规则：

```
      {{ (X ≤ 5) [X ↦ X + 1]
         i.e., X + 1 ≤ 5 }}
      X ::= X + 1
      {{ X ≤ 5 }}

      {{ (X = 3) [X ↦ 3]
         i.e., 3 = 3}}
      X ::= 3
      {{ X = 3 }}

      {{ (0 ≤ X ∧ X ≤ 5) [X ↦ 3]
         i.e., (0 ≤ 3 ∧ 3 ≤ 5)}}
      X ::= 3
      {{ 0 ≤ X ∧ X ≤ 5 }}

    To formalize the rule, we must first formalize the idea of
    "substituting an expression for an Imp variable in an assertion."
    That is, given a proposition P, a variable X, and an
    arithmetic expression a, we want to derive another proposition
    P' that is just the same as P except that, wherever P
    mentions X, P' should instead mention a.

    Since P is an arbitrary Coq proposition, we can't directly
    "edit" its text.  Instead, we can achieve the same effect by
    evaluating P in an updated state:

```

定义 assn_sub X a P：断言 :=

fun (st : state) ⇒

P（t_update st X（aeval st a））。

符号“P [ X |-> a ]”：=（assn_sub X a P）（在级别 10 处）。

```

    That is, P [X ↦ a] stands for an assertion — let's call it P' — 
    that is just like P except that, wherever P looks up the 
    variable X in the current state, P' instead uses the value 
    of the expression a. 

    To see how this works, let's calculate what happens with a couple
    of examples.  First, suppose P' is (X ≤ 5) [X ↦ 3] — that
    is, more formally, P' is the Coq expression

```

fun st ⇒

（fun st' ⇒ st' X ≤ 5）

（t_update st X （aeval st （ANum 3））），

    这简化为

```
    fun st ⇒
      (fun st' ⇒ st' X ≤ 5)
      (t_update st X 3)

    and further simplifies to

```

fun st ⇒

((t_update st X 3) X) ≤ 5）

    最后到

```
    fun st ⇒
      (3 ≤ 5).

    That is, P' is the assertion that 3 is less than or equal to
    5 (as expected). 

    For a more interesting example, suppose P' is (X ≤ 5) [X ↦ X+1].  Formally, P' is the Coq expression

```

fun st ⇒

(fun st' ⇒ st' X ≤ 5)

（t_update st X (aeval st (APlus (AId X) (ANum 1))），

    这简化为

```
    fun st ⇒
      (((t_update st X (aeval st (APlus (AId X) (ANum 1))))) X) ≤ 5

    and further simplifies to

```

fun st ⇒

(aeval st (APlus (AId X) (ANum 1))) ≤ 5。

    也就是说，P'是 X+1 最多为 5 的断言。

    现在，使用替换的概念，我们可以给出精确的

    赋值的证明规则：

        |

                        （hoare_asgn）

        |

* * *

        |

                        {{Q [X ↦ a]}} X ::= a {{Q}}

        |

                    |

    我们可以正式证明这个规则确实是有效的。

```
Theorem hoare_asgn : ∀Q X a,
  {{Q [X ↦ a]}} (X ::= a) {{Q}}.

    Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption. Qed.

```

    这是使用这个规则的第一个正式证明。

```
Example assn_sub_example :
  {{(fun st ⇒ st X = 3) [X ↦ ANum 3]}}
  (X ::= (ANum 3))
  {{fun st ⇒ st X = 3}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_asgn. Qed.

```

#### 练习：2 星 M（hoare_asgn_examples）

    翻译这些非正式的霍尔三元组...

```
    1) {{ (X ≤ 5) [X ↦ X + 1] }}
       X ::= X + 1
       {{ X ≤ 5 }}

    2) {{ (0 ≤ X ∧ X ≤ 5) [X ↦ 3] }}
       X ::= 3
       {{ 0 ≤ X ∧ X ≤ 5 }}

    ...into formal statements (use the names assn_sub_ex[1] 
   and assn_sub_ex[2]) and use hoare_asgn to prove them.

```

(* 在这里填写*)

```

    ☐ 

#### Exercise: 2 stars, recommendedM (hoare_asgn_wrong)

    The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems puzzling, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:

           |

                        (hoare_asgn_wrong)  
           |

* * *

           |

                        {{ True }} X ::= a {{ X = a }}
           |

                     |

    Give a counterexample showing that this rule is incorrect and 
    argue informally that it is really a counterexample.  (Hint: 
    The rule universally quantifies over the arithmetic expression 
    a, and your counterexample needs to exhibit an a for which 
    the rule doesn't work.)

```

(* 在这里填写*)

```

    ☐ 

#### Exercise: 3 stars, advanced (hoare_asgn_fwd)

    However, by using a *parameter* m (a Coq number) to remember the 
    original value of X we can define a Hoare rule for assignment 
    that does, intuitively, "work forwards" rather than backwards.

           |

                        (hoare_asgn_fwd)  
           |

* * *

           |

                        {{fun st ⇒ P st ∧ st X = m}}
           |

                     |

                        X ::= a
           |

                     |

                        {{fun st ⇒ P st' ∧ st X = aeval st' a }}
           |

                     |

                        (where st' = t_update st X m)
           |

                     |

    Note that we use the original value of X to reconstruct the
    state st' before the assignment took place. Prove that this rule
    is correct.  (Also note that this rule is more complicated than 
    hoare_asgn.)

```

定理 hoare_asgn_fwd：

（∀{X Y: Type} {f g : X → Y}，

（∀(x: X), f x = g x) →  f = g) →

∀m a P,

{{fun st ⇒ P st ∧ st X = m}}

X ::= a

{{fun st ⇒ P（t_update st X m）

∧ st X = aeval（t_update st X m）a }}。

证明。

(* 在这里填写*) 已承认。

```

    ☐ 

#### Exercise: 2 stars, advanced (hoare_asgn_fwd_exists)

    Another way to define a forward rule for assignment is to
    existentially quantify over the previous value of the assigned
    variable.

           |

                        (hoare_asgn_fwd_exists)  
           |

* * *

           |

                        {{fun st ⇒ P st}}
           |

                     |

                        X ::= a
           |

                     |

                        {{fun st ⇒ ∃m, P (t_update st X m) ∧
           |

                     |

                        st X = aeval (t_update st X m) a }}
           |

                     |

```

定理 hoare_asgn_fwd_exists：

（∀{X Y: Type} {f g : X → Y}，

（∀(x: X), f x = g x) →  f = g) →

∀a P，

{{fun st ⇒ P st}}

X ::= a

{{fun st ⇒ ∃m, P (t_update st X m) ∧

st X = aeval（t_update st X m）a }}。

证明。

intros functional_extensionality a P。

(* 在这里填写*) 已承认。

```

    ☐

```

## 结果

    有时我们从中获得的前提条件和后置条件

    霍尔规则在特定情况下不会完全是我们想要的

    手头的情况 — 它们可能在逻辑上等价，但有一个

    与我们要解决的目标不一致的不同语法形式

    尝试证明，或者它们实际上可能在逻辑上较弱（对于

    前提条件）或更强（对于后置条件）比我们需要的。

    例如，当

```
      {{(X = 3) [X ↦ 3]}} X ::= 3 {{X = 3}},

    follows directly from the assignment rule,

```

{{True}} X ::= 3 {{X = 3}}

    不是。这个三元组是有效的，但它不是

    hoare_asgn 因为 True 和 (X = 3) [X ↦ 3] 不是

    语法上相等的断言。然而，它们在逻辑上是

    *等价*，因此如果一个三元组有效，则另一个必须

    肯定也是如此。我们可以用两个*推论规则*来捕捉这一观察。

    遵循规则：

                        {{P'}} c {{Q}}

        |

                    |

                        P ⇿ P'

        |

                        (hoare_consequence_pre_equiv)

        |

* * *

        |

                        {{P}} c {{Q}}

        |

                    |

    进一步思考这一点，我们可以看到

    加强前置条件或减弱后置条件的

    有效的三元组总是产生另一个有效的三元组。这

    观察由两个*推论规则*捕捉。

                        {{P'}} c {{Q}}

        |

                    |

                        P ⇾ P'

        |

                        (hoare_consequence_pre)

        |

* * *

        |

                        {{P}} c {{Q}}

        |

                    |

                        {{P}} c {{Q'}}

        |

                    |

                        Q' ⇾ Q

        |

                        (hoare_consequence_post)

        |

* * *

        |

                        {{P}} c {{Q}}

        |

                    |

    这里是正式版本：

```
Theorem hoare_consequence_pre : ∀(P P' Q : Assertion) c,
  {{P'}} c {{Q}} →
  P ⇾ P' →
  {{P}} c {{Q}}.

    Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : ∀(P Q Q' : Assertion) c,
  {{P}} c {{Q'}} →
  Q' ⇾ Q →
  {{P}} c {{Q}}.

    Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.

```

    例如，我们可以像这样使用第一个推论规则：

```
                {{ True }} ⇾
                {{ 1 = 1 }}
    X ::= 1
                {{ X = 1 }}

    Or, formally...

```

例 hoare_asgn_example1：

{{fun st ⇒ True}} (X ::= (ANum 1)) {{fun st ⇒ st X = 1}}。

证明。

(* 在课堂上运行 *)

应用 hoare_consequence_pre

使用 (P' := (fun st ⇒ st X = 1) [X ↦ ANum 1])。

应用 hoare_asgn。

intros st H。展开 assn_sub, t_update。简化。一致性。

Qed。

```

    Finally, for convenience in proofs, we can state a combined
    rule of consequence that allows us to vary both the precondition
    and the postcondition at the same time.

                        {{P'}} c {{Q'}}
           |

                     |

                        P ⇾ P'
           |

                     |

                        Q' ⇾ Q
           |

                        (hoare_consequence)  
           |

* * *

           |

                        {{P}} c {{Q}}
           |

                     |

```

定理 hoare_consequence : ∀(P P' Q Q' : Assertion) c，

{{P'}} c {{Q'}} →

P ⇾ P' →

Q' ⇾ Q →

{{P}} c {{Q}}。

    证明。

intros P P' Q Q' c Hht HPP' HQ'Q。

使用 [hoare_consequence_pre](https://Hoare.html#hoare_consequence_pre) 应用 (P' := P')。

使用 [hoare_consequence_post](https://Hoare.html#hoare_consequence_post) 应用 (Q' := Q')。

假设。假设。假设。Qed。

```

## Digression: The eapply Tactic

    This is a good moment to take another look at the eapply tactic,
    which we introduced briefly in the Auto chapter.

    We had to write "with (P' := ...)" explicitly in the proof of
    hoare_asgn_example1 and hoare_consequence above, to make sure
    that all of the metavariables in the premises to the
    hoare_consequence_pre rule would be set to specific
    values.  (Since P' doesn't appear in the conclusion of
    hoare_consequence_pre, the process of unifying the conclusion
    with the current goal doesn't constrain P' to a specific
    assertion.)

    This is annoying, both because the assertion is a bit long and
    also because, in hoare_asgn_example1, the very next thing we are
    going to do — applying the hoare_asgn rule — will tell us
    exactly what it should be!  We can use eapply instead of apply
    to tell Coq, essentially, "Be patient: The missing part is going
    to be filled in later in the proof."

```

例 hoare_asgn_example1'：

{{fun st ⇒ True}}

(X ::= (ANum 1))

{{fun st ⇒ st X = 1}}。

证明。

eapply hoare_consequence_pre。

应用 hoare_asgn。

intros st H。一致性。Qed。

```

    In general, eapply H tactic works just like apply H except
    that, instead of failing if unifying the goal with the conclusion
    of H does not determine how to instantiate all of the variables
    appearing in the premises of H, eapply H will replace these
    variables with *existential variables* (written ?nnn), which
    function as placeholders for expressions that will be
    determined (by further unification) later in the proof. 

    In order for Qed to succeed, all existential variables need to
    be determined by the end of the proof. Otherwise Coq
    will (rightly) refuse to accept the proof. Remember that the Coq
    tactics build proof objects, and proof objects containing
    existential variables are not complete.

```

引理 silly1 : ∀(P : nat → nat → Prop) (Q : nat → Prop),

(∀x y : nat, P x y) →

(∀x y : nat, P x y → Q x) →

Q 42。

证明。

intros P Q HP HQ。eapply HQ。应用 HP。

```

    Coq gives a warning after apply HP.  (The warnings look
    different between Coq 8.4 and Coq 8.5\.  In 8.4, the warning says
    "No more subgoals but non-instantiated existential variables."  In
    8.5, it says "All the remaining goals are on the shelf," meaning
    that we've finished all our top-level proof obligations but along
    the way we've put some aside to be done later, and we have not
    finished those.)  Trying to close the proof with Qed gives an
    error.

```

中止。

```

    An additional constraint is that existential variables cannot be
    instantiated with terms containing ordinary variables that did not
    exist at the time the existential variable was created.  (The
    reason for this technical restriction is that allowing such
    instantiation would lead to inconsistency of Coq's logic.)

```

引理 silly2：

∀(P : nat → nat → Prop) (Q : nat → Prop)，

(∃y, P 42 y) →

(∀x y : nat, P x y → Q x) →

Q 42。

证明。

intros P Q HP HQ。eapply HQ。破坏 HP 为 [y HP']。

```

    Doing apply HP' above fails with the following error:

```

错误：无法将"?175"统一为"y"。

    在这种情况下有一个简单的解决方法：在*之前*执行破坏 HP

    执行 eapply HQ。

```
Abort.

Lemma silly2_fixed :
  ∀(P : nat → nat → Prop) (Q : nat → Prop),
  (∃y, P 42 y) →
  (∀x y : nat, P x y → Q x) →
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP'].
  eapply HQ. apply HP'.
Qed.

```

    最后一步中的 apply HP' 统一了存在变量

    在目标中的变量 y。

    注意，在这种情况下假设策略不起作用，因为

    它无法处理存在变量。然而，Coq 也

    提供了一个 eassumption 策略，如果其中一个解决目标

    前提与目标匹配直到存在变量的实例化

    变量。我们可以使用它来代替 apply HP'。

```
Lemma silly2_eassumption : ∀(P : nat → nat → Prop) (Q : nat → Prop),
  (∃y, P 42 y) →
  (∀x y : nat, P x y → Q x) →
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

```

#### 练习：2 星 M (hoare_asgn_examples_2)

    翻译这些非正式的 Hoare 三元组...

```
       {{ X + 1 ≤ 5 }}  X ::= X + 1  {{ X ≤ 5 }}
       {{ 0 ≤ 3 ∧ 3 ≤ 5 }}  X ::= 3  {{ 0 ≤ X ∧ X ≤ 5 }}

    ...into formal statements (name them assn_sub_ex[1]' and 
   assn_sub_ex[2]') and use hoare_asgn and hoare_consequence_pre 
   to prove them.

```

(* 在这里填写 *)

```

    ☐

```

## 跳过

    由于 SKIP 不改变状态，它保留任何

    属性 P：

        |

                        (hoare_skip)

        |

* * *

        |

                        {{ P }} SKIP {{ P }}

        |

                    |

```
Theorem hoare_skip : ∀P,
     {{P}} SKIP {{P}}.

    Proof.
  intros P st st' H HP. inversion H. subst.
  assumption. Qed.

```

## 顺序

    更有趣的是，如果命令 c[1] 接受任何状态，其中

    P 成立到一个状态，其中 Q 成立，如果 c[2] 接受任何

    Q 成立到一个状态，其中 R 成立，然后执行 c[1]

    然后 c[2] 将接受任何状态，其中 P 成立到一个

    其中 R 成立：

                        {{ P }} c[1] {{ Q }}

        |

                    |

                        {{ Q }} c[2] {{ R }}

        |

                        (hoare_seq)

        |

* * *

        |

                        {{ P }} c[1];;c[2] {{ R }}

        |

                    |

```
Theorem hoare_seq : ∀P Q R c[1] c[2],
     {{Q}} c[2] {{R}} →
     {{P}} c[1] {{Q}} →
     {{P}} c[1];;c[2] {{R}}.

    Proof.
  intros P Q R c[1] c[2] H[1] H[2] st st' H[12] Pre.
  inversion H[12]; subst.
  apply (H[1] st'0 st'); try assumption.
  apply (H[2] st st'0); assumption. Qed.

```

    注意，在形式化规则 hoare_seq 中，前提是

    以倒序给出（c[2] 在 c[1] 之前）。这与

    在许多情况下，我们将看到信息的自然流动

    使用该规则，因为构造 Hoare 逻辑的自然方式

    证明是从程序的末尾开始（使用最终

    后置条件）并将后置条件向后推移通过命令

    直到我们到达开头。

    非正式地，使用序列化显示证明的一种好方法

    规则是一个“装饰程序”，其中间断言

    Q 写在 c[1] 和 c[2] 之间：

```
      {{ a = n }}
    X ::= a;;
      {{ X = n }}    <---- decoration for Q
    SKIP
      {{ X = n }}

    Here's an example of a program involving both assignment and
    sequencing.

```

例子 hoare_asgn_example3 : ∀a n,

{{fun st ⇒ aeval st a = n}}

(X ::= a;; SKIP)

{{fun st ⇒ st X = n}}.

证明。

intros a n. eapply hoare_seq.

- (* seq 的右部分 *)

应用 hoare_skip.

- (* seq 的左部分 *)

eapply hoare_consequence_pre. apply hoare_asgn.

intros st H. subst. reflexivity.

Qed.

```

    We typically use hoare_seq in conjunction with
    hoare_consequence_pre and the eapply tactic, as in this
    example. 

#### Exercise: 2 stars, recommended (hoare_asgn_example4)

    Translate this "decorated program" into a formal proof:

```

{{ True }} ⇾

{{ 1 = 1 }}

X ::= 1;;

{{ X = 1 }} ⇾

{{ X = 1 ∧ 2 = 2 }}

Y ::= 2

{{ X = 1 ∧ Y = 2 }}

    （注意使用“⇾”装饰，每个标记一个使用

hoare_consequence_pre.)

```
Example hoare_asgn_example4 :
  {{fun st ⇒ True}} (X ::= (ANum 1);; Y ::= (ANum 2))
  {{fun st ⇒ st X = 1 ∧ st Y = 2}}.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星（swap_exercise）

    编写一个 Imp 程序 c，交换 X 和 Y 的值，并

    显示它满足以下规范：

```
      {{X ≤ Y}} c {{Y ≤ X}}

    Your proof should not need to use unfold hoare_triple.

```

定义 swap_program : com

(* 用“:= _your_definition_ .” 替换此行 *). Admitted.

定理 swap_exercise :

{{fun st ⇒ st X ≤ st Y}}

swap_program

{{fun st ⇒ st Y ≤ st X}}.

证明。

(* 在此填写 *） Admitted.

```

    ☐ 

#### Exercise: 3 starsM (hoarestate1)

    Explain why the following proposition can't be proven:

```

∀(a : aexp) (n : nat),

{{fun st ⇒ aeval st a = n}}

(X ::= (ANum 3);; Y ::= a)

{{fun st ⇒ st Y = n}}。

```
(* FILL IN HERE *)

```

    ☐

```

## Conditionals

    What sort of rule do we want for reasoning about conditional
    commands?  

    Certainly, if the same assertion Q holds after executing 
    either of the branches, then it holds after the whole conditional.  
    So we might be tempted to write:

                        {{P}} c[1] {{Q}}
           |

                     |

                        {{P}} c[2] {{Q}}
           |

           |

* * *

           |

                        {{P}} IFB b THEN c[1] ELSE c[2] {{Q}}
           |

                     |

    However, this is rather weak. For example, using this rule,
   we cannot show 

```

{{ True }}

IFB X == 0

THEN Y ::= 2

ELSE Y ::= X + 1

FI

{{ X ≤ Y }}

    因为规则没有告诉我们关于

赋值发生在“then”和“else”分支中。

    幸运的是，我们可以说得更加精确。在

    “then”分支，我们知道布尔表达式 b 评估为

    真，并且在“else”分支中，我们知道它的值为假。

    使这些信息在规则的前提中可用给出

    在推理行为时给我们更多信息。

    c[1] 和 c[2] 的（即，它们建立

    后置条件 Q）。

                        {{P ∧  b}} c[1] {{Q}}

        |

                    |

                        {{P ∧ ~b}} c[2] {{Q}}

        |

                        (hoare_if)

        |

* * *

        |

                        {{P}} IFB b THEN c[1] ELSE c[2] FI {{Q}}

        |

                    |

    要正式解释这个规则，我们需要做一些工作。

    严格来说，我们写的断言 P ∧ b 是

    一个断言和一个布尔表达式的合取——即，它

    不会通过类型检查。为了修复这个问题，我们需要一种正式的方式

    将任何 bexp b “提升”为一个断言。我们将 bassn b 写为

    断言“布尔表达式 b 评估为真（在

    给定的状态）。”

```
Definition bassn b : Assertion :=
  fun st ⇒ (beval st b = true).

```

    关于 bassn 的一些有用事实：

```
Lemma bexp_eval_true : ∀b st,
  beval st b = true → (bassn b) st.

    Proof.
  intros b st Hbe.
  unfold bassn. assumption. Qed.

Lemma bexp_eval_false : ∀b st,
  beval st b = false → ¬ ((bassn b) st).

    Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite → contra in Hbe. inversion Hbe. Qed.

```

    现在我们可以为条件语句形式化 Hoare 证明规则

    并证明它的正确性。

```
Theorem hoare_if : ∀P Q b c[1] c[2],
  {{fun st ⇒ P st ∧ bassn b st}} c[1] {{Q}} →
  {{fun st ⇒ P st ∧ ~(bassn b st)}} c[2] {{Q}} →
  {{P}} (IFB b THEN c[1] ELSE c[2] FI) {{Q}}.

    Proof.
  intros P Q b c[1] c[2] HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
             apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

```

### 例子

    这是一个正式证明，证明我们用来激励的程序

    规则满足我们给定的规范。

```
Example if_example :
    {{fun st ⇒ True}}
  IFB (BEq (AId X) (ANum 0))
    THEN (Y ::= (ANum 2))
    ELSE (Y ::= APlus (AId X) (ANum 1))
  FI
    {{fun st ⇒ st X ≤ st Y}}.

    Proof.
  (* WORKED IN CLASS *)
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros st [_ H].
    apply [beq_nat_true](http://coq.inria.fr/library/Coq.Arith.EqNat.html#beq_nat_true) in H.
    rewrite H. omega.
  - (* Else *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, t_update, assert_implies.
    simpl; intros st _. omega.
    Qed.

```

#### 练习：2 星（if_minus_plus）

    使用 hoare_if 证明以下 hoare 三元组。不要

    使用 unfold hoare_triple。

```
Theorem if_minus_plus :
  {{fun st ⇒ True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st ⇒ st Y = st X + st Z}}.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

### Exercise: One-sided conditionals

#### Exercise: 4 starsM (if1_hoare)

    In this exercise we consider extending Imp with "one-sided
    conditionals" of the form IF[1] b THEN c FI. Here b is a
    boolean expression, and c is a command. If b evaluates to
    true, then command c is evaluated. If b evaluates to
    false, then IF[1] b THEN c FI does nothing.

    We recommend that you do this exercise before the ones that
    follow, as it should help solidify your understanding of the
    material. 

    The first step is to extend the syntax of commands and introduce
    the usual notations.  (We've done this for you.  We use a separate
    module to prevent polluting the global name space.)

```

模块 If[1]。

Inductive com : Type :=

| CSkip : com

| CAss : id → aexp → com

| CSeq : com → com → com

| CIf : bexp → com → com → com

| CWhile : bexp → com → com

| CIf1 : bexp → com → com。

Notation "'SKIP'" :=

CSkip。

Notation "c1 ;; c2" :=

(CSeq c[1] c[2]) (at level 80, right associativity)。

Notation "X '::=' a" :=

(CAss X a) (at level 60)。

Notation "'WHILE' b 'DO' c 'END'" :=

(CWhile b c) (at level 80, right associativity)。

Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=

(CIf e[1] e[2] e[3]) (at level 80, right associativity).

Notation "'IF1' b 'THEN' c 'FI'" :=

(CIf1 b c) (at level 80, right associativity)。

```

    Next we need to extend the evaluation relation to accommodate
    IF[1] branches.  This is for you to do... What rule(s) need to be
    added to ceval to evaluate one-sided conditionals?

```

Reserved Notation "c1 '/' st '⇓' st'" (at level 40, st at level 39).

Inductive ceval : com → state → state → Prop :=

| E_Skip : ∀st : state, SKIP / st ⇓ st

| E_Ass : ∀(st : state) (a[1] : aexp) (n : nat) (X : id),

aeval st a[1] = n → (X ::= a[1]) / st ⇓ t_update st X n

| E_Seq : ∀(c[1] c[2] : com) (st st' st'' : state),

c[1] / st ⇓ st' → c[2] / st' ⇓ st'' → (c[1] ;; c[2]) / st ⇓ st''

| E_IfTrue : ∀(st st' : state) (b[1] : bexp) (c[1] c[2] : com),

beval st b[1] = true →

c[1] / st ⇓ st' → (IFB b[1] THEN c[1] ELSE c[2] FI) / st ⇓ st'

| E_IfFalse : ∀(st st' : state) (b[1] : bexp) (c[1] c[2] : com),

beval st b[1] = false →

c[2] / st ⇓ st' → (IFB b[1] THEN c[1] ELSE c[2] FI) / st ⇓ st'

| E_WhileEnd : ∀(b[1] : bexp) (st : state) (c[1] : com),

beval st b[1] = false → (WHILE b[1] DO c[1] END) / st ⇓ st

| E_WhileLoop : ∀(st st' st'' : state) (b[1] : bexp) (c[1] : com),

beval st b[1] = true →

c[1] / st ⇓ st' →

(WHILE b[1] DO c[1] END) / st' ⇓ st'' →

(WHILE b[1] DO c[1] END) / st ⇓ st''

(* 在此处填写 *)

where "c1 '/' st '⇓' st'" := (ceval c[1] st st')。

```

    Now we repeat (verbatim) the definition and notation of Hoare triples.

```

定义 hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=

∀st st'，

c / st ⇓ st'  →

P st  →

Q st'。

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)

(at level 90, c at next level)

: hoare_spec_scope。

```

    Finally, we (i.e., you) need to state and prove a theorem,
    hoare_if[1], that expresses an appropriate Hoare logic proof rule
    for one-sided conditionals. Try to come up with a rule that is
    both sound and as precise as possible.

```

(* 在此处填写 *)

```

    For full credit, prove formally hoare_if1_good that your rule is
    precise enough to show the following valid Hoare triple:

```

{{ X + Y = Z }}

IF[1] Y ≠ 0 THEN

X ::= X + Y

FI

{{ X = Z }}

    提示：你对这个三元组的证明可能需要使用其他证明

    也是规则。因为我们是在一个单独的模块中工作，你会

    需要在此处复制你认为必要的规则。

```
Lemma hoare_if1_good :
  {{ fun st ⇒ st X + st Y = st Z }}
  IF[1] BNot (BEq (AId Y) (ANum 0)) THEN
    X ::= APlus (AId X) (AId Y)
  FI
  {{ fun st ⇒ st X = st Z }}.
Proof. (* FILL IN HERE *) Admitted.

End If[1].

```

    ☐

```

## Loops

    Finally, we need a rule for reasoning about while loops. 

    Suppose we have a loop

```

WHILE b DO c END

    而我们想要找到一个前置条件 P 和一个后置条件

    Q，使得

```
      {{P}} WHILE b DO c END {{Q}}

    is a valid triple. 

    First of all, let's think about the case where b is false at the
    beginning — i.e., let's assume that the loop body never executes
    at all.  In this case, the loop behaves like SKIP, so we might
    be tempted to write: 

```

{{P}} WHILE b DO c END {{P}}。

    但是，正如我们上面对条件语句所述，我们知道一个

    结尾处再多一点 —— 不仅仅是 P，还有事实

    在当前状态下 b 是 false。所以我们可以丰富

    将后置条件稍微修改一下：

```
      {{P}} WHILE b DO c END {{P ∧ ¬b}}

    What about the case where the loop body *does* get executed?
    In order to ensure that P holds when the loop finally
    exits, we certainly need to make sure that the command c
    guarantees that P holds whenever c is finished.
    Moreover, since P holds at the beginning of the first
    execution of c, and since each execution of c
    re-establishes P when it finishes, we can always assume
    that P holds at the beginning of c.  This leads us to the
    following rule: 

                        {{P}} c {{P}}
           |

           |

* * *

           |

                        {{P}} WHILE b DO c END {{P ∧ ~b}}
           |

                     |

    This is almost the rule we want, but again it can be improved a
    little: at the beginning of the loop body, we know not only that
    P holds, but also that the guard b is true in the current
    state.  This gives us a little more information to use in
    reasoning about c (showing that it establishes the invariant by
    the time it finishes).  This gives us the final version of the
    rule:

                        {{P ∧ b}} c {{P}}
           |

                        (hoare_while)  
           |

* * *

           |

                        {{P}} WHILE b DO c END {{P ∧ ~b}}
           |

                     |

    The proposition P is called an *invariant* of the loop.

```

Lemma hoare_while : ∀P b c，

{{fun st ⇒ P st ∧ bassn b st}} c {{P}} →

{{P}} WHILE b DO c END {{fun st ⇒ P st ∧ ¬ (bassn b st)}}。

    证明。

引入 P b c Hhoare st st' He HP。

(* 就像我们以前见过的那样，我们需要通过对 He 的归纳推理      进行推理，因为，在“继续循环”情况下，其假设      谈论整个循环而不仅仅是 c。*)

记住 (WHILE b DO c END) 作为 wcom eqn:Heqwcom。

归纳 He;

尝试（反转 Heqwcom）; 替换; 清除 Heqwcom。

- (* E_WhileEnd *)

分割。假设。应用 bexp_eval_false。假设。

- (* E_WhileLoop *)

应用 IHHe2。一致性。

应用 (Hhoare st st')。假设。

分割。假设。应用 bexp_eval_true。假设。

    结论。

```

    One subtlety in the terminology is that calling some assertion P
    a "loop invariant" doesn't just mean that it is preserved by the
    body of the loop in question (i.e., {{P}} c {{P}}, where c is
    the loop body), but rather that P *together with the fact that the loop's guard is true* is a sufficient precondition for c to
    ensure P as a postcondition.

    This is a slightly (but significantly) weaker requirement.  For
    example, if P is the assertion X = 0, then P *is* an
    invariant of the loop

```

WHILE X = 2 DO X := 1 END

    尽管很明显 *不是* 被循环体保留的

    循环。

```
Example while_example :
    {{fun st ⇒ st X ≤ 3}}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
    {{fun st ⇒ st X = 3}}.

    Proof.
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
    intros st [H[1] H[2]]. apply [leb_complete](http://coq.inria.fr/library/Coq.Arith.Compare_dec.html#leb_complete) in H[2]. omega.
  unfold bassn, assert_implies. intros st [Hle Hb].
    simpl in Hb. destruct ([leb](http://coq.inria.fr/library/Coq.Arith.Compare_dec.html#leb) (st X) 2) eqn : Heqle.
    exfalso. apply Hb; reflexivity.
    apply [leb_iff_conv](http://coq.inria.fr/library/Coq.Arith.Compare_dec.html#leb_iff_conv) in Heqle. omega.
    Qed.

```

    我们可以使用 WHILE 规则来证明以下 Hoare 三元组...

```
Theorem always_loop_hoare : ∀P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.

    Proof.
  (* WORKED IN CLASS *)
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state ⇒ [True](http://coq.inria.fr/library/Coq.Init.Logic.html#True)).
  eapply hoare_consequence_post.
  apply hoare_while.
  - (* Loop body preserves invariant *)
    apply hoare_post_true. intros st. apply [I](http://coq.inria.fr/library/Coq.Init.Logic.html#I).
  - (* Loop invariant and negated guard imply postcondition *)
    simpl. intros st [Hinv Hguard].
    exfalso. apply Hguard. reflexivity.
  - (* Precondition implies invariant *)
    intros st H. constructor. Qed.

```

    当然，如果我们记得这一点，这个结果就不足为奇

    hoare_triple 的定义断言后条件

    只有当命令终止时才能成立。如果命令

    不终止，我们可以证明任何我们想要的关于

    后条件。

    只谈论终止命令的 Hoare 规则是

    常常被描述为“部分”正确性的逻辑。这是

    还有可能为“完全”正确性制定 Hoare 规则，即

    构建在命令终止的事实之上。然而，在这个

    当然我们只会谈论部分正确性。

```

### Exercise: REPEAT

#### Exercise: 4 stars, advancedM (hoare_repeat)

    In this exercise, we'll add a new command to our language of
    commands: REPEAT c UNTIL a END. You will write the
    evaluation rule for repeat and add a new Hoare rule to the
    language for programs involving it.  (You may recall that the
    evaluation rule is given in an example in the Auto chapter.
    Try to figure it out yourself here rather than peeking.)

```

模块 RepeatExercise。

诱导 com : Type :=

| CSkip : com

| CAsgn : id → aexp → com

| CSeq : com → com → com

| CIf : bexp → com → com → com

| CWhile : bexp → com → com

| CRepeat : com → bexp → com。

```

    REPEAT behaves like WHILE, except that the loop guard is
    checked *after* each execution of the body, with the loop
    repeating as long as the guard stays *false*.  Because of this,
    the body will always execute at least once.

```

注释 "'SKIP'" :=

CSkip。

注释 "c1 ;; c2" :=

(CSeq c[1] c[2]) (at level 80, right associativity).

注释 "X '::=' a" :=

(CAsgn X a) (at level 60).

注释 "'WHILE' b 'DO' c 'END'" :=

(CWhile b c) (at level 80, right associativity).

注释 "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=

(CIf e[1] e[2] e[3]) (at level 80, right associativity).

注释 "'REPEAT' e1 'UNTIL' b2 'END'" :=

(CRepeat e[1] b[2]) (at level 80, right associativity).

```

    Add new rules for REPEAT to ceval below.  You can use the rules
    for WHILE as a guide, but remember that the body of a REPEAT
    should always execute at least once, and that the loop ends when
    the guard becomes true.  Then update the ceval_cases tactic to
    handle these added cases.

```

诱导 ceval : state → com → state → Prop :=

| E_Skip : ∀st,

ceval st SKIP st

| E_Ass  : ∀st a[1] n X,

aeval st a[1] = n →

ceval st (X ::= a[1]) (t_update st X n)

| E_Seq : ∀c[1] c[2] st st' st'',

ceval st c[1] st' →

ceval st' c[2] st'' →

ceval st (c[1] ;; c[2]) st''

| E_IfTrue : ∀st st' b[1] c[1] c[2],

beval st b[1] = true →

ceval st c[1] st' →

ceval st (IFB b[1] THEN c[1] ELSE c[2] FI) st'

| E_IfFalse : ∀st st' b[1] c[1] c[2],

beval st b[1] = false →

ceval st c[2] st' →

ceval st (IFB b[1] THEN c[1] ELSE c[2] FI) st'

| E_WhileEnd : ∀b[1] st c[1],

beval st b[1] = false →

ceval st (WHILE b[1] DO c[1] END) st

| E_WhileLoop : ∀st st' st'' b[1] c[1],

beval st b[1] = true →

ceval st c[1] st' →

ceval st' (WHILE b[1] DO c[1] END) st'' →

ceval st (WHILE b[1] DO c[1] END) st''

(* 填写这里 *)

。

```

    A couple of definitions from above, copied here so they use the
    new ceval.

```

注释 "c1 '/' st '⇓' st'" := (ceval st c[1] st')

(at level 40, st at level 39).

定义 hoare_triple (P:Assertion) (c:com) (Q:Assertion)

: Prop :=

∀st st', (c / st ⇓ st') → P st → Q st'。

注释 "{{ P }}  c  {{ Q }}" :=

(hoare_triple P c Q) (at level 90, c at next level).

```

    To make sure you've got the evaluation rules for REPEAT right,
    prove that ex1_repeat evaluates correctly.

```

定义 ex1_repeat :=

重复

X ::= ANum 1;;

Y ::= APlus (AId Y) (ANum 1)

UNTIL (BEq (AId X) (ANum 1)) END。

定理 ex1_repeat_works：

ex1_repeat / empty_state ⇓

t_update (t_update empty_state X 1) Y 1.

证明。

(*填写这里*) 已证明。

```

    Now state and prove a theorem, hoare_repeat, that expresses an
    appropriate proof rule for repeat commands.  Use hoare_while
    as a model, and try to make your rule as precise as possible.

```

(*填写这里*)

```

    For full credit, make sure (informally) that your rule can be used
    to prove the following valid Hoare triple:

```

{{ X > 0 }}

重复

Y ::= X;;

X ::= X - 1

直到 X = 0 结束

{{ X = 0 ∧ Y > 0 }}

```
End RepeatExercise.

```

    ☐

```

# Summary

    So far, we've introduced Hoare Logic as a tool for reasoning about
    Imp programs.  In the reminder of this chapter we'll explore a
    systematic way to use Hoare Logic to prove properties about
    programs. The rules of Hoare Logic are:

           |

                        (hoare_asgn)  
           |

* * *

           |

                        {{Q [X ↦ a]}} X::=a {{Q}}
           |

                     |

           |

                        (hoare_skip)  
           |

* * *

           |

                        {{ P }} SKIP {{ P }}
           |

                     |

                        {{ P }} c[1] {{ Q }}
           |

                     |

                        {{ Q }} c[2] {{ R }}
           |

                        (hoare_seq)  
           |

* * *

           |

                        {{ P }} c[1];;c[2] {{ R }}
           |

                     |

                        {{P ∧  b}} c[1] {{Q}}
           |

                     |

                        {{P ∧ ~b}} c[2] {{Q}}
           |

                        (hoare_if)  
           |

* * *

           |

                        {{P}} IFB b THEN c[1] ELSE c[2] FI {{Q}}
           |

                     |

                        {{P ∧ b}} c {{P}}
           |

                        (hoare_while)  
           |

* * *

           |

                        {{P}} WHILE b DO c END {{P ∧ ~b}}
           |

                     |

                        {{P'}} c {{Q'}}
           |

                     |

                        P ⇾ P'
           |

                     |

                        Q' ⇾ Q
           |

                        (hoare_consequence)  
           |

* * *

           |

                        {{P}} c {{Q}}
           |

                     |

    In the next chapter, we'll see how these rules are used to prove
    that programs satisfy specifications of their behavior.

```

# 附加练习

#### 练习：3 颗星（himp_hoare）

    在这个练习中，我们将为 HAVOC 命令推导证明规则

    我们在上一章中学习了的命令。

    首先，我们将这项工作放在一个单独的模块中，并回顾一下

    Himp 命令的语法和大步语义。

```
Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com
  | CHavoc : id → com.

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c[1] c[2]) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e[1] e[2] e[3]) (at level 80, right associativity).
Notation "'HAVOC' X" := (CHavoc X) (at level 60).

Reserved Notation "c1 '/' st '⇓' st'" (at level 40, st at level 39).

Inductive ceval : com → state → state → Prop :=
  | E_Skip : ∀st : state, SKIP / st ⇓ st
  | E_Ass : ∀(st : state) (a[1] : aexp) (n : nat) (X : id),
            aeval st a[1] = n → (X ::= a[1]) / st ⇓ t_update st X n
  | E_Seq : ∀(c[1] c[2] : com) (st st' st'' : state),
            c[1] / st ⇓ st' → c[2] / st' ⇓ st'' → (c[1] ;; c[2]) / st ⇓ st''
  | E_IfTrue : ∀(st st' : state) (b[1] : bexp) (c[1] c[2] : com),
               beval st b[1] = true →
               c[1] / st ⇓ st' → (IFB b[1] THEN c[1] ELSE c[2] FI) / st ⇓ st'
  | E_IfFalse : ∀(st st' : state) (b[1] : bexp) (c[1] c[2] : com),
                beval st b[1] = false →
                c[2] / st ⇓ st' → (IFB b[1] THEN c[1] ELSE c[2] FI) / st ⇓ st'
  | E_WhileEnd : ∀(b[1] : bexp) (st : state) (c[1] : com),
                 beval st b[1] = false → (WHILE b[1] DO c[1] END) / st ⇓ st
  | E_WhileLoop : ∀(st st' st'' : state) (b[1] : bexp) (c[1] : com),
                  beval st b[1] = true →
                  c[1] / st ⇓ st' →
                  (WHILE b[1] DO c[1] END) / st' ⇓ st'' →
                  (WHILE b[1] DO c[1] END) / st ⇓ st''
  | E_Havoc : ∀(st : state) (X : id) (n : nat),
              (HAVOC X) / st ⇓ t_update st X n

  where "c1 '/' st '⇓' st'" := (ceval c[1] st st').

```

    Himp 三元组的定义与以前完全相同。

```
Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  ∀st st', c / st ⇓ st' → P st → Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.

```

    通过定义以下 HAVOC 命令的 Hoare 规则来完成以下任务

    havoc_pre，并证明得到的规则是正确的。

```
Definition havoc_pre (X : id) (Q : Assertion) : Assertion 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem hoare_havoc : ∀(Q : Assertion) (X : id),
  {{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof.
  (* FILL IN HERE *) Admitted.

End Himp.

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
