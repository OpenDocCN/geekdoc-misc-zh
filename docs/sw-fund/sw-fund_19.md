# Hoare2Hoare 逻辑，第二部分

```

```

Require Import Coq.Bool.Bool.

Require Import Coq.Arith.Arith.

Require Import Coq.Arith.EqNat.

Require Import Coq.omega.Omega.

Require Import Maps.

Require Import Imp.

Require Import Hoare.

```

# Decorated Programs

 The beauty of Hoare Logic is that it is *compositional*: the
    structure of proofs exactly follows the structure of programs.
    This suggests that we can record the essential ideas of a proof
    informally (leaving out some low-level calculational details) by
    decorating a program with appropriate assertions on each of its
    commands.  Such a *decorated program* carries with it
    an (informal) proof of its own correctness.

    For example, consider the program: 

```

X ::= m;;

Z ::= p;

WHILE X ≠ 0 DO

Z ::= Z - 1;;

X ::= X - 1

END

```

   (Note the *parameters* m and p, which stand for
   fixed-but-arbitrary numbers.  Formally, they are simply Coq
   variables of type nat.)
 One possible specification for this program: 

```

{{ True }}

X ::= m;;

Z ::= p;

WHILE X ≠ 0 DO

Z ::= Z - 1;;

X ::= X - 1

END

{{ Z = p - m }}

```

 Finally, here is a decorated version of the program, embodying a
    proof of this specification: 

```

{{ True }} ⇾

{{ m = m }}

X ::= m;;

{{ X = m }} ⇾

{{ X = m ∧ p = p }}

Z ::= p;

{{ X = m ∧ Z = p }} ⇾

{{ Z - X = p - m }}

WHILE X ≠ 0 DO

{{ Z - X = p - m ∧ X ≠ 0 }} ⇾

{{ (Z - 1) - (X - 1) = p - m }}

Z ::= Z - 1;;

{{ Z - (X - 1) = p - m }}

X ::= X - 1

{{ Z - X = p - m }}

END

{{ Z - X = p - m ∧ ¬ (X ≠ 0) }} ⇾ {{ Z = p - m }}

```

 Concretely, a decorated program consists of the program text
    interleaved with assertions (either a single assertion or possibly
    two assertions separated by an implication).  To check that a
    decorated program represents a valid proof, we check that each
    individual command is *locally consistent* with its nearby
    assertions in the following sense: 

*   SKIP is locally consistent if its precondition and
          postcondition are the same:

    ```

    {{ P }} SKIP {{ P }}

    ```

*   The sequential composition of c[1] and c[2] is locally
          consistent (with respect to assertions P and R) if c[1] is
          locally consistent (with respect to P and Q) and c[2] is
          locally consistent (with respect to Q and R):

    ```

    {{ P }} c[1];; {{ Q }} c[2] {{ R }}

    ```

*   An assignment is locally consistent if its precondition is the
          appropriate substitution of its postcondition:

    ```

    {{ P [X ↦ a] }}

    X ::= a

    {{ P }}

    ```

*   A conditional is locally consistent (with respect to assertions
          P and Q) if the assertions at the top of its "then" and
          "else" branches are exactly P ∧ b and P ∧ ¬b and if its
          "then" branch is locally consistent (with respect to P ∧ b
          and Q) and its "else" branch is locally consistent (with
          respect to P ∧ ¬b and Q):

    ```

    {{ P }}

    IFB b THEN

    {{ P ∧ b }}

    c[1]

    {{ Q }}

    ELSE

    {{ P ∧ ¬b }}

    c[2]

    {{ Q }}

    FI

    {{ Q }}

    ```

*   A while loop with precondition P is locally consistent if its
          postcondition is P ∧ ¬b, if the pre- and postconditions of
          its body are exactly P ∧ b and P, and if its body is
          locally consistent:

    ```

    {{ P }}

    WHILE b DO

    {{ P ∧ b }}

    c[1]

    {{ P }}

    END

    {{ P ∧ ¬b }}

    ```

*   A pair of assertions separated by ⇾ is locally consistent if
          the first implies the second:

    ```

    {{ P }} ⇾

    {{ P' }}

    ```

          This corresponds to the application of hoare_consequence and
          is the only place in a decorated program where checking whether
          decorations are correct is not fully mechanical and syntactic,
          but rather may involve logical and/or arithmetic reasoning. 

 The above essentially describes a procedure for *verifying*
    the correctness of a given proof involves checking that every
    single command is locally consistent with the accompanying
    assertions.  If we are instead interested in *finding* a proof for
    a given specification, we need to discover the right assertions.
    This can be done in an almost mechanical way, with the exception
    of finding loop invariants, which is the subject of the next
    section.  In the remainder of this section we explain in detail
    how to construct decorations for several simple programs that
    don't involve non-trivial loop invariants. 

```

## 例子：使用加法和减法交换

这是一个使用加法和减法交换两个变量值的程序

    加法和减法（而不是通过分配给临时变量

    变量)。

```
       X ::= X + Y;; 
       Y ::= X - Y;; 
       X ::= X - Y

```

    我们可以使用装饰证明这个程序是正确的 —

    即，它总是交换变量 X 和 Y 的值。

[

    (1)     {{ X = m ∧ Y = n }} ⇾

    (2)     {{ (X + Y) - ((X + Y) - Y) = n ∧ (X + Y) - Y = m }}

        X ::= X + Y;;

    (3)     {{ X - (X - Y) = n ∧ X - Y = m }}

        Y ::= X - Y;;

    (4)     {{ X - Y = n ∧ Y = m }}

        X ::= X - Y

    (5)     {{ X = n ∧ Y = m }}

]

    这些装饰可以按以下方式构建：

+   我们从未装饰的程序开始（未编号的行）。

+   我们添加规范 — 即，外部前置条件(1)

            和后置条件(5)。在前置条件中，我们使用参数

            m 和 n 以记住变量 X 的初始值

            和 Y，这样我们可以在

            后置条件(5)。

+   我们从(5)开始机械地向后工作，并

            继续，直到我们到达(2)。在每一步中，我们获得

            从其后置条件到前置条件

            通过用右侧替换分配变量

            分配。例如，我们通过替换获得(4)

            X 用 X - Y 替换在(5)中，并通过用 X -替换 Y

            Y 在(4)中。

+   最后，我们验证(1)逻辑上蕴含(2) — 即，

            从(1)到(2)是法则的有效使用

            结果。为此，我们将 X 替换为 m，Y 替换为 n

            并计算如下：

    ```
        (m + n) - ((m + n) - n) = n ∧ (m + n) - n = m 
        (m + n) - m = n ∧ m = m 
        n = n ∧ m = m

    ```

    请注意，由于我们使用自然数而不是

    固定宽度的机器整数，我们不需要担心

    在这个论点中的任何地方都有算术溢出的可能性。

    这使生活变得简单多了！

```

## Example: Simple Conditionals

 Here is a simple decorated program using conditionals:

```

(1)     {{True}}

IFB X ≤ Y THEN

(2)       {{True ∧ X ≤ Y}} ⇾

(3)       {{(Y - X) + X = Y ∨ (Y - X) + Y = X}}

Z ::= Y - X

(4)       {{Z + X = Y ∨ Z + Y = X}}

ELSE

(5)       {{True ∧ ~(X ≤ Y) }} ⇾

(6)       {{(X - Y) + X = Y ∨ (X - Y) + Y = X}}

Z ::= X - Y

(7)       {{Z + X = Y ∨ Z + Y = X}}

FI

(8)     {{Z + X = Y ∨ Z + Y = X}}

```

These decorations were constructed as follows:

*   We start with the outer precondition (1) and postcondition (8).

*   We follow the format dictated by the hoare_if rule and copy the
        postcondition (8) to (4) and (7). We conjoin the precondition (1)
        with the guard of the conditional to obtain (2). We conjoin (1)
        with the negated guard of the conditional to obtain (5).

*   In order to use the assignment rule and obtain (3), we substitute
        Z by Y - X in (4). To obtain (6) we substitute Z by X - Y
        in (7).

*   Finally, we verify that (2) implies (3) and (5) implies (6). Both
        of these implications crucially depend on the ordering of X and
        Y obtained from the guard. For instance, knowing that X ≤ Y
        ensures that subtracting X from Y and then adding back X
        produces Y, as required by the first disjunct of (3). Similarly,
        knowing that ¬ (X ≤ Y) ensures that subtracting Y from X
        and then adding back Y produces X, as needed by the second
        disjunct of (6). Note that n - m + m = n does *not* hold for
        arbitrary natural numbers n and m (for example, 3 - 5 + 5 =
        5). 

#### Exercise: 2 starsM (if_minus_plus_reloaded)

 Fill in valid decorations for the following program:

```

{{ True }}

IFB X ≤ Y THEN

{{                         }} ⇾

{{                         }}

Z ::= Y - X

{{                         }}

否则

{{                         }} ⇾

{{                         }}

Y ::= X + Z

{{                         }}

FI

{{ Y = X + Z }}

```

 ☐ 

```

## 例如：减少到零

这是一个 WHILE 循环，非常简单，不需要

    不变量（即，不变量 True 将完成工作）。

```
        (1)      {{ True }}
               WHILE X ≠ 0 DO
        (2)        {{ True ∧ X ≠ 0 }} ⇾
        (3)        {{ True }}
                 X ::= X - 1
        (4)        {{ True }}
               END
        (5)      {{ True ∧ X = 0 }} ⇾
        (6)      {{ X = 0 }}

```

装饰物可以按以下方式构造：

+   从外部前提（1）和后提（6）开始。

+   遵循由 hoare_while 规则规定的格式，我们

        将（1）复制到（4）。 我们与保护合并（1）以获得（2）和

        用保护的否定来获得（5）。 请注意，因为

        外部后件（6）在语法上不匹配（5），我们

        需要从（5）到（6）的平凡使用后果规则。

+   断言（3）与（4）相同，因为 X 不出现在中

        4，因此在赋值规则中的替换是平凡的。

+   最后，（2）和（3）之间的含义也是显而易见的。

从这个非正式证明中，很容易读出一个正式证明

    使用 Hoare 规则的 Coq 版本。 请注意，我们不要*不要*

    在此证明中的任何位置展开 hoare_triple 的定义-

    思想是使用 Hoare 规则作为“自包含”的逻辑

    对程序进行推理。

```
Definition reduce_to_zero' : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem reduce_to_zero_correct' :
  {{fun st ⇒ True}}
  reduce_to_zero'
  {{fun st ⇒ st X = 0}}.
Proof.
  unfold reduce_to_zero'.
  (* First we need to transform the postcondition so
     that hoare_while will apply. *)
  eapply hoare_consequence_post.
  apply hoare_while.
  - (* Loop body preserves invariant *)
    (* Need to massage precondition before hoare_asgn applies *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    (* Proving trivial implication (2) ->> (3) *)
    intros st [HT Hbp]. unfold assn_sub. apply I.
  - (* Invariant and negated guard imply postcondition *)
    intros st [Inv GuardFalse].
    unfold bassn in GuardFalse. simpl in GuardFalse.
    rewrite not_true_iff_false in GuardFalse.
    rewrite negb_false_iff in GuardFalse.
    apply beq_nat_true in GuardFalse.
    apply GuardFalse. Qed.

```

## 例如：分割

以下的 Imp 程序计算整数商和

    两个任意常数 m 和 n 的余数

    在程序中。

```
       X ::= m;;
       Y ::= 0;;
       WHILE n ≤ X DO
         X ::= X - n;;
         Y ::= Y + 1
       END;

```

    在我们用具体数字替换 m 和 n 并执行时

    程序，它将以变量 X 设置为

    m 除以 n 时的余数，Y 设置为

    商。

为了给这个程序一个规范，我们需要

    记住，将 m 除以 n 会产生余数 X 和 a

    商 Y，使 n * Y + X = m ∧ X <n。

    结果发现我们对这个程序很幸运，不必

    非常努力考虑循环不变性：不变性就是

    第一个合取 n * Y + X = m，我们可以使用此合取

    装饰程序。

```
      (1)    {{ True }} ⇾
      (2)    {{ n * 0 + m = m }}
           X ::= m;;
      (3)    {{ n * 0 + X = m }}
           Y ::= 0;;
      (4)    {{ n * Y + X = m }}
           WHILE n ≤ X DO
      (5)      {{ n * Y + X = m ∧ n ≤ X }} ⇾
      (6)      {{ n * (Y + 1) + (X - n) = m }}
             X ::= X - n;;
      (7)      {{ n * (Y + 1) + X = m }}
             Y ::= Y + 1
      (8)      {{ n * Y + X = m }}
           END
      (9)    {{ n * Y + X = m ∧ X < n }}

```

    断言（4），（5），（8）和（9）从机械上推导

    不变量和循环的保护。 断言（8），（7）和（6）

    使用从（8）反向进行的赋值规则进行推导

    到（6）。 断言（4），（3）和（2）再次反向推导

    赋值规则的应用。

    现在我们已经装饰了程序，只剩下检查

    后果规则的两个用法是正确的-即，（1）

    暗示（2）和（5）暗示（6）。 的确如此，所以

    我们有一个有效的装饰程序。

```

# Finding Loop Invariants

 Once the outermost precondition and postcondition are
    chosen, the only creative part in verifying programs using Hoare
    Logic is finding the right loop invariants.  The reason this is
    difficult is the same as the reason that inductive mathematical
    proofs are: strengthening the loop invariant (or the induction
    hypothesis) means that you have a stronger assumption to work with
    when trying to establish the postcondition of the loop body (or
    complete the induction step of the proof), but it also means that
    the loop body's postcondition (or the statement being proved
    inductively) is stronger and thus harder to prove!

    This section explains how to approach the challenge of finding loop
    invariants through a series of examples and exercises. 

## Example: Slow Subtraction

 The following program subtracts the value of X from the value of
    Y by repeatedly decrementing both X and Y.  We want to verify its
    correctness with respect to the following specification:

```

{{ X = m ∧ Y = n }}

WHILE X ≠ 0 DO

Y ::= Y - 1;;

X ::= X - 1

结束

{{ Y = n - m }}

```

    To verify this program, we need to find an invariant I for the
    loop.  As a first step we can leave I as an unknown and build a
    *skeleton* for the proof by applying (backward) the rules for local
    consistency.  This process leads to the following skeleton:

```

（1）      {{ X = m ∧ Y = n }}  ⇾             （a）

（2）      {{ I }}

WHILE X ≠ 0 DO

（3）        {{ I ∧ X ≠ 0 }}  ⇾              （c）

（4）        {{ I [X ↦ X-1] [Y ↦ Y-1] }}

Y ::= Y - 1;;

（5）        {{ I [X ↦ X-1] }}

X ::= X - 1

（6）        {{ I }}

结束

（7）      {{ I ∧ ¬ （X ≠ 0） }}  ⇾            （b）

（8）      {{ Y = n - m }}

```

    By examining this skeleton, we can see that any valid I will
    have to respect three conditions:

*   (a) it must be weak enough to be implied by the loop's
          precondition, i.e., (1) must imply (2);

*   (b) it must be strong enough to imply the program's postcondition,
          i.e., (7) must imply (8);

*   (c) it must be preserved by one iteration of the loop, i.e., (3)
          must imply (4). 

 These conditions are actually independent of the particular
    program and specification we are considering. Indeed, every loop
    invariant has to satisfy them. One way to find an invariant that
    simultaneously satisfies these three conditions is by using an
    iterative process: start with a "candidate" invariant (e.g., a
    guess or a heuristic choice) and check the three conditions above;
    if any of the checks fails, try to use the information that we get
    from the failure to produce another — hopefully better — candidate
    invariant, and repeat the process.

    For instance, in the reduce-to-zero example above, we saw that,
    for a very simple loop, choosing True as an invariant did the
    job.  So let's try instantiating I with True in the skeleton 
    above see what we get...

```

（1）      {{ X = m ∧ Y = n }} ⇾       （a-OK）

（2）      {{ True }}

WHILE X ≠ 0 DO

(3)        {{ True ∧ X ≠ 0 }}  ⇾    (c - 正确)

(4)        {{ True }}

Y ::= Y - 1;;

(5)        {{ True }}

X ::= X - 1

(6)        {{ True }}

END

(7)      {{ True ∧ X = 0 }}  ⇾       (b - 错误！)

(8)      {{ Y = n - m }}

```

    While conditions (a) and (c) are trivially satisfied,
    condition (b) is wrong, i.e., it is not the case that (7) True ∧
    X = 0 implies (8) Y = n - m.  In fact, the two assertions are
    completely unrelated, so it is very easy to find a counterexample 
    to the implication (say, Y = X = m = 0 and n = 1).

    If we want (b) to hold, we need to strengthen the invariant so
    that it implies the postcondition (8).  One simple way to do
    this is to let the invariant *be* the postcondition.  So let's
    return to our skeleton, instantiate I with Y = n - m, and
    check conditions (a) to (c) again.

```

(1)      {{ X = m ∧ Y = n }}  ⇾          (a - 错误！)

(2)      {{ Y = n - m }}

WHILE X ≠ 0 DO

(3)        {{ Y = n - m ∧ X ≠ 0 }}  ⇾   (c - 错误！)

(4)        {{ Y - 1 = n - m }}

Y ::= Y - 1;;

(5)        {{ Y = n - m }}

X ::= X - 1

(6)        {{ Y = n - m }}

END

(7)      {{ Y = n - m ∧ X = 0 }}  ⇾      (b - 正确)

(8)      {{ Y = n - m }}

```

    This time, condition (b) holds trivially, but (a) and (c) are
    broken. Condition (a) requires that (1) X = m ∧ Y = n
    implies (2) Y = n - m.  If we substitute Y by n we have to
    show that n = n - m for arbitrary m and n, which is not 
    the case (for instance, when m = n = 1).  Condition (c) requires 
    that n - m - 1 = n - m, which fails, for instance, for n = 1 
    and m = 0. So, although Y = n - m holds at the end of the loop, 
    it does not hold from the start, and it doesn't hold on each 
    iteration; it is not a correct invariant.

    This failure is not very surprising: the variable Y changes
    during the loop, while m and n are constant, so the assertion
    we chose didn't have much chance of being an invariant!

    To do better, we need to generalize (8) to some statement that is
    equivalent to (8) when X is 0, since this will be the case
    when the loop terminates, and that "fills the gap" in some
    appropriate way when X is nonzero.  Looking at how the loop
    works, we can observe that X and Y are decremented together
    until X reaches 0.  So, if X = 2 and Y = 5 initially,
    after one iteration of the loop we obtain X = 1 and Y = 4;
    after two iterations X = 0 and Y = 3; and then the loop stops.
    Notice that the difference between Y and X stays constant
    between iterations: initially, Y = n and X = m, and the
    difference is always n - m.  So let's try instantiating I in
    the skeleton above with Y - X = n - m.

```

(1)      {{ X = m ∧ Y = n }}  ⇾               (a - 正确)

(2)      {{ Y - X = n - m }}

WHILE X ≠ 0 DO

(3)        {{ Y - X = n - m ∧ X ≠��0 }}  ⇾    (c - 正确)

(4)        {{ (Y - 1) - (X - 1) = n - m }}

Y ::= Y - 1;;

(5)        {{ Y - (X - 1) = n - m }}

X ::= X - 1

(6)        {{ Y - X = n - m }}

END

(7)      {{ Y - X = n - m ∧ X = 0 }}  ⇾       (b - 正确)

(8)      {{ Y = n - m }}

```

    Success!  Conditions (a), (b) and (c) all hold now.  (To
    verify (c), we need to check that, under the assumption that X ≠
    0, we have Y - X = (Y - 1) - (X - 1); this holds for all
    natural numbers X and Y.) 

```

## 练习：慢赋值

#### 练习：2 星 M（慢赋值）

一个将当前存储在 X 中的数字分配给的绕道方法

    变量 Y 是从 0 开始的，然后递减 X 直到

    它达到 0 时，每一步都会增加 Y。这是一个实现这个想法的程序

    实现这个想法：

```
        {{ X = m }}
      Y ::= 0;;
      WHILE X ≠ 0 DO
        X ::= X - 1;;
        Y ::= Y + 1
      END
        {{ Y = m }}

```

    编写一个非正式的装饰程序，显示此过程

    是正确的。

```
(* FILL IN HERE *)

```

☐

```

## Exercise: Slow Addition

#### Exercise: 3 stars, optional (add_slowly_decoration)

 The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.

```

WHILE X ≠ 0 DO

Z ::= Z + 1;;

X ::= X - 1

END

```

    Following the pattern of the subtract_slowly example above, pick
    a precondition and postcondition that give an appropriate
    specification of add_slowly; then (informally) decorate the
    program accordingly. 

```

(* 在这里填写*）

```

☐ 

```

## 示例：奇偶性

这是一个用于计算奇偶性的可爱小程序

    最初存储在 X 中的值（由 Daniel Cristofani）。

```
         {{ X = m }}
       WHILE 2 ≤ X DO
         X ::= X - 2
       END
         {{ X = parity m }}

```

    规范中使用的数学奇偶函数是

    在 Coq 中定义如下：

```
Fixpoint parity x :=
  match x with
  | 0 ⇒ 0
  | 1 ⇒ 1
  | S (S x') ⇒ parity x'
  end.

```

循环开始时不满足后置条件

    因为 m = 奇偶性 m 对于任意 m 都不成立，所以我们

    不能将其用作不变量。要找到有效的不变量，

    让我们思考一下这个循环的作用。每次迭代时

    递减 2，这保持了 X 的奇偶性。因此

    X 的奇偶性不会改变，即它是不变的。初始

    X 的奇偶性始终等于 X 的奇偶性

    m 的奇偶性。使用奇偶性 X = 奇偶性 m 作为不变量

    获得以下装��程序：

```
        {{ X = m }} ⇾                               (a - OK)
        {{ parity X = parity m }}
      WHILE 2 ≤ X DO
          {{ parity X = parity m ∧ 2 ≤ X }}  ⇾    (c - OK)
          {{ parity (X-2) = parity m }}
        X ::= X - 2
          {{ parity X = parity m }}
      END
        {{ parity X = parity m ∧ X < 2 }}  ⇾       (b - OK)
        {{ X = parity m }}

```

    有了这个不变量，条件（a），（b）和（c）都是

    满足。验证（b）时，我们观察到，当 X < 2 时，我们

    具有奇偶性 X = X（我们可以在定义中轻松看到这一点

    奇偶性）。验证（c）时，我们观察到，当 2 ≤ X 时，我们

    具有奇偶性 X = 奇偶性(X-2)。

#### 练习：3 星，可选（奇偶形式）

将此证明翻译为 Coq。参考 reduce_to_zero 示例

    对于想法。您可能会发现以下两个引理有用：

```
Lemma parity_ge_2 : ∀x,
  2 ≤ x →
  parity (x - 2) = parity x.

Proof.
  induction x; intro. reflexivity.
  destruct x. inversion H. inversion H[1].
  simpl. rewrite ← [minus_n_O](http://coq.inria.fr/library/Coq.Arith.Minus.html#minus_n_O). reflexivity.
Qed.

Lemma parity_lt_2 : ∀x,
  ¬ 2 ≤ x →
  parity (x) = x.

Proof.
  intros. induction x. reflexivity. destruct x. reflexivity.
    exfalso. apply H. omega.
Qed.

Theorem parity_correct : ∀m,
    {{ fun st ⇒ st X = m }}
  WHILE BLe (ANum 2) (AId X) DO
    X ::= AMinus (AId X) (ANum 2)
  END
    {{ fun st ⇒ st X = parity m }}.
Proof.
  (* FILL IN HERE *) Admitted.

```

☐

```

## Example: Finding Square Roots

 The following program computes the square root of X
    by naive iteration:

```

{{ X=m }}

Z ::= 0;;

WHILE (Z+1)*(Z+1) ≤ X DO

Z ::= Z+1

END

{{ Z*Z≤m ∧ m<(Z+1)*(Z+1) }}

```

 As above, we can try to use the postcondition as a candidate
    invariant, obtaining the following decorated program:

```

(1)  {{ X=m }}  ⇾           (a - (2)的第二个连接词是错误的！)

(2)  {{ 0*0 ≤ m ∧ m<1*1 }}

Z ::= 0;;

(3)  {{ Z*Z ≤ m ∧ m<(Z+1)*(Z+1) }}

WHILE (Z+1)*(Z+1) ≤ X DO

(4)    {{ Z*Z≤m ∧ (Z+1)*(Z+1)≤X }}  ⇾             (c - 错误！)

(5)    {{ (Z+1)*(Z+1)≤m ∧ m<(Z+2)*(Z+2) }}

Z ::= Z+1

(6)    {{ Z*Z≤m ∧ m<(Z+1)*(Z+1) }}

END

(7)  {{ Z*Z≤m ∧ m<(Z+1)*(Z+1) ∧ ~((Z+1)*(Z+1)≤X) }}  ⇾ (b - OK)

(8)  {{ Z*Z≤m ∧ m<(Z+1)*(Z+1) }}

```

    This didn't work very well: conditions (a) and (c) both failed.
    Looking at condition (c), we see that the second conjunct of (4)
    is almost the same as the first conjunct of (5), except that (4)
    mentions X while (5) mentions m. But note that X is never
    assigned in this program, so we should always have X=m, but we 
    didn't propagate this information from (1) into the loop invariant.

    Also, looking at the second conjunct of (8), it seems quite
    hopeless as an invariant (why?); fortunately, we don't need it, 
    since we can obtain it from the negation of the guard — the third 
    conjunct in (7) — again under the assumption that X=m.

    So we now try X=m ∧ Z*Z ≤ m as the loop invariant:

```

{{ X=m }}  ⇾                                      (a - OK)

{{ X=m ∧ 0*0 ≤ m }}

Z ::= 0;

{{ X=m ∧ Z*Z ≤ m }}

当 (Z+1)*(Z+1) ≤ X 时

{{ X=m ∧ Z*Z≤m ∧ (Z+1)*(Z+1)≤X }}  ⇾        (c - OK)

{{ X=m ∧ (Z+1)*(Z+1)≤m }}

Z ::= Z+1

{{ X=m ∧ Z*Z ≤ m }}

结束

{{ X=m ∧ Z*Z≤m ∧ X<(Z+1)*(Z+1) }}  ⇾           (b - OK)

{{ Z*Z≤m ∧ m<(Z+1)*(Z+1) }}

```

    This works, since conditions (a), (b), and (c) are now all
    trivially satisfied.

    Very often, even if a variable is used in a loop in a read-only
    fashion (i.e., it is referred to by the program or by the
    specification and it is not changed by the loop), it is necessary
    to add the fact that it doesn't change to the loop invariant. 

```

## 例子：平方

这是一个通过重复加法来平方 X 的程序：

```
    {{ X = m }}
  Y ::= 0;;
  Z ::= 0;;
  WHILE  Y ≠ X  DO
    Z ::= Z + X;;
    Y ::= Y + 1
  END
    {{ Z = m*m }}

```

首先要注意的是循环读取 X 但不读取

    改变其值。正如我们在前面的例子中看到的，这是一个好主意

    在这种情况下，将 X = m 添加到不变量是有用的。另一件事

    我们经常在不变量中使用的一件事是后置条件，

    因此让我们也添加这个，导致不变量候选

    Z = m * m ∧ X = m。

```
      {{ X = m }} ⇾                            (a - WRONG)
      {{ 0 = m*m ∧ X = m }}
    Y ::= 0;;
      {{ 0 = m*m ∧ X = m }}
    Z ::= 0;;
      {{ Z = m*m ∧ X = m }}
    WHILE Y ≠ X DO
        {{ Z = Y*m ∧ X = m ∧ Y ≠ X }} ⇾     (c - WRONG)
        {{ Z+X = m*m ∧ X = m }}
      Z ::= Z + X;;
        {{ Z = m*m ∧ X = m }}
      Y ::= Y + 1
        {{ Z = m*m ∧ X = m }}
    END
      {{ Z = m*m ∧ X = m ∧ ~(Y ≠ X) }} ⇾         (b - OK)
      {{ Z = m*m }}

```

    条件（a）和（c）因为 Z = m*m 部分而失败。虽然

    Z 从 0 开始，逐渐增加到 m*m，我们不能期望

    从一开始 Z 就是 m*m。如果我们看看 Z 的进展

    在循环中，第 1 次迭代后 Z = m，第 2 次迭代后

    迭代 Z = 2*m，最终 Z = m*m。由于变量

    Y 跟踪我们通过循环的次数，这导致我们

    推导一个新的不变量候选：Z = Y*m ∧ X = m。

```
      {{ X = m }} ⇾                               (a - OK)
      {{ 0 = 0*m ∧ X = m }}
    Y ::= 0;;
      {{ 0 = Y*m ∧ X = m }}
    Z ::= 0;;
      {{ Z = Y*m ∧ X = m }}
    WHILE Y ≠ X DO
        {{ Z = Y*m ∧ X = m ∧ Y ≠ X }} ⇾        (c - OK)
        {{ Z+X = (Y+1)*m ∧ X = m }}
      Z ::= Z + X;
        {{ Z = (Y+1)*m ∧ X = m }}
      Y ::= Y + 1
        {{ Z = Y*m ∧ X = m }}
    END
      {{ Z = Y*m ∧ X = m ∧ ~(Y ≠ X) }} ⇾           (b - OK)
      {{ Z = m*m }}

```

    这个新的不变量使得证明通过：所有三个

    条件很容易检查。

    值得比较后置条件 Z = m*m 和 Z =

    Y*m 是不变量的一个合取。通常情况下，一个人可能会

    用变量替换参数 — 或者

    包含变量和参数的表达式，如

    m - Y — 从后置条件到不变量时。

```

## Exercise: Factorial

#### Exercise: 3 starsM (factorial)

 Recall that n! denotes the factorial of n (i.e., n! =
    1*2*...*n).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable X and puts it in
    the variable Y:

```

{{ X = m }}

Y ::= 1 ;;

当 X ≠ 0

做

Y ::= Y * X ;;

X ::= X - 1

结束

{{ Y = m! }}

```

    Fill in the blanks in following decorated program:

```

{{ X = m }} ⇾

{{                                      }}

Y ::= 1;;

{{                                      }}

当 X ≠ 0

做   {{                                      }} ⇾

{{                                      }}

Y ::= Y * X;;

{{                                      }}

X ::= X - 1

{{                                      }}

结束

{{                                      }} ⇾

{{ Y = m! }}

```

 ☐ 

```

## 练习：Min

#### 练习：3 星 M（Min_Hoare）

为以下程序填写有效的装饰。

在您的注释中，对于⇒ 步骤，您可以依赖（悄悄地）

关于 min 的以下事实

```
  Lemma lemma1 : ∀x y,
    (x=0 ∨ y=0) → min x y = 0.
  Lemma lemma2 : ∀x y,
    min (x-1) (y-1) = (min x y) - 1.

```

再加上标准的高中代数，一如既往。

```
  {{ True }} ⇾
  {{                    }}
  X ::= a;;
  {{                       }}
  Y ::= b;;
  {{                       }}
  Z ::= 0;;
  {{                       }}
  WHILE (X ≠ 0 ∧ Y ≠ 0) DO
  {{                                     }} ⇾
  {{                                }}
  X := X - 1;;
  {{                            }}
  Y := Y - 1;;
  {{                        }}
  Z := Z + 1
  {{                       }}
  END
  {{                            }} ⇾
  {{ Z = min a b }}

```

☐

#### 练习：3 星 M（two_loops）

这是一个非常低效的方法来相加 3 个数字：

```
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X ≠ a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y ≠ b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

```

    通过填写注释中的空白来展示它的功能。

    以下是装饰过的程序。

```
    {{ True }} ⇾
    {{                                        }}
  X ::= 0;;
    {{                                        }}
  Y ::= 0;;
    {{                                        }}
  Z ::= c;;
    {{                                        }}
  WHILE X ≠ a DO
      {{                                        }} ⇾
      {{                                        }}
    X ::= X + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END;;
    {{                                        }} ⇾
    {{                                        }}
  WHILE Y ≠ b DO
      {{                                        }} ⇾
      {{                                        }}
    Y ::= Y + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END
    {{                                        }} ⇾
    {{ Z = a + b + c }}

```

☐

```

## Exercise: Power Series

#### Exercise: 4 stars, optional (dpow2_down)

 Here is a program that computes the series:
    1 + 2 + 2² + ... + 2^m = 2^(m+1) - 1

```

X ::= 0;;

Y ::= 1;;

Z ::= 1;;

当 X ≠ m 时

Z ::= 2 * Z;;

Y ::= Y + Z;;

X ::= X + 1

结束

```

    Write a decorated program for this. 

```

(* 在这里填写 *)

```

☐ 

```

# 最弱前置条件（可选）

一些 Hoare 三元组比其他的更有趣。

    例如，

```
      {{ False }}  X ::= Y + 1  {{ X ≤ 5 }}

```

    *不* 非常有趣：尽管它是完全有效的，但它

    告诉我们没有什么有用的信息。由于前置条件不满足

    通过任何状态，它并不描述任何我们可以使用的情况

    命令 X ::= Y + 1 来实现后置条件 X ≤ 5。

    相比之下，

```
      {{ Y ≤ 4 ∧ Z = 0 }}  X ::= Y + 1 {{ X ≤ 5 }}

```

    是有用的：它告诉我们，如果我们可以以某种方式创造一种情况

    在我们知道 Y ≤ 4 ∧ Z = 0 的情况下，然后运行此命令

    将产生一个满足后置条件的状态。然而，这

    三元组仍然不如它本应该的那么有用，因为 Z = 0

    前提子句实际上与

    后置条件 X ≤ 5。*最*有用的三元组（对于这个

    命令和后置条件）是这个：

```
      {{ Y ≤ 4 }}  X ::= Y + 1  {{ X ≤ 5 }}

```

    换句话说，Y ≤ 4 是 X ::= Y + 1 的*最弱*有效前置条件

    命令 X ::= Y + 1 的后置条件为 X ≤ 5。

一般来说，我们说“P 是 c 的最弱前置条件

    如果{{P}} c {{Q}}，并且，

    每当 P'是一个断言，使得{{P'}} c {{Q}}，它就是

    如果 P' st 意味着对于所有状态 st 都成立。

```
Definition is_wp P c Q :=
  {{P}} c {{Q}} ∧
  ∀P', {{P'}} c {{Q}} → (P' ⇾ P).

```

也就是说，P 是 Q 的 c 的最弱前置条件

    如果（a）P *是* Q 和 c 的前提条件，且（b）P 是

    *最弱*（最容易满足）的断言，保证

    Q 将在执行 c 后成立。

#### 练习：1 星，可选（wp）

以下命令的最弱前置条件是什么

对于以下后置条件？

```
  1) {{ ? }}  SKIP  {{ X = 5 }}

  2) {{ ? }}  X ::= Y + Z {{ X = 5 }}

  3) {{ ? }}  X ::= Y  {{ X = Y }}

  4) {{ ? }}
     IFB X == 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
     {{ Y = 5 }}

  5) {{ ? }}
     X ::= 5
     {{ X = 0 }}

  6) {{ ? }}
     WHILE True DO X ::= 0 END
     {{ X = 0 }}

```

```
(* FILL IN HERE *)

```

☐

#### 练习：3 星，高级，可选（is_wp_formal）

正式证明，使用 hoare_triple 的定义，Y ≤ 4

实际上是 X ::= Y + 1 的最弱前置条件

后置条件 X ≤ 5。

```
Theorem is_wp_example :
  is_wp (fun st ⇒ st Y ≤ 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st ⇒ st X ≤ 5).
Proof.
  (* FILL IN HERE *) Admitted.

```

☐

#### 练习：2 星，高级，可选（hoare_asgn_weakest）

显示 hoare_asgn 规则中的前置条件实际上是

    最弱前置条件。

```
Theorem hoare_asgn_weakest : ∀Q X a,
  is_wp (Q [X ↦ a]) (X ::= a) Q.
Proof.
(* FILL IN HERE *) Admitted.

```

☐

#### 练习：2 星，高级，可选（hoare_havoc_weakest）

显示你从 himp_hoare 练习中的 havoc_pre 规则

    在 Hoare 章节中返回最弱的前置条件。

```
Module Himp2.
Import Himp.

Lemma hoare_havoc_weakest : ∀(P Q : Assertion) (X : id),
  {{ P }} HAVOC X {{ Q }} →
  P ⇾ havoc_pre X Q.
Proof.
(* FILL IN HERE *) Admitted.

```

☐

```

# Formal Decorated Programs (Optional)

 Our informal conventions for decorated programs amount to a
    way of displaying Hoare triples, in which commands are annotated
    with enough embedded assertions that checking the validity of a
    triple is reduced to simple logical and algebraic calculations
    showing that some assertions imply others.  In this section, we
    show that this informal presentation style can actually be made
    completely formal and indeed that checking the validity of
    decorated programs can mostly be automated.  

## Syntax

 The first thing we need to do is to formalize a variant of the
    syntax of commands with embedded assertions.  We call the new
    commands *decorated commands*, or dcoms. 

 We don't want both preconditions and postconditions on each
    command, because a sequence of two commands would contain
    redundant decorations, the postcondition of the first likely
    being the same as the precondition of the second. Instead,
    decorations are added corresponding to each postcondition.
    A separate type, decorated, is used to add the precondition
    for the entire program. 

```

归纳 dcom：类型：=

| DCSkip：  断言 → dcom

| DCSeq：dcom → dcom → dcom

| DCAsgn：id → aexp →  断言 → dcom

| DCIf：bexp →  断言 → dcom →  断言 → dcom

→ 断言→ dcom

| DCWhile：bexp → 断言 → dcom → 断言 → dcom

| DCPre：断言 → dcom → dcom

| DCPost：dcom → 断言 → dcom。

归纳装饰：类型：=

| 装饰：断言 → dcom → 装饰。

符号"'SKIP' {{ P }}"

:=（DCSkip P）

（在 10 级别）：dcom_scope。

符号"l '::=' a {{ P }}"

:=（DCAsgn l a P）

（在 60 级别，下一个级别为 a）：dcom_scope。

符号"'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"

:=（DCWhile b Pbody d Ppost）

（在 80 级别，右结合性）：dcom_scope。

符号"'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}"

:=（DCIf b P d P' d' Q）

（在 80 级别，右结合性）：dcom_scope。

符号"'⇾' {{ P }} d"

:=（DCPre P d）

（在 90 级别，右结合性）：dcom_scope。

符号"d '⇾' {{ P }}"

:=（DCPost d P）

（在 80 级别，右结合性）：dcom_scope。

符号"d ;; d' "

:=（DCSeq d d'）

（在 80 级别，右结合性）：dcom_scope。

符号"{{ P }} d"

:=（Decorated P d）

（在 90 级别）：dcom_scope。

使用 dcom 的 Delimit Scope dcom_scope。

```

To avoid clashing with the existing Notation definitions
    for ordinary commands, we introduce these notations in a special
    scope called dcom_scope, and we wrap examples with the
    declaration % dcom to signal that we want the notations to be
    interpreted in this scope.

    Careful readers will note that we've defined two notations for the
    DCPre constructor, one with and one without a ⇾.  The
    "without" version is intended to be used to supply the initial
    precondition at the very top of the program. 

```

示例 dec_while：装饰 := (

{{ fun st ⇒ True }}

{{'_x_'}}'_x_'END'_'{{'_x_'}}'">WHILE（BNot（BEq（AId X）（ANum 0）））

做

{{ fun st ⇒ True ∧ st X ≠ 0}}

X ::= (AMinus (AId X) (ANum 1))

{{ fun _ ⇒ True }}

END

{{ fun st ⇒ True ∧ st X = 0}} ⇾

{{ fun st ⇒ st X = 0 }}

) % dcom.

```

It is easy to go from a dcom to a com by erasing all
    annotations. 

```

Fixpoint extract (d:dcom) : com :=

match d with

| DCSkip _           ⇒ SKIP

| DCSeq d[1] d[2]        ⇒ (extract d[1] ;; extract d[2])

| DCAsgn X a _       ⇒ X ::= a

| DCIf b _ d[1] _ d[2] _ ⇒ IFB b THEN extract d[1] ELSE extract d[2] FI

| DCWhile b _ d _    ⇒ WHILE b DO extract d END

| DCPre _ d          ⇒ extract d

| DCPost d _         ⇒ extract d

end.

Definition extract_dec (dec : decorated) : com :=

match dec with

| Decorated P d ⇒ extract d

end.

```

The choice of exactly where to put assertions in the definition of
    dcom is a bit subtle.  The simplest thing to do would be to
    annotate every dcom with a precondition and postcondition.  But
    this would result in very verbose programs with a lot of repeated
    annotations: for example, a program like SKIP;SKIP would have to
    be annotated as

```

{{P}} ({{P}} SKIP {{P}}) ;; ({{P}} SKIP {{P}}) {{P}},

```

    with pre- and post-conditions on each SKIP, plus identical pre-
    and post-conditions on the semicolon!

    Instead, the rule we've followed is this:

*   The *post*-condition expected by each dcom d is embedded
             in d.

*   The *pre*-condition is supplied by the context. 

 In other words, the invariant of the representation is that a
    dcom d together with a precondition P determines a Hoare
    triple {{P}} (extract d) {{post d}}, where post is defined as
    follows: 

```

Fixpoint post (d:dcom) : Assertion :=

match d with

| DCSkip P                ⇒ P

| DCSeq d[1] d[2]             ⇒ post d[2]

| DCAsgn X a Q            ⇒ Q

| DCIf  _ _ d[1] _ d[2] Q     ⇒ Q

| DCWhile b Pbody c Ppost ⇒ Ppost

| DCPre _ d               ⇒ post d

| DCPost c Q              ⇒ Q

end.

```

It is straightforward to extract the precondition and
    postcondition from a decorated program. 

```

Definition pre_dec (dec : decorated) : Assertion :=

match dec with

| Decorated P d ⇒ P

end.

Definition post_dec (dec : decorated) : Assertion :=

match dec with

| Decorated P d ⇒ post d

end.

```

We can express what it means for a decorated program to be
    correct as follows: 

```

Definition dec_correct (dec : decorated) :=

{{pre_dec dec}} (extract_dec dec) {{post_dec dec}}.

```

To check whether this Hoare triple is *valid*, we need a way to
    extract the "proof obligations" from a decorated program.  These
    obligations are often called *verification conditions*, because
    they are the facts that must be verified to see that the
    decorations are logically consistent and thus add up to a complete
    proof of correctness. 

## Extracting Verification Conditions

 The function verification_conditions takes a dcom d together
    with a precondition P and returns a *proposition* that, if it
    can be proved, implies that the triple {{P}} (extract d) {{post d}}
    is valid. 

 It does this by walking over d and generating a big
    conjunction including all the "local checks" that we listed when
    we described the informal rules for decorated programs.  (Strictly
    speaking, we need to massage the informal rules a little bit to
    add some uses of the rule of consequence, but the correspondence
    should be clear.) 

```

Fixpoint verification_conditions (P : Assertion) (d:dcom)

: Prop :=

match d with

| DCSkip Q ⇒

(P ⇾ Q)

| DCSeq d[1] d[2] ⇒

verification_conditions P d[1]

∧ verification_conditions (post d[1]) d[2]

| DCAsgn X a Q ⇒

(P ⇾ Q [X ↦ a])

| DCIf b P[1] d[1] P[2] d[2] Q ⇒

((fun st ⇒ P st ∧ bassn b st) ⇾ P[1])

∧ ((fun st ⇒ P st ∧ ¬ (bassn b st)) ⇾ P[2])

∧ (post d[1] ⇾ Q) ∧ (post d[2] ⇾ Q)

∧ verification_conditions P[1] d[1]

∧ verification_conditions P[2] d[2]

| DCWhile b Pbody d Ppost ⇒

(* post d is the loop invariant and the initial

precondition *)

(P ⇾ post d)

∧ ((fun st ⇒ post d st ∧ bassn b st) ⇾ Pbody)

∧ ((fun st ⇒ post d st ∧ ~(bassn b st)) ⇾ Ppost)

∧ verification_conditions Pbody d

| DCPre P' d ⇒

(P ⇾ P') ∧ verification_conditions P' d

| DCPost d Q ⇒

verification_conditions P d ∧ (post d ⇾ Q)

end.

```

And now the key theorem, stating that verification_conditions
    does its job correctly.  Not surprisingly, we need to use each of
    the Hoare Logic rules at some point in the proof. 

```

Theorem verification_correct : ∀d P,

verification_conditions P d → {{P}} (extract d) {{post d}}.

Proof

induction d; intros P H; simpl in *.

- (* 跳过 *)

eapply hoare_consequence_pre.

apply hoare_skip.

assumption.

- (* 序列 *)

inversion H as [H[1] H[2]]. clear H.

eapply hoare_seq.

apply IHd2. apply H[2].

apply IHd1. apply H[1].

- (* 赋值 *)

eapply hoare_consequence_pre.

apply hoare_asgn.

assumption.

- (* 条件 *)

inversion H as [HPre1 [HPre2 [Hd[1] [Hd[2] [HThen HElse]]]]].

clear H.

apply IHd1 in HThen. clear IHd1.

apply IHd2 in HElse. clear IHd2.

apply hoare_if.

+ eapply hoare_consequence_post with (Q':=post d[1]); eauto.

eapply hoare_consequence_pre; eauto.

+使用 hoare_consequence_postwith（Q':=post d[2]）; eauto。

使用 hoare_consequence_pre; eauto。

验证。

作为[Hpre [Hbody1 [Hpost1 Hd]]]进行反演。 清除 H。

匹配目标；

使用 hoare_consequence_post； eauto。

应用 hoare_while。

{{fun st ⇒ st Z - st X = p - m ∧ st X = 0}} ⇾

- （* 前 *）

作为[H：_ = st _⊢_]⇒重写← H 在*中; 清除 H

使用 hoare_consequence_pre。 应用 IHd。 应用 Hd。 假设。

- （* 后置 *）

Z :: = AMinus（AId Z）（ANum 1）

应用 hoare_consequence_post。 应用 IHd。 应用 Hd。 假设。

重复在 t_update_eq 中写入;

```

(If you expand the proof, you'll see that it uses an
    unfamiliar idiom: simpl in *.  We have used ...in... variants
    of several tactics before, to apply them to values in the context
    rather than the goal.  The syntax tactic in * extends this idea,
    applying tactic in the goal and every hypothesis in the
    context.) 

## Automation

 Now that all the pieces are in place, we can verify an entire program. 

```

定义 verification_conditions_dec（dec：decorated）：= 

- （* 当 *）

| Decorated P d ⇒ verification_conditions P d

结束。

匹配 dec 与

使用 hoare_consequence_pre; eauto。

证明。

对[P d]进行推理。 应用 verification_correct。

完成。

```

The propositions generated by verification_conditions are fairly
    big, and they contain many conjuncts that are essentially trivial. 

```

在 verification_conditions_dec dec_while 中评估简化。

```

```

⇒（（（fun _：state ⇒ True）⇾（fun _：state ⇒ True））∧

verification_conditions_dec dec→dec_correct dec。

（fun st：state ⇒ True ∧ st X ≠ 0））∧

（（fun st：state ⇒ True ∧ ¬ bassn（BNot（BEq（AId X）（ANum 0）））st）⇾

（fun st：state ⇒ True ∧ st X = 0））∧

（fun st：state ⇒ True ∧ st X ≠ 0）⇾

（fun _：state ⇒ True）[X↦AMinus（AId X）（ANum 1）]）∧

（fun st：state ⇒ True ∧ st X = 0）⇾（fun st：state ⇒ st X = 0）

```

 In principle, we could work with such propositions using just the
    tactics we have so far, but we can make things much smoother with
    a bit of automation.  We first define a custom verify tactic
    that uses split repeatedly to turn all the conjunctions into
    separate subgoals and then uses omega and eauto (described in
    chapter Auto) to deal with as many of them as possible. 

```

重复在 t_update_eq 中写入;

应用 verification_correct。

作为[Hd HQ]反演 H。 清除 H。

简化; 展开 assert_implies;

在*中展开 bassn; 在*中展开 beval; 在*中展开 aeval;

展开 assn_sub; 进入;

重复分割;

重复（rewrite t_update_neq; [|（intro X; inversion X）]）。

简化*;

重复匹配目标，其中[H：_∧_⊢_]⇒分解 H 结束;

重复在*中写入 not_true_iff;

在*中重复写入 not_false_iff;

在*中重复写入 negb_true_iff;

重复在*中写入 negb_false_iff;

在*中重复写入 beq_nat_true_iff;

重复在 beq_nat_false_iff 中写入*;

重复在 leb_iff 中写入*;

重复在 leb_iff_conv 中写入*;

尝试替换;

重复

与目标匹配

[st：state ⊢ _]⇒

| [H：_ = st _⊢_]⇒重写← H 在*中; 清除 H

[H：st _ = _⊢_]⇒重写→H 在*中; 清除 H

定理 verification_correct_dec：∀dec，

结束

结束;

尝试 eauto; 尝试 omega。

```

What's left after verify does its thing is "just the interesting
    parts" of checking that the decorations are correct. For very
    simple examples verify immediately solves the goal (provided
    that the annotations are correct). 

```

定理 dec_while_correct：

verification_conditions_dec dec_while 正确。

证明。 验证。 完成。

```

Another example (formalizing a decorated program we've seen
    before): 

```

例子 subtract_slowly_dec（m：nat）（p：nat）：decorated：= (

{{fun st ⇒ st X = m ∧ st Z = p}} ⇾

{{fun st ⇒ st Z - st X = p - m}}

{{'_x_'}}'_x_'END'_'{{'_x_'}}'">WHILE BNot（BEq（AId X）（ANum 0））

DO   {{fun st ⇒ st Z - st X = p - m ∧ st X ≠ 0}} ⇾

{{fun st ⇒（st Z - 1）-（st X - 1）= p - m}}

使用 hoare_consequence_pre; eauto。

{{fun st ⇒ st Z -（st X - 1）= p - m}} ;;

X :: = AMinus（AId X）（ANum 1）

{{fun st ⇒ st Z - st X = p - m}}

END

Z :: = AMinus（AId Z）（ANum 1）

{{fun st ⇒ st Z = p - m}}

) % dcom。

定理 subtract_slowly_dec_correct：∀m p，

dec_correct (subtract_slowly_dec m p).

证明。引入 m p。验证。(* 这个需要花点时间！ *) Qed.

```

## Examples

 In this section, we use the automation developed above to verify
    formal decorated programs corresponding to most of the informal
    ones we have seen. 

### Swapping Using Addition and Subtraction

```

定义交换：com :=

X ::= APlus (AId X) (AId Y);;

Y ::= AMinus (AId X) (AId Y);;

X ::= AMinus (AId X) (AId Y)。

定义 swap_dec m n：decorated :=

({{ fun st ⇒ st X = m ∧ st Y = n}} ⇾

{{ fun st ⇒ (st X + st Y) - ((st X + st Y) - st Y) = n

∧ (st X + st Y) - st Y = m }}

X ::= APlus (AId X) (AId Y)

{{ fun st ⇒ st X - (st X - st Y) = n ∧ st X - st Y = m }};;

Y ::= AMinus (AId X) (AId Y)

{{ fun st ⇒ st X - st Y = n ∧ st Y = m }};;

X ::= AMinus (AId X) (AId Y)

{{ fun st ⇒ st X = n ∧ st Y = m}})%dcom。

定理 swap_correct：∀m n，

dec_correct (swap_dec m n)。

证明。引入；验证。Qed。

```

### Simple Conditionals

```

定义 if_minus_plus_com :=

如果 (BLe (AId X) (AId Y))

然后 (Z ::= AMinus (AId Y) (AId X))

否则 (Y ::= APlus (AId X) (AId Z))

FI。

定义 if_minus_plus_dec :=

({{fun st ⇒ True}}

{{'_x_'}}'_x_'ELSE'_'{{'_x_'}}'_x_'FI'_'{{'_x_'}}'">如果 (BLe (AId X) (AId Y)) 则

{{ fun st ⇒ True ∧ st X ≤ st Y }} ⇾

{{ fun st ⇒ st Y = st X + (st Y - st X) }}

Z ::= AMinus (AId Y) (AId X)

{{ fun st ⇒ st Y = st X + st Z }}

否则

{{ fun st ⇒ True ∧ ~(st X ≤ st Y) }} ⇾

{{ fun st ⇒ st X + st Z = st X + st Z }}

Y ::= APlus (AId X) (AId Z)

{{ fun st ⇒ st Y = st X + st Z }}

FI

{{fun st ⇒ st Y = st X + st Z}})%dcom。

定理 if_minus_plus_correct：

dec_correct if_minus_plus_dec。

证明。引入；验证。Qed。

定义 if_minus_dec :=

( {{fun st ⇒ True}}

{{'_x_'}}'_x_'ELSE'_'{{'_x_'}}'_x_'FI'_'{{'_x_'}}'">如果 (BLe (AId X) (AId Y)) 则

{{fun st ⇒ True ∧ st X ≤ st Y }} ⇾

{{fun st ⇒ (st Y - st X) + st X = st Y

∨ (st Y - st X) + st Y = st X}}

Z ::= AMinus (AId Y) (AId X)

{{fun st ⇒ st Z + st X = st Y ∨ st Z + st Y = st X}}

否则

{{fun st ⇒ True ∧ ~(st X ≤ st Y) }} ⇾

{{fun st ⇒ (st X - st Y) + st X = st Y

∨ (st X - st Y) + st Y = st X}}

Z ::= AMinus (AId X) (AId Y)

{{fun st ⇒ st Z + st X = st Y ∨ st Z + st Y = st X}}

FI

{{fun st ⇒ st Z + st X = st Y ∨ st Z + st Y = st X}})%dcom。

定理 if_minus_correct：

dec_correct if_minus_dec。

证明。验证。Qed.

```

### Division

```

定义 div_mod_dec (a b : 自然数)：decorated := (

{{ fun st ⇒ True }} ⇾

{{ fun st ⇒ b * 0 + a = a }}

X ::= ANum a

{{ fun st ⇒ b * 0 + st X = a }};;

Y ::= ANum 0

{{ fun st ⇒ b * st Y + st X = a }};;

{{'_x_'}}'_x_'END'_'{{'_x_'}}'">当 (BLe (ANum b) (AId X)) 时

{{ fun st ⇒ b * st Y + st X = a ∧ b ≤ st X }} ⇾

{{ fun st ⇒ b * (st Y + 1) + (st X - b) = a }}

X ::= AMinus (AId X) (ANum b)

{{ fun st ⇒ b * (st Y + 1) + st X = a }};;

Y ::= APlus (AId Y) (ANum 1)

{{ fun st ⇒ b * st Y + st X = a }}

结束

{{ fun st ⇒ b * st Y + st X = a ∧ ~(b ≤ st X) }} ⇾

{{ fun st ⇒ b * st Y + st X = a ∧ (st X < b) }}

)%dcom。

定理 div_mod_dec_correct：∀a b，

dec_correct (div_mod_dec a b)。

证明。引入 a b。验证。

重写 mult_plus_distr_l。omega。

Qed.

```

### Parity

```

定义找奇偶性：com :=

当 (BLe (ANum 2) (AId X)) 时

X ::= AMinus (AId X) (ANum 2)

结束。

```

There are actually several ways to phrase the loop invariant for
    this program.  Here is one natural one, which leads to a rather
    long proof: 

```

归纳 ev：自然数 → 命题 :=

| ev_0 : ev O

| ev_SS : ∀n:nat, ev n → ev (S (S n))。

定义 find_parity_dec m : decorated :=

({{ fun st ⇒ st X = m}} ⇾

{{ fun st ⇒ st X ≤ m ∧ ev (m - st X) }}

{{'_x_'}}'_x_'END'_'{{'_x_'}}'">WHILE (BLe (ANum 2) (AId X)) DO

{{ fun st ⇒ (st X ≤ m ∧ ev (m - st X)) ∧ 2 ≤ st X }} ⇾

{{ fun st ⇒ st X - 2 ≤ m ∧ (ev (m - (st X - 2))) }}

X ::= AMinus (AId X) (ANum 2)

{{ fun st ⇒ st X ≤ m ∧ ev (m - st X) }}

END

{{ fun st ⇒ (st X ≤ m ∧ ev (m - st X)) ∧ st X < 2 }} ⇾

{{ fun st ⇒ st X=0 ↔ ev m }})%dcom。

引理 l[1] : ∀m n p，

p ≤ n →

n ≤ m →

m - (n - p) = m - n + p。

证明。intros。omega。Qed。

引理 l[2] : ∀m，

ev m →

ev (m + 2)。

证明。intros。重写 plus_comm。简化。constructor。assumption。Qed。

引理 l[3]' : ∀m，

ev m →

¬ev (S m)。

证明。对 m 进行归纳；intros H[1] H[2]。推导 H[2]。apply IHm。

推导 H[2]；subst；assumption。assumption。Qed。

引理 l[3] : ∀m，

1 ≤ m →

ev m →

ev (m - 1) →

False。

证明。intros。apply l[2] in H[1]。

断言 (G : m - 1 + 2 = S m)。清除 H[0] H[1]。omega。

在 H[1] 中重写 G。apply l[3]' 于 H[0]。apply H[0]。assumption。Qed。

定理 find_parity_correct : ∀m，

dec_correct (find_parity_dec m)。

证明。

intro m。验证；

(* 简化过于激进...稍微回退一点 *）

在 * 中折叠 (leb 2 (st X))；

尝试在 * 中重写 leb_iff；

尝试在 * 中重写 leb_iff_conv；eauto；尝试 omega。

- (* 不变量初始成立 *)

重写 minus_diag。constructor。

- (* 不变量保持 *)

重写 l[1]；尝试 assumption。

apply l[2]；assumption。

- (* 不变量足以推出结论 *)

(-> 方向) *)

重写 ← minus_n_O 于 H[2] 中。assumption。

- (* 不变量足以推出结论 *)

(<- 方向) *)

对 (st X) 进行分解为 [| [| n]]。

(* 根据 H[1]，X 只能是 0 或 1 *)

+ (* st X = 0 *)

reflexivity。

+ (* st X = 1 *)

apply l[3] 于 H；尝试 assumption。推导 H。

+ (* st X = 2 *)

清除 H[0] H[2]。（否则 omega 会混淆）

omega。

Qed。

```

Here is a more intuitive way of writing the invariant: 

```

定义 find_parity_dec' m : decorated :=

({{ fun st ⇒ st X = m}} ⇾

{{ fun st ⇒ ev (st X) ↔ ev m }}

{{'_x_'}}'_x_'END'_'{{'_x_'}}'">WHILE (BLe (ANum 2) (AId X)) DO

{{ fun st ⇒ (ev (st X) ↔ ev m) ∧ 2 ≤ st X }} ⇾

{{ fun st ⇒ (ev (st X - 2) ↔ ev m) }}

X ::= AMinus (AId X) (ANum 2)

{{ fun st ⇒ (ev (st X) ↔ ev m) }}

END

{{ fun st ⇒ (ev (st X) ↔ ev m) ∧ ~(2 ≤ st X) }} ⇾

{{ fun st ⇒ st X=0 ↔ ev m }})%dcom。

引理 l[4] : ∀m，

2 ≤ m →

(ev (m - 2) ↔ ev m)。

证明。

对 m 进行归纳；intros。split；intro；constructor。

对 m 进行分解。推导 H。assumption。assumption。Qed。

在 * 中重写 ← minus_n_O。分割；intro。

constructor。assumption。

推导 H[0]。assumption。

Qed。

定理 find_parity_correct' : ∀m，

dec_correct (find_parity_dec' m)。

证明。

intros m。验证；

(* 简化过于激进...稍微回退一点 *)

在 * 中折叠 (leb 2 (st X))；

尝试在 * 中重写 leb_iff；

尝试在 * 中重写 leb_iff_conv；intuition；eauto；尝试 omega。

- (* 不变量保持（部分 1） *)

在 H[0] 中重写 l[4]；eauto。

- (* 不变量保持（部分 2） *)

重写 l[4]；eauto。

- (* 不变量足以推出结论 *)

(-> 方向) *)

apply H[0]。constructor。

- (* 不变量足够强以暗示结论 *)

(<- 方向) *)

将 (st X) 拆分为 [| [| n]]。 (* 由 H[1] 可知 X 只能是 0 或 1 *)

+ (* st X = 0 *)

反射性。

+ (* st X = 1 *)

反转 H。

+ (* st X = 2 *)

清除 H[0] H H[3]。 (* 否则 omega 会混淆 *)

omega。

完成。

```

Here is the simplest invariant we've found for this program: 

```

定义 parity_dec m : decorated :=

({{ fun st ⇒ st X = m}} ⇾

{{ fun st ⇒ parity (st X) = parity m }}

{{'_x_'}}'_x_'END'_'{{'_x_'}}'">WHILE (BLe (ANum 2) (AId X)) DO

{{ fun st ⇒ parity (st X) = parity m ∧ 2 ≤ st X }} ⇾

{{ fun st ⇒ parity (st X - 2) = parity m }}

X ::= AMinus (AId X) (ANum 2)

{{ fun st ⇒ parity (st X) = parity m }}

END

{{ fun st ⇒ parity (st X) = parity m ∧ ~(2 ≤ st X) }} ⇾

{{ fun st ⇒ st X = parity m }})%dcom。

定理 parity_dec_correct : ∀m,

dec_correct (parity_dec m).

证明。

介绍。验证；

(* 简化过于激进...稍微回退一点 *)

在 * 中折叠 (leb 2 (st X))；

尝试在 * 中重写 leb_iff；完成；

尝试在 * 中重写 leb_iff_conv；自动；尝试 omega。

- (* 不变量保持不变 *)

重写 ← H。应用 parity_ge_2。假设。

- (* 足够强的不变量 *)

重写 ← H。对称。应用 parity_lt_2。假设。

完成。

```

### Square Roots

```

定义 sqrt_dec m : decorated := (

{{ fun st ⇒ st X = m }} ⇾

{{ fun st ⇒ st X = m ∧ 0*0 ≤ m }}

Z ::= ANum 0

{{ fun st ⇒ st X = m ∧ st Z*st Z ≤ m }};;

{{'_x_'}}'_x_'END'_'{{'_x_'}}'">WHILE BLe (AMult (APlus (AId Z) (ANum 1))

(APlus (AId Z) (ANum 1)))

(AId X) DO

{{ fun st ⇒ (st X = m ∧ st Z*st Z≤m)

∧ (st Z + 1)*(st Z + 1) ≤ st X }} ⇾

{{ fun st ⇒ st X = m ∧ (st Z+1)*(st Z+1)≤m }}

Z ::= APlus (AId Z) (ANum 1)

{{ fun st ⇒ st X = m ∧ st Z*st Z≤m }}

END

{{ fun st ⇒ (st X = m ∧ st Z*st Z≤m)

∧ ~((st Z + 1)*(st Z + 1) ≤ st X) }} ⇾

{{ fun st ⇒ st Z*st Z≤m ∧ m<(st Z+1)*(st Z+1) }})%dcom.

定理 sqrt_correct : ∀m,

dec_correct (sqrt_dec m).

证明。介绍 m. 验证。完成。

```

### Squaring

 Again, there are several ways of annotating the squaring program.
    The simplest variant we've found, square_simpler_dec, is given
    last. 

```

定义 square_dec (m : nat) : decorated := (

{{ fun st ⇒ st X = m }}

Y ::= AId X

{{ fun st ⇒ st X = m ∧ st Y = m }};;

Z ::= ANum 0

{{ fun st ⇒ st X = m ∧ st Y = m ∧ st Z = 0}} ⇾

{{ fun st ⇒ st Z + st X * st Y = m * m }};;

{{'_x_'}}'_x_'END'_'{{'_x_'}}'">WHILE BNot (BEq (AId Y) (ANum 0)) DO

{{ fun st ⇒ st Z + st X * st Y = m * m ∧ st Y ≠ 0 }} ⇾

{{ fun st ⇒ (st Z + st X) + st X * (st Y - 1) = m * m }}

Z ::= APlus (AId Z) (AId X)

{{ fun st ⇒ st Z + st X * (st Y - 1) = m * m }};;

Y ::= AMinus (AId Y) (ANum 1)

{{ fun st ⇒ st Z + st X * st Y = m * m }}

END

{{ fun st ⇒ st Z + st X * st Y = m * m ∧ st Y = 0 }} ⇾

{{ fun st ⇒ st Z = m * m }}

)%dcom。

定理 square_dec_correct : ∀m,

dec_correct (square_dec m).

证明。

介绍 n. 验证。

- (* 不变量保持不变 *)

将 (st Y) 拆分为 [| y']。应用 False_ind。应用 H[0]。

反射性。

简化。重写 ← minus_n_O。

断言 (G : ∀n m, n * S m = n + n * m)。{

清除。介绍。归纳 n. 反射性。简化。

重写 IHn。omega。}

重写 ← H。重写 G。重写 plus_assoc。完成。

完成。

定义 square_dec' (n : nat) : decorated := (

{{ fun st ⇒ True }}

X ::= ANum n

{{ fun st ⇒ st X = n }};;

Y ::= AId X

{{ fun st ⇒ st X = n ∧ st Y = n }};;

Z ::= ANum 0

{{ fun st ⇒ st X = n ∧ st Y = n ∧ st Z = 0 }} ⇾

{{ fun st ⇒ st Z = st X * (st X - st Y)

∧ st X = n ∧ st Y ≤ st X }};;

{{'_x_'}}'_x_'END'_'{{'_x_'}}'">WHILE BNot (BEq (AId Y) (ANum 0)) DO

{{ fun st ⇒ (st Z = st X * (st X - st Y)

∧ st X = n ∧ st Y ≤ st X)

∧ st Y ≠ 0 }}

Z ::= APlus (AId Z) (AId X)

{{ fun st ⇒ st Z = st X * (st X - (st Y - 1))

∧ st X = n ∧ st Y ≤ st X }};;

Y ::= AMinus (AId Y) (ANum 1)

{{ fun st ⇒ st Z = st X * (st X - st Y)

∧ st X = n ∧ st Y ≤ st X }}

END

{{ fun st ⇒ (st Z = st X * (st X - st Y)

∧ st X = n ∧ st Y ≤ st X)

∧ st Y = 0 }} ⇾

{{ fun st ⇒ st Z = n * n }}

)%dcom.

Theorem square_dec'_correct : ∀n,

dec_correct (square_dec' n).

Proof.

intro n. verify.

- (* invariant holds initially *)

rewrite minus_diag. omega.

- (* invariant preserved *) subst.

rewrite mult_minus_distr_l.

repeat rewrite mult_minus_distr_l. rewrite mult_1_r.

assert (G : ∀n m p,

m ≤ n → p ≤ m → n - (m - p) = n - m + p).

intros. omega.

rewrite G. reflexivity. apply mult_le_compat_l. assumption.

destruct (st Y). apply False_ind. apply H[0]. reflexivity.

clear. rewrite mult_succ_r. rewrite plus_comm.

apply le_plus_l.

- (* invariant + negation of guard imply

desired postcondition *)

rewrite ← minus_n_O. reflexivity.

Qed.

Definition square_simpler_dec (m : nat) : decorated := (

{{ fun st ⇒ st X = m }} ⇾

{{ fun st ⇒ 0 = 0*m ∧ st X = m }}

Y ::= ANum 0

{{ fun st ⇒ 0 = (st Y)*m ∧ st X = m }};;

Z ::= ANum 0

{{ fun st ⇒ st Z = (st Y)*m ∧ st X = m }}⇾

{{ fun st ⇒ st Z = (st Y)*m ∧ st X = m }};;

{{'_x_'}}'_x_'END'_'{{'_x_'}}'">WHILE BNot (BEq (AId Y) (AId X)) DO

{{ fun st ⇒ (st Z = (st Y)*m ∧ st X = m)

∧ st Y ≠ st X }} ⇾

{{ fun st ⇒ st Z + st X = ((st Y) + 1)*m ∧ st X = m }}

Z ::= APlus (AId Z) (AId X)

{{ fun st ⇒ st Z = ((st Y) + 1)*m ∧ st X = m }};;

Y ::= APlus (AId Y) (ANum 1)

{{ fun st ⇒ st Z = (st Y)*m ∧ st X = m }}

END

{{ fun st ⇒ (st Z = (st Y)*m ∧ st X = m) ∧ st Y = st X }} ⇾

{{ fun st ⇒ st Z = m*m }}

)%dcom.

Theorem square_simpler_dec_correct : ∀m,

dec_correct (square_simpler_dec m).

Proof.

intro m. verify.

rewrite mult_plus_distr_r. simpl. rewrite ← plus_n_O.

reflexivity.

Qed.

```

### Two loops

```

Definition two_loops_dec (a b c : nat) : decorated :=

( {{ fun st ⇒ True }} ⇾

{{ fun st ⇒ c = 0 + c ∧ 0 = 0 }}

X ::= ANum 0

{{ fun st ⇒ c = st X + c ∧ 0 = 0 }};;

Y ::= ANum 0

{{ fun st ⇒ c = st X + c ∧ st Y = 0 }};;

Z ::= ANum c

{{ fun st ⇒ st Z = st X + c ∧ st Y = 0 }};;

{{'_x_'}}'_x_'END'_'{{'_x_'}}'">WHILE BNot (BEq (AId X) (ANum a)) DO

{{ fun st ⇒ (st Z = st X + c ∧ st Y = 0) ∧ st X ≠ a }} ⇾

{{ fun st ⇒ st Z + 1 = st X + 1 + c ∧ st Y = 0 }}

X ::= APlus (AId X) (ANum 1)

{{ fun st ⇒ st Z + 1 = st X + c ∧ st Y = 0 }};;

Z ::= APlus (AId Z) (ANum 1)

{{ fun st ⇒ st Z = st X + c ∧ st Y = 0 }}

END

{{ fun st ⇒ (st Z = st X + c ∧ st Y = 0) ∧ st X = a }} ⇾

{{ fun st ⇒ st Z = a + st Y + c }};;

{{'_x_'}}'_x_'END'_'{{'_x_'}}'">WHILE BNot (BEq (AId Y) (ANum b)) DO

{{ fun st ⇒ st Z = a + st Y + c ∧ st Y ≠ b }} ⇾

{{ fun st ⇒ st Z + 1 = a + st Y + 1 + c }}

Y ::= APlus (AId Y) (ANum 1)

{{ fun st ⇒ st Z + 1 = a + st Y + c }};;

Z ::= APlus (AId Z) (ANum 1)

{{ fun st ⇒ st Z = a + st Y + c }}

END

{{ fun st ⇒ (st Z = a + st Y + c) ∧ st Y = b }} ⇾

{{ fun st ⇒ st Z = a + b + c }}

)%dcom.

Theorem two_loops_correct : ∀a b c,

dec_correct (two_loops_dec a b c).

Proof. intros a b c. verify. Qed.

```

### Power Series

```

Fixpoint pow2 n :=

match n with

| 0 ⇒ 1

| S n' ⇒ 2 * (pow2 n')

end.

Definition dpow2_down n :=

( {{ fun st ⇒ True }} ⇾

{{ fun st ⇒ 1 = (pow2 (0 + 1))-1 ∧ 1 = pow2 0 }}

X ::= ANum 0

{{ fun st ⇒ 1 = (pow2 (0 + 1))-1 ∧ 1 = pow2 (st X) }};;

Y ::= ANum 1

{{ fun st ⇒ st Y = (pow2 (st X + 1))-1 ∧ 1 = pow2 (st X) }};;

Z ::= ANum 1

{{ fun st ⇒ st Y = (pow2 (st X + 1))-1 ∧ st Z = pow2 (st X) }};;

{{'_x_'}}'_x_'END'_'{{'_x_'}}'">WHILE BNot (BEq (AId X) (ANum n)) DO

{{ fun st ⇒ (st Y = (pow2 (st X + 1))-1 ∧ st Z = pow2 (st X))

∧ st X ≠ n }} ⇾

{{ fun st ⇒ st Y + 2 * st Z = (pow2 (st X + 2))-1

∧ 2 * st Z = pow2 (st X + 1) }}

Z ::= AMult (ANum 2) (AId Z)

{{ fun st ⇒ st Y + st Z = (pow2 (st X + 2))-1

∧ st Z = pow2 (st X + 1) }};;

Y ::= APlus (AId Y) (AId Z)

{{ fun st ⇒ st Y = (pow2 (st X + 2))-1

∧ st Z = pow2 (st X + 1) }};;

X ::= APlus (AId X) (ANum 1)

{{ fun st ⇒ st Y = (pow2 (st X + 1))-1

∧ st Z = pow2 (st X) }}

END

{{ fun st ⇒ (st Y = (pow2 (st X + 1))-1 ∧ st Z = pow2 (st X))

∧ st X = n }} ⇾

{{ fun st ⇒ st Y = pow2 (n+1) - 1 }}

)%dcom.

Lemma pow2_plus_1 : ∀n,

pow2 (n+1) = pow2 n + pow2 n.

Proof. induction n; simpl. reflexivity. omega. Qed.

Lemma pow2_le_1 : ∀n, pow2 n ≥ 1.

Proof. induction n. simpl. constructor. simpl. omega. Qed.

Theorem dpow2_down_correct : ∀n,

dec_correct (dpow2_down n).

Proof.

intro m. verify.

- (* 1 *)

rewrite pow2_plus_1. rewrite ← H[0]. reflexivity.

- (* 2 *)

rewrite ← plus_n_O.

rewrite ← pow2_plus_1. remember (st X) as n.

replace (pow2 (n + 1) - 1 + pow2 (n + 1))

with (pow2 (n + 1) + pow2 (n + 1) - 1) by omega.

rewrite ← pow2_plus_1.

replace (n + 1 + 1) with (n + 2) by omega.

reflexivity.

- (* 3 *)

rewrite ← plus_n_O. rewrite ← pow2_plus_1.

reflexivity.

- (* 4 *)

replace (st X + 1 + 1) with (st X + 2) by omega.

reflexivity.

Qed.

```

Further Exercises 

#### Exercise: 3 stars, advanced (slow_assignment_dec)

 In the slow_assignment exercise above, we saw a roundabout way
    of assigning a number currently stored in X to the variable Y:
    start Y at 0, then decrement X until it hits 0,
    incrementing Y at each step.  Write a formal version of this
    decorated program and prove it correct. 

```

Example slow_assignment_dec (m:nat) : decorated

(* REPLACE THIS LINE WITH ":= _your_definition_." *) Admitted.

Theorem slow_assignment_dec_correct : ∀m,

dec_correct (slow_assignment_dec m).

Proof. (* FILL IN HERE *) Admitted.

```

☐ 

#### Exercise: 4 stars, advancedM (factorial_dec)

 Remember the factorial function we worked with before: 

```

Fixpoint real_fact (n:nat) : nat :=

match n with

| O ⇒ 1

| S n' ⇒ n * (real_fact n')

end.

```

Following the pattern of subtract_slowly_dec, write a decorated
    program factorial_dec that implements the factorial function and
    prove it correct as factorial_dec_correct. 

```

(* FILL IN HERE *)

```

☐ 

#### Exercise: 4 stars, advanced, optional (fib_eqn)

 The Fibonacci function is usually written like this:

```

Fixpoint fib n :=

match n with

| 0 ⇒ 1

| 1 ⇒ 1

| _ ⇒ fib (pred n) + fib (pred (pred n))

end.

```

   This doesn't pass Coq's termination checker, but here is a 
   slightly clunkier definition that does: 

```

Fixpoint fib n :=

match n with

| 0 ⇒ 1

| S n' ⇒ match n' with

| 0 ⇒ 1

| S n'' ⇒ fib n' + fib n''

end

end.

```

Prove that fib satisfies the following equation: 

```

Lemma fib_eqn : ∀n,

n > 0 →

fib n + fib (Init.Nat.pred n) = fib (n + 1).

Proof.

(* FILL IN HERE *) Admitted.

```

☐ 

#### Exercise: 4 stars, advanced, optional (fib)

 The following Imp program leaves the value of fib n in the
    variable Y when it terminates: 

```

X ::= 1;;

Y ::= 1;;

Z ::= 1;;

WHILE X ≠ n+1 DO

T ::= Z;

Z ::= Z + Y;;

Y ::= T;;

X ::= X + 1

END

```

    Fill in the following definition of dfib and prove that it 
    satisfies this specification:

```

{{True}} dfib {{ Y = fib n }}

```

```

Definition T : id := Id "T".

Definition dfib (n:nat) : decorated

(* REPLACE THIS LINE WITH ":= _your_definition_." *). Admitted.

定理 dfib_correct : ∀n，

dec_correct (dfib n)。

(*请在此处填写*) 已验证。

```

☐ 

#### Exercise: 5 stars, advanced, optional (improve_dcom)

 The formal decorated programs defined in this section are intended 
    to look as similar as possible to the informal ones defined earlier
    in the chapter.  If we drop this requirement, we can eliminate
    almost all annotations, just requiring final postconditions and 
    loop invariants to be provided explicitly.  Do this — i.e., define a 
    new version of dcom with as few annotations as possible and adapt the
    rest of the formal development leading up to the verification_correct 
    theorem. 

```

(*请在此处填写*)

```

☐ 

#### Exercise: 4 stars, advanced, optional (implement_dcom)

 Adapt the parser for Imp presented in chapter ImpParser 
    to parse decorated commands (either ours or the ones you defined
    in the previous exercise). 

```

(*请在此处填写*)

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
