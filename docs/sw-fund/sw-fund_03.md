# 归纳法证明

```

    Before getting started, we need to import all of our
    definitions from the previous chapter:

```

需要导出基础知识。

```

    For the Require Export to work, you first need to use
    coqc to compile Basics.v into Basics.vo.  This is like
    making a .class file from a .java file, or a .o file from a .c
    file.  There are two ways to do it:

*   In CoqIDE: 

     Open Basics.v. In the "Compile" menu, click on "Compile Buffer". 

*   From the command line: 

    coqc Basics.v

    If you have trouble (e.g., if you get complaints about missing
   identifiers later in the file), it may be because the "load path"
   for Coq is not set up correctly.  The Print LoadPath. command may
   be helpful in sorting out such issues.

```

# 归纳证明

    我们在上一章证明了 0 是一个中性元素

    对于+在左边，使用基于简单论据的简单论证

    简化。我们还观察到证明它是事实

    也是一个中性元素在*右边*...

```
Theorem plus_n_O_firsttry : ∀n:nat,
  n = n + 0.

```

    ... 不能以同样简单的方式完成。只需应用

reflexivity 不起作用，因为 n + 0 中的 n 是任意的

未知数，因此+的定义中的匹配不能

简化。

```
Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

```

    并且通过使用 destruct n 进行情况推理并不能让我们得到太多

    进一步：在假设 n = 0 的情况分析分支中

    进行得很好，但在 n = S n'的分支中，我们

    以完全相同的方式陷入困境。

```
Theorem plus_n_O_secondtry : ∀n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.

```

    我们可以使用 destruct n'再走一步，但是，

    由于 n 可以任意大，如果我们继续这样下去

    我们永远也无法完成。

    要证明关于数字，列表和其他有趣事实

    在归纳定义的集合中，我们通常需要更强大的

    情况推理原则：*归纳*。

    回想（从高中，离散数学课程等）这个

    *自然数归纳原理*：如果 P(n)是某个

    涉及自然数 n 的命题，我们想要展示

    对于所有数字 n，我们可以这样推理：

+   表明 P(O)成立；

+   表明，对于任何 n'，如果 P(n')成立，则 P(S n')也成立；

+   得出结论，对于所有 n，P(n)都成立。

    在 Coq 中，步骤是相同的：我们从证明目标开始

    P(n)对于所有 n 并将其分解（通过应用归纳

    策略）成两个单独的子目标：一个我们必须展示 P(O)

    另一个我们必须展示 P(n') → P(S n')的地方。这是如何

    这对于手头的定理有效：

```
Theorem plus_n_O : ∀n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite ← IHn'. reflexivity. Qed.

```

    与 destruct 类似，归纳策略需要一个 as...

    指定要引入的变量的名称的子句

    在子目标中。由于有两个子目标，as...子句

    有两部分，用|分隔。（严格来说，我们可以省略

    as...子句，Coq 将为我们选择名称。实际上，

    这是一个坏主意，因为 Coq 的自动选择往往是

    令人困惑。）

    在第一个子目标中，n 被替换为 0。没有新变量

    被引入（因此 as...的第一部分为空），并且

    目标变为 0 + 0 = 0，通过简化得出。

    在第二个子目标中，n 被替换为 S n'，而

    假设 n' + 0 = n'被添加到上下文中，并命名为

    IHn'（即 n'的归纳假设）。这两个名称

    在 as...子句的第二部分中指定。目标

    在这种情况下变为(S n') + 0 = S n'，简化为

    S (n' + 0) = S n'，这又是由 IHn'得出的。

```
Theorem minus_diag : ∀n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite → IHn'. reflexivity. Qed.

```

    （在这些证明中使用 intros 策略实际上是

    冗余。当应用于包含量化的目标时

    变量，归纳策略将自动移动它们

    根据需要将其引入上下文。）

#### 练习：2 星，推荐（basic_induction）

    使用归纳证明以下内容。您可能需要先前

    已经证明的结果。

```
Theorem mult_0_r : ∀n:nat,
  n * 0 = 0.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_n_Sm : ∀n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_comm : ∀n m : nat,
  n + m = m + n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_assoc : ∀n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：2 星（double_plus）

    考虑以下函数，它将其参数加倍：

```
Fixpoint double (n:nat) :=
  match n with
  | O ⇒ O
  | S n' ⇒ S (S (double n'))
  end.

```

    使用归纳来证明关于 double 的这个简单事实：

```
Lemma double_plus : ∀n, double n = n + n .
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：2 星，可选（evenb_S）

    我们定义 evenb n 的一个不方便的方面是

    n - 2 的递归调用。这使得关于 evenb n 的证明

    当在 n 上归纳时更难，因为我们可能需要一个

    对 n - 2 的归纳假设。以下引理给出了

    evenb（S n）的另一种更好的特征化

    使用归纳：

```
Theorem evenb_S : ∀n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：1 星 M（destruct_induction）

    简要解释破坏之间的差异

    和归纳。

    （*在这里填写*）

    ☐

```

# Proofs Within Proofs

    In Coq, as in informal mathematics, large proofs are often
    broken into a sequence of theorems, with later proofs referring to
    earlier theorems.  But sometimes a proof will require some
    miscellaneous fact that is too trivial and of too little general
    interest to bother giving it its own top-level name.  In such
    cases, it is convenient to be able to simply state and prove the
    needed "sub-theorem" right at the point where it is used.  The
    assert tactic allows us to do this.  For example, our earlier
    proof of the mult_0_plus theorem referred to a previous theorem
    named plus_O_n.  We could instead use assert to state and
    prove plus_O_n in-line:

```

定理 mult_0_plus'：∀n m：自然数，

（0 + n）* m = n * m。

证明。

引入 n m。

断言（H：0 + n = n）。{自反性。}

重写 → H。

自反性。Qed。

```

    The assert tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with H: we name the
    assertion H.  (We can also name the assertion with as just as
    we did above with destruct and induction, i.e., assert (0 + n = n) as H.)  Note that we surround the proof of this assertion
    with curly braces { ... }, both for readability and so that,
    when using Coq interactively, we can see more easily when we have
    finished this sub-proof.  The second goal is the same as the one
    at the point where we invoke assert except that, in the context,
    we now have the assumption H that 0 + n = n.  That is,
    assert generates one subgoal where we must prove the asserted
    fact and a second subgoal where we can use the asserted fact to
    make progress on whatever we were trying to prove in the first
    place. 

    Another example of assert... 

    For example, suppose we want to prove that (n + m) + (p + q) = (m + n) + (p + q). The only difference between the two sides of
    the = is that the arguments m and n to the first inner +
    are swapped, so it seems we should be able to use the
    commutativity of addition (plus_comm) to rewrite one into the
    other.  However, the rewrite tactic is not very smart about
    *where* it applies the rewrite.  There are three uses of + here,
    and it turns out that doing rewrite → plus_comm will affect
    only the *outer* one...

```

定理 plus_rearrange_firsttry：∀n m p q：自然数，

（n + m）+（p + q）=（m + n）+（p + q）。

证明。

引入 n m p q。

（*我们只需要交换（n + m）为（m + n）...似乎 plus_comm 应该能解决问题！*）

重写 → plus_comm。

（*不起作用...Coq 重写了错误的加法！*）

放弃。

```

    To use plus_comm at the point where we need it, we can introduce
    a local lemma stating that n + m = m + n (for the particular m
    and n that we are talking about here), prove this lemma using
    plus_comm, and then use it to do the desired rewrite.

```

定理 plus_rearrange：∀n m p q：自然数，

（n + m）+（p + q）=（m + n）+（p + q）。

证明。

引入 n m p q。

断言（H：n + m = m + n）。

{重写 → plus_comm。自反性。} 

重写 → H。自反性。Qed。

```

# Formal vs. Informal Proof

      "*Informal proofs are algorithms; formal proofs are code*."

    What constitutes a successful proof of a mathematical claim?
    The question has challenged philosophers for millennia, but a
    rough and ready definition could be this: A proof of a
    mathematical proposition P is a written (or spoken) text that
    instills in the reader or hearer the certainty that P is true —
    an unassailable argument for the truth of P.  That is, a proof
    is an act of communication.

    Acts of communication may involve different sorts of readers.  On
    one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is that P can be mechanically
    derived from a certain set of formal logical rules, and the proof
    is a recipe that guides the program in checking this fact.  Such
    recipes are *formal* proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    and will thus necessarily be *informal*.  Here, the criteria for
    success are less clearly specified.  A "valid" proof is one that
    makes the reader believe P.  But the same proof may be read by
    many different readers, some of whom may be convinced by a
    particular way of phrasing the argument, while others may not be.
    Some readers may be particularly pedantic, inexperienced, or just
    plain thick-headed; the only way to convince them will be to make
    the argument in painstaking detail.  But other readers, more
    familiar in the area, may find all this detail so overwhelming
    that they lose the overall thread; all they want is to be told the
    main ideas, since it is easier for them to fill in the details for
    themselves than to wade through a written presentation of them.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.

    In practice, however, mathematicians have developed a rich set of
    conventions and idioms for writing about complex mathematical
    objects that — at least within a certain community — make
    communication fairly reliable.  The conventions of this stylized
    form of communication give a fairly clear standard for judging
    proofs good or bad.

    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can
    completely forget about informal ones!  Formal proofs are useful
    in many ways, but they are *not* very efficient ways of
    communicating ideas between human beings. 

    For example, here is a proof that addition is associative:

```

定理 plus_assoc'：∀n m p：自然数，

n +（m + p）=（n + m）+ p。

证明。引入 n m p。归纳 n 为 [| n' IHn']。自反性。

简化。重写 → IHn'。自反性。Qed。

```

    Coq is perfectly happy with this.  For a human, however, it
    is difficult to make much sense of it.  We can use comments and
    bullets to show the structure a little more clearly...

```

定理 plus_assoc''：∀n m p：自然数，

n +（m + p）=（n + m）+ p。

证明。

引入 n m p。归纳 n 为 [| n' IHn']。

- （*n = 0*）

自反性。

- （*n = S n'*）

简化。重写 → IHn'。自反性。Qed。

```

    ... and if you're used to Coq you may be able to step
    through the tactics one after the other in your mind and imagine
    the state of the context and goal stack at each point, but if the
    proof were even a little bit more complicated this would be next
    to impossible.

    A (pedantic) mathematician might write the proof something like
    this: 

*   *Theorem*: For any n, m and p, 

    ```

    n + (m + p) = (n + m) + p。

    *证明*：通过对 n 进行归纳。

    +   首先，假设 n = 0。我们必须展示

        ```
          0 + (m + p) = (0 + m) + p.

         This follows directly from the definition of +. 

        ```

    +   接下来，假设 n = S n'，其中

        ```
          n' + (m + p) = (n' + m) + p.

         We must show 

        ```

        （S n'）+（m + p）=（（S n'）+ m）+ p。

        通过 + 的定义，这可以从

        ```
          S (n' + (m + p)) = S ((n' + m) + p),

         which is immediate from the induction hypothesis. *Qed*.
        ```

        ```

        ```

    ```

    The overall form of the proof is basically similar, and of
    course this is no accident: Coq has been designed so that its
    induction tactic generates the same sub-goals, in the same
    order, as the bullet points that a mathematician would write.  But
    there are significant differences of detail: the formal proof is
    much more explicit in some ways (e.g., the use of reflexivity)
    but much less explicit in others (in particular, the "proof state"
    at any given point in the Coq proof is completely implicit,
    whereas the informal proof reminds the reader several times where
    things stand). 

#### Exercise: 2 stars, advanced, recommendedM (plus_comm_informal)

    Translate your solution for plus_comm into an informal proof:

    Theorem: Addition is commutative.

    Proof: (* FILL IN HERE *)

    ☐ 

#### Exercise: 2 stars, optionalM (beq_nat_refl_informal)

    Write an informal proof of the following theorem, using the
    informal proof of plus_assoc as a model.  Don't just
    paraphrase the Coq tactics into English!

    Theorem: true = beq_nat n n for any n.

    Proof: (* FILL IN HERE *)

    ☐

```

# 更多练习

#### 练习：3 星，推荐（mult_comm）

    使用断言来帮助证明这个定理。你不应该需要

    使用对 plus_swap 进行归纳。

```
Theorem plus_swap : ∀n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.

```

    现在证明乘法的交换律。（你可能会

    需要定义和��明一个单独的辅助定理来使用

    在这个证明中。你可能会发现 plus_swap 很有用

    方便。）

```
Theorem mult_comm : ∀m n : nat,
  m * n = n * m.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星，可选（more_exercises）

    拿一张纸。对于以下每个定理，首先

    *思考*是否（a）只能使用

    简化和重写，（b）还需要案例

    分析（破坏），或（c）还需要归纳。写

    预测下降。然后填写证明。（没有必要

    提交你的纸张；这只是为了鼓励你

    在黑客之前反思！）

```
Theorem leb_refl : ∀n:nat,
  true = leb n n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem zero_nbeq_S : ∀n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem andb_false_r : ∀b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_ble_compat_l : ∀n m p : nat,
  leb n m = true → leb (p + n) (p + m) = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem S_nbeq_0 : ∀n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_1_l : ∀n:nat, 1 * n = n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem all3_spec : ∀b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_plus_distr_r : ∀n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_assoc : ∀n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：2 星，可选（beq_nat_refl）

    证明以下定理。（将真放在左手边

    等式的一侧可能看起来奇怪，但这就是定理的

    在 Coq 标准库中规定，因此我们也遵循。重写

    无论以哪种方式陈述，都可以正常工作，因此我们不会遇到问题。

    使用定理无论如何陈述，都可以正常工作。）

```
Theorem beq_nat_refl : ∀n : nat,
  true = beq_nat n n.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：2 星，可选（plus_swap'）

    替换策略允许您指定特定的子项

重写以及你想要它被重写成的内容：用 (t) 替换 (u)

用表达式 u 替换目标中表达式 t（所有副本）。

u，并生成 t = u 作为一个额外的子目标。这通常

当一个普通的重写作用在目标的错误部分时，这是有用的。

    使用 replace 策略来证明 plus_swap'，就像

不需要使用断言的 plus_swap（n + m = m + n）。

```
Theorem plus_swap' : ∀n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

#### 练习：3 星，推荐（binary_commute）

    回想一下你写的 incr 和 bin_to_nat 函数

    在 Basics 章节中编写的二进制练习中。 证明

    下面的图表是可交换的：

```
                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

    That is, incrementing a binary number and then converting it to
    a (unary) natural number yields the same result as first converting
    it to a natural number and then incrementing.
    Name your theorem bin_to_nat_pres_incr ("pres" for "preserves").

    Before you start working on this exercise, copy the definitions
    from your solution to the binary exercise here so that this file
    can be graded on its own.  If you want to change your original
    definitions to make the property easier to prove, feel free to
    do so!

```

(* 填充在这里 *)

```

    ☐ 

#### Exercise: 5 stars, advancedM (binary_inverse)

    This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    there to complete this one; please copy them to this file to make
    it self contained for grading.

    (a) First, write a function to convert natural numbers to binary
        numbers.  Then prove that starting with any natural number,
        converting to binary, then converting back yields the same
        natural number you started with.

    (b) You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, this is not true!
        Explain what the problem is.

    (c) Define a "direct" normalization function — i.e., a function
        normalize from binary numbers to binary numbers such that,
        for any binary number b, converting to a natural and then back
        to binary yields (normalize b).  Prove it.  (Warning: This
        part is tricky!)

    Again, feel free to change your earlier definitions if this helps
    here.

```

(* 填充在这里 *)

```

    ☐ 

```

```

```

```

```
