# 引用类型 可变引用

```

    Up to this point, we have considered a variety of *pure*
    language features, including functional abstraction, basic types
    such as numbers and booleans, and structured types such as records
    and variants.  These features form the backbone of most
    programming languages — including purely functional languages
    such as Haskell and "mostly functional" languages such as ML, as
    well as imperative languages such as C and object-oriented
    languages such as Java, C#, and Scala.

    However, most practical languages also include various *impure*
    features that cannot be described in the simple semantic framework
    we have used so far.  In particular, besides just yielding
    results, computation in these languages may assign to mutable
    variables (reference cells, arrays, mutable record fields, etc.);
    perform input and output to files, displays, or network
    connections; make non-local transfers of control via exceptions,
    jumps, or continuations; engage in inter-process synchronization
    and communication; and so on.  In the literature on programming
    languages, such "side effects" of computation are collectively
    referred to as *computational effects*.

    In this chapter, we'll see how one sort of computational effect —
    mutable references — can be added to the calculi we have studied.
    The main extension will be dealing explicitly with a *store* (or
    *heap*) and *pointers* that name store locations.  This extension
    is fairly straightforward to define; the most interesting part is
    the refinement we need to make to the statement of the type
    preservation theorem.

```

要求导入 Coq.Arith.Arith。

要求导入 Coq.omega.Omega。

要求导入 Coq.Lists.List。

导入 ListNotations。

要求导入 Maps。

要求导入 Smallstep。

```

# Definitions

    Pretty much every programming language provides some form of
    assignment operation that changes the contents of a previously
    allocated piece of storage.  (Coq's internal language Gallina is a
    rare exception!)

    In some languages — notably ML and its relatives — the
    mechanisms for name-binding and those for assignment are kept
    separate.  We can have a variable x whose *value* is the number
    5, or we can have a variable y whose value is a
    *reference* (or *pointer*) to a mutable cell whose current
    contents is 5.  These are different things, and the difference
    is visible to the programmer.  We can add x to another number,
    but not assign to it.  We can use y to assign a new value to the
    cell that it points to (by writing y:=84), but we cannot use y
    directly as an argument to an operation like +.  Instead, we
    must explicitly *dereference* it, writing !y to obtain its
    current contents.

    In most other languages — in particular, in all members of the C
    family, including Java — *every* variable name refers to a
    mutable cell, and the operation of dereferencing a variable to
    obtain its current contents is implicit.

    For purposes of formal study, it is useful to keep these
    mechanisms separate.  The development in this chapter will closely
    follow ML's model.  Applying the lessons learned here to C-like
    languages is a straightforward matter of collapsing some
    distinctions and rendering some operations such as dereferencing
    implicit instead of explicit.

```

# 语法

    在本章中，我们研究向

    具有自然数的简单类型 λ 演算。

```
Module STLCRef.

```

    引用的基本操作是 *分配*，

    *解引用* 和 *赋值*。

+   要分配一个引用，我们使用 ref 运算符，提供新单元格的初始值。例如，ref 5 创建一个包含值 5 的新单元格，并简化为对该单元格的引用。

+   要读取此单元格的当前值，我们使用解引用运算符！；例如，!(ref 5) 简化为 5。

+   要更改存储在单元格中的值，我们使用赋值运算符。如果 r 是一个引用，r := 7 将在由 r 引用的单元格中存储值 7。

```

### Types

    We start with the simply typed lambda calculus over the
    natural numbers. Besides the base natural number type and arrow
    types, we need to add two more types to deal with
    references. First, we need the *unit type*, which we will use as
    the result type of an assignment operation.  We then add
    *reference types*. 

    If T is a type, then Ref T is the type of references to
    cells holding values of type T.

```

T ::= 自然数

| 单元

| T → T

| 引用 T

```
Inductive ty : Type :=
  | TNat   : ty
  | TUnit  : ty
  | TArrow : ty → ty → ty
  | TRef   : ty → ty.

```

### 术语

    除了变量、抽象、应用程序之外，

    与自然数相关的术语和单元，我们需要四种更多的排序

    为了处理可变引用的术语：

```
      t ::= ...              Terms
          | ref t              allocation
          | !t                 dereference
          | t := t             assignment
          | l                  location

```

```
Inductive tm  : Type :=
  (* STLC with numbers: *)
  | tvar    : id → tm
  | tapp    : tm → tm → tm
  | tabs    : id → ty → tm → tm
  | tnat    : nat → tm
  | tsucc   : tm → tm
  | tpred   : tm → tm
  | tmult   : tm → tm → tm
  | tif0    : tm → tm → tm → tm
  (* New terms: *)
  | tunit   : tm
  | tref    : tm → tm
  | tderef  : tm → tm
  | tassign : tm → tm → tm
  | tloc    : nat → tm.

```

    直观上：

+   ref t（形式上，tref t）分配一个具有值 t 的新引用单元格，并简化为新分配单元格的位置；

+   !t（形式上，tderef t）简化为由 t 引用的单元格的内容；

+   t[1] := t[2]（形式上，tassign t[1] t[2]）将 t[2] 分配给由 t[1] 引用的单元格；以及

+   l（形式上，tloc l）是指向位置 l 处单元格的引用。我们稍后会讨论位置。

    在非正式示例中，我们还将自由使用扩展

    在 MoreStlc 章节中开发的 STLC 的一部分；然而，为了保持

    证明小，我们不会在这里再次正式化它们。（它

    这样做将很容易，因为没有非常有趣的

    这些特��与引用之间的交互。）

```

### Typing (Preview)

    Informally, the typing rules for allocation, dereferencing, and
    assignment will look like this:

| 
             Γ ⊢ t[1] : T[1]
           | 
             (T_Ref)  
           |
| 
             

* * *

           |
| 
             Γ ⊢ ref t[1] : Ref T[1]
           | 
          |

| 
             Γ ⊢ t[1] : Ref T[11]
           | 
             (T_Deref)  
           |
| 
             

* * *

           |
| 
             Γ ⊢ !t[1] : T[11]
           | 
          |

| 
             Γ ⊢ t[1] : Ref T[11]
           | 
          |
| 
             Γ ⊢ t[2] : T[11]
           | 
             (T_Assign)  
           |
| 
             

* * *

           |
| 
             Γ ⊢ t[1] := t[2] : Unit
           | 
          |

    The rule for locations will require a bit more machinery, and this
    will motivate some changes to the other rules; we'll come back to
    this later.

```

### 值和替换

    除了抽象和数字，我们还有两种新类型的值：

    单元值和位置。

```
Inductive value : tm → Prop :=
  | v_abs  : ∀x T t,
      value (tabs x T t)
  | v_nat : ∀n,
      value (tnat n)
  | v_unit :
      value tunit
  | v_loc : ∀l,
      value (tloc l).

Hint Constructors value.

```

    扩展替换以处理术语的新语法是

    直接。

```
Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x'       ⇒
      if beq_id x x' then s else t
  | tapp t[1] t[2]    ⇒
      tapp (subst x s t[1]) (subst x s t[2])
  | tabs x' T t[1]  ⇒
      if beq_id x x' then t else tabs x' T (subst x s t[1])
  | tnat n        ⇒
      t
  | tsucc t[1]      ⇒
      tsucc (subst x s t[1])
  | tpred t[1]      ⇒
      tpred (subst x s t[1])
  | tmult t[1] t[2]   ⇒
      tmult (subst x s t[1]) (subst x s t[2])
  | tif0 t[1] t[2] t[3] ⇒
      tif0 (subst x s t[1]) (subst x s t[2]) (subst x s t[3])
  | tunit         ⇒
      t
  | tref t[1]       ⇒
      tref (subst x s t[1])
  | tderef t[1]     ⇒
      tderef (subst x s t[1])
  | tassign t[1] t[2] ⇒
      tassign (subst x s t[1]) (subst x s t[2])
  | tloc _        ⇒
      t
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

```

# 实用语

```

## Side Effects and Sequencing

    The fact that we've chosen the result of an assignment
    expression to be the trivial value unit allows a nice
    abbreviation for *sequencing*.  For example, we can write

```

    r:=succ(!r); !r

```

    as an abbreviation for

```

    (λx:Unit. !r) (r:=succ(!r)).

```

    This has the effect of reducing two expressions in order and
    returning the value of the second.  Restricting the type of the
    first expression to Unit helps the typechecker to catch some
    silly errors by permitting us to throw away the first value only
    if it is really guaranteed to be trivial.

    Notice that, if the second expression is also an assignment, then
    the type of the whole sequence will be Unit, so we can validly
    place it to the left of another ; to build longer sequences of
    assignments:

```

    r:=succ(!r); r:=succ(!r); r:=succ(!r); r:=succ(!r); !r

```

    Formally, we introduce sequencing as a *derived form* tseq that expands into an abstraction and an application.

```

定义 tseq t[1] t[2] :=

tapp (tabs (Id "x") TUnit t[2]) t[1].

```

## References and Aliasing

    It is important to bear in mind the difference between the
    *reference* that is bound to some variable r and the *cell* 
    in the store that is pointed to by this reference.

    If we make a copy of r, for example by binding its value to
    another variable s, what gets copied is only the *reference*,
    not the contents of the cell itself.

    For example, after reducing

```

    让 r = ref 5 然后

    让 s = r 然后

    s := 82;

    (!r)+1

```

    the cell referenced by r will contain the value 82, while the
    result of the whole expression will be 83.  The references r
    and s are said to be *aliases* for the same cell.

    The possibility of aliasing can make programs with references
    quite tricky to reason about.  For example, the expression

```

    r := 5; r := !s

```

    assigns 5 to r and then immediately overwrites it with s's
    current value; this has exactly the same effect as the single
    assignment

```

    r := !s

```

    *unless* we happen to do it in a context where r and s are
    aliases for the same cell!

```

## 共享状态

    当然，别名也是使引用

    有用。特别是，它允许我们建立“隐式

    通信通道" — 不同部分之间的共享状态 —

    程序的一个例子。例如，假设我们定义一个引用单元格和

    两个操作其内容的函数：

```
      let c = ref 0 in
      let incc = λ_:Unit. (c := succ (!c); !c) in
      let decc = λ_:Unit. (c := pred (!c); !c) in
      ...

```

    请注意，由于它们的参数类型为 Unit，因此

    作为抽象定义中的抽象的参数

    decc 不提供任何有用信息给

    这些函数（使用通配符 _ 作为绑定的名称

    变量是这些的目的的提醒）。相反，它们的目的是

    抽象是“减慢”函数执行的

    主体。由于函数抽象是值，两个 let 都是

    通过简单地将这些函数绑定到名称 incc 和

    decc，而不是通过实际增加或减少 c。

    后来，对这些函数中的一个进行 caddll 将导致其主体

    被执行一次并对其进行适当的突变

    c。这样的函数通常被称为*thunks*。

    在这些声明的上下文中，调用 incc 会导致

    对 c 的更改可以通过调用 decc 观察到。对于

    例如，如果我们用（incc unit; incc unit; decc unit）替换...，整个程序的结果将是 1。

```

## Objects

    We can go a step further and write a *function* that creates c,
    incc, and decc, packages incc and decc together into a
    record, and returns this record:

```

    newcounter =

        λ_:Unit。

            让 c = ref 0 in

            让 incc = λ_:Unit。 (c := succ (!c); !c) in

            让 decc = λ_:Unit。 (c := pred (!c); !c) in

            {i=incc，d=decc}

```

    Now, each time we call newcounter, we get a new record of
    functions that share access to the same storage cell c.  The
    caller of newcounter can't get at this storage cell directly,
    but can affect it indirectly by calling the two functions.  In
    other words, we've created a simple form of *object*.

```

    让 c1 = newcounter unit in

    让 c2 = newcounter unit in

    //请注意，我们现在已经分配了两个独立的存储单元！

    让 r1 = c1.i unit in

    让 r2 = c2.i unit in

    r2 //产生 1，而不是 2！

```

#### Exercise: 1 star (store_draw)

    Draw (on paper) the contents of the store at the point in
    execution where the first two lets have finished and the third
    one is about to begin.

```

(*在这里填写*)

```

    ☐

```

## 复合类型的引用

    引用单元不一定只包含一个数字：原语

    我们上面定义的允许我们创建任何值的引用

    类型，包括函数。例如，我们可以使用引用来

    函数来给出数组的（低效的）实现

    的数字，如下所示。为类型编写 NatArray

    Ref（Nat→Nat）。

    回想一下 MoreStlc 章节中的 equal 函数：

```
      equal =
        fix
          (λeq:Nat->Nat->Bool.
             λm:Nat. λn:Nat.
               if m=0 then iszero n
               else if n=0 then false
               else eq (pred m) (pred n))

```

    要构建一个新数组，我们分配一个引用单元并填充

    用一个函数替换它，当给定一个索引时，总是返回 0。

```
      newarray = λ_:Unit. ref (λn:Nat.0)

```

    要查找数组的元素，我们只需应用

    函数到所需的索引。

```
      lookup = λa:NatArray. λn:Nat. (!a) n

```

    编码的有趣部分是更新函数。它

    接受一个数组，一个索引和一个要存储在该索引处的新值，并

    通过创建（并存储在引用中）一个新函数来完成其工作

    当被要求在这个索引处的值时，返回新的

    给定给 update 的值，而在所有其他索引上传递

    查找到先前存储在引用中的函数。

```
      update = λa:NatArray. λm:Nat. λv:Nat.
                   let oldf = !a in
                   a := (λn:Nat. if equal m n then v else oldf n);

```

    包含其他引用的值的引用也可以非常

    有用，允许我们定义可变的数据结构，如

    列表和树。

#### 练习：2 星，推荐（compact_update）

    如果我们像这样更紧凑地定义更新

```
      update = λa:NatArray. λm:Nat. λv:Nat.
                  a := (λn:Nat. if equal m n then v else (!a) n)

```

    它会表现得一样吗？

```
(* FILL IN HERE *)

```

    ☐

```

## Null References

    There is one final significant difference between our
    references and C-style mutable variables: in C-like languages,
    variables holding pointers into the heap may sometimes have the
    value NULL.  Dereferencing such a "null pointer" is an error,
    and results either in a clean exception (Java and C#) or in
    arbitrary and possibly insecure behavior (C and relatives like
    C++).  Null pointers cause significant trouble in C-like
    languages: the fact that any pointer might be null means that any
    dereference operation in the program can potentially fail.

    Even in ML-like languages, there are occasionally situations where
    we may or may not have a valid pointer in our hands.  Fortunately,
    there is no need to extend the basic mechanisms of references to
    represent such situations: the sum types introduced in the
    MoreStlc chapter already give us what we need.

    First, we can use sums to build an analog of the option types
    introduced in the Lists chapter.  Define Option T to be an
    abbreviation for Unit + T.

    Then a "nullable reference to a T" is simply an element of the
    type Option (Ref T).

```

## 垃圾回收

    在我们继续之前，我们应该提到的最后一个问题

    形式化引用是存储*解*分配。我们还没有

    在释放引用单元时是否提供了任何原语

    不再需要。相反，像许多现代语言一样（包括

    ML 和 Java）我们依赖运行时系统执行*垃圾回收*，自动识别和重用可以

    不再被程序访问。

    这不仅仅是语言设计上的品味问题：这是

    在存在时实现类型安全非常困难

    显式的解除分配操作。这样做的一个原因是

    熟悉的*悬空引用*问题：我们分配一个包含的单元

    一个数字，将其保存在某种数据结构中的引用中，使用它

    一段时间，然后释放它并分配一个新的单元格来保存

    布尔值，可能重复使用相同的存储。 现在我们可以有两个

    相同存储单元的不同名称 —— 一个类型为 Ref Nat，另一个

    其他类型为 Ref Bool 的。

#### 练习：1 星（类型安全性违规）

    展示这如何导致类型安全性的违反。

```
(* FILL IN HERE *)

```

    ☐

```

# Operational Semantics

```

## 位置

    对引用处理的最微妙的方面

    当我们考虑如何形式化它们的操作时出现

    行为。 看清楚的一种方法是问，“应该是什么

    *类型为 Ref T 的值？* 我们需要的关键观察

    要考虑的一点是 reduci a ref 运算符应该

    *做* 一些事情 —— 即，分配一些存储 —— 结果

    操作的结果应该是对此存储的引用。

    那么，什么是引用？

    大多数编程语言实现中的运行时存储是

    本质上只是一个大字节数组。 运行时系统保持

    跟踪这个数组的哪些部分当前正在使用；当我们

    需要分配一个新的引用单元格，我们分配一个足够大的

    存储的空闲区域中的段（4 字节用于整数

    单元格，8 字节用于存储 Floats 的单元格等），记录在某处

    它正在被使用，并返回索引（通常是 32 位或

    64 位整数）指向新分配区域的起始位置。 这些

    索引是引用。

    就目前而言，没有必要如此具体。

    我们可以将存储看作是一个 *值* 数组，而不是一个

    字节数组，抽象出不同大小的

    不同值的运行时表示。 那么，一个引用，

    只是一个索引到存储中。 （如果我们愿意，我们甚至可以

    抽象化，使这些索引是数字，但

    出于在 Coq 中形式化的目的，使用

    数字。）我们使用 *位置* 这个词，而不是 *引用* 或

    *指针* 来强调这种抽象特质。

    以这种方式抽象地处理位置将防止我们

    建模在低级语言中找到的 *指针算术*

    例如 C。 这种限制是有意的。 虽然指针

    算术偶尔非常有用，特别是对于

    实现低级服务，如垃圾收集器，它

    大多数类型系统无法跟踪：知道位置 n

    存储中包含浮点数并不告诉我们任何有用��信息

    关于位置 n+4 的类型。 在 C 中，指针算术是一个

    类型安全性违规的臭名昭著来源。

```

## Stores

    Recall that, in the small-step operational semantics for
    IMP, the step relation needed to carry along an auxiliary state in
    addition to the program being executed.  In the same way, once we
    have added reference cells to the STLC, our step relation must
    carry along a store to keep track of the contents of reference
    cells.

    We could re-use the same functional representation we used for
    states in IMP, but for carrying out the proofs in this chapter it
    is actually more convenient to represent a store simply as a
    *list* of values.  (The reason we didn't use this representation
    before is that, in IMP, a program could modify any location at any
    time, so states had to be ready to map *any* variable to a value.
    However, in the STLC with references, the only way to create a
    reference cell is with tref t[1], which puts the value of t[1]
    in a new reference cell and reduces to the location of the newly
    created reference cell. When reducing such an expression, we can
    just add a new reference cell to the end of the list representing
    the store.)

```

定义 store := list tm。

```

    We use store_lookup n st to retrieve the value of the reference
    cell at location n in the store st.  Note that we must give a
    default value to nth in case we try looking up an index which is
    too large. (In fact, we will never actually do this, but proving
    that we don't will require a bit of work.)

```

定义 store_lookup (n:nat) (st:store) =

第 n 个 st tunit。

```

    To update the store, we use the replace function, which replaces
    the contents of a cell at a particular index.

```

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=

匹配 l 与

| nil    ⇒ nil

| h :: t ⇒

匹配 n 与

| O    ⇒ x :: t

| S n' ⇒ h :: replace n' x t

结束

结束。

```

    As might be expected, we will also need some technical
    lemmas about replace; they are straightforward to prove.

```

引理 replace_nil : ∀A n (x:A),

replace n x nil = nil.

    证明。

destruct n; auto.

    Qed.

引理 length_replace : ∀A n x (l:list A),

长度（用 n x l 替换）= 长度 l。

    Proof with auto.

intros A n x l. generalize dependent n.

归纳 l; intros n.

destruct n...

destruct n...

simpl. rewrite IHl...

    Qed.

引理 lookup_replace_eq：对于 l、t 和 st，

当 l 小于 st 的长度时 →

store_lookup l (replace l t st) = t.

    证明与自动化相关。

引入 l、t 和 st。

展开 store_lookup。

推广 l。

以 st 为基础进行归纳，当 st 为空或者为 t' :: st'时，引入 l 和 Hlen。

- (* st =  *) 

对 Hlen 进行反演。

- (* st = t' :: st' *)

对 l 进行分析; 简化...

应用 IHst'。在 Hlen 中简化。omega。

    证毕。

引理 lookup_replace_neq：对于 l[1]、l[2]、t 和 st，

l[1] ≠ l[2] →

store_lookup l[1] (replace l[2] t st) = store_lookup l[1] st.

    证明与自动化相关。

展开 store_lookup。

以 l[1]为基础进行归纳，引入 l[2]、t 和 st，Hneq 表示不相等。

- (* l[1] = 0 *)

对 st 进行分析。

+ (* st =  *) 重写 replace_nil...

+ (* st = _ :: _ *) 对 l[2]进行分析... 反驳 Hneq...

- (* l[1] = S l[1]' *)

对 st 进行分析，作为[t[2] st]的情况。

+ (* st =  *) 对 l[2]进行分析...

+ (* st = t[2] :: st[2] *)

对 l[2]进行分析...

简化；应用 IHl1'...

    证毕。

```

## Reduction

    Next, we need to extend the operational semantics to take
    stores into account.  Since the result of reducing an expression
    will in general depend on the contents of the store in which it is
    reduced, the evaluation rules should take not just a term but
    also a store as argument.  Furthermore, since the reduction of a
    term can cause side effects on the store, and these may affect the
    reduction of other terms in the future, the reduction rules need
    to return a new store.  Thus, the shape of the single-step
    reduction relation needs to change from t ⇒ t' to t / st ⇒ t' / st', where st and st' are the starting and ending states of
    the store.

    To carry through this change, we first need to augment all of our
    existing reduction rules with stores:

| 
             value v[2]
           | 
             (ST_AppAbs)  
           |
| 
             

* * *

           |
| 
             (λx:T.t12) v[2] / st ⇒ [x:=v[2]]t[12] / st
           | 
          |

| 
             t[1] / st ⇒ t[1]' / st'
           | 
             (ST_App1)  
           |
| 
             

* * *

           |
| 
             t[1] t[2] / st ⇒ t[1]' t[2] / st'
           | 
          |

| 
             value v[1] t[2] / st ⇒ t[2]' / st'
           | 
             (ST_App2)  
           |
| 
             

* * *

           |
| 
             v[1] t[2] / st ⇒ v[1] t[2]' / st'
           | 
          |

    Note that the first rule here returns the store unchanged, since
    function application, in itself, has no side effects.  The other
    two rules simply propagate side effects from premise to
    conclusion.

    Now, the result of reducing a ref expression will be a fresh
    location; this is why we included locations in the syntax of terms
    and in the set of values.  It is crucial to note that making this 
    extension to the syntax of terms does not mean that we intend 
    *programmers* to write terms involving explicit, concrete locations: 
    such terms will arise only as intermediate results during reduction.  
    This may seem odd, but it follows naturally from our design decision
    to represent the result of every reduction step by a modified *term*. 
    If we had chosen a more "machine-like" model, e.g., with an explicit 
    stack to contain values of bound identifiers, then the idea of adding 
    locations to the set of allowed values might seem more obvious.

    In terms of this expanded syntax, we can state reduction rules
    for the new constructs that manipulate locations and the store.
    First, to reduce a dereferencing expression !t[1], we must first
    reduce t[1] until it becomes a value:

| 
             t[1] / st ⇒ t[1]' / st'
           | 
             (ST_Deref)  
           |
| 
             

* * *

           |
| 
             !t[1] / st ⇒ !t[1]' / st'
           | 
          |

    Once t[1] has finished reducing, we should have an expression of
    the form !l, where l is some location.  (A term that attempts
    to dereference any other sort of value, such as a function or
    unit, is erroneous, as is a term that tries to dereference a
    location that is larger than the size |st| of the currently
    allocated store; the reduction rules simply get stuck in this
    case.  The type-safety properties established below assure us 
    that well-typed terms will never misbehave in this way.)

| 
             l < &#124;st&#124;< td="">
           | 
             (ST_DerefLoc)  
           |
| 
             

* * *

           |
| 
             !(loc l) / st ⇒ lookup l st / st
           | 
          |

    Next, to reduce an assignment expression t[1]:=t[2], we must first
    reduce t[1] until it becomes a value (a location), and then
    reduce t[2] until it becomes a value (of any sort):

| 
             t[1] / st ⇒ t[1]' / st'
           | 
             (ST_Assign1)  
           |
| 
             

* * *

           |
| 
             t[1] := t[2] / st ⇒ t[1]' := t[2] / st'
           | 
          |

| 
             t[2] / st ⇒ t[2]' / st'
           | 
             (ST_Assign2)  
           |
| 
             

* * *

           |
| 
             v[1] := t[2] / st ⇒ v[1] := t[2]' / st'
           | 
          |

    Once we have finished with t[1] and t[2], we have an expression of
    the form l:=v[2], which we execute by updating the store to make
    location l contain v[2]:

| 
             l < &#124;st&#124;< td="">
           | 
             (ST_Assign)  
           |
| 
             

* * *

           |
| 
             loc l := v[2] / st ⇒ unit / [l:=v[2]]st
           | 
          |

    The notation [l:=v[2]]st means "the store that maps l to v[2]
    and maps all other locations to the same thing as st."  Note
    that the term resulting from this reduction step is just unit;
    the interesting result is the updated store.

    Finally, to reduct an expression of the form ref t[1], we first
    reduce t[1] until it becomes a value:

| 
             t[1] / st ⇒ t[1]' / st'
           | 
             (ST_Ref)  
           |
| 
             

* * *

           |
| 
             ref t[1] / st ⇒ ref t[1]' / st'
           | 
          |

    Then, to reduce the ref itself, we choose a fresh location at
    the end of the current store — i.e., location |st| — and yield
    a new store that extends st with the new value v[1].

| 
               
           | 
             (ST_RefValue)  
           |
| 
             

* * *

           |
| 
             ref v[1] / st ⇒ loc &#124;st&#124; / st,v[1]
           | 
          |

    The value resulting from this step is the newly allocated location
    itself.  (Formally, st,v[1] means st ++ v[1]::nil — i.e., to add
    a new reference cell to the store, we append it to the end.)  

    Note that these reduction rules do not perform any kind of
    garbage collection: we simply allow the store to keep growing
    without bound as reduction proceeds.  This does not affect the
    correctness of the results of reduction (after all, the
    definition of "garbage" is precisely parts of the store that are
    no longer reachable and so cannot play any further role in
    reduction), but it means that a naive implementation of our
    evaluator might run out of memory where a more sophisticated 
    evaluator would be able to continue by reusing locations whose 
    contents have become garbage.

    Here are the rules again, formally:

```

保留记号"t1 '/' st1 '⇒' t2 '/' st2"

(在 40 级，st[1]在 39 级，t[2]在 39 级)。

导入 ListNotations。

步骤的归纳定义：tm * store → tm * store → Prop :=

| ST_AppAbs : ∀x T t[12] v[2] st,

值 v[2] →

tapp (tabs x T t[12]) v[2] / st ⇒ [x:=v[2]]t[12] / st

| ST_App1 : ∀t[1] t[1]' t[2] st st',

t[1] / st ⇒ t[1]' / st' →

tapp t[1] t[2] / st ⇒ tapp t[1]' t[2] / st'

| ST_App2 : ∀v[1] t[2] t[2]' st st',

值 v[1] →

t[2] / st ⇒ t[2]' / st' →

tapp v[1] t[2] / st ⇒ tapp v[1] t[2]'/ st'

| ST_SuccNat : ∀n st,

tsucc (tnat n) / st ⇒ tnat (S n) / st

| ST_Succ : ∀t[1] t[1]' st st',

t[1] / st ⇒ t[1]' / st' →

tsucc t[1] / st ⇒ tsucc t[1]' / st'

| ST_PredNat : ∀n st,

tpred (tnat n) / st ⇒ tnat (pred n) / st

| ST_Pred : ∀t[1] t[1]' st st',

t[1] / st ⇒ t[1]' / st' →

tpred t[1] / st ⇒ tpred t[1]' / st'

| ST_MultNats : ∀n[1] n[2] st,

tmult (tnat n[1]) (tnat n[2]) / st ⇒ tnat (mult n[1] n[2]) / st

| ST_Mult1 : ∀t[1] t[2] t[1]' st st',

t[1] / st ⇒ t[1]' / st' →

tmult t[1] t[2] / st ⇒ tmult t[1]' t[2] / st'

| ST_Mult2 : ∀v[1] t[2] t[2]' st st',

值 v[1] →

t[2] / st ⇒ t[2]' / st' →

tmult v[1] t[2] / st ⇒ tmult v[1] t[2]' / st'

| ST_If[0] : ∀t[1] t[1]' t[2] t[3] st st',

t[1] / st ⇒ t[1]' / st' →

tif0 t[1] t[2] t[3] / st ⇒ tif0 t[1]' t[2] t[3] / st'

| ST_If0_Zero : ∀t[2] t[3] st,

tif0 (tnat 0) t[2] t[3] / st ⇒ t[2] / st

| ST_If0_Nonzero : ∀n t[2] t[3] st,

tif0 (tnat (S n)) t[2] t[3] / st ⇒ t[3] / st

| ST_RefValue : ∀v[1] st,

值 v[1] →

tref v[1] / st ⇒ tloc (length st) / (st ++ v[1]::nil)

| ST_Ref : ∀t[1] t[1]' st st',

t[1] / st ⇒ t[1]' / st' →

tref t[1] /  st ⇒ tref t[1]' /  st'

| ST_DerefLoc : ∀st l,

当 l 小于 st 的长度时 →

tderef (tloc l) / st ⇒ store_lookup l st / st

| ST_Deref : ∀t[1] t[1]' st st',

t[1] / st ⇒ t[1]' / st' →

tderef t[1] / st ⇒ tderef t[1]' / st'

| ST_Assign : ∀v[2] l st,

值 v[2] →

l < length st →

tassign (tloc l) v[2] / st ⇒ tunit / replace l v[2] st

| ST_Assign1 : ∀t[1] t[1]' t[2] st st',

t[1] / st ⇒ t[1]' / st' →

tassign t[1] t[2] / st ⇒ tassign t[1]' t[2] / st'

| ST_Assign2 : ∀v[1] t[2] t[2]' st st',

值 v[1] →

t[2] / st ⇒ t[2]' / st' →

tassign v[1] t[2] / st ⇒ tassign v[1] t[2]' / st'

其中“t1 '/' st1 '⇒' t2 '/' st2”:=（步骤（t[1]，st[1]）（t[2]，st[2])）。

```

    One slightly ugly point should be noted here: In the ST_RefValue
    rule, we extend the state by writing st ++ v[1]::nil rather than
    the more natural st ++ [v[1]].  The reason for this is that the
    notation we've defined for substitution uses square brackets,
    which clash with the standard library's notation for lists.

```

Hint Constructors step。

定义 multistep :=（多步骤）。

Notation "t1 '/' st '⇒*' t2 '/' st'" :=

（multistep（t[1]，st）（t[2]，st'））

（在级别 40，st 在级别 39，t[2] 在级别 39）。

```

# Typing

    The contexts assigning types to free variables are exactly the
    same as for the STLC: partial maps from identifiers to types.

```

定义上下文 := partial_map ty。

```

## Store typings

    Having extended our syntax and reduction rules to accommodate
    references, our last job is to write down typing rules for the new
    constructs (and, of course, to check that these rules are sound!).
    Naturally, the key question is, "What is the type of a location?"

    First of all, notice that this question doesn't arise when
    typechecking terms that programmers actually
    write.  Concrete location constants arise only in terms that are
    the intermediate results of reduction; they are not in the
    language that programmers write.  So we only need to determine the
    type of a location when we're in the middle of a reduction
    sequence, e.g., trying to apply the progress or preservation
    lemmas.  Thus, even though we normally think of typing as a
    *static* program property, it makes sense for the typing of
    locations to depend on the *dynamic* progress of the program too.

    As a first try, note that when we reduce a term containing
    concrete locations, the type of the result depends on the contents
    of the store that we start with.  For example, if we reduce the
    term !(loc 1) in the store [unit, unit], the result is unit;
    if we reduce the same term in the store [unit, \x:Unit.x], the
    result is \x:Unit.x.  With respect to the former store, the
    location 1 has type Unit, and with respect to the latter it
    has type Unit→Unit. This observation leads us immediately to a
    first attempt at a typing rule for locations:

| 
             Γ ⊢ lookup  l st : T[1]
           | 
              
           |
| 
             

* * *

           |
| 
             Γ ⊢ loc l : Ref T[1]
           | 
          |

    That is, to find the type of a location l, we look up the
    current contents of l in the store and calculate the type T[1]
    of the contents.  The type of the location is then Ref T[1].

    Having begun in this way, we need to go a little further to reach a
    consistent state.  In effect, by making the type of a term depend on
    the store, we have changed the typing relation from a three-place
    relation (between contexts, terms, and types) to a four-place relation
    (between contexts, *stores*, terms, and types).  Since the store is,
    intuitively, part of the context in which we calculate the type of a
    term, let's write this four-place relation with the store to the left
    of the turnstile: Γ; st ⊢ t : T.  Our rule for typing
    references now has the form

| 
             Gamma; st ⊢ lookup l st : T[1]
           | 
              
           |
| 
             

* * *

           |
| 
             Gamma; st ⊢ loc l : Ref T[1]
           | 
          |

    and all the rest of the typing rules in the system are extended
    similarly with stores.  (The other rules do not need to do anything
    interesting with their stores — just pass them from premise to
    conclusion.)

    However, this rule will not quite do.  For one thing, typechecking
    is rather inefficient, since calculating the type of a location l
    involves calculating the type of the current contents v of l.  If
    l appears many times in a term t, we will re-calculate the type of
    v many times in the course of constructing a typing derivation for
    t.  Worse, if v itself contains locations, then we will have to
    recalculate *their* types each time they appear.  Worse yet, the 
    proposed typing rule for locations may not allow us to derive 
    anything at all, if the store contains a *cycle*.  For example,
    there is no finite typing derivation for the location 0 with respect
    to this store:

```

[\x:Nat。(!(loc 1)) x，λx:Nat。(!(loc 0)) x]

```

#### Exercise: 2 stars (cyclic_store)

    Can you find a term whose reduction will create this particular
    cyclic store?  ☐ 

    These problems arise from the fact that our proposed
    typing rule for locations requires us to recalculate the type of a
    location every time we mention it in a term.  But this,
    intuitively, should not be necessary.  After all, when a location
    is first created, we know the type of the initial value that we
    are storing into it.  Suppose we are willing to enforce the
    invariant that the type of the value contained in a given location
    *never changes*; that is, although we may later store other values
    into this location, those other values will always have the same
    type as the initial one.  In other words, we always have in mind a
    single, definite type for every location in the store, which is
    fixed when the location is allocated.  Then these intended types
    can be collected together as a *store typing* — a finite function
    mapping locations to types.

    As with the other type systems we've seen, this conservative typing 
    restriction on allowed updates means that we will rule out as 
    ill-typed some programs that could reduce perfectly well without
    getting stuck. 

    Just as we did for stores, we will represent a store type simply
    as a list of types: the type at index i records the type of the
    values that we expect to be stored in cell i.

```

定义 store_ty := list ty。

```

    The store_Tlookup function retrieves the type at a particular
    index.

```

定义 store_Tlookup（n：nat）（ST：store_ty） :=

第 n 个 ST TUnit。

```

    Suppose we are given a store typing ST describing the store
    st in which some term t will be reduced.  Then we can use
    ST to calculate the type of the result of t without ever
    looking directly at st.  For example, if ST is [Unit, Unit→Unit], then we can immediately infer that !(loc 1) has
    type Unit→Unit.  More generally, the typing rule for locations
    can be reformulated in terms of store typings like this:

| 
             l < &#124;st&#124;< td="">
           | 
              
           |
| 
             

* * *

           |
| 
             Gamma; ST ⊢ loc l : Ref (lookup l ST)
           | 
          |

    That is, as long as l is a valid location, we can compute the 
    type of l just by looking it up in ST.  Typing is again a 
    four-place relation, but it is parameterized on a store *typing* 
    rather than a concrete store.  The rest of the typing rules are 
    analogously augmented with store typings.

```

## 类型关系

    我们现在可以形式化带有的类型关系

    引用。在这里，我们再次添加到基础的规则

    STLC（带有数字和 Unit）：

|

            l < |st| < td="">

        |

            （T_Loc）

        |

|

* * *

        |

|

            Gamma；ST ⊢ loc l：Ref（lookup l ST）

        |

        |

|

            Gamma；ST ⊢ t[1]：T[1]

        |

            （T_Ref）

        |

|

* * *

        |

|

            Gamma；ST ⊢ ref t[1]：Ref T[1]

        |

        |

|

            Gamma；ST ⊢ t[1]：Ref T[11]

        |

            （T_Deref）

        |

|

* * *

        |

|

            Gamma；ST ⊢！t[1]：T[11]

        |

        |

|

            Gamma；ST ⊢ t[1]：Ref T[11]

        |

        |

|

            Gamma；ST ⊢ t[2]：T[11]

        |

            （T_Assign）

        |

|

* * *

        |

|

            Gamma；ST ⊢ t[1] := t[2] : Unit

        |

        |

```
Reserved Notation "Gamma ';' ST '⊢' t '∈' T" (at level 40).

Inductive has_type : context → store_ty → tm → ty → Prop :=
  | T_Var : ∀Γ ST x T,
      Γ x = Some T →
      Γ; ST ⊢ (tvar x) ∈ T
  | T_Abs : ∀Γ ST x T[11] T[12] t[12],
      (update Γ x T[11]); ST ⊢ t[12] ∈ T[12] →
      Γ; ST ⊢ (tabs x T[11] t[12]) ∈ (TArrow T[11] T[12])
  | T_App : ∀T[1] T[2] Γ ST t[1] t[2],
      Γ; ST ⊢ t[1] ∈ (TArrow T[1] T[2]) →
      Γ; ST ⊢ t[2] ∈ T[1] →
      Γ; ST ⊢ (tapp t[1] t[2]) ∈ T[2]
  | T_Nat : ∀Γ ST n,
      Γ; ST ⊢ (tnat n) ∈ TNat
  | T_Succ : ∀Γ ST t[1],
      Γ; ST ⊢ t[1] ∈ TNat →
      Γ; ST ⊢ (tsucc t[1]) ∈ TNat
  | T_Pred : ∀Γ ST t[1],
      Γ; ST ⊢ t[1] ∈ TNat →
      Γ; ST ⊢ (tpred t[1]) ∈ TNat
  | T_Mult : ∀Γ ST t[1] t[2],
      Γ; ST ⊢ t[1] ∈ TNat →
      Γ; ST ⊢ t[2] ∈ TNat →
      Γ; ST ⊢ (tmult t[1] t[2]) ∈ TNat
  | T_If[0] : ∀Γ ST t[1] t[2] t[3] T,
      Γ; ST ⊢ t[1] ∈ TNat →
      Γ; ST ⊢ t[2] ∈ T →
      Γ; ST ⊢ t[3] ∈ T →
      Γ; ST ⊢ (tif0 t[1] t[2] t[3]) ∈ T
  | T_Unit : ∀Γ ST,
      Γ; ST ⊢ tunit ∈ TUnit
  | T_Loc : ∀Γ ST l,
      l < length ST →
      Γ; ST ⊢ (tloc l) ∈ (TRef (store_Tlookup l ST))
  | T_Ref : ∀Γ ST t[1] T[1],
      Γ; ST ⊢ t[1] ∈ T[1] →
      Γ; ST ⊢ (tref t[1]) ∈ (TRef T[1])
  | T_Deref : ∀Γ ST t[1] T[11],
      Γ; ST ⊢ t[1] ∈ (TRef T[11]) →
      Γ; ST ⊢ (tderef t[1]) ∈ T[11]
  | T_Assign : ∀Γ ST t[1] t[2] T[11],
      Γ; ST ⊢ t[1] ∈ (TRef T[11]) →
      Γ; ST ⊢ t[2] ∈ T[11] →
      Γ; ST ⊢ (tassign t[1] t[2]) ∈ TUnit

where "Gamma ';' ST '⊢' t '∈' T" := (has_type Γ ST t T).

Hint Constructors has_type.

```

    当然，这些类型规则将准确预测结果

    仅当在减少过程中使用的具体存储

    实际上符合我们为了目的而假设的存储类型

    类型检查。这个限定条件与情况完全相似

    在基本 STLC 中具有自由变量的项：替换引理

    承诺，如果 Γ ⊢ t：T，则我们可以替换自由的

    t 中的变量与Γ中列出的类型的值

    获得一个类型为 T 的闭合项，这通过类型保留

    定理将导致类型为 T 的最终结果，如果它产生

    任何结果。我们将在下面看到如何形式化一个

    对存储和存储类型的类似直觉。

    但是，为了对程序员编写的项进行类型检查

    实际上写代码时，我们不需要做任何花哨的事情来猜测什么。

    应该使用的存储类型。具体位置仅在

    减少的中间结果的项；它们是

    不在程序员编写的语言中。因此，我们可以简单地

    将程序员的项与*空*存储类型检查

    类型。随着减少的进行和新位置的创建，我们

    将始终能够看到如何通过扩展存储类型来扩展

    查看放置在新创建的位置中的初始值的类型

    分配的单元格；这种直觉在陈述中被形式化为

    下面是类型保留定理。

```

# Properties

    Our final task is to check that standard type safety
    properties continue to hold for the STLC with references.  The
    progress theorem ("well-typed terms are not stuck") can be stated
    and proved almost as for the STLC; we just need to add a few
    straightforward cases to the proof to deal with the new
    constructs.  The preservation theorem is a bit more interesting,
    so let's look at it first.

```

## 良好类型的存储

    由于我们已经扩展了减少关系（具有

    初始和最终存储）和类型关系（带有存储

    输入），我们需要改变保留的陈述为

    包括这些参数。但很明显，我们不能简单地添加存储

    和存储类型，而不说它们是如何的

    相关的 —— 即，这是错误的：

```
Theorem preservation_wrong1 : ∀ST T t st t' st',
  empty; ST ⊢ t ∈ T →
  t / st ⇒ t' / st' →
  empty; ST ⊢ t' ∈ T.
Abort.

```

    如果我们针对一些关于

    存储中的值的类型，然后根据情况减少

    违反这些假设的存储，结果将是

    灾难。我们说存储 st 相对于

    存储类型 ST 如果 st 中每个位置 l 处的项都有

    在 ST 中位置 l 处的类型。由于只有封闭项才能

    存储在位置中（为什么？），只需在空的情况下对它们进行类型

    上下文。以下 store_well_typed 的定义形式化

    这个。

```
Definition store_well_typed (ST:store_ty) (st:store) :=
  length ST = length st ∧
  (∀l, l < length st →
     empty; ST ⊢ (store_lookup l st) ∈ (store_Tlookup l ST)).

```

    非正式地，我们将写成 ST ⊢ st 表示 store_well_typed ST st。

    直观地，存储 st 与存储类型一致

    如果存储中的每个值都具有预测的类型，则 ST 是存储类型。

    存储类型。唯一微妙的地方是，当

    在存储中输入数值，我们提供相同的存储

    类型到类型关系。这使我们能够对循环进行类型

    像我们上面看到的那样的存储。

#### 练习：2 星（store_not_unique）

    你能找到一个存储 st，和两个

    不同的存储类型 ST[1] 和 ST[2]，使得两者都

    ST[1] ⊢ st 和 ST[2] ⊢ st？

```
(* FILL IN HERE *)

```

    ☐

    现在���们可以陈述更接近所需的保留

    属性：

```
Theorem preservation_wrong2 : ∀ST T t st t' st',
  empty; ST ⊢ t ∈ T →
  t / st ⇒ t' / st' →
  store_well_typed ST st →
  empty; ST ⊢ t' ∈ T.
Abort.

```

    这个陈述对于所有的规约规则都是可以的，除了

    分配规则 ST_RefValue。问题在于这个规则

    产生一个具有比初始存储更大域的存储，

    反驳上述陈述的结论：如果 st' 包含

    为新位置 l 绑定，那么 l 不能在

    ST 的域，并且不会出现 t'（

    明确提到 l）在 ST 下是可类型化的。

```

## Extending Store Typings

    Evidently, since the store can increase in size during reduction,
    we need to allow the store typing to grow as well.  This motivates
    the following definition.  We say that the store type ST' *extends* ST if ST' is just ST with some new types added to
    the end.

```

归纳 extends : store_ty → store_ty → Prop :=

| extends_nil  : ∀ST'，

扩展 ST' 为 nil

| extends_cons : ∀x ST' ST，

extends ST' ST →

extends (x::ST') (x::ST)。

提示 构造 extends。

```

    We'll need a few technical lemmas about extended contexts.

    First, looking up a type in an extended store typing yields the
    same result as in the original:

```

引理 extends_lookup : ∀l ST ST',

l < length ST →

扩展 ST' ST →

store_Tlookup l ST' = store_Tlookup l ST。

    证明。自动。

intros l ST ST' Hlen H。

推广 ST'。推广 l。

对 ST 进行归纳，作为 [|a ST[2]]；intros l Hlen ST' HST'。

- (* nil *) 反转 Hlen。

- (* cons *) 在 * 中展开 store_Tlookup。

拆分 ST'。

+ (* ST' = nil *) 反转 HST'。

+ (* ST' = a' :: ST'2 *)

反转 HST'; 替换。

拆分 l 为 [|l']。

* (* l = 0 *) 自动。

* (* l = S l' *) 简化。应用 IHST2...

简化 Hlen; omega。

    完成。

```

    Next, if ST' extends ST, the length of ST' is at least that
    of ST.

```

引理 length_extends : ∀l ST ST',

l < length ST →

扩展 ST' ST →

l < length ST'。

    证明。使用 eauto。

intros。推广 l。对 H[0] 进行归纳；intros l Hlen。

反转 Hlen。

简化。

拆分 l；尝试 omega。

应用 [lt_n_S](http://coq.inria.fr/library/Coq.Arith.Lt.html#lt_n_S)。应用 IHextends。omega。

    完成。

```

    Finally, ST ++ T extends ST, and extends is reflexive.

```

引理 extends_app : ∀ST T，

extends (ST ++ T) ST。

    证明。自动。

对 ST 进行归纳; intros T...

简化...

    完成。

引理 extends_refl : ∀ST，

extends ST ST。

    证明。

对 ST 进行归纳; 自动。

    完成。

```

## Preservation, Finally

    We can now give the final, correct statement of the type
    preservation property:

```

保留定理定义为 ∀ST t t' T st st'，

空; ST ⊢ t ∈ T →

store_well_typed ST st →

t / st ⇒ t' / st' →

∃ST'，

（扩展 ST' ST ∧

空; ST' ⊢ t' ∈ T ∧

store_well_typed ST' st')。

```

    Note that the preservation theorem merely asserts that there is
    *some* store typing ST' extending ST (i.e., agreeing with ST
    on the values of all the old locations) such that the new term
    t' is well typed with respect to ST'; it does not tell us
    exactly what ST' is.  It is intuitively clear, of course, that
    ST' is either ST or else exactly ST ++ T[1]::nil, where
    T[1] is the type of the value v[1] in the extended store st ++ v[1]::nil, but stating this explicitly would complicate the statement of
    the theorem without actually making it any more useful: the weaker
    version above is already in the right form (because its conclusion
    implies its hypothesis) to "turn the crank" repeatedly and
    conclude that every *sequence* of reduction steps preserves
    well-typedness.  Combining this with the progress property, we
    obtain the usual guarantee that "well-typed programs never go
    wrong."

    In order to prove this, we'll need a few lemmas, as usual.

```

## 替换引理

    首先，我们需要标准替换的简单扩展

    引理，以及关于上下文不变性的相同机制

    我们在 STLC 的替换引理的证明中使用的

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
  | afi_succ : ∀x t[1],
      appears_free_in x t[1] →
      appears_free_in x (tsucc t[1])
  | afi_pred : ∀x t[1],
      appears_free_in x t[1] →
      appears_free_in x (tpred t[1])
  | afi_mult1 : ∀x t[1] t[2],
      appears_free_in x t[1] →
      appears_free_in x (tmult t[1] t[2])
  | afi_mult2 : ∀x t[1] t[2],
      appears_free_in x t[2] →
      appears_free_in x (tmult t[1] t[2])
  | afi_if0_1 : ∀x t[1] t[2] t[3],
      appears_free_in x t[1] →
      appears_free_in x (tif0 t[1] t[2] t[3])
  | afi_if0_2 : ∀x t[1] t[2] t[3],
      appears_free_in x t[2] →
      appears_free_in x (tif0 t[1] t[2] t[3])
  | afi_if0_3 : ∀x t[1] t[2] t[3],
      appears_free_in x t[3] →
      appears_free_in x (tif0 t[1] t[2] t[3])
  | afi_ref : ∀x t[1],
      appears_free_in x t[1] → appears_free_in x (tref t[1])
  | afi_deref : ∀x t[1],
      appears_free_in x t[1] → appears_free_in x (tderef t[1])
  | afi_assign1 : ∀x t[1] t[2],
      appears_free_in x t[1] → appears_free_in x (tassign t[1] t[2])
  | afi_assign2 : ∀x t[1] t[2],
      appears_free_in x t[2] → appears_free_in x (tassign t[1] t[2]).

Hint Constructors appears_free_in.

Lemma free_in_context : ∀x t T Γ ST,
   appears_free_in x t →
   Γ; ST ⊢ t ∈ T →
   ∃T', Γ x = Some T'.

    Proof with eauto.
  intros. generalize dependent Γ. generalize dependent T.
  induction H;
        intros; (try solve [ inversion H[0]; subst; eauto ]).
  - (* afi_abs *)
    inversion H[1]; subst.
    apply IHappears_free_in in H[8].
    rewrite update_neq in H[8]; assumption.
    Qed.

Lemma context_invariance : ∀Γ Γ' ST t T,
  Γ; ST ⊢ t ∈ T →
  (∀x, appears_free_in x t → Γ x = Γ' x) →
  Γ'; ST ⊢ t ∈ T.

    Proof with eauto.
  intros.
  generalize dependent Γ'.
  induction H; intros...
  - (* T_Var *)
    apply T_Var. symmetry. rewrite ← H...
  - (* T_Abs *)
    apply T_Abs. apply IHhas_type; intros.
    unfold update, t_update.
    destruct (beq_idP x x[0])...
  - (* T_App *)
    eapply T_App.
      apply IHhas_type1...
      apply IHhas_type2...
  - (* T_Mult *)
    eapply T_Mult.
      apply IHhas_type1...
      apply IHhas_type2...
  - (* T_If[0] *)
    eapply [T_If[0]](References.html#STLCRef.T_If<sub>0</sub>).
      apply IHhas_type1...
      apply IHhas_type2...
      apply IHhas_type3...
  - (* T_Assign *)
    eapply T_Assign.
      apply IHhas_type1...
      apply IHhas_type2...
    Qed.

Lemma substitution_preserves_typing : ∀Γ ST x s S t T,
  empty; ST ⊢ s ∈ S →
  (update Γ x S); ST ⊢ t ∈ T →
  Γ; ST ⊢ ([x:=s]t) ∈ T.

    Proof with eauto.
  intros Γ ST x s S t T Hs Ht.
  generalize dependent Γ. generalize dependent T.
  induction t; intros T Γ H;
    inversion H; subst; simpl...
  - (* tvar *)
    rename i into y.
    destruct (beq_idP x y).
    + (* x = y *)
      subst.
      rewrite update_eq in H[3].
      inversion H[3]; subst.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ _ _ _ Hcontra Hs)
        as [T' HT'].
      inversion HT'.
    + (* x <> y *)
      apply T_Var.
      rewrite update_neq in H[3]...
  - (* tabs *) subst.
    rename i into y.
    destruct (beq_idP x y).
    + (* x = y *)
      subst.
      apply T_Abs. eapply context_invariance...
      intros. rewrite update_shadow. reflexivity.
    + (* x <> x[0] *)
      apply T_Abs. apply IHt.
      eapply context_invariance...
      intros. unfold update, t_update.
      destruct (beq_idP y x[0])...
      subst.
      rewrite false_beq_id...
    Qed.

```

## 分配保留存储类型

    接下来，我们必须证明替换单元格内容不会改变

    用适当类型的新值替换存储器中的内容不会改变

    存储的整体类型。（这对于 ST_Assign 是必要的

    规则。）

```
Lemma assign_pres_store_typing : ∀ST st l t,
  l < length st →
  store_well_typed ST st →
  empty; ST ⊢ t ∈ (store_Tlookup l ST) →
  store_well_typed ST (replace l t st).

    Proof with auto.
  intros ST st l t Hlen HST Ht.
  inversion HST; subst.
  split. rewrite length_replace...
  intros l' Hl'.
  destruct ([beq_nat](http://coq.inria.fr/library/Coq.Arith.EqNat.html#beq_nat) l' l) eqn: Heqll'.
  - (* l' = l *)
    apply [beq_nat_true](http://coq.inria.fr/library/Coq.Arith.EqNat.html#beq_nat_true) in Heqll'; subst.
    rewrite lookup_replace_eq...
  - (* l' <> l *)
    apply [beq_nat_false](http://coq.inria.fr/library/Coq.Arith.EqNat.html#beq_nat_false) in Heqll'.
    rewrite lookup_replace_neq...
    rewrite length_replace in Hl'.
    apply H[0]...
    Qed.

```

## 存储弱化

    最后，我们需要一个关于存储类型的引理，陈述如果

    存储类型扩展为一个新位置，扩展的位置

    仍然允许我们为相同的术语分配相同的类型

    原始的。

    （该引理称为 store_weakening，因为它类似于

    在证明理论中找到的“弱化”引理，显示添加一个

    对某个逻辑理论的新假设不会减少

    可证明的定理。）

```
Lemma store_weakening : ∀Γ ST ST' t T,
  extends ST' ST →
  Γ; ST ⊢ t ∈ T →
  Γ; ST' ⊢ t ∈ T.

    Proof with eauto.
  intros. induction H[0]; eauto.
  - (* T_Loc *)
    erewrite ← extends_lookup...
    apply T_Loc.
    eapply length_extends...
    Qed.

```

    我们可以使用 store_weakening 引理证明，如果一个存储器是

    关于存储类型的类型化，然后扩展存储

    用一个新术语 t 扩展后，仍然会根据

    存储类型扩展为 t 的类型。

```
Lemma store_well_typed_app : ∀ST st t[1] T[1],
  store_well_typed ST st →
  empty; ST ⊢ t[1] ∈ T[1] →
  store_well_typed (ST ++ T[1]::nil) (st ++ t[1]::nil).

    Proof with auto.
  intros.
  unfold store_well_typed in *.
  inversion H as [Hlen Hmatch]; clear H.
  rewrite [app_length](http://coq.inria.fr/library/Coq.Lists.List.html#app_length), [plus_comm](http://coq.inria.fr/library/Coq.Arith.Plus.html#plus_comm). simpl.
  rewrite [app_length](http://coq.inria.fr/library/Coq.Lists.List.html#app_length), [plus_comm](http://coq.inria.fr/library/Coq.Arith.Plus.html#plus_comm). simpl.
  split...
  - (* types match. *)
    intros l Hl.
    unfold store_lookup, store_Tlookup.
    apply [le_lt_eq_dec](http://coq.inria.fr/library/Coq.Arith.Compare_dec.html#le_lt_eq_dec) in Hl; inversion Hl as [Hlt | Heq].
    + (* l < length st *)
      apply [lt_S_n](http://coq.inria.fr/library/Coq.Arith.Lt.html#lt_S_n) in Hlt.
      rewrite ![app_nth1](http://coq.inria.fr/library/Coq.Lists.List.html#app_nth1)...
      * apply store_weakening with ST. apply extends_app.
        apply Hmatch...
      * rewrite Hlen...
    + (* l = length st *)
      inversion Heq.
      rewrite [app_nth2](http://coq.inria.fr/library/Coq.Lists.List.html#app_nth2); try omega.
      rewrite ← Hlen.
      rewrite [minus_diag](http://coq.inria.fr/library/Coq.Arith.Minus.html#minus_diag). simpl.
      apply store_weakening with ST...
      { apply extends_app. }
        rewrite [app_nth2](http://coq.inria.fr/library/Coq.Lists.List.html#app_nth2); try omega.
      rewrite [minus_diag](http://coq.inria.fr/library/Coq.Arith.Minus.html#minus_diag). simpl. trivial.
    Qed.

```

## 保留！

    现在我们已经准备就绪，保留的证明

    事实上是非常直接的。

    从一个技术引理开始：

```
Lemma nth_eq_last : ∀A (l:list A) x d,
  nth (length l) (l ++ x::nil) d = x.

    Proof.
  induction l; intros; [ auto | simpl; rewrite IHl; auto ].
    Qed.

```

    最后，在这里是保留定理和证明：

```
Theorem preservation : ∀ST t t' T st st',
  empty; ST ⊢ t ∈ T →
  store_well_typed ST st →
  t / st ⇒ t' / st' →
  ∃ST',
    (extends ST' ST ∧
     empty; ST' ⊢ t' ∈ T ∧
     store_well_typed ST' st').

    Proof with eauto using store_weakening, extends_refl.
  remember (@empty ty) as Γ.
  intros ST t t' T st st' Ht.
  generalize dependent t'.
  induction Ht; intros t' HST Hstep;
    subst; try solve_by_invert; inversion Hstep; subst;
    try (eauto using store_weakening, extends_refl).
  (* T_App *)
  - (* ST_AppAbs *) ∃ST.
    inversion Ht[1]; subst.
    split; try split... eapply substitution_preserves_typing...
  - (* ST_App1 *)
    eapply IHHt1 in H[0]...
    inversion H[0] as [ST' [Hext [Hty Hsty]]].
    ∃ST'...
  - (* ST_App2 *)
    eapply IHHt2 in H[5]...
    inversion H[5] as [ST' [Hext [Hty Hsty]]].
    ∃ST'...
  - (* T_Succ *)
    + (* ST_Succ *)
      eapply IHHt in H[0]...
      inversion H[0] as [ST' [Hext [Hty Hsty]]].
      ∃ST'...
  - (* T_Pred *)
    + (* ST_Pred *)
      eapply IHHt in H[0]...
      inversion H[0] as [ST' [Hext [Hty Hsty]]].
      ∃ST'...
  (* T_Mult *)
  - (* ST_Mult1 *)
    eapply IHHt1 in H[0]...
    inversion H[0] as [ST' [Hext [Hty Hsty]]].
    ∃ST'...
  - (* ST_Mult2 *)
    eapply IHHt2 in H[5]...
    inversion H[5] as [ST' [Hext [Hty Hsty]]].
    ∃ST'...
  - (* T_If[0] *)
    + (* ST_If0_1 *)
      eapply IHHt1 in H[0]...
      inversion H[0] as [ST' [Hext [Hty Hsty]]].
      ∃ST'... split...
  (* T_Ref *)
  - (* ST_RefValue *)
    ∃(ST ++ T[1]::[nil](http://coq.inria.fr/library/Coq.Init.Datatypes.html#nil)).
    inversion HST; subst.
    split.
      apply extends_app.
    split.
      replace (TRef T[1])
        with (TRef (store_Tlookup ([length](http://coq.inria.fr/library/Coq.Init.Datatypes.html#length) st) (ST ++ T[1]::[nil](http://coq.inria.fr/library/Coq.Init.Datatypes.html#nil)))).
      apply T_Loc.
      rewrite ← H. rewrite [app_length](http://coq.inria.fr/library/Coq.Lists.List.html#app_length), [plus_comm](http://coq.inria.fr/library/Coq.Arith.Plus.html#plus_comm). simpl. omega.
      unfold store_Tlookup. rewrite ← H. rewrite nth_eq_last.
      reflexivity.
      apply store_well_typed_app; assumption.
  - (* ST_Ref *)
    eapply IHHt in H[0]...
    inversion H[0] as [ST' [Hext [Hty Hsty]]].
    ∃ST'...
  (* T_Deref *)
  - (* ST_DerefLoc *)
    ∃ST. split; try split...
    inversion HST as [_ Hsty].
    replace T[11] with (store_Tlookup l ST).
    apply Hsty...
    inversion Ht; subst...
  - (* ST_Deref *)
    eapply IHHt in H[0]...
    inversion H[0] as [ST' [Hext [Hty Hsty]]].
    ∃ST'...
  (* T_Assign *)
  - (* ST_Assign *)
    ∃ST. split; try split...
    eapply assign_pres_store_typing...
    inversion Ht[1]; subst...
  - (* ST_Assign1 *)
    eapply IHHt1 in H[0]...
    inversion H[0] as [ST' [Hext [Hty Hsty]]].
    ∃ST'...
  - (* ST_Assign2 *)
    eapply IHHt2 in H[5]...
    inversion H[5] as [ST' [Hext [Hty Hsty]]].
    ∃ST'...
    Qed.

```

#### 练习：3 星（保留非正式）

    仔细写出保留定理的非正式证明，

    集中在 T_App、T_Deref、T_Assign 和 T_Ref

    情况。

    (* 在这里填写 *)

    ☐

```

## Progress

    As we've said, progress for this system is pretty easy to prove;
    the proof is very similar to the proof of progress for the STLC,
    with a few new cases for the new syntactic constructs.

```

定理进展：∀ST t T st，

空; ST ⊢ t ∈ T →

存储类型良好 ST st →

（值 t ∨ ∃t'，∃st'，t / st ⇒ t' / st'）。

    Proof with eauto.

intros ST t T st Ht HST. remember (@empty ty) as Γ。

归纳 Ht; subst; try solve_by_invert...

- (* T_App *)

right. destruct IHHt1 as [Ht1p | Ht1p]...

+ (* t[1] 是值 *)

inversion Ht1p; subst; try solve_by_invert.

destruct IHHt2 as [Ht2p | Ht2p]...

* (* t[2] 步骤 *)

inversion Ht2p as [t[2]' [st' Hstep]]。

∃(tapp (tabs x T t) t[2]'). ∃st'...

+ (* t[1] 步骤 *)

inversion Ht1p as [t[1]' [st' Hstep]]。

∃(tapp t[1]' t[2]). ∃st'...

- (* T_Succ *)

right. destruct IHHt as [Ht1p | Ht1p]...

+ (* t[1] 是值 *)

inversion Ht1p; subst; try solve [ inversion Ht ]。

* (* t[1] 是一个 tnat *)

∃(tnat ([S](http://coq.inria.fr/library/Coq.Init.Datatypes.html#S) n)). ∃st...

+ (* t[1] 步骤 *)

inversion Ht1p as [t[1]' [st' Hstep]]。

∃(tsucc t[1]'). ∃st'...

- (* T_Pred *)

right. destruct IHHt as [Ht1p | Ht1p]...

+ (* t[1] 是值 *)

inversion Ht1p; subst; try solve [inversion Ht ]。

* (* t[1] 是一个 tnat *)

∃(tnat ([pred](http://coq.inria.fr/library/Coq.Init.Peano.html#pred) n)). ∃st...

+ (* t[1] 步骤 *)

inversion Ht1p as [t[1]' [st' Hstep]]。

∃(tpred t[1]'). ∃st'...

- (* T_Mult *)

right. destruct IHHt1 as [Ht1p | Ht1p]...

+ (* t[1] 是值 *)

inversion Ht1p; subst; try solve [inversion Ht[1]]。

destruct IHHt2 as [Ht2p | Ht2p]...

* (* t[2] 是一个值 *)

反演 Ht2p; 替换; 尝试解决 [inversion Ht[2]]。

∃([tnat](https://example.org/STLCRef.tnat) ([mult](http://coq.inria.fr/library/Coq.Init.Peano.html#mult) n n[0])). ∃st...

* (* t[2] 步骤 *)

反演 Ht2p 作为 [t[2]' [st' Hstep]]。

∃([tmult](https://example.org/STLCRef.tmult) ([tnat](https://example.org/STLCRef.tnat) n) t[2]'). ∃st'...

+ (* t[1] 步骤 *)

反演 Ht1p 作为 [t[1]' [st' Hstep]]。

∃([tmult](https://example.org/STLCRef.tmult) t[1]' t[2]). ∃st'...

- (* T_If[0] *)

right. 分解 IHHt1 为 [Ht1p | Ht1p]...

+ (* t[1] 是一个值 *)

反演 Ht1p; 替换; 尝试解决 [inversion Ht[1]]。

分解 n。

* (* n = 0 *) ∃t[2]. ∃st...

* (* n = S n' *) ∃t[3]. ∃st...

+ (* t[1] 步骤 *)

反演 Ht1p 作为 [t[1]' [st' Hstep]]。

∃([tif0](https://example.org/STLCRef.tif0) t[1]' t[2] t[3]). ∃st'...

- (* T_Ref *)

right. 分解 IHHt1 为 [Ht1p | Ht1p]...

+ (* t[1] 步骤 *)

反演 Ht1p 作为 [t[1]' [st' Hstep]]。

∃([tref](https://example.org/STLCRef.tref) t[1]'). ∃st'...

- (* T_Deref *)

right. 分解 IHHt1 为 [Ht1p | Ht1p]...

+ (* t[1] 是一个值 *)

反演 Ht1p; 替换; 尝试通过反演解决。

存在。存在。应用 [ST_DerefLoc](https://example.org/STLCRef.ST_DerefLoc)...

反演 Ht; 替换。反演 HST; 替换。

重写 ← H...

+ (* t[1] 步骤 *)

反演 Ht1p 作为 [t[1]' [st' Hstep]]。

∃([tderef](https://example.org/STLCRef.tderef) t[1]'). ∃st'...

- (* T_Assign *)

right. 分解 IHHt1 为 [Ht1p|Ht1p]...

+ (* t[1] 是一个值 *)

分解 IHHt2 为 [Ht2p|Ht2p]...

* (* t[2] 是一个值 *)

反演 Ht1p; 替换; 尝试通过反演解决。

存在。存在。应用 [ST_Assign](https://example.org/STLCRef.ST_Assign)...

替换 HST; 替换。反演 Ht[1]; 替换。

在 H 中重写 H[5]...

* (* t[2] 步骤 *)

反演 Ht2p 作为 [t[2]' [st' Hstep]]。

∃([tassign](https://example.org/STLCRef.tassign) t[1] t[2]'). ∃st'...

+ (* t[1] 步骤 *)

反演 Ht1p 作为 [t[1]' [st' Hstep]]。

∃([tassign](https://example.org/STLCRef.tassign) t[1]' t[2]). ∃st'...

    完成。

```

# References and Nontermination

    An important fact about the STLC (proved in chapter Norm) is
    that it is is *normalizing* — that is, every well-typed term can
    be reduced to a value in a finite number of steps.

    What about STLC + references?  Surprisingly, adding references
    causes us to lose the normalization property: there exist
    well-typed terms in the STLC + references which can continue to
    reduce forever, without ever reaching a normal form!

    How can we construct such a term?  The main idea is to make a
    function which calls itself.  We first make a function which calls
    another function stored in a reference cell; the trick is that we
    then smuggle in a reference to itself!

```

(λr:Ref (Unit -> Unit).

        r := (λx:Unit.(!r) unit); (!r) unit)

(ref (λx:Unit.unit))

```

    First, ref (λx:Unit.unit) creates a reference to a cell of type
   Unit → Unit.  We then pass this reference as the argument to a
   function which binds it to the name r, and assigns to it the
   function \x:Unit.(!r) unit — that is, the function which ignores
   its argument and calls the function stored in r on the argument
   unit; but of course, that function is itself!  To start the 
   divergent loop, we execute the function stored in the cell by 
   evaluating (!r) unit. 

    Here is the divergent term in Coq:

```

模块 示例变量。

定义 x := Id "x"。

定义 y := Id "y"。

定义 r := Id "r"。

定义 s := Id "s"。

结束 示例变量。

模块 RefsAndNontermination。

导入 示例变量。

定义 loop_fun :=

tabs x TUnit (tapp (tderef (tvar r)) tunit)。

定义 loop :=

tapp

(tabs r (TRef (TArrow TUnit TUnit))

(tseq (tassign (tvar r) loop_fun)

(tapp (tderef (tvar r)) tunit)))

(tref (tabs x TUnit tunit))。

```

    This term is well typed:

```

引理 loop_typeable : ∃T, empty; nil ⊢ loop ∈ T.

    证明与 eauto。

存在。展开 [loop](https://example.org/STLCRef.RefsAndNontermination.loop)。展开 [loop_fun](https://example.org/STLCRef.RefsAndNontermination.loop_fun)。

应用 [T_App](https://example.org/STLCRef.RefsAndNontermination.T_App)...

应用 [T_Abs](https://example.org/STLCRef.RefsAndNontermination.T_Abs)...

应用 [T_App](https://example.org/STLCRef.RefsAndNontermination.T_App)...

eapply T_Abs. eapply T_App. eapply T_Deref. eapply T_Var.

展开 update, t_update. 简化。反射性。自动。

eapply T_Assign.

eapply T_Var. 展开 update, t_update. 简化。反射性。

eapply T_Abs.

eapply T_App...

eapply T_Deref. eapply T_Var. 反射性。

    完成。

```

    To show formally that the term diverges, we first define the
    step_closure of the single-step reduction relation, written
    ⇒+.  This is just like the reflexive step closure of
    single-step reduction (which we're been writing ⇒*), except
    that it is not reflexive: t ⇒+ t' means that t can reach
    t' by *one or more* steps of reduction.

```

归纳步骤闭包 {X:Type} (R: relation X) : X → X → Prop :=

| sc_one  : ∀(x y : X),

R x y → step_closure R x y

| sc_step : ∀(x y z : X),

R x y →

步骤闭包 R y z →

步骤闭包 R x z。

定义 multistep1 := (step_closure step).

Notation "t1 '/' st '⇒+' t2 '/' st'" :=

(multistep1 (t[1],st) (t[2],st'))

(at level 40, st at level 39, t[2] at level 39).

```

    Now, we can show that the expression loop reduces to the
    expression !(loc 0) unit and the size-one store 
    [r:=(loc 0)]loop_fun. 

    As a convenience, we introduce a slight variant of the normalize
    tactic, called reduce, which tries solving the goal with
    multi_refl at each step, instead of waiting until the goal can't
    be reduced any more. Of course, the whole point is that loop
    doesn't normalize, so the old normalize tactic would just go
    into an infinite loop reducing it forever!

```

Ltac print_goal := match goal with ⊢ ?x ⇒ idtac x end.

Ltac reduce :=

重复（print_goal; eapply multi_step ;

[ (eauto 10; fail) | (instantiate; compute)];

尝试解决 [apply multi_refl]).

```

    Next, we use reduce to show that loop steps to 
    !(loc 0) unit, starting from the empty store.

```

引理 loop_steps_to_loop_fun :

loop / nil ⇒*

tapp (tderef (tloc 0)) tunit / cons ([r:=tloc 0]loop_fun) nil。

证明

展开 loop。

减少。

完成。

```

    Finally, we show that the latter expression reduces in
    two steps to itself!

```

引理 loop_fun_step_self :

tapp (tderef (tloc 0)) tunit / cons ([r:=tloc 0]loop_fun) nil ⇒+

tapp (tderef (tloc 0)) tunit / cons ([r:=tloc 0]loop_fun) nil。

    证明与 eauto。

展开 loop_fun; 简化。

eapply sc_step. apply ST_App1...

eapply sc_one. compute. apply ST_AppAbs...

    完成。

```

#### Exercise: 4 stars (factorial_ref)

    Use the above ideas to implement a factorial function in STLC with
    references.  (There is no need to prove formally that it really
    behaves like the factorial.  Just uncomment the example below to make
    sure it gives the correct result when applied to the argument
    4.)

```

阶乘定义：tm

(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

引理 factorial_type : empty; nil ⊢ factorial ∈ (TArrow TNat TNat).

证明与 eauto。

(* FILL IN HERE *) Admitted.

```

    If your definition is correct, you should be able to just
    uncomment the example below; the proof should be fully
    automatic using the reduce tactic.

```

(*  Lemma factorial_4 : exists st,   tapp factorial (tnat 4) / nil ==>* tnat 24 / st. Proof.   eexists. unfold factorial. reduce. Qed. *)

```

    ☐

```

# 附加练习

#### 练习：5 星，可选（垃圾回收器）

    挑战问题：修改我们的形式化以包括一个账户

    垃圾收集的定义，并证明它满足任何好的

    你可以考虑证明的属性。

    ☐

```
End RefsAndNontermination.
End STLCRef.

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
