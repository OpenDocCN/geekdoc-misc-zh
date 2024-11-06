# Stlc 简单类型 λ 演算

```

```

需要导入映射。

需要导入 Smallstep。

需要导入类型。

```

# The Simply Typed Lambda-Calculus

    The simply typed lambda-calculus (STLC) is a tiny core
    calculus embodying the key concept of *functional abstraction*,
    which shows up in pretty much every real-world programming
    language in some form (functions, procedures, methods, etc.).

    We will follow exactly the same pattern as in the previous chapter
    when formalizing this calculus (syntax, small-step semantics,
    typing rules) and its main properties (progress and preservation).
    The new technical challenges arise from the mechanisms of
    *variable binding* and *substitution*.  It which will take some
    work to deal with these.

```

## 概述

    STLC 建立在一些*基本类型*的集合上：

    布尔值、数字、字符串等。基本类型的确切选择

    并不重要 — 语言的构建及其

    理论性质都是一样的，不管我们

    选择 — 所以为了简洁起见，让我们只取 Bool 作为

    此刻。在本章结束时，我们将看到如何添加更多

    基本类型，并在后面的章节中我们将用纯 STLC 丰富

    其他有用的构造，如对、记录、子类型和

    可变状态。

    从布尔常量和条件开始，我们添加了三个

    事物：

+   变量

+   函数抽象

+   应用

    这给我们带来了以下抽象语法的集合

    构造函数（首先以非正式 BNF 符号表示 — 我们将

    在下面形式化它）。

```
       t ::= x                       variable
           | \x:T[1].t2                abstraction
           | t[1] t[2]                   application
           | true                    constant true
           | false                   constant false
           | if t[1] then t[2] else t[3]   conditional

    The \ symbol in a function abstraction \x:T[1].t2 is generally
    written as a Greek letter "lambda" (hence the name of the
    calculus).  The variable x is called the *parameter* to the
    function; the term t[2] is its *body*.  The annotation :T[1]
    specifies the type of arguments that the function can be applied
    to. 

    Some examples:

*   \x:Bool. x 

     The identity function for booleans. 

*   (λx:Bool. x) true 

     The identity function for booleans, applied to the boolean true. 

*   \x:Bool. if x then false else true 

     The boolean "not" function. 

*   \x:Bool. true 

     The constant function that takes every (boolean) argument to true.

*   \x:Bool. \y:Bool. x 

     A two-argument function that takes two booleans and returns the first one. (As in Coq, a two-argument function is really a one-argument function whose body is also a one-argument function.) 

*   (λx:Bool. \y:Bool. x) false true 

     A two-argument function that takes two booleans and returns the first one, applied to the booleans false and true. 

     As in Coq, application associates to the left — i.e., this expression is parsed as ((λx:Bool. \y:Bool. x) false) true. 

*   \f:Bool→Bool. f (f true) 

     A higher-order function that takes a *function* f (from booleans to booleans) as an argument, applies f to true, and applies f again to the result. 

*   (λf:Bool→Bool. f (f true)) (λx:Bool. false) 

     The same higher-order function, applied to the constantly false function.

    As the last several examples show, the STLC is a language of
    *higher-order* functions: we can write down functions that take
    other functions as arguments and/or return other functions as
    results.

    The STLC doesn't provide any primitive syntax for defining *named*
    functions — all functions are "anonymous."  We'll see in chapter
    MoreStlc that it is easy to add named functions to what we've
    got — indeed, the fundamental naming and binding mechanisms are
    exactly the same.

    The *types* of the STLC include Bool, which classifies the
    boolean constants true and false as well as more complex
    computations that yield booleans, plus *arrow types* that classify
    functions. 

```

T ::= Bool

| T[1] → T[2]

    例如：

+   \x:Bool. false 的类型为 Bool→Bool

+   \x:Bool. x 的类型为 Bool→Bool

+   (λx:Bool. x) true 的类型为 Bool

+   \x:Bool. \y:Bool. x 的类型为 Bool→Bool→Bool（即，Bool → (Bool→Bool)）

+   (λx:Bool. \y:Bool. x) false 的类型为 Bool→Bool

+   (λx:Bool. \y:Bool. x) false true 的类型为 Bool

```

## Syntax

    We next formalize the syntax of the STLC.

```

模块 STLC。

```

### Types

```

归纳类型：ty : Type :=

| TBool  : ty

| TArrow : ty → ty → ty。

```

### Terms

```

归纳类型 tm : Type :=

| tvar : id → tm

| tapp : tm → tm → tm

| tabs : id → ty → tm → tm

| ttrue : tm

| tfalse : tm

| tif : tm → tm → tm → tm。

```

    Note that an abstraction \x:T.t (formally, tabs x T t) is
    always annotated with the type T of its parameter, in contrast
    to Coq (and other functional languages like ML, Haskell, etc.),
    which use type inference to fill in missing annotations.  We're
    not considering type inference here. 

    Some examples...

```

定义 x := (Id "x").

定义 y := (Id "y").

定义 z := (Id "z").

提示展开 x。

提示展开 y。

提示展开 z。

```

    idB = \x:Bool. x

```

定义 idB :=

(tabs x TBool (tvar x)).

```

    idBB = \x:Bool→Bool. x

```

定义 idBB :=

(tabs x (TArrow TBool TBool) (tvar x)).

```

    idBBBB = \x:(Bool→Bool) → (Bool→Bool). x

```

定义 idBBBB :=

(tabs x (TArrow (TArrow TBool TBool)

（TArrow TBool TBool））

(tvar x)).

```

    k = \x:Bool. \y:Bool. x

```

定义 k := (tabs x TBool (tabs y TBool (tvar x))).

```

    notB = \x:Bool. if x then false else true

```

定义 notB := (tabs x TBool (tif (tvar x) tfalse ttrue)).

```

    (We write these as Notations rather than Definitions to make
    things easier for auto.)

```

## 操作语义

    要定义 STLC 术语的小步语义，我们从

    始终通过定义值的集合来定义。接下来，我们定义

    *自由变量*和*替换*的关键概念，这些概念

    在应用表达式的减少规则中使用。而

    最后我们给出了小步关系本身。

```

### Values

    To define the values of the STLC, we have a few cases to consider.

    First, for the boolean part of the language, the situation is
    clear: true and false are the only values.  An if
    expression is never a value. 

    Second, an application is clearly not a value: It represents a
    function being invoked on some argument, which clearly still has
    work left to do. 

    Third, for abstractions, we have a choice:

*   We can say that \x:T. t[1] is a value only when t[1] is a value — i.e., only if the function's body has been reduced (as much as it can be without knowing what argument it is going to be applied to). 

*   Or we can say that \x:T. t[1] is always a value, no matter whether t[1] is one or not — in other words, we can say that reduction stops at abstractions.

    Our usual way of evaluating expressions in Coq makes the first
    choice — for example,

```

Compute (fun x:bool ⇒ 3 + 4)

    产生 fun x:bool ⇒ 7。

    大多数现实世界的函数式编程语言都采用第二种

    选择 — 函数的主体只有在

    函数实际应用于参数时。我们还做出

    这里的第二个选择。

```
Inductive value : tm → Prop :=
  | v_abs : ∀x T t,
      value (tabs x T t)
  | v_true :
      value ttrue
  | v_false :
      value tfalse.

Hint Constructors value.

```

    最后，我们必须考虑什么构成了一个*完整*的程序。

    直观地说，“完整的程序”不得引用任何未定义的

    变量。我们很快将看到如何定义*自由*变量

    在 STLC 术语中。一个完整的程序是*封闭*的 — 即，

    不包含任何自由变量。

    （相反，一个带有自由变量的术语通常被称为*开放术语*。）

    选择不在抽象下减少后，我们不会

    不需要担心变量是否是值，因为我们将

    总是从“外部向内部”减少程序，这意味着

    步骤关系将始终处理封闭术语。

```

### Substitution

    Now we come to the heart of the STLC: the operation of
    substituting one term for a variable in another term.  This
    operation is used below to define the operational semantics of
    function application, where we will need to substitute the
    argument term for the function parameter in the function's body.
    For example, we reduce

```

（λx：Bool。如果 x 那么 true 否则 x）假

    至

```
       if false then true else false

    by substituting false for the parameter x in the body of the
    function.

    In general, we need to be able to substitute some given term s
    for occurrences of some variable x in another term t.  In
    informal discussions, this is usually written [x:=s]t and
    pronounced "substitute x with s in t." 

    Here are some examples:

*   [x:=true] (if x then x else false) yields if true then true else false 

*   [x:=true] x yields true 

*   [x:=true] (if x then x else y) yields if true then true else y 

*   [x:=true] y yields y 

*   [x:=true] false yields false (vacuous substitution) 

*   [x:=true] (λy:Bool. if y then x else false) yields \y:Bool. if y then true else false 

*   [x:=true] (λy:Bool. x) yields \y:Bool. true 

*   [x:=true] (λy:Bool. y) yields \y:Bool. y 

*   [x:=true] (λx:Bool. x) yields \x:Bool. x

    The last example is very important: substituting x with true in
    \x:Bool. x does *not* yield \x:Bool. true!  The reason for
    this is that the x in the body of \x:Bool. x is *bound* by the
    abstraction: it is a new, local name that just happens to be
    spelled the same as some global name x. 

    Here is the definition, informally...

```

[x:=s]x               = s

[x:=s]y               = y                      if x ≠ y

[x:=s]（λx:T[11]. t[12]）   = \x:T[11]. t[12]

[x:=s]（λy:T[11]. t[12]）   = \y:T[11]. [x:=s]t[12]      如果 x ≠ y

[x:=s]（t[1] t[2]）         = （[x:=s]t[1]） （[x:=s]t[2]）

[x:=s]true            = true

[x:=s]false           = false

[x:=s]（如果 t[1]那么 t[2]否则 t[3]） =

如果[x:=s]t[1]那么[x:=s]t[2]否则[x:=s]t[3]

    ...并正式地：

```
Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' ⇒
      if beq_id x x' then s else t
  | tabs x' T t[1] ⇒
      tabs x' T (if beq_id x x' then t[1] else ([x:=s] t[1]))
  | tapp t[1] t[2] ⇒
      tapp ([x:=s] t[1]) ([x:=s] t[2])
  | ttrue ⇒
      ttrue
  | tfalse ⇒
      tfalse
  | tif t[1] t[2] t[3] ⇒
      tif ([x:=s] t[1]) ([x:=s] t[2]) ([x:=s] t[3])
  end

where "'[' x ':=' s ']' t" := (subst x s t).

```

    *技术说明*：如果我们

    考虑替换的术语 s 的情况

    其他一些术语中的变量，本身可能包含自由变量。

    由于我们这里只关心定义步骤关系

    对封闭术语（即包括\x：Bool。x 这样的术语

    绑定所有提到的变量），我们可以避免这种情况

    这里有额外的复杂性，但在形式化时必须处理

    更丰富的语言。

    例如，参见[[Aydemir 2008]](Bib.html#Aydemir 2008)以获取进一步讨论

    这个问题的讨论。

#### 练习：3 星（substi）

    我们上面给出的定义使用了 Coq 的 Fixpoint 功能

    将替换定义为*函数*。 假设我们

    想要将替换定义为归纳关系 substi。

    我们已经通过提供归纳标题和

    其中一个构造函数；您的任务是填写其余部分

    构造并证明您定义的关系与之重合

    使用上面给出的函数。

```
Inductive substi (s:tm) (x:id) : tm → tm → Prop :=
  | s_var1 :
      substi s x (tvar x) s
  (* FILL IN HERE *)
.

Hint Constructors substi.

Theorem substi_correct : ∀s x t t',
  [x:=s]t = t' ↔ substi s x t t'.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

### Reduction

    The small-step reduction relation for STLC now follows the
    same pattern as the ones we have seen before.  Intuitively, to
    reduce a function application, we first reduce its left-hand
    side (the function) until it becomes an abstraction; then we
    reduce its right-hand side (the argument) until it is also a
    value; and finally we substitute the argument for the bound
    variable in the body of the abstraction.  This last rule, written
    informally as

```

(λx:T.t12) v[2] ⇒ [x:=v[2]]t[12]

    传统上称为“β-还原”。

                        值 v[2]

        |

                        (ST_AppAbs)

        |

* * *

        |

                        （λx：T.t12）v[2] ⇒ [x:=v[2]]t[12]

        |

                    |

                        t[1] ⇒ t[1]'

        |

                        (ST_App1)

        |

* * *

        |

                        t[1] t[2] ⇒ t[1]' t[2]

        |

                    |

                        值 v[1]

        |

                    |

                        t[2] ⇒ t[2]'

        |

                        (ST_App2)

        |

* * *

        |

                        v[1] t[2] ⇒ v[1] t[2]'

        |

                    |

    ...再加上布尔值的常规规则：

        |

                        （ST_IfTrue）

        |

* * *

        |

                        （如果 true 那么 t[1]否则 t[2]） ⇒ t[1]

        |

                    |

        |

                        （ST_IfFalse）

        |

* * *

        |

                        (如果 false 则 t[1]否则 t[2]) ⇒ t[2]

        |

                    |

                        t[1] ⇒ t[1]'

        |

                        （ST_If）

        |

* * *

        |

                        （如果 t[1]那么 t[2]否则 t[3]） ⇒ （如果 t[1]'那么 t[2]否则 t[3]）

        |

                    |

    正式地：

```
Reserved Notation "t1 '⇒' t2" (at level 40).

Inductive step : tm → tm → Prop :=
  | ST_AppAbs : ∀x T t[12] v[2],
         value v[2] →
         (tapp (tabs x T t[12]) v[2]) ⇒ [x:=v[2]]t[12]
  | ST_App1 : ∀t[1] t[1]' t[2],
         t[1] ⇒ t[1]' →
         tapp t[1] t[2] ⇒ tapp t[1]' t[2]
  | ST_App2 : ∀v[1] t[2] t[2]',
         value v[1] →
         t[2] ⇒ t[2]' →
         tapp v[1] t[2] ⇒ tapp v[1]  t[2]'
  | ST_IfTrue : ∀t[1] t[2],
      (tif ttrue t[1] t[2]) ⇒ t[1]
  | ST_IfFalse : ∀t[1] t[2],
      (tif tfalse t[1] t[2]) ⇒ t[2]
  | ST_If : ∀t[1] t[1]' t[2] t[3],
      t[1] ⇒ t[1]' →
      (tif t[1] t[2] t[3]) ⇒ (tif t[1]' t[2] t[3])

where "t1 '⇒' t2" := (step t[1] t[2]).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '⇒*' t2" := (multistep t[1] t[2]) (at level 40).

```

### 例子

    例子：

```
      (λx:Bool→Bool. x) (λx:Bool. x) ⇒* \x:Bool. x

    i.e.,

```

idBB idB ⇒* idB

```
Lemma step_example1 :
  (tapp idBB idB) ⇒* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl. Qed.

```

    例子：

```
      (λx:Bool→Bool. x) ((λx:Bool→Bool. x) (λx:Bool. x))
            ⇒* \x:Bool. x

    i.e.,

```

（idBB（idBB idB）） ⇒* idB。

```
Lemma step_example2 :
  (tapp idBB (tapp idBB idB)) ⇒* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl. Qed.

```

    例子：

```
      (λx:Bool→Bool. x) 
         (λx:Bool. if x then false else true) 
         true
            ⇒* false

    i.e.,

```

（idBB notB）ttrue ⇒* tfalse。

```
Lemma step_example3 :
  tapp (tapp idBB notB) ttrue ⇒* tfalse.
Proof.
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_IfTrue. apply multi_refl. Qed.

```

    例子：

```
      (λx:Bool → Bool. x) 
         ((λx:Bool. if x then false else true) true)
            ⇒* false

    i.e.,

```

idBB（notB ttrue） ⇒* tfalse。

```
Lemma step_example4 :
  tapp idBB (tapp notB ttrue) ⇒* tfalse.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_IfTrue.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl. Qed.

```

    我们可以使用 Types 章节中定义的 normalize 策略

    简化这些证明。

```
Lemma step_example1' :
  (tapp idBB idB) ⇒* idB.
Proof. normalize. Qed.

Lemma step_example2' :
  (tapp idBB (tapp idBB idB)) ⇒* idB.
Proof. normalize. Qed.

Lemma step_example3' :
  tapp (tapp idBB notB) ttrue ⇒* tfalse.
Proof. normalize. Qed.

Lemma step_example4' :
  tapp idBB (tapp notB ttrue) ⇒* tfalse.
Proof. normalize. Qed.

```

#### 练习：2 星（step_example3）

    尝试使用和不使用 normalize 来做这个。

```
Lemma step_example5 :
       tapp (tapp idBBBB idBB) idB
  ⇒* idB.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma step_example5_with_normalize :
       tapp (tapp idBBBB idBB) idB
  ⇒* idB.
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```

## Typing

    Next we consider the typing relation of the STLC.

```

### 上下文

    *问题*：术语“xy”的类型是什么？

    *答案*：这取决于 x 和 y 的类型！

    即，为了给一个术语分配一个类型，我们需要知道

    我们应该对其自由变量的类型做出什么假设

    变量。

    这将引导我们进入一个三元*类型判断*，非正式地

    写作Γ ⊢ t ∈ T，其中Γ是一个

    “类型上下文” - 从变量到其类型的映射。

    非正式地，我们将写作Γ，x：T 表示“扩展部分

    函数Γ也将 x 映射到 T。”形式上，我们使用

    函数扩展以向部分映射添加绑定。

```
Definition context := partial_map ty.

```

### 类型关系

                        Γ x = T

        |

                        （T_Var）

        |

* * *

        |

                        Γ ⊢ x ∈ T

        |

                    |

                        Γ , x:T[11] ⊢ t[12] ∈ T[12]

        |

                        (T_Abs)

        |

* * *

        |

                        Γ ⊢ \x:T[11].t12 ∈ T[11]->T[12]

        |

                    |

                        Γ ⊢ t[1] ∈ T[11]->T[12]

        |

                    |

                        Γ ⊢ t[2] ∈ T[11]

        |

                        (T_App)

        |

* * *

        |

                        Γ ⊢ t[1] t[2] ∈ T[12]

        |

                    |

        |

                        (T_True)

        |

* * *

        |

                        Γ ⊢ true ∈ Bool

        |

                    |

        |

                        (T_False)

        |

* * *

        |

                        Γ ⊢ false ∈ Bool

        |

                    |

                        Γ ⊢ t[1] ∈ Bool    Γ ⊢ t[2] ∈ T    Γ ⊢ t[3] ∈ T

        |

                        (T_If)

        |

* * *

        |

                        Γ ⊢ if t[1] then t[2] else t[3] ∈ T

        |

                    |

    我们可以将三元关系 Γ ⊢ t ∈ T 理解为：

    "对于项 t，我们可以使用类型 T 作为类型，使用如下类型

    t 的自由变量是上下文中指定的变量

    Γ。"

```
Reserved Notation "Gamma '⊢' t '∈' T" (at level 40).

Inductive has_type : context → tm → ty → Prop :=
  | T_Var : ∀Γ x T,
      Γ x = Some T →
      Γ ⊢ tvar x ∈ T
  | T_Abs : ∀Γ x T[11] T[12] t[12],
      update Γ x T[11] ⊢ t[12] ∈ T[12] →
      Γ ⊢ tabs x T[11] t[12] ∈ TArrow T[11] T[12]
  | T_App : ∀T[11] T[12] Γ t[1] t[2],
      Γ ⊢ t[1] ∈ TArrow T[11] T[12] →
      Γ ⊢ t[2] ∈ T[11] →
      Γ ⊢ tapp t[1] t[2] ∈ T[12]
  | T_True : ∀Γ,
       Γ ⊢ ttrue ∈ TBool
  | T_False : ∀Γ,
       Γ ⊢ tfalse ∈ TBool
  | T_If : ∀t[1] t[2] t[3] T Γ,
       Γ ⊢ t[1] ∈ TBool →
       Γ ⊢ t[2] ∈ T →
       Γ ⊢ t[3] ∈ T →
       Γ ⊢ tif t[1] t[2] t[3] ∈ T

where "Gamma '⊢' t '∈' T" := (has_type Γ t T).

Hint Constructors has_type.

```

### 例子

```
Example typing_example_1 :
  empty ⊢ tabs x TBool (tvar x) ∈ TArrow TBool TBool.
Proof.
  apply T_Abs. apply T_Var. reflexivity. Qed.

```

    请注意，由于我们将 has_type 构造函数添加到提示中

    数据库，auto 实际上可以立即解决这个问题。

```
Example typing_example_1' :
  empty ⊢ tabs x TBool (tvar x) ∈ TArrow TBool TBool.
Proof. auto. Qed.

```

    另一个例子：

```
       empty ⊢ \x:A. λy:A→A. y (y x))
             ∈ A → (A→A) → A.

```

    示�� typing_example_2：

empty ⊢

(tabs x TBool

(tabs y (TArrow TBool TBool)

(tapp (tvar y) (tapp (tvar y) (tvar x))))) ∈

(TArrow TBool (TArrow (TArrow TBool TBool) TBool)。

    证明，使用 update_eq 自动完成。

应用 T_Abs。

应用 T_Abs。

应用 T_App。应用 T_Var...

应用 T_App。应用 T_Var...

应用 T_Var...

    证毕。

```

#### Exercise: 2 stars, optional (typing_example_2_full)

    Prove the same result without using auto, eauto, or
    eapply (or ...).

```

示例 typing_example_2_full：

empty ⊢

(tabs x TBool

(tabs y (TArrow TBool TBool)

(tapp (tvar y) (tapp (tvar y) (tvar x))))) ∈

(TArrow TBool (TArrow (TArrow TBool TBool) TBool))。

证明。

(* 在此填写*) 已承认。

```

    ☐ 

#### Exercise: 2 stars (typing_example_3)

    Formally prove the following typing derivation holds:  

```

empty ⊢ \x:Bool→B. λy:Bool→Bool. λz:Bool.

y (x z)

∈ T。

```
Example typing_example_3 :
  ∃T,
    empty ⊢
      (tabs x (TArrow TBool TBool)
         (tabs y (TArrow TBool TBool)
            (tabs z TBool
               (tapp (tvar y) (tapp (tvar x) (tvar z)))))) ∈
      T.
Proof with auto.
  (* FILL IN HERE *) Admitted.

```

    ☐

    我们还可以展示项是*不*可类型化的。例如，让我们

    正式检查是否没有类型推导分配类型

    对于项 \x:Bool。 \y:Bool，x y — 即，

```
    ¬ ∃T,
        empty ⊢ \x:Bool. λy:Bool, x y : T.

```

    示例 typing_nonexample_1：

¬ ∃T，

empty ⊢

(tabs x TBool

(tabs y TBool

(tapp (tvar x) (tvar y)))) ∈

T。

    证明。

引入 Hc。反演 Hc。

(* 在这里清除策略对于整理我们将不再需要的上下文部分非常有用。*)

反演 H。替换。清除 H。

反演 H[5]。替换。清除 H[5]。

反演 H[4]。替换。清除 H[4]。

反演 H[2]。替换。清除 H[2]。

反演 H[5]。替换。清除 H[5]。

反演 H[1]。证毕。

```

#### Exercise: 3 stars, optional (typing_nonexample_3)

    Another nonexample:

```

¬ (∃S, ∃T,

empty ⊢ \x:S. x x ∈ T)。

```
Example typing_nonexample_3 :
  ¬ (∃S, ∃T,
        empty ⊢
          (tabs x S
             (tapp (tvar x) (tvar x))) ∈
          T).
Proof.
  (* FILL IN HERE *) Admitted.

```

    ☐

```
End STLC.

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
