# 更多关于简单类型 λ 演算的内容

```

```

导入 Maps。

导入 Types。

导入 Smallstep。

导入 Stlc。

```

# Simple Extensions to STLC

    The simply typed lambda-calculus has enough structure to make its
    theoretical properties interesting, but it is not much of a
    programming language.

    In this chapter, we begin to close the gap with real-world
    languages by introducing a number of familiar features that have
    straightforward treatments at the level of typing. 

## Numbers

    As we saw in exercise stlc_arith at the end of the StlcProp
    chapter, adding types, constants, and primitive operations for
    natural numbers is easy — basically just a matter of combining
    the Types and Stlc chapters.  Adding more realistic
    numeric types like machine integers and floats is also
    straightforward, though of course the specifications of the
    numeric primitives become more fiddly. 

## Let Bindings

    When writing a complex expression, it is useful to be able
    to give names to some of its subexpressions to avoid repetition
    and increase readability.  Most languages provide one or more ways
    of doing this.  In OCaml (and Coq), for example, we can write let x=t[1] in t[2] to mean "reduce the expression t[1] to a value and
    bind the name x to this value while reducing t[2]."

    Our let-binder follows OCaml in choosing a standard
    *call-by-value* evaluation order, where the let-bound term must
    be fully reduced before reduction of the let-body can begin.
    The typing rule T_Let tells us that the type of a let can be
    calculated by calculating the type of the let-bound term,
    extending the context with a binding with this type, and in this
    enriched context calculating the type of the body (which is then
    the type of the whole let expression).

    At this point in the book, it's probably easier simply to look at
    the rules defining this new feature than to wade through a lot of
    English text conveying the same information.  Here they are: 

    Syntax:

```

    t ::=                术语

        | ...               (其他术语与之前相同)

        | 让 x=t 在 t 中      让绑定

```

    Reduction:

                        t[1] ⇒ t[1]'
           |

                        (ST_Let1)  
           |

* * *

           |

                        let x=t[1] in t[2] ⇒ let x=t[1]' in t[2]
           |

                     |

           |

                        (ST_LetValue)  
           |

* * *

           |

                        let x=v[1] in t[2] ⇒ [x:=v[1]]t[2]
           |

                     |

    Typing:

                        Γ ⊢ t[1] : T[1]      Gamma, x:T[1] ⊢ t[2] : T[2]
           |

                        (T_Let)  
           |

* * *

           |

                        Γ ⊢ let x=t[1] in t[2] : T[2]
           |

                     |

## Pairs

    Our functional programming examples in Coq have made
    frequent use of *pairs* of values.  The type of such a pair is
    called a *product type*.

    The formalization of pairs is almost too simple to be worth
    discussing.  However, let's look briefly at the various parts of
    the definition to emphasize the common pattern. 

    In Coq, the primitive way of extracting the components of a pair
    is *pattern matching*.  An alternative is to take fst and
    snd — the first- and second-projection operators — as
    primitives.  Just for fun, let's do our pairs this way.  For
    example, here's how we'd write a function that takes a pair of
    numbers and returns the pair of their sum and difference:

```

    λx : Nat*Nat.

        让和 = x.fst + x.snd 在

        让差值 = x.fst - x.snd

        (和,差)

```

    Adding pairs to the simply typed lambda-calculus, then, involves
    adding two new forms of term — pairing, written (t[1],t[2]), and
    projection, written t.fst for the first projection from t and
    t.snd for the second projection — plus one new type constructor,
    T[1]*T[2], called the *product* of T[1] and T[2].  

    Syntax:

```

    t ::=                术语

        | (t,t)             对

        | t.fst             第一投影

        | t.snd             第二投影

        | ...

    v ::=                值

        | (v,v)             对值

        | ...

    T ::=                类型

        | T * T             乘积类型

        | ...

```

    For reduction, we need several new rules specifying how pairs and
    projection behave. 

                        t[1] ⇒ t[1]'
           |

                        (ST_Pair1)  
           |

* * *

           |

                        (t[1],t[2]) ⇒ (t[1]',t[2])
           |

                     |

                        t[2] ⇒ t[2]'
           |

                        (ST_Pair2)  
           |

* * *

           |

                        (v[1],t[2]) ⇒ (v[1],t[2]')
           |

                     |

                        t[1] ⇒ t[1]'
           |

                        (ST_Fst1)  
           |

* * *

           |

                        t[1].fst ⇒ t[1]'.fst
           |

                     |

           |

                        (ST_FstPair)  
           |

* * *

           |

                        (v[1],v[2]).fst ⇒ v[1]
           |

                     |

                        t[1] ⇒ t[1]'
           |

                        (ST_Snd1)  
           |

* * *

           |

                        t[1].snd ⇒ t[1]'.snd
           |

                     |

           |

                        (ST_SndPair)  
           |

* * *

           |

                        (v[1],v[2]).snd ⇒ v[2]
           |

                     |

    Rules ST_FstPair and ST_SndPair say that, when a fully
    reduced pair meets a first or second projection, the result is
    the appropriate component.  The congruence rules ST_Fst1 and
    ST_Snd1 allow reduction to proceed under projections, when the
    term being projected from has not yet been fully reduced.
    ST_Pair1 and ST_Pair2 reduce the parts of pairs: first the
    left part, and then — when a value appears on the left — the right
    part.  The ordering arising from the use of the metavariables v
    and t in these rules enforces a left-to-right evaluation
    strategy for pairs.  (Note the implicit convention that
    metavariables like v and v[1] can only denote values.)  We've
    also added a clause to the definition of values, above, specifying
    that (v[1],v[2]) is a value.  The fact that the components of a pair
    value must themselves be values ensures that a pair passed as an
    argument to a function will be fully reduced before the function
    body starts executing. 

    The typing rules for pairs and projections are straightforward. 

                        Γ ⊢ t[1] : T[1]       Γ ⊢ t[2] : T[2]
           |

                        (T_Pair)  
           |

* * *

           |

                        Γ ⊢ (t[1],t[2]) : T[1]*T[2]
           |

                     |

                        Γ ⊢ t[1] : T[11]*T[12]
           |

                        (T_Fst)  
           |

* * *

           |

                        Γ ⊢ t[1].fst : T[11]
           |

                     |

                        Γ ⊢ t[1] : T[11]*T[12]
           |

                        (T_Snd)  
           |

* * *

           |

                        Γ ⊢ t[1].snd : T[12]
           |

                     |

    T_Pair says that (t[1],t[2]) has type T[1]*T[2] if t[1] has
   type T[1] and t[2] has type T[2].  Conversely, T_Fst and T_Snd
   tell us that, if t[1] has a product type T[11]*T[12] (i.e., if it
   will reduce to a pair), then the types of the projections from
   this pair are T[11] and T[12]. 

## Unit

    Another handy base type, found especially in languages in
    the ML family, is the singleton type Unit.  It has a single element — the term constant unit (with a small
    u) — and a typing rule making unit an element of Unit.  We
    also add unit to the set of possible values — indeed, unit is
    the *only* possible result of reducing an expression of type
    Unit. 

    Syntax:

```

    t ::=                术语

        | unit              单元值

        | ...

    v ::=                值

        | unit              单元

        | ...

    T ::=                类型

        | Unit              单元类型

        | ...

```

    Typing:

           |

                        (T_Unit)  
           |

* * *

           |

                        Γ ⊢ unit : Unit
           |

                     |

    It may seem a little strange to bother defining a type that
    has just one element — after all, wouldn't every computation
    living in such a type be trivial?

    This is a fair question, and indeed in the STLC the Unit type is
    not especially critical (though we'll see two uses for it below).
    Where Unit really comes in handy is in richer languages with
    *side effects* — e.g., assignment statements that mutate
    variables or pointers, exceptions and other sorts of nonlocal
    control structures, etc.  In such languages, it is convenient to
    have a type for the (trivial) result of an expression that is
    evaluated only for its effect. 

## Sums

    Many programs need to deal with values that can take two distinct
   forms.  For example, we might identify employees in an accounting
   application using *either* their name *or* their id number.
   A search function might return *either* a matching value *or* an
   error code.

    These are specific examples of a binary *sum type* (sometimes called
   a *disjoint union*), which describes a set of values drawn from 
   one of two given types, e.g.:

```

    Nat + Bool

```

    We create elements of these types by *tagging* elements of
    the component types.  For example, if n is a Nat then inl n
    is an element of Nat+Bool; similarly, if b is a Bool then
    inr b is a Nat+Bool.  The names of the tags inl and inr
    arise from thinking of them as functions

```

inl : Nat -> Nat + Bool

inr : Bool -> Nat + Bool

```

    that "inject" elements of Nat or Bool into the left and right
    components of the sum type Nat+Bool.  (But note that we don't
    actually treat them as functions in the way we formalize them:
    inl and inr are keywords, and inl t and inr t are primitive
    syntactic forms, not function applications.) 

    In general, the elements of a type T[1] + T[2] consist of the
    elements of T[1] tagged with the token inl, plus the elements of
    T[2] tagged with inr. 

    One important usage of sums is signaling errors:

```

    div : Nat -> Nat -> (Nat + Unit) =

    除法 =

    λx:Nat. λy:Nat.

        如果 y 是零则

        inr 单元

        否则

        inl ...

```

    The type Nat + Unit above is in fact isomorphic to option nat in Coq — i.e., it's easy to write functions that translate
    back and forth. 

    To *use* elements of sum types, we introduce a case
    construct (a very simplified form of Coq's match) to destruct
    them. For example, the following procedure converts a Nat+Bool
    into a Nat: 

```

    获取自然数 =

    λx:Nat+Bool.

        对 x 进行分析

        inl n => n

        | inr b => 如果 b 则 1 否则 0

```

    More formally... 

    Syntax:

```

    t ::=                术语

        | inl T t           标记（左）

        | inr T t           标记（右）

        | case t of         案例

            inl x => t

            | inr x => t

        | ...

    v ::=                值

        | inl T v           标记值（左）

        | inr T v           标记值（右）

        | ...

    T ::=                类型

        | T + T             和类型

        | ...

```

    Reduction:

                        t[1] ⇒ t[1]'
           |

                        (ST_Inl)  
           |

* * *

           |

                        inl T t[1] ⇒ inl T t[1]'
           |

                     |

                        t[1] ⇒ t[1]'
           |

                        (ST_Inr)  
           |

* * *

           |

                        inr T t[1] ⇒ inr T t[1]'
           |

                     |

                        t[0] ⇒ t[0]'
           |

                        (ST_Case)  
           |

* * *

           |

                        case t[0] of inl x[1] ⇒ t[1] &#124; inr x[2] ⇒ t[2] ⇒
           |

                     |

                        case t[0]' of inl x[1] ⇒ t[1] &#124; inr x[2] ⇒ t[2]
           |

                     |

           |

                        (ST_CaseInl)  
           |

* * *

           |

                        case (inl T v[0]) of inl x[1] ⇒ t[1] &#124; inr x[2] ⇒ t[2]
           |

                     |

                        ⇒  [x[1]:=v[0]]t[1]
           |

                     |

           |

                        (ST_CaseInr)  
           |

* * *

           |

                        case (inr T v[0]) of inl x[1] ⇒ t[1] &#124; inr x[2] ⇒ t[2]
           |

                     |

                        ⇒  [x[2]:=v[0]]t[2]
           |

                     |

    Typing:

                        Γ ⊢ t[1] :  T[1]
           |

                        (T_Inl)  
           |

* * *

           |

                        Γ ⊢ inl T[2] t[1] : T[1] + T[2]
           |

                     |

                        Γ ⊢ t[1] : T[2]
           |

                        (T_Inr)  
           |

* * *

           |

                        Γ ⊢ inr T[1] t[1] : T[1] + T[2]
           |

                     |

                        Γ ⊢ t[0] : T[1]+T[2]
           |

                     |

                        Γ , x[1]:T[1] ⊢ t[1] : T
           |

                     |

                        Γ , x[2]:T[2] ⊢ t[2] : T
           |

                        (T_Case)  
           |

* * *

           |

                        Γ ⊢ case t[0] of inl x[1] ⇒ t[1] &#124; inr x[2] ⇒ t[2] : T
           |

                     |

    We use the type annotation in inl and inr to make the typing 
    relation simpler, similarly to what we did for functions. 

    Without this extra information, the typing rule T_Inl, for
    example, would have to say that, once we have shown that t[1] is
    an element of type T[1], we can derive that inl t[1] is an element
    of T[1] + T[2] for *any* type T[2].  For example, we could derive both
    inl 5 : Nat + Nat and inl 5 : Nat + Bool (and infinitely many
    other types).  This peculiarity (technically, a failure of
    uniqueness of types) would mean that we cannot build a
    typechecking algorithm simply by "reading the rules from bottom to
    top" as we could for all the other features seen so far.

    There are various ways to deal with this difficulty.  One simple
    one — which we've adopted here — forces the programmer to
    explicitly annotate the "other side" of a sum type when performing
    an injection.  This is a bit heavy for programmers (so real
    languages adopt other solutions), but it is easy to understand and
    formalize. 

## Lists

    The typing features we have seen can be classified into *base types* like Bool, and *type constructors* like → and * that
    build new types from old ones.  Another useful type constructor is
    List.  For every type T, the type List T describes
    finite-length lists whose elements are drawn from T.

    In principle, we could encode lists using pairs, sums and
    *recursive* types. But giving semantics to recursive types is
    non-trivial. Instead, we'll just discuss the special case of lists
    directly.

    Below we give the syntax, semantics, and typing rules for lists.
    Except for the fact that explicit type annotations are mandatory
    on nil and cannot appear on cons, these lists are essentially
    identical to those we built in Coq.  We use lcase to destruct
    lists, to avoid dealing with questions like "what is the head of
    the empty list?" 

    For example, here is a function that calculates the sum of
    the first two elements of a list of numbers:

```

    λx:List Nat.

    lcase x of nil -> 0

        | a::x' -> lcase x' of nil -> a

                    | b::x'' -> a+b

```

    Syntax:

```

    t ::=                术语

        | nil T

        | cons t t

        | lcase t of nil -> t | x::x -> t

        | ...

    v ::=                值

        | nil T             空值

        | cons v v          cons 值

        | ...

    T ::=                类型

        | List T            Ts 的列表

        | ...

```

    Reduction:

                        t[1] ⇒ t[1]'
           |

                        (ST_Cons1)  
           |

* * *

           |

                        cons t[1] t[2] ⇒ cons t[1]' t[2]
           |

                     |

                        t[2] ⇒ t[2]'
           |

                        (ST_Cons2)  
           |

* * *

           |

                        cons v[1] t[2] ⇒ cons v[1] t[2]'
           |

                     |

                        t[1] ⇒ t[1]'
           |

                        (ST_Lcase1)  
           |

* * *

           |

                        (lcase t[1] of nil → t[2] &#124; xh::xt → t[3]) ⇒
           |

                     |

                        (lcase t[1]' of nil → t[2] &#124; xh::xt → t[3])
           |

                     |

           |

                        (ST_LcaseNil)  
           |

* * *

           |

                        (lcase nil T of nil → t[2] &#124; xh::xt → t[3])
           |

                     |

                        ⇒ t[2]
           |

                     |

           |

                        (ST_LcaseCons)  
           |

* * *

           |

                        (lcase (cons vh vt) of nil → t[2] &#124; xh::xt → t[3])
           |

                     |

                        ⇒ [xh:=vh,xt:=vt]t[3]
           |

                     |

    Typing:

           |

                        (T_Nil)  
           |

* * *

           |

                        Γ ⊢ nil T : List T
           |

                     |

                        Γ ⊢ t[1] : T      Γ ⊢ t[2] : List T
           |

                        (T_Cons)  
           |

* * *

           |

                        Γ ⊢ cons t[1] t[2]: List T
           |

                     |

                        Γ ⊢ t[1] : List T[1]
           |

                     |

                        Γ ⊢ t[2] : T
           |

                     |

                        Γ , h:T[1], t:List T[1] ⊢ t[3] : T
           |

                        (T_Lcase)  
           |

* * *

           |

                        Γ ⊢ (lcase t[1] of nil → t[2] &#124; h::t → t[3]) : T
           |

                     |

## General Recursion

    Another facility found in most programming languages (including
    Coq) is the ability to define recursive functions.  For example,
    we might like to be able to define the factorial function like
    this:

```

    阶乘 = λx:Nat.

                如果 x=0 则 1 否则 x * (阶乘 (前驱 x)))

```

    Note that the right-hand side of this binder mentions the variable
   being bound — something that is not allowed by our formalization of
   let above.  

    Directly formalizing this "recursive definition" mechanism is possible, 
   but it requires a bit of extra effort: in particular, we'd have to 
   pass around an "environment" of recursive function definitions in 
   the definition of the step relation. 

    Here is another way of presenting recursive functions that is equally
    powerful (though not quite as convenient for the programmer) and 
    more straightforward to formalize: instead of writing recursive 
    definitions, we define a *fixed-point operator* called fix 
    that performs the "unfolding" of the recursive definition in the 
    right-hand side as needed, during reduction.  

    For example, instead of 

```

    阶乘 = λx:Nat.

                如果 x=0 则 1 否则 x * (阶乘 (前驱 x)))

```

    we will write:

```

    阶乘 =

        修复

            (λf:Nat->Nat.

            λx:Nat.

                如果 x=0 则 1 否则 x * (f (前驱 x)))

```

    We can derive the latter from the former as follows:

*   In the right-hand side of the definition of fact, replace recursive references to fact by a fresh variable f. 

*   Add an abstraction binding f at the front, with an appropriate type annotation. (Since we are using f in place of fact, which had type Nat→Nat, we should require f to have the same type.) The new abstraction has type (Nat→Nat) → (Nat→Nat). 

*   Apply fix to this abstraction. This application has type Nat→Nat. 

*   Use all of this as the right-hand side of an ordinary let-binding for fact.

    The intuition is that the higher-order function f passed
    to fix is a *generator* for the fact function: if f is
    applied to a function that "approximates" the desired behavior of
    fact up to some number n (that is, a function that returns
    correct results on inputs less than or equal to n but we don't
    care what it does on inputs greater than n), then f returns a
    slightly better approximation to fact — a function that returns
    correct results for inputs up to n+1.  Applying fix to this
    generator returns its *fixed point*, which is a function that
    gives the desired behavior for all inputs n.

    (The term "fixed point" is used here in exactly the same sense as
    in ordinary mathematics, where a fixed point of a function f is
    an input x such that f(x) = x.  Here, a fixed point of a
    function F of type (Nat→Nat)->(Nat→Nat) is a function f of
    type Nat→Nat such that F f behaves the same as f.) 

    Syntax:

```

    t ::=                术语

        | 修复 t             不动点运算符

        | ...

```

    Reduction:

                        t[1] ⇒ t[1]'
           |

                        (ST_Fix1)  
           |

* * *

           |

                        fix t[1] ⇒ fix t[1]'
           |

                     |

           |

                        (ST_FixAbs)  
           |

* * *

           |

                        fix (λxf:T[1].t2) ⇒ [xf:=fix (λxf:T[1].t2)] t[2]
           |

                     |

    Typing:

                        Γ ⊢ t[1] : T[1]->T[1]
           |

                        (T_Fix)  
           |

* * *

           |

                        Γ ⊢ fix t[1] : T[1]
           |

                     |

    Let's see how ST_FixAbs works by reducing fact 3 = fix F 3,
    where 

```

    F = (λf. λx. 如果 x=0 则 1 否则 x * (f (前驱 x)))

```

    (type annotations are omitted for brevity).

```

    修复 F 3

```

    ⇒ ST_FixAbs + ST_App1 

```

    (λx. 如果 x=0 则 1 否则 x * (修复 F (前驱 x))) 3

```

    ⇒ ST_AppAbs 

```

    如果 3=0 则 1 否则 3 * (修复 F (前驱 3))

```

    ⇒ ST_If0_Nonzero 

```

    3 * (修复 F (前驱 3))

```

    ⇒ ST_FixAbs + ST_Mult2 

```

    3 * ((λx. 如果 x=0 则 1 否则 x * (修复 F (前驱 x))) (前驱 3))

```

    ⇒ ST_PredNat + ST_Mult2 + ST_App2 

```

    3 * ((λx. 如果 x=0 则 1 否则 x * (修复 F (前驱 x))) 2)

```

    ⇒ ST_AppAbs + ST_Mult2 

```

    3 * (如果 2=0 则 1 否则 2 * (修复 F (前驱 2)))

```

    ⇒ ST_If0_Nonzero + ST_Mult2 

```

    3 * (2 * (修复 F (前驱 2)))

```

    ⇒ ST_FixAbs + 2 x ST_Mult2 

```

    3 * (2 * ((λx. 如果 x=0 则 1 否则 x * (修复 F (前驱 x))) (前驱 2)))

```

    ⇒ ST_PredNat + 2 x ST_Mult2 + ST_App2 

```

    3 * (2 * ((λx. 如果 x=0 则 1 否则 x * (修复 F (前驱 x))) 1))

```

    ⇒ ST_AppAbs + 2 x ST_Mult2 

```

    3 * (2 * (如果 1=0 则 1 否则 1 * (修复 F (前驱 1))))

```

    ⇒ ST_If0_Nonzero + 2 x ST_Mult2 

```

    3 * (2 * (1 * (修复 F (前驱 1)))

```

    ⇒ ST_FixAbs + 3 x ST_Mult2 

```

    3 * (2 * (1 * ((λx. 如果 x=0 则 1 否则 x * (修复 F (前驱 x))) (前驱 1))))

```

    ⇒ ST_PredNat + 3 x ST_Mult2 + ST_App2 

```

    3 * (2 * (1 * ((λx. 如果 x=0 则 1 否则 x * (修复 F (前驱 x))) 0)))

```

    ⇒ ST_AppAbs + 3 x ST_Mult2 

```

    3 * (2 * (1 * (如果 0=0 则 1 否则 0 * (修复 F (前驱 0))))

```

    ⇒ ST_If0Zero + 3 x ST_Mult2 

```

    3 * (2 * (1 * 1))

```

    ⇒ ST_MultNats + 2 x ST_Mult2 

```

    3 * (2 * 1)

```

    ⇒ ST_MultNats + ST_Mult2 

```

    3 * 2

```

    ⇒ ST_MultNats 

```

    6

```

    One important point to note is that, unlike Fixpoint
    definitions in Coq, there is nothing to prevent functions defined
    using fix from diverging. 

#### Exercise: 1 star, optional (halve_fix)

    Translate this informal recursive definition into one using fix:

```

    halve =

        λx:Nat.

        如果 x=0 则 0

        否则如果 (前驱 x)=0 则 0

        否则 1 + (halve (前驱 (前驱 x))))

```

    (* FILL IN HERE *)

    ☐ 

#### Exercise: 1 star, optional (fact_steps)

    Write down the sequence of steps that the term fact 1 goes
    through to reduce to a normal form (assuming the usual reduction
    rules for arithmetic operations).

    (* FILL IN HERE *)

    ☐ 

    The ability to form the fixed point of a function of type T→T
    for any T has some surprising consequences.  In particular, it
    implies that *every* type is inhabited by some term.  To see this,
    observe that, for every type T, we can define the term

```

修复 (λx:T.x)

    通过 T_Fix 和 T_Abs，这个术语的类型为 T。通过 ST_FixAbs

    它一遍又一遍地减少自身。因此它是一个

    *发散元素* of T.

    更有用的是，这里有一个使用 fix 来定义的示例

    二参数递归函数：

```
    equal =
      fix
        (λeq:Nat->Nat->Bool.
           λm:Nat. λn:Nat.
             if m=0 then iszero n
             else if n=0 then false
             else eq (pred m) (pred n))

```

    最后，这里是一个使用 fix 来定义的示例

    *对*递归函数对（说明类型的事实

    T[1]在规则 T_Fix 中不必是函数类型）：

```
      evenodd =
        fix
          (λeo: (Nat->Bool * Nat->Bool).
             let e = λn:Nat. if n=0 then true  else eo.snd (pred n) in
             let o = λn:Nat. if n=0 then false else eo.fst (pred n) in
             (e,o))

      even = evenodd.fst
      odd  = evenodd.snd

```

```

## Records

    As a final example of a basic extension of the STLC, let's look
    briefly at how to define *records* and their types.  Intuitively,
    records can be obtained from pairs by two straightforward
    generalizations: they are n-ary (rather than just binary) and
    their fields are accessed by *label* (rather than position). 

    Syntax:

```

    t ::=                          术语

        | {i1=t1, ..., in=tn}         记录

        | t.i                         投影

        | ...

    v ::=                          值

        | {i1=v1, ..., in=vn}         记录值

        | ...

    T ::=                          类型

        | {i1:T1, ..., in:Tn}         记录类型

        | ...

```

    The generalization from products should be pretty obvious.  But 
   it's worth noticing the ways in which what we've actually written is
   even *more* informal than the informal syntax we've used in previous 
   sections and chapters: we've used "..." in several places to mean "any
   number of these," and we've omitted explicit mention of the usual
   side condition that the labels of a record should not contain any
   repetitions. 

    Reduction:

                        ti ⇒ ti'
           |

                        (ST_Rcd)  
           |

* * *

           |

                        {i[1]=v[1], ..., im=vm, in=ti, ...}
           |

                     |

                        ⇒ {i[1]=v[1], ..., im=vm, in=ti', ...}
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

    Again, these rules are a bit informal.  For example, the first rule
   is intended to be read "if ti is the leftmost field that is not a
   value and if ti steps to ti', then the whole record steps..."
   In the last rule, the intention is that there should only be one
   field called i, and that all the other fields must contain values. 

    The typing rules are also simple:

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

    There are several ways to approach formalizing the above
    definitions.

*   We can directly formalize the syntactic forms and inference rules, staying as close as possible to the form we've given them above. This is conceptually straightforward, and it's probably what we'd want to do if we were building a real compiler (in particular, it will allow us to print error messages in the form that programmers will find easy to understand). But the formal versions of the rules will not be very pretty or easy to work with, because all the ...s above will have to be replaced with explicit quantifications or comprehensions. For this reason, records are not included in the extended exercise at the end of this chapter. (It is still useful to discuss them informally here because they will help motivate the addition of subtyping to the type system when we get to the Sub chapter.) 

*   Alternatively, we could look for a smoother way of presenting records — for example, a binary presentation with one constructor for the empty record and another constructor for adding a single field to an existing record, instead of a single monolithic constructor that builds a whole record at once. This is the right way to go if we are primarily interested in studying the metatheory of the calculi with records, since it leads to clean and elegant definitions and proofs. Chapter Records shows how this can be done. 

*   Finally, if we like, we can avoid formalizing records altogether, by stipulating that record notations are just informal shorthands for more complex expressions involving pairs and product types. We sketch this approach in the next section.

```

### 编码记录（可选）

    让我们看看如何只使用对和单位来编码记录。

    首先，观察到我们可以使用任意大小的*元组*进行编码

    嵌套对和单位值。为了避免过载对

    符号（t[1]，t[2]），我们将使用没有标签的花括号来写

    减少元组，所以{}是空元组，{5}是单例

    元组，{5,6}是一个 2 元组（道义上与一对相同），

    {5,6,7}是三元组，等等。

```
      {}                 ---->  unit
      {t1, t2, ..., tn}  ---->  (t1, trest)
                                where {t2, ..., tn} ----> trest

```

    同样，我们可以使用嵌套乘积类型来编码元组类型：

```
      {}                 ---->  Unit
      {T1, T2, ..., Tn}  ---->  T1 * TRest
                                where {T2, ..., Tn} ----> TRest

```

    从元组中投影字段的操作可以被编码

    使用一系列第二个投影，然后是第一个投影：

```
      t.0        ---->  t.fst
      t.(n+1)    ---->  (t.snd).n

```

    接下来，假设记录标签上有一些完全排序，

    以便我们可以将每个标签与唯一的自然数关联起来。

    这个数字被称为*标签的位置*。例如，

    我们可能分配位置如下：

```
      LABEL   POSITION
      a       0
      b       1
      c       2
      ...     ...
      bar     1395
      ...     ...
      foo     4460
      ...     ...

```

    我们使用这些位置将记录值编码为元组（即，作为

    嵌套对）通过根据其位置对字段进行排序。

    例如：

```
      {a=5, b=6}      ---->   {5,6}
      {a=5, c=7}      ---->   {5,unit,7}
      {c=7, a=5}      ---->   {5,unit,7}
      {c=5, b=3}      ---->   {unit,3,5}
      {f=8,c=5,a=7}   ---->   {7,unit,5,unit,unit,8}
      {f=8,c=5}       ---->   {unit,unit,5,unit,unit,8}

```

    请注意，每个字段都出现在与其关联的位置上

    标签，元组的大小由带有标签的标签确定

    最高位置，并且我们用未使用的位置填充

    单位。

    我们对记录类型执行完全相同的操作：

```
      {a:Nat, b:Nat}      ---->   {Nat,Nat}
      {c:Nat, a:Nat}      ---->   {Nat,Unit,Nat}
      {f:Nat,c:Nat}       ---->   {Unit,Unit,Nat,Unit,Unit,Nat}

```

    最后，记录投影被编码为元组投影

    适当的位置：

```
      t.l  ---->  t.(position of l)

```

    检查原始的所有类型规则并不难

    “直接”呈现记录由此验证

    编码。（减少规则“几乎验证” — 不

    相当，因为编码重新排序字段。）

    当然，如果我们这样做

    碰巧使用具有标签 foo 的记录！但事情并不是

    实际上并不像它们看起来那么糟糕：例如，如果我们假设

    我们的编译器可以同时看到整个程序，我们可以

    *选择*标签的编号，以便我们分配小位置

    到最常用的标签。实际上，有工业

    本质上是这样做的编译器！

### 变体（可选）

    正如乘积可以推广到记录，和可以

    广义到 n 元标记类型称为*变体*。而不是

    T[1]+T[2]，我们可以写一些类似<l[1]:T[1],l[2]:T[2],...ln:Tn>

    其中 l[1]，l[2]，...是用于构建的字段标签

    实例和作为案例臂标签。

    这些 n 元变体几乎为我们提供了足够的机制来构建

    任意归纳数据类型，如列表和树

    scratch — 唯一缺少的是允许在 *递归* 中

    类型定义。我们不会在这里涵盖这一点，但详细

    可以在许多教科书中找到；例如，类型和

    编程语言[[Pierce 2002]](Bib.html#Pierce 2002)的示例的形式化版本。

```

# Exercise: Formalizing the Extensions

#### Exercise: 5 stars (STLC_extensions)

    In this exercise, you will formalize some of the extensions
    described in this chapter.  We've provided the necessary additions
    to the syntax of terms and types, and we've included a few
    examples that you can test your definitions with to make sure they
    are working as expected.  You'll fill in the rest of the
    definitions and extend all the proofs accordingly.

    To get you started, we've provided implementations for:

*   numbers

*   sums

*   lists

*   unit

    You need to complete the implementations for:

*   pairs

*   let (which involves binding)

*   fix

    A good strategy is to work on the extensions one at a time, in two
    passes, rather than trying to work through the file from start to
    finish in a single pass.  For each definition or proof, begin by
    reading carefully through the parts that are provided for you,
    referring to the text in the Stlc chapter for high-level
    intuitions and the embedded comments for detailed mechanics.

```

模块 STLCExtended。

```

### Syntax

```

归纳 ty：Type :=

| TArrow : ty → ty → ty

| TNat   : ty

| TUnit  : ty

| TProd  : ty → ty → ty

| TSum   : ty → ty → ty

| TList  : ty → ty.

归纳 tm：Type :=

(* 纯粹的 STLC *)

| tvar : id → tm

| tapp : tm → tm → tm

| tabs : id → ty → tm → tm

(* 数字 *)

| tnat : nat → tm

| tsucc : tm → tm

| tpred : tm → tm

| tmult : tm → tm → tm

| tif0  : tm → tm → tm → tm

(* 对 *)

| tpair : tm → tm → tm

| tfst : tm → tm

| tsnd : tm → tm

(* 单元 *)

| tunit : tm

(* let *)

| tlet : id → tm → tm → tm

(* 即，let x = t[1] in t[2] *)

(* 总和 *)

| tinl : ty → tm → tm

| tinr : ty → tm → tm

| tcase : tm → id → tm → id → tm → tm

(* 即，case t[0] of inl x[1] ⇒ t[1] | inr x[2] ⇒ t[2] *)

(* 列表 *)

| tnil : ty → tm

| tcons : tm → tm → tm

| tlcase : tm → tm → id → id → tm → tm

(* 即，lcase t[1] of | nil → t[2] | x::y → t[3] *)

(* 修复 *)

| tfix  : tm → tm.

```

    Note that, for brevity, we've omitted booleans and instead
    provided a single if[0] form combining a zero test and a
    conditional.  That is, instead of writing

```

    如果 x = 0 则 ... 否则 ...

```

    we'll write this:

```

    if0 x 则 ... 否则 ...

```

```

### 替换

```
Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar y ⇒
      if beq_id x y then s else t
  | tabs y T t[1] ⇒
      tabs y T (if beq_id x y then t[1] else (subst x s t[1]))
  | tapp t[1] t[2] ⇒
      tapp (subst x s t[1]) (subst x s t[2])
  | tnat n ⇒
      tnat n
  | tsucc t[1] ⇒
      tsucc (subst x s t[1])
  | tpred t[1] ⇒
      tpred (subst x s t[1])
  | tmult t[1] t[2] ⇒
      tmult (subst x s t[1]) (subst x s t[2])
  | tif0 t[1] t[2] t[3] ⇒
      tif0 (subst x s t[1]) (subst x s t[2]) (subst x s t[3])
  (* FILL IN HERE *)
  | tunit ⇒ tunit
  (* FILL IN HERE *)
  | tinl T t[1] ⇒
      tinl T (subst x s t[1])
  | tinr T t[1] ⇒
      tinr T (subst x s t[1])
  | tcase t[0] y[1] t[1] y[2] t[2] ⇒
      tcase (subst x s t[0])
         y[1] (if beq_id x y[1] then t[1] else (subst x s t[1]))
         y[2] (if beq_id x y[2] then t[2] else (subst x s t[2]))
  | tnil T ⇒
      tnil T
  | tcons t[1] t[2] ⇒
      tcons (subst x s t[1]) (subst x s t[2])
  | tlcase t[1] t[2] y[1] y[2] t[3] ⇒
      tlcase (subst x s t[1]) (subst x s t[2]) y[1] y[2]
        (if beq_id x y[1] then
           t[3]
         else if beq_id x y[2] then t[3]
              else (subst x s t[3]))
  (* FILL IN HERE *)
  | _ ⇒ t  (* ... and delete this line *)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

```

### 约简

    接下来我们定义语言的值。

```
Inductive value : tm → Prop :=
  | v_abs : ∀x T[11] t[12],
      value (tabs x T[11] t[12])
  (* Numbers are values: *)
  | v_nat : ∀n[1],
      value (tnat n[1])
  (* A pair is a value if both components are: *)
  | v_pair : ∀v[1] v[2],
      value v[1] →
      value v[2] →
      value (tpair v[1] v[2])
  (* A unit is always a value *)
  | v_unit : value tunit
  (* A tagged value is a value:  *)
  | v_inl : ∀v T,
      value v →
      value (tinl T v)
  | v_inr : ∀v T,
      value v →
      value (tinr T v)
  (* A list is a value iff its head and tail are values: *)
  | v_lnil : ∀T, value (tnil T)
  | v_lcons : ∀v[1] vl,
      value v[1] →
      value vl →
      value (tcons v[1] vl)
  .

Hint Constructors value.

Reserved Notation "t1 '⇒' t2" (at level 40).

Inductive step : tm → tm → Prop :=
  | ST_AppAbs : ∀x T[11] t[12] v[2],
         value v[2] →
         (tapp (tabs x T[11] t[12]) v[2]) ⇒ [x:=v[2]]t[12]
  | ST_App1 : ∀t[1] t[1]' t[2],
         t[1] ⇒ t[1]' →
         (tapp t[1] t[2]) ⇒ (tapp t[1]' t[2])
  | ST_App2 : ∀v[1] t[2] t[2]',
         value v[1] →
         t[2] ⇒ t[2]' →
         (tapp v[1] t[2]) ⇒ (tapp v[1] t[2]')
  (* nats *)
  | ST_Succ1 : ∀t[1] t[1]',
       t[1] ⇒ t[1]' →
       (tsucc t[1]) ⇒ (tsucc t[1]')
  | ST_SuccNat : ∀n[1],
       (tsucc (tnat n[1])) ⇒ (tnat (S n[1]))
  | ST_Pred : ∀t[1] t[1]',
       t[1] ⇒ t[1]' →
       (tpred t[1]) ⇒ (tpred t[1]')
  | ST_PredNat : ∀n[1],
       (tpred (tnat n[1])) ⇒ (tnat (pred n[1]))
  | ST_Mult1 : ∀t[1] t[1]' t[2],
       t[1] ⇒ t[1]' →
       (tmult t[1] t[2]) ⇒ (tmult t[1]' t[2])
  | ST_Mult2 : ∀v[1] t[2] t[2]',
       value v[1] →
       t[2] ⇒ t[2]' →
       (tmult v[1] t[2]) ⇒ (tmult v[1] t[2]')
  | ST_MultNats : ∀n[1] n[2],
       (tmult (tnat n[1]) (tnat n[2])) ⇒ (tnat (mult n[1] n[2]))
  | ST_If[01] : ∀t[1] t[1]' t[2] t[3],
       t[1] ⇒ t[1]' →
       (tif0 t[1] t[2] t[3]) ⇒ (tif0 t[1]' t[2] t[3])
  | ST_If0Zero : ∀t[2] t[3],
       (tif0 (tnat 0) t[2] t[3]) ⇒ t[2]
  | ST_If0Nonzero : ∀n t[2] t[3],
       (tif0 (tnat (S n)) t[2] t[3]) ⇒ t[3]
  (* pairs *)
  (* FILL IN HERE *)
  (* let *)
  (* FILL IN HERE *)
  (* sums *)
  | ST_Inl : ∀t[1] t[1]' T,
        t[1] ⇒ t[1]' →
        (tinl T t[1]) ⇒ (tinl T t[1]')
  | ST_Inr : ∀t[1] t[1]' T,
        t[1] ⇒ t[1]' →
        (tinr T t[1]) ⇒ (tinr T t[1]')
  | ST_Case : ∀t[0] t[0]' x[1] t[1] x[2] t[2],
        t[0] ⇒ t[0]' →
        (tcase t[0] x[1] t[1] x[2] t[2]) ⇒ (tcase t[0]' x[1] t[1] x[2] t[2])
  | ST_CaseInl : ∀v[0] x[1] t[1] x[2] t[2] T,
        value v[0] →
        (tcase (tinl T v[0]) x[1] t[1] x[2] t[2]) ⇒ [x[1]:=v[0]]t[1]
  | ST_CaseInr : ∀v[0] x[1] t[1] x[2] t[2] T,
        value v[0] →
        (tcase (tinr T v[0]) x[1] t[1] x[2] t[2]) ⇒ [x[2]:=v[0]]t[2]
  (* lists *)
  | ST_Cons1 : ∀t[1] t[1]' t[2],
       t[1] ⇒ t[1]' →
       (tcons t[1] t[2]) ⇒ (tcons t[1]' t[2])
  | ST_Cons2 : ∀v[1] t[2] t[2]',
       value v[1] →
       t[2] ⇒ t[2]' →
       (tcons v[1] t[2]) ⇒ (tcons v[1] t[2]')
  | ST_Lcase1 : ∀t[1] t[1]' t[2] x[1] x[2] t[3],
       t[1] ⇒ t[1]' →
       (tlcase t[1] t[2] x[1] x[2] t[3]) ⇒ (tlcase t[1]' t[2] x[1] x[2] t[3])
  | ST_LcaseNil : ∀T t[2] x[1] x[2] t[3],
       (tlcase (tnil T) t[2] x[1] x[2] t[3]) ⇒ t[2]
  | ST_LcaseCons : ∀v[1] vl t[2] x[1] x[2] t[3],
       value v[1]  →
       value vl  →
       (tlcase (tcons v[1] vl) t[2] x[1] x[2] t[3]) ⇒ (subst x[2] vl (subst x[1] v[1] t[3]))
  (* fix *)
  (* FILL IN HERE *)

where "t1 '⇒' t2" := (step t[1] t[2]).

Notation multistep := (multi step).
Notation "t1 '⇒*' t2" := (multistep t[1] t[2]) (at level 40).

Hint Constructors step.

```

### 类型

```
Definition context := partial_map ty.

```

    接下来我们定义类型规则。这些几乎是直接的

    上面显示的推理规则的转录。

```
Reserved Notation "Gamma '⊢' t '∈' T" (at level 40).

Inductive has_type : context → tm → ty → Prop :=
  (* Typing rules for proper terms *)
  | T_Var : ∀Γ x T,
      Γ x = Some T →
      Γ ⊢ (tvar x) ∈ T
  | T_Abs : ∀Γ x T[11] T[12] t[12],
      (update Γ x T[11]) ⊢ t[12] ∈ T[12] →
      Γ ⊢ (tabs x T[11] t[12]) ∈ (TArrow T[11] T[12])
  | T_App : ∀T[1] T[2] Γ t[1] t[2],
      Γ ⊢ t[1] ∈ (TArrow T[1] T[2]) →
      Γ ⊢ t[2] ∈ T[1] →
      Γ ⊢ (tapp t[1] t[2]) ∈ T[2]
  (* nats *)
  | T_Nat : ∀Γ n[1],
      Γ ⊢ (tnat n[1]) ∈ TNat
  | T_Succ : ∀Γ t[1],
      Γ ⊢ t[1] ∈ TNat →
      Γ ⊢ (tsucc t[1]) ∈ TNat
  | T_Pred : ∀Γ t[1],
      Γ ⊢ t[1] ∈ TNat →
      Γ ⊢ (tpred t[1]) ∈ TNat
  | T_Mult : ∀Γ t[1] t[2],
      Γ ⊢ t[1] ∈ TNat →
      Γ ⊢ t[2] ∈ TNat →
      Γ ⊢ (tmult t[1] t[2]) ∈ TNat
  | T_If[0] : ∀Γ t[1] t[2] t[3] T[1],
      Γ ⊢ t[1] ∈ TNat →
      Γ ⊢ t[2] ∈ T[1] →
      Γ ⊢ t[3] ∈ T[1] →
      Γ ⊢ (tif0 t[1] t[2] t[3]) ∈ T[1]
  (* pairs *)
  (* FILL IN HERE *)
  (* unit *)
  | T_Unit : ∀Γ,
      Γ ⊢ tunit ∈ TUnit
  (* let *)
  (* FILL IN HERE *)
  (* sums *)
  | T_Inl : ∀Γ t[1] T[1] T[2],
      Γ ⊢ t[1] ∈ T[1] →
      Γ ⊢ (tinl T[2] t[1]) ∈ (TSum T[1] T[2])
  | T_Inr : ∀Γ t[2] T[1] T[2],
      Γ ⊢ t[2] ∈ T[2] →
      Γ ⊢ (tinr T[1] t[2]) ∈ (TSum T[1] T[2])
  | T_Case : ∀Γ t[0] x[1] T[1] t[1] x[2] T[2] t[2] T,
      Γ ⊢ t[0] ∈ (TSum T[1] T[2]) →
      (update Γ x[1] T[1]) ⊢ t[1] ∈ T →
      (update Γ x[2] T[2]) ⊢ t[2] ∈ T →
      Γ ⊢ (tcase t[0] x[1] t[1] x[2] t[2]) ∈ T
  (* lists *)
  | T_Nil : ∀Γ T,
      Γ ⊢ (tnil T) ∈ (TList T)
  | T_Cons : ∀Γ t[1] t[2] T[1],
      Γ ⊢ t[1] ∈ T[1] →
      Γ ⊢ t[2] ∈ (TList T[1]) →
      Γ ⊢ (tcons t[1] t[2]) ∈ (TList T[1])
  | T_Lcase : ∀Γ t[1] T[1] t[2] x[1] x[2] t[3] T[2],
      Γ ⊢ t[1] ∈ (TList T[1]) →
      Γ ⊢ t[2] ∈ T[2] →
      (update (update Γ x[2] (TList T[1])) x[1] T[1]) ⊢ t[3] ∈ T[2] →
      Γ ⊢ (tlcase t[1] t[2] x[1] x[2] t[3]) ∈ T[2]
  (* fix *)
  (* FILL IN HERE *)

where "Gamma '⊢' t '∈' T" := (has_type Γ t T).

Hint Constructors has_type.

```

## 示例

    本节展示了来自

    上面（以及更多）。一开始的重点是

    特定功能；你可以使用这些来确保你的定义

    给定功能的合理性后，再继续扩展

    之后的证明与与此功能相关的情况。

    后面的例子需要所有功能一起，所以你会

    当你拥有所有定义时，需要回头看这些内容

    填写。

```
Module Examples.

```

### 准备工作

    首先，让我们定义一些变量名：

```
Notation x := (Id "x").
Notation y := (Id "y").
Notation a := (Id "a").
Notation f := (Id "f").
Notation g := (Id "g").
Notation l := (Id "l").
Notation k := (Id "k").
Notation i[1] := (Id "i1").
Notation i[2] := (Id "i2").
Notation processSum := (Id "processSum").
Notation n := (Id "n").
Notation eq := (Id "eq").
Notation m := (Id "m").
Notation evenodd := (Id "evenodd").
Notation even := (Id "even").
Notation odd := (Id "odd").
Notation eo := (Id "eo").

```

    接下来，一点 Coq 的技巧来自动搜索类型

    推导。你不需要详细了解这一点 —

    只是看一下，这样你就会知道如果

    如果你发现自己需要对

    auto。

    以下的提示声明表明，每当 auto

    到达形式为 (Γ ⊢ (tapp e[1] e[1]) ∈ T) 的目标时，它

    应该考虑使用 eapply T_App，留下一个存在变量

    对于中间类型 T[1]，以及 lcase 类似。那个变量

    将在搜索类型推导时填充

    e[1] 和 e[2]。我们还包括一个提示“更加努力”时

    解决相等性目标；这对于自动使用

    T_Var（其中包括相等性作为前提条件）非常有用。

```
Hint Extern 2 (has_type _ (tapp _ _) _) ⇒
  eapply T_App; auto.
Hint Extern 2 (has_type _ (tlcase _ _ _ _ _) _) ⇒
  eapply T_Lcase; auto.
Hint Extern 2 (_ = _) ⇒ compute; reflexivity.

```

### 数字

```
Module Numtest.

(* if[0] (pred (succ (pred (2 * 0))) then 5 else 6 *)
Definition test :=
  tif0
    (tpred
      (tsucc
        (tpred
          (tmult
            (tnat 2)
            (tnat 0)))))
    (tnat 5)
    (tnat 6).

```

    一旦你实现了足够的内容，就删除注释大括号

    你认为这应该有效。

```
(*  Example typechecks :   empty |- test ∈ TNat. Proof.   unfold test.   (* This typing derivation is quite deep, so we need       to increase the max search depth of auto from the       default 5 to 10. *)   auto 10\. Qed. Example numtest_reduces :   test ==>* tnat 5\. Proof.   unfold test. normalize. Qed. *)

End Numtest.

```

### 产品

```
Module Prodtest.

(* ((5,6),7).fst.snd *)
Definition test :=
  tsnd
    (tfst
      (tpair
        (tpair
          (tnat 5)
          (tnat 6))
        (tnat 7))).

(*  Example typechecks :   empty |- test ∈ TNat. Proof. unfold test. eauto 15. Qed. Example reduces :   test ==>* tnat 6\. Proof. unfold test. normalize. Qed. *)

End Prodtest.

```

### 让

```
Module LetTest.

(* let x = pred 6 in succ x *)
Definition test :=
  tlet
    x
    (tpred (tnat 6))
    (tsucc (tvar x)).

(*  Example typechecks :   empty |- test ∈ TNat. Proof. unfold test. eauto 15. Qed. Example reduces :   test ==>* tnat 6\. Proof. unfold test. normalize. Qed. *)

End LetTest.

```

### 总和

```
Module Sumtest1.

(* case (inl Nat 5) of      inl x => x    | inr y => y *)

Definition test :=
  tcase (tinl TNat (tnat 5))
    x (tvar x)
    y (tvar y).

(*  Example typechecks :   empty |- test ∈ TNat. Proof. unfold test. eauto 15. Qed. Example reduces :   test ==>* (tnat 5). Proof. unfold test. normalize. Qed. *)

End Sumtest1.

Module Sumtest2.

(* let processSum =      \x:Nat+Nat.         case x of           inl n => n           inr n => if[0] n then 1 else 0 in    (processSum (inl Nat 5), processSum (inr Nat 5))    *)

Definition test :=
  tlet
    processSum
    (tabs x (TSum TNat TNat)
      (tcase (tvar x)
         n (tvar n)
         n (tif0 (tvar n) (tnat 1) (tnat 0))))
    (tpair
      (tapp (tvar processSum) (tinl TNat (tnat 5)))
      (tapp (tvar processSum) (tinr TNat (tnat 5)))).

(*  Example typechecks :   empty |- test ∈ (TProd TNat TNat). Proof. unfold test. eauto 15. Qed. Example reduces :   test ==>* (tpair (tnat 5) (tnat 0)). Proof. unfold test. normalize. Qed. *)

End Sumtest2.

```

### 列表

```
Module ListTest.

(* let l = cons 5 (cons 6 (nil Nat)) in    lcase l of      nil => 0    | x::y => x*x *)

Definition test :=
  tlet l
    (tcons (tnat 5) (tcons (tnat 6) (tnil TNat)))
    (tlcase (tvar l)
       (tnat 0)
       x y (tmult (tvar x) (tvar x))).

(*  Example typechecks :   empty |- test ∈ TNat. Proof. unfold test. eauto 20. Qed. Example reduces :   test ==>* (tnat 25). Proof. unfold test. normalize. Qed. *)

End ListTest.

```

### 修复

```
Module FixTest1.

(* fact := fix              (λf:nat->nat.                 \a:nat.                    if a=0 then 1 else a * (f (pred a))) *)
Definition fact :=
  tfix
    (tabs f (TArrow TNat TNat)
      (tabs a TNat
        (tif0
           (tvar a)
           (tnat 1)
           (tmult
              (tvar a)
              (tapp (tvar f) (tpred (tvar a))))))).

```

    （警告：你可能能够对 fact 进行类型检查，但仍然可能存在一些

    规则错误！）

```
(*  Example fact_typechecks :   empty |- fact ∈ (TArrow TNat TNat). Proof. unfold fact. auto 10\. Qed. *)

(*  Example fact_example:   (tapp fact (tnat 4)) ==>* (tnat 24). Proof. unfold fact. normalize. Qed. *)

End FixTest1.

Module FixTest2.

(* map :=      \g:nat->nat.        fix          (λf:nat->nat.             \l:nat.                case l of                | ->  | x::l -> (g x)::(f l)) *)
Definition map :=
  tabs g (TArrow TNat TNat)
    (tfix
      (tabs f (TArrow (TList TNat) (TList TNat))
        (tabs l (TList TNat)
          (tlcase (tvar l)
            (tnil TNat)
            a l (tcons (tapp (tvar g) (tvar a))
                         (tapp (tvar f) (tvar l))))))).

(*  (* Make sure you've uncommented the last Hint Extern above... *) Example map_typechecks :   empty |- map ∈     (TArrow (TArrow TNat TNat)       (TArrow (TList TNat)         (TList TNat))). Proof. unfold map. auto 10. Qed. Example map_example :   tapp (tapp map (tabs a TNat (tsucc (tvar a))))          (tcons (tnat 1) (tcons (tnat 2) (tnil TNat)))   ==>* (tcons (tnat 2) (tcons (tnat 3) (tnil TNat))). Proof. unfold map. normalize. Qed. *)

End FixTest2.

Module FixTest3.

(* equal =       fix         (λeq:Nat->Nat->Bool.            \m:Nat. \n:Nat.              if[0] m then (if[0] n then 1 else 0)              else if[0] n then 0              else eq (pred m) (pred n))   *)

Definition equal :=
  tfix
    (tabs eq (TArrow TNat (TArrow TNat TNat))
      (tabs m TNat
        (tabs n TNat
          (tif0 (tvar m)
            (tif0 (tvar n) (tnat 1) (tnat 0))
            (tif0 (tvar n)
              (tnat 0)
              (tapp (tapp (tvar eq)
                              (tpred (tvar m)))
                      (tpred (tvar n)))))))).

(*  Example equal_typechecks :   empty |- equal ∈ (TArrow TNat (TArrow TNat TNat)). Proof. unfold equal. auto 10\. Qed. *)

(*  Example equal_example1:   (tapp (tapp equal (tnat 4)) (tnat 4)) ==>* (tnat 1). Proof. unfold equal. normalize. Qed. *)

(*  Example equal_example2:   (tapp (tapp equal (tnat 4)) (tnat 5)) ==>* (tnat 0). Proof. unfold equal. normalize. Qed. *)

End FixTest3.

Module FixTest4.

(* let evenodd =          fix            (λeo: (Nat->Nat * Nat->Nat).               let e = \n:Nat. if[0] n then 1 else eo.snd (pred n) in               let o = \n:Nat. if[0] n then 0 else eo.fst (pred n) in               (e,o)) in     let even = evenodd.fst in     let odd  = evenodd.snd in     (even 3, even 4) *)

Definition eotest :=
  tlet evenodd
    (tfix
      (tabs eo (TProd (TArrow TNat TNat) (TArrow TNat TNat))
        (tpair
          (tabs n TNat
            (tif0 (tvar n)
              (tnat 1)
              (tapp (tsnd (tvar eo)) (tpred (tvar n)))))
          (tabs n TNat
            (tif0 (tvar n)
              (tnat 0)
              (tapp (tfst (tvar eo)) (tpred (tvar n))))))))
  (tlet even (tfst (tvar evenodd))
  (tlet odd (tsnd (tvar evenodd))
  (tpair
    (tapp (tvar even) (tnat 3))
    (tapp (tvar even) (tnat 4))))).

(*  Example eotest_typechecks :   empty |- eotest ∈ (TProd TNat TNat). Proof. unfold eotest. eauto 30\. Qed. *)

(*  Example eotest_example1:   eotest ==>* (tpair (tnat 0) (tnat 1)). Proof. unfold eotest. normalize. Qed. *)

End FixTest4.

End Examples. 
```

## 类型的属性

    这个丰富系统的进展和保留的证明

    本质上与纯粹的相同（当然更长）。

    STLC。

```

### Progress

```

定理 progress： ∀t T，

empty ⊢ t ∈ T →

value t ∨ ∃t', t ⇒ t'.

    Proof with eauto.

(* 定理：假设 empty |- t : T。那么要么        1. t 是一个值，或者        2. t ==> t'，对于某个 t'。      证明：通过对给定的类型推导进行归纳。*)

intros t T Ht.

remember empty as Γ.

generalize dependent HeqGamma.

induction Ht; intros HeqGamma; subst.

- (* T_Var *)

(* 给定的类型推导中的最后一条规则不能是        T_Var，因为        empty ⊢ x : T （因为上下文是空的）永远不可能成立。*)

inversion H.

- (* T_Abs *)

(* 如果最后使用的规则是 T_Abs，那么        t = tabs x T[11] t[12]，这是一个值。*)

left...

- (* T_App *)

(* 如果最后应用的规则是 T_App，那么 t = t[1] t[2]，        我们从规则的形式知道          empty ⊢ t[1] : T[1] → T[2]          empty ⊢ t[2] : T[1]        根据归纳假设，t[1] 和 t[2] 中的每一个要么是        一个值，要么可以进行一步推导。*)

right.

destruct IHHt1; subst...

+ (* t[1] 是一个值 *)

destruct IHHt2; subst...

* (* t[2] 是一个值 *)

(* 如果 t[1]和 t[2]都是值，那么我们知道            t[1] = tabs x T[11] t[12]，因为抽象是            唯一可以有箭头类型的值。但是            (tabs x T[11] t[12]) t[2] ⇒ [x:=t[2]]t[12] 通过 ST_AppAbs。*)

inversion H; subst; try solve_by_invert.

∃(subst x t[2] t[12])...

* (* t[2] 步骤 *)

(* 如果 t[1]是一个值，并且 t[2] ⇒ t[2]'，            那么 t[1] t[2] ⇒ t[1] t[2]' 通过 ST_App2。*)

inversion H[0] as [t[2]' Hstp]. ∃(tapp t[1] t[2]')...

+ (* t[1] 步骤 *)

(* 最后，如果 t[1] ⇒ t[1]'，那么 t[1] t[2] ⇒ t[1]' t[2]           通过 ST_App1。*)

inversion H as [t[1]' Hstp]. ∃(tapp t[1]' t[2])...

- (* T_Nat *)

left...

- (* T_Succ *)

right.

destruct IHHt...

+ (* t[1] 是一个值 *)

inversion H; subst; try solve_by_invert.

∃(tnat ([S](http://coq.inria.fr/library/Coq.Init.Datatypes.html#S) n[1]))...

+ (* t[1] 步骤 *)

inversion H as [t[1]' Hstp].

∃(tsucc t[1]')...

- (* T_Pred *)

right.

destruct IHHt...

+ (* t[1] 是一个值 *)

inversion H; subst; try solve_by_invert.

∃(tnat ([pred](http://coq.inria.fr/library/Coq.Init.Peano.html#pred) n[1]))...

+ (* t[1] 步骤 *)

inversion H as [t[1]' Hstp].

∃(tpred t[1]')...

- (* T_Mult *)

right.

destruct IHHt1...

+ (* t[1] 是一个值 *)

destruct IHHt2...

* (* t[2] 是一个值 *)

inversion H; subst; try solve_by_invert.

inversion H[0]; subst; try solve_by_invert.

∃(tnat ([mult](http://coq.inria.fr/library/Coq.Init.Peano.html#mult) n[1] n[0]))...

* (* t[2] 步骤 *)

inversion H[0] as [t[2]' Hstp].

∃(tmult t[1] t[2]')...

+ (* t[1] 步骤 *)

inversion H as [t[1]' Hstp].

∃(tmult t[1]' t[2])...

- (* T_If[0] *)

right.

destruct IHHt1...

+ (* t[1] is a value *)

inversion H; subst; try solve_by_invert.

destruct n[1] as [|n[1]'].

* (* n[1]=0 *)

∃t[2]...

* (* n[1]<>0 *)

∃t[3]...

+ (* t[1] steps *)

inversion H as [t[1]' H[0]].

∃(tif0 t[1]' t[2] t[3])...

(* FILL IN HERE *)

- (* T_Unit *)

left...

(* let *)

(* FILL IN HERE *)

- (* T_Inl *)

destruct IHHt...

+ (* t[1] steps *)

right. inversion H as [t[1]' Hstp]...

(* exists (tinl _ t[1]')... *)

- (* T_Inr *)

destruct IHHt...

+ (* t[1] steps *)

right. inversion H as [t[1]' Hstp]...

(* exists (tinr _ t[1]')... *)

- (* T_Case *)

right.

destruct IHHt1...

+ (* t[0] is a value *)

inversion H; subst; try solve_by_invert.

* (* t[0] is inl *)

∃([x[1]:=v]t[1])...

* (* t[0] is inr *)

∃([x[2]:=v]t[2])...

+ (* t[0] steps *)

inversion H as [t[0]' Hstp].

∃(tcase t[0]' x[1] t[1] x[2] t[2])...

- (* T_Nil *)

left...

- (* T_Cons *)

destruct IHHt1...

+ (* head is a value *)

destruct IHHt2...

* (* tail steps *)

right. inversion H[0] as [t[2]' Hstp].

∃(tcons t[1] t[2]')...

+ (* head steps *)

right. inversion H as [t[1]' Hstp].

∃(tcons t[1]' t[2])...

- (* T_Lcase *)

right.

destruct IHHt1...

+ (* t[1] is a value *)

inversion H; subst; try solve_by_invert.

* (* t[1]=tnil *)

∃t[2]...

* (* t[1]=tcons v[1] vl *)

∃([x[2]:=vl]([x[1]:=v[1]]t[3]))...

+ (* t[1] steps *)

inversion H as [t[1]' Hstp].

∃(tlcase t[1]' t[2] x[1] x[2] t[3])...

(* fix *)

(* FILL IN HERE *) Qed.

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

(* nats *)

| afi_succ : ∀x t,

appears_free_in x t →

appears_free_in x (tsucc t)

| afi_pred : ∀x t,

appears_free_in x t →

appears_free_in x (tpred t)

| afi_mult1 : ∀x t[1] t[2],

appears_free_in x t[1] →

appears_free_in x (tmult t[1] t[2])

| afi_mult2 : ∀x t[1] t[2],

appears_free_in x t[2] →

appears_free_in x (tmult t[1] t[2])

| afi_if[01] : ∀x t[1] t[2] t[3],

appears_free_in x t[1] →

appears_free_in x (tif0 t[1] t[2] t[3])

| afi_if[02] : ∀x t[1] t[2] t[3],

appears_free_in x t[2] →

appears_free_in x (tif0 t[1] t[2] t[3])

| afi_if[03] : ∀x t[1] t[2] t[3],

appears_free_in x t[3] →

appears_free_in x (tif0 t[1] t[2] t[3])

(* pairs *)

(* FILL IN HERE *)

(* let *)

(* FILL IN HERE *)

(* sums *)

| afi_inl : ∀x t T,

appears_free_in x t →

appears_free_in x (tinl T t)

| afi_inr : ∀x t T,

appears_free_in x t →

appears_free_in x (tinr T t)

| afi_case0 : ∀x t[0] x[1] t[1] x[2] t[2],

appears_free_in x t[0] →

appears_free_in x (tcase t[0] x[1] t[1] x[2] t[2])

| afi_case1 : ∀x t[0] x[1] t[1] x[2] t[2],

x[1] ≠ x →

appears_free_in x t[1] →

appears_free_in x (tcase t[0] x[1] t[1] x[2] t[2])

| afi_case2 : ∀x t[0] x[1] t[1] x[2] t[2],

x[2] ≠ x →

appears_free_in x t[2] →

appears_free_in x (tcase t[0] x[1] t[1] x[2] t[2])

(* lists *)

| afi_cons1 : ∀x t[1] t[2],

appears_free_in x t[1] →

appears_free_in x (tcons t[1] t[2])

| afi_cons2 : ∀x t[1] t[2],

appears_free_in x t[2] →

appears_free_in x (tcons t[1] t[2])

| afi_lcase1 : ∀x t[1] t[2] y[1] y[2] t[3],

appears_free_in x t[1] →

appears_free_in x (tlcase t[1] t[2] y[1] y[2] t[3])

| afi_lcase2 : ∀x t[1] t[2] y[1] y[2] t[3],

appears_free_in x t[2] →

appears_free_in x (tlcase t[1] t[2] y[1] y[2] t[3])

| afi_lcase3 : ∀x t[1] t[2] y[1] y[2] t[3],

y[1] ≠ x →

y[2] ≠ x →

appears_free_in x t[3] →

appears_free_in x (tlcase t[1] t[2] y[1] y[2] t[3])

(* fix *)

(* 在此填写内容*)

.

Hint Constructors appears_free_in.

Lemma context_invariance : ∀Γ Γ' t S,

Γ ⊢ t ∈ S  →

(∀x, appears_free_in x t → Γ x = Γ' x)  →

Γ' ⊢ t ∈ S.

    Proof with eauto.

intros. generalize dependent Γ'.

induction H;

intros Γ' Heqv...

- (* T_Var *)

apply T_Var... rewrite ← Heqv...

- (* T_Abs *)

apply T_Abs... apply IHhas_type. intros y Hafi.

unfold update, t_update.

destruct (beq_idP x y)...

- (* T_Mult *)

apply T_Mult...

- (* T_If[0] *)

apply [T_If[0]](MoreStlc.html#STLCExtended.T_If<sub>0</sub>)...

(* pair *)

(* 在此填写内容*)

(* let *)

(* 在此填写内容*)

- (* T_Case *)

eapply T_Case...

+ apply IHhas_type2. intros y Hafi.

unfold update, t_update.

destruct (beq_idP x[1] y)...

+ apply IHhas_type3. intros y Hafi.

unfold update, t_update.

destruct (beq_idP x[2] y)...

- (* T_Cons *)

apply T_Cons...

- (* T_Lcase *)

eapply T_Lcase... apply IHhas_type3. intros y Hafi.

unfold update, t_update.

destruct (beq_idP x[1] y)...

destruct (beq_idP x[2] y)...

    Qed.

Lemma free_in_context : ∀x t T Γ,

appears_free_in x t →

Γ ⊢ t ∈ T →

∃T', Γ x = Some T'.

    Proof with eauto.

intros x t T Γ Hafi Htyp.

induction Htyp; inversion Hafi; subst...

- (* T_Abs *)

destruct IHHtyp as [T' Hctx]... ∃T'.

unfold update, t_update in Hctx.

rewrite false_beq_id in Hctx...

(* let *)

(* 在此填写内容*)

(* T_Case *)

- (* left *)

destruct IHHtyp2 as [T' Hctx]... ∃T'.

unfold update, t_update in Hctx.

rewrite false_beq_id in Hctx...

- (* right *)

destruct IHHtyp3 as [T' Hctx]... ∃T'.

在 Hctx 中展开 update, t_update。

在 Hctx 中重写 false_beq_id...

- (* T_Lcase *)

清除 Htyp1 IHHtyp1 Htyp2 IHHtyp2。

将 IHHtyp3 破坏为 [T' Hctx]... ∃T'。

在 Hctx 中展开 update, t_update。

在 Hctx 中重写 false_beq_id...

在 Hctx 中重写 false_beq_id...

    完成。

```

### Substitution

```

替换保持类型不变引理：∀Γ x U v t S，

(update Γ x U) ⊢ t ∈ S  →

empty ⊢ v ∈ U   →

Γ ⊢ ([x:=v]t) ∈ S。

    证明使用 eauto。

(* 定理：如果 Gamma,x:U |- t : S 并且 empty |- v : U，则      Gamma |- x:=vt : S。*)

对 Γ x U v t S Htypt Htypv 进行介绍。

推广到 Γ。推广到 S。

(* 证明：通过对项 t 进行归纳。大多数情况都可以直接      从 IH 推导出来，除了 tvar      和 tabs。这些不是自动的，因为我们必须      推理变量之间的交互。*)

对 t 进行归纳;

对 S Γ Htypt 进行介绍；简化；反演 Htypt；替换...

- (* tvar *)

简化。将 i 重命名为 y。

(* 如果 t = y，我们知道          empty ⊢ v : U 和          Γ,x:U ⊢ y : S        并且，通过反演，update Γ x U y = Some S。  我们想要展示        Γ ⊢ [x:=v]y : S。        有两种情况需要考虑：要么 x=y，要么 x≠y。*)

在 H[1] 中展开 update, t_update。

破坏 (beq_idP x y).

+ (* x=y *)

(* 如果 x = y，那么我们知道 U = S，并且          [x:=v]y = v。  所以我们真正需要展示的是          如果 empty ⊢ v : U，则 Γ ⊢ v : U。          我们已经证明了一个更一般的定理，称为上下文不变性。*)

替换。

反演 H[1]；替换。清除 H[1]。

应用 上下文不变性...

对 x Hcontra 进行介绍。

将 (free_in_context _ _ S empty Hcontra) 破坏

如 [T' HT'] 所示...

反演 HT'。

+ (* x<>y *)

(* 如果 x ≠ y，那么 Γ y = Some S，替换没有影响。我们可以通过 T_Var 展示        Γ ⊢ y : S。*)

应用 T_Var...

- (* tabs *)

将 i 重命名为 y。将 t 重命名为 T[11]。

(* 如果 t = tabs y T[11] t[0]，那么我们知道          Γ,x:U ⊢ tabs y T[11] t[0] : T[11]→T[12]          Γ,x:U,y:T[11] ⊢ t[0] : T[12]          empty ⊢ v : U        根据我们的 IH，我们知道对于所有的 S 和 Gamma，          Γ,x:U ⊢ t[0] : S → Γ ⊢ [x:=v]t[0] : S。        我们可以计算出          x:=vt = tabs y T[11] (if beq_id x y then t[0] else x:=vt[0])        我们必须展示 Γ ⊢ [x:=v]t : T[11]→T[12]。  我们知道        我们将使用 T_Abs 来完成，所以我们还需要展示：          Γ,y:T[11] ⊢ if beq_id x y then t[0] else [x:=v]t[0] : T[12]        我们考虑两种情况：x = y 和 x ≠ y。     *)

应用 T_Abs...

将 (beq_idP x y) 分解为 [Hxy|Hxy]。

+ (* x=y *)

(* If x = y, then the substitution has no effect.  Context        invariance shows that Γ,y:U,y:T[11] and Γ,y:T[11] are        equivalent.  Since the former context shows that         t[0] : T[12], so does the latter. *)

eapply context_invariance...

subst.

intros x Hafi. unfold update, t_update.

destruct (beq_id y x)...

+ (* x<>y *)

(* If x ≠ y, then the IH and context invariance allow           us to show that            Γ,x:U,y:T[11] ⊢ t[0] : T[12]       =>            Γ,y:T[11],x:U ⊢ t[0] : T[12]       =>            Γ,y:T[11] ⊢ [x:=v]t[0] : T[12] *)

apply IHt. eapply context_invariance...

intros z Hafi. unfold update, t_update.

destruct (beq_idP y z) as [Hyz|Hyz]...

subst.

rewrite false_beq_id...

(* let *)

(* FILL IN HERE *)

- (* tcase *)

rename i into x[1]. rename i[0] into x[2].

eapply T_Case...

+ (* left arm *)

destruct (beq_idP x x[1]) as [Hxx1|Hxx1].

* (* x = x[1] *)

eapply context_invariance...

subst.

intros z Hafi. unfold update, t_update.

destruct (beq_id x[1] z)...

* (* x <> x[1] *)

apply IHt2. eapply context_invariance...

intros z Hafi. unfold update, t_update.

destruct (beq_idP x[1] z) as [Hx1z|Hx1z]...

subst. rewrite false_beq_id...

+ (* right arm *)

destruct (beq_idP x x[2]) as [Hxx2|Hxx2].

* (* x = x[2] *)

eapply context_invariance...

subst.

intros z Hafi. unfold update, t_update.

destruct (beq_id x[2] z)...

* (* x <> x[2] *)

apply IHt3. eapply context_invariance...

intros z Hafi. unfold update, t_update.

destruct (beq_idP x[2] z)...

subst. rewrite false_beq_id...

- (* tlcase *)

rename i into y[1]. rename i[0] into y[2].

eapply T_Lcase...

destruct (beq_idP x y[1]).

+ (* x=y[1] *)

simpl.

eapply context_invariance...

subst.

intros z Hafi. unfold update, t_update.

destruct (beq_idP y[1] z)...

+ (* x<>y[1] *)

destruct (beq_idP x y[2]).

* (* x=y[2] *)

eapply context_invariance...

subst.

intros z Hafi. unfold update, t_update.

分解 (beq_idP y[2] z)...

* (* x<>y[2] *)

应用 IHt3。使用 context_invariance...

对 z 和 Hafi 进行介绍。展开 update，t_update。

分解 (beq_idP y[1] z)...

替换。重写 false_beq_id...

分解 (beq_idP y[2] z)...

替换。重写 false_beq_id...

    完成。

```

### Preservation

```

定理保持性：∀t t' T，

empty ⊢ t ∈ T  →

t ⇒ t'  →

empty ⊢ t' ∈ T。

    证明使用 eauto。

对 t t' T HT 进行介绍。

(* 定理：如果 empty ⊢ t : T 并且 t ⇒ t'，那么 empty ⊢ t' : T。*)

记住 empty 作为 Γ。推广依赖于 HeqGamma。

推广依赖于 t'。

(* 证明：通过对给定的类型推导进行归纳。许多情况是矛盾的（T_Var，T_Abs）。我们只展示有趣的情况。*)

对 HT 进行归纳；

对 t' 进行介绍 HeqGamma HE；替换；反演 HE；替换...

- (* T_App *)

(* 如果最后使用的规则是 T_App，则 t = t[1] t[2]，并且有三个规则可以用来展示 t ⇒ t'：ST_App1，ST_App2 和 ST_AppAbs。在前两种情况下，结果直接由 IH 得出。*)

反演 HE；替换...

+ (* ST_AppAbs *)

(* 对于第三种情况，假设            t[1] = tabs x T[11] t[12]          并且            t[2] = v[2]。          我们必须展示 empty ⊢ [x:=v[2]]t[12] : T[2]。          我们知道根据假设              empty ⊢ tabs x T[11] t[12] : T[1]→T[2]          并且根据反演              x:T[1] ⊢ t[12] : T[2]          我们已经证明了替换保持          类型，并且              empty ⊢ v[2] : T[1]          根据假设，所以我们完成了。*)

使用 substitution_preserves_typing 与 T[1]...

对 HT[1] 进行反演...

(* fst 和 snd *)

(* 在这里填写 *)

(* let *)

(* 在这里填写 *)

(* T_Case *)

- (* ST_CaseInl *)

对 HT[1] 进行反演；替换。

使用 substitution_preserves_typing...

- (* ST_CaseInr *)

对 HT[1] 进行反演；替换。

使用 substitution_preserves_typing...

- (* T_Lcase *)

+ (* ST_LcaseCons *)

对 HT[1] 进行反演；替换。

使用 substitution_preserves_typing 与 (TList T[1])...

使用 substitution_preserves_typing 与 T[1]...

(* fix *)

(* 在这里填写 *) 完成。

结束 STLCExtended。

```

    ☐

```

(* $Date: 2016-12-17 23:53:20 -0500 (Sat, 17 Dec 2016) $ *)

```

```

```

```

```

```

```

```
