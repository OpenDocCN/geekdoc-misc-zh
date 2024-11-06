# SubSubtyping

```

```

导入 Maps 模块。

导入 Types 模块。

导入 Smallstep 模块。

```

# Concepts

 We now turn to the study of *subtyping*, a key feature
    needed to support the object-oriented programming style. 

## A Motivating Example

 Suppose we are writing a program involving two record types
    defined as follows:

```

    Person  = {name:String, age:Nat}

    Student = {name:String, age:Nat, gpa:Nat}

```

 In the simply typed lamdba-calculus with records, the term

```

    (λr:Person. (r.age)+1) {name="Pat",age=21,gpa=1}

```

   is not typable, since it applies a function that wants a one-field
   record to an argument that actually provides two fields, while the
   T_App rule demands that the domain type of the function being
   applied must match the type of the argument precisely.

   But this is silly: we're passing the function a *better* argument
   than it needs!  The only thing the body of the function can
   possibly do with its record argument r is project the field age
   from it: nothing else is allowed by the type, and the presence or
   absence of an extra gpa field makes no difference at all.  So,
   intuitively, it seems that this function should be applicable to
   any record value that has at least an age field.

   More generally, a record with more fields is "at least as good in
   any context" as one with just a subset of these fields, in the
   sense that any value belonging to the longer record type can be
   used *safely* in any context expecting the shorter record type.  If
   the context expects something with the shorter type but we actually
   give it something with the longer type, nothing bad will
   happen (formally, the program will not get stuck).

   The principle at work here is called *subtyping*.  We say that "S
   is a subtype of T", written S <: T, if a value of type S can
   safely be used in any context where a value of type T is
   expected.  The idea of subtyping applies not only to records, but
   to all of the type constructors in the language — functions,
   pairs, etc. 

## Subtyping and Object-Oriented Languages

 Subtyping plays a fundamental role in many programming
    languages — in particular, it is closely related to the notion of
    *subclassing* in object-oriented languages.

    An *object* in Java, C#, etc. can be thought of as a record,
    some of whose fields are functions ("methods") and some of whose
    fields are data values ("fields" or "instance variables").
    Invoking a method m of an object o on some arguments a[1]..an
    roughly consists of projecting out the m field of o and
    applying it to a[1]..an.

    The type of an object is called a *class* — or, in some
    languages, an *interface*.  It describes which methods and which
    data fields the object offers.  Classes and interfaces are related
    by the *subclass* and *subinterface* relations.  An object
    belonging to a subclass (or subinterface) is required to provide
    all the methods and fields of one belonging to a superclass (or
    superinterface), plus possibly some more.

    The fact that an object from a subclass can be used in place of
    one from a superclass provides a degree of flexibility that is is
    extremely handy for organizing complex libraries.  For example, a
    GUI toolkit like Java's Swing framework might define an abstract
    interface Component that collects together the common fields and
    methods of all objects having a graphical representation that can
    be displayed on the screen and interact with the user, such as the
    buttons, checkboxes, and scrollbars of a typical GUI.  A method
    that relies only on this common interface can now be applied to
    any of these objects.

    Of course, real object-oriented languages include many other
    features besides these.  For example, fields can be updated.
    Fields and methods can be declared private.  Classes can give
    *initializers* that are used when constructing objects.  Code in
    subclasses can cooperate with code in superclasses via
    *inheritance*.  Classes can have static methods and fields.  Etc.,
    etc.

    To keep things simple here, we won't deal with any of these
    issues — in fact, we won't even talk any more about objects or
    classes.  (There is a lot of discussion in [[Pierce 2002]](Bib.html#Pierce 2002), if
    you are interested.)  Instead, we'll study the core concepts
    behind the subclass / subinterface relation in the simplified
    setting of the STLC. 

## The Subsumption Rule

 Our goal for this chapter is to add subtyping to the simply typed
    lambda-calculus (with some of the basic extensions from MoreStlc).
    This involves two steps:

*   Defining a binary *subtype relation* between types.

*   Enriching the typing relation to take subtyping into account.

    The second step is actually very simple.  We add just a single rule
    to the typing relation: the so-called *rule of subsumption*:

| Γ ⊢ t : S     S <: t< td="">
    | 
     (T_Sub)  
   |
|  
* * *

 |
| Γ ⊢ t : T | 
 
 |

    This rule says, intuitively, that it is OK to "forget" some of
    what we know about a term. 

 For example, we may know that t is a record with two
    fields (e.g., S = {x:A→A, y:B→B}), but choose to forget about
    one of the fields (T = {y:B→B}) so that we can pass t to a
    function that requires just a single-field record. 

## The Subtype Relation

 The first step — the definition of the relation S <: T — is
    where all the action is.  Let's look at each of the clauses of its
    definition.  

### Structural Rules

 To start off, we impose two "structural rules" that are
    independent of any particular type constructor: a rule of
    *transitivity*, which says intuitively that, if S is 
    better (richer, safer) than U and U is better than T, 
    then S is better than T...

| S <: u    u <: t< td="">
    | 
     (S_Trans)  
   |
|  
* * *

 |
| S <: t< td="">
    | 
 
 |

    ... and a rule of *reflexivity*, since certainly any type T is
    as good as itself:

|    | 
     (S_Refl)  
   |
|  
* * *

 |
| T <: t< td="">
    | 
 
 |

### Products

 Now we consider the individual type constructors, one by one,
    beginning with product types.  We consider one pair to be a subtype 
    of another if each of its components is.

| S[1] <: t[1    S[2] <: t[2]] | 
     (S_Prod)  
   |
|  
* * *

 |
| S[1] * S[2] <: t[1 * T[2]] | 
 
 |

### Arrows

 The subtyping rule for arrows is a little less intuitive.  
    Suppose we have functions f and g with these types:

```

f : C → Student

g : (C→Person) → D

```

    That is, f is a function that yields a record of type Student,
    and g is a (higher-order) function that expects its argument to be 
    a function yielding a record of type Person.  Also suppose that
    Student is a subtype of Person.  Then the application g f is
    safe even though their types do not match up precisely, because
    the only thing g can do with f is to apply it to some
    argument (of type C); the result will actually be a Student,
    while g will be expecting a Person, but this is safe because
    the only thing g can then do is to project out the two fields
    that it knows about (name and age), and these will certainly
    be among the fields that are present.

    This example suggests that the subtyping rule for arrow types
    should say that two arrow types are in the subtype relation if
    their results are:

| S[2] <: t[2] | 
     (S_Arrow_Co)  
   |
|  
* * *

 |
| S[1] → S[2] <: s[1 → T[2]] | 
 
 |

    We can generalize this to allow the arguments of the two arrow
    types to be in the subtype relation as well:

| T[1] <: s[1    S[2] <: t[2]] | 
     (S_Arrow)  
   |
|  
* * *

 |
| S[1] → S[2] <: t[1 → T[2]] | 
 
 |

    But notice that the argument types are subtypes "the other way round":
    in order to conclude that S[1]→S[2] to be a subtype of T[1]→T[2], it
    must be the case that T[1] is a subtype of S[1].  The arrow
    constructor is said to be *contravariant* in its first argument
    and *covariant* in its second.

    Here is an example that illustrates this:

```

f : Person → C

g : (Student → C) → D

```

    The application g f is safe, because the only thing the body of
    g can do with f is to apply it to some argument of type
    Student.  Since f requires records having (at least) the
    fields of a Person, this will always work. So Person → C is a
    subtype of Student → C since Student is a subtype of
    Person.

    The intuition is that, if we have a function f of type S[1]→S[2],
    then we know that f accepts elements of type S[1]; clearly, f
    will also accept elements of any subtype T[1] of S[1]. The type of
    f also tells us that it returns elements of type S[2]; we can
    also view these results belonging to any supertype T[2] of
    S[2]. That is, any function f of type S[1]→S[2] can also be
    viewed as having type T[1]→T[2]. 

### Records

 What about subtyping for record types? 

 The basic intuition is that it is always safe to use a "bigger"
    record in place of a "smaller" one.  That is, given a record type,
    adding extra fields will always result in a subtype.  If some code
    is expecting a record with fields x and y, it is perfectly safe
    for it to receive a record with fields x, y, and z; the z
    field will simply be ignored.  For example,

```

{name:String, age:Nat, gpa:Nat} <: {name:String, age:Nat}

{name:String, age:Nat} <: {name:String} {name:String} <: {}

```

    This is known as "width subtyping" for records. 

 We can also create a subtype of a record type by replacing the type
    of one of its fields with a subtype.  If some code is expecting a
    record with a field x of type T, it will be happy with a record
    having a field x of type S as long as S is a subtype of
    T. For example,

```

{x:Student} <: {x:Person}

```

    This is known as "depth subtyping". 

 Finally, although the fields of a record type are written in a
    particular order, the order does not really matter. For example,

```

{name:String,age:Nat} <: {age:Nat,name:String}

```

    This is known as "permutation subtyping". 

 We *could* formalize these requirements in a single subtyping rule
    for records as follows:

| ∀jk in j[1]..jn, | 
 
 |
| ∃ip in i[1]..im, such that | 
 
 |
| jk=ip and Sp <: tk< td="">
    | 
     (S_Rcd)  
   |
|  
* * *

 |
| {i[1]:S[1]...im:Sm} <: {j[1:T[1]...jn:Tn}] | 
 
 |

    That is, the record on the left should have all the field labels of
    the one on the right (and possibly more), while the types of the
    common fields should be in the subtype relation. 

    However, this rule is rather heavy and hard to read, so it is often 
    decomposed into three simpler rules, which can be combined using 
    S_Trans to achieve all the same effects. 

 First, adding fields to the end of a record type gives a subtype:

| n > m | 
     (S_RcdWidth)  
   |
|  
* * *

 |
| {i[1]:T[1]...in:Tn} <: {i[1:T[1]...im:Tm}] | 
 
 |

    We can use S_RcdWidth to drop later fields of a multi-field
    record while keeping earlier fields, showing for example that
    {age:Nat,name:String} <: {name:String}. 

 Second, subtyping can be applied inside the components of a compound
    record type:

| S[1] <: t[1  ...  Sn <: tn< td="">]  | 
     (S_RcdDepth)  
   |
|  
* * *

 |
| {i[1]:S[1]...in:Sn} <: {i[1:T[1]...in:Tn}] | 
 
 |

    For example, we can use S_RcdDepth and S_RcdWidth together to
    show that {y:Student, x:Nat} <: {y:Person}. 

 Third, subtyping can reorder fields.  For example, we
    want {name:String, gpa:Nat, age:Nat} <: Person.  (We
    haven't quite achieved this yet: using just S_RcdDepth and
    S_RcdWidth we can only drop fields from the *end* of a record
    type.)  So we add:

| {i[1]:S[1]...in:Sn} is a permutation of {j[1]:T[1]...jn:Tn} | 
     (S_RcdPerm)  
   |
|  
* * *

 |
| {i[1]:S[1]...in:Sn} <: {j[1:T[1]...jn:Tn}] | 
 
 |

 It is worth noting that full-blown language designs may choose not
    to adopt all of these subtyping rules. For example, in Java:

*   A subclass may not change the argument or result types of a
          method of its superclass (i.e., no depth subtyping or no arrow
          subtyping, depending how you look at it).

*   Each class member (field or method) can be assigned a single
          index, adding new indices "on the right" as more members are
          added in subclasses (i.e., no permutation for classes).

*   A class may implement multiple interfaces — so-called "multiple
          inheritance" of interfaces (i.e., permutation is allowed for
          interfaces). 

#### Exercise: 2 stars, recommendedM (arrow_sub_wrong)

 Suppose we had incorrectly defined subtyping as covariant on both
    the right and the left of arrow types:

| S[1] <: t[1    S[2] <: t[2]] | 
     (S_Arrow_wrong)  
   |
|  
* * *

 |
| S[1] → S[2] <: t[1 → T[2]] | 
 
 |

    Give a concrete example of functions f and g with the following
    types...

```

f : Student → Nat

g : (Person → Nat) → Nat

```

    ... such that the application g f will get stuck during
    execution.  (Use informal syntax.  No need to prove formally that 
    the application gets stuck.)

☐ 

### Top

 Finally, it is convenient to give the subtype relation a maximum
    element — a type that lies above every other type and is
    inhabited by all (well-typed) values.  We do this by adding to the
    language one new type constant, called Top, together with a
    subtyping rule that places it above every other type in the
    subtype relation:

|    | 
     (S_Top)  
   |
|  
* * *

 |
| S <: top< td="">
    | 
 
 |

    The Top type is an analog of the Object type in Java and C#. 

### Summary

 In summary, we form the STLC with subtyping by starting with the
    pure STLC (over some set of base types) and then...

*   adding a base type Top,

*   adding the rule of subsumption

    | Γ ⊢ t : S     S <: t< td="">
    | 
     (T_Sub)  
       |
    |  
    * * *

     |
    | Γ ⊢ t : T | 
 
     |

          to the typing relation, and

*   defining a subtype relation as follows:

    | S <: u    u <: t< td="">
    | 
     (S_Trans)  
       |
    |  
    * * *

     |
    | S <: t< td="">
    | 
 
     |

    |    | 
     (S_Refl)  
       |
    |  
    * * *

     |
    | T <: t< td="">
    | 
 
     |

    |    | 
     (S_Top)  
       |
    |  
    * * *

     |
    | S <: top< td="">
    | 
 
     |

    | S[1] <: t[1    S[2] <: t[2]] | 
     (S_Prod)  
       |
    |  
    * * *

     |
    | S[1] * S[2] <: t[1 * T[2]] | 
 
     |

    | T[1] <: s[1    S[2] <: t[2]] | 
     (S_Arrow)  
       |
    |  
    * * *

     |
    | S[1] → S[2] <: t[1 → T[2]] | 
 
     |

    | n > m | 
     (S_RcdWidth)  
       |
    |  
    * * *

     |
    | {i[1]:T[1]...in:Tn} <: {i[1:T[1]...im:Tm}] | 
 
     |

    | S[1] <: t[1  ...  Sn <: tn< td="">]  | 
     (S_RcdDepth)  
       |
    |  
    * * *

     |
    | {i[1]:S[1]...in:Sn} <: {i[1:T[1]...in:Tn}] | 
 
     |

    | {i[1]:S[1]...in:Sn} is a permutation of {j[1]:T[1]...jn:Tn} | 
     (S_RcdPerm)  
       |
    |  
    * * *

     |
    | {i[1]:S[1]...in:Sn} <: {j[1:T[1]...jn:Tn}] | 
 
     |

## Exercises

#### Exercise: 1 star, optional (subtype_instances_tf_1)

 Suppose we have types S, T, U, and V with S <: T
    and U <: V.  Which of the following subtyping assertions
    are then true?  Write *true* or *false* after each one.
    (A, B, and C here are base types like Bool, Nat, etc.)

*   T→S <: T→S

*   Top→U <: S→Top

*   (C→C) → (A*B)  <:  (C→C) → (Top*B)

*   T→T→U <: S→S→V

*   (T→T)→U <: (S→S)→V

*   ((T→S)→T)→U <: ((S→T)→S)→V

*   S*V <: T*U

☐ 

#### Exercise: 2 starsM (subtype_order)

 The following types happen to form a linear order with respect to subtyping:

*   Top

*   Top → Student

*   Student → Person

*   Student → Top

*   Person → Student

Write these types in order from the most specific to the most general.

Where does the type Top→Top→Student fit into this order?

☐ 

#### Exercise: 1 starM (subtype_instances_tf_2)

 Which of the following statements are true?  Write *true* or
    *false* after each one.

```

∀S T,

S <: T  →

S→S   <:  T→T

∀S,

S <: A→A →

∃T,

S = T→T  ∧  T <: A

∀S T[1] T[2],

(S <: T[1] → T[2]) →

∃S[1] S[2],

S = S[1] → S[2]  ∧  T[1] <: S[1]  ∧  S[2] <: T[2]

∃S,

S <: S→S

∃S,

S→S <: S

∀S T[1] T[2],

S <: T[1]*T[2] →

∃S[1] S[2],

S = S[1]*S[2]  ∧  S[1] <: T[1]  ∧  S[2] <: T[2]

```

☐ 

#### Exercise: 1 starM (subtype_concepts_tf)

 Which of the following statements are true, and which are false?

*   There exists a type that is a supertype of every other type.

*   There exists a type that is a subtype of every other type.

*   There exists a pair type that is a supertype of every other
          pair type.

*   There exists a pair type that is a subtype of every other
          pair type.

*   There exists an arrow type that is a supertype of every other
          arrow type.

*   There exists an arrow type that is a subtype of every other
          arrow type.

*   There is an infinite descending chain of distinct types in the
          subtype relation—-that is, an infinite sequence of types
          S[0], S[1], etc., such that all the Si's are different and
          each S(i+1) is a subtype of Si.

*   There is an infinite *ascending* chain of distinct types in
          the subtype relation—-that is, an infinite sequence of types
          S[0], S[1], etc., such that all the Si's are different and
          each S(i+1) is a supertype of Si.

☐ 

#### Exercise: 2 starsM (proper_subtypes)

 Is the following statement true or false?  Briefly explain your
    answer.  (Here TBase n stands for a base type, where n is 
    a string standing for the name of the base type.  See the 
    Syntax section below.)

```

∀T,

~(T = TBool ∨ ∃n, T = TBase n) →

∃S,

S <: T  ∧  S ≠ T

```

☐ 

#### Exercise: 2 starsM (small_large_1)

*   What is the *smallest* type T ("smallest" in the subtype
         relation) that makes the following assertion true?  (Assume we
         have Unit among the base types and unit as a constant of this
         type.)

    ```

    empty ⊢ (λp:T*Top. p.fst) ((λz:A.z), unit) : A→A

    ```

*   What is the *largest* type T that makes the same assertion true?

☐ 

#### Exercise: 2 starsM (small_large_2)

*   What is the *smallest* type T that makes the following
         assertion true?

    ```

    empty ⊢ (λp:(A→A * B→B). p) ((λz:A.z), (λz:B.z)) : T

    ```

*   What is the *largest* type T that makes the same assertion true?

☐ 

#### Exercise: 2 stars, optional (small_large_3)

*   What is the *smallest* type T that makes the following
         assertion true?

    ```

    a:A ⊢ (λp:(A*T). (p.snd) (p.fst)) (a , \z:A.z) : A

    ```

*   What is the *largest* type T that makes the same assertion true?

☐ 

#### Exercise: 2 starsM (small_large_4)

*   What is the *smallest* type T that makes the following
         assertion true?

    ```

    ∃S,

    empty ⊢ (λp:(A*T). (p.snd) (p.fst)) : S

    ```

*   What is the *largest* type T that makes the same
         assertion true?

☐ 

#### Exercise: 2 starsM (smallest_1)

 What is the *smallest* type T that makes the following
    assertion true?

```

∃S, ∃t,

empty��⊢ (λx:T. x x) t : S

```

☐ 

#### Exercise: 2 starsM (smallest_2)

 What is the *smallest* type T that makes the following
    assertion true?

```

empty ⊢ (λx:Top. x) ((λz:A.z) , (λz:B.z)) : T

```

☐ 

#### Exercise: 3 stars, optional (count_supertypes)

 How many supertypes does the record type {x:A, y:C→C} have?  That is,
    how many different types T are there such that {x:A, y:C→C} <:
    T?  (We consider two types to be different if they are written
    differently, even if each is a subtype of the other.  For example,
    {x:A,y:B} and {y:B,x:A} are different.)

☐ 

#### Exercise: 2 starsM (pair_permutation)

 The subtyping rule for product types

| S[1] <: t[1    S[2] <: t[2]] | 
     (S_Prod)  
   |
|  
* * *

 |
| S[1]*S[2] <: t[1*T[2]] | 
 
 |

    intuitively corresponds to the "depth" subtyping rule for records. 
    Extending the analogy, we might consider adding a "permutation" rule

|    | 
      
   |
|  
* * *

 |
| T[1]*T[2] <: t[2*T[1]] | 
 
 |

    for products.  Is this a good idea? Briefly explain why or why not.

☐ 

# Formal Definitions

 Most of the definitions needed to formalize what we've discussed
    above — in particular, the syntax and operational semantics of
    the language — are identical to what we saw in the last chapter.
    We just need to extend the typing relation with the subsumption
    rule and add a new Inductive definition for the subtyping
    relation.  Let's first do the identical bits. 

## Core Definitions

### Syntax

 In the rest of the chapter, we formalize just base types,
    booleans, arrow types, Unit, and Top, omitting record types
    and leaving product types as an exercise.  For the sake of more
    interesting examples, we'll add an arbitrary set of base types
    like String, Float, etc.  (Since they are just for examples,
    we won't bother adding any operations over these base types, but
    we could easily do so.) 

```

Inductive ty : Type :=

| TTop   : ty

| TBool  : ty

| TBase  : id → ty

| TArrow : ty → ty → ty

| TUnit  : ty

.

Inductive tm : Type :=

| tvar : id → tm

| tapp : tm → tm → tm

| tabs : id → ty → tm → tm

| ttrue : tm

| tfalse : tm

| tif : tm → tm → tm → tm

| tunit : tm

.

```

### Substitution

 The definition of substitution remains exactly the same as for the
    pure STLC. 

```

Fixpoint subst (x:id) (s:tm)  (t:tm) : tm :=

match t with

| tvar y ⇒

if beq_id x y then s else t

| tabs y T t[1] ⇒

tabs y T (if beq_id x y then t[1] else (subst x s t[1]))

| tapp t[1] t[2] ⇒

tapp (subst x s t[1]) (subst x s t[2])

| ttrue ⇒

ttrue

| tfalse ⇒

tfalse

| tif t[1] t[2] t[3] ⇒

tif (subst x s t[1]) (subst x s t[2]) (subst x s t[3])

| tunit ⇒

tunit

end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

```

### Reduction

 Likewise the definitions of the value property and the step
    relation. 

```

Inductive value : tm → Prop :=

| v_abs : ∀x T t,

value (tabs x T t)

| v_true :

value ttrue

| v_false :

value tfalse

| v_unit :

value tunit

.

Hint Constructors value.

Reserved Notation "t1 '⇒' t2" (at level 40).

Inductive step : tm → tm → Prop :=

| ST_AppAbs : ∀x T t[12] v[2],

value v[2] →

(tapp (tabs x T t[12]) v[2]) ⇒ [x:=v[2]]t[12]

| ST_App1 : ∀t[1] t[1]' t[2],

t[1] ⇒ t[1]' →

(tapp t[1] t[2]) ⇒ (tapp t[1]' t[2])

| ST_App2 : ∀v[1] t[2] t[2]',

value v[1] →

t[2] ⇒ t[2]' →

(tapp v[1] t[2]) ⇒ (tapp v[1]  t[2]')

| ST_IfTrue : ∀t[1] t[2],

(tif ttrue t[1] t[2]) ⇒ t[1]

| ST_IfFalse : ∀t[1] t[2],

(tif tfalse t[1] t[2]) ⇒ t[2]

| ST_If : ∀t[1] t[1]' t[2] t[3],

t[1] ⇒ t[1]' →

(tif t[1] t[2] t[3]) ⇒ (tif t[1]' t[2] t[3])

where "t1 '⇒' t2" := (step t[1] t[2]).

Hint Constructors step.

```

## Subtyping

 Now we come to the interesting part.  We begin by defining
    the subtyping relation and developing some of its important
    technical properties. 

 The definition of subtyping is just what we sketched in the
    motivating discussion. 

```

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty → ty → Prop :=

| S_Refl : ∀T,

T <: T

| S_Trans : ∀S U T,

S <: U →

U <: T →

S <: T

| S_Top : ∀S,

S <: TTop

| S_Arrow : ∀S[1] S[2] T[1] T[2],

T[1] <: S[1] →

S[2] <: T[2] →

(TArrow S[1] S[2]) <: (TArrow T[1] T[2])

where "T '<:' U" := (subtype T U).

```

Note that we don't need any special rules for base types (TBool
    and TBase): they are automatically subtypes of themselves (by
    S_Refl) and Top (by S_Top), and that's all we want. 

```

Hint Constructors subtype.

Module Examples.

Notation x := (Id "x").

定义 y := (Id "y").

定义 z := (Id "z").

定义 A := (TBase (Id "A")).

定义 B := (TBase (Id "B")).

定义 C := (TBase (Id "C")).

定义 String := (TBase (Id "String")).

定义 Float := (TBase (Id "Float")).

定义 Integer := (TBase (Id "Integer")).

例子 subtyping_example_0 :

(TArrow C TBool) <: (TArrow C TTop).

(* C->Bool <: C->Top *)

Proof. auto. Qed.

```

#### Exercise: 2 stars, optional (subtyping_judgements)

 (Wait to do this exercise after you have added product types to the
    language — see exercise products — at least up to this point 
    in the file).

    Recall that, in chapter MoreStlc, the optional section "Encoding
    Records" describes how records can be encoded as pairs.
    Using this encoding, define pair types representing the following 
    record types:

```

Person   := { name : String }

Student  := { name : String ;

gpa  : Float }

Employee := { name : String ;

ssn  : Integer }

```

```

定义 Person : ty

(* 用你的定义替换这一行 *). Admitted.

定义 Student : ty

(* 用你的定义替换这一行 *). Admitted.

定义 Employee : ty

(* 用你的定义替换这一行 *). Admitted.

```

Now use the definition of the subtype relation to prove the following: 

```

例子 sub_student_person :

Student <: Person.

Proof.

(* 在这里填写 *) Admitted.

例子 sub_employee_person :

Employee <: Person.

Proof.

(* 在这里填写 *) Admitted.

```

☐ 

 The following facts are mostly easy to prove in Coq.  To get
    full benefit from the exercises, make sure you also
    understand how to prove them on paper! 

#### Exercise: 1 star, optional (subtyping_example_1)

```

例子 subtyping_example_1 :

(TArrow TTop Student) <: (TArrow (TArrow C C) Person).

(* Top->Student <: (C->C)->Person *)

Proof with eauto.

(* 在这里填写 *) Admitted.

```

☐ 

#### Exercise: 1 star, optional (subtyping_example_2)

```

例子 subtyping_example_2 :

(TArrow TTop Person) <: (TArrow Person TTop).

(* Top->Person <: Person->Top *)

Proof with eauto.

(* 在这里填写 *) Admitted.

```

☐ 

```

End Examples.

```

## Typing

 The only change to the typing relation is the addition of the rule
    of subsumption, T_Sub. 

```

定义上下文为部分映射 ty。

Reserved Notation "Gamma '⊢' t '∈' T" (at level 40).

Inductive has_type : context → tm → ty → Prop :=

(* 同上 *)

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

| T_True : ∀Γ,

Γ ⊢ ttrue ∈ TBool

| T_False : ∀Γ,

Γ ⊢ tfalse ∈ TBool

| T_If : ∀t[1] t[2] t[3] T Γ,

Γ ⊢ t[1] ∈ TBool →

Γ ⊢ t[2] ∈ T →

Γ ⊢ t[3] ∈ T →

Γ ⊢ (tif t[1] t[2] t[3]) ∈ T

| T_Unit : ∀Γ,

Γ ⊢ tunit ∈ TUnit

(* 子类型新规则 *)

| T_Sub : ∀Γ t S T,

Γ ⊢ t ∈ S →

S <: T →

Γ ⊢ t ∈ T

where "Gamma '⊢' t '∈' T" := (has_type Γ t T).

提��� 构造 has_type。

```

The following hints help auto and eauto construct typing
    derivations.  (See chapter UseAuto for more on hints.) 

```

提示 外部 2 (has_type _ (tapp _ _) _) ⇒

应用 T_App; auto.

提示 外部 2 (_ = _) ⇒ 计算; 反射性。

模块 Examples2。

导入 Examples。

```

Do the following exercises after you have added product types to
    the language.  For each informal typing judgement, write it as a
    formal statement in Coq and prove it. 

#### Exercise: 1 star, optional (typing_example_0)

```

(* 空 |- ((λz:A.z), (λz:B.z))

: (A->A * B->B) *)

(* 在这里填写 *)

```

☐ 

#### Exercise: 2 stars, optional (typing_example_1)

```

(* 空 |- (λx:(Top * B->B). x.snd) ((λz:A.z), (λz:B.z))

: B->B *)

(* 在这里填写 *)

```

☐ 

#### Exercise: 2 stars, optional (typing_example_2)

```

(* 空 |- (λz:(C->C)->(Top * B->B). (z (λx:C.x)).snd)

(λz:C->C. ((λz:A.z), (λz:B.z)))

: (A->A * B->B) *)

(* 在这里填写 *)

```

☐ 

```

End Examples2.

```

# Properties

 The fundamental properties of the system that we want to
    check are the same as always: progress and preservation.  Unlike
    the extension of the STLC with references (chapter References),
    we don't need to change the *statements* of these properties to
    take subtyping into account.  However, their proofs do become a
    little bit more involved. 

## Inversion Lemmas for Subtyping

 Before we look at the properties of the typing relation, we need
    to establish a couple of critical structural properties of the
    subtype relation:

*   Bool is the only subtype of Bool, and

*   every subtype of an arrow type is itself an arrow type. 

 These are called *inversion lemmas* because they play a
    similar role in proofs as the built-in inversion tactic: given a
    hypothesis that there exists a derivation of some subtyping
    statement S <: T and some constraints on the shape of S and/or
    T, each inversion lemma reasons about what this derivation must
    look like to tell us something further about the shapes of S and
    T and the existence of subtype relations between their parts. 

#### Exercise: 2 stars, optional (sub_inversion_Bool)

```

引理 sub_inversion_Bool : ∀U,

U <: TBool →

U = TBool.

Proof with auto.

intros U Hs.

记住 TBool 作为 V。

(* 在这里填写 *) Admitted.

```

#### Exercise: 3 stars, optional (sub_inversion_arrow)

```

Lemma sub_inversion_arrow : ∀U V[1] V[2],

U <: (TArrow V[1] V[2]) →

∃U[1], ∃U[2],

U = (TArrow U[1] U[2]) ∧ (V[1] <: U[1]) ∧ (U[2] <: V[2]).

Proof with eauto.

intros U V[1] V[2] Hs.

记住 (TArrow V[1] V[2]) 作为 V。

推广 V[1]。推广 V[2]。

(* 在这里填写 *) Admitted.

```

☐ 

## Canonical Forms

 The proof of the progress theorem — that a well-typed
    non-value can always take a step — doesn't need to change too
    much: we just need one small refinement.  When we're considering
    the case where the term in question is an application t[1] t[2]
    where both t[1] and t[2] are values, we need to know that t[1] has
    the *form* of a lambda-abstraction, so that we can apply the
    ST_AppAbs reduction rule.  In the ordinary STLC, this is
    obvious: we know that t[1] has a function type T[11]→T[12], and
    there is only one rule that can be used to give a function type to
    a value — rule T_Abs — and the form of the conclusion of this
    rule forces t[1] to be an abstraction.

    In the STLC with subtyping, this reasoning doesn't quite work
    because there's another rule that can be used to show that a value
    has a function type: subsumption.  Fortunately, this possibility
    doesn't change things much: if the last rule used to show Γ
    ⊢ t[1] : T[11]→T[12] is subsumption, then there is some
    *sub*-derivation whose subject is also t[1], and we can reason by
    induction until we finally bottom out at a use of T_Abs.

    This bit of reasoning is packaged up in the following lemma, which
    tells us the possible "canonical forms" (i.e., values) of function
    type. 

#### Exercise: 3 stars, optional (canonical_forms_of_arrow_types)

```

Lemma canonical_forms_of_arrow_types : ∀Γ s T[1] T[2],

Γ ⊢ s ∈ (TArrow T[1] T[2]) →

value s →

∃x, ∃S[1], ∃s[2],

s = tabs x S[1] s[2].

Proof with eauto.

(* FILL IN HERE *) Admitted.

```

☐ 

 Similarly, the canonical forms of type Bool are the constants
    true and false. 

```

Lemma canonical_forms_of_Bool : ∀Γ s,

Γ ⊢ s ∈ TBool →

value s →

(s = ttrue ∨ s = tfalse).

Proof with eauto.

intros Γ s Hty Hv.

remember [TBool](https://example.org/TBool) as T.

induction Hty; try solve_by_invert...

- (* T_Sub *)

subst. apply [sub_inversion_Bool](https://example.org/sub_inversion_Bool) in H. subst...

Qed.

```

## Progress

 The proof of progress now proceeds just like the one for the
    pure STLC, except that in several places we invoke canonical forms
    lemmas... 

 *Theorem* (Progress): For any term t and type T, if empty ⊢
    t : T then t is a value or t ⇒ t' for some term t'.

    *Proof*: Let t and T be given, with empty ⊢ t : T.  Proceed
    by induction on the typing derivation.

    The cases for T_Abs, T_Unit, T_True and T_False are
    immediate because abstractions, unit, true, and false are
    already values.  The T_Var case is vacuous because variables
    cannot be typed in the empty context.  The remaining cases are
    more interesting:

*   If the last step in the typing derivation uses rule T_App,
          then there are terms t[1] t[2] and types T[1] and T[2] such that
          t = t[1] t[2], T = T[2], empty ⊢ t[1] : T[1] → T[2], and empty ⊢
          t[2] : T[1].  Moreover, by the induction hypothesis, either t[1] is
          a value or it steps, and either t[2] is a value or it steps.
          There are three possibilities to consider:

    *   Suppose t[1] ⇒ t[1]' for some term t[1]'.  Then t[1] t[2] ⇒ t[1]' t[2]
                by ST_App1.

    *   Suppose t[1] is a value and t[2] ⇒ t[2]' for some term t[2]'.
                Then t[1] t[2] ⇒ t[1] t[2]' by rule ST_App2 because t[1] is a
                value.

    *   Finally, suppose t[1] and t[2] are both values.  By the 
                canonical forms lemma for arrow types, we know that t[1] has the
                form \x:S[1].s2 for some x, S[1], and s[2].  But then
                (λx:S[1].s2) t[2] ⇒ [x:=t[2]]s[2] by ST_AppAbs, since t[2] is a
                value.

*   If the final step of the derivation uses rule T_If, then there
          are terms t[1], t[2], and t[3] such that t = if t[1] then t[2] else
          t[3], with empty ⊢ t[1] : Bool and with empty ⊢ t[2] : T and
          empty ⊢ t[3] : T.  Moreover, by the induction hypothesis,
          either t[1] is a value or it steps.

    *   If t[1] is a value, then by the canonical forms lemma for
                 booleans, either t[1] = true or t[1] = false.  In either
                 case, t can step, using rule ST_IfTrue or ST_IfFalse.

    *   If t[1] can step, then so can t, by rule ST_If.

*   If the final step of the derivation is by T_Sub, then there is
          a type S such that S <: T and empty ⊢ t : S.  The desired
          result is exactly the induction hypothesis for the typing
          subderivation. 

```

Theorem progress : ∀t T,

empty ⊢ t ∈ T →

value t ∨ ∃t', t ⇒ t'.

Proof with eauto.

intros t T Ht.

remember [empty](https://example.org/empty) as Γ.

revert HeqGamma.

induction Ht;

intros HeqGamma; subst...

- (* T_Var *)

inversion H.

- (* T_App *)

right.

destruct IHHt1; subst...

+ (* t[1] is a value *)

destruct IHHt2; subst...

* (* t[2] is a value *)

destruct ([canonical_forms_of_arrow_types](https://example.org/canonical_forms_of_arrow_types) [empty](https://example.org/empty) t[1] T[1] T[2])

as [x [S[1] [t[12] Heqt1]]]...

subst. ∃([x:=t[2]]t[12])...

* (* t[2] steps *)

inversion H[0] as [t[2]' Hstp]. ∃([tapp](https://example.org/tapp) t[1] t[2]')...

+ (* t[1] steps *)

inversion H as [t[1]' Hstp]. ∃([tapp](https://example.org/tapp) t[1]' t[2])...

- (* T_If *)

right.

destruct IHHt1.

+ (* t[1] is a value *) eauto.

+ assert (t[1] = [ttrue](https://example.org/ttrue) ∨ t[1] = [tfalse](https://example.org/tfalse))

by (eapply [canonical_forms_of_Bool](https://example.org/canonical_forms_of_Bool); eauto).

inversion H[0]; subst...

+ inversion H. rename x into t[1]'. eauto.

Qed.

```

## Inversion Lemmas for Typing

 The proof of the preservation theorem also becomes a little more
    complex with the addition of subtyping.  The reason is that, as
    with the "inversion lemmas for subtyping" above, there are a
    number of facts about the typing relation that are immediate from
    the definition in the pure STLC (formally: that can be obtained
    directly from the inversion tactic) but that require real proofs
    in the presence of subtyping because there are multiple ways to
    derive the same has_type statement.

    The following inversion lemma tells us that, if we have a
    derivation of some typing statement Γ ⊢ \x:S[1].t2 : T whose
    subject is an abstraction, then there must be some subderivation
    giving a type to the body t[2]. 

 *Lemma*: If Γ ⊢ \x:S[1].t2 : T, then there is a type S[2]
    such that Γ, x:S[1] ⊢ t[2] : S[2] and S[1] → S[2] <: T.

    (Notice that the lemma does *not* say, "then T itself is an arrow
    type" — this is tempting, but false!)

    *Proof*: Let Γ, x, S[1], t[2] and T be given as
     described.  Proceed by induction on the derivation of Γ ⊢
     \x:S[1].t2 : T.  Cases T_Var, T_App, are vacuous as those
     rules cannot be used to give a type to a syntactic abstraction.

*   If the last step of the derivation is a use of T_Abs then
           there is a type T[12] such that T = S[1] → T[12] and Γ,
           x:S[1] ⊢ t[2] : T[12].  Picking T[12] for S[2] gives us what we
           need: S[1] → T[12] <: S[1] → T[12] follows from S_Refl.

*   If the last step of the derivation is a use of T_Sub then
           there is a type S such that S <: T and Γ ⊢ \x:S[1].t2 :
           S.  The IH for the typing subderivation tell us that there is
           some type S[2] with S[1] → S[2] <: S and Γ, x:S[1] ⊢ t[2] :
           S[2].  Picking type S[2] gives us what we need, since S[1] → S[2]
           <: T then follows by S_Trans. 

```

Lemma typing_inversion_abs : ∀Γ x S[1] t[2] T,

Γ ⊢ (tabs x S[1] t[2]) ∈ T →

(∃S[2], (TArrow S[1] S[2]) <: T

∧ (update Γ x S[1]) ⊢ t[2] ∈ S[2]).

Proof with eauto.

intros Γ x S[1] t[2] T H.

remember ([tabs](https://example.org/tabs) x S[1] t[2]) as t.

induction H;

inversion Heqt; subst; intros; try solve_by_invert.

- (* T_Abs *)

∃T[12]...

- (* T_Sub *)

destruct IHhas_type as [S[2] [Hsub Hty]]...

Qed.

```

Similarly... 

```

Lemma typing_inversion_var : ∀Γ x T,

Γ ⊢ (tvar x) ∈ T →

∃S,

Γ x = Some S ∧ S <: T.

Proof with eauto.

intros Γ x T Hty.

remember ([tvar](https://example.org/tvar) x) as t.

induction Hty; intros;

inversion Heqt; subst; try solve_by_invert.

- (* T_Var *)

∃T...

- (* T_Sub *)

destruct IHHty as [U [Hctx HsubU]]... Qed.

Lemma typing_inversion_app : ∀Γ t[1] t[2] T[2],

Γ ⊢ (tapp t[1] t[2]) ∈ T[2] →

∃T[1],

Γ ⊢ t[1] ∈ (TArrow T[1] T[2]) ∧

Γ ⊢ t[2] ∈ T[1].

Proof with eauto.

intros Γ t[1] t[2] T[2] Hty.

remember ([tapp](https://example.org/tapp) t[1] t[2]) as t.

induction Hty; intros;

inversion Heqt; subst; try solve_by_invert.

- (* T_App *)

∃T[1]...

- (* T_Sub *)

destruct IHHty as [U[1] [Hty1 Hty2]]...

Qed.

Lemma typing_inversion_true : ∀Γ T,

Γ ⊢ ttrue ∈ T →

TBool <: T.

Proof with eauto.

intros Γ T Htyp. remember [ttrue](https://example.org/ttrue) as tu.

induction Htyp;

inversion Heqtu; subst; intros...

Qed.

Lemma typing_inversion_false : ∀Γ T,

Γ ⊢ tfalse ∈ T →

TBool <: T.

Proof with eauto.

intros Γ T Htyp. remember [tfalse](https://example.org/tfalse) as tu.

induction Htyp;

inversion Heqtu; subst; intros...

Qed.

Lemma typing_inversion_if : ∀Γ t[1] t[2] t[3] T,

Γ ⊢ (tif t[1] t[2] t[3]) ∈ T →

Γ ⊢ t[1] ∈ TBool

∧ Γ ⊢ t[2] ∈ T

∧ Γ ⊢ t[3] ∈ T.

Proof with eauto.

intros Γ t[1] t[2] t[3] T Hty.

remember (tif t[1] t[2] t[3]) as t.

induction Hty; intros;

inversion Heqt; subst; try solve_by_invert.

- (* T_If *)

auto.

- (* T_Sub *)

destruct (IHHty H[0]) as [H[1] [H[2] H[3]]]...

Qed.

Lemma typing_inversion_unit : ∀Γ T,

Γ ⊢ tunit ∈ T →

TUnit <: T.

Proof with eauto.

intros Γ T Htyp. remember tunit as tu.

induction Htyp;

inversion Heqtu; subst; intros...

Qed.

```

The inversion lemmas for typing and for subtyping between arrow
    types can be packaged up as a useful "combination lemma" telling
    us exactly what we'll actually require below. 

```

Lemma abs_arrow : ∀x S[1] s[2] T[1] T[2],

empty ⊢ (tabs x S[1] s[2]) ∈ (TArrow T[1] T[2]) →

T[1] <: S[1]

∧ (update empty x S[1]) ⊢ s[2] ∈ T[2].

Proof with eauto.

intros x S[1] s[2] T[1] T[2] Hty.

apply typing_inversion_abs in Hty.

inversion Hty as [S[2] [Hsub Hty1]].

apply sub_inversion_arrow in Hsub.

inversion Hsub as [U[1] [U[2] [Heq [Hsub1 Hsub2]]]].

inversion Heq; subst... Qed.

```

## Context Invariance

 The context invariance lemma follows the same pattern as in the
    pure STLC. 

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

| afi_if[1] : ∀x t[1] t[2] t[3],

appears_free_in x t[1] →

appears_free_in x (tif t[1] t[2] t[3])

| afi_if[2] : ∀x t[1] t[2] t[3],

appears_free_in x t[2] →

appears_free_in x (tif t[1] t[2] t[3])

| afi_if[3] : ∀x t[1] t[2] t[3],

appears_free_in x t[3] →

appears_free_in x (tif t[1] t[2] t[3])

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

apply T_Abs... apply IHhas_type. intros x[0] Hafi.

unfold update, t_update. destruct (beq_idP x x[0])...

- (* T_If *)

apply T_If...

Qed.

Lemma free_in_context : ∀x t T Γ,

appears_free_in x t →

Γ ⊢ t ∈ T →

∃T', Γ x = Some T'.

Proof with eauto.

intros x t T Γ Hafi Htyp.

induction Htyp;

subst; inversion Hafi; subst...

- (* T_Abs *)

destruct (IHHtyp H[4]) as [T Hctx]. ∃T.

unfold update, t_update in Hctx.

rewrite ← beq_id_false_iff in H[2].

rewrite H[2] in Hctx... Qed.

```

## Substitution

 The *substitution lemma* is proved along the same lines as
    for the pure STLC.  The only significant change is that there are
    several places where, instead of the built-in inversion tactic,
    we need to use the inversion lemmas that we proved above to
    extract structural information from assumptions about the
    well-typedness of subterms. 

```

Lemma substitution_preserves_typing : ∀Γ x U v t S,

(update Γ x U) ⊢ t ∈ S  →

empty ⊢ v ∈ U   →

Γ ⊢ ([x:=v]t) ∈ S.

Proof with eauto.

intros Γ x U v t S Htypt Htypv.

generalize dependent S. generalize dependent Γ.

induction t; intros; simpl.

- (* tvar *)

rename i into y.

destruct (typing_inversion_var _ _ _ Htypt)

as [T [Hctx Hsub]].

在 Hctx 中展开 update, t_update。

分解 (beq_idP x y) 得到 [Hxy|Hxy]; 自动;

替换。

对 Hctx 进行反演; 替换; 清除 Hctx。

应用 context_invariance 得�� empty...

引入 x Hcontra。

分解 (free_in_context _ _ S empty Hcontra)

得到 [T' HT']...

对 HT' 进行反演。

- (* tapp *)

分解 (typing_inversion_app _ _ _ _ Htypt)

得到 [T[1] [Htypt1 Htypt2]]。

应用 T_App...

- (* tabs *)

重命名 i 为 y。重命名 t 为 T[1]。

分解 (typing_inversion_abs _ _ _ _ _ Htypt)

得到 [T[2] [Hsub Htypt2]]。

应用 T_Sub 得到 (TArrow T[1] T[2])... 应用 T_Abs...

分解 (beq_idP x y) 得到 [Hxy|Hxy]。

+ (* x=y *)

应用 context_invariance...

替换。

引入 x Hafi. 展开 update, t_update.

分解 (beq_id y x)...

+ (* x<>y *)

应用 IHt。通过 context_invariance...

引入 z Hafi. 展开 update, t_update.

分解 (beq_idP y z)...

替换。

通过 beq_id_false_iff 重写 Hxy。重写 Hxy...

- (* ttrue *)

断言 TBool <: S

通过应用 (typing_inversion_true _ _  Htypt)...

- (* tfalse *)

断言 TBool <: S

通过应用 (typing_inversion_false _ _  Htypt) 得到...

- (* tif *)

断言 ((update Γ x U) ⊢ t[1] ∈ TBool

∧ (update Γ x U) ⊢ t[2] ∈ S

∧ (update Γ x U) ⊢ t[3] ∈ S)

通过应用 (typing_inversion_if _ _ _ _ _ Htypt) 得到。

对 H 进行反演得到 [H[1] [H[2] H[3]]]。

对 H[1] 应用 IHt1。对 H[2] 应用 IHt2。对 H[3] 应用 IHt3。

自动。

- (* tunit *)

断言 TUnit <: S

通过应用 (typing_inversion_unit _ _  Htypt)...

完成。

```

## Preservation

 The proof of preservation now proceeds pretty much as in earlier
    chapters, using the substitution lemma at the appropriate point
    and again using inversion lemmas from above to extract structural
    information from typing assumptions. 

 *Theorem* (Preservation): If t, t' are terms and T is a type
    such that empty ⊢ t : T and t ⇒ t', then empty ⊢ t' :
    T.

    *Proof*: Let t and T be given such that empty ⊢ t : T.  We
    proceed by induction on the structure of this typing derivation,
    leaving t' general.  The cases T_Abs, T_Unit, T_True, and
    T_False cases are vacuous because abstractions and constants
    don't step.  Case T_Var is vacuous as well, since the context is
    empty.

*   If the final step of the derivation is by T_App, then there
           are terms t[1] and t[2] and types T[1] and T[2] such that
           t = t[1] t[2], T = T[2], empty ⊢ t[1] : T[1] → T[2], and
           empty ⊢ t[2] : T[1].

           By the definition of the step relation, there are three ways
           t[1] t[2] can step.  Cases ST_App1 and ST_App2 follow
           immediately by the induction hypotheses for the typing
           subderivations and a use of T_App.

           Suppose instead t[1] t[2] steps by ST_AppAbs.  Then t[1] =
           \x:S.t12 for some type S and term t[12], and t' =
           [x:=t[2]]t[12].

           By lemma abs_arrow, we have T[1] <: S and x:S[1] ⊢ s[2] : T[2].
           It then follows by the substitution lemma
           (substitution_preserves_typing) that empty ⊢ [x:=t[2]]
           t[12] : T[2] as desired.

    *   If the final step of the derivation uses rule T_If, then
                there are terms t[1], t[2], and t[3] such that t = if t[1] then
                t[2] else t[3], with empty ⊢ t[1] : Bool and with empty ⊢ t[2] :
                T and empty ⊢ t[3] : T.  Moreover, by the induction
                hypothesis, if t[1] steps to t[1]' then empty ⊢ t[1]' : Bool.
                There are three cases to consider, depending on which rule was
                used to show t ⇒ t'.

        *   If t ⇒ t' by rule ST_If, then t' = if t[1]' then t[2]
                         else t[3] with t[1] ⇒ t[1]'.  By the induction hypothesis,
                         empty ⊢ t[1]' : Bool, and so empty ⊢ t' : T by T_If.

        *   If t ⇒ t' by rule ST_IfTrue or ST_IfFalse, then
                         either t' = t[2] or t' = t[3], and empty ⊢ t' : T
                         follows by assumption.

*   If the final step of the derivation is by T_Sub, then there
           is a type S such that S <: T and empty ⊢ t : S.  The
           result is immediate by the induction hypothesis for the typing
           subderivation and an application of T_Sub.  ☐ 

```

定理保持性 : ∀t t' T,

empty ⊢ t ∈ T  →

t ⇒ t'  →

empty ⊢ t' ∈ T。

证明使用 eauto。

引入 t t' T HT.

记住 empty 为 Γ。推广 HeqGamma。

推广 t'.

归纳 HT;

引入 t' HeqGamma HE; 替换; 反演 HE; 替换...

- (* T_App *)

反演 HE; 替换...

+ (* ST_AppAbs *)

分解 (abs_arrow _ _ _ _ _ HT[1]) 得到 [HA[1] HA[2]]。

应用 substitution_preserves_typing 得到 T...

完成。

```

## Records, via Products and Top

 This formalization of the STLC with subtyping omits record
    types for brevity.  If we want to deal with them more seriously,
    we have two choices.

    First, we can treat them as part of the core language, writing
    down proper syntax, typing, and subtyping rules for them.  Chapter
    RecordSub shows how this extension works.

    On the other hand, if we are treating them as a derived form that
    is desugared in the parser, then we shouldn't need any new rules:
    we should just check that the existing rules for subtyping product
    and Unit types give rise to reasonable rules for record
    subtyping via this encoding. To do this, we just need to make one
    small change to the encoding described earlier: instead of using
    Unit as the base case in the encoding of tuples and the "don't
    care" placeholder in the encoding of records, we use Top.  So:

```

    {a:Nat, b:Nat} ----> {Nat,Nat}       即，(Nat,(Nat,Top))

    {c:Nat, a:Nat} ----> {Nat,Top,Nat}   即，(Nat,(Top,(Nat,Top)))

```

    The encoding of record values doesn't change at all.  It is
    easy (and instructive) to check that the subtyping rules above are
    validated by the encoding. 

## Exercises

#### Exercise: 2 starsM (variations)

 Each part of this problem suggests a different way of changing the
    definition of the STLC with Unit and subtyping.  (These changes
    are not cumulative: each part starts from the original language.)
    In each part, list which properties (Progress, Preservation, both,
    or neither) become false.  If a property becomes false, give a
    counterexample.

*   Suppose we add the following typing rule:

    | Γ ⊢ t : S[1]->S[2] | 
 
     |
    | S[1] <: t[1     T[1] <: s[1      S[2] <: t[2]]] | 
     (T_Funny1)  
       |
    |  
    * * *

     |
    | Γ ⊢ t : T[1]->T[2] | 
 
     |

*   Suppose we add the following reduction rule:

    |    | 
     (ST_Funny21)  
       |
    |  
    * * *

     |
    | unit ⇒ (λx:Top. x) | 
 
     |

*   Suppose we add the following subtyping rule:

    |    | 
     (S_Funny3)  
       |
    |  
    * * *

     |
    | Unit <: top->Top | 
 
     |

*   Suppose we add the following subtyping rule:

    |    | 
     (S_Funny4)  
       |
    |  
    * * *

     |
    | Top->Top <: unit< td="">
    | 
 
     |

*   Suppose we add the following reduction rule:

    |    | 
     (ST_Funny5)  
       |
    |  
    * * *

     |
    | (unit t) ⇒ (t unit) | 
 
     |

*   Suppose we add the same reduction rule *and* a new typing rule:

    |    | 
     (ST_Funny5)  
       |
    |  
    * * *

     |
    | (unit t) ⇒ (t unit) | 
 
     |

    |    | 
     (T_Funny6)  
       |
    |  
    * * *

     |
    | empty ⊢ unit : Top->Top | 
 
     |

*   Suppose we *change* the arrow subtyping rule to:

    | S[1] <: t[1 S[2] <: t[2]] | 
     (S_Arrow')  
       |
    |  
    * * *

     |
    | S[1]->S[2] <: t[1->T[2]] | 
 
     |

☐ 

# Exercise: Adding Products

#### Exercise: 4 stars (products)

 Adding pairs, projections, and product types to the system we have
    defined is a relatively straightforward matter.  Carry out this
    extension:

*   Below, we've added constructors for pairs, first and second
          projections, and product types to the definitions of ty and
          tm.

*   Copy the definitions of the substitution function and value
          relation from above and extend them as in chapter
          MoreSTLC to include products.

*   Similarly, copy and extend the operational semantics with the
          same reduction rules as in chapter MoreSTLC.

*   (Copy and) extend the subtyping relation with this rule:

    | S[1] <: t[1 S[2] <: t[2]] | 
     (Sub_Prod)  
       |
    |  
    * * *

     |
    | S[1] * S[2] <: t[1 * T[2]] | 
 
     |

*   Extend the typing relation with the same rules for pairs and
          projections as in chapter MoreSTLC.

*   Extend the proofs of progress, preservation, and all their
          supporting lemmas to deal with the new constructs.  (You'll also
          need to add a couple of completely new lemmas.) 

```

模块 ProductExtension。

归纳 ty : Type :=

| TTop   : ty

| TBool  : ty

| TBase  : id → ty

| TArrow : ty → ty → ty

| TUnit  : ty

| TProd : ty → ty → ty.

归纳 tm : Type :=

| tvar : id → tm

| tapp : tm → tm → tm

| tabs : id → ty → tm → tm

| ttrue : tm

| tfalse : tm

| tif : tm → tm → tm → tm

| tunit : tm

| tpair : tm → tm → tm

| tfst : tm → tm

| tsnd : tm → tm.

(* 复制并扩展和/或填写所需的定义和引理

here. *)

定理 progress : ∀t T,

empty ⊢ t ∈ T →

value t ∨ ∃t', t ⇒ t'.

Proof.

(* 在这里填写 *) 已承认。

定理 preservation : ∀t t' T,

empty ⊢ t ∈ T  →

t ⇒ t'  →

empty ⊢ t' ∈ T.

Proof.

(* 在这里填写 *) 已承认。

End ProductExtension.

```

☐ 

```
