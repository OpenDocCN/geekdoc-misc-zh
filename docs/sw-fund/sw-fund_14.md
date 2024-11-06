# ImpParserLexing 和 Coq 中的解析

```

    The development of the Imp language in Imp.v completely ignores
    issues of concrete syntax — how an ascii string that a programmer
    might write gets translated into abstract syntax trees defined by
    the datatypes aexp, bexp, and com.  In this chapter, we
    illustrate how the rest of the story can be filled in by building
    a simple lexical analyzer and parser using Coq's functional
    programming facilities.

    It is not important to understand all the details here (and
    accordingly, the explanations are fairly terse and there are no
    exercises).  The main point is simply to demonstrate that it can
    be done.  You are invited to look through the code — most of it
    is not very complicated, though the parser relies on some
    "monadic" programming idioms that may require a little work to
    make out — but most readers will probably want to just skim down
    to the Examples section at the very end to get the punchline.

```

(* 删除 *)

```

# Internals

```

需要导入 Coq.Strings.String.

需要导入 Coq.Strings.Ascii.

需要导入 Coq.Arith.Arith.

需要导入 Coq.Arith.EqNat.

需要导入 Coq.Lists.List.

导入 ListNotations.

需要导入 Maps.

需要导入 Imp.

```

## Lexical Analysis

```

定义 isWhite (c : ascii) : bool :=

让 n := nat_of_ascii c

orb (orb (beq_nat n 32)   (* 空格 *)

(beq_nat n 9))   (* 制表符 *)

(orb (beq_nat n 10)   (* 换行符 *)

(beq_nat n 13)). (* 回车符 *)

记号 "x '<=?' y" := (leb x y)

(在第 70 级，不结合) : nat_scope.

定义 isLowerAlpha (c : ascii) : bool :=

让 n := nat_of_ascii c

andb (97 <=? n) (n <=? 122).

定义 isAlpha (c : ascii) : bool :=

让 n := nat_of_ascii c

orb (andb (65 <=? n) (n <=? 90))

(andb (97 <=? n) (n <=? 122)).

定义 isDigit (c : ascii) : bool :=

让 n := nat_of_ascii c

andb (48 <=? n) (n <=? 57).

归纳 chartype := white | alpha | digit | other.

定义 classifyChar (c : ascii) : chartype :=

如果是空格 c then

白色

否则如果是字母 c then

字母

否则如果是数字 c then

数字

否则

other.

修复 list_of_string (s : string) : list ascii :=

匹配 s 时

| EmptyString ⇒ []

| String c s ⇒ c :: (list_of_string s)

结束.

修复 string_of_list (xs : list ascii) : string :=

fold_right String EmptyString xs.

定义 token := string.

修复 tokenize_helper (cls : chartype) (acc xs : list ascii)

: list (list ascii) :=

让 tk := 匹配 acc 时 [] ⇒ [] | _::_ ⇒ [反转 acc] 结束 in

匹配 xs 时

| [] ⇒ tk

| (x::xs') ⇒

匹配 cls, classifyChar x, x 时

| _, _, "("      ⇒

tk ++ ["("]::(tokenize_helper other [] xs')

| _, _, ")"      ⇒

tk ++ [")"]::(tokenize_helper other [] xs')

| _, 白色, _    ⇒

tk ++ (tokenize_helper white [] xs')

| alpha,alpha,x  ⇒

tokenize_helper alpha (x::acc) xs'

| digit,digit,x  ⇒

tokenize_helper digit (x::acc) xs'

| other,other,x  ⇒

tokenize_helper other (x::acc) xs'

| _,tp,x         ⇒

tk ++ (tokenize_helper tp [x] xs')

结束

结束 %char.

定义 tokenize (s : string) : list string :=

map string_of_list (tokenize_helper white [] (list_of_string s)).

示例 tokenize_ex[1] :

tokenize "abc12==3  223*(3+(a+c))" %string

= ["abc"; "12"; "=="; "3"; "223";

"*"; "("; "3"; "+"; "(";

"a"; "+"; "c"; ")"; ")"]%string.

    证明. 反射性. 完成.

```

## Parsing

### Options With Errors

    An option type with error messages:

```

归纳 optionE (X:Type) : Type :=

| SomeE : X → optionE X

| NoneE : string → optionE X.

隐式参数 SomeE [[X]].

隐式参数 NoneE [[X]].

```

    Some syntactic sugar to make writing nested match-expressions on
    optionE more convenient.

```

记号 "'DO' ( x , y ) <== e1 ; e2"

:= (匹配 e[1] 时

| SomeE (x,y) ⇒ e[2]

| NoneE err ⇒ NoneE err

结束)

(右结合，级别为 60).

记号 "'DO' ( x , y ) <-- e1 ; e2 'OR' e3"

:= (匹配 e[1] 时

| SomeE (x,y) ⇒ e[2]

| NoneE err ⇒ e[3]

结束)

(右结合，级别为 60，e[2]在下一个级别).

```

### Generic Combinators for Building Parsers

```

打开 string_scope.

定义 parser (T : Type) :=

列表 token → optionE (T * 列表 token).

修复 many_helper {T} (p : parser T) acc steps xs :=

匹配 steps, p xs 时

| 0, _ ⇒

NoneE "递归调用太多"

| _, NoneE _ ⇒

SomeE ((反转 acc), xs)

| S steps', SomeE (t, xs') ⇒

many_helper p (t::acc) steps' xs'

end.

```

    A (step-indexed) parser that expects zero or more ps:

```

Fixpoint many {T} (p : parser T) (steps : nat) : parser (list T) :=

many_helper p [] steps.

```

    A parser that expects a given token, followed by p:

```

Definition firstExpect {T} (t : token) (p : parser T)

: parser T :=

fun xs ⇒ match xs with

| x::xs' ⇒

if string_dec x t

then p xs'

else NoneE ("expected '" ++ t ++ "'.")

| [] ⇒

NoneE ("expected '" ++ t ++ "'.")

end.

```

    A parser that expects a particular token:

```

Definition expect (t : token) : parser unit :=

firstExpect t (fun xs ⇒ SomeE(tt, xs)).

```

### A Recursive-Descent Parser for Imp

    Identifiers:

```

Definition parseIdentifier (xs : list token)

: optionE (id * list token) :=

match xs with

| [] ⇒ NoneE "Expected identifier"

| x::xs' ⇒

if forallb isLowerAlpha (list_of_string x) then

SomeE (Id x, xs')

else

NoneE ("Illegal identifier:'" ++ x ++ "'")

end.

```

    Numbers:

```

Definition parseNumber (xs : list token)

: optionE (nat * list token) :=

match xs with

| [] ⇒ NoneE "Expected number"

| x::xs' ⇒

if forallb isDigit (list_of_string x) then

SomeE (fold_left

(fun n d ⇒

10 * n + (nat_of_ascii d -

nat_of_ascii "0"%char))

(list_of_string x)

0,

xs')

else

NoneE "Expected number"

end.

```

    Parse arithmetic expressions

```

Fixpoint parsePrimaryExp (steps:nat)

(xs : list token)

: optionE (aexp * list token) :=

match steps with

| 0 ⇒ NoneE "Too many recursive calls"

| S steps' ⇒

DO (i, rest) <-- parseIdentifier xs ;

SomeE (AId i, rest)

OR DO (n, rest) <-- parseNumber xs ;

SomeE (ANum n, rest)

OR (DO (e, rest) <== firstExpect "("

(parseSumExp steps') xs;

DO (u, rest') <== expect ")" rest ;

SomeE(e,rest'))

end

with parseProductExp (steps:nat)

(xs : list token) :=

match steps with

| 0 ⇒ NoneE "Too many recursive calls"

| S steps' ⇒

DO (e, rest) <==

parsePrimaryExp steps' xs ;

DO (es, rest') <==

many (firstExpect "*" (parsePrimaryExp steps'))

steps' rest;

SomeE (fold_left AMult es e, rest')

end

with parseSumExp (steps:nat) (xs : list token)  :=

match steps with

| 0 ⇒ NoneE "Too many recursive calls"

| S steps' ⇒

DO (e, rest) <==

parseProductExp steps' xs ;

DO (es, rest') <==

many (fun xs ⇒

DO (e,rest') <--

firstExpect "+"

(parseProductExp steps') xs;

SomeE ( (true, e), rest')

OR DO (e,rest') <==

firstExpect "-"

(parseProductExp steps') xs;

SomeE ( (false, e), rest'))

steps' rest;

SomeE (fold_left (fun e[0] term ⇒

match term with

(true,  e) ⇒ APlus e[0] e

| (false, e) ⇒ AMinus e[0] e

end)

es e,

rest')

end.

Definition parseAExp := parseSumExp.

```

    Parsing boolean expressions:

```

Fixpoint parseAtomicExp (steps:nat)

(xs : list token)  :=

match steps with

| 0 ⇒ NoneE "Too many recursive calls"

| S steps' ⇒

DO    (u,rest) <-- expect "true" xs;

SomeE (BTrue,rest)

OR DO (u,rest) <-- expect "false" xs;

SomeE (BFalse,rest)

OR DO (e,rest) <--

firstExpect "not"

(parseAtomicExp steps')

xs;

SomeE (BNot e, rest)

OR DO (e,rest) <--

firstExpect "("

(parseConjunctionExp steps') xs;

(DO (u,rest') <== expect ")" rest;

SomeE (e, rest'))

OR DO (e, rest) <== parseProductExp steps' xs;

(DO (e', rest') <--

firstExpect "=="

(parseAExp steps') rest;

SomeE (BEq e e', rest')

OR DO (e', rest') <--

firstExpect "≤"

(parseAExp steps') rest;

SomeE (BLe e e', rest')

OR

NoneE

"Expected '==' or '≤' after arithmetic expression")

end

with parseConjunctionExp (steps:nat)

(xs : list token) :=

match steps with

| 0 ⇒ NoneE "递归调用太多"

| S steps' ⇒

DO (e, rest) <==

parseAtomicExp steps' xs ;

DO (es, rest') <==

many (firstExpect "&&"

(parseAtomicExp steps'))

steps' rest;

SomeE (fold_left BAnd es e, rest')

end.

Definition parseBExp := parseConjunctionExp.

Check parseConjunctionExp.

Definition testParsing {X : Type}

(p : nat →

list token →

optionE (X * list token))

(s : string) :=

let t := tokenize s in

p 100 t.

(* 计算 parse "   testParsing parseProductExp "x*y*(x*x)*x". 计算 parse "   testParsing parseConjunctionExp "not((x==x||x*x<=(x*x)*x)&&x==x".  *)

```

    Parsing commands:

```

Fixpoint parseSimpleCommand (steps:nat)

(xs : list token) :=

match steps with

| 0 ⇒ NoneE "递归调用太多"

| S steps' ⇒

DO (u, rest) <-- expect "SKIP" xs;

SomeE (SKIP, rest)

OR DO (e,rest) <--

firstExpect "IF" (parseBExp steps') xs;

DO (c,rest')  <==

firstExpect "THEN"

(parseSequencedCommand steps') rest;

DO (c',rest'') <==

firstExpect "ELSE"

(parseSequencedCommand steps') rest';

DO (u,rest''') <==

expect "END" rest'';

SomeE(IFB e THEN c ELSE c' FI, rest''')

OR DO (e,rest) <--

firstExpect "WHILE"

(parseBExp steps') xs;

DO (c,rest') <==

firstExpect "DO"

(parseSequencedCommand steps') rest;

DO (u,rest'') <==

expect "END" rest';

SomeE(WHILE e DO c END, rest'')

OR DO (i, rest) <==

parseIdentifier xs;

DO (e, rest') <==

firstExpect ":=" (parseAExp steps') rest;

SomeE(i ::= e, rest')

end

with parseSequencedCommand (steps:nat)

(xs : list token) :=

match steps with

| 0 ⇒ NoneE "递归调用太多"

| S steps' ⇒

DO (c, rest) <==

parseSimpleCommand steps' xs;

DO (c', rest') <--

firstExpect ";"

(parseSequencedCommand steps') rest;

SomeE(c ;; c', rest')

OR

SomeE(c, rest)

end.

Definition bignumber := 1000.

Definition parse (str : string) : optionE (com * list token) :=

let tokens := tokenize str in

parseSequencedCommand bignumber tokens.

```

# Examples

```

(* 计算 parse "   IF x == y + 1 + 2 - y * 6 + 3 THEN     x := x * 1;;     y := 0   ELSE     SKIP   END  ". ====>   SomeE      (IFB BEq (AId (Id 0))               (APlus                  (AMinus (APlus (APlus (AId (Id 1)) (ANum 1)) (ANum 2))                     (AMult (AId (Id 1)) (ANum 6)))                  (ANum 3))       THEN Id 0 ::= AMult (AId (Id 0)) (ANum 1);; Id 1 ::= ANum 0       ELSE SKIP FI, ) *)

(* 计算 parse "   SKIP;;   z:=x*y*(x*x);;   WHILE x==x DO     IF z <= z*z && not x == 2 THEN       x := z;;       y := z     ELSE       SKIP     END;;     SKIP   END;;   x:=z  ". ====>   SomeE      (SKIP;;       Id 0 ::= AMult (AMult (AId (Id 1)) (AId (Id 2)))                      (AMult (AId (Id 1)) (AId (Id 1)));;       WHILE BEq (AId (Id 1)) (AId (Id 1)) DO         IFB BAnd (BLe (AId (Id 0)) (AMult (AId (Id 0)) (AId (Id 0))))                   (BNot (BEq (AId (Id 1)) (ANum 2)))  ��         THEN Id 1 ::= AId (Id 0);; Id 2 ::= AId (Id 0)            ELSE SKIP FI;;         SKIP       END;;       Id 1 ::= AId (Id 0),      ) *)

(* 计算解析 "   SKIP;;   z:=x*y*(x*x);;   WHILE x==x DO     IF z <= z*z && not x == 2 THEN       x := z;;       y := z     ELSE       SKIP     END;;     SKIP   END;;   x:=z  ". =====>   SomeE      (SKIP;;       Id 0 ::= AMult (AMult (AId (Id 1)) (AId (Id 2)))             (AMult (AId (Id 1)) (AId (Id 1)));;       WHILE BEq (AId (Id 1)) (AId (Id 1)) DO         IFB BAnd (BLe (AId (Id 0)) (AMult (AId (Id 0)) (AId (Id 0))))                  (BNot (BEq (AId (Id 1)) (ANum 2)))           THEN Id 1 ::= AId (Id 0);;                Id 2 ::= AId (Id 0)           ELSE SKIP         FI;;         SKIP       END;;       Id 1 ::= AId (Id 0),      ). *)

(* /DROP *)

```

```
