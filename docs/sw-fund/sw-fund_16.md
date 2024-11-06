# 从 Coq 中提取 ML

```

```

(* DROP *)

```

# Basic Extraction

    In its simplest form, extracting an efficient program from one
    written in Coq is completely straightforward. 

    First we say what language we want to extract into.  Options are
    OCaml (the most mature), Haskell (which mostly works), and
    Scheme (a bit out of date).

```

提取语言 Ocaml。

```

    Now we load up the Coq environment with some definitions, either
    directly or by importing them from other modules.

```

Require Import Coq.Arith.Arith.

Require Import Coq.Arith.EqNat.

Require Import ImpCEvalFun.

```

    Finally, we tell Coq the name of a definition to extract and the
    name of a file to put the extracted code into.

```

Extraction "imp1.ml" ceval_step.

```

    When Coq processes this command, it generates a file imp1.ml
    containing an extracted version of ceval_step, together with
    everything that it recursively depends on.  Compile the present
    .v file and have a look at imp1.ml now.

```

# 控制特定类型的提取

    我们可以告诉 Coq 将某些归纳定义提取到

    特定的 OCaml 类型。对于每一个，我们必须说明

+   Coq 类型本身在 OCaml 中应该如何表示，以及

+   每个构造函数应如何翻译。

```
Extract Inductive bool ⇒ "bool" [ "true" "false" ].

```

    此外，对于非枚举类型（其中构造函数采用

    参数），我们给出一个可以用作

    对类型的元素进行“递归器”。（想想教堂数。）

```
Extract Inductive nat ⇒ "int"
  [ "0" "(fun x → x + 1)" ]
  "(fun zero succ n →
      if n=0 then zero () else succ (n-1))".

```

    我们还可以将定义的常量提取为特定的 OCaml 术语或

    运算符。

```
Extract Constant plus ⇒ "( + )".
Extract Constant mult ⇒ "( * )".
Extract Constant beq_nat ⇒ "( = )".

```

    重要提示：完全是*你的责任*确保

    您正在证明的翻译是否有意义。例如，可能

    诱人的是包括这一个

```
      Extract Constant minus ⇒ "( - )".

    but doing so could lead to serious confusion!  (Why?)

```

Extraction "imp2.ml" ceval_step.

```

    Have a look at the file imp2.ml.  Notice how the fundamental
    definitions have changed from imp1.ml.

```

# 一个完整的例子

    要使用我们提取的评估器运行 Imp 程序，我们只需要

    add 是一个调用评估器并打印的小型驱动程序

    输出结果。

    为了简单起见，我们将通过倾倒出前四个

    最终状态中的内存位置。

    此外，为了更容易输入示例，让我们提取一个

    从 ImpParser Coq 模块中提取解析器。为此，我们需要一些

    设置 Coq 之间正确对应的魔术声明

    OCaml 字符的字符串和列表。

```
Require Import Ascii String.
Extract Inductive ascii ⇒ char
[
"(* If this appears, you're using Ascii internals. Please don't *) (fun (b0,b1,b2,b3,b4,b5,b6,b7) → let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(* If this appears, you're using Ascii internals. Please don't *) (fun f c → let n = Char.code c in let h i = (n land (1 lsl i)) ≠ 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".
Extract Constant zero ⇒ "'\000'".
Extract Constant one ⇒ "'\001'".
Extract Constant shift ⇒
 "fun b c → Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)".
Extract Inlined Constant ascii_dec ⇒ "(=)".

```

    我们还需要另一种布尔值的变体。

```
Extract Inductive sumbool ⇒ "bool" ["true" "false"].

```

    提取与往常一样。

```
Require Import Imp.
Require Import ImpParser.
Extraction "imp.ml" empty_state ceval_step parse.

```

    现在让我们运行生成的 Imp 评估器。首先，看一看

    impdriver.ml。（这是手写的，而不是提取的。）

    接下来，将驱动程序与提取的代码一起编译并

    执行它，如下所示。

```
        ocamlc -w -20 -w -26 -o impdriver imp.mli imp.ml impdriver.ml
        ./impdriver

```

    （ocamlc 的-w 标志只是为了抑制一些

    不必要的警告。）

```

# Discussion

    Since we've proved that the ceval_step function behaves the same
    as the ceval relation in an appropriate sense, the extracted
    program can be viewed as a *certified* Imp interpreter.  Of
    course, the parser we're using is not certified, since we didn't
    prove anything about it!

```

(* /DROP *)

```

```

```

```

```

```
