# 序言

```

```

# 欢迎

    本电子书是关于*软件基础*的课程，该课程

    可靠软件的数学基础。主题包括

    逻辑的基本概念，计算机辅助定理证明，该

    Coq 证明助手，函数式编程，操作

    语义学，霍尔逻辑和静态类型系统。叙述

    面向广泛读者，从高级

    本科生到博士生和研究人员。没有具体

    假设具有逻辑或编程语言背景，尽管

    数学素养程度将有所帮助。

    该课程的主要新颖之处在于它是百分之百

    百分之百形式化和机器检查：整个文本都是

    简直就是 Coq 的脚本。它旨在被阅读

    与 Coq 的交互会话一起（或内部）。所有

    文本中的细节在 Coq 中完全形式化，大部分

    练习设计为使用 Coq 进行。

    文件组织成一系列核心章节，涵盖

    大约一个学期的材料并组织成一个

    连贯的线性叙述，再加上一些“分支”章节

    涵盖其他主题。所有核心章节都适用

    既适用于高年级本科生又适用于研究生。

```

# Overview

    Building reliable software is hard.  The scale and complexity of
    modern systems, the number of people involved in building them,
    and the range of demands placed on them make it extremely
    difficult to build software that is even more-or-less correct,
    much less 100% correct.  At the same time, the increasing degree
    to which information processing is woven into every aspect of
    society greatly amplifies the cost of bugs and insecurities.

    Computer scientists and software engineers have responded to these
    challenges by developing a whole host of techniques for improving
    software reliability, ranging from recommendations about managing
    software projects teams (e.g., extreme programming) to design
    philosophies for libraries (e.g., model-view-controller,
    publish-subscribe, etc.) and programming languages (e.g.,
    object-oriented programming, aspect-oriented programming,
    functional programming, ...) to mathematical techniques for
    specifying and reasoning about properties of software and tools
    for helping validate these properties.  The present course is
    focused on this last set of techniques.

    The text weaves together five conceptual threads:

    (1) basic tools from *logic* for making and justifying precise
        claims about programs;

    (2) the use of *proof assistants* to construct rigorous logical
        arguments;

    (3) *functional programming*, both as a method of programming that
        simplifies reasoning about programs and as a bridge between
        programming and logic;

    (4) formal techniques for *reasoning about the properties of specific programs* (e.g., the fact that a sorting function or
        a compiler obeys some formal specification); and

    (5) the use of *type systems* for establishing well-behavedness
        guarantees for *all* programs in a given programming
        language (e.g., the fact that well-typed Java programs cannot
        be subverted at runtime).

    Each of these is easily rich enough to fill a whole course in its
    own right, and tackling all of them together naturally means that
    much will be left unsaid.  Nevertheless, we hope readers will find
    that these themes illuminate and amplify each other and that
    bringing them together creates a good foundation for digging into
    any of them more deeply.  Some suggestions for further reading can
    be found in the Postscript chapter.  Bibliographic
    information for all cited works can be found in the file
    Bib. 

## Logic

    Logic is the field of study whose subject matter is *proofs* —
    unassailable arguments for the truth of particular propositions.
    Volumes have been written about the central role of logic in
    computer science.  Manna and Waldinger called it "the calculus of
    computer science," while Halpern et al.'s paper *On the Unusual Effectiveness of Logic in Computer Science* catalogs scores of
    ways in which logic offers critical tools and insights.  Indeed,
    they observe that, "As a matter of fact, logic has turned out to
    be significiantly more effective in computer science than it has
    been in mathematics.  This is quite remarkable, especially since
    much of the impetus for the development of logic during the past
    one hundred years came from mathematics."

    In particular, the fundamental tools of *inductive proof* are
    ubiquitous in all of computer science.  You have surely seen them
    before, perhaps in a course on discrete math or analysis of
    algorithms, but in this course we will examine them much more
    deeply than you have probably done so far. 

## Proof Assistants

    The flow of ideas between logic and computer science has not been
    unidirectional: CS has also made important contributions to logic.
    One of these has been the development of software tools for
    helping construct proofs of logical propositions.  These tools
    fall into two broad categories:

*   *Automated theorem provers* provide "push-button" operation: you give them a proposition and they return either *true* or *false* (or, sometimes, *don't know: ran out of time*). Although their capabilities are still limited to specific domains, they have matured tremendously in recent years and are used now in a multitude of settings. Examples of such tools include SAT solvers, SMT solvers, and model checkers. 

*   *Proof assistants* are hybrid tools that automate the more routine aspects of building proofs while depending on human guidance for more difficult aspects. Widely used proof assistants include Isabelle, Agda, Twelf, ACL2, PVS, and Coq, among many others.

    This course is based around Coq, a proof assistant that has been
    under development since 1983 and that in recent years has
    attracted a large community of users in both research and
    industry.  Coq provides a rich environment for interactive
    development of machine-checked formal reasoning.  The kernel of
    the Coq system is a simple proof-checker, which guarantees that
    only correct deduction steps are ever performed.  On top of this
    kernel, the Coq environment provides high-level facilities for
    proof development, including a large library of common definitions
    and lemmas, powerful tactics for constructing complex proofs
    semi-automatically, and a special-purpose programming language for
    defining new proof-automation tactics for specific situations.

    Coq has been a critical enabler for a huge variety of work across
    computer science and mathematics:

*   As a *platform for modeling programming languages*, it has become a standard tool for researchers who need to describe and reason about complex language definitions. It has been used, for example, to check the security of the JavaCard platform, obtaining the highest level of common criteria certification, and for formal specifications of the x[86] and LLVM instruction sets and programming languages such as C. 

*   As an *environment for developing formally certified software and hardware*, Coq has been used, for example, to build CompCert, a fully-verified optimizing compiler for C, and CertiKos, a fully verified hypervisor, for proving the correctness of subtle algorithms involving floating point numbers, and as the basis for CertiCrypt, an environment for reasoning about the security of cryptographic algorithms. It is also being used to build verified implementations of the open-source RISC-V processor. 

*   As a *realistic environment for functional programming with dependent types*, it has inspired numerous innovations. For example, the Ynot system embeds "relational Hoare reasoning" (an extension of the *Hoare Logic* we will see later in this course) in Coq. 

*   As a *proof assistant for higher-order logic*, it has been used to validate a number of important results in mathematics. For example, its ability to include complex computations inside proofs made it possible to develop the first formally verified proof of the 4-color theorem. This proof had previously been controversial among mathematicians because part of it included checking a large number of configurations using a program. In the Coq formalization, everything is checked, including the correctness of the computational part. More recently, an even more massive effort led to a Coq formalization of the Feit-Thompson Theorem — the first major step in the classification of finite simple groups.

    By the way, in case you're wondering about the name, here's what
   the official Coq web site at INRIA (the French national research
   lab where Coq has mostly been developed) says about it: "Some
   French computer scientists have a tradition of naming their
   software as animal species: Caml, Elan, Foc or Phox are examples of
   this tacit convention. In French, 'coq' means rooster, and it
   sounds like the initials of the Calculus of Constructions (CoC) on
   which it is based."  The rooster is also the national symbol of
   France, and C-o-q are the first three letters of the name of
   Thierry Coquand, one of Coq's early developers. 

## Functional Programming

    The term *functional programming* refers both to a collection of
    programming idioms that can be used in almost any programming
    language and to a family of programming languages designed to
    emphasize these idioms, including Haskell, OCaml, Standard ML,
    F#, Scala, Scheme, Racket, Common Lisp, Clojure, Erlang, and Coq.

    Functional programming has been developed over many decades —
    indeed, its roots go back to Church's lambda-calculus, which was
    invented in the 1930s, well before the first computers (at least
    the first electronic ones)!  But since the early '90s it has
    enjoyed a surge of interest among industrial engineers and
    language designers, playing a key role in high-value systems at
    companies like Jane St. Capital, Microsoft, Facebook, and
    Ericsson.

    The most basic tenet of functional programming is that, as much as
    possible, computation should be *pure*, in the sense that the only
    effect of execution should be to produce a result: it should be
    free from *side effects* such as I/O, assignments to mutable
    variables, redirecting pointers, etc.  For example, whereas an
    *imperative* sorting function might take a list of numbers and
    rearrange its pointers to put the list in order, a pure sorting
    function would take the original list and return a *new* list
    containing the same numbers in sorted order.

    A significant benefit of this style of programming is that it
    makes programs easier to understand and reason about.  If every
    operation on a data structure yields a new data structure, leaving
    the old one intact, then there is no need to worry about how that
    structure is being shared and whether a change by one part of the
    program might break an invariant that another part of the program
    relies on.  These considerations are particularly critical in
    concurrent systems, where every piece of mutable state that is
    shared between threads is a potential source of pernicious bugs.
    Indeed, a large part of the recent interest in functional
    programming in industry is due to its simpler behavior in the
    presence of concurrency.

    Another reason for the current excitement about functional
    programming is related to the first: functional programs are often
    much easier to parallelize than their imperative counterparts.  If
    running a computation has no effect other than producing a result,
    then it does not matter *where* it is run.  Similarly, if a data
    structure is never modified destructively, then it can be copied
    freely, across cores or across the network.  Indeed, the
    "Map-Reduce" idiom, which lies at the heart of massively
    distributed query processors like Hadoop and is used by Google to
    index the entire web is a classic example of functional
    programming.

    For purposes of this course, functional programming has yet
    another significant attraction: it serves as a bridge between
    logic and computer science.  Indeed, Coq itself can be viewed as a
    combination of a small but extremely expressive functional
    programming language plus a set of tools for stating and proving
    logical assertions.  Moreover, when we come to look more closely,
    we find that these two sides of Coq are actually aspects of the
    very same underlying machinery — i.e., *proofs are programs*.  

## Program Verification

    Approximately the first third of *Software Foundations* is devoted
    to developing the conceptual framework of logic and functional
    programming and gaining enough fluency with Coq to use it for
    modeling and reasoning about nontrivial artifacts.  In the middle
    third, we turn our attention to two broad topics of critical
    importance in building reliable software (and hardware):
    techniques for proving specific properties of particular
    *programs* and for proving general properties of whole programming
    *languages*.

    For both of these, the first thing we need is a way of
    representing programs as mathematical objects, so we can talk
    about them precisely, plus ways of describing their behavior in
    terms of mathematical functions or relations.  Our main tools for
    these tasks are *abstract syntax* and *operational semantics*, a
    method of specifying programming languages by writing abstract
    interpreters.  At the beginning, we work with operational
    semantics in the so-called "big-step" style, which leads to simple
    and readable definitions when it is applicable.  Later on, we
    switch to a lower-level "small-step" style, which helps make some
    useful distinctions (e.g., between different sorts of
    nonterminating program behaviors) and which is applicable to a
    broader range of language features, including concurrency.

    The first programming language we consider in detail is *Imp*, a
    tiny toy language capturing the core features of conventional
    imperative programming: variables, assignment, conditionals, and
    loops.

    We study two different ways of reasoning about the properties of
    Imp programs.  First, we consider what it means to say that two
    Imp programs are *equivalent* in the intuitive sense that they
    exhibit the same behavior when started in any initial memory
    state.  This notion of equivalence then becomes a criterion for
    judging the correctness of *metaprograms* — programs that
    manipulate other programs, such as compilers and optimizers.  We
    build a simple optimizer for Imp and prove that it is correct.

    Second, we develop a methodology for proving that a given Imp
    program satisfies some formal specifications of its behavior.  We
    introduce the notion of *Hoare triples* — Imp programs annotated
    with pre- and post-conditions describing what they expect to be
    true about the memory in which they are started and what they
    promise to make true about the memory in which they terminate —
    and the reasoning principles of *Hoare Logic*, a domain-specific
    logic specialized for convenient compositional reasoning about
    imperative programs, with concepts like "loop invariant" built in.

    This part of the course is intended to give readers a taste of the
    key ideas and mathematical tools used in a wide variety of
    real-world software and hardware verification tasks. 

## Type Systems

    Our final major topic, covering approximately the last third of
    the course, is *type systems*, which are powerful tools for
    establishing properties of *all* programs in a given language.

    Type systems are the best established and most popular example of
    a highly successful class of formal verification techniques known
    as *lightweight formal methods*.  These are reasoning techniques
    of modest power — modest enough that automatic checkers can be
    built into compilers, linkers, or program analyzers and thus be
    applied even by programmers unfamiliar with the underlying
    theories.  Other examples of lightweight formal methods include
    hardware and software model checkers, contract checkers, and
    run-time monitoring techniques.

    This also completes a full circle with the beginning of the book:
    the language whose properties we study in this part, the *simply typed lambda-calculus*, is essentially a simplified model of the
    core of Coq itself!

```

## 进一步阅读

    本文旨在是自包含的，但寻求更深入了解的读者

    为了更深入地研究特定主题，读者会发现一些

    进一步阅读建议在附录中

    章节。

```

# Practicalities

## Chapter Dependencies

    A diagram of the dependencies between chapters and some 
    paths through the material can be found in the file deps.html. 

## System Requirements

    Coq runs on Windows, Linux, and OS X.  You will need:

*   A current installation of Coq, available from the Coq home page. Everything should work with version 8.4 (or 8.5). 

*   An IDE for interacting with Coq. Currently, there are two choices: 

    *   Proof General is an Emacs-based IDE. It tends to be preferred by users who are already comfortable with Emacs. It requires a separate installation (google "Proof General"). 

         Adventurous users of Coq within Emacs may also want to check out extensions such as company-coq and control-lock. 

    *   CoqIDE is a simpler stand-alone IDE. It is distributed with Coq, so it should be available once you have Coq installed. It can also be compiled from scratch, but on some platforms this may involve installing additional packages for GUI libraries and such.

## Exercises

    Each chapter includes numerous exercises.  Each is marked with a
    "star rating," which can be interpreted as follows:

*   One star: easy exercises that underscore points in the text and that, for most readers, should take only a minute or two. Get in the habit of working these as you reach them. 

*   Two stars: straightforward exercises (five or ten minutes). 

*   Three stars: exercises requiring a bit of thought (ten minutes to half an hour). 

*   Four and five stars: more difficult exercises (half an hour and up).

    Also, some exercises are marked "advanced," and some are marked
    "optional."  Doing just the non-optional, non-advanced exercises
    should provide good coverage of the core material.  Optional
    exercises provide a bit of extra practice with key concepts and
    introduce secondary themes that may be of interest to some
    readers.  Advanced exercises are for readers who want an extra
    challenge and a deeper cut at the material.

    *Please do not post solutions to the exercises in a public places*: 
    Software Foundations is widely used both for self-study and for
    university courses.  Having solutions easily available makes it
    much less useful for courses, which typically have graded homework
    assignments.  We especially request that readers not post
    solutions to the exercises anyplace where they can be found by
    search engines.

## Downloading the Coq Files

    A tar file containing the full sources for the "release version"
    of this book (as a collection of Coq scripts and HTML files) is
    available here:

```

        http://www.cis.upenn.edu/~bcpierce/sf

```

    (If you are using the book as part of a class, your professor may
    give you access to a locally modified version of the files, which
    you should use instead of the release version.)

```

# 讲师注意事项

    如果您计划在自己的课程中使用这些材料，您将

    毫无疑问，您会发现您想要更改，改进或添加的内容。

    欢迎您的贡献！

    为了保持法律简单并拥有一个单一的“记录作者”，如下所示：

    在需要时负责的一点是，如果有必要的话

    调整许可条款，转让许可等，我们要求所有

    贡献者（即，所有可以访问开发者的人

    存储库）将其贡献的版权转让给

    适当的“记录作者”如下：

+   我特此将我过去和未来对软件基础项目的贡献的版权转让给每卷或组件的“记录作者”，并授权以与软件基础的其余部分相同的条款许可。我了解，目前，“记录作者”如下：对于直到 2016 年被称为“软件基础”并从 2016 年起分别为“逻辑基础”和“编程基础”的第 1 卷和第 2 卷，作者是本杰明·皮尔斯。对于第 3 卷，“验证功能算法”，作者是安德鲁·W·阿普尔。对于指定卷之外的组件（例如，排版和评分工具以及其他软件基础设施），作者是本杰明·皮尔斯。

    要开始，请发送电子邮件给本杰明·皮尔斯，描述

    自己以及您计划如何使用这些材料并包括

    （1）上述版权转让文本和

    （2）执行“htpasswd -s -n NAME”的结果

    其中 NAME 是您首选的用户名。

    我们会为您提供访问子版本库的权限，并

    开发者邮件列表。在存储库中，您会找到一个

    附有进一步说明的文件 INSTRUCTORS。

```

# Translations

    Thanks to the efforts of a team of volunteer translators,
    *Software Foundations* can be enjoyed in Japanese at
    [`proofcafe.org/sf`](http://proofcafe.org/sf).  A Chinese translation is underway. 

```

```

```

```

```

```

```
