# 后记 

```

    Congratulations: We've made it to the end! 

# Looking Back

    We've covered a lot of ground.  Here's a quick review...  

*   *Functional programming*: 

    *   "declarative" programming style (recursion over persistent data structures, rather than looping over mutable arrays or pointer structures)

    *   higher-order functions

    *   polymorphism

*   *Logic*, the mathematical basis for software engineering: 

    ```

                逻辑                        微积分 

            --------------------   ~   ---------------------------- 

            软件工程       机械/土木工程 

    ```

    *   inductively defined sets and relations

    *   inductive proofs

    *   proof objects

*   *Coq*, an industrial-strength proof assistant 

    *   functional core language

    *   core tactics

    *   automation

*   *Foundations of programming languages* 

    *   notations and definitional techniques for precisely specifying 

        *   abstract syntax

        *   operational semantics 

            *   big-step style

            *   small-step style

        *   type systems 

    *   program equivalence 

    *   Hoare logic 

    *   fundamental metatheory of type systems 

        *   progress and preservation 

    *   theory of subtyping

```

# 四处看看 

    这些核心主题的大规模应用可以找到 

    到处都是，无论是正在进行的研究项目还是实际世界 

    软件系统。 这里有一些涉及的最新例子 

    实际软件和机器检查验证的形式验证 

    硬件系统，以了解正在进行的工作 

    今天... 

### CompCert 

    *CompCert*是一个几乎所有的完全验证的优化编译器 

    ISO C[90] / ANSI C 语言的代码，为 x[86]，ARM 生成代码， 

    和 PowerPC 处理器。 CompCert 的整体都是用 

    Gallina 并提取为一个高效的 OCaml 程序，使用 Coq 的 

    提取设施。 

    "CompCert 项目调查了 

    适用于关键嵌入式软件的现实编译器。 这样的 

    验证的编译器���带数学的，机器检查的证明 

    生成的可执行代码的行为与规定完全一致 

    通过源程序的语义。 通过排除 

    编译器引入的错误的可能性，验证的编译器 

    加强可以通过应用形式获得的保证 

    方法到源程序。 

    2011 年，CompCert 被纳入一项关于模糊测试的里程碑研究 

    大量真实世界的 C 编译器使用 CSmith 工具。 

    CSmith 的作者写道： 

+   我们 CompCert 结果的显着之处在于我们在所有其他编译器中发现的中间错误在其中都不存在。 截至 2011 年初，我们测试过的正在开发中的 CompCert 版本是我们测试过的唯一一个 Csmith 找不到错误代码错误的编译器。 这不是因为没有尝试：我们已经致力于这项任务约六个 CPU 年。 CompCert 的明显不可破坏性支持了一个强有力的论点，即在证明框架内开发编译器优化，其中安全检查是明确的并且经过机器检查，对于编译器用户具有切实的好处。 

    [`compcert.inria.fr`](http://compcert.inria.fr) 

### seL4 

    *seL4*是一个完全验证的微内核，被认为是 

    具有实现端到端证明的世界第一的 OS 内核 

    正确性和安全执行。 它是用 C 实现的 

    ARM 汇编并使用 Isabelle 指定和验证。 代码 

    可作为开源提供。

    "seL4 已经全面形式验证：一个严格的 

    证明其可执行代码的数学过程，因为它 

    在硬件上运行，正确实现了允许的行为 

    规范，并没有其他。 此外，我们已经证明 

    规范具有所需的安全性和安全性 

    属性（完整性和机密性）...验证已经完成 

    达到的成本明显低于 

    传统的高保障开发方法，同时给予 

    传统方法无法提供的保证。 

    [`sel4.systems`](https://sel4.systems)。 

### CertiKOS 

    *CertiKOS*是一个全面验证的清洁状态虚拟化程序，编写在 

    CompCert C 和 Coq 中的验证

    “CertiKOS 项目旨在开发一种新颖实用的

    用于构建大规模认证的编程基础设施

    系统软件。通过结合最近的编程进步

    语言，操作系统和形式方法，我们希望

    攻击以下研究问题：（1）什么操作系统内核

    结构可以为可扩展性、安全性提供最佳支持，

    和韧性？（2）哪些语义模型和程序逻辑可以

    最好捕捉这些抽象？（3）什么是正确的

    用于开发此类环境的编程语言和环境

    认证内核？和（4）如何构建自动化设施

    使认证软件开发真正扩展？

    [`flint.cs.yale.edu/certikos/`](http://flint.cs.yale.edu/certikos/)

### 铁甲

    *铁甲应用程序*是一组完全验证的网络

    应用程序，包括用于安全签名的“公证人”

    语句，密码哈希器，多用户可信计数器和

    差分私有数据库。

    该系统是以面向验证的编程编写的

    语言 Dafny 并使用 Boogie 进行验证，一种验证工具

    基于霍尔逻辑。

    “一个铁甲应用程序允许用户安全地传输她的数据到

    远程机器，保证每条指令都得到执行

    该机器上的应用程序遵循正式的抽象规范

    应用程序的行为。这不仅消除了实现

    漏洞，如缓冲区溢出，解析错误或数据

    泄漏；它告诉用户应用程序将如何在所有情况下表现

    时间。我们通过完整的低级别提供这些保证

    软件验证。然后我们使用加密和安全

    硬件，以实现从经过验证的软件到安全通道

    远程用户。”

    [`github.com/Microsoft/Ironclad/tree/master/ironclad-apps`](https://github.com/Microsoft/Ironclad/tree/master/ironclad-apps)

### Verdi

    *Verdi*是一个用于实现和正式验证的框架

    分布式系统。

    “Verdi 支持几种不同的故障模型，范围从

    理想到现实。Verdi 的验证系统

    变压器（VSTs）封装了常见的容错

    技术。开发人员可以在理想化的环境中验证应用程序

    故障模型，然后应用 VST 获得一个应用程序

    保证在更具对抗性的环境中具有类似的属性

    环境。Verdi 是使用 Coq 证明助手开发的

    系统被提取到 OCaml 以供执行。Verdi 系统，

    包括容错键值存储，实现可比较的

    性能与未经验证的对应物相比。”

    [`verdi.uwplse.org`](http://verdi.uwplse.org)

### DeepSpec

    *深度规范的科学*是 NSF 的“远征”

    项目（从 2016 年到 2020 年）专注于

    完全正确的规范和验证

    软件和硬件。它还赞助研讨会和暑期

    学校。

+   网站：[`deepspec.org/`](http://deepspec.org/)

+   概述演示：

    +   [`deepspec.org/about/`](http://deepspec.org/about/)

    +   [`www.youtube.com/watch?v=IPNdsnRWBkk`](https://www.youtube.com/watch?v=IPNdsnRWBkk)

### REMS

    *REMS*是一个关于主流严格工程的欧洲项目

    系统。它已经制定了广泛的正式规范

    一系列关键的现实世界接口、协议和 API，

    包括

    C 语言，

    ELF 链接器格式，

    ARM、Power、MIPS、CHERI 和 RISC-V 指令集，

    ARM 和 Power 处理器的弱内存模型，以及

    POSIX 文件系统。

    “该项目专注于轻量级严格方法：精确

    规范（事后和设计期间）和针对

    规范，在某些情况下进行全面验证。该

    项目强调构建有用（和可重用）的语义和

    工具。我们正在构建准确的全尺度数学模型

    一些关键的计算抽象（处理器

    架构、编程语言、并发操作系统接口，

    和网络协议），研究如何实现这一点，以及

    研究如何利用这些模型进行新的验证

    研究和新的系统和编程语言

    研究。为了支持所有这些，我们还在研究新的

    规范工具及其基础。

    [`www.cl.cam.ac.uk/~pes20/rems/`](http://www.cl.cam.ac.uk/~pes20/rems/)

### 其他

    还有更多。其他值得关注的项目包括：

+   Vellvm（LLVM 优化通道的形式化规范和验证）

+   扎克·塔特洛克的正式认证的浏览器

+   托比亚斯·尼普考对大部分 Java 的形式化

+   CakeML 验证 ML 编译器

+   格雷格·莫里塞特对 x[86]指令集和 RockSalt 软件故障隔离工具（谷歌原生客户端的更好、更快、更安全版本）的正式规范

+   Ur/Web，一种用于在 Coq 中嵌入的验证 Web 应用程序的编程语言

+   普林斯顿验证软件工具链

```

# Looking Forward

    Some good places to learn more...

*   This book includes several optional chapters covering topics that you may find useful. Take a look at the table of contents and the chapter dependency diagram to find them. 

*   Cutting-edge conferences on programming languages and formal verification: 

    *   Principles of Programming Langauges (POPL)

    *   Programming Language Design and Implementation (PLDI)

    *   SPLASH/OOPSLA

    *   International Conference on Functional Programming (ICFP)

    *   Computer Aided Verification (CAV)

    *   Interactive Theorem Proving (ITP)

    *   Principles in Practice workshop (PiP)

    *   CoqPL workshop 

*   More on functional programming 

    *   Learn You a Haskell for Great Good, by Miran Lipovaca [[Lipovaca 2011]](Bib.html#Lipovaca 2011).

    *   Real World Haskell, by Bryan O'Sullivan, John Goerzen, and Don Stewart [[O'Sullivan 2008]](Bib.html#O'Sullivan 2008)

    *   ...and many other excellent books on Haskell, OCaml, Scheme, Racket, Scala, F sharp, etc., etc. 

*   More on Hoare logic and program verification 

    *   The Formal Semantics of Programming Languages: An Introduction, by Glynn Winskel [[Winskel 1993]](Bib.html#Winskel 1993).

    *   Many practical verification tools, e.g. Microsoft's Boogie system, Java Extended Static Checking, etc. 

*   More on the foundations of programming languages: 

    *   Concrete Semantics with Isabelle/HOL, by Tobias Nipkow and Gerwin Klein [[Nipkow 2014]](Bib.html#Nipkow 2014)

    *   Types and Programming Languages, by Benjamin C. Pierce [[Pierce 2002]](Bib.html#Pierce 2002).

    *   Practical Foundations for Programming Languages, by Robert Harper [[Harper 2016]](Bib.html#Harper 2016).

    *   Foundations for Programming Languages, by John C. Mitchell [[Mitchell 1996]](Bib.html#Mitchell 1996). 

*   More on Coq: 

    *   Verified Functional Algorithms, by Andrew Appel [[Chlipala 2013]](Bib.html#Chlipala 2013).

    *   Certified Programming with Dependent Types, by Adam Chlipala [[Chlipala 2013]](Bib.html#Chlipala 2013).

    *   Interactive Theorem Proving and Program Development: Coq'Art: The Calculus of Inductive Constructions, by Yves Bertot and Pierre Casteran [[Bertot 2004]](Bib.html#Bertot 2004).

    *   Iron Lambda (http://iron.ouroborus.net/) is a collection of ​Coq formalisations for functional languages of increasing complexity. It fills part of the gap between the end of the​ Software Foundations course and what appears in current research papers. The collection has at least Progress and Preservation theorems for a number of variants of STLC and the polymorphic lambda-calculus (System F).

```

(* $Date: 2016-12-08 16:57:10 -0500 (Thu, 08 Dec 2016) $ *)

```

```

```

```
