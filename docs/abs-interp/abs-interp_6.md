# 6  基于抽象解释的工具

下面列出的静态分析和验证自动工具清单提供了抽象解释在软件验证中的实际应用范围的一种想法（但这个清单绝对不是详尽的）。这些工具旨在保证准确性。由于不存在通用工具（由于不可判定性），因此这些工具必然是不完全的，并且在产生很少的误报和扩展到非常大的程序方面各不相同。

### 6.1  [Airac5](http://ropas.snu.ac.kr/airac5/)

一款来自[首尔国立大学](http://www.useoul.edu/) [编程研究实验室](http://ropas.snu.ac.kr/) 和[RopasWork](http://ropaswork.com/) 的静态分析器，用于自动检测 C 程序中的缓冲区溢出错误。

### 6.2  [aiT WCET Analyzers](http://www.absint.com/ait/)

来自[AbsInt Angewandte Informatik](http://www.absint.com/) 的商业静态分析器，用于在实时系统中静态计算任务最坏情况执行时间（WCET）的严格界限。

### 6.3  [ASTRÉE](http://www.astree.ens.fr/)

一款来自[巴黎高等师范学校](http://www.ens.fr/)的静态分析器，专门用于证明用 C 语言编写的同步控制/命令程序中不存在运行时错误。

### 6.4  [C Global Surveyor](http://ti.arc.nasa.gov/ase/cgs/index.html)

一款来自[NASA](http://ti.arc.nasa.gov/index.php) [Ames](http://ti.arc.nasa.gov/index.php) [Research](http://ti.arc.nasa.gov/index.php) [Center](http://ti.arc.nasa.gov/index.php) [智能系统部门](http://ti.arc.nasa.gov/index.php) 的研究原型静态分析器，用于发现 C 程序中的运行时错误。

### 6.5  [Fluctuat](http://www-list.cea.fr/labos/gb/LSL/fluctuat/index.html)

一款来自[CEA-LIST](http://www-list.cea.fr/) 的静态分析器，用于研究 C 或汇编程序中浮点计算中舍入误差的传播。

### 6.6  [PolySpace Verifier](http://www.polyspace.com/products.htm)

一款来自[PolySpace Technologies](http://www.polyspace.com/) 的商业通用静态分析器，用于检测 Ada、C、C++和 Java 中的运行时错误。

### 6.7  [TERMINATOR](http://research.microsoft.com/terminator/)

一款来自[Microsoft Research Cambridge](http://research.microsoft.com/aboutmsr/labs/cambridge/) 的静态分析器，用于证明 C 程序的终止和一般存活性属性。

### 6.8  [TVLA](http://www.cs.tau.ac.il/~tvla/)

[TVLA](http://www.cs.tau.ac.il/~tvla/) 是在[特拉维夫大学](http://www.cs.tau.ac.il/) 开发的一个研究工具，用于使用程序语义的逻辑描述和预定义的谓词抽象来进行抽象解释实验。
