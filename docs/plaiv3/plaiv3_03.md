## 结构化我们的研究

正如我在其他地方更详细地论证过[elsewhere](https://www.google.com/url?q=https://cs.brown.edu/~sk/Publications/Papers/Published/sk-teach-pl-post-linnaean/&sa=D&source=editors&ust=1695232021063528&usg=AOvVaw37Mi6t9TcyPiWLJtD_NsvH)，将编程语言视为特性的集合更有意义。特性是构建块。当然，一旦组合，语言更像化合物而不是混合物：特性以可能难以预测的方式相互作用。因此，理解特性和它们的组合是理解语言的一种有价值的途径。

本书围绕一个核心思想展开，即 SMoL，即语言的标准模型。这是许多我们广泛使用的编程语言的计算核心的体现，从 C#和 Java 到 JavaScript、Lua、Python 和 Ruby，再到 OCaml 和 Racket。敏锐的读者会注意到，这种共性并不尊重“范式”。相反，所有这些语言（以及许多其他语言），在很大程度上，都有一个共同的计算核心：安全的运行时系统、自动的内存管理、贪婪求值、一等词法作用域函数、一等可变变量和一等可变结构。当代编程需要对这些有深刻的理解。例如，我认为，如果不理解 SMoL，你就无法理解并发中的突变、静态成员或所有权。

然而，由于语言是人为的，编程几乎是无限可塑的，即使是“标准”特性在历史上也看到了变化。因此，当我们跨越特性时，我们也想研究它们内部的差异。我们通过使用[mystery language](https://www.google.com/url?q=https://cs.brown.edu/~sk/Publications/Papers/Published/pkf-teach-pl-exp-adv-think/&sa=D&source=editors&ust=1695232021064466&usg=AOvVaw0VIwT72D0WNabBksW4GD3x)方法来做这件事：使用固定的语法，我们探索相同特性可以表现出的不同方式。这希望基于[对比案例](https://www.google.com/url?q=https://www.cultofpedagogy.com/contrasting-cases/&sa=D&source=editors&ust=1695232021064751&usg=AOvVaw1sitvi37D-BaEv1xrf6erl)的认知理论来提高学习效果。

当然，SMoL 中包含的内容是一个判断：当一个特性在大量不同的语言中（如静态类型）不存在，或者在不同语言之间（如对象）表现出太多的差异时，我认为它不再是标准模型的一部分。但这并不是一个价值判断：在这本书中，我们深入探讨了 SMoL，然后转向关注几个不仅重要而且美丽迷人的非“标准”特性。

转到实施方面，本书提供了另一个支柱：SImPl，即标准实现计划。这是这样的想法：编程语言可以有益地用抽象语法树来考虑；这个树通过代数数据类型得到了很好的表示；处理这个树的程序是一个主要受类型结构指导的递归函数。这种描述级别涵盖了标准评估媒体，即解释器和编译器。它还捕捉了类型检查器、类型推断、静态分析等的本质。因此，当学生们想要实现自己的语言实验时，他们应该能够熟练掌握这种结构。
