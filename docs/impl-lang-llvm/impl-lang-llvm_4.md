# JIT 和优化

# 添加 JIT 和优化器支持

欢迎来到“使用 LLVM 实现语言”教程的第四章。第 1-3 章描述了一个简单语言的实现，并添加了生成 LLVM IR 的支持。本章描述了两种新技术：为您的语言添加优化器支持和添加 JIT 编译器支持。这些补充将演示如何为 Kaleidoscope 语言获得漂亮、高效的代码。

# 4.1 无关紧要的常量折叠

我们在第三章的演示是优雅且易于扩展的。不幸的是，它并不产生出色的代码。然而，IRBuilder 在编译简单代码时确实为我们提供了明显的优化：

```
ready> def test(x) 1+2+x;
Read function definition:
define double @test(double %x) {
entry:
        %addtmp = fadd double 3.000000e+00, %x
        ret double %addtmp
} 
```

这段代码不是通过解析输入构建的 AST 的文字转录。那将是：

```
ready> def test(x) 1+2+x;
Read function definition:
define double @test(double %x) {
entry:
        %addtmp = fadd double 2.000000e+00, 1.000000e+00
        %addtmp1 = fadd double %addtmp, %x
        ret double %addtmp1
} 
```

常量折叠，如上所示，特别是一种非常常见且非常重要的优化：以至于许多语言实现者在其 AST 表示中实现常量折叠支持。

使用 LLVM，AST 中不需要这种支持。由于构建 LLVM IR 的所有调用都通过 LLVM IR 构建器进行，构建器本身在调用时会检查是否存在常量折叠的机会。如果有，它只会执行常量折叠并返回常量，而不是创建指令。

嗯，这很容易 :). 在实践中，我们建议在生成这样的代码时始终使用 IRBuilder。它在使用时没有“语法开销”（您不必在各处进行常量检查）并且在某些情况下可以显著减少生成的 LLVM IR 的数量（特别是对于具有宏预处理器或使用大量常量的语言）。

另一方面，IRBuilder 受到一个限制，即它在构建代码时会进行所有分析。如果您考虑一个稍微复杂的例子：

```
ready> def test(x) (1+2+x)*(x+(1+2));
ready> Read function definition:
define double @test(double %x) {
entry:
        %addtmp = fadd double 3.000000e+00, %x
        %addtmp1 = fadd double %x, 3.000000e+00
        %multmp = fmul double %addtmp, %addtmp1
        ret double %multmp
} 
```

在这种情况下，乘法的左手边和右手边是相同的值。我们真的希望看到这生成`tmp = x+3; result = tmp*tmp;`而不是两次计算`x+3`。

不幸的是，任何数量的局部分析都无法检测和纠正这个问题。这需要两个转换：表达式的重新关联（使 add 的词法相同）和公共子表达式消除（CSE）以删除多余的 add 指令。幸运的是，LLVM 提供了广泛的优化，您可以使用它们，以“通道”的形式。

# 4.2 LLVM 优化通道

LLVM 提供了许多优化通道，执行许多不同类型的操作并具有不同的权衡。与其他系统不同，LLVM 不坚持错误的观念，即一组优化适用于所有语言和所有情况。LLVM 允许编译器实现者完全决定使用哪些优化，以何种顺序以及在什么情况下。

作为一个具体的例子，LLVM 支持"整个模块"passes，这些 passes 会尽可能地查看尽可能大的代码体量（通常是整个文件，但如果在链接时运行，这可以是整个程序的重要部分）。它还支持和包含"每个函数"passes，这些 passes 只在单个函数上运行，而不查看其他函数。有关 passes 及其运行方式的更多信息，请参阅《如何编写 Pass》文档和 LLVM Pass 列表。

对于 Kaleidoscope，我们目前是在用户输入时即时生成函数，一次一个。在这种情况下，我们并不追求最终的优化体验，但我们也希望尽可能地捕捉到简单和快速的东西。因此，我们选择在用户输入函数时运行一些每个函数的优化。如果我们想制作一个"静态 Kaleidoscope 编译器"，我们将使用现有的代码，但会推迟运行优化器直到整个文件被解析完毕。

为了启动每个函数的优化，我们需要设置一个 FunctionPassManager 来持有和组织我们想要运行的 LLVM 优化。一旦我们有了这个，我们可以添加一组要运行的优化。代码看起来像这样：

```
FunctionPassManager OurFPM(TheModule);

// Set up the optimizer pipeline.  Start with registering info about how the
// target lays out data structures.
OurFPM.add(new DataLayout(*TheExecutionEngine->getDataLayout()));
// Provide basic AliasAnalysis support for GVN.
OurFPM.add(createBasicAliasAnalysisPass());
// Do simple "peephole" optimizations and bit-twiddling optzns.
OurFPM.add(createInstructionCombiningPass());
// Reassociate expressions.
OurFPM.add(createReassociatePass());
// Eliminate Common SubExpressions.
OurFPM.add(createGVNPass());
// Simplify the control flow graph (deleting unreachable blocks, etc).
OurFPM.add(createCFGSimplificationPass());

OurFPM.doInitialization();

// Set the global so the code gen can use this.
TheFPM = &OurFPM;

// Run the main "interpreter loop" now.
MainLoop(); 
```

此代码定义了一个 FunctionPassManager，`OurFPM`。它需要一个指向模块的指针来构建自身。一旦设置完成，我们使用一系列`add`调用来添加一堆 LLVM passes。第一个 pass 基本上是样板文件，它添加了一个 pass，以便后续优化知道程序中的数据结构是如何布局的。`TheExecutionEngine`变量与 JIT 相关，我们将在下一节中介绍。

在这种情况下，我们选择添加 4 个优化 passes。我们选择的 passes 是一组相当标准的"清理"优化，适用于各种代码。我不会深入探讨它们的作用，但请相信我，它们是一个很好的起点 :).

一旦 PassManager 设置完成，我们需要利用它。我们通过在我们新创建的函数构造之后（在`FunctionAST::Codegen`中）但在它被返回给客户端之前运行它来做到这一点：

```
if (Value *RetVal = Body->Codegen()) {
  // Finish off the function.
  Builder.CreateRet(RetVal);

  // Validate the generated code, checking for consistency.
  verifyFunction(*TheFunction);

  // Optimize the function.
  TheFPM->run(*TheFunction);

  return TheFunction;
} 
```

正如你所见，这非常简单。FunctionPassManager 在原地优化和更新 LLVM `Function*`，改善（希望是）其主体。有了这个设置，我们可以再次尝试我们上面的测试：

```
ready> def test(x) (1+2+x)*(x+(1+2));
ready> Read function definition:
define double @test(double %x) {
entry:
        %addtmp = fadd double %x, 3.000000e+00
        %multmp = fmul double %addtmp, %addtmp
        ret double %multmp
} 
```

如预期的那样，我们现在得到了我们优化后的代码，每次执行此函数都可以节省一个浮点加法指令。

LLVM 提供了各种各样的优化，在某些情况下可以使用。一些关于各种 pass 的文档是可用的，但它并不是非常完整。另一个好的思路来源是查看 Clang 运行的 passes。"opt"工具允许您从命令行实验 passes，这样您就可以看到它们是否有任何作用。

现在我们从前端得到了合理的代码，让我们谈谈如何执行它！

# 4.3 添加 JIT 编译器

可用于 LLVM IR 的代码可以应用各种各样的工具。例如，您可以对其进行优化（如上所示），可以以文本或二进制形式将其转储出来，可以将代码编译为某个目标的汇编文件（.s），或者可以对其进行 JIT 编译。LLVM IR 表示的好处是它是编译器的许多不同部分之间的“共同货币”。

在这一部分，我们将为我们的解释器添加 JIT 编译器支持。Kaleidoscope 的基本思想是让用户像现在一样输入函数体，但立即评估他们输入的顶层表达式。例如，如果他们输入 `1 + 2;`，我们应该评估并打印出 3。如果他们定义了一个函数，他们应该能够从命令行调用它。

为了做到这一点，我们首先声明并初始化 JIT。这是通过在主函数中添加一个全局变量和一个调用来完成的：

```
static ExecutionEngine *TheExecutionEngine;
...
int main() {
  ..
  // Create the JIT.  This takes ownership of the module.
  TheExecutionEngine = EngineBuilder(TheModule).create();
  ..
} 
```

这将创建一个抽象的 `Execution Engine`，它可以是 JIT 编译器或 LLVM 解释器。如果您的平台有可用的 JIT 编译器，LLVM 将自动为您选择一个 JIT 编译器，否则它将退回到解释器。

一旦创建了 ExecutionEngine，JIT 就可以使用了。有各种有用的 API，但最简单的一个是 `getPointerToFunction(F)` 方法。此方法 JIT 编译指定的 LLVM 函数并返回生成的机器代码的函数指针。在我们的情况下，这意味着我们可以将解析顶层表达式的代码更改为以下内容：

```
static void HandleTopLevelExpression() {
  // Evaluate a top-level expression into an anonymous function.
  if (FunctionAST *F = ParseTopLevelExpr()) {
    if (Function *LF = F->Codegen()) {
      LF->dump();  // Dump the function for exposition purposes.

      // JIT the function, returning a function pointer.
      void *FPtr = TheExecutionEngine->getPointerToFunction(LF);

      // Cast it to the right type (takes no arguments, returns a double) so we
      // can call it as a native function.
      double (*FP)() = (double (*)())(intptr_t)FPtr;
      fprintf(stderr, "Evaluated to %f\n", FP());
    } 
```

请回想，我们将顶层表达式编译成一个独立的 LLVM 函数，该函数不带参数并返回计算的双精度值。由于 LLVM JIT 编译器匹配本机平台 ABI，这意味着您只需将结果指针转换为该类型的函数指针并直接调用它。这意味着，JIT 编译的代码与静态链接到应用程序中的本机机器代码之间没有区别。

只需这两个更改，让我们看看现在 Kaleidoscope 的工作原理如何！

```
ready> 4+5;
Read top-level expression:
define double @0() {
entry:
  ret double 9.000000e+00
}

Evaluated to 9.000000 
```

嗯，这看起来基本上是在工作了。函数的转储显示了我们为键入的每个顶层表达式合成的“无参数函数，始终返回双精度”的函数。这展示了非常基本的功能，但我们能做得更多吗？

```
ready> def testfunc(x y) x + y*2;
Read function definition:
define double @testfunc(double %x, double %y) {
entry:
  %multmp = fmul double %y, 2.000000e+00
  %addtmp = fadd double %multmp, %x
  ret double %addtmp
}

ready> testfunc(4, 10);
Read top-level expression:
define double @1() {
entry:
  %calltmp = call double @testfunc(double 4.000000e+00, double 1.000000e+01)
  ret double %calltmp
}

Evaluated to 24.000000 
```

这说明我们现在可以调用用户代码，但这里有一些微妙的地方。请注意，我们只在调用 testfunc 的匿名函数上调用了 JIT，但我们从未在 testfunc 本身上调用它。实际上在这里发生的是，JIT 扫描了从匿名函数中传递调用的所有非 JIT 函数，并在从 `getPointerToFunction()` 返回之前将它们全部编译了。

JIT 提供了许多其他更高级的接口，用于释放分配的机器代码，重新 JIT 编译函数以更新它们等等。然而，即使是这段简单的代码，我们也获得了一些令人惊讶的强大功能 - 请看（我删除了匿名函数的转储，现在你应该明白了 :)：

```
ready> extern sin(x);
Read extern:
declare double @sin(double)

ready> extern cos(x);
Read extern:
declare double @cos(double)

ready> sin(1.0);
Read top-level expression:
define double @2() {
entry:
  ret double 0x3FEAED548F090CEE
}

Evaluated to 0.841471

ready> def foo(x) sin(x)*sin(x) + cos(x)*cos(x);
Read function definition:
define double @foo(double %x) {
entry:
  %calltmp = call double @sin(double %x)
  %multmp = fmul double %calltmp, %calltmp
  %calltmp2 = call double @cos(double %x)
  %multmp4 = fmul double %calltmp2, %calltmp2
  %addtmp = fadd double %multmp, %multmp4
  ret double %addtmp
}

ready> foo(4.0);
Read top-level expression:
define double @3() {
entry:
  %calltmp = call double @foo(double 4.000000e+00)
  ret double %calltmp
}

Evaluated to 1.000000 
```

哇，JIT 是如何知道 sin 和 cos 的呢？答案出奇的简单：在这个例子中，JIT 开始执行一个函数并到达一个函数调用。它意识到该函数尚未 JIT 编译，并调用标准的一套例程来解析该函数。在这种情况下，函数没有定义主体，因此 JIT 最终在 Kaleidoscope 进程本身上调用了 `dlsym("sin")`。由于 `sin` 在 JIT 的地址空间内定义，因此它简单地修补了模块中的调用，直接调用 libm 版本的 sin。

LLVM JIT 提供了许多接口（查看 ExecutionEngine.h 文件），用于控制如何解析未知函数。它允许您在 IR 对象和地址之间建立显式映射（例如，对于您希望映射到静态表的 LLVM 全局变量很有用），允许您基于函数名称动态地决定，在函数首次被调用时甚至允许您懒惰地 JIT 编译函数。

这样做的一个有趣应用是，我们现在可以通过编写任意的 C++ 代码来实现操作来扩展语言。例如，如果我们添加：

```
/// putchard - putchar that takes a double and returns 0.
extern "C"
double putchard(double X) {
  putchar((char)X);
  return 0;
} 
```

现在，我们可以通过使用诸如：`extern putchard(x); putchard(120);` 这样的东西来在控制台上产生简单的输出，这在控制台上打印了一个小写的 `x`（120 是 `x` 的 ASCII 码）。类似的代码可以用来实现文件 I/O、控制台输入以及 Kaleidoscope 中的许多其他功能。

这完成了 Kaleidoscope 教程的 JIT 和优化器章节。到目前为止，我们可以编译一种非图灵完备的编程语言，以用户驱动的方式优化和 JIT 编译它。接下来，我们将研究如何使用控制流构造扩展语言，并解决一些有趣的 LLVM IR 问题。
