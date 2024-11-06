# 可变变量

# 可变变量

# 第 7.1 章介绍

欢迎来到“使用 LLVM 实现语言”教程的第七章。在第 1 到第六章中，我们构建了一种非常体面但简单的函数式编程语言。在我们的旅程中，我们学习了一些解析技巧，如何构建和表示 AST，如何构建 LLVM IR，以及如何优化结果代码以及 JIT 编译它。

尽管万花筒作为一种功能性语言很有趣，但它的功能性使得为其生成 LLVM IR“太容易”了。特别是，功能性语言使得直接在 SSA 形式中构建 LLVM IR 非常容易。由于 LLVM 要求输入代码处于 SSA 形式，这是一个非常好的特性，对于新手来说，如何为带有可变变量的命令式语言生成代码通常是不清楚的。

本章的简短（和快乐）总结是，你的前端不需要构建 SSA 形式：LLVM 提供了高度调优和经过充分测试的支持，尽管它的工作方式对于一些人来说有点出乎意料。

# 第 7.2 章 为什么这是一个困难的问题？

要理解为什么可变变量会导致 SSA 构造复杂性，请考虑这个极其简单的 C 示例：

```
int G, H;
int test(_Bool Condition) {
  int X;
  if (Condition)
    X = G;
  else
    X = H;
  return X;
} 
```

在这种情况下，我们有变量 “X”，其值取决于程序中执行的路径。由于在返回指令之前 X 有两个不同的可能值，因此插入一个 PHI 节点来合并这两个值。我们希望这个示例的 LLVM IR 看起来像这样：

```
@G = weak global i32 0   ; type of @G is i32*
@H = weak global i32 0   ; type of @H is i32*

define i32 @test(i1 %Condition) {
entry:
  br i1 %Condition, label %cond_true, label %cond_false

cond_true:
  %X.0 = load i32* @G
  br label %cond_next

cond_false:
  %X.1 = load i32* @H
  br label %cond_next

cond_next:
  %X.2 = phi i32 [ %X.1, %cond_false ], [ %X.0, %cond_true ]
  ret i32 %X.2
} 
```

在这个示例中，LLVM IR 中的 G 和 H 全局变量的负载是明确的，并且它们存在于 if 语句（cond_true/cond_false）的 then/else 分支中。为了合并传入的值，在 `cond_next` 块中的 `X.2` phi 节点根据控制流来选择要使用的正确值：如果控制流来自 `cond_false` 块，则 `X.2` 得到 `X.1` 的值。或者，如果控制流来自 cond_true，则它得到 `X.0` 的值。本章的目的不是解释 SSA 形式的细节。有关更多信息，请参阅众多在线参考资料之一。

本文的问题是“在将可变变量降级为 phi 节点时，谁放置 phi 节点？” 这里的问题是 LLVM 要求其 IR 处于 SSA 形式：没有“非 SSA”模式。然而，SSA 构造需要非平凡的算法和数据结构，因此每个前端都必须重现这个逻辑是不方便和浪费的。

# 第 7.3 章 LLVM 中的内存

这里的“技巧”是，虽然 LLVM 确实要求所有的寄存器值都以 SSA 形式存在，但它不要求（或允许）内存对象以 SSA 形式存在。在上面的示例中，请注意，从 G 和 H 加载的是直接访问 G 和 H：它们没有重命名或版本化。这与一些其他编译器系统不同，它们尝试对内存对象进行版本控制。在 LLVM 中，不是将内存的数据流分析编码到 LLVM IR 中，而是通过按需计算的分析通道来处理。

有了这个想法，高层次的想法是，我们想要为函数中的每个可变对象创建一个堆栈变量（因为它位于堆栈上，所以它在内存中）。要利用这个技巧，我们需要讨论 LLVM 如何表示堆栈变量。

在 LLVM 中，所有的内存访问都是通过 load/store 指令显式进行的，并且它被精心设计为不具有（或不需要）“取地址”运算符。请注意，@G/@H 全局变量的类型实际上是“i32*”，即使变量被定义为`i32`。这意味着@G 在全局数据区域定义了一个 i32 的空间，但它的名称实际上是该空间的地址。堆栈变量的工作原理相同，只是它们不是用全局变量定义声明的，而是用 LLVM alloca 指令声明的：

```
define i32 @example() {
entry:
  %X = alloca i32           ; type of %X is i32*.
  ...
  %tmp = load i32* %X       ; load the stack value %X from the stack.
  %tmp2 = add i32 %tmp, 1   ; increment it
  store i32 %tmp2, i32* %X  ; store it back
  ... 
```

此代码展示了如何在 LLVM IR 中声明和操作堆栈变量的示例。用 alloca 指令分配的堆栈内存是完全通用的：你可以将堆栈槽的地址传递给函数，你可以将其存储在其他变量中等等。在上面的示例中，我们可以重写示例以使用 alloca 技术来避免使用 PHI 节点：

```
@G = weak global i32 0   ; type of @G is i32*
@H = weak global i32 0   ; type of @H is i32*

define i32 @test(i1 %Condition) {
entry:
  %X = alloca i32           ; type of %X is i32*.
  br i1 %Condition, label %cond_true, label %cond_false

cond_true:
  %X.0 = load i32* @G
  store i32 %X.0, i32* %X   ; Update X
  br label %cond_next

cond_false:
  %X.1 = load i32* @H
  store i32 %X.1, i32* %X   ; Update X
  br label %cond_next

cond_next:
  %X.2 = load i32* %X       ; Read X
  ret i32 %X.2
} 
```

有了这个，我们发现了一种处理任意可变变量的方法，而不需要创建 Phi 节点：

每个可变变量都变成了一个堆栈分配。每次对变量的读取都变成了从堆栈加载。每次对变量的更新都变成了对堆栈的存储。取变量的地址只是直接使用堆栈地址。虽然这个解决方案解决了我们的即时问题，但它引入了另一个问题：我们现在显然为非常简单和常见的操作引入了大量的堆栈流量，这是一个主要的性能问题。幸运的是，LLVM 优化器有一个高度调优的优化通道，名为“mem2reg”，它处理这种情况，将像这样的 alloca 提升为 SSA 寄存器，并适当插入 Phi 节点。例如，如果你通过该通道运行这个示例，你将得到：

```
$ llvm-as < example.ll | opt -mem2reg | llvm-dis
@G = weak global i32 0
@H = weak global i32 0

define i32 @test(i1 %Condition) {
entry:
  br i1 %Condition, label %cond_true, label %cond_false

cond_true:
  %X.0 = load i32* @G
  br label %cond_next

cond_false:
  %X.1 = load i32* @H
  br label %cond_next

cond_next:
  %X.01 = phi i32 [ %X.1, %cond_false ], [ %X.0, %cond_true ]
  ret i32 %X.01
} 
```

mem2reg 通道实现了标准的“迭代支配前沿”算法来构造 SSA 形式，并且有许多优化来加速（非常常见的）退化情况。mem2reg 优化通道是处理可变变量的答案，我们强烈建议您依赖它。请注意，mem2reg 仅在某些情况下适用于变量：

mem2reg 是基于 alloca 的：它查找 alloca，如果可以处理它们，就会提升它们。它不适用于全局变量或堆分配。 mem2reg 只在函数的入口块中查找 alloca 指令。在入口块中保证了 alloca 只执行一次，这使得分析更简单。 mem2reg 只提升其使用为直接加载和存储的 alloca。如果堆栈对象的地址传递给函数，或者涉及任何有趣的指针算术，那么 alloca 将不会被提升。 mem2reg 仅适用于第一类值（如指针、标量和向量）的 alloca，仅当分配的数组大小为 1（或在.ll 文件中缺失）时。 mem2reg 无法将结构体或数组提升为寄存器。请注意，“scalarrepl” pass 更强大，可以在许多情况下提升结构体、“联合体”和数组。对于大多数命令式语言来说，这些属性都很容易满足，我们将在下面用 Kaleidoscope 进行说明。您可能会问的最后一个问题是：我是否应该为我的前端费心处理这些废话？直接进行 SSA 构造，避免使用 mem2reg 优化通道不是更好吗？简而言之，我们强烈建议您使用这种技术来构建 SSA 形式，除非有极好的理由不这样做。使用这种技术是：

经过验证和经过充分测试：clang 使用这种技术来处理本地可变变量。因此，LLVM 最常见的客户端正在使用这种技术来处理大部分变量。您可以确信错误会被快速发现并及早修复。极快：mem2reg 具有许多特殊情况，使其在常见情况下快速运行以及完全通用。例如，它对仅在单个块中使用的变量、仅有一个赋值点的变量、避免插入不需要的 phi 节点的良好启发式等都有快速路径。调试信息生成所需：LLVM 中的调试信息依赖于暴露变量的地址，以便可以附加调试信息。这种技术与这种风格的调试信息非常自然地结合在一起。如果没有其他办法，这将使得启动和运行您的前端变得更加容易，并且实现起来非常简单。现在让我们在 Kaleidoscope 中扩展可变变量！

# 7.4 Kaleidoscope 中的可变变量

现在我们知道了我们要解决的问题类型，让我们看看在我们的小 Kaleidoscope 语言中是什么样子。我们将添加两个功能：

使用`=`运算符改变变量的能力。定义新变量的能力。虽然第一项才是重点，我们只有用于传入参数以及归纳变量的变量，重新定义这些变量只能走得那么远 :). 此外，定义新变量的能力是一个有用的事情，无论您是否会对它们进行变异。这里有一个激励性的例子，展示了我们如何使用这些功能：

```
# Define ':' for sequencing: as a low-precedence operator that ignores operands
# and just returns the RHS.
def binary : 1 (x y) y;

# Recursive fib, we could do this before.
def fib(x)
  if (x < 3) then
    1
  else
    fib(x-1)+fib(x-2);

# Iterative fib.
def fibi(x)
  var a = 1, b = 1, c in
  (for i = 3, i < x in
     c = a + b :
     a = b :
     b = c) :
  b;

# Call it.
fibi(10); 
```

为了变异变量，我们必须改变我们现有的变量以使用“alloca 诀窍”。一旦我们有了这个，我们将添加我们的新运算符，然后扩展 Kaleidoscope 以支持新的变量定义。

# 7.5 调整现有变量以进行变异

Kaleidoscope 中的符号表在代码生成时由 `NamedValues` 映射管理。该映射当前跟踪 LLVM `Value*`，该值保存了命名变量的 double 值。为了支持变异，我们需要稍微更改这个，使得 NamedValues 保存变量的内存位置。注意，这个改变是一种重构：它改变了代码的结构，但并不会（本身）改变编译器的行为。所有这些更改都被隔离在 Kaleidoscope 代码生成器中。

在 Kaleidoscope 的开发中的这一点上，它只支持变量用于两个事物：函数的传入参数和 `for` 循环的归纳变量。为了一致性，我们将允许这些变量以及其他用户定义的变量进行变异。这意味着这些都需要内存位置。

要开始转换我们的 Kaleidoscope，我们将更改 NamedValues 映射，使其映射到 `AllocaInst*` 而不是 `Value*`。一旦我们这样做了，C++ 编译器将告诉我们需要更新的代码部分：

```
static std::map<std::string, AllocaInst*> NamedValues; 
```

另外，由于我们需要创建这些 alloca，我们将使用一个帮助函数来确保这些 alloca 在函数的入口块中创建：

```
/// CreateEntryBlockAlloca - Create an alloca instruction in the entry block of
/// the function.  This is used for mutable variables etc.
static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction,
                                          const std::string &VarName) {
  IRBuilder<> TmpB(&TheFunction->getEntryBlock(),
                 TheFunction->getEntryBlock().begin());
  return TmpB.CreateAlloca(Type::getDoubleTy(getGlobalContext()), 0,
                           VarName.c_str());
} 
```

这段看起来有趣的代码创建了一个 IRBuilder 对象，该对象指向入口块的第一条指令（.begin()）。然后它创建一个具有预期名称的 alloca 并返回它。由于 Kaleidoscope 中的所有值都是 double，因此不需要传入类型来使用。

有了这个，我们想要做的第一个功能更改是变量引用。在我们的新方案中，变量存储在堆栈上，因此生成对它们的引用的代码实际上需要从堆栈槽加载：

```
Value *VariableExprAST::Codegen() {
  // Look this variable up in the function.
  Value *V = NamedValues[Name];
  if (V == 0) return ErrorV("Unknown variable name");

  // Load the value.
  return Builder.CreateLoad(V, Name.c_str());
} 
```

正如您所看到的，这非常简单。现在我们需要更新定义变量的东西以设置 alloca。我们将从 ForExprAST::Codegen 开始（请参阅完整的代码列表以获取未删减的代码）：

```
Function *TheFunction = Builder.GetInsertBlock()->getParent();

// Create an alloca for the variable in the entry block.
AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, VarName);

  // Emit the start code first, without 'variable' in scope.
Value *StartVal = Start->Codegen();
if (StartVal == 0) return 0;

// Store the value into the alloca.
Builder.CreateStore(StartVal, Alloca);
...

// Compute the end condition.
Value *EndCond = End->Codegen();
if (EndCond == 0) return EndCond;

// Reload, increment, and restore the alloca.  This handles the case where
// the body of the loop mutates the variable.
Value *CurVar = Builder.CreateLoad(Alloca);
Value *NextVar = Builder.CreateFAdd(CurVar, StepVal, "nextvar");
Builder.CreateStore(NextVar, Alloca);
... 
```

这段代码与允许可变变量之前的代码几乎相同。最大的区别是我们不再需要构造 PHI 节点，而是根据需要使用 load/store 访问变量。

为了支持可变参数变量，我们还需要为它们创建 allocas。这部分代码也相当简单：

```
/// CreateArgumentAllocas - Create an alloca for each argument and register the
/// argument in the symbol table so that references to it will succeed.
void PrototypeAST::CreateArgumentAllocas(Function *F) {
  Function::arg_iterator AI = F->arg_begin();
  for (unsigned Idx = 0, e = Args.size(); Idx != e; ++Idx, ++AI) {
    // Create an alloca for this variable.
    AllocaInst *Alloca = CreateEntryBlockAlloca(F, Args[Idx]);

    // Store the initial value into the alloca.
    Builder.CreateStore(AI, Alloca);

    // Add arguments to variable symbol table.
    NamedValues[Args[Idx]] = Alloca;
  }
} 
```

对于每个参数，我们都会创建一个 alloca，将函数的输入值存储到 alloca 中，并将 alloca 注册为参数的内存位置。此方法由 FunctionAST::Codegen 在为函数设置入口块后立即调用。

最后缺失的部分是添加 mem2reg 传递，这样我们就可以再次获得良好的代码生成：

```
// Set up the optimizer pipeline.  Start with registering info about how the
// target lays out data structures.
OurFPM.add(new DataLayout(*TheExecutionEngine->getDataLayout()));
// Promote allocas to registers.
OurFPM.add(createPromoteMemoryToRegisterPass());
// Do simple "peephole" optimizations and bit-twiddling optzns.
OurFPM.add(createInstructionCombiningPass());
// Reassociate expressions.
OurFPM.add(createReassociatePass());
It is interesting to see what the code looks like before and after the mem2reg optimization runs. For example, this is the before/after code for our recursive fib function. Before the optimization:

define double @fib(double %x) {
entry:
  %x1 = alloca double
  store double %x, double* %x1
  %x2 = load double* %x1
  %cmptmp = fcmp ult double %x2, 3.000000e+00
  %booltmp = uitofp i1 %cmptmp to double
  %ifcond = fcmp one double %booltmp, 0.000000e+00
  br i1 %ifcond, label %then, label %else

then:       ; preds = %entry
  br label %ifcont

else:       ; preds = %entry
  %x3 = load double* %x1
  %subtmp = fsub double %x3, 1.000000e+00
  %calltmp = call double @fib(double %subtmp)
  %x4 = load double* %x1
  %subtmp5 = fsub double %x4, 2.000000e+00
  %calltmp6 = call double @fib(double %subtmp5)
  %addtmp = fadd double %calltmp, %calltmp6
  br label %ifcont

ifcont:     ; preds = %else, %then
  %iftmp = phi double [ 1.000000e+00, %then ], [ %addtmp, %else ]
  ret double %iftmp
} 
```

这里只有一个变量（输入参数 x），但您仍然可以看到我们正在使用的极端简单的代码生成策略。在入口块中，创建一个 alloca，并将初始输入值存储到其中。对变量的每个引用都从堆栈重新加载。另外，请注意，我们没有修改 if/then/else 表达式，所以它仍然插入 PHI 节点。虽然我们可以为它创建一个 alloca，但实际上为它创建一个 PHI 节点更容易，所以我们仍然只是创建 PHI。

在 mem2reg pass 运行后的代码如下：

```
define double @fib(double %x) {
entry:
  %cmptmp = fcmp ult double %x, 3.000000e+00
  %booltmp = uitofp i1 %cmptmp to double
  %ifcond = fcmp one double %booltmp, 0.000000e+00
  br i1 %ifcond, label %then, label %else

then:
  br label %ifcont

else:
  %subtmp = fsub double %x, 1.000000e+00
  %calltmp = call double @fib(double %subtmp)
  %subtmp5 = fsub double %x, 2.000000e+00
  %calltmp6 = call double @fib(double %subtmp5)
  %addtmp = fadd double %calltmp, %calltmp6
  br label %ifcont

ifcont:     ; preds = %else, %then
  %iftmp = phi double [ 1.000000e+00, %then ], [ %addtmp, %else ]
  ret double %iftmp
} 
```

对于 mem2reg 来说，这是一个微不足道的案例，因为没有对变量的重新定义。展示这个案例的目的是为了缓解您关于插入这种明显的低效的紧张情绪 :）。

在其余的优化器运行之后，我们得到了：

```
define double @fib(double %x) {
entry:
  %cmptmp = fcmp ult double %x, 3.000000e+00
  %booltmp = uitofp i1 %cmptmp to double
  %ifcond = fcmp ueq double %booltmp, 0.000000e+00
  br i1 %ifcond, label %else, label %ifcont

else:
  %subtmp = fsub double %x, 1.000000e+00
  %calltmp = call double @fib(double %subtmp)
  %subtmp5 = fsub double %x, 2.000000e+00
  %calltmp6 = call double @fib(double %subtmp5)
  %addtmp = fadd double %calltmp, %calltmp6
  ret double %addtmp

ifcont:
  ret double 1.000000e+00
} 
```

在这里，我们看到 simplifycfg pass 决定将返回指令克隆到`else`块的末尾。这使得它能够消除一些分支和 PHI 节点。

现在，所有符号表引用都已更新为使用堆栈变量，我们将添加赋值运算符。

# 7.6 新的赋值运算符

使用我们当前的框架，添加一个新的赋值运算符非常简单。我们将它解析就像任何其他二元运算符一样，但在内部处理它（而不是允许用户定义它）。第一步是设置优先级：

```
int main() {
  // Install standard binary operators.
  // 1 is lowest precedence.
  BinopPrecedence['='] = 2;
  BinopPrecedence['<'] = 10;
  BinopPrecedence['+'] = 20;
  BinopPrecedence['-'] = 20; 
```

现在解析器知道了二元运算符的优先级，它会处理所有解析和 AST 生成。我们只需要为赋值运算符实现代码生成。代码如下所示：

```
Value *BinaryExprAST::Codegen() {
  // Special case '=' because we don't want to emit the LHS as an expression.
  if (Op == '=') {
    // Assignment requires the LHS to be an identifier.
    VariableExprAST *LHSE = dynamic_cast<VariableExprAST*>(LHS);
    if (!LHSE)
      return ErrorV("destination of '=' must be a variable"); 
```

与其他二元运算符不同，我们的赋值运算符不遵循“发出 LHS，发出 RHS，进行计算”的模式。因此，它在处理其他二元运算符之前作为特例处理。另一件奇怪的事情是它要求 LHS 是一个变量。像“(x+1) = expr”这样的表达式是无效的——只有像“x = expr”这样的东西是允许的。

```
 // Codegen the RHS.
  Value *Val = RHS->Codegen();
  if (Val == 0) return 0;

  // Look up the name.
  Value *Variable = NamedValues[LHSE->getName()];
  if (Variable == 0) return ErrorV("Unknown variable name");

  Builder.CreateStore(Val, Variable);
  return Val;
}
... 
```

一旦我们有了变量，生成赋值代码就很简单了：我们发出赋值的 RHS，创建一个存储，然后返回计算出的值。返回一个值允许像`X = (Y = Z)`这样的链式赋值。

现在我们有了一个赋值运算符，我们可以改变循环变量和参数。例如，我们现在可以运行这样的代码：

```
# Function to print a double.
extern printd(x);

# Define ':' for sequencing: as a low-precedence operator that ignores operands
# and just returns the RHS.
def binary : 1 (x y) y;

def test(x)
  printd(x) :
  x = 4 :
  printd(x);

test(123); 
```

运行时，这个示例打印“123”，然后“4”，显示我们确实改变了值！好的，我们现在正式实现了我们的目标：在一般情况下，使 SSA 构造工作需要一定的努力。然而，为了真正有用，我们希望能够定义自己的局部变量，让我们下一步添加这个！

# 7.7 用户定义的局部变量

添加 var/in 与我们向 Kaleidoscope 添加的任何其他扩展一样简单：我们扩展了词法分析器、解析器、AST 和代码生成器。为了添加我们的新‘var/in’结构，首先要扩展词法分析器。与以前一样，这相当琐碎，代码如下所示：

```
enum Token {
  ...
  // var definition
  tok_var = -13
...
}
...
static int gettok() {
...
    if (IdentifierStr == "in") return tok_in;
    if (IdentifierStr == "binary") return tok_binary;
    if (IdentifierStr == "unary") return tok_unary;
    if (IdentifierStr == "var") return tok_var;
    return tok_identifier;
... 
```

下一步是定义我们将构造的 AST 节点。对于 var/in，它看起来像这样：

```
/// VarExprAST - Expression class for var/in
class VarExprAST : public ExprAST {
  std::vector<std::pair<std::string, ExprAST*> > VarNames;
  ExprAST *Body;
public:
  VarExprAST(const std::vector<std::pair<std::string, ExprAST*> > &varnames,
             ExprAST *body)
  : VarNames(varnames), Body(body) {}

  virtual Value *Codegen();
}; 
```

var/in 允许一次性定义一个名称列表，并且每个名称可以选择性地具有初始化值。因此，我们将这些信息捕捉在 VarNames 向量中。此外，var/in 有一个主体，这个主体可以访问 var/in 定义的变量。

有了这个基础，我们可以定义解析器的部分。我们首先将其添加为主表达式：

```
/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
///   ::= ifexpr
///   ::= forexpr
///   ::= varexpr
static ExprAST *ParsePrimary() {
  switch (CurTok) {
  default: return Error("unknown token when expecting an expression");
  case tok_identifier: return ParseIdentifierExpr();
  case tok_number:     return ParseNumberExpr();
  case '(':            return ParseParenExpr();
  case tok_if:         return ParseIfExpr();
  case tok_for:        return ParseForExpr();
  case tok_var:        return ParseVarExpr();
  }
} 
```

接下来我们定义 ParseVarExpr：

```
/// varexpr ::= 'var' identifier ('=' expression)?
//                    (',' identifier ('=' expression)?)* 'in' expression
static ExprAST *ParseVarExpr() {
  getNextToken();  // eat the var.

  std::vector<std::pair<std::string, ExprAST*> > VarNames;

  // At least one variable name is required.
  if (CurTok != tok_identifier)
    return Error("expected identifier after var");
The first part of this code parses the list of identifier/expr pairs into the local VarNames vector.

while (1) {
  std::string Name = IdentifierStr;
  getNextToken();  // eat identifier.

  // Read the optional initializer.
  ExprAST *Init = 0;
  if (CurTok == '=') {
    getNextToken(); // eat the '='.

    Init = ParseExpression();
    if (Init == 0) return 0;
  }

  VarNames.push_back(std::make_pair(Name, Init));

  // End of var list, exit loop.
  if (CurTok != ',') break;
  getNextToken(); // eat the ','.

  if (CurTok != tok_identifier)
    return Error("expected identifier list after var");
} 
```

一旦所有变量都被解析，我们然后解析主体并创建 AST 节点：

```
 // At this point, we have to have 'in'.
  if (CurTok != tok_in)
    return Error("expected 'in' keyword after 'var'");
  getNextToken();  // eat 'in'.

  ExprAST *Body = ParseExpression();
  if (Body == 0) return 0;

  return new VarExprAST(VarNames, Body);
} 
```

现在我们可以解析和表示代码，我们需要支持为其发出 LLVM IR。这段代码从以下内容开始：

```
Value *VarExprAST::Codegen() {
  std::vector<AllocaInst *> OldBindings;

  Function *TheFunction = Builder.GetInsertBlock()->getParent();

  // Register all variables and emit their initializer.
  for (unsigned i = 0, e = VarNames.size(); i != e; ++i) {
    const std::string &VarName = VarNames[i].first;
    ExprAST *Init = VarNames[i].second; 
```

基本上，它循环遍历所有变量，逐个安装它们。对于放入符号表的每个变量，我们记住要替换的上一个值，放入 OldBindings 中。

```
 // Emit the initializer before adding the variable to scope, this prevents
  // the initializer from referencing the variable itself, and permits stuff
  // like this:
  //  var a = 1 in
  //    var a = a in ...   # refers to outer 'a'.
  Value *InitVal;
  if (Init) {
    InitVal = Init->Codegen();
    if (InitVal == 0) return 0;
  } else { // If not specified, use 0.0.
    InitVal = ConstantFP::get(getGlobalContext(), APFloat(0.0));
  }

  AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, VarName);
  Builder.CreateStore(InitVal, Alloca);

  // Remember the old variable binding so that we can restore the binding when
  // we unrecurse.
  OldBindings.push_back(NamedValues[VarName]);

  // Remember this binding.
  NamedValues[VarName] = Alloca;
} 
```

这里的注释比代码还多。基本思想是我们发出初始化器，创建 alloca，然后更新符号表指向它。一旦所有变量都安装在符号表中，我们评估 var/in 表达式的主体：

```
// Codegen the body, now that all vars are in scope.
Value *BodyVal = Body->Codegen();
if (BodyVal == 0) return 0;
Finally, before returning, we restore the previous variable bindings:

  // Pop all our variables from scope.
  for (unsigned i = 0, e = VarNames.size(); i != e; ++i)
    NamedValues[VarNames[i].first] = OldBindings[i];

  // Return the body computation.
  return BodyVal;
} 
```

所有这些的最终结果是，我们得到了正确作用域的变量定义，甚至（微不足道地）允许对它们进行变异 :).

有了这个，我们完成了我们的目标。我们在介绍中漂亮的迭代 fib 示例编译并运行得很好。mem2reg 优化了我们所有的栈变量为 SSA 寄存器，根据需要插入 PHI 节点，我们的前端保持简单：没有“迭代支配前沿”计算。
