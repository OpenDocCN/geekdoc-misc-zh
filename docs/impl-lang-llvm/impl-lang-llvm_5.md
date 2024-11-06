# 控制流

# 控制流

欢迎来到"使用 LLVM 实现语言"教程的第五章。第 1-4 部分描述了简单的万花筒语言的实现，并包括生成 LLVM IR 的支持，随后是优化和 JIT 编译器。不幸的是，按照目前的形式，万花筒语言几乎没什么用处：除了调用和返回之外，它没有任何控制流。这意味着你不能在代码中使用条件分支，从而极大地限制了它的功能。在本集的"构建编译器"中，我们将扩展万花筒语言，使其具有 if/then/else 表达式和一个简单的`for`循环。

# 5.1 如果/那么/否则

扩展万花筒以支持 if/then/else 非常简单。基本上需要将对这个"新"概念的支持添加到词法分析器、解析器、AST 和 LLVM 代码发射器中。这个例子很好，因为它展示了如何随着时间的推移"增长"一种语言，逐步扩展它，发现新思想时逐渐扩展它。

在我们开始"如何"添加这个扩展之前，让我们谈谈我们想要的"什么"。基本想法是我们想要能够写出这样的东西：

```
def fib(x)
  if x < 3 then
    1
  else
    fib(x-1)+fib(x-2); 
```

在万花筒中，每个构造都是一个表达式：没有语句。因此，if/then/else 表达式需要像其他任何表达式一样返回一个值。由于我们使用的是大多数函数形式，我们将使其评估其条件，然后根据条件的解析方式返回`then`或`else`值。这与 C 中的"？:"表达式非常相似。

如果/那么/否则表达式的语义是将条件评估为布尔相等值：0.0 被视为 false，其他任何值都被视为 true。如果条件为 true，则评估并返回第一个子表达式，如果条件为 false，则评估并返回第二个子表达式。由于万花筒允许副作用，这种行为非常重要。

现在我们知道我们"想要"什么，让我们把它分解成其组成部分。

# 5.1.1 对于 If/Then/Else 的词法分析器扩展

词法分析器的扩展很简单。首先我们为相关的标记添加新的枚举值：

```
// control
tok_if = -6, tok_then = -7, tok_else = -8,
Once we have that, we recognize the new keywords in the lexer. This is pretty simple stuff:

...
if (IdentifierStr == "def") return tok_def;
if (IdentifierStr == "extern") return tok_extern;
if (IdentifierStr == "if") return tok_if;
if (IdentifierStr == "then") return tok_then;
if (IdentifierStr == "else") return tok_else;
return tok_identifier; 
```

# 5.1.2 If/Then/Else 的 AST 扩展

为了表示新的表达式，我们添加了一个新的 AST 节点：

```
/// IfExprAST - Expression class for if/then/else.
class IfExprAST : public ExprAST {
  ExprAST *Cond, *Then, *Else;
public:
  IfExprAST(ExprAST *cond, ExprAST *then, ExprAST *_else)
    : Cond(cond), Then(then), Else(_else) {}
  virtual Value *Codegen();
}; 
```

AST 节点只是指向各种子表达式的指针。

# 5.1.3 对于 If/Then/Else 的解析器扩展

现在我们从词法分析器获得了相关的标记，我们有了要构建的 AST 节点，我们的解析逻辑相对简单。首先我们定义一个新的解析函数：

```
/// ifexpr ::= 'if' expression 'then' expression 'else' expression
static ExprAST *ParseIfExpr() {
  getNextToken();  // eat the if.

  // condition.
  ExprAST *Cond = ParseExpression();
  if (!Cond) return 0;

  if (CurTok != tok_then)
    return Error("expected then");
  getNextToken();  // eat the then

  ExprAST *Then = ParseExpression();
  if (Then == 0) return 0;

  if (CurTok != tok_else)
    return Error("expected else");

  getNextToken();

  ExprAST *Else = ParseExpression();
  if (!Else) return 0;

  return new IfExprAST(Cond, Then, Else);
} 
```

接下来我们将其连接为一个主要的表达式：

```
static ExprAST *ParsePrimary() {
  switch (CurTok) {
  default: return Error("unknown token when expecting an expression");
  case tok_identifier: return ParseIdentifierExpr();
  case tok_number:     return ParseNumberExpr();
  case '(':            return ParseParenExpr();
  case tok_if:         return ParseIfExpr();
  }
} 
```

# 5.1.4 If/Then/Else 的 LLVM IR

现在我们已经对其进行了解析并构建了 AST，最后一步是添加 LLVM 代码生成支持。这是 if/then/else 示例中最有趣的部分，因为这是它开始引入新概念的地方。以上所有代码在前几章中都已经详细描述过了。

为了激励我们想要生成的代码，让我们看一个简单的例子。考虑：

```
extern foo();
extern bar();
def baz(x) if x then foo() else bar();
If you disable optimizations, the code you'll (soon) get from Kaleidoscope looks like this:

declare double @foo()

declare double @bar()

define double @baz(double %x) {
entry:
  %ifcond = fcmp one double %x, 0.000000e+00
  br i1 %ifcond, label %then, label %else

then:       ; preds = %entry
  %calltmp = call double @foo()
  br label %ifcont

else:       ; preds = %entry
  %calltmp1 = call double @bar()
  br label %ifcont

ifcont:     ; preds = %else, %then
  %iftmp = phi double [ %calltmp, %then ], [ %calltmp1, %else ]
  ret double %iftmp
} 
```

要可视化控制流图，你可以使用 LLVM 'opt'工具的一个很好的功能。如果你将这个 LLVM IR 放入“t.ll”并运行 `llvm-as < t.ll | opt -analyze -view-cfg`，一个窗口将弹出，你将看到这个图：

示例 CFG

![cfg](img/cfg.png)

示例 CFG

另一种获取这个的方法是调用 `F->viewCFG()` 或 `F->viewCFGOnly()`（其中 F 是 `Function*`），可以通过在代码中插入实际调用并重新编译，或者在调试器中调用这些来实现。LLVM 有许多很好的功能来可视化各种图形。

回到生成的代码，很简单：入口块评估条件表达式（在我们这里是 `x`）并将结果与 `fcmp one` 指令中的 0.0 进行比较（'one' 是 "有序且不等于"）。根据此表达式的结果，代码跳转到 `then` 或 `else` 块，其中包含真/假情况的表达式。

一旦 then/else 块执行完毕，它们都会跳转回 `ifcont` 块以执行 if/then/else 之后发生的代码。在这种情况下，唯一要做的就是返回给函数的调用者。然后问题就变成了：代码如何知道返回哪个表达式？

这个问题的答案涉及一个重要的 SSA 操作：Phi 操作。如果你不熟悉 SSA，请查看维基百科文章，这是一个很好的介绍，你的最爱搜索引擎上还有各种其他介绍。简短版是，“执行”Phi 操作需要“记住”控制来自哪个块。Phi 操作接受与输入控制块相对应的值。在这种情况下，如果控制来自`then`块，则获取`calltmp`的值。如果控制来自`else`块，则获取`calltmp1`的值。

此时，你可能开始思考“哦不！这意味着我的简单而优雅的前端将不得不开始生成 SSA 形式以使用 LLVM！”。幸运的是，情况并非如此，我们强烈建议在你的前端中不要实现 SSA 构造算法，除非有一个非常好的理由这样做。在实践中，有两种在为您的普通命令式编程语言编写的代码中流动的值可能需要 Phi 节点：

涉及用户变量的代码：

+   x = 1; x = x + 1;

+   在你的 AST 结构中隐含的值，例如本例中的 Phi 节点。

在本教程的第七章（"可变变量"）中，我们将深入讨论#1。现在，只需相信我，你不需要 SSA 构造来处理这种情况。对于#2，你可以选择使用我们将为#1 描述的技术，或者如果方便的话，直接插入 Phi 节点。在这种情况下，生成 Phi 节点非常容易，所以我们选择直接生成。

好了，足够的动机和概述了，让我们生成代码吧！

# 5.1.5 If/Then/Else 的代码生成

为了生成这个代码，我们为 IfExprAST 实现了 Codegen 方法：

```
Value *IfExprAST::Codegen() {
  Value *CondV = Cond->Codegen();
  if (CondV == 0) return 0;

  // Convert condition to a bool by comparing equal to 0.0.
  CondV = Builder.CreateFCmpONE(CondV,
                              ConstantFP::get(getGlobalContext(), APFloat(0.0)),
                                "ifcond");
This code is straightforward and similar to what we saw before. We emit the expression for the condition, then compare that value to zero to get a truth value as a 1-bit (bool) value.

Function *TheFunction = Builder.GetInsertBlock()->getParent();

// Create blocks for the then and else cases.  Insert the 'then' block at the
// end of the function.
BasicBlock *ThenBB = BasicBlock::Create(getGlobalContext(), "then", TheFunction);
BasicBlock *ElseBB = BasicBlock::Create(getGlobalContext(), "else");
BasicBlock *MergeBB = BasicBlock::Create(getGlobalContext(), "ifcont");

Builder.CreateCondBr(CondV, ThenBB, ElseBB); 
```

这段代码创建了与 if/then/else 语句相关的基本块，并直接对应上面示例中的块。第一行获取当前正在构建的 Function 对象。它通过向构建器请求当前的 BasicBlock，并向该块请求其“父级”（当前嵌入的函数）来获取这个。

一旦有了这个，它就创建了三个块。请注意，它将“TheFunction”传递给`then`块的构造函数。这会导致构造函数自动将新块插入到指定函数的末尾。另外两个块已经创建，但尚未插入到函数中。

创建了这些块后，我们可以发出选择它们之间的条件分支。请注意，创建新块不会隐式影响 IRBuilder，因此它仍然插入到条件进入的块中。还要注意，它正在创建一个分支到`then`块和`else`块，即使`else`块尚未插入到函数中。这都没问题：这是 LLVM 支持前向引用的标准方式。

```
// Emit then value.
Builder.SetInsertPoint(ThenBB);

Value *ThenV = Then->Codegen();
if (ThenV == 0) return 0;

Builder.CreateBr(MergeBB);
// Codegen of 'Then' can change the current block, update ThenBB for the PHI.
ThenBB = Builder.GetInsertBlock(); 
```

插入条件分支后，我们将构建器移动到开始插入`then`块。严格来说，这个调用将插入点移动到指定块的末尾。但是，由于`then`块为空，它也从该块的开头开始插入。 :)

一旦插入点设置好了，我们就递归地从 AST 代码生成`then`表达式。为了完成`then`块，我们创建了一个无条件分支到合并块。LLVM IR 的一个有趣（也非常重要）的方面是，它要求所有的基本块都必须用控制流指令（如 return 或 branch）“终止”。这意味着所有的控制流，包括跨越，都必须在 LLVM IR 中明确指定。如果违反了这个规则，验证器将发出错误。

这里的最后一行非常微妙，但非常重要。基本问题是，当我们在合并块中创建 Phi 节点时，我们需要设置指示 Phi 如何工作的块/值对。重要的是，Phi 节点期望在 CFG 的块的每个前任中都有一个条目。那么，我们为什么在刚刚将其设置为 ThenBB 的当前块时获取当前块？问题是，如果`then`表达式实际上更改了 Builder 正在发出的块，例如，如果它包含嵌套的“if/then/else”表达式。因为递归调用 Codegen 可能会任意更改当前块的概念，我们需要获取一个用于设置 Phi 节点的代码的最新值。

```
// Emit else block.
TheFunction->getBasicBlockList().push_back(ElseBB);
Builder.SetInsertPoint(ElseBB);

Value *ElseV = Else->Codegen();
if (ElseV == 0) return 0;

Builder.CreateBr(MergeBB);
// Codegen of 'Else' can change the current block, update ElseBB for the PHI.
ElseBB = Builder.GetInsertBlock();
Code generation for the 'else' block is basically identical to codegen for the 'then' block. The only significant difference is the first line, which adds the 'else' block to the function. Recall previously that the 'else' block was created, but not added to the function. Now that the 'then' and 'else' blocks are emitted, we can finish up with the merge code:

  // Emit merge block.
  TheFunction->getBasicBlockList().push_back(MergeBB);
  Builder.SetInsertPoint(MergeBB);
  PHINode *PN = Builder.CreatePHI(Type::getDoubleTy(getGlobalContext()), 2,
                                  "iftmp");

  PN->addIncoming(ThenV, ThenBB);
  PN->addIncoming(ElseV, ElseBB);
  return PN;
} 
```

这里的前两行现在很熟悉：第一行将“merge”块添加到 Function 对象中（它之前是浮动的，就像上面的 else 块一样）。第二个块更改了插入点，使新创建的代码将进入“merge”块。一旦完成了这一点，我们需要创建 PHI 节点并为 PHI 设置块/值对。

最后，CodeGen 函数将 phi 节点作为 if/then/else 表达式计算的值返回。在我们上面的例子中，这个返回值将进入顶层函数的代码中，该代码将创建返回指令。

总的来说，我们现在可以在 Kaleidoscope 中执行条件代码了。通过这个扩展，Kaleidoscope 是一种相当完整的语言，可以计算各种各样的数值函数。接下来，我们将添加另一个从非函数式语言中熟悉的有用表达式...

# 5.2 `for`循环表达式

现在我们知道如何将基本的控制流构造添加到语言中，我们有了添加更强大功能的工具。让我们添加一些更具攻击性的东西，一个`for`表达式：

```
extern putchard(char)
def printstar(n)
  for i = 1, i < n, 1.0 in
    putchard(42);  # ascii 42 = '*'

# print 100 '*' characters
printstar(100); 
```

此表达式定义了一个新变量（在本例中为`i`），它从一个起始值迭代，当条件（在本例中为`i < n`）为真时，按照一个可选的步长值（在本例中为`1.0`）递增。如果省略了步长值，则默认为`1.0`。在循环为真时，它执行其主体表达式。因为我们没有更好的返回值，所以我们将定义循环始终返回`0.0`。将来当我们有了可变变量时，它将变得更有用。

与之前一样，让我们谈谈我们需要对 Kaleidoscope 进行的更改。

# 5.2.1 `for`循环的词法分析器扩展

词法分析器扩展与 if/then/else 的情况类似：

```
... in enum Token ...
// control
tok_if = -6, tok_then = -7, tok_else = -8,
tok_for = -9, tok_in = -10

... in gettok ...
if (IdentifierStr == "def") return tok_def;
if (IdentifierStr == "extern") return tok_extern;
if (IdentifierStr == "if") return tok_if;
if (IdentifierStr == "then") return tok_then;
if (IdentifierStr == "else") return tok_else;
if (IdentifierStr == "for") return tok_for;
if (IdentifierStr == "in") return tok_in;
return tok_identifier; 
```

# 5.2.2 `for`循环的 AST 扩展

AST 节点同样简单。它基本上归结为在节点中捕获变量名和组成表达式。

```
/// ForExprAST - Expression class for for/in.
class ForExprAST : public ExprAST {
  std::string VarName;
  ExprAST *Start, *End, *Step, *Body;
public:
  ForExprAST(const std::string &varname, ExprAST *start, ExprAST *end,
             ExprAST *step, ExprAST *body)
    : VarName(varname), Start(start), End(end), Step(step), Body(body) {}
  virtual Value *Codegen();
}; 
```

# 5.2.3 `for`循环的解析器扩展

解析器代码也是相当标准的。这里唯一有趣的事情是处理可选的步长值。解析器代码通过检查第二个逗号是否存在来处理它。如果不存在，则将步长值设置为 AST 节点中的 null：

```
/// forexpr ::= 'for' identifier '=' expr ',' expr (',' expr)? 'in' expression
static ExprAST *ParseForExpr() {
  getNextToken();  // eat the for.

  if (CurTok != tok_identifier)
    return Error("expected identifier after for");

  std::string IdName = IdentifierStr;
  getNextToken();  // eat identifier.

  if (CurTok != '=')
    return Error("expected '=' after for");
  getNextToken();  // eat '='.

  ExprAST *Start = ParseExpression();
  if (Start == 0) return 0;
  if (CurTok != ',')
    return Error("expected ',' after for start value");
  getNextToken();

  ExprAST *End = ParseExpression();
  if (End == 0) return 0;

  // The step value is optional.
  ExprAST *Step = 0;
  if (CurTok == ',') {
    getNextToken();
    Step = ParseExpression();
    if (Step == 0) return 0;
  }

  if (CurTok != tok_in)
    return Error("expected 'in' after for");
  getNextToken();  // eat 'in'.

  ExprAST *Body = ParseExpression();
  if (Body == 0) return 0;

  return new ForExprAST(IdName, Start, End, Step, Body);
} 
```

# 5.2.4 `for`循环的 LLVM IR

现在我们来到了好部分：我们想要为这个东西生成的 LLVM IR。对于上面的简单示例，我们得到了这个 LLVM IR（请注意，这个转储是为了清晰起见而生成的，因此已禁用了优化）：

```
declare double @putchard(double)

define double @printstar(double %n) {
entry:
  ; initial value = 1.0 (inlined into phi)
  br label %loop

loop:       ; preds = %loop, %entry
  %i = phi double [ 1.000000e+00, %entry ], [ %nextvar, %loop ]
  ; body
  %calltmp = call double @putchard(double 4.200000e+01)
  ; increment
  %nextvar = fadd double %i, 1.000000e+00

  ; termination test
  %cmptmp = fcmp ult double %i, %n
  %booltmp = uitofp i1 %cmptmp to double
  %loopcond = fcmp one double %booltmp, 0.000000e+00
  br i1 %loopcond, label %loop, label %afterloop

afterloop:      ; preds = %loop
  ; loop always returns 0.0
  ret double 0.000000e+00
} 
```

这个循环包含了我们之前看到的所有结构：一个 phi 节点，几个表达式和一些基本块。让我们看看这是如何组合在一起的。

# 5.2.5 `for`循环的代码生成

Codegen 的第一部分非常简单：我们只输出循环值的起始表达式：

```
Value *ForExprAST::Codegen() {
  // Emit the start code first, without 'variable' in scope.
  Value *StartVal = Start->Codegen();
  if (StartVal == 0) return 0; 
```

解决了这个问题之后，下一步是为循环体的开始设置 LLVM 基本块。在上面的情况中，整个循环体是一个块，但请记住，循环体代码本身可能由多个块组成（例如，如果它包含 if/then/else 或 for/in 表达式）。

```
// Make the new basic block for the loop header, inserting after current
// block.
Function *TheFunction = Builder.GetInsertBlock()->getParent();
BasicBlock *PreheaderBB = Builder.GetInsertBlock();
BasicBlock *LoopBB = BasicBlock::Create(getGlobalContext(), "loop", TheFunction);

// Insert an explicit fall through from the current block to the LoopBB.
Builder.CreateBr(LoopBB); 
```

这段代码与我们在 if/then/else 中看到的类似。因为我们将需要它来创建 Phi 节点，所以我们记住了掉入循环的块。一旦我们有了这个，我们就创建了实际开始循环的块，并为两个块之间的掉落创建了一个无条件分支。

```
// Start insertion in LoopBB.
Builder.SetInsertPoint(LoopBB);

// Start the PHI node with an entry for Start.
PHINode *Variable = Builder.CreatePHI(Type::getDoubleTy(getGlobalContext()), 2, VarName.c_str());
Variable->addIncoming(StartVal, PreheaderBB); 
```

现在循环的“前导块”已经设置好，我们切换到为循环体生成代码。首先，我们移动插入点并为循环归纳变量创建 PHI 节点。由于我们已经知道起始值的传入值，我们将其添加到 Phi 节点中。请注意，Phi 最终将获得第二个值用于回边，但我们目前无法设置它（因为它还不存在！）。

```
// Within the loop, the variable is defined equal to the PHI node.  If it
// shadows an existing variable, we have to restore it, so save it now.
Value *OldVal = NamedValues[VarName];
NamedValues[VarName] = Variable;

// Emit the body of the loop.  This, like any other expr, can change the
// current BB.  Note that we ignore the value computed by the body, but don't
// allow an error.
if (Body->Codegen() == 0)
  return 0; 
```

现在代码开始变得更有趣了。我们的'for'循环向符号表引入了一个新变量。这意味着我们的符号表现在可以包含函数参数或循环变量。为了处理这个问题，在我们生成循环体之前，我们将循环变量添加为其名称的当前值。请注意，外部作用域可能存在同名变量。将其视为错误（如果 VarName 已经有条目，则发出错误并返回 null）很容易，但我们选择允许变量的遮蔽。为了正确处理这一点，我们记住了我们潜在遮蔽的值 OldVal（如果没有遮蔽变量，则为 null）。

一旦循环变量设置到符号表中，代码就会递归地生成循环体。这使得循环体可以使用循环变量：对它的任何引用都会自然地在符号表中找到它。

```
// Emit the step value.
Value *StepVal;
if (Step) {
  StepVal = Step->Codegen();
  if (StepVal == 0) return 0;
} else {
  // If not specified, use 1.0.
  StepVal = ConstantFP::get(getGlobalContext(), APFloat(1.0));
}

Value *NextVar = Builder.CreateFAdd(Variable, StepVal, "nextvar"); 
```

现在循环体已经生成，我们通过添加步长值或者如果不存在则为 1.0 来计算迭代变量的下一个值。`NextVar`将是循环变量在循环的下一次迭代中的值。

```
// Compute the end condition.
Value *EndCond = End->Codegen();
if (EndCond == 0) return EndCond;

// Convert condition to a bool by comparing equal to 0.0.
EndCond = Builder.CreateFCmpONE(EndCond,
                            ConstantFP::get(getGlobalContext(), APFloat(0.0)),
                                "loopcond"); 
```

最后，我们评估循环的退出值，以确定循环是否应该退出。这与 if/then/else 语句的条件评估相似。

```
// Create the "after loop" block and insert it.
BasicBlock *LoopEndBB = Builder.GetInsertBlock();
BasicBlock *AfterBB = BasicBlock::Create(getGlobalContext(), "afterloop", TheFunction);

// Insert the conditional branch into the end of LoopEndBB.
Builder.CreateCondBr(EndCond, LoopBB, AfterBB);

// Any new code will be inserted in AfterBB.
Builder.SetInsertPoint(AfterBB); 
```

循环体的代码完成后，我们只需要完成其控制流。这段代码记住了结束块（用于 Phi 节点），然后创建了循环退出的块（`afterloop`）。根据退出条件的值，它创建了一个条件分支，选择是再次执行循环还是退出循环。任何未来的代码都将在`afterloop`块中生成，因此将插入位置设置为它。

```
 // Add a new entry to the PHI node for the backedge.
  Variable->addIncoming(NextVar, LoopEndBB);

  // Restore the unshadowed variable.
  if (OldVal)
    NamedValues[VarName] = OldVal;
  else
    NamedValues.erase(VarName);

  // for expr always returns 0.0.
  return Constant::getNullValue(Type::getDoubleTy(getGlobalContext()));
} 
```

最终的代码处理了各种清理工作：现在我们有了`NextVar`值，我们可以将传入值添加到循环 PHI 节点中。之后，我们从符号表中移除循环变量，这样在 for 循环之后它就不在作用域内了。最后，for 循环的代码生成总是返回 0.0，这就是我们从`ForExprAST::Codegen`返回的内容。

通过这一章节，我们结束了教程中“为 Kaleidoscope 添加控制流”部分。在这一章节中，我们添加了两个控制流结构，并用它们来激发 LLVM IR 的一些方面，这对于前端实现者来说是很重要的。在我们故事的下一章中，我们将变得有点疯狂，向我们那可怜无辜的语言添加用户定义的运算符。
