# 代码生成

# 生成 LLVM IR 代码

欢迎来到《使用 LLVM 实现语言》教程的第三章。本章将向您展示如何将第二章构建的抽象语法树转换为 LLVM IR。这将教会您一些关于 LLVM 的工作原理，并演示使用 LLVM 有多容易。构建词法分析器和解析器比生成 LLVM IR 代码要复杂得多。 :)

请注意：本章及后续章节中的代码需要 LLVM 2.2 或更高版本。LLVM 2.1 及之前的版本不适用于此。还请注意，您需要使用与您的 LLVM 发布版本匹配的教程版本：如果您使用的是官方 LLVM 发布版本，请使用您发布版本中附带的文档或在 llvm.org 发布页面上找到的文档。

# 3.1 代码生成设置

为了生成 LLVM IR，我们希望有一些简单的设置来开始。首先，在每个 AST 类中定义虚拟代码生成（codegen）方法：

```
/// ExprAST - Base class for all expression nodes.
class ExprAST {
public:
  virtual ~ExprAST() {}
  virtual Value *Codegen() = 0;
};

/// NumberExprAST - Expression class for numeric literals like "1.0".
class NumberExprAST : public ExprAST {
  double Val;
public:
  NumberExprAST(double val) : Val(val) {}
  virtual Value *Codegen();
};
... 
```

`Codegen()`方法表示要为该 AST 节点以及它所依赖的所有内容发出 IR，并且它们都返回一个 LLVM Value 对象。 "Value" 是用于表示 LLVM 中的 "静态单赋值（SSA）寄存器" 或 "SSA 值" 的类。SSA 值最显著的特点是它们的值是与相关指令执行时计算的，并且在指令重新执行之前（如果有必要）不会获得新值。换句话说，没有办法“更改”SSA 值。有关更多信息，请阅读有关静态单赋值的内容 - 一旦你理解了这些概念，它们真的很自然。

请注意，与其向 ExprAST 类层次结构添加虚拟方法，还可以使用访问者模式或其他一些方式来建模。再次强调，本教程不会深入探讨良好的软件工程实践：对于我们的目的，添加一个虚拟方法是最简单的方法。

我们想要的第二件事是一个像我们为解析器使用的`Error`方法，它将用于报告在代码生成过程中发现的错误（例如，使用了未声明的参数）：

```
Value *ErrorV(const char *Str) { Error(Str); return 0; }

static Module *TheModule;
static IRBuilder<> Builder(getGlobalContext());
static std::map<std::string, Value*> NamedValues; 
```

静态变量将在代码生成过程中使用。TheModule 是 LLVM 的构造，它包含了一段代码中的所有函数和全局变量。在许多方面，它是 LLVM IR 用来包含代码的顶层结构。

Builder 对象是一个辅助对象，它使生成 LLVM 指令变得简单。[IRBuilder](http://llvm.org/doxygen/IRBuilder_8h-source.html) 类模板的实例跟踪当前插入指令的位置，并具有创建新指令的方法。

NamedValues 映射跟踪当前作用域中定义的哪些值以及它们的 LLVM 表示形式是什么（换句话说，它是代码的符号表）。在这种形式的 Kaleidoscope 中，唯一可以引用的是函数参数。因此，在为其函数体生成代码时，函数参数将在此映射中。

有了这些基础，我们可以开始讨论如何为每个表达式生成代码。请注意，这假定 Builder 已经设置好，以将代码生成到某个地方。暂时假设这已经完成，我们将只使用它来发出代码。

# 3.2 表达式代码生成

为表达式节点生成 LLVM 代码非常简单：我们的四个表达式节点的所有注释代码不到 45 行。首先我们来处理数字文字：

```
Value *NumberExprAST::Codegen() {
  return ConstantFP::get(getGlobalContext(), APFloat(Val));
} 
```

在 LLVM IR 中，数字常量用 ConstantFP 类表示，该类在内部使用 APFloat 保存数字值（APFloat 具有保存任意精度浮点常量的能力）。这段代码基本上只是创建并返回一个 ConstantFP。请注意，在 LLVM IR 中，常量都是唯一的并共享的。因此，API 使用 `foo::get(...)` 惯用法而不是 `new foo(..)` 或 `foo::Create(..)`。

```
Value *VariableExprAST::Codegen() {
  // Look this variable up in the function.
  Value *V = NamedValues[Name];
  return V ? V : ErrorV("Unknown variable name");
} 
```

使用 LLVM 引用变量也非常简单。在 Kaleidoscope 的简单版本中，我们假设变量已经在某处发出，并且其值可用。实际上，NamedValues 映射中唯一可能存在的值是函数参数。这段代码简单地检查指定的名称是否在映射中（如果不在，则引用了未知变量），并返回其值。在后续章节中，我们将为符号表添加对循环归纳变量和局部变量的支持。

```
Value *BinaryExprAST::Codegen() {
  Value *L = LHS->Codegen();
  Value *R = RHS->Codegen();
  if (L == 0 || R == 0) return 0;

  switch (Op) {
  case '+': return Builder.CreateFAdd(L, R, "addtmp");
  case '-': return Builder.CreateFSub(L, R, "subtmp");
  case '*': return Builder.CreateFMul(L, R, "multmp");
  case '<':
    L = Builder.CreateFCmpULT(L, R, "cmptmp");
    // Convert bool 0/1 to double 0.0 or 1.0
    return Builder.CreateUIToFP(L, Type::getDoubleTy(getGlobalContext()),
                                "booltmp");
  default: return ErrorV("invalid binary operator");
  }
} 
```

二元运算符开始变得更有趣。基本思想是我们递归地为表达式的左侧发出代码，然后是右侧，然后计算二元表达式的结果。在这段代码中，我们简单地根据操作码进行切换以创建正确的 LLVM 指令。

在上面的示例中，LLVM builder 类开始显示其价值。IRBuilder 知道在哪里插入新创建的指令，你只需指定要创建的指令（例如使用 CreateFAdd），要使用的操作数（这里是 L 和 R），并可选择为生成的指令提供一个名称。

LLVM 的一个好处是名称只是一个提示。例如，如果上面的代码发出多个`addtmp`变量，LLVM 将自动为每个变量提供递增的唯一数字后缀。指令的本地值名称是完全可选的，但这样做可以使阅读 IR 转储变得更容易。

LLVM 指令受严格规则约束：例如，加法指令的左右操作数必须具有相同类型，并且加法的结果类型必须与操作数类型匹配。由于 Kaleidoscope 中的所有值都是双精度，这使得加法、减法和乘法的代码非常简单。

另一方面，LLVM 规定 fcmp 指令始终返回一个‘i1’值（一个一位整数）。问题在于 Kaleidoscope 希望该值为 0.0 或 1.0 值。为了获得这些语义，我们将 fcmp 指令与 uitofp 指令结合使用。该指令通过将输入整数视为无符号值，将其转换为浮点值。相比之下，如果我们使用 sitofp 指令，Kaleidoscope 的‘<' 运算符将根据输入值返回 0.0 和 -1.0。

```
Value *CallExprAST::Codegen() {
  // Look up the name in the global module table.
  Function *CalleeF = TheModule->getFunction(Callee);
  if (CalleeF == 0)
    return ErrorV("Unknown function referenced");

  // If argument mismatch error.
  if (CalleeF->arg_size() != Args.size())
    return ErrorV("Incorrect # arguments passed");

  std::vector<Value*> ArgsV;
  for (unsigned i = 0, e = Args.size(); i != e; ++i) {
    ArgsV.push_back(Args[i]->Codegen());
    if (ArgsV.back() == 0) return 0;
  }

  return Builder.CreateCall(CalleeF, ArgsV, "calltmp");
} 
```

使用 LLVM 进行函数调用的代码非常简单。上面的代码首先在 LLVM 模块的符号表中进行函数名称查找。回想一下，LLVM 模块是包含我们 JIT 的所有函数的容器。通过为每个函数指定与用户指定的名称相同的名称，我们可以使用 LLVM 符号表来解析函数名称。

一旦我们有要调用的函数，我们递归地为每个要传递的参数生成代码，并创建一个 LLVM 调用指令。请注意，LLVM 默认使用本机 C 调用约定，允许这些调用调用标准库函数如`sin`和`cos`，而无需额外的努力。

这样我们就完成了对 Kaleidoscope 中迄今为止的四种基本表达式的处理。随时添加更多内容。例如，通过查阅 LLVM 语言参考，您会发现几个其他有趣的指令，这些指令非常容易插入到我们的基本框架中。

# 3.3 函数代码生成

原型和函数的代码生成必须处理许多细节，这使得它们的代码比表达式代码生成更加复杂，但可以帮助我们阐明一些重要的观点。首先，让我们谈谈原型的代码生成：它们既用于函数体，也用于外部函数声明。代码从以下开始：

```
Function *PrototypeAST::Codegen() {
  // Make the function type:  double(double,double) etc.
  std::vector<Type*> Doubles(Args.size(),
                             Type::getDoubleTy(getGlobalContext()));
  FunctionType *FT = FunctionType::get(Type::getDoubleTy(getGlobalContext()),
                                       Doubles, false);

  Function *F = Function::Create(FT, Function::ExternalLinkage, Name, TheModule); 
```

这段代码将大量功能打包到几行代码中。首先注意到这个函数返回的是`Function*`而不是`Value*`。因为“原型”实际上是指函数的外部接口（而不是表达式计算得到的值），所以在代码生成时返回对应的 LLVM 函数是有意义的。

对 FunctionType::get 的调用创建了应用于给定原型的 FunctionType。由于 Kaleidoscope 中的所有函数参数都是 double 类型，第一行创建了一个包含“N”个 LLVM double 类型的向量。然后使用 Functiontype::get 方法创建一个函数类型，该函数接受“N”个 double 作为参数，返回一个 double 作为结果，并且不是 vararg（false 参数表示这一点）。请注意，LLVM 中的类型和常量一样是唯一的，因此你不需要“new”一个类型，而是“get”它。

上面的最后一行实际上创建了原型将对应的函数。这指示了要使用的类型、链接和名称，以及要插入的模块。"外部链接"意味着函数可以在当前模块之外定义和/或可以由模块外的函数调用。传入的名称是用户指定的名称：由于指定了 "TheModule"，这个名称将在 "TheModule" 的符号表中注册，该符号表由上面的函数调用代码使用。

```
// If F conflicted, there was already something named 'Name'.  If it has a
// body, don't allow redefinition or reextern.
if (F->getName() != Name) {
  // Delete the one we just made and get the existing one.
  F->eraseFromParent();
  F = TheModule->getFunction(Name); 
```

模块符号表的工作方式与函数符号表在处理名称冲突时完全相同：如果使用先前添加到符号表的名称创建了一个新函数，则在将其添加到模块时，新函数将隐式重命名。上面的代码利用了这一事实来确定是否存在此函数的先前定义。

在万花筒中，我选择允许两种情况下的函数重新定义：首先，我们希望允许对函数进行多次 "extern"，只要外部的原型匹配即可（因为所有参数具有相同的类型，我们只需检查参数数量是否匹配）。其次，我们希望允许对函数进行 "extern" 然后为其定义主体。这在定义相互递归函数时很有用。

为了实现这一点，上面的代码首先检查函数名称是否发生冲突。如果是，则删除我们刚刚创建的函数（通过调用 eraseFromParent）然后调用 getFunction 来获取具有指定名称的现有函数。注意，LLVM 中的许多 API 都有 "erase" 形式和 "remove" 形式。"remove" 形式将对象从其父对象（例如从模块中的函数）中取消链接并返回它。"erase" 形式取消链接对象然后删除它。

```
 // If F already has a body, reject this.
  if (!F->empty()) {
    ErrorF("redefinition of function");
    return 0;
  }

  // If F took a different number of args, reject.
  if (F->arg_size() != Args.size()) {
    ErrorF("redefinition of function with different # args");
    return 0;
  }
} 
```

为了验证上面的逻辑，我们首先检查预先存在的函数是否是 "空的"。在这种情况下，空的意思是它没有基本块，这意味着它没有主体。如果没有主体，它就是一个前向声明。由于我们不允许在函数的完整定义之后出现任何内容，所以代码拒绝了这种情况。如果前一个对函数的引用是一个 "extern"，我们只需验证该定义和此定义的参数数量是否匹配。如果不匹配，我们会发出错误。

```
 // Set names for all arguments.
  unsigned Idx = 0;
  for (Function::arg_iterator AI = F->arg_begin(); Idx != Args.size();
       ++AI, ++Idx) {
    AI->setName(Args[Idx]);

    // Add arguments to variable symbol table.
    NamedValues[Args[Idx]] = AI;
  }
  return F;
} 
```

最后一部分原型代码循环遍历函数中的所有参数，将 LLVM Argument 对象的名称设置为匹配，并在 NamedValues 映射中注册参数，以供将来 VariableExprAST AST 节点使用。设置完成后，将 Function 对象返回给调用者。注意，我们这里不检查参数名称是否冲突（例如 "extern foo(a b a)"）。如果这样做，根据我们上面已经使用的机制，将会非常简单。

```
Function *FunctionAST::Codegen() {
  NamedValues.clear();

  Function *TheFunction = Proto->Codegen();
  if (TheFunction == 0)
    return 0; 
```

函数定义的代码生成开始得相当简单：我们只需对原型（Proto）进行代码生成并验证其是否正常。然后我们清空 NamedValues 映射，以确保它不包含上次编译的函数中的任何内容。原型的代码生成确保有一个准备就绪的 LLVM 函数对象。

```
// Create a new basic block to start insertion into.
BasicBlock *BB = BasicBlock::Create(getGlobalContext(), "entry", TheFunction);
Builder.SetInsertPoint(BB);

if (Value *RetVal = Body->Codegen()) { 
```

现在我们来到了设置构建器的地方。第一行创建了一个新的基本块（命名为"entry"），它被插入到 TheFunction 中。第二行告诉构建器新指令应该插入到新基本块的末尾。LLVM 中的基本块是定义控制流图的函数中的重要部分。由于我们没有任何控制流，此时我们的函数将只包含一个块。我们将在第五章中修复这个问题 :).

```
if (Value *RetVal = Body->Codegen()) {
  // Finish off the function.
  Builder.CreateRet(RetVal);

  // Validate the generated code, checking for consistency.
  verifyFunction(*TheFunction);

  return TheFunction;
} 
```

一旦插入点设置好了，我们就为函数的根表达式调用 CodeGen()方法。如果没有错误发生，这将生成代码以计算表达式到入口块，并返回计算的值。假设没有错误，然后我们创建一个 LLVM ret 指令，完成函数。函数构建完成后，我们调用 LLVM 提供的 verifyFunction。这个函数对生成的代码进行各种一致性检查，以确定我们的编译器是否一切正常。使用这个函数很重要：它可以捕捉到很多错误。函数完成并验证后，我们返回它。

```
 // Error reading body, remove function.
  TheFunction->eraseFromParent();
  return 0;
} 
```

这里唯一剩下的部分是处理错误情况。为简单起见，我们通过简单地使用`eraseFromParent`方法删除我们生成的函数来处理这个问题。这允许用户重新定义他们之前错误输入的函数：如果我们不删除它，它将存在于符号表中，带有一个主体，阻止未来的重新定义。

不过，这段代码确实有一个错误。由于`PrototypeAST::Codegen`可能返回先前定义的前向声明，我们的代码实际上可以删除一个前向声明。有许多方法可以修复这个错误，请看看你能想出什么！这里是一个测试用例：

```
extern foo(a b);     # ok, defines foo.
def foo(a b) c;      # error, 'c' is invalid.
def bar() foo(1, 2); # error, unknown function "foo" 
```

# 3.4 驱动程序更改和结束思考

目前，将代码生成到 LLVM 并没有给我们带来太多好处，除了我们可以查看漂亮的 IR 调用。示例代码将 Codegen 调用插入到`HandleDefinition`、`HandleExtern`等函数中，然后输出 LLVM IR。这为查看简单函数的 LLVM IR 提供了一个很好的方式。例如：

```
ready> 4+5;
Read top-level expression:
define double @0() {
entry:
  ret double 9.000000e+00
} 
```

注意解析器如何将顶层表达式转换为匿名函数。当我们在下一章中添加 JIT 支持时，这将非常方便。还要注意代码是非常直接转录的，除了 IRBuilder 执行的简单常量折叠之外，没有进行任何优化。我们将在下一章中明确添加优化。

```
ready> def foo(a b) a*a + 2*a*b + b*b;
Read function definition:
define double @foo(double %a, double %b) {
entry:
  %multmp = fmul double %a, %a
  %multmp1 = fmul double 2.000000e+00, %a
  %multmp2 = fmul double %multmp1, %b
  %addtmp = fadd double %multmp, %multmp2
  %multmp3 = fmul double %b, %b
  %addtmp4 = fadd double %addtmp, %multmp3
  ret double %addtmp4
} 
```

这展示了一些简单的算术。注意到我们用来创建指令的 LLVM 构建器调用与之有着惊人的相似之处。

```
ready> def bar(a) foo(a, 4.0) + bar(31337);
Read function definition:
define double @bar(double %a) {
entry:
  %calltmp = call double @foo(double %a, double 4.000000e+00)
  %calltmp1 = call double @bar(double 3.133700e+04)
  %addtmp = fadd double %calltmp, %calltmp1
  ret double %addtmp
} 
```

这里展示了一些函数调用。请注意，如果你调用这个函数，它将需要很长时间才能执行。在未来，我们将添加条件控制流，以使递归真正有用 :).

```
ready> extern cos(x);
Read extern:
declare double @cos(double)

ready> cos(1.234);
Read top-level expression:
define double @1() {
entry:
  %calltmp = call double @cos(double 1.234000e+00)
  ret double %calltmp
} 
```

这里展示了对 libm 中的"cos"函数的外部引用，并对其进行调用。

```
ready> ^D
; ModuleID = 'my cool jit'

define double @0() {
entry:
  %addtmp = fadd double 4.000000e+00, 5.000000e+00
  ret double %addtmp
}

define double @foo(double %a, double %b) {
entry:
  %multmp = fmul double %a, %a
  %multmp1 = fmul double 2.000000e+00, %a
  %multmp2 = fmul double %multmp1, %b
  %addtmp = fadd double %multmp, %multmp2
  %multmp3 = fmul double %b, %b
  %addtmp4 = fadd double %addtmp, %multmp3
  ret double %addtmp4
}

define double @bar(double %a) {
entry:
  %calltmp = call double @foo(double %a, double 4.000000e+00)
  %calltmp1 = call double @bar(double 3.133700e+04)
  %addtmp = fadd double %calltmp, %calltmp1
  ret double %addtmp
}

declare double @cos(double)

define double @1() {
entry:
  %calltmp = call double @cos(double 1.234000e+00)
  ret double %calltmp
} 
```

当你退出当前演示时，它会输出整个模块生成的 IR。在这里，你可以看到所有函数相互引用的整体情况。

这结束了万花筒教程的第三章。接下来，我们将描述如何为此添加 JIT 代码生成和优化器支持，以便我们实际上可以开始运行代码！
