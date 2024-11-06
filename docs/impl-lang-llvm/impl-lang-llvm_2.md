# 解析器

# 实现解析器和 AST

欢迎来到“使用 LLVM 实现语言”教程的第二章。本章将向您展示如何使用第一章中构建的词法分析器来为我们的 Kaleidoscope 语言构建一个完整的解析器。一旦我们有了解析器，我们将定义并构建一个抽象语法树（AST）。

我们将构建的解析器使用递归下降解析和运算符优先级解析的组合来解析 Kaleidoscope 语言（后者用于二元表达式，前者用于其他所有内容）。在我们开始解析之前，让我们先谈谈解析器的输出：抽象语法树。

# 2.1 抽象语法树（AST）

程序的 AST 以一种易于编译器后续阶段（例如代码生成）解释的方式捕获其行为。我们基本上希望语言中的每个构造都有一个对象，并且 AST 应该紧密模拟语言。在 Kaleidoscope 中，我们有表达式、原型和函数对象。我们将首先从表达式开始：

```
/// ExprAST - Base class for all expression nodes.
class ExprAST {
public:
  virtual ~ExprAST() {}
};

/// NumberExprAST - Expression class for numeric literals like "1.0".
class NumberExprAST : public ExprAST {
  double Val;
public:
  NumberExprAST(double val) : Val(val) {}
}; 
```

上面的代码显示了基本 ExprAST 类的定义以及我们用于数字文字的一个子类。关于这段代码的重要事情是，NumberExprAST 类将文字的数值作为实例变量捕获。这使得编译器的后续阶段能够知道存储的数值是什么。

目前我们只创建了 AST，所以它们上面没有有用的访问器方法。例如，添加一个虚拟方法来漂亮地打印代码将非常容易。以下是我们将在 Kaleidoscope 语言的基本形式中使用的其他表达式 AST 节点定义：

```
/// VariableExprAST - Expression class for referencing a variable, like "a".
class VariableExprAST : public ExprAST {
  std::string Name;
public:
  VariableExprAST(const std::string &name) : Name(name) {}
};

/// BinaryExprAST - Expression class for a binary operator.
class BinaryExprAST : public ExprAST {
  char Op;
  ExprAST *LHS, *RHS;
public:
  BinaryExprAST(char op, ExprAST *lhs, ExprAST *rhs)
    : Op(op), LHS(lhs), RHS(rhs) {}
};

/// CallExprAST - Expression class for function calls.
class CallExprAST : public ExprAST {
  std::string Callee;
  std::vector<ExprAST*> Args;
public:
  CallExprAST(const std::string &callee, std::vector<ExprAST*> &args)
    : Callee(callee), Args(args) {}
}; 
```

这一切（故意）相当直接：变量捕获变量名，二元运算符捕获其操作码（例如，`+`），调用捕获函数名以及任何参数表达式的列表。我们的 AST 的一个好处是，它捕获了语言特性，而不涉及语言的语法。请注意，没有讨论二元运算符的优先级、词法结构等。

对于我们的基本语言，这些是我们将定义的所有表达式节点。因为它没有条件控制流，所以它不是图灵完备的；我们将在以后的安装中修复这个问题。接下来我们需要的是一种讨论函数接口的方法，以及一种讨论函数本身的方法：

```
/// PrototypeAST - This class represents the "prototype" for a function,
/// which captures its name, and its argument names (thus implicitly the number
/// of arguments the function takes).
class PrototypeAST {
  std::string Name;
  std::vector<std::string> Args;
public:
  PrototypeAST(const std::string &name, const std::vector<std::string> &args)
    : Name(name), Args(args) {}
};

/// FunctionAST - This class represents a function definition itself.
class FunctionAST {
  PrototypeAST *Proto;
  ExprAST *Body;
public:
  FunctionAST(PrototypeAST *proto, ExprAST *body)
    : Proto(proto), Body(body) {}
}; 
```

在 Kaleidoscope 中，函数仅用其参数的计数进行类型化。由于所有值都是双精度浮点数，每个参数的类型不需要存储在任何地方。在一个更积极和现实的语言中，`ExprAST`类可能会有一个类型字段。

有了这个支架，我们现在可以谈论在 Kaleidoscope 中解析表达式和函数体。

# 2.2 解析器基础知识

现在我们有了一个要构建的 AST，我们需要定义构建它的解析器代码。这里的想法是，我们想解析类似于`x+y`的东西（由词法分析器返回为三个标记），并将其转换为可以通过类似于这样的调用生成的 AST：

```
ExprAST *X = new VariableExprAST("x");
ExprAST *Y = new VariableExprAST("y");
ExprAST *Result = new BinaryExprAST('+', X, Y);
In order to do this, we'll start by defining some basic helper routines:

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static int CurTok;
static int getNextToken() {
  return CurTok = gettok();
} 
```

这实现了围绕词法分析器的简单标记缓冲区。这使我们能够提前查看词法分析器返回的一个标记。我们解析器中的每个函数都将假定 CurTok 是需要解析的当前标记。

```
/// Error* - These are little helper functions for error handling.
ExprAST *Error(const char *Str) { fprintf(stderr, "Error: %s\n", Str);return 0;}
PrototypeAST *ErrorP(const char *Str) { Error(Str); return 0; }
FunctionAST *ErrorF(const char *Str) { Error(Str); return 0; } 
```

Error 例程是我们解析器将用于处理错误的简单辅助例程。我们解析器中的错误恢复不会是最佳的，也不是特别用户友好的，但它对于我们的教程来说已经足够了。这些例程使在具有各种返回类型的例程中处理错误变得更容易：它们总是返回 null。

使用这些基本的辅助函数，我们可以实现我们语法的第一部分：数值字面量。

# 2.3 基本表达式解析

我们从数值字面量开始，因为它们是最简单的处理。对于我们语法中的每个产生式，我们将定义一个函数来解析该产生式。对于数值字面量，我们有：

```
/// numberexpr ::= number
static ExprAST *ParseNumberExpr() {
  ExprAST *Result = new NumberExprAST(NumVal);
  getNextToken(); // consume the number
  return Result;
} 
```

此例程非常简单：它期望在当前标记是 tok_number 标记时调用。它获取当前数字值，创建一个 NumberExprAST 节点，将词法分析器推进到下一个标记，最后返回。

这有一些有趣的方面。最重要的是，此例程会吃掉与产生式对应的所有标记，并返回带有下一个标记（不是语法产生的一部分）的词法分析器缓冲区，准备好使用。这是递归下降解析器的一种相当标准的方法。作为更好的例子，括号运算符是这样定义的：

```
/// parenexpr ::= '(' expression ')'
static ExprAST *ParseParenExpr() {
  getNextToken();  // eat (.
  ExprAST *V = ParseExpression();
  if (!V) return 0;

  if (CurTok != ')')
    return Error("expected ')'");
  getNextToken();  // eat ).
  return V;
} 
```

此函数说明了解析器的许多有趣之处：

1) 它展示了我们如何使用 Error 例程。当调用时，此函数期望当前标记是一个`（`标记，但在解析子表达式之后，可能没有等待的`）`。例如，如果用户键入了`(4 x`而不是`(4)`，解析器应该发出错误。因为错误可能会发生，解析器需要一种指示它们发生的方法：在我们的解析器中，错误时我们返回 null。

2) 此函数的另一个有趣之处在于它通过调用 ParseExpression 使用了递归（我们很快会看到 ParseExpression 可以调用 ParseParenExpr）。这很强大，因为它允许我们处理递归语法，并保持每个产生式非常简单。请注意，括号本身并不会导致 AST 节点的构造。虽然我们可以这样做，但括号的最重要作用是指导解析器并提供分组。一旦解析器构造了 AST，括号就不再需要了。

处理变量引用和函数调用的下一个简单产生式是：

```
/// identifierexpr
///   ::= identifier
///   ::= identifier '(' expression* ')'
static ExprAST *ParseIdentifierExpr() {
  std::string IdName = IdentifierStr;

  getNextToken();  // eat identifier.

  if (CurTok != '(') // Simple variable ref.
    return new VariableExprAST(IdName);

  // Call.
  getNextToken();  // eat (
  std::vector<ExprAST*> Args;
  if (CurTok != ')') {
    while (1) {
      ExprAST *Arg = ParseExpression();
      if (!Arg) return 0;
      Args.push_back(Arg);

      if (CurTok == ')') break;

      if (CurTok != ',')
        return Error("Expected ')' or ',' in argument list");
      getNextToken();
    }
  }

  // Eat the ')'.
  getNextToken();

  return new CallExprAST(IdName, Args);
} 
```

这个例程遵循与其他例程相同的风格。（它期望在当前标记为 tok_identifier 标记时被调用）。它还具有递归和错误处理。其中一个有趣的方面是它使用前瞻来确定当前标识符是独立的变量引用还是函数调用表达式。它通过检查标识符后面的标记是否为`(`标记来处理，根据情况构造 VariableExprAST 或 CallExprAST 节点。

现在我们已经完成了所有简单表达式解析逻辑，我们可以定义一个辅助函数将它们包装在一起成为一个入口点。我们将这类表达式称为“主要”表达式，原因将在本教程后面更清晰地展现。为了解析任意主要表达式，我们需要确定它是什么类型的表达式：

```
/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
static ExprAST *ParsePrimary() {
  switch (CurTok) {
  default: return Error("unknown token when expecting an expression");
  case tok_identifier: return ParseIdentifierExpr();
  case tok_number:     return ParseNumberExpr();
  case '(':            return ParseParenExpr();
  }
} 
```

现在您看到这个函数的定义，更容易理解为什么我们可以假设各个函数中 CurTok 的状态。这使用前瞻来确定正在检查的表达式类型，然后通过函数调用解析它。

现在基本表达式已经处理完毕，我们需要处理二进制表达式。它们稍微复杂一些。

# 2.4 二进制表达式解析

二进制表达式通常更难解析，因为它们经常存在歧义。例如，当给定字符串`x+y*z`时，解析器可以选择将其解析为`(x+y)*z`或`x+(y*z)`。根据数学中的常见定义，我们期望后一种解析，因为`*`（乘法）比`+`（加法）具有更高的优先级。

处理这个问题的方法有很多种，但一种优雅且高效的方法是使用运算符优先级解析。这种解析技术使用二元运算符的优先级来引导递归。首先，我们需要一个优先级表：

```
/// BinopPrecedence - This holds the precedence for each binary operator that is
/// defined.
static std::map<char, int> BinopPrecedence;

/// GetTokPrecedence - Get the precedence of the pending binary operator token.
static int GetTokPrecedence() {
  if (!isascii(CurTok))
    return -1;

  // Make sure it's a declared binop.
  int TokPrec = BinopPrecedence[CurTok];
  if (TokPrec <= 0) return -1;
  return TokPrec;
}

int main() {
  // Install standard binary operators.
  // 1 is lowest precedence.
  BinopPrecedence['<'] = 10;
  BinopPrecedence['+'] = 20;
  BinopPrecedence['-'] = 20;
  BinopPrecedence['*'] = 40;  // highest.
  ...
} 
```

对于 Kaleidoscope 的基本形式，我们只支持 4 个二元运算符（显然，您可以扩展）。GetTokPrecedence 函数返回当前标记的优先级，如果标记不是二元运算符，则返回-1。使用映射使添加新运算符变得容易，并清楚地表明算法不依赖于特定的运算符，但也可以很容易地消除映射，并在 GetTokPrecedence 函数中进行比较（或者只使用固定大小的数组）。

有了上面定义的辅助函数，我们现在可以开始解析二进制表达式了。运算符优先级解析的基本思想是将具有潜在模糊二进制运算符的表达式分解为片段。例如，考虑表达式 `a+b+(c+d)*e*f+g`。运算符优先级解析将其视为一系列由二进制运算符分隔的主表达式流。因此，它首先解析前导主表达式 `a`，然后它将看到对流 [+, b] [+, (c+d)] [*, e] [*, f] 和 [+, g]。注意，因为括号是主表达式，所以二进制表达式解析器根本不需要担心像 (c+d) 这样的嵌套子表达式。

要开始，一个表达式是一个主表达式，后面可能跟着一系列 [binop, primaryexpr] 对：

```
/// expression
///   ::= primary binoprhs
///
static ExprAST *ParseExpression() {
  ExprAST *LHS = ParsePrimary();
  if (!LHS) return 0;

  return ParseBinOpRHS(0, LHS);
} 
```

ParseBinOpRHS 是为我们解析对流的函数。它接受一个优先级和一个指向到目前为止已解析部分的表达式的指针。注意 `x` 是一个完全有效的表达式：因此，`binoprhs` 允许为空，在这种情况下，它会返回传入它的表达式。在我们上面的例子中，代码将 `a` 的表达式传递给 ParseBinOpRHS，当前标记是 `+`。

传入 ParseBinOpRHS 的优先级值指示了该函数被允许吞食的最低运算符优先级。例如，如果当前的对流是 `[+, x]`，并且 ParseBinOpRHS 被传入一个优先级为 40，那么它不会消耗任何标记（因为 `+` 的优先级只有 20）。有了这个想法，ParseBinOpRHS 从以下开始：

```
/// binoprhs
///   ::= ('+' primary)*
static ExprAST *ParseBinOpRHS(int ExprPrec, ExprAST *LHS) {
  // If this is a binop, find its precedence.
  while (1) {
    int TokPrec = GetTokPrecedence();

    // If this is a binop that binds at least as tightly as the current binop,
    // consume it, otherwise we are done.
    if (TokPrec < ExprPrec)
      return LHS; 
```

此代码获取当前标记的优先级并检查是否过低。因为我们定义了无效标记的优先级为 -1，所以这个检查隐式地知道当标记流耗尽二进制运算符时，对流也将结束。如果此检查成功，我们知道该标记是一个二进制运算符，并且它将包含在此表达式中：

```
// Okay, we know this is a binop.
int BinOp = CurTok;
getNextToken();  // eat binop

// Parse the primary expression after the binary operator.
ExprAST *RHS = ParsePrimary();
if (!RHS) return 0; 
```

因此，此代码吃掉（并记住）二进制运算符，然后解析后面的主表达式。这构建了整个对流，对于运行示例来说，第一个对流是 [+, b]。

现在我们已经解析了表达式的左侧和一对 RHS 序列，我们必须决定表达式的关联方式。特别地，我们可以有 `(a+b) binop unparsed` 或者 `a + (b binop unparsed)`。为了确定这一点，我们向前看 `binop` 来确定其优先级，并将其与 BinOp 的优先级（在本例中为 `+`）进行比较：

```
// If BinOp binds less tightly with RHS than the operator after RHS, let
// the pending operator take RHS as its LHS.
int NextPrec = GetTokPrecedence();
if (TokPrec < NextPrec) { 
```

如果 "RHS" 右侧的 binop 的优先级低于或等于我们当前运算符的优先级，那么我们知道括号的关联方式是 `(a+b) binop ...`。在我们的例子中，当前运算符是 `+`，下一个运算符是 `+`，我们知道它们具有相同的优先级。在这种情况下，我们将创建 `a+b` 的 AST 节点，然后继续解析：

```
 ... if body omitted ...
    }

    // Merge LHS/RHS.
    LHS = new BinaryExprAST(BinOp, LHS, RHS);
  }  // loop around to the top of the while loop.
} 
```

在我们上面的示例中，这将把`a+b+`转换为`(a+b)`并执行循环的下一次迭代，`+`作为当前的标记。上面的代码将吞下、记住并解析`(c+d)`作为主要表达式，这使得当前的对等于[+, (c+d)]。然后，它将使用`*`作为主要右侧的二进制运算符来评估上面的`if`条件。在这种情况下，`*`的优先级高于`+`的优先级，因此将进入 if 条件。

这里的关键问题是“if 条件如何解析右手边的完整内容”？特别是，为了为我们的示例正确构建 AST，它需要将所有的`(c+d)*e*f`作为 RHS 表达式变量。执行此操作的代码非常简单（从上述两个块中复制的代码以获得上下文）：

```
 // If BinOp binds less tightly with RHS than the operator after RHS, let
    // the pending operator take RHS as its LHS.
    int NextPrec = GetTokPrecedence();
    if (TokPrec < NextPrec) {
      RHS = ParseBinOpRHS(TokPrec+1, RHS);
      if (RHS == 0) return 0;
    }
    // Merge LHS/RHS.
    LHS = new BinaryExprAST(BinOp, LHS, RHS);
  }  // loop around to the top of the while loop.
} 
```

在这一点上，我们知道主要右手边的二进制运算符的优先级高于我们当前解析的二进制运算符。因此，我们知道任何操作符的序列，其优先级都高于`+`，应该一起解析并作为"RHS"返回。为此，我们递归调用 ParseBinOpRHS 函数，指定"TokPrec+1"作为继续执行所需的最小优先级。在我们上面的示例中，这将导致它返回`(c+d)*e*f`的 AST 节点作为 RHS，然后将其设置为`+`表达式的 RHS。

最后，在 while 循环的下一次迭代中，`+g`部分被解析并添加到 AST 中。通过这小段代码（14 行非平凡代码），我们以非常优雅的方式正确处理了完全一般的二进制表达式解析。这是对这段代码的一次风驰电掣的演示，它有些微妙。我建议使用一些复杂的示例运行它，看看它是如何工作的。

这就是表达式的处理。在这一点上，我们可以将解析器指向任意的标记流，并从中构建一个表达式，在遇到不是表达式的第一个标记时停止。接下来我们需要处理函数定义等等。

# 2.5 解析剩余部分

下一个缺失的东西是处理函数原型。在 Kaleidoscope 中，这些既用于`extern`函数声明，也用于函数主体定义。要执行此操作的代码很简单，也不是很有趣（一旦您完成了表达式）：

```
/// prototype
///   ::= id '(' id* ')'
static PrototypeAST *ParsePrototype() {
  if (CurTok != tok_identifier)
    return ErrorP("Expected function name in prototype");

  std::string FnName = IdentifierStr;
  getNextToken();

  if (CurTok != '(')
    return ErrorP("Expected '(' in prototype");

  // Read the list of argument names.
  std::vector<std::string> ArgNames;
  while (getNextToken() == tok_identifier)
    ArgNames.push_back(IdentifierStr);
  if (CurTok != ')')
    return ErrorP("Expected ')' in prototype");

  // success.
  getNextToken();  // eat ')'.

  return new PrototypeAST(FnName, ArgNames);
} 
```

鉴于此，函数定义非常简单，只是一个原型加上一个实现主体的表达式：

```
/// definition ::= 'def' prototype expression
static FunctionAST *ParseDefinition() {
  getNextToken();  // eat def.
  PrototypeAST *Proto = ParsePrototype();
  if (Proto == 0) return 0;

  if (ExprAST *E = ParseExpression())
    return new FunctionAST(Proto, E);
  return 0;
} 
```

此外，我们支持`extern`来声明函数，如`sin`和`cos`，以及支持用户函数的前向声明。这些'extern'只是没有主体的原型：

```
/// external ::= 'extern' prototype
static PrototypeAST *ParseExtern() {
  getNextToken();  // eat extern.
  return ParsePrototype();
} 
```

最后，我们还将让用户输入任意顶级表达式，并在运行时对其进行评估。我们将通过为它们定义匿名的零参数函数来处理这个问题：

```
/// toplevelexpr ::= expression
static FunctionAST *ParseTopLevelExpr() {
  if (ExprAST *E = ParseExpression()) {
    // Make an anonymous proto.
    PrototypeAST *Proto = new PrototypeAST("", std::vector<std::string>());
    return new FunctionAST(Proto, E);
  }
  return 0;
} 
```

现在我们有了所有的部分，让我们构建一个小型驱动程序，让我们实际执行我们构建的这段代码！

# 2.6 驱动程序

这个驱动程序只是通过一个顶层分发循环调用所有的解析部分。这里没有太多有趣的内容，所以我将只包含顶层循环。请参见下面的“顶层解析”部分中的完整代码。

```
/// top ::= definition | external | expression | ';'
static void MainLoop() {
  while (1) {
    fprintf(stderr, "ready> ");
    switch (CurTok) {
    case tok_eof:    return;
    case ';':        getNextToken(); break;  // ignore top-level semicolons.
    case tok_def:    HandleDefinition(); break;
    case tok_extern: HandleExtern(); break;
    default:         HandleTopLevelExpression(); break;
    }
  }
} 
```

这个最有趣的部分是我们忽略了顶层分号。你会问为什么，这是为什么呢？基本原因是，如果你在命令行上输入`4 + 5`，解析器不知道这是否是你要输入的内容的结尾。例如，下一行你可能会输入`def foo...`，这样`4+5`就是顶层表达式的结尾。或者你可能会输入`* 6`，这将继续表达式。有了顶层分号，你可以输入`4+5;`，解析器就会知道你已经完成了。

# 2.8\. 结论

仅有不到 400 行的注释代码（240 行非注释、非空白代码），我们完全定义了我们的最小语言，包括词法分析器、语法分析器和抽象语法树构建器。完成后，可执行文件将验证万花筒代码，并告诉我们它是否在语法上无效。例如，这是一个示例交互：

```
$ ./a.out
ready> def foo(x y) x+foo(y, 4.0);
Parsed a function definition.
ready> def foo(x y) x+y y;
Parsed a function definition.
Parsed a top-level expr
ready> def foo(x y) x+y );
Parsed a function definition.
Error: unknown token when expecting an expression
ready> extern sin(a);
ready> Parsed an extern
ready> ^D
$ 
```

这里有很多扩展的空间。你可以定义新的抽象语法树节点，以多种方式扩展语言等。在下一部分中，我们将描述如何从抽象语法树生成 LLVM 中间表示（IR）。
