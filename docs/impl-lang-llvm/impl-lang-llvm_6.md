# 用户定义的操作

# 用户自定义操作

欢迎来到“使用 LLVM 实现语言”的教程第六章。在我们的教程中的这一点上，我们现在有一个完全功能的语言，它相当简单，但也有用。然而，它还有一个很大的问题。我们的语言没有很多有用的运算符（比如除法、逻辑否定，甚至除了小于以外没有任何比较）。

本教程的这一章将在简单而美丽的 Kaleidoscope 语言中添加用户定义的运算符。在某些方面，这种离题的结果使我们的语言变得简单但丑陋，但同时也是强大的。创建自己的语言的一大好处是你可以决定什么是好的或坏的。在本教程中，我们将假设使用这种方法来展示一些有趣的解析技术是可以的。

在本教程结束时，我们将运行一个渲染 Mandelbrot 集合的 Kaleidoscope 应用程序示例。这提供了一个使用 Kaleidoscope 及其特性集构建的示例。

# 6.1 用户自定义运算符：概念

我们将添加到 Kaleidoscope 的“操作符重载”比 C++等语言更通用。在 C++中，你只能重新定义现有的操作符：你不能编程地改变语法，引入新的操作符，改变优先级等。在本章中，我们将向 Kaleidoscope 添加此功能，这将允许用户完善支持的运算符集。

像这样的教程中讨论用户定义的运算符的目的是展示使用手写解析器的强大和灵活性。到目前为止，我们一直在实现的解析器对语法的大部分部分使用递归下降，对表达式使用操作符优先级解析。详情请参见第二章。如果不使用操作符优先级解析，允许程序员将新运算符引入语法将会非常困难：语法在 JIT 运行时是动态可扩展的。

我们将添加的两个具体功能是可编程的一元运算符（现在，Kaleidoscope 根本没有一元运算符）以及二元运算符。一个例子是：

```
# Logical unary not.
def unary!(v)
  if v then
    0
  else
    1;

# Define > with the same precedence as <.
def binary> 10 (LHS RHS)
  RHS < LHS;

# Binary "logical or", (note that it does not "short circuit")
def binary| 5 (LHS RHS)
  if LHS then
    1
  else if RHS then
    1
  else
    0;

# Define = with slightly lower precedence than relationals.
def binary= 9 (LHS RHS)
  !(LHS < RHS | LHS > RHS); 
```

许多语言渴望能够在语言本身中实现其标准运行时库。在 Kaleidoscope 中，我们可以在库中实现语言的重要部分！

我们将这些功能的实现分为两部分：实现对用户定义的二元运算符的支持和添加一元运算符。

# 6.2 用户自定义二元运算符

使用我们当前的框架添加对用户定义的二元运算符的支持非常简单。我们将首先添加对一元/二元关键字的支持：

```
enum Token {
  ...
  // operators
  tok_binary = -11, tok_unary = -12
};
...
static int gettok() {
...
    if (IdentifierStr == "for") return tok_for;
    if (IdentifierStr == "in") return tok_in;
    if (IdentifierStr == "binary") return tok_binary;
    if (IdentifierStr == "unary") return tok_unary;
    return tok_identifier; 
```

这只是为一元和二元关键字添加了词法支持，就像我们在前几章中所做的那样。我们当前 AST 的一个好处是，我们通过使用它们的 ASCII 码作为操作码，用完全泛化的方式表示二元运算符。对于我们扩展的运算符，我们将使用相同的表示，因此我们不需要任何新的 AST 或解析器支持。

另一方面，我们必须能够表示这些新运算符的定义，在函数定义的“def binary| 5”部分。到目前为止，我们的语法中，“名称”被解析为“原型”产生式，并转换为 PrototypeAST AST 节点。为了将我们的新用户定义的运算符表示为原型，我们必须像这样扩展 PrototypeAST AST 节点：

```
/// PrototypeAST - This class represents the "prototype" for a function,
/// which captures its argument names as well as if it is an operator.
class PrototypeAST {
  std::string Name;
  std::vector<std::string> Args;
  bool isOperator;
  unsigned Precedence;  // Precedence if a binary op.
public:
  PrototypeAST(const std::string &name, const std::vector<std::string> &args,
               bool isoperator = false, unsigned prec = 0)
  : Name(name), Args(args), isOperator(isoperator), Precedence(prec) {}

  bool isUnaryOp() const { return isOperator && Args.size() == 1; }
  bool isBinaryOp() const { return isOperator && Args.size() == 2; }

  char getOperatorName() const {
    assert(isUnaryOp() || isBinaryOp());
    return Name[Name.size()-1];
  }

  unsigned getBinaryPrecedence() const { return Precedence; }

  Function *Codegen();
}; 
```

基本上，除了知道原型的名称外，我们现在还要跟踪它是否是运算符，以及如果是运算符，则该运算符的优先级水平是多少。优先级仅用于二元运算符（如下所示，它对一元运算符不适用）。现在我们有了一种表示用户定义的运算符原型的方法，我们需要对其进行解析：

```
/// prototype
///   ::= id '(' id* ')'
///   ::= binary LETTER number? (id, id)
static PrototypeAST *ParsePrototype() {
  std::string FnName;

  unsigned Kind = 0;  // 0 = identifier, 1 = unary, 2 = binary.
  unsigned BinaryPrecedence = 30;

  switch (CurTok) {
  default:
    return ErrorP("Expected function name in prototype");
  case tok_identifier:
    FnName = IdentifierStr;
    Kind = 0;
    getNextToken();
    break;
  case tok_binary:
    getNextToken();
    if (!isascii(CurTok))
      return ErrorP("Expected binary operator");
    FnName = "binary";
    FnName += (char)CurTok;
    Kind = 2;
    getNextToken();

    // Read the precedence if present.
    if (CurTok == tok_number) {
      if (NumVal < 1 || NumVal > 100)
        return ErrorP("Invalid precedecnce: must be 1..100");
      BinaryPrecedence = (unsigned)NumVal;
      getNextToken();
    }
    break;
  }

  if (CurTok != '(')
    return ErrorP("Expected '(' in prototype");

  std::vector<std::string> ArgNames;
  while (getNextToken() == tok_identifier)
    ArgNames.push_back(IdentifierStr);
  if (CurTok != ')')
    return ErrorP("Expected ')' in prototype");

  // success.
  getNextToken();  // eat ')'.

  // Verify right number of names for operator.
  if (Kind && ArgNames.size() != Kind)
    return ErrorP("Invalid number of operands for operator");

  return new PrototypeAST(FnName, ArgNames, Kind != 0, BinaryPrecedence);
} 
```

这都是相当直接的解析代码，我们已经在过去看过很多类似的代码。上面代码的一个有趣部分是为二元运算符设置 FnName 的几行代码。这构建了类似“binary@”的名称，用于新定义的“@”运算符。然后，利用了 LLVM 符号表中的符号名称允许包含任何字符，包括嵌入的空字符的事实。

添加的下一个有趣的内容是对这些二元运算符的代码生成支持。鉴于我们当前的结构，这只是对现有二元运算符节点的默认情况进行简单添加：

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
  default: break;
  }

  // If it wasn't a builtin binary operator, it must be a user defined one. Emit
  // a call to it.
  Function *F = TheModule->getFunction(std::string("binary")+Op);
  assert(F && "binary operator not found!");

  Value *Ops[2] = { L, R };
  return Builder.CreateCall(F, Ops, "binop");
} 
```

如您在上面所见，新代码实际上非常简单。它只是在符号表中查找适当的运算符，并生成对其的函数调用。由于用户定义的运算符只是作为普通函数构建的（因为“原型”归结为具有正确名称的函数），所以一切都就位了。

我们缺少的最后一部分代码是一点顶层魔法：

```
Function *FunctionAST::Codegen() {
  NamedValues.clear();

  Function *TheFunction = Proto->Codegen();
  if (TheFunction == 0)
    return 0;

  // If this is an operator, install it.
  if (Proto->isBinaryOp())
    BinopPrecedence[Proto->getOperatorName()] = Proto->getBinaryPrecedence();

  // Create a new basic block to start insertion into.
  BasicBlock *BB = BasicBlock::Create(getGlobalContext(), "entry", TheFunction);
  Builder.SetInsertPoint(BB);

  if (Value *RetVal = Body->Codegen()) {
    ... 
```

基本上，在对函数进行代码生成之前，如果它是用户定义的运算符，我们将在优先级表中注册它。这使我们已经放置的二元运算符解析逻辑能够处理它。由于我们正在使用全面的运算符优先级解析器，这是我们“扩展语法”的全部内容。

现在我们有了有用的用户定义的二元运算符。这在我们为其他运算符构建的先前框架基础上构建了很多内容。添加一元运算符要困难一些，因为我们还没有为它构建任何框架 - 看看需要什么。

# 6.3 用户定义的一元运算符

由于我们当前不支持一元运算符在万花筒语言中，我们需要添加一切以支持它们。在上面，我们为词法分析器添加了对‘unary’关键字的简单支持。除此之外，我们还需要一个 AST 节点：

```
/// UnaryExprAST - Expression class for a unary operator.
class UnaryExprAST : public ExprAST {
  char Opcode;
  ExprAST *Operand;
public:
  UnaryExprAST(char opcode, ExprAST *operand)
    : Opcode(opcode), Operand(operand) {}
  virtual Value *Codegen();
}; 
```

到目前为止，这个 AST 节点非常简单和明显。它直接反映了二元运算符 AST 节点，只是它只有一个子节点。因此，我们需要添加解析逻辑。解析一元运算符非常简单：我们将添加一个新函数来完成它：

```
/// unary
///   ::= primary
///   ::= '!' unary
static ExprAST *ParseUnary() {
  // If the current token is not an operator, it must be a primary expr.
  if (!isascii(CurTok) || CurTok == '(' || CurTok == ',')
    return ParsePrimary();

  // If this is a unary operator, read it.
  int Opc = CurTok;
  getNextToken();
  if (ExprAST *Operand = ParseUnary())
    return new UnaryExprAST(Opc, Operand);
  return 0;
} 
```

我们在这里添加的语法非常简单明了。如果在解析主要运算符时遇到一元运算符，我们将将该运算符作为前缀吞掉，并将剩余部分解析为另一个一元运算符。这使我们能够处理多个一元运算符（例如`!!x`）。请注意，一元运算符不像二元运算符那样具有歧义解析，因此不需要优先级信息。

这个函数的问题在于我们需要从某个地方调用 ParseUnary。为此，我们需要更改之前调用 ParsePrimary 的调用者，改为调用 ParseUnary：

```
/// binoprhs
///   ::= ('+' unary)*
static ExprAST *ParseBinOpRHS(int ExprPrec, ExprAST *LHS) {
  ...
    // Parse the unary expression after the binary operator.
    ExprAST *RHS = ParseUnary();
    if (!RHS) return 0;
  ...
}
/// expression
///   ::= unary binoprhs
///
static ExprAST *ParseExpression() {
  ExprAST *LHS = ParseUnary();
  if (!LHS) return 0;

  return ParseBinOpRHS(0, LHS);
} 
```

通过这两个简单的更改，我们现在能够解析一元运算符并为其构建 AST。接下来，我们需要添加原型的解析器支持，以解析一元运算符原型。我们通过以下方式扩展上面的二元运算符代码：

```
/// prototype
///   ::= id '(' id* ')'
///   ::= binary LETTER number? (id, id)
///   ::= unary LETTER (id)
static PrototypeAST *ParsePrototype() {
  std::string FnName;

  unsigned Kind = 0;  // 0 = identifier, 1 = unary, 2 = binary.
  unsigned BinaryPrecedence = 30;

  switch (CurTok) {
  default:
    return ErrorP("Expected function name in prototype");
  case tok_identifier:
    FnName = IdentifierStr;
    Kind = 0;
    getNextToken();
    break;
  case tok_unary:
    getNextToken();
    if (!isascii(CurTok))
      return ErrorP("Expected unary operator");
    FnName = "unary";
    FnName += (char)CurTok;
    Kind = 1;
    getNextToken();
    break;
  case tok_binary:
    ... 
```

与二元运算符一样，我们使用包含运算符字符的名称来命名一元运算符。这在代码生成时对我们有所帮助。说到这里，我们需要添加的最后一部分是一元运算符的代码生成支持。代码如下：

```
Value *UnaryExprAST::Codegen() {
  Value *OperandV = Operand->Codegen();
  if (OperandV == 0) return 0;

  Function *F = TheModule->getFunction(std::string("unary")+Opcode);
  if (F == 0)
    return ErrorV("Unknown unary operator");

  return Builder.CreateCall(F, OperandV, "unop");
} 
```

这段代码与二元运算符的代码类似，但更简单。主要因为它不需要处理任何预定义的运算符。

# 6.4 试驾

有点难以置信，但通过我们在最后几章中介绍的一些简单扩展，我们已经构建了一个接近真实的语言。有了这个，我们可以做很多有趣的事情，包括 I/O、数学和其他一堆事情。例如，我们现在可以添加一个不错的顺序运算符（printd 被定义为打印指定值和一个换行符）：

```
ready> extern printd(x);
Read extern:
declare double @printd(double)

ready> def binary : 1 (x y) 0;  # Low-precedence operator that ignores operands.
..
ready> printd(123) : printd(456) : printd(789);
123.000000
456.000000
789.000000
Evaluated to 0.000000 
```

我们还可以定义一堆其他“原始”操作，比如：

```
# Logical unary not.
def unary!(v)
  if v then
    0
  else
    1;

# Unary negate.
def unary-(v)
  0-v;

# Define > with the same precedence as <.
def binary> 10 (LHS RHS)
  RHS < LHS;

# Binary logical or, which does not short circuit.
def binary| 5 (LHS RHS)
  if LHS then
    1
  else if RHS then
    1
  else
    0;

# Binary logical and, which does not short circuit.
def binary& 6 (LHS RHS)
  if !LHS then
    0
  else
    !!RHS;

# Define = with slightly lower precedence than relationals.
def binary = 9 (LHS RHS)
  !(LHS < RHS | LHS > RHS);

# Define ':' for sequencing: as a low-precedence operator that ignores operands
# and just returns the RHS.
def binary : 1 (x y) y; 
```

鉴于之前的 if/then/else 支持，我们还可以为 I/O 定义有趣的函数。例如，以下函数根据传入的值打印出反映该值的“密度”的字符：值越低，字符越密集：

```
ready>

extern putchard(char)
def printdensity(d)
  if d > 8 then
    putchard(32)  # ' '
  else if d > 4 then
    putchard(46)  # '.'
  else if d > 2 then
    putchard(43)  # '+'
  else
    putchard(42); # '*'
...
ready> printdensity(1): printdensity(2): printdensity(3):
       printdensity(4): printdensity(5): printdensity(9):
       putchard(10);
**++. 
```

评估为 0.000000 基于这些简单的原始操作，我们可以开始定义更有趣的事物。例如，这里有一个解决复平面中函数收敛所需迭代次数的小函数：

```
# Determine whether the specific location diverges.
# Solve for z = z² + c in the complex plane.
def mandleconverger(real imag iters creal cimag)
  if iters > 255 | (real*real + imag*imag > 4) then
    iters
  else
    mandleconverger(real*real - imag*imag + creal,
                    2*real*imag + cimag,
                    iters+1, creal, cimag);

# Return the number of iterations required for the iteration to escape
def mandleconverge(real imag)
  mandleconverger(real, imag, 0, real, imag); 
```

这个`z = z2 + c`函数是曼德勃罗集的计算基础，是一个美丽的小生物。我们的 mandelconverge 函数返回一个复杂轨道逃逸所需的迭代次数，饱和到 255。这个函数本身并不是很有用，但如果你在二维平面上绘制其值，就可以看到曼德勃罗集。鉴于我们在这里只能使用 putchard，我们惊人的图形输出受到限制，但我们可以利用上面的密度绘图器拼凑出一些东西：

```
# Compute and plot the mandlebrot set with the specified 2 dimensional range
# info.
def mandelhelp(xmin xmax xstep   ymin ymax ystep)
  for y = ymin, y < ymax, ystep in (
    (for x = xmin, x < xmax, xstep in
       printdensity(mandleconverge(x,y)))
    : putchard(10)
  )

# mandel - This is a convenient helper function for plotting the mandelbrot set
# from the specified position with the specified Magnification.
def mandel(realstart imagstart realmag imagmag)
  mandelhelp(realstart, realstart+realmag*78, realmag,
             imagstart, imagstart+imagmag*40, imagmag); 
```

有了这些，我们可以尝试绘制曼德勃罗集！让我们试一试：

```
ready> mandel(-2.3, -1.3, 0.05, 0.07);
*******************************+++++++++++*************************************
*************************+++++++++++++++++++++++*******************************
**********************+++++++++++++++++++++++++++++****************************
*******************+++++++++++++++++++++.. ...++++++++*************************
*****************++++++++++++++++++++++.... ...+++++++++***********************
***************+++++++++++++++++++++++.....   ...+++++++++*********************
**************+++++++++++++++++++++++....     ....+++++++++********************
*************++++++++++++++++++++++......      .....++++++++*******************
************+++++++++++++++++++++.......       .......+++++++******************
***********+++++++++++++++++++....                ... .+++++++*****************
**********+++++++++++++++++.......                     .+++++++****************
*********++++++++++++++...........                    ...+++++++***************
********++++++++++++............                      ...++++++++**************
********++++++++++... ..........                        .++++++++**************
*******+++++++++.....                                   .+++++++++*************
*******++++++++......                                  ..+++++++++*************
*******++++++.......                                   ..+++++++++*************
*******+++++......                                     ..+++++++++*************
*******.... ....                                      ...+++++++++*************
*******.... .                                         ...+++++++++*************
*******+++++......                                    ...+++++++++*************
*******++++++.......                                   ..+++++++++*************
*******++++++++......                                   .+++++++++*************
*******+++++++++.....                                  ..+++++++++*************
********++++++++++... ..........                        .++++++++**************
********++++++++++++............                      ...++++++++**************
*********++++++++++++++..........                     ...+++++++***************
**********++++++++++++++++........                     .+++++++****************
**********++++++++++++++++++++....                ... ..+++++++****************
***********++++++++++++++++++++++.......       .......++++++++*****************
************+++++++++++++++++++++++......      ......++++++++******************
**************+++++++++++++++++++++++....      ....++++++++********************
***************+++++++++++++++++++++++.....   ...+++++++++*********************
*****************++++++++++++++++++++++....  ...++++++++***********************
*******************+++++++++++++++++++++......++++++++*************************
*********************++++++++++++++++++++++.++++++++***************************
*************************+++++++++++++++++++++++*******************************
******************************+++++++++++++************************************
*******************************************************************************
*******************************************************************************
*******************************************************************************
Evaluated to 0.000000
ready> mandel(-2, -1, 0.02, 0.04);
**************************+++++++++++++++++++++++++++++++++++++++++++++++++++++
***********************++++++++++++++++++++++++++++++++++++++++++++++++++++++++
*********************+++++++++++++++++++++++++++++++++++++++++++++++++++++++++.
*******************+++++++++++++++++++++++++++++++++++++++++++++++++++++++++...
*****************+++++++++++++++++++++++++++++++++++++++++++++++++++++++++.....
***************++++++++++++++++++++++++++++++++++++++++++++++++++++++++........
**************++++++++++++++++++++++++++++++++++++++++++++++++++++++...........
************+++++++++++++++++++++++++++++++++++++++++++++++++++++..............
***********++++++++++++++++++++++++++++++++++++++++++++++++++........        .
**********++++++++++++++++++++++++++++++++++++++++++++++.............
********+++++++++++++++++++++++++++++++++++++++++++..................
*******+++++++++++++++++++++++++++++++++++++++.......................
******+++++++++++++++++++++++++++++++++++...........................
*****++++++++++++++++++++++++++++++++............................
*****++++++++++++++++++++++++++++...............................
****++++++++++++++++++++++++++......   .........................
***++++++++++++++++++++++++.........     ......    ...........
***++++++++++++++++++++++............
**+++++++++++++++++++++..............
**+++++++++++++++++++................
*++++++++++++++++++.................
*++++++++++++++++............ ...
*++++++++++++++..............
*+++....++++................
*..........  ...........
*
*..........  ...........
*+++....++++................
*++++++++++++++..............
*++++++++++++++++............ ...
*++++++++++++++++++.................
**+++++++++++++++++++................
**+++++++++++++++++++++..............
***++++++++++++++++++++++............
***++++++++++++++++++++++++.........     ......    ...........
****++++++++++++++++++++++++++......   .........................
*****++++++++++++++++++++++++++++...............................
*****++++++++++++++++++++++++++++++++............................
******+++++++++++++++++++++++++++++++++++...........................
*******+++++++++++++++++++++++++++++++++++++++.......................
********+++++++++++++++++++++++++++++++++++++++++++..................
Evaluated to 0.000000
ready> mandel(-0.9, -1.4, 0.02, 0.03);
*******************************************************************************
*******************************************************************************
*******************************************************************************
**********+++++++++++++++++++++************************************************
*+++++++++++++++++++++++++++++++++++++++***************************************
+++++++++++++++++++++++++++++++++++++++++++++**********************************
++++++++++++++++++++++++++++++++++++++++++++++++++*****************************
++++++++++++++++++++++++++++++++++++++++++++++++++++++*************************
+++++++++++++++++++++++++++++++++++++++++++++++++++++++++**********************
+++++++++++++++++++++++++++++++++.........++++++++++++++++++*******************
+++++++++++++++++++++++++++++++....   ......+++++++++++++++++++****************
+++++++++++++++++++++++++++++.......  ........+++++++++++++++++++**************
++++++++++++++++++++++++++++........   ........++++++++++++++++++++************
+++++++++++++++++++++++++++.........     ..  ...+++++++++++++++++++++**********
++++++++++++++++++++++++++...........        ....++++++++++++++++++++++********
++++++++++++++++++++++++.............       .......++++++++++++++++++++++******
+++++++++++++++++++++++.............        ........+++++++++++++++++++++++****
++++++++++++++++++++++...........           ..........++++++++++++++++++++++***
++++++++++++++++++++...........                .........++++++++++++++++++++++*
++++++++++++++++++............                  ...........++++++++++++++++++++
++++++++++++++++...............                 .............++++++++++++++++++
++++++++++++++.................                 ...............++++++++++++++++
++++++++++++..................                  .................++++++++++++++
+++++++++..................                      .................+++++++++++++
++++++........        .                               .........  ..++++++++++++
++............                                         ......    ....++++++++++
..............                                                    ...++++++++++
..............                                                    ....+++++++++
..............                                                    .....++++++++
.............                                                    ......++++++++
...........                                                     .......++++++++
.........                                                       ........+++++++
.........                                                       ........+++++++
.........                                                           ....+++++++
........                                                             ...+++++++
.......                                                              ...+++++++
                                                                    ....+++++++
                                                                   .....+++++++
                                                                    ....+++++++
                                                                    ....+++++++
                                                                    ....+++++++
Evaluated to 0.000000
ready> ^D 
```

此时，您可能开始意识到 Kaleidoscope 是一种真正而强大的语言。它可能不是自相似的 :), 但它可以用来绘制一些东西！

使用这个，我们结束了教程中的“添加用户定义运算符”章节。我们成功地扩展了我们的语言，在库中添加了扩展语言的能力，并展示了如何使用它来构建一个简单但有趣的端用户应用程序在 Kaleidoscope 中。在这一点上，Kaleidoscope 可以构建各种功能齐全的应用程序，并可以调用具有副作用的函数，但它实际上无法定义和改变一个变量本身。

引人注目的是，变量突变是一些语言的重要特性，如何在不必在前端添加“SSA 构造”阶段的情况下添加对可变变量的支持并不明显。在下一章中，我们将描述如何在前端中添加变量突变而不构建 SSA。
