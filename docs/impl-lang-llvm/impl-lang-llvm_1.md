# 词法分析器

# Kaleidoscope 语言及其词法分析器

# 1.1 基本语言

本教程将以一个我们将称之为“Kaleidoscope”的玩具语言来说明。Kaleidoscope 是一种过程化语言，允许您定义函数，使用条件语句，进行数学计算等。在教程的过程中，我们将扩展 Kaleidoscope 以支持 if/then/else 结构，for 循环，用户定义的操作符，具有简单命令行界面的 JIT 编译等。

由于我们希望保持简单，Kaleidoscope 中唯一的数据类型是 64 位浮点类型（在 C 中称为`double`）。因此，所有值都隐式为双精度，并且语言不需要类型声明。这使得语言具有非常好的简单语法。例如，以下简单示例计算斐波那契数列：

```
# Compute the x'th fibonacci number.
def fib(x)
  if x < 3 then
    1
  else
    fib(x-1)+fib(x-2)

# This expression will compute the 40th number.
fib(40) 
```

我们还允许 Kaleidoscope 调用标准库函数（LLVM JIT 使这完全微不足道）。这意味着您可以使用`extern`关键字在使用之前定义函数（这对于相互递归函数也很有用）。例如：

```
extern sin(arg);
extern cos(arg);
extern atan2(arg1 arg2);

atan2(sin(.4), cos(42)) 
```

在第六章中包含了一个更有趣的示例，我们编写了一个小的 Kaleidoscope 应用程序，以不同的放大级别显示曼德勃罗特集。

让我们深入了解这种语言的实现！

# 1.2 词法分析器

在实现语言时，首先需要的是处理文本文件并识别其内容的能力。传统的做法是使用“词法分析器”（也称为“扫描器”）将输入分解为“标记”。词法分析器返回的每个标记都包括一个标记代码和可能的一些元数据（例如数字的数值）。首先，我们定义可能性：

```
// The lexer returns tokens [0-255] if it is an unknown character, otherwise one
// of these for known things.
enum Token {
  tok_eof = -1,

  // commands
  tok_def = -2, tok_extern = -3,

  // primary
  tok_identifier = -4, tok_number = -5,
};

static std::string IdentifierStr;  // Filled in if tok_identifier
static double NumVal;              // Filled in if tok_number 
```

我们的词法分析器返回的每个标记要么是 Token 枚举值之一，要么是一个像`+`这样的‘未知’字符，以其 ASCII 值返回。如果当前标记是标识符，则 IdentifierStr 全局变量保存标识符的名称。如果当前标记是数值文字（例如 1.0），NumVal 保存其值。请注意，出于简单起见，我们使用全局变量，这不是实现真实语言的最佳选择 :)。

词法分析器的实际实现是一个名为 gettok 的单个函数。gettok 函数被调用以从标准输入返回下一个标记。其定义如下：

```
/// gettok - Return the next token from standard input.
static int gettok() {
  static int LastChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar))
    LastChar = getchar(); 
```

gettok 通过调用 C 的 getchar() 函数从标准输入逐个读取字符。它在识别字符时吞掉它们，并将上次读取但未处理的最后一个字符存储在 LastChar 中。它必须做的第一件事是忽略标记之间的空白。通过上面的循环完成这一点。

gettok 需要做的下一件事是识别标识符和特定关键字，例如`def`。Kaleidoscope 使用以下简单循环完成此操作：

```
if (isalpha(LastChar)) { // identifier: [a-zA-Z][a-zA-Z0-9]*
  IdentifierStr = LastChar;
  while (isalnum((LastChar = getchar())))
    IdentifierStr += LastChar;

  if (IdentifierStr == "def") return tok_def;
  if (IdentifierStr == "extern") return tok_extern;
  return tok_identifier;
} 
```

注意，每当词法分析器识别出一个标识符时，此代码会设置`IdentifierStr`全局变量。此外，由于语言关键字也是在同一个循环中匹配的，我们在此内联处理它们。数值也是类似的：

```
if (isdigit(LastChar) || LastChar == '.') {   // Number: [0-9.]+
  std::string NumStr;
  do {
    NumStr += LastChar;
    LastChar = getchar();
  } while (isdigit(LastChar) || LastChar == '.');

  NumVal = strtod(NumStr.c_str(), 0);
  return tok_number;
} 
```

这些代码都是用于处理输入的非常直接的代码。当从输入中读取数值时，我们使用 C 语言的 strtod 函数将其转换为我们存储在 NumVal 中的数值。请注意，这并没有进行足够的错误检查：它会错误地读取"1.23.45.67"并将其处理为你输入的"1.23"。欢迎扩展它 : )。接下来我们处理注释：

```
if (LastChar == '#') {
  // Comment until end of line.
  do LastChar = getchar();
  while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

  if (LastChar != EOF)
    return gettok();
} 
```

我们通过跳过到行尾来处理注释，然后返回下一个标记。最后，如果输入不匹配上述情况之一，那么它要么是一个操作符字符，如`+`，要么是文件的结尾。这些情况会用以下代码处理：

```
 // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF)
    return tok_eof;

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  LastChar = getchar();
  return ThisChar;
} 
```

有了这些，我们就有了基本 Kaleidoscope 语言的完整词法分析器（词法分析器的完整代码清单在本教程的下一章节中提供）。接下来，我们将构建一个简单的解析器，使用它来构建一个抽象语法树。当我们完成后，我们将包含一个驱动程序，这样你就可以同时使用词法分析器和解析器。
