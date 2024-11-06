# 第七章。输入和输出

所有的输入和输出操作都是通过*端口*执行的。端口是指向（可能是无限的）数据流（通常是文件）的指针，是程序可以从流中提取字节或字符或将字节或字符放入流中的开口。端口可以是输入端口、输出端口或同时是两者。

端口是 Scheme 中的一等对象，就像任何其他对象一样。与过程一样，端口没有像字符串和数字那样的打印表示。最初有三个端口：当前输入端口、当前输出端口和当前错误端口，它们是连接到进程标准输入、标准输出和标准错误流的文本端口。提供了几种打开新端口的方法。

输入端口通常指向有限流，例如，存储在磁盘上的输入文件。如果输入操作中的一个，例如，`get-u8`、`get-char`或`get-datum`，被要求从已经到达有限流末尾的端口读取时，它会返回一个特殊的*eof*（文件结束）*对象*。谓词`eof-object?`可以用来确定从输入操作返回的值是否是 eof 对象。

端口可以是*二进制*或*文本*。二进制端口允许程序从底层流中读取或写入 8 位无符号字节，或“八位字节”，文本端口允许程序读取或写入字符。

在许多情况下，底层流被组织为一系列字节，但这些字节应被视为字符的编码。在这种情况下，可以使用*转码器*创建文本端口来将字节解码为字符（用于输入）或将字符编码为字节（用于输出）。转码器封装了一个确定字符如何表示为字节的*编解码器*。提供了三种标准编解码器：*latin-1*编解码器，Unicode *utf-8*编解码器和 Unicode *utf-16*编解码器。对于*latin-1*编码，每个字符由一个字节表示。对于*utf-8*，每个字符由一个到四个字节表示，对于*utf-16*，每个字符由两个或四个字节表示。

转码器还封装了一个确定如何识别行尾的*eol 样式*。如果 eol 样式是`none`，则不识别行尾。另外提供了六种标准 eol 样式，如下所示：

| `lf`: | 换行符字符 |
| --- | --- |
| `cr`: | 回车字符 |
| `nel`: | Unicode 下一行字符 |
| `ls`: | Unicode 换行符字符 |
| `crlf`: | 回车后跟换行，并 |
| `crnel`: | 回车后跟下一行 |

换行样式会对输入和输出操作产生不同影响。对于输入而言，除了 `none` 外的任何换行样式都会导致每个换行字符或两个字符序列被转换为一个换行字符。对于输出而言，除了 `none` 外的任何换行样式都会导致换行字符被转换为与换行样式关联的特定的一个或两个字符序列。在输入方向上，除了 `none` 外的所有换行样式都是等效的，而在输出方向上，换行样式 `none` 和 `lf` 是等效的。

除了编解码器和换行样式外，转码器还封装了另一个信息：一个 *错误处理模式*，用于确定在发生解码或编码错误时会发生什么，即如果一个字节序列无法在输入方向上用封装的编解码器转换为字符，或者一个字符无法在输出方向上用封装的编解码器转换为字节序列。错误处理模式是 `ignore`、`raise` 或 `replace`。如果错误处理模式是 `ignore`，则会忽略有问题的字节序列或字符。如果错误处理模式是 `raise`，则会引发一个带有 `i/o-decoding` 或 `i/o-encoding` 条件类型的异常；在输入方向上，端口会被定位到字节序列之后。如果错误处理模式是 `replace`，则会产生一个替换字符或字符编码：在输入方向上，替换字符是 U+FFFD，而在输出方向上，替换字符是 `utf-8` 和 `utf-16` 编解码器的编码或者 `latin-1` 编解码器的问号字符 ( ? ) 的编码。

为了提高效率，可以对端口进行缓冲，以消除每个字节或字符调用操作系统的开销。支持三种标准的缓冲模式：*block*、*line* 和 *none*。使用块缓冲时，输入从流中获取，输出以一些与实现相关的大小的块发送到流中。使用行缓冲时，缓冲是基于行或其他某种与实现相关的基础进行的。行缓冲通常仅对文本输出端口进行区分；在二进制端口中没有行分隔，输入可能会在流中可用时获取。使用无缓冲区模式时，不进行缓冲，因此输出立即发送到流中，并且只有在需要时才获取输入。

本章的其余部分涵盖了对转码器、文件端口、标准端口、字符串和字节向量端口、自定义端口、一般端口操作、输入操作、输出操作、便捷 I/O、文件系统操作以及字节向量和字符串之间的转换的操作。

### 第 7.1 节。转码器

如上所述，转码器封装了三个值：编解码器、换行样式和错误处理模式。本节描述了创建或操作转码器以及转码器封装的值的过程。

**procedure**: `(make-transcoder *codec*)`

**procedure**: `(make-transcoder *codec* *eol-style*)`

**procedure**: `(make-transcoder *codec* *eol-style* *error-handling-mode*)`

**returns:** 封装了 `*codec*`、`*eol-style*` 和 `*error-handling-mode*` 的转码器

**libraries:** `(rnrs io ports)`, `(rnrs)`

`*eol-style*` 必须是有效的 eol-style 符号之一（`lf`、`cr`、`nel`、`ls`、`crlf`、`crnel` 或 `none`）；它默认为平台的本机 eol 样式。`*error-handling-mode*` 必须是有效的错误处理模式符号（`ignore`、`raise` 或 `replace`）并默认为 `replace`。

**procedure**: `(transcoder-codec *transcoder*)`

**returns:** 以 `*transcoder*` 封装的编解码器

**procedure**: `(transcoder-eol-style *transcoder*)`

**returns:** 以 `*transcoder*` 封装的 eol-style 符号

**procedure**: `(transcoder-error-handling-mode *transcoder*)`

**returns:** 以 `*transcoder*` 封装的错误处理模式符号

**libraries:** `(rnrs io ports)`, `(rnrs)`

**procedure**: `(native-transcoder)`

**returns:** 本机转码器

**libraries:** `(rnrs io ports)`, `(rnrs)`

本机编解码器是实现相关的，可能会因平台或语言环境而异。

**procedure**: `(latin-1-codec)`

**returns:** 用于 ISO 8859-1（Latin 1）字符编码的编解码器

**procedure**: `(utf-8-codec)`

**returns:** 用于 Unicode UTF-8 字符编码的编解码器

**procedure**: `(utf-16-codec)`

**returns:** 用于 Unicode UTF-16 字符编码的编解码器

**libraries:** `(rnrs io ports)`, `(rnrs)`

**syntax**: `(eol-style *symbol*)`

**returns:** `*symbol*`

**libraries:** `(rnrs io ports)`, `(rnrs)`

`*symbol*` 必须是 `lf`、`cr`、`nel`、`ls`、`crlf`、`crnel` 或 `none` 符号之一。表达式 `(eol-style *symbol*)` 等同于 `(quote *symbol*)`，除了前者在扩展时检查 `*symbol*` 是否为 eol-style 符号之外。`eol-style` 语法还提供了有用的文档。

`(eol-style crlf) ![<graphic>](img/ch2_0.gif) crlf

(eol-style lfcr) ![<graphic>](img/ch2_0.gif) *syntax violation*`

**procedure**: `(native-eol-style)`

**returns:** 本机 eol 样式

**libraries:** `(rnrs io ports)`, `(rnrs)`

本机 eol 样式是实现相关的，可能会因平台或语言环境而异。

**syntax**: `(error-handling-mode *symbol*)`

**returns:** `*symbol*`

**libraries:** `(rnrs io ports)`, `(rnrs)`

`*symbol*` 必须是 `ignore`、`raise` 或 `replace` 符号之一。表达式 `(error-handling-mode *symbol*)` 等同于 `(quote *symbol*)`，除了前者在扩展时检查 `*symbol*` 是否为错误处理模式符号之外。`error-handling-mode` 语法还提供了有用的文档。

`(error-handling-mode replace) ![<graphic>](img/ch2_0.gif) replace

`(error-handling-mode replace) ![<graphic>](img/ch2_0.gif) *syntax violation*`

### 第 7.2 节。打开文件

本节中的程序用于打开文件端口。用于打开其他类型的端口（例如字符串端口或自定义端口）的程序在随后的部分中描述。

每个文件打开操作都接受一个 `*path*` 参数，该参数指定要打开的文件。它必须是一个字符串或其他一些实现相关的值，指定了一个文件的名称。

一些文件打开程序接受可选的 `*options*`、`*b-mode*` 和 `*?transcoder*` 参数。`*options*` 必须是一个枚举集，包含了下面描述的有效文件选项符号，并且默认值为 `(file-options)` 的值。`*b-mode*` 必须是下面描述的有效缓冲区模式，并且默认为 `block`。`*?transcoder*` 必须是一个转码器或 `#f`；如果它是一个转码器，则打开操作返回底层二进制文件的转码端口，而如果它是 `#f`（默认值），则打开操作返回二进制端口。

本节中创建的二进制端口支持 `port-position` 和 `set-port-position!` 操作。由本节中的程序创建的文本端口是否支持这些操作是依赖于实现的。

**语法：** `(file-options *symbol* ...)`

**返回值：** 文件选项枚举集

**库：** `(rnrs io ports)`，`(rnrs)`

文件选项枚举集可以传递给文件打开操作，以控制打开操作的各个方面。有三个标准文件选项：`no-create`、`no-fail` 和 `no-truncate`，它们仅影响创建输出（包括输入/输出）端口的文件打开操作。

默认文件选项，即 `(file-options)` 的值，在程序尝试打开文件进行输出时，如果文件已经存在，则引发 `i/o-file-already-exists` 条件类型的异常，并且如果文件不存在，则创建该文件。如果包括 `no-fail` 选项，则如果文件已经存在，则不会引发异常；相反，文件会被打开并截断为零长度。如果包括 `no-create` 选项，则如果文件不存在，则不会创建该文件；相反，会引发 `i/o-file-does-not-exist` 条件类型的异常。`no-create` 选项暗示了 `no-fail` 选项。`no-truncate` 选项仅在包括或隐含了 `no-fail` 选项时相关，此时如果打开了现有文件，则不会将其截断，但端口的位置仍然设置为文件的开头。

或许更容易想象默认文件选项是虚构的选项符号 `create`、`fail-if-exists` 和 `truncate`；`no-create` 移除 `create`，`no-fail` 移除 `fail-if-exists`，而 `no-truncate` 移除 `truncate`。

实现可能支持其他文件选项符号。例如，Chez Scheme 支持控制文件是否或应该被压缩、文件是否被锁定以进行独占访问以及如果创建文件，则给予文件什么权限的选项[9]。

**语法：** `(buffer-mode *符号*)`

**返回：** `*符号*`

**库：** `(rnrs io ports)`, `(rnrs)`

`*符号*`必须是`block`、`line`或`none`中的一个符号。表达式`(buffer-mode *符号*)`等价于表达式`(quote *符号*)`，但前者在扩展时检查`*符号*`是否是缓冲区模式符号之一。`buffer-mode`语法还提供了有用的文档。

`(buffer-mode block) ![<图形>](img/ch2_0.gif) block`

(buffer-mode cushion) ![<图形>](img/ch2_0.gif) *语法违规*

**语法：** `(buffer-mode? *obj*)`

**返回：** 如果`*obj*`是有效的缓冲区模式，则返回`#t`，否则返回`#f`

**库：** `(rnrs io ports)`, `(rnrs)`

`(buffer-mode? 'block) ![<图形>](img/ch2_0.gif) #t

(buffer-mode? 'line) ![<图形>](img/ch2_0.gif) #t

(buffer-mode? 'none) ![<图形>](img/ch2_0.gif) #t

(buffer-mode? 'something-else) ![<图形>](img/ch2_0.gif) #f`

**过程：** `(open-file-input-port *路径*)`

**过程：** `(open-file-input-port *路径* *选项*)`

**过程：** `(open-file-input-port *路径* *选项* *b-模式*)`

**过程：** `(open-file-input-port *路径* *选项* *b-模式* *?编码转换器*)`

**返回：** 命名文件的新的输入端口

**库：** `(rnrs io ports)`, `(rnrs)`

如果`*?编码转换器*`存在且不为`#f`，则它必须是一个编码转换器，并且此过程返回一个其编码转换器为`*?编码转换器*`的文本输入端口。否则，此过程返回一个二进制输入端口。有关其他参数的约束和效果的描述，请参阅本节的导言。

**过程：** `(open-file-output-port *路径*)`

**过程：** `(open-file-output-port *路径* *选项*)`

**过程：** `(open-file-output-port *路径* *选项* *b-模式*)`

**过程：** `(open-file-output-port *路径* *选项* *b-模式* *?编码转换器*)`

**返回：** 命名文件的新的输出端口

**库：** `(rnrs io ports)`, `(rnrs)`

如果`*?编码转换器*`存在且不为`#f`，则它必须是一个编码转换器，并且此过程返回一个其编码转换器为`*?编码转换器*`的文本输出端口。否则，此过程返回一个二进制输出端口。有关其他参数的约束和效果的描述，请参阅本节的导言。

**过程：** `(open-file-input/output-port *路径*)`

**过程：** `(open-file-input/output-port *路径* *选项*)`

**过程：** `(open-file-input/output-port *路径* *选项* *b-模式*)`

**过程：** `(open-file-input/output-port *路径* *选项* *b-模式* *?编码转换器*)`

**返回：** 命名文件的新的输入/输出端口

**库：** `(rnrs io ports)`, `(rnrs)`

如果`*?transcoder*`存在且不为`#f`，则必须是一个转码器，此过程返回其转码器为`*?transcoder*`的文本输入/输出端口。否则，此过程返回一个二进制输入/输出端口。有关其他参数的约束和效果的描述，请参见本节的导言。

### 第 7.3 节。标准端口

本节中描述的过程返回连接到进程的标准输入、标准输出和标准错误流的端口。第一组返回具有实现相关的转码器（如果有）和缓冲模式的“现成”文本端口。第二组创建新的二进制端口，可以用于二进制输入/输出，或者借助`transcoded-port`进行文本输入/输出，使用程序提供的转码器和缓冲模式。

**procedure**: `(current-input-port)`

**returns:** 当前的输入端口

**procedure**: `(current-output-port)`

**returns:** 当前的输出端口

**procedure**: `(current-error-port)`

**returns:** 当前的错误端口

**libraries:** `(rnrs io ports)`, `(rnrs io simple)`, `(rnrs)`

current-input、current-output 和 current-error 端口返回预先构建的文本端口，最初与进程的标准输入、标准输出和标准错误流相关联。

`current-input-port`和`current-output-port`返回的值可以通过方便的 I/O 过程`with-input-from-file`和`with-output-to-file`（第 7.9 节）暂时更改。

**procedure**: `(standard-input-port)`

**returns:** 一个连接到标准输入流的新的二进制输入端口

**procedure**: `(standard-output-port)`

**returns:** 一个连接到标准输出流的新的二进制输出端口

**procedure**: `(standard-error-port)`

**returns:** 一个连接到标准错误流的新的二进制输出端口

**libraries:** `(rnrs io ports)`, `(rnrs)`

因为端口可能被缓冲，如果对连接到进程的标准流之一的多个端口进行交错操作，可能会导致混乱。因此，这些过程通常只适用于程序不再需要使用连接到标准流的任何现有端口时。

### 第 7.4 节。字符串和字节向量端口

本节中的过程允许字节向量和字符串用作输入或输出流。

本节中的过程创建的二进制端口支持`port-position`和`set-port-position!`操作。由本节中的过程创建的文本端口是否支持这些操作取决于实现。

**procedure**: `(open-bytevector-input-port *bytevector*)`

**procedure**: `(open-bytevector-input-port *bytevector* *?transcoder*)`

**returns:** 一个从`*bytevector*`获取输入的新的输入端口

**libraries:** `(rnrs io ports)`, `(rnrs)`

如果`*?transcoder*`存在且不是`#f`，它必须是一个转码器，此过程返回其转码器为`*?transcoder*`的文本输入端口。否则，此过程返回一个二进制输入端口。

调用此过程后修改`*bytevector*`的效果未指定。

`(let ([ip (open-bytevector-input-port #vu8(1 2))])

`(let* ([x1 (get-u8 ip)] [x2 (get-u8 ip)] [x3 (get-u8 ip)])

(list x1 x2 (eof-object? x3)))) ![<graphic>](img/ch2_0.gif) (1 2 #t)`

无需关闭字节向量端口；当不再需要时，其存储将自动回收，就像任何其他对象一样，并且打开的字节向量端口不会占用任何操作系统资源。

**过程**：`(open-string-input-port *string*)`

**返回**：从`*string*`获取输入的新文本输入端口

**库：**`(rnrs io ports)`，`(rnrs)`

调用此过程后修改`*string*`的效果未指定。新端口可能有也可能没有转码器，如果有，转码器是实现相关的。虽然不是必需的，但鼓励实现支持字符串端口的`port-position`和`set-port-position!`。

`(get-line (open-string-input-port "hi.\nwhat's up?\n")) ![<graphic>](img/ch2_0.gif) "hi."`

无需关闭字符串端口；当不再需要时，其存储将自动回收，就像任何其他对象一样，并且打开的字符串端口不会占用任何操作系统资源。

**过程**：`(open-bytevector-output-port)`

**过程**：`(open-bytevector-output-port *?transcoder*)`

**返回**：两个值，一个新的输出端口和一个提取过程

**库：**`(rnrs io ports)`，`(rnrs)`

如果`*?transcoder*`存在且不是`#f`，它必须是一个转码器，端口值是其转码器为`*?transcoder*`的文本输出端口。否则，端口值是一个二进制输出端口。

提取过程是一个过程，当无参数调用时，创建一个包含端口中累积字节的字节向量，清除端口的累积字节，将其位置重置为零，并返回字节向量。累积的字节包括任何写入超出当前位置的字节，如果位置已从其最大范围设置回来。

`(let-values ([(op g) (open-bytevector-output-port)])

(put-u8 op 15)

(put-u8 op 73)

(put-u8 op 115)

(set-port-position! op 2)

(let ([bv1 (g)])

(put-u8 op 27)

(list bv1 (g)))) ![<graphic>](img/ch2_0.gif) (#vu8(15 73 115) #vu8(27))`

无需关闭字节向量端口；当不再需要时，其存储将自动回收，就像任何其他对象一样，并且打开的字节向量端口不会占用任何操作系统资源。

**过程**：`(open-string-output-port)`

**返回**：两个值，一个新的文本输出端口和一个提取过程

**库：**`(rnrs io ports)`，`(rnrs)`

提取过程是一个过程，当无参数调用时，将创建一个包含端口中累积字符的字符串，清除端口的累积字符，将其位置重置为零，并返回字符串。如果位置已从其最大范围设置回来，则累积字符包括写在当前位置之外的任何字符。虽然不是必需的，但鼓励实现支持字符串端口的`port-position`和`set-port-position!`。

（让-值（（`op` `g`）（打开字符串输出端口））

（放置字符串`op` "一些数据"）

（让）`[str1]`是`g`）

（放置字符串`op` "新东西")

（列出`str1` `g`）![<graphic>](img/ch2_0.gif)（"一些数据" "新东西"）

不需要关闭字符串端口；当不再需要时，其存储将自动回收，就像任何��他对象一样，并且打开的字符串端口不会占用任何操作系统资源。

**过程**：`(call-with-bytevector-output-port *procedure*)`

**过程**：`(call-with-bytevector-output-port *procedure* *?transcoder*)`

**返回**：包含累积字节的字节向量

**库**：`（rnrs io ports）`，`（rnrs）`

如果`*?transcoder*`存在且不是`#f`，它必须是一个转码器，并且将使用带有文本字节向量输出端口的转码器`*?transcoder*`调用`*procedure*`。否则，将使用二进制字节向量输出端口调用`*procedure*`。如果`*procedure*`返回，将创建一个包含端口中累积字节的字节向量，清除端口中的累积字节，将端口位置重置为零，并从`call-with-bytevector-output-port`返回字节向量。这些操作每次`*procedure*`返回时发生，如果由于在`*procedure*`活动时创建的延续调用而多次返回。

（让）`[tx]`（制作转码器（latin-1-codec）（eol-style lf）

（错误处理模式替换））]

(调用带字节向量输出端口的过程

（lambda（p）（放置字符串`p` "abc"）

tx）![<graphic>](img/ch2_0.gif) #vu8（97 98 99）

**过程**：`(call-with-string-output-port *procedure*)`

**返回**：包含累积字符的字符串

**库**：`（rnrs io ports）`，`（rnrs）`

`*procedure*`被调用时带有一个参数，即一个字符串输出端口。如果`*procedure*`返回，将创建一个包含端口中累积字符的字符串，清除端口中的累积字符，将端口位置重置为零，并从`call-with-string-output-port`返回字符串。这些操作每次`*procedure*`返回时发生，如果由于在`*procedure*`活动时创建的延续调用而多次返回。

`call-with-string-output-port`可以与`put-datum`一起使用来定义一个过程`object->string`，该过程返回包含对象的打印表示的字符串。

（定义）`（object->string x）

（调用带字符串输出端口

（lambda（p）（放置数据`p` `x`））

(object->string (cons 'a '(b c))) ![<graphic>](img/ch2_0.gif) "(a b c)"

### 第 7.5 节。打开自定义端口

**procedure**: `(make-custom-binary-input-port *id* *r!* *gp* *sp!* *close*)`

**returns:** 一个新的自定义二进制输入端口

**procedure**: `(make-custom-binary-output-port *id* *w!* *gp* *sp!* *close*)`

**returns:** 一个新的自定义二进制输出端口

**procedure**: `(make-custom-binary-input/output-port *id* *r!* *w!* *gp* *sp!* *close*)`

**returns:** 一个新的自定义二进制输入/输出端口

**libraries:** `(rnrs io ports)`, `(rnrs)`

这些过程允许程序从任意字节流创建端口。`*id*`必须是一个命名新端口的字符串；该名称仅用于信息目的，并且实现可以选择在自定义端口的打印语法（如果有）中包含它。`*r!*`和`*w!*`必须是过程，而`*gp*`，`*sp!*`和`*close*`必须是过程或`#f`。下面描述了这些参数。

`*r!*`

被调用以从自定义端口获取输入，例如，支持`get-u8`或`get-bytevector-n`。它被调用时带有三个参数：`*bytevector*`，`*start*`和`*n*`。`*start*`将是一个非负的精确整数，`*n*`将是一个正的精确整数，并且`*start*`和`*n*`的和不会超过`*bytevector*`的长度。如果字节流已到达文件末尾，`*r!*`应返回精确的 0。否则，它应该从流中读取至少一个字节，最多`*n*`个字节，将这些字节存储在`*bytevector*`的连续位置中，从`*start*`开始，并返回实际读取的字节数，作为一个精确的正整数。

`*w!*`

被调用以向端口发送输出，例如，支持`put-u8`或`put-bytevector`。它被调用时带有三个参数：`*bytevector*`，`*start*`和`*n*`。`*start*`和`*n*`将是非负的精确整数，并且`*start*`和`*n*`的和不会超过`*bytevector*`的长度。`*w!*`应该从`*bytevector*`的`*start*`位置开始写入最多`*n*`个连续字节，并返回实际写入的字节数，作为一个精确的非负整数。

`*gp*`

被调用以查询端口的位置。如果是`#f`，则端口不支持`port-position`。如果不是`#f`，则将传递零个参数，并应返回当前位置，作为从字节流开始的位移（以精确的非负整数表示）。

`*sp!*`

被调用以设置端口的位置。如果是`#f`，则端口不支持`set-port-position!`。如果不是`#f`，则将传递一个参数，一个表示从字节流开始的位移的精确非负整数，它应将位置设置为此值。

`*close*`

被调用以关闭字节流。如果是`#f`，则在关闭新端口时不会采取任何操作来关闭字节流。如果不是`#f`，则将传递零个参数，并应采取必要的操作来关闭字节流。

如果新端口是输入/输出端口，并且没有提供`*gp*`或`*sp!*`过程，那么如果在输入操作之后发生输出操作，实现可能无法正确定位端口，因为必须进行输入缓冲以支持`lookahead-u8`，通常也为了效率而这样做。出于同样的原因，如果没有提供`*sp!*`过程，那么在输入操作之后调用`port-position`可能不会返回准确的位置。因此，通常应该为创建自定义二进制输入/输出端口的程序提供`*gp*`和`*sp!*`过程。

**过程**：`(make-custom-textual-input-port *id* *r!* *gp* *sp!* *close*)`

**返回**：一个新的自定义文本输入端口

**过程**：`(make-custom-textual-output-port *id* *w!* *gp* *sp!* *close*)`

**返回**：一个新的自定义文本输出端口

**过程**：`(make-custom-textual-input/output-port *id* *r!* *w!* *gp* *sp!* *close*)`

**返回**：一个新的自定义文本输入/输出端口

**库**：`(rnrs io ports)`，`(rnrs)`

这些过程允许程序从任意字符流创建端口。`*id*`必须是命名新端口的字符串；该名称仅用于信息目的，如果有的话，实现可以选择将其包含在自定义端口的打印语法中。`*r!*`和`*w!*`必须是过程，而`*gp*`，`*sp!*`和`*close*`必须是过程或`#f`。下面描述了这些参数。

`*r!*`

用于从端口中提取输入，例如，支持`get-char`或`get-string-n`。它接受三个参数：`*string*`，`*start*`和`*n*`。`*start*`将是非负确切整数，`*n*`将是正确切整数，并且`*start*`和`*n*`的总和不会超过`*string*`的长度。如果字符流已到达文件末尾，`*r!*`应返回确切的 0。否则，它应该从流中读取至少一个字符，最多`*n*`个字符，将这些字符存储在从`*start*`开始的`*string*`的连续位置，并返回实际读取的字符数作为确切的正整数。

`*w!*`

用于向端口发送输出，例如，支持`put-char`或`put-string`。它接受三个参数：`*string*`，`*start*`和`*n*`。`*start*`和`*n*`将是非负确切整数，并且`*start*`和`*n*`的总和不会超过`*string*`的长度。`*w!*`应该从`*start*`开始的`*string*`中写入最多`*n*`个连续字符，并返回实际写入的字符数作为确切的非负整数。

`*gp*`

用于查询端口的位置。如果是`#f`，端口将不支持`port-position`。如果不是`#f`，将传递零个参数，并应返回当前位置，这可能是任意值。

`*sp!*`

被调用以设置端口的位置。如果为`#f`，则端口将不支持`set-port-position!`。如果不是`#f`，则将传递一个参数`*pos*`，表示新位置的值。如果`*pos*`是先前调用`*gp*`的结果，则`*sp!*`应将位置设置为`*pos*`。

`*close*`

被调用以关闭字符流。如果为`#f`，则在关闭新端口时不会执行任何操作以关闭字符流。如果不是`#f`，则将传递零个参数，并应执行必要的操作以关闭字符流。

如果新端口是输入/输出端口，则在输入操作之后发生输出操作时，即使提供了`*gp*`和`*sp!*`过程，由于必须进行支持`lookahead-char`的输入缓冲，甚至为了效率而经常进行的输入缓冲，实现可能无法正确定位端口。由于端口位置的表示未指定，因此实现无法调整`*gp*`返回值以考虑缓冲字符的数量。出于同样的原因，即使提供了`*sp!*`过程，输入操作后调用`port-position`可能不会返回准确的位置。

然而，如果将位置重置到起始位置后，应该可以可靠地执行输出。因此，创建自定义文本输入/输出端口的程序通常应提供`*gp*`和`*sp!*`两种过程，这些端口的使用者在进行任何输入操作之前应通过`port-position`获取起始位置，并在进行任何输出操作之前将位置重置回起始位置。

### 第 7.6 节。端口操作

本节描述了一系列与端口相关的操作，这些操作不直接涉及从端口读取或写入。输入和输出操作在后续章节中描述。

**procedure**: `(port? *obj*)`

**returns:** 如果`*obj*`是端口，则返回`#t`，否则返回`#f`

**libraries:** `(rnrs io ports)`，`(rnrs)`

**procedure**: `(input-port? *obj*)`

**returns:** 如果`*obj*`是输入或输入/输出端口，则返回`#t`，否则返回`#f`

**procedure**: `(output-port? *obj*)`

**returns:** 如果`*obj*`是输出或输入/输出端口，则返回`#t`，否则返回`#f`

**libraries:** `(rnrs io ports)`，`(rnrs io simple)`，`(rnrs)`

**procedure**: `(binary-port? *obj*)`

**returns:** 如果`*obj*`是二进制端口，则返回`#t`，否则返回`#f`

**procedure**: `(textual-port? *obj*)`

**returns:** 如果`*obj*`是文本端口，则返回`#t`，否则返回`#f`

**libraries:** `(rnrs io ports)`，`(rnrs)`

**procedure**: `(close-port *port*)`

**returns:** 未指定

**libraries:** `(rnrs io ports)`，`(rnrs)`

如果`*port*`尚未关闭，`close-port`将关闭它，首先将任何缓冲的字节或字符刷新到底层流（如果端口是输出端口）。一旦关闭了端口，就无法对该端口执行更多的输入或输出操作。因为操作系统可能会对同时打开的文件端口数设置限制，或者限制对打开文件的访问，所以最好关闭任何不再用于输入或输出的文件端口。如果端口是输出端口，则显式关闭端口还确保缓冲数据被写入底层流。一些 Scheme 实现在程序无法访问文件端口或 Scheme 程序退出后会自动关闭文件端口，但最好在可能的情况下显式关闭文件端口。关闭已经关闭的端口不会产生任何效果。

**procedure**: `(transcoded-port *binary-port* *transcoder*)`

**returns:** 具有与`*binary-port*`相同字节流的新文本端口

**libraries:** `(rnrs io ports)`，`(rnrs)`

此过程返回一个具有转码器`*transcoder*`和与`*binary-port*`相同的底层字节流的新文本端口，定位在`*binary-port*`的当前位置。

作为创建文本端口的副作用，关闭`*binary-port*`以防止对`*binary-port*`的读写操作干扰新文本端口上的读写操作。然而，底层字节流仍然保持打开状态，直到关闭文本端口为止。

**procedure**: `(port-transcoder *port*)`

**returns:** 如果有的话，返回与`*port*`关联的转码器，否则返回`#f`。

**libraries:** `(rnrs io ports)`，`(rnrs)`

对于二进制端口，此过程始终返回`#f`，对于某些文本端口可能返回`#f`。

**procedure**: `(port-position *port*)`

**returns:** 端口的当前位置

**procedure**: `(port-has-port-position? *port*)`

**returns:** 如果端口支持`port-position`，则返回`#t`，否则返回`#f`。

**libraries:** `(rnrs io ports)`，`(rnrs)`

一个端口可以允许查询以确定其在底层字节流或字符流中的当前位置。如果是这样，那么过程`port-has-port-position?`返回`#t`，而`port-position`返回当前位置。对于二进制端口，位置始终是从字节流的开头的精确非负整数字节偏移。对于文本端口，位置的表示未指定；它可能不是精确的非负整数，即使是，它也可能不代表底层流中的字节或字符偏移。稍后可能会使用位置重置位置，如果端口支持`set-port-position!`。如果在不支持它的端口上调用`port-position`，则会引发带有条件类型`&assertion`的异常。

**procedure**: `(set-port-position! *port* *pos*)`

**returns:** 未指定

**procedure**: `(port-has-set-port-position!? *port*)`

**returns:** 如果端口支持`set-port-position!`则返回`#t`，否则返回`#f`

**libraries:** `(rnrs io ports)`, `(rnrs)`

一个端口可以允许将其当前位置直接移动到字节流或字符流的不同位置。如果是这样，过程`port-has-set-port-position!?`返回`#t`，并且`set-port-position!`改变当前位置。对于二进制端口，位置`*pos*`必须是从字节流开始的精确非负整数位移。对于文本端口，位置的表示是未指定的，如上面的`port-position`条目中所述，但`*pos*`必须是文本端口的适当位置，通常只有在从同一端口调用`port-position`时才能保证。如果在不支持的端口上调用`set-port-position!`，则会引发条件类型为`&assertion`的异常。

如果`*port*`是一个二进制输出端口，并且位置设置超出了底层流中当前数据的末尾，直到在该位置写入新数据，流才会被扩展。如果在该位置写入新数据，则每个中间位置的内容是未指定的。使用`open-file-output-port`和`open-file-input/output-port`创建的二进制端口始终可以在底层操作系统的限制范围内以这种方式扩展。在其他情况下，尝试将端口设置到底层对象中当前数据的末尾可能会导致异常，条件类型为`&i/o-invalid-position`。

**procedure**: `(call-with-port *port* *procedure*)`

**returns:** `*procedure*`返回的值

**libraries:** `(rnrs io ports)`, `(rnrs)`

`call-with-port`使用`*port*`作为唯一参数调用`*procedure*`。如果`*procedure*`返回，`call-with-port`关闭端口并返回`*procedure*`返回的值。

`call-with-port` 不会在外部调用`*procedure*`时自动关闭端口，因为可能会在稍后调用在`*procedure*`内部创建的另一个续体，将控制返回给`*procedure*`。如果`*procedure*`没有返回，实现可以自由地关闭端口，只要能证明输出端口不再可访问。

下面的示例将 infile 的内容复制到 outfile，如果 outfile 存在则覆盖。除非发生错误，在复制完成后关闭端口。

`(call-with-port (open-file-input-port "infile" (file-options)

(buffer-mode block) (native-transcoder))

(lambda (ip)

(call-with-port (open-file-output-port "outfile"

(file-options no-fail)

(buffer-mode block)

(native-transcoder))

(lambda (op)

(do ([c (get-char ip) (get-char ip)])

((eof-object? c))

(put-char op c))))))`

`call-with-port`的定义在第 135 页上。

**procedure**: `(output-port-buffer-mode *port*)`

**returns:** 代表`*port*`的缓冲区模式的符号

**libraries:** `(rnrs io ports)`, `(rnrs)`

### 第 7.7 节 输入操作

本节描述了主要目的是从输入端口读取数据的过程，以及用于识别或创建文件末尾（eof）对象的相关过程。

**procedure**: `(eof-object? *obj*)`

**returns:** 如果`*obj*`是 eof 对象，则返回`#t`，否则返回`#f`

**libraries:** `(rnrs io ports)`, `(rnrs io simple)`, `(rnrs)`

输入操作返回文件末尾对象，例如，当输入端口已达到输入末尾时，`get-datum`等。

**procedure**: `(eof-object)`

**returns:** eof 对象

**libraries:** `(rnrs io ports)`, `(rnrs io simple)`, `(rnrs)`

`(eof-object? (eof-object)) ![<graphic>](img/ch2_0.gif) #t`

**procedure**: `(get-u8 *binary-input-port*)`

**returns:** 从`*binary-input-port*`中获取下一个字节，或 eof 对象

**libraries:** `(rnrs io ports)`, `(rnrs)`

如果`*binary-input-port*`在文件末尾，将返回 eof 对象。否则，下一个可用的字节将作为无符号 8 位数量返回，即小于或等于 255 的精确无符号整数，并且端口的位置将向前移动一个字节。

**procedure**: `(lookahead-u8 *binary-input-port*)`

**returns:** 从`*binary-input-port*`中获取下一个字节，或 eof 对象

**libraries:** `(rnrs io ports)`, `(rnrs)`

如果`*binary-input-port*`在文件末尾，将返回 eof 对象。否则，下一个可用的字节将作为无符号 8 位数量返回，即小于或等于 255 的精确无符号整数。与`get-u8`相反，`lookahead-u8`不会消耗从端口读取的字节，因此如果端口的下一个操作是调用`lookahead-u8`或`get-u8`，则将返回相同的字节。

**procedure**: `(get-bytevector-n *binary-input-port* *n*)`

**returns:** 包含最多`*n*`个字节的非空字节向量，或 eof 对象

**libraries:** `(rnrs io ports)`, `(rnrs)`

`*n*`必须是一个精确的非负整数。如果`*binary-input-port*`在文件末尾，将返回 eof 对象。否则，`get-bytevector-n`读取（就像使用`get-u8`一样）尽可能多的字节，最多达到`*n*`，在端口到达文件末尾之前可用，并返回一个包含这些字节的新（非空）字节向量。端口的位置将超过读取的字节。

**procedure**: `(get-bytevector-n! *binary-input-port* *bytevector* *start* *n*)`

**returns:** 返回读取的字节数或 eof 对象

**libraries:** `(rnrs io ports)`, `(rnrs)`

`*start*`和`*n*`必须是精确的非负整数，并且`*start*`和`*n*`的总和不得超过`*bytevector*`的长度。

如果`*binary-input-port*`已经到达文件末尾，则返回 eof 对象。否则，`get-bytevector-n!`读取（如同使用`get-u8`）尽可能多的字节，最多达到`*n*`个，在端口到达文件末尾之前，将这些字节存储在`*bytevector*`的连续位置中，返回读取的字节数作为一个确切的正整数。端口的位置会向前移动到读取的字节之后。

**procedure**: `(get-bytevector-some *binary-input-port*)`

**returns:** 一个非空的字节向量或者 eof 对象

**libraries:** `(rnrs io ports)`, `(rnrs)`

如果`*binary-input-port*`已经到达文件末尾，则返回 eof 对象。否则，`get-bytevector-some`读取（如同使用`get-u8`）至少一个字节，可能更多，并返回包含这些字节的字节向量。端口的位置会向前移动到读取的字节之后。此操作读取的最大字节数取决于实现。

**procedure**: `(get-bytevector-all *binary-input-port*)`

**returns:** 一个非空的字节向量或者 eof 对象

**libraries:** `(rnrs io ports)`, `(rnrs)`

如果`*binary-input-port*`已经到达文件末尾，则返回 eof 对象。否则，`get-bytevector-all`读取（如同使用`get-u8`）在端口到达文件末尾之前的所有可用字节，并返回包含这些字节的字节向量。端口的位置会向前移动到读取的字节之后。

**procedure**: `(get-char *textual-input-port*)`

**returns:** 从`*textual-input-port*`中获取下一个字符，或者返回 eof 对象

**libraries:** `(rnrs io ports)`, `(rnrs)`

如果`*textual-input-port*`已经到达文件末尾，则返回 eof 对象。否则，返回下一个可用字符，并且端口的位置向前移动一个字符。如果`*textual-input-port*`是一个转码端口，则底层字节流中的位置可能会向前移动超过一个字节。

**procedure**: `(lookahead-char *textual-input-port*)`

**returns:** 从`*textual-input-port*`中获取下一个字符，或者返回 eof 对象

**libraries:** `(rnrs io ports)`, `(rnrs)`

如果`*textual-input-port*`已经到达文件末尾，则返回 eof 对象。否则，返回下一个可用字符。与`get-char`不同，`lookahead-char`不会消耗它从端口读取的字符，因此如果端口的下一个操作是调用`lookahead-char`或`get-char`，则会返回相同的字符。

`lookahead-char`用于需要向前查看一个字符的应用程序。下面定义的`get-word`过程从文本输入端口中返回下一个单词作为字符串，其中一个单词被定义为一系列字母字符。由于`get-word`在看到单词之外的一个字符之前不知道它已经读取了整个单词，它使用`lookahead-char`来确定下一个字符，并使用`get-char`来消耗该字符。

`(define get-word

(lambda (p)

(list->string

(let f ()

(let ([c (lookahead-char p)])

(cond

[(eof-object? c) '()]

[(char-alphabetic? c) (get-char p) (cons c (f))]

[else '()]))))))`

**procedure**: `(get-string-n *textual-input-port* *n*)`

**returns:** 包含最多 `*n*` 个字符的非空字符串，或者 eof 对象

**libraries:** `(rnrs io ports)`, `(rnrs)`

`*n*` 必须是一个精确的非负整数。如果 `*textual-input-port*` 在文件末尾，将返回 eof 对象。否则，`get-string-n` 读取（如同使用 `get-char`）尽可能多的字符，最多 `*n*` 个，在端口到达文件末尾之前，返回一个新的（非空）字符串，包含这些字符。端口的位置在读取的字符之后被推进。

**procedure**: `(get-string-n! *textual-input-port* *string* *start* *n*)`

**returns:** 读取的字符数或 eof 对象

**libraries:** `(rnrs io ports)`, `(rnrs)`

`*start*` 和 `*n*` 必须是精确的非负整数，并且 `*start*` 和 `*n*` 的和不能超过 `*string*` 的长度。

如果 `*textual-input-port*` 在文件末尾，将返回 eof 对象。否则，`get-string-n!` 读取（如同使用 `get-char`）尽可能多的字符，最多 `*n*` 个，在端口到达文件末尾之前，将字符存储在 `*string*` 的连续位置中，从 `*start*` 开始，并返回读取的字符数作为精确的正整数。端口的位置在读取的字符之后被推进。

`get-string-n!` 可以用于实现 `string-set!` 和 `string-fill!`，如下所示，尽管这不是它的主要目的。

`(define string-set!

(lambda (s i c)

(let ([sip (open-string-input-port (string c))])

(get-string-n! sip s i 1)

; return unspecified values:

(if #f #f))))

(define string-fill!

(lambda (s c)

(let ([n (string-length s)])

(let ([sip (open-string-input-port (make-string n c))])

(get-string-n! sip s 0 n)

; return unspecified values:

(if #f #f)))))

(let ([x (make-string 3)])

(string-fill! x #\-)

(string-set! x 2 #\))

(string-set! x 0 #\;)

x) ![<graphic>](img/ch2_0.gif) ";-)"`

**procedure**: `(get-string-all *textual-input-port*)`

**returns:** 非空字符串或 eof 对象

**libraries:** `(rnrs io ports)`, `(rnrs)`

如果 `*textual-input-port*` 在文件末尾，将返回 eof 对象。否则，`get-string-all` 读取（如同使用 `get-char`）端口到达文件末尾之前的所有可用字符，并返回一个包含这些字符的字符串。端口的位置在读取的字符之后被推进。

**procedure**: `(get-line *textual-input-port*)`

**returns:** a string or the eof object

**libraries:** `(rnrs io ports)`, `(rnrs)`

如果 `*textual-input-port*` 在文件末尾，将返回 eof 对象。否则，`get-line` 读取（如同使用 `get-char`）端口到达文件末尾之前的所有可用字符，或者读取了一个换行符字符，并返回包含读取字符但不包含换行字符的字符串。端口的位置在读取的字符之后被推进。

`(let ([sip (open-string-input-port "one\ntwo\n")])

(let* ([s1 (get-line sip)] [s2 (get-line sip)])

(list s1 s2 (port-eof? sip)))) ![<graphic>](img/ch2_0.gif) ("one" "two" #t)

(let ([sip (open-string-input-port "one\ntwo")])

(let* ([s1 (get-line sip)] [s2 (get-line sip)])

(list s1 s2 (port-eof? sip)))) ![<graphic>](img/ch2_0.gif) ("one" "two" #t)`

**过程**：`(get-datum *textual-input-port*)`

**返回：** 一个 Scheme 数据对象或 eof 对象

**库：** `(rnrs io ports)`，`(rnrs)`

此过程扫描空白和注释，以找到数据的外部表示的开始。如果 `*textual-input-port*` 在找到数据的外部表示的开始之前到达文件末尾，则返回 eof 对象。

否则，`get-datum` 读取尽可能多的字符，以解析单个数据，并返回一个由外部表示确定结构的新分配对象。端口的位置将在读取的字符之后前进。如果在数据的外部表示完成之前达到文件末尾，或者读取到意外字符，则会引发带有条件类型 `&lexical` 和 `i/o-read` 的异常。

`(let ([sip (open-string-input-port "; a\n\n one (two)\n")])

(let* ([x1 (get-datum sip)]

[c1 (lookahead-char sip)]

[x2 (get-datum sip)]) 

(list x1 c1 x2 (port-eof? sip)))) ![<graphic>](img/ch2_0.gif) (one #\space (two) #f)`

**过程**：`(port-eof? *input-port*)`

**返回：** 如果 `*input-port*` 处于文件末尾，则返回 `#t`，否则返回 `#f`

**库：** `(rnrs io ports)`，`(rnrs)`

此过程类似于二进制输入端口上的 `lookahead-u8` 或文本输入端口上的 `lookahead-char`，不同之处在于它不返回下一个字节/字符或 eof 对象，而是返回一个布尔值，指示该值是否为 eof 对象。

### 第 7.8 节。输出操作

主要目的是向输出端口发送数据的过��在本节中描述。

**过程**：`(put-u8 *binary-output-port* *octet*)`

**返回：** 未指定

**库：** `(rnrs io ports)`，`(rnrs)`

`*octet*` 必须是小于或等于 255 的非负确切整数。此过程将 `*octet*` 写入 `*binary-output-port*`，将端口的位置前进一个字节。

**过程**：`(put-bytevector *binary-output-port* *bytevector*)`

**过程**：`(put-bytevector *binary-output-port* *bytevector* *start*)`

**过程**：`(put-bytevector *binary-output-port* *bytevector* *start* *n*)`

**返回：** 未指定

**库：** `(rnrs io ports)`，`(rnrs)`

`*start*` 和 `*n*` 必须是非负确切整数，并且 `*start*` 和 `*n*` 的总和不能超过 `*bytevector*` 的长度。如果未提供，则 `*start*` 默认为零，`*n*` 默认为 `*bytevector*` 的长度与 `*start*` 之差。

此过程将从 `*start*` 处开始的 `*bytevector*` 的 `*n*` 个字节写入端口，并将其位置移至写入字节的末尾之后。

**过程**：`(put-char *textual-output-port* *char*)`

**返回：** 未指定

**libraries:** `(rnrs io ports)`, `(rnrs)`

此过程将 `*char*` 写入 `*textual-output-port*`，并将端口的位置向前移动一个字符。如果 `*textual-output-port*` 是一个转码端口，则底层字节流中的位置可能会向前移动多于一个字节。

**procedure**: `(put-string *textual-output-port* *string*)`

**procedure**: `(put-string *textual-output-port* *string* *start*)`

**procedure**: `(put-string *textual-output-port* *string* *start* *n*)`

**returns:** 未指定

**libraries:** `(rnrs io ports)`, `(rnrs)`

`*start*` 和 `*n*` 必须是非负确切整数，并且 `*start*` 和 `*n*` 的总和不能超过 `*string*` 的长度。如果未提供，则 `*start*` 默认为零，`*n*` 默认为 `*string*` 的长度与 `*start*` 的差值。

此过程将从 `*start*` 开始写入 `*string*` 的 `*n*` 个字符到端口，并将其位置移至已写入字符的末尾之后。

**procedure**: `(put-datum *textual-output-port* *obj*)`

**returns:** 未指定

**libraries:** `(rnrs io ports)`, `(rnrs)`

此过程将 `*obj*` 的外部表示写入 `*textual-output-port*`。如果 `*obj*` 没有作为数据的外部表示，行为是未指定的。精确的外部表示是依赖于实现的，但是当 `*obj*` 确实有作为数据的外部表示时，`put-datum` 应该生成一个字符序列，稍后可以被 `get-datum` 读取为等效对象（在 `equal?` 的意义上）为 `*obj*`。参见第 12.5 节中 `put-datum`、`write` 和 `display` 的实现示例。

**procedure**: `(flush-output-port *output-port*)`

**returns:** 未指定

**libraries:** `(rnrs io ports)`, `(rnrs)`

此过程强制将与 `*output-port*` 关联的缓冲区中的任何字节或字符立即发送到底层流。

### 第 7.9 节 便利 I/O

本节中的过程被称为“便利”I/O 运算符，因为它们提供了一个相对简化的接口来创建和与文本端口交互。它们还提供了与 Revised⁵ Report 的向后兼容性，该报告不支持单独的二进制和文本 I/O。

便利的输入/输出过程可以使用或不使用显式的端口参数进行调用。如果没有显式的端口参数进行调用，则使用当前的输入或输出端口，视情况而定。例如，`(read-char)` 和 `(read-char (current-input-port))` 都会从当前输入端口返回下一个字符。

**procedure**: `(open-input-file *path*)`

**returns:** 一个新的输入端口

**libraries:** `(rnrs io simple)`, `(rnrs)`

`*path*` 必须是一个字符串或其他一些依赖于实现的值，用于命名一个文件。 `open-input-file` 为名为 `*path*` 的文件创建一个新的文本输入端口，就像使用默认选项的 `open-file-input-port`，一个依赖于实现的缓冲模式和一个依赖于实现的转码器一样。

以下示例展示了在从名为 "myfile.ss" 的文件中收集对象列表的表达式中使用 `open-input-file`、`read` 和 `close-port`。

`(let ([p (open-input-file "myfile.ss")])

(let f ([x (read p)])

(if (eof-object? x)

(begin

(close-port p)

'())

(cons x (f (read p))))))`

**procedure**: `(open-output-file *path*)`

**returns:** 一个新的输出端口

**libraries:** `(rnrs io simple)`, `(rnrs)`

`*path*` 必须是一个字符串或其他一些依赖于实现的值，用于命名一个文件。 `open-output-file` 为名为 `*path*` 的文件创建一个新的输出端口，就像使用默认选项的 `open-file-output-port`，一个依赖于实现的缓冲模式和一个依赖于实现的转码器一样。

以下示例展示了使用 `open-output-file` 将对象列表（`list-to-be-printed` 的值）写入以换行符分隔的名为 "myfile.ss" 的文件。

`(let ([p (open-output-file "myfile.ss")])

(let f ([ls list-to-be-printed])

(if (not (null? ls))

(begin

(write (car ls) p)

(newline p)

(f (cdr ls)))))

(close-port p))

**procedure**: `(call-with-input-file *path* *procedure*)`

**returns:** `*procedure*` 返回的值

**libraries:** `(rnrs io simple)`, `(rnrs)`

`*path*` 必须是一个字符串或其他一些依赖于实现的值，用于命名一个文件。 `*procedure*` 应接受一个参数。

`call-with-input-file` 为名为 `*path*` 的文件创建一个新的输入端口，就像使用 `open-input-file` 一样，并将此端口传递给 `*procedure*`。 如果 `*procedure*` 返回，`call-with-input-file` 将关闭输入端口并返回 `*procedure*` 返回的值。

如果在 `*procedure*` 外部创建的延续被调用，`call-with-input-file` 不会自动关闭输入端口，因为可能会在以后的某个时候调用在 `*procedure*` 内部创建的另一个延续，将控制返回给 `*procedure*`。 如果 `*procedure*` 不返回，实现可以自由地仅在能够证明输入端口不再可访问时关闭输入端口。 如第 5.6 节所示，`dynamic-wind` 可用于确保在调用在 `*procedure*` 外部创建的延续时关闭端口。

以下示例展示了在从名为 "myfile.ss" 的文件中收集对象列表的表达式中使用 `call-with-input-file`，其功能等同于上面给出的 `open-input-file` 示例。

`(call-with-input-file "myfile.ss"

(lambda (p)

(let f ([x (read p)])

(if (eof-object? x)

'()

(cons x (f (read p)))))))`

`call-with-input-file` 可能被定义为以下不带错误检查的形式。

`(define call-with-input-file

(lambda (filename proc)

(let ([p (open-input-file filename)])

(let-values ([v* (proc p)])

(close-port p)

(apply values v*)))))`

**procedure**: `(call-with-output-file *path* *procedure*)`

**returns:** `*procedure*`返回的值

**libraries:** `(rnrs io simple)`, `(rnrs)`

`*path*`必须是一个字符串或其他一些依赖于实现的值，用于命名文件。`*procedure*`应该接受一个参数。

`call-with-output-file` 创建一个新的输出端口，用于文件名为`*path*`，就像使用`open-output-file`一样，并将此端口传递给`*procedure*`。如果`*procedure*`返回，`call-with-output-file`关闭输出端口并返回`*procedure*`返回的值。

`call-with-output-file` 如果在`*procedure*`外部创建的延续被调用，则不会自动关闭输出端口，因为可能会在以后的某个时候调用在`*procedure*`内部创建的另一个延续，将控制返回给`*procedure*`。如果`*procedure*`不返回，实现可以自由地仅在可以证明输出端口不再可访问时关闭输出端口。如第 5.6 节所示，可以使用`dynamic-wind`来确保在调用在`*procedure*`外部创建的延续时关闭端口。

以下显示了使用`call-with-output-file`将对象列表（`list-to-be-printed`的值）写入由"myfile.ss"命名的文件中，用换行符分隔。在功能上等同于上面给出的`open-output-file`示例。

`(call-with-output-file "myfile.ss"

(lambda (p)

(let f ([ls list-to-be-printed])

(unless (null? ls)

(write (car ls) p)

(newline p)

(f (cdr ls))))))`

`call-with-output-file` 可能如下定义，不带错误检查。

`(define call-with-output-file

(lambda (filename proc)

(let ([p (open-output-file filename)])

(let-values ([v* (proc p)])

(close-port p)

(apply values v*)))))`

**procedure**: `(with-input-from-file *path* *thunk*)`

**returns:** `*thunk*`返回的值

**libraries:** `(rnrs io simple)`, `(rnrs)`

`*path*`必须是一个字符串或其他一些依赖于实现的值，用于命名文件。`*thunk*`必须是一个过程，并且应该接受零个参数。

`with-input-from-file` 在应用`*thunk*`期间，临时将当前输入端口更改为打开文件名为`*path*`的文件的结果，就像使用`open-input-file`一样。如果`*thunk*`返回，端口将被关闭，并且当前输入端口将恢复到其旧值。

如果在`*thunk*`返回之前调用了在`*thunk*`外部创建的延续，则`with-input-from-file`的行为是未指定的。实现可以关闭端口并将当前输入端口恢复到其旧值---但也可能不这样做。

**procedure**: `(with-output-to-file *path* *thunk*)`

**returns:** `*thunk*`返回的值

**libraries:** `(rnrs io simple)`, `(rnrs)`

`*path*`必须是字符串或其他一些命名文件的实现相关值。`*thunk*`必须是一个过程，并且应该接受零个参数。

`with-output-to-file`临时将当前输出端口重新绑定为由`*path*`命名的文件的打开结果，就像使用`open-output-file`一样，在应用`*thunk*`期间。如果`*thunk*`返回，则关闭端口，并将当前输出端口恢复为其旧值。

如果在`*thunk*`返回之前调用了在`*thunk*`之外创建的续延，那么`with-output-to-file`的行为是未指定的。实现可能关闭端口并将当前输出端口恢复为其旧值---但也可能不会。

**procedure**: `(read)`

**procedure**: `(read *textual-input-port*)`

**返回：**一个 Scheme 数据对象或 eof 对象

**libraries:** `(rnrs io simple)`，`(rnrs)`

如果未提供`*textual-input-port*`，则默认为当前输入端口。否则，此过程等同于`get-datum`。

**procedure**: `(read-char)`

**procedure**: `(read-char *textual-input-port*)`

**返回：**来自`*textual-input-port*`的下一个字符

**libraries:** `(rnrs io simple)`，`(rnrs)`

如果未提供`*textual-input-port*`，则默认为当前输入端口。否则，此过程等同于`get-char`。

**procedure**: `(peek-char)`

**procedure**: `(peek-char *textual-input-port*)`

**返回：**来自`*textual-input-port*`的下一个字符

**libraries:** `(rnrs io simple)`，`(rnrs)`

如果未提供`*textual-input-port*`，则默认为当前输入端口。否则，此过程等同于`lookahead-char`。

**procedure**: `(write *obj*)`

**procedure**: `(write *obj* *textual-output-port*)`

**返回：**未指定

**libraries:** `(rnrs io simple)`，`(rnrs)`

如果未提供`*textual-output-port*`，则默认为当前输出端口。否则，此过程等同于`put-datum`，参数颠倒。有关`put-datum`、`write`和`display`的实现，请参见第 12.5 节。

**procedure**: `(display *obj*)`

**procedure**: `(display *obj* *textual-output-port*)`

**返回：**未指定

**libraries:** `(rnrs io simple)`，`(rnrs)`

如果未提供`*textual-output-port*`，则默认为当前输出端口。

`display`类似于`write`或`put-datum`，但直接打印`*obj*`中的字符串和字符。字符串将被打印，不带引号或特殊字符转义，就像`put-string`一样；字符将被打印，不带`#\`符号，就像`put-char`一样。使用`display`，三元素列表`(a b c)`和两元素列表`("a b" c)`都打印为`(a b c)`。因此，不应使用`display`来打印预期用`read`读取的对象。`display`主要用于打印消息，`*obj*`通常是字符串。参见第 12.5 节中的`put-datum`、`write`和`display`的实现。

**过程**：`(write-char *char*)`

**过程**：`(write-char *char* *textual-output-port*)`

**返回**：未指定

**库**：`(rnrs io simple)`，`(rnrs)`

如果未提供`*textual-output-port*`，则默认为当前输出端口。否则，此过程等效于`put-char`，参数顺序相反。

**过程**：`(newline)`

**过程**：`(newline *textual-output-port*)`

**返回**：未指定

**库**：`(rnrs io simple)`，`(rnrs)`

如果未提供`*textual-output-port*`，则默认为当前输出端口。`newline`向端口发送一个换行符。

**过程**：`(close-input-port *input-port*)`

**过程**：`(close-output-port *output-port*)`

**返回**：未指定

**库**：`(rnrs io simple)`，`(rnrs)`

`close-input-port`关闭一个输入端口，`close-output-port`关闭一个输出端口。这些过程是为了与修订⁵报告向后兼容而提供的；实际上，它们并不比`close-port`更方便使用。

### 第 7.10 节。文件系统操作

Scheme 有两个标准操作，除了文件输入/输出，用于与文件系统交互：`file-exists?`和`delete-file`。大多数实现支持额外的操作。

**过程**：`(file-exists? *path*)`

**返回**：如果由`*path*`命名的文件存在，则为`#t`，否则为`#f`

**库**：`(rnrs files)`，`(rnrs)`

`*path*`必须是一个字符串或其他一些特定于实现的值，用于命名一个文件。`file-exists?`是否遵循符号链接是未指定的。

**过程**：`(delete-file *path*)`

**返回**：未指定

**库**：`(rnrs files)`，`(rnrs)`

`*path*`必须是一个字符串或其他一些特定于实现的值，用于命名一个文件。`delete-file`如果存在并且可以删除，则删除由`*path*`命名的文件，否则引发一个带有条件类型`&i/o-filename`的异常。`delete-file`是否遵循符号链接是未指定的。

### 第 7.11 节。字节向量/字符串转换

本节描述的过程编码或解码字符序列，将字符串转换为字节向量或字节向量转换为字符串。它们不一定涉及输入/输出，尽管它们可能是使用字节向量输入和输出端口实现的。

前两个过程，`bytevector->string`和`string->bytevector`，需要一个显式的转码器参数，确定字符编码、行尾样式和错误处理模式。其他过程执行特定的 Unicode 转换，隐含的行尾样式为`none`，错误处理模式为`replace`。

**过程**：`(bytevector->string *bytevector* *transcoder*)`

**返回**：包含在`*bytevector*`中编码的字符的字符串

**库**：`(rnrs io ports)`，`(rnrs)`

这个操作，至少在效果上，创建了一个具有指定`*transcoder*`的字节向量输入端口，从中读取所有可用的字符，就像通过`get-string-all`一样，并将其放入输出字符串中。

`(let ([tx (make-transcoder (utf-8-codec) (eol-style lf)

(`error-handling-mode replace))])

(`bytevector->string #vu8(97 98 99) tx))` ![<graphic>](img/ch2_0.gif) "abc"`

**procedure**: `(string->bytevector *string* *transcoder*)`

**returns:** 包含 `*string*` 中字符的编码的字节向量

**libraries:** `(rnrs io ports)`, `(rnrs)`

此操作至少在效果上创建一个具有指定 `*transcoder*` 的字节向量输出端口，其中写入了 `*string*` 的所有字符，然后提取一个包含累积字节的字节向量。

`(let ([tx (make-transcoder (utf-8-codec) (eol-style none)

(`error-handling-mode raise))])

(`string->bytevector "abc" tx))` ![<graphic>](img/ch2_0.gif) #vu8(97 98 99)`

**procedure**: `(string->utf8 *string*)`

**returns:** 包含 `*string*` 的 UTF-8 编码的字节向量

**libraries:** `(rnrs bytevectors)`, `(rnrs)`

**procedure**: `(string->utf16 *string*)`

**procedure**: `(string->utf16 *string* *endianness*)`

**procedure**: `(string->utf32 *string*)`

**procedure**: `(string->utf32 *string* *endianness*)`

**returns:** 包含指定编码的字节向量 `*string*`

**libraries:** `(rnrs bytevectors)`, `(rnrs)`

`*endianness*` 必须是 `big` 或 `little` 符号之一。 如果未提供 `*endianness*` 或为符号 `big`，则 `string->utf16` 返回 `*string*` 的 UTF-16BE 编码，并且 `string->utf32` 返回 `*string*` 的 UTF-32BE 编码。 如果 `*endianness*` 是符号 `little`，则 `string->utf16` 返回 `*string*` 的 UTF-16LE 编码，并且 `string->utf32` 返回 `*string*` 的 UTF-32LE 编码。 编码中不包括字节顺序标记。

**procedure**: `(utf8->string *bytevector*)`

**returns:** 包含 `*bytevector*` 的 UTF-8 解码的字符串

**libraries:** `(rnrs bytevectors)`, `(rnrs)`

**procedure**: `(utf16->string *bytevector* *endianness*)`

**procedure**: `(utf16->string *bytevector* *endianness* *endianness-mandatory?*)`

**procedure**: `(utf32->string *bytevector* *endianness*)`

**procedure**: `(utf32->string *bytevector* *endianness* *endianness-mandatory?*)`

**returns:** 包含指定解码的字符串 `*bytevector*`

**libraries:** `(rnrs bytevectors)`, `(rnrs)`

`*endianness*` 必须是 `big` 或 `little` 符号之一。 这些过程返回 `*bytevector*` 的 UTF-16 或 UTF-32 解码，其表示的字节顺序由 `*endianness*` 参数或字节顺序标记（BOM）确定。 如果未提供 `*endianness-mandatory?*` 或为 `#f`，则字节顺序由 `*bytevector*` 前面的 BOM 或（如果不存在 BOM）由 `*endianness*` 确定。 如果 `*endianness-mandatory?*` 为 `#t`，则字节顺序由 `*endianness*` 确定，并且如果 `*bytevector*` 前面出现 BOM，则将其视为常规字符编码。

UTF-16 BOM 是指定“big”的两字节序列 `#xFE`, `#xFF` 或指定“little”的两字节序列 `#xFF`, `#xFE`。UTF-32 BOM 是指定“big”的四字节序列 `#x00`, `#x00`, `#xFE`, `#xFF` 或指定“little”的四字节序列 `#xFF`, `#xFE`, `#x00`, `#x00`。
