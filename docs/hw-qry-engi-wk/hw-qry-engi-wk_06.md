# Apache Arrow

> 原文：[`howqueryengineswork.com/02-apache-arrow.html`](https://howqueryengineswork.com/02-apache-arrow.html)

在我们开始构建查询引擎之前，我们需要选择如何在内存中表示数据。这个选择会影响一切：我们如何读取文件，我们如何在算子之间传递数据，以及我们的计算运行得多快。我们将使用 Apache Arrow，它已成为内存中列式数据的标准。

## 为什么使用列式存储？

传统数据库和编程语言通常按行存储数据。如果你有一个员工表，每个员工记录在内存中是连续存放的：

```rs
Row 0: [1, "Alice", "Engineering", 95000]
Row 1: [2, "Bob", "Sales", 87000]
Row 2: [3, "Carol", "Engineering", 102000] 
```

这种布局直观且在需要访问整个记录时表现良好。但查询引擎通常一次只处理几个列。考虑：

```rs
SELECT AVG(salary) FROM employees WHERE department = 'Engineering' 
```

这个查询只需要`department`和`salary`列。在基于行的存储中，我们只需为了访问两个字段就将整个行加载到内存中。

列式存储则相反。每个列都是连续存储的：

```rs
ids:         [1, 2, 3]
names:       ["Alice", "Bob", "Carol"]
departments: ["Engineering", "Sales", "Engineering"]
salaries:    [95000, 87000, 102000] 
```

现在读取`salary`意味着读取一块连续的内存，无需跳过不需要的字段。这对性能影响极大：

+   现代 CPU 以缓存行（通常是 64 字节）的形式加载内存。列式数据可以在每个缓存行中打包更多的有用值。

+   相似值分组在一起可以更好地压缩。部门列可能压缩到只有几个不同的值。

+   CPU 可以对多个值同时执行相同的操作（单指令，多数据）。列式布局使得这一点成为可能。

## Apache Arrow 是什么？

Apache Arrow 是一个关于如何在内存中表示列式数据的规范，以及实现该规范的多种语言的库。将其视为一个不同系统可以共享的通用格式。

Arrow 背后的关键洞察是数据分析涉及许多工具：Python 用于探索，Spark 用于分布式处理，数据库用于存储，可视化工具用于展示。传统上，每个工具都有自己的内部格式，因此在不同工具之间移动数据意味着序列化和反序列化，反复转换格式。

Arrow 消除了这种开销。如果你的 Python 代码和 Java 代码都使用 Arrow 格式，它们可以直接共享内存。指向 Arrow 数据的指针对任何 Arrow 感知系统都是有意义的。

## 箭头内存布局

箭头列（称为“向量”或“数组”）由以下内容组成：

1.  包含实际值的缓冲区，这些值连续打包

1.  一个有效性缓冲区，它是一个位图，指示哪些值是 null

1.  可选的偏移缓冲区，用于字符串等变长类型

对于一个 32 位整数列 `[1, null, 3, 4]`：

```rs
Validity bitmap: [1, 0, 1, 1]  (bit per value: 1=valid, 0=null)
Data buffer:     [1, ?, 3, 4]  (? = undefined, since null) 
```

对于字符串，我们需要偏移量，因为字符串的长度不同：

```rs
Values: ["hello", "world", "!"]

Offsets: [0, 5, 10, 11]  (start position of each string, plus end)
Data:    "helloworld!"   (all strings concatenated) 
```

要获取索引为 1 的字符串：从偏移量[1]=5 读取到偏移量[2]=10，得到“world”。

这种布局简单但强大。固定宽度的类型，如整数，每个值只需要一次内存访问。有效性位图每个值只需要一个位，因此检查空值成本低。

## 记录批次

单个列本身并不很有用。我们需要多个列一起使用。查询引擎通常将列分组到记录批次中：具有描述其名称和类型的模式的等长列集合。KQuery 为此定义了自己的`RecordBatch`类。

```rs
RecordBatch:
  Schema: {id: Int32, name: Utf8, salary: Float64}
  Columns:
    id:     [1, 2, 3]
    name:   ["Alice", "Bob", "Carol"]
    salary: [95000.0, 87000.0, 102000.0]
  Length: 3 
```

查询引擎以批量的方式处理数据，而不是逐行或一次性处理。批量处理击中了最佳点：

+   足够小，可以放入 CPU 缓存。

+   足够大，可以分摊每批开销。

+   支持流式处理（数据到达时进行处理）。

典型的批量大小从 1,000 到 100,000 行不等，具体取决于工作负载。

## 模式和类型

Arrow 定义了一个丰富的类型系统，涵盖：

+   整数：Int8、Int16、Int32、Int64（有符号和无符号）。

+   浮点数：Float32（单精度），Float64（双精度）。

+   二进制：可变长度的字节数组。

+   字符串：UTF-8 编码的文本。

+   时间：日期、时间、时间戳、持续时间、间隔

+   嵌套：列表、结构、映射、联合。

一个模式命名和指定列：

```rs
Schema:
  - id: Int32, not nullable
  - name: Utf8, nullable
  - hire_date: Date32, nullable
  - salary: Float64, not nullable 
```

在模式中具有显式的可空性可以让查询引擎进行优化。如果一个列不能为空，我们可以完全跳过空值检查。

## 语言实现

Arrow 在 C++、Java、Python、Rust、Go、JavaScript、C#、Ruby 等多种语言中都有官方实现。对于这本书，我们将使用 Java 实现。

Java API 提供：

+   FieldVector：列向量的基类（IntVector、VarCharVector 等）。

+   VectorSchemaRoot：记录批次的容器。

+   ArrowType：表示数据类型。

+   模式/字段：描述数据的结构。

这里是一个在 Java 中创建 Arrow 向量的简单示例：

```rs
try (IntVector vector = new IntVector("id", allocator)) {
    vector.allocateNew(3);
    vector.set(0, 1);
    vector.set(1, 2);
    vector.set(2, 3);
    vector.setValueCount(3);
    // vector now contains [1, 2, 3]
} 
```

## 为什么选择 Arrow 作为我们的查询引擎？

我们将使用 Arrow 作为我们查询引擎的基础，原因有几个：

1.  它是一个标准格式，因此我们可以轻松地读写 Parquet 文件并与其他工具集成。

1.  Java 库成熟且经过充分测试。

1.  列式布局使得查询处理更加高效。

1.  理解 Arrow 有助于你理解其他数据系统。

下一章将在 Arrow 之上构建我们的类型系统，添加查询引擎需要的抽象。

## 进一步阅读

[Arrow 规范](https://arrow.apache.org/docs/format/Columnar.html)详细描述了内存格式。[Arrow 网站](https://arrow.apache.org/)为每种语言实现提供了文档。

Arrow 还提供了在网络上传输数据（Arrow Flight）和文件格式（Arrow IPC，Feather）的协议，但在这本书中我们不会直接使用它们。对我们来说，核心价值是内存中的列式格式。

*本书也以 ePub、MOBI 和 PDF 格式在[`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work)上出售*。

**版权所有 © 2020-2025 安迪·格鲁夫。保留所有权利。**
