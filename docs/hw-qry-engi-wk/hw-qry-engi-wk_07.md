# 类型系统

> 原文：[`howqueryengineswork.com/03-type-system.html`](https://howqueryengineswork.com/03-type-system.html)

*本章讨论的源代码可以在 [KQuery 项目](https://github.com/andygrove/how-query-engines-work) 的 `datatypes` 模块中找到。*

每个查询引擎都需要一个类型系统——一种表示和推理数据类型的方法。当你写 `SELECT price * quantity` 时，引擎必须知道 `price` 和 `quantity` 是可以相乘的数字，以及结果将是什么类型。本章在 Apache Arrow 的基础上构建了 KQuery 的类型系统。

## 类型的重要性

考虑这个查询：

```rs
SELECT name, salary * 1.1 AS new_salary
FROM employees
WHERE department = 'Engineering' 
```

在执行之前，查询引擎必须回答：

+   `salary` 是否是支持乘法的数值类型？

+   `salary * 1.1` 的结果类型是什么？（如果工资是整数，结果应该是整数还是浮点数？）

+   `department` 是否是支持等值比较的字符串类型？

+   结果包含哪些列和类型？

这些问题在查询规划期间出现，在我们接触任何数据之前。一个设计良好的类型系统可以早期捕获错误（“你不能将字符串乘以数字”）并启用优化（“这个列永远不会为空，因此跳过空值检查”）。

## 基于 Arrow 构建

我们不会发明自己的类型系统，而是直接使用 Apache Arrow 的类型。这给我们：

+   一系列丰富的标准类型（整数、浮点数、字符串、日期等）

+   高效的内存表示（如前一章所述）

+   与基于 Arrow 的工具和文件格式兼容

Arrow 的类型系统包括：

| 类别 | 类型 |
| --- | --- |
| 布尔值 | Bool |
| 整数 | Int8, Int16, Int32, Int64 (有符号和无符号) |
| 浮点数 | Float32, Float64 |
| 文本 | Utf8 (可变长度字符串) |
| 二进制 | Binary (可变长度字节) |
| 时间 | Date32, Date64, Timestamp, Time32, Time64, Duration |
| 嵌套 | List, Struct, Map |

对于 KQuery，我们将关注常见类型：布尔值、整数、浮点数和字符串。我们为这些定义了方便的常量：

```rs
object ArrowTypes {
    val BooleanType = ArrowType.Bool()
    val Int8Type = ArrowType.Int(8, true)
    val Int16Type = ArrowType.Int(16, true)
    val Int32Type = ArrowType.Int(32, true)
    val Int64Type = ArrowType.Int(64, true)
    val UInt8Type = ArrowType.Int(8, false)
    val UInt16Type = ArrowType.Int(16, false)
    val UInt32Type = ArrowType.Int(32, false)
    val UInt64Type = ArrowType.Int(64, false)
    val FloatType = ArrowType.FloatingPoint(FloatingPointPrecision.SINGLE)
    val DoubleType = ArrowType.FloatingPoint(FloatingPointPrecision.DOUBLE)
    val StringType = ArrowType.Utf8()
} 
```

## 模式与字段

模式描述了数据集的结构：存在哪些列以及每个列的类型。模式是整个查询引擎中流动的必要元数据。

Arrow 将模式表示为字段列表，其中每个字段具有：

+   一个名称（字符串）

+   数据类型（ArrowType）

+   一个可空标志（此列是否可以包含空值？）

例如，员工表可能具有以下模式：

```rs
Schema:
  - id: Int32, not nullable
  - name: Utf8, nullable
  - department: Utf8, nullable
  - salary: Float64, not nullable 
```

模式服务于多个目的：

1.  验证：拒绝引用不存在列或误用类型的查询

1.  规划：确定表达式的输出类型

1.  优化：跳过非空列的空值检查

1.  执行：为结果分配正确类型的存储

## 列向量

Arrow 在向量（也称为数组）中存储列数据。每种向量类型都有自己的类：`IntVector`、`Float8Vector`、`VarCharVector` 等。这是高效的，但不太方便——处理列的代码需要在每个地方都有类型特定的分支。

KQuery 引入了一个 `ColumnVector` 接口来抽象底层的 Arrow 向量：

```rs
/** Abstraction over different implementations of a column vector. */
interface ColumnVector : AutoCloseable {
  fun getType(): ArrowType

  fun getValue(i: Int): Any?

  fun size(): Int
} 
```

这个接口让我们能够编写与任何列类型都兼容的通用代码。`getValue` 方法返回 `Any?`（Kotlin 对 Java 的 `Object` 的等效），这虽然对性能不是最佳，但使我们的代码更简单。

我们可以将 Arrow 的 `FieldVector` 包裹在这个接口中：

```rs
/** Wrapper around Arrow FieldVector */
class ArrowFieldVector(val field: FieldVector) : ColumnVector {

  override fun getType(): ArrowType {
    return when (field) {
      is BitVector -> ArrowTypes.BooleanType
      is TinyIntVector -> ArrowTypes.Int8Type
      is SmallIntVector -> ArrowTypes.Int16Type
      ...
      else -> throw IllegalStateException("Unsupported vector type: ${field.javaClass.name}")
    }
  }

  override fun getValue(i: Int): Any? {

    if (field.isNull(i)) {
      return null
    }

    return when (field) {
      is BitVector -> if (field.get(i) == 1) true else false
      is TinyIntVector -> field.get(i)
      is SmallIntVector -> field.get(i)
      ...
      else -> throw IllegalStateException("Unsupported vector type: ${field.javaClass.name}")
    }
  }

  override fun size(): Int {
    return field.valueCount
  }

  override fun close() {
    field.close()
  }
} 
```

## 字面量值

有时候我们需要一个包含相同值重复的“列”。例如，当评估 `salary * 1.1` 时，字面量 `1.1` 需要像 1.1 值的列一样（每个批次中的一行）行动。

而不是为成千上万的相同值分配内存，我们创建一个虚拟列：

```rs
class LiteralValueVector(
    private val arrowType: ArrowType,
    private val value: Any?,
    private val size: Int
) : ColumnVector {

    override fun getType(): ArrowType = arrowType

    override fun getValue(i: Int): Any? {
        if (i < 0 || i >= size) {
            throw IndexOutOfBoundsException()
        }
        return value
    }

    override fun size(): Int = size
} 
```

这对于任何有效的索引都返回相同的值，使用常量内存，而不管我们正在处理多少行。

## 记录批次

记录批次将多个列与架构一起分组。这是我们查询引擎中流动的基本数据单元。

```rs
class RecordBatch(
    val schema: Schema,
    val fields: List<ColumnVector>
) {
    fun rowCount(): Int = fields.first().size()

    fun columnCount(): Int = fields.size

    fun field(i: Int): ColumnVector = fields[i]
} 
```

记录批次允许批量处理：而不是一次处理一行（由于函数调用开销而缓慢）或加载整个数据集到内存中（对于大数据来说不切实际），我们处理通常为 1,000 到 100,000 行的块。

## 类型强制转换

真实的查询引擎需要类型强制转换：在必要时自动转换类型。例如：

+   `5 + 3.14` 应该将整数 `5` 提升为浮点数

+   比较 `Int32` 和 `Int64` 应该可以在不进行显式转换的情况下工作

+   对于 `date > '2024-01-01'` 这样的谓词进行字符串到日期的转换

KQuery 保持简单，并在大多数情况下需要显式类型。生产查询引擎会实现强制转换规则，通常提升到“更宽”的类型（Int32 → Int64 → Float64）。

## 整合一切

这些部分是如何组合在一起的。在处理查询时：

1.  数据源提供描述可用列的架构

1.  查询规划使用架构来验证表达式并确定结果类型

1.  执行阶段在算子之间传递记录批次

1.  每个算子产生具有已知架构的输出批次

类型系统是这个可能性的基础。没有它，我们无法验证查询、高效规划或正确分配存储。

下一章将在此基础上创建从文件中读取数据的抽象。

*这本书也可以以 ePub、MOBI 和 PDF 格式从 [`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work) 购买*

**版权 © 2020-2025 安迪·格鲁夫。保留所有权利。**
