# 数据源

> 原文：[`howqueryengineswork.com/04-data-sources.html`](https://howqueryengineswork.com/04-data-sources.html)

*本章讨论的源代码可以在[KQuery 项目](https://github.com/andygrove/how-query-engines-work)的`datasource`模块中找到。*

查询引擎需要数据来进行查询。数据可能来自 CSV 文件、Parquet 文件、数据库，甚至已经存在于内存中的数据。我们希望我们的查询引擎能够与这些数据源一起工作，而不关心细节。本章介绍了使这成为可能的数据源抽象。

## 为什么需要抽象数据源？

考虑一个简单的查询：

```rs
SELECT name, salary FROM employees WHERE department = 'Engineering' 
```

从查询引擎的角度来看，它需要：

1.  知道哪些列存在（以验证`name`、`salary`和`department`是真实的）

1.  知道这些列的类型（以验证将`department`与字符串进行比较是有意义的）

1.  读取实际数据，最好是它需要的列

无论`employees`是 CSV 文件、Parquet 文件还是内存中的表，这些要求都是相同的。通过定义一个公共接口，我们可以一次性编写查询规划和执行逻辑，并且它可以与任何数据源一起工作。

## 数据源接口

KQuery 定义了一个简单的接口，所有数据源都必须实现：

```rs
interface DataSource {

  / Return the schema for the underlying data source */
  fun schema(): Schema

  / Scan the data source, selecting the specified columns */
  fun scan(projection: List<String>): Sequence<RecordBatch>
} 
```

schema()返回数据的模式，即列名及其类型。查询规划器在规划期间使用它来验证查询。如果你引用了一个不存在的列，规划器可以在执行开始之前报告错误。

scan(projection)读取数据，并以记录批次的序列返回它。`projection`参数列出了要读取的列。这对于效率很重要：如果查询只使用表中的三个列，而表有五十个列，我们只应该读取这三个列。一些文件格式如 Parquet 原生支持这一点。对于其他如 CSV 的格式，我们可能读取所有内容，但只为请求的列构建向量。

返回类型`Sequence<RecordBatch>`启用流式处理。我们不需要将整个文件加载到内存中，我们可以分批处理它。当数据大于可用内存时，这很重要。

## CSV 数据源

CSV 是最容易理解的格式，但有一些尴尬的特性。文件只是由逗号（或制表符，或分号）分隔的值组成的文本。文件中没有嵌入模式，只有第一行可选的列名。

下面是一个 CSV 文件可能的样子：

```rs
id,name,department,salary
1,Alice,Engineering,95000
2,Bob,Sales,87000
3,Carol,Engineering,102000 
```

要读取这个，我们需要处理几件事情：

1.  从标题行中解析列名（如果有的话）

1.  推断或接受一个模式（这些列的类型是什么？）

1.  将文本值解析为类型值

1.  处理缺失或格式不正确的值

KQuery 的`CsvDataSource`接受一个可选的模式。如果提供了，它使用那个模式。如果没有提供，它通过读取标题行并将所有列视为字符串来推断一个模式：

```rs
class CsvDataSource(
    val filename: String,
    val schema: Schema?,
    private val hasHeaders: Boolean,
    private val batchSize: Int
) : DataSource {

  private val finalSchema: Schema by lazy { schema ?: inferSchema() }

  override fun schema(): Schema {
    return finalSchema
  }
  // ...
} 
```

`scan` 方法通过文件流式传输，将行解析到批次中。对于每个批次，它创建 Arrow 向量并用解析的值填充它们：

```rs
override fun scan(projection: List<String>): Sequence<RecordBatch> {
  val readSchema =
      if (projection.isNotEmpty()) {
        finalSchema.select(projection)
      } else {
        finalSchema
      }

  val parser = buildParser(settings)
  parser.beginParsing(file.inputStream().reader())

  return ReaderAsSequence(readSchema, parser, batchSize)
} 
```

`ReaderAsSequence` 类实现了 Kotlin 的 `Sequence` 接口，按需读取行并将它们分组到批次中。每个批次根据模式将字符串值转换为适当的 Arrow 向量类型。

### 类型转换

CSV 文件是文本，但我们的模式可能指定列是整数或浮点数。CSV 读取器必须将这些字符串解析为类型值：

```rs
when (vector) {
  is IntVector ->
      rows.withIndex().forEach { row ->
        val valueStr = row.value.getValue(field.value.name, "").trim()
        if (valueStr.isEmpty()) {
          vector.setNull(row.index)
        } else {
          vector.set(row.index, valueStr.toInt())
        }
      }
  is Float8Vector ->
      rows.withIndex().forEach { row ->
        val valueStr = row.value.getValue(field.value.name, "")
        if (valueStr.isEmpty()) {
          vector.setNull(row.index)
        } else {
          vector.set(row.index, valueStr.toDouble())
        }
      }
  // ... other types
} 
```

空值变为 null。无效值（如整数列中的“abc”）将抛出异常，这是正确的行为，因为数据与声明的模式不匹配。

## Parquet 数据源

Parquet 是一种为分析设计的二进制列格式。与 CSV 不同，Parquet 文件包含：

+   模式信息（列名、类型、可空性）

+   在行组内按列块组织的数据

+   压缩（snappy、gzip 等）

+   可选的统计信息（每列块的 min/max 值）

这使得 Parquet 对查询引擎更加高效。读取单个列意味着只读取该列的数据，而不是整个文件。模式是已知的，无需推断。并且压缩减少了存储和 I/O。

KQuery 的 `ParquetDataSource` 比 CSV 版本简单，因为 Parquet 库提供了我们需要的许多功能：

```rs
class ParquetDataSource(private val filename: String) : DataSource {

  override fun schema(): Schema {
    return ParquetScan(filename, listOf()).use {
      val arrowSchema = SchemaConverter().fromParquet(it.schema).arrowSchema
      SchemaConverter.fromArrow(arrowSchema)
    }
  }

  override fun scan(projection: List<String>): Sequence<RecordBatch> {
    return ParquetScan(filename, projection)
  }
} 
```

模式直接来自文件的元数据。扫描逐个读取行组，将 Parquet 的列格式转换为 Arrow 向量。

### 投影下推

Parquet 的列组织意味着投影下推是高效的。当我们只请求某些列时，Parquet 读取器只解压缩和读取这些列块。对于只有少数列被查询的宽表（数百列），这可以比读取所有内容快几个数量级。

## 内存数据源

有时数据已经存在于内存中，可能是从另一个来源加载或由之前的查询生成。`InMemoryDataSource` 包装现有的记录批次：

```rs
class InMemoryDataSource(
    val schema: Schema,
    val data: List<RecordBatch>
) : DataSource {

  override fun schema(): Schema {
    return schema
  }

  override fun scan(projection: List<String>): Sequence<RecordBatch> {
    val projectionIndices =
        projection.map { name -> schema.fields.indexOfFirst { it.name == name } }
    return data.asSequence().map { batch ->
      RecordBatch(schema, projectionIndices.map { i -> batch.field(i) })
    }
  }
} 
```

这对于测试和基于其他查询的查询很有用。这里的投影只是选择要包含在输出批次中的列。

## 其他数据源

真正的查询引擎支持更多的数据源。一些常见的数据源：

JSON：结构化但无模式。每一行可能是一个 JSON 对象。模式推断是可能的，但复杂，因为嵌套结构必须展平或表示为 Arrow 的嵌套类型。

ORC：类似于 Parquet，另一种在 Hadoop 生态系统中流行的列格式。数据以具有模式和统计信息的列“条带”形式存储。

数据库：查询引擎可以通过 JDBC 或本地协议从其他数据库读取。模式来自数据库的目录。将谓词下推到源数据库可以显着减少数据传输。

对象存储：云系统如 S3 或 GCS 可以作为数据源。查询引擎列出匹配模式的文件并读取它们，通常并行读取。

流式数据源：Kafka、Kinesis 或其他消息队列。由于数据是连续到达而不是从文件中读取，因此需要不同的处理方式。

## 无模式数据源

一些数据源没有固定的模式。JSON 文档中的每个记录可以有不同的字段。基于读取的模式的系统将模式决策推迟到查询时间。

处理无模式数据源增加了复杂性。选项包括：

+   要求用户显式声明模式

+   从数据样本中推断模式

+   使用灵活的表示方式，如字符串到值的映射

+   在运行时而不是规划时拒绝引用不存在字段的查询

KQuery 在规划时需要模式，因此无模式的数据源必须以某种方式提供或推断模式。

## 将数据源连接到查询引擎

数据源通过执行上下文连接到查询引擎。在 KQuery 中，您可以通过名称注册数据源：

```rs
val ctx = ExecutionContext()
ctx.registerCsv("employees", "data/employees.csv")
ctx.registerParquet("sales", "data/sales.parquet")

val result = ctx.sql("SELECT * FROM employees e JOIN sales s ON e.id = s.employee_id") 
```

查询规划器将表名解析为数据源，检索用于验证的模式，并在查询计划中创建扫描操作。CSV 与 Parquet 或其他任何东西的详细信息都隐藏在`DataSource`接口之后。

这种分离非常强大。添加对新文件格式的支持意味着实现两种方法。查询引擎的其余部分，从规划到优化再到执行，无需修改即可工作。

*本书也以 ePub、MOBI 和 PDF 格式可供购买，详情请访问[`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work)*

**版权所有 © 2020-2025 安迪·格鲁夫。保留所有权利。**
