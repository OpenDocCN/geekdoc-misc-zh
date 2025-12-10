# 物理计划和表达式

> 原文：[`howqueryengineswork.com/08-physical-plan.html`](https://howqueryengineswork.com/08-physical-plan.html)

*本章讨论的源代码可以在 [KQuery 项目](https://github.com/andygrove/how-query-engines-work) 的 `physical-plan` 模块中找到。*

逻辑计划描述要执行的计算。物理计划描述如何执行。本章涵盖了物理计划层，其中抽象操作变为可执行代码。

## 为什么将物理与逻辑分开？

逻辑计划表示“按部门汇总这些数据。”物理计划指定使用哪种算法。可能有几个有效的选择：

+   哈希聚合：按分组列键构建哈希映射，随着行的到达更新累加器。对于具有适度基数的不排序数据效果良好。

+   排序聚合：需要按分组列排序的数据，但由于它一次只跟踪一个组，所以使用的内存较少。

对于连接也是类似的：

+   哈希连接：从一个侧面构建哈希表，用另一个侧面进行探测。对于等值连接非常快。

+   排序-合并连接：对两边进行排序，然后合并。当数据已经排序时效果很好。

+   嵌套循环连接：对于左边的每一行，扫描整个右边的所有行。简单但慢；对于非等值连接是必要的。

逻辑计划不关心运行哪种算法。查询规划器根据数据特征、可用索引和成本估计进行选择。保持逻辑和物理分离，使得这种灵活性成为可能。

物理计划可能也因执行环境而异：

+   单线程与并行执行

+   CPU 与 GPU 计算

+   本地与分布式处理

## 物理计划接口

物理计划产生数据。接口反映了这一点：

```rs
interface PhysicalPlan {

  fun schema(): Schema

  /* Execute a physical plan and produce a series of record batches. */
  fun execute(): Sequence<RecordBatch>

  /*
   * Returns the children (inputs) of this physical plan. This method is used
   * to enable use of the visitor pattern to walk a query tree.
   */
  fun children(): List<PhysicalPlan>
} 
```

关键方法是 `execute()`，它返回一系列的记录批次。这是基于拉取的执行模型：调用者按需拉取批次，而不是让批次推送到它。Kotlin 的 `Sequence` 是懒加载的，所以只有在批次被消费时才会进行计算。

## 物理表达式

逻辑表达式通过名称引用列。物理表达式通过索引引用列以提高效率。在执行时间，我们不希望搜索列名。

```rs
interface Expression {
  fun evaluate(input: RecordBatch): ColumnVector
} 
```

物理表达式接受一个记录批次并产生一个列向量。输出对于输入批次中的每一行有一个值。

### 列表达式

最简单的表达式是从输入中检索一个列：

```rs
class ColumnExpression(val i: Int) : Expression {

  override fun evaluate(input: RecordBatch): ColumnVector {
    return input.field(i)
  }
} 
```

没有计算，只是通过索引查找。

### 文字表达式

文字值产生一个列，其中每一行都有相同的值。而不是为相同的值分配存储空间，我们使用一个 `LiteralValueVector`，它对任何索引都返回相同的值：

```rs
class LiteralValueVector(
    val arrowType: ArrowType,
    val value: Any?,
    val size: Int
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

这种优化很重要，因为像 `salary * 1.1` 这样的表达式否则会分配一个包含 1.1 个值的列，只是为了逐元素相乘。

```rs
class LiteralDoubleExpression(val value: Double) : Expression {
  override fun evaluate(input: RecordBatch): ColumnVector {
    return LiteralValueVector(ArrowTypes.DoubleType, value, input.rowCount())
  }
} 
```

### 二元表达式

二元表达式评估两个子表达式并将它们组合。一个基类处理常见的逻辑：

```rs
abstract class BinaryExpression(val l: Expression, val r: Expression) : Expression {

  override fun evaluate(input: RecordBatch): ColumnVector {
    val ll = l.evaluate(input)
    val rr = r.evaluate(input)
    assert(ll.size() == rr.size())
    return evaluate(ll, rr)
  }

  abstract fun evaluate(l: ColumnVector, r: ColumnVector): ColumnVector
} 
```

比较表达式产生布尔结果：

```rs
class EqExpression(l: Expression, r: Expression) : BooleanExpression(l, r) {

  override fun evaluate(l: Any?, r: Any?, arrowType: ArrowType): Boolean {
    return when (arrowType) {
      ArrowTypes.Int32Type -> (l as Int) == (r as Int)
      ArrowTypes.Int64Type -> (l as Long) == (r as Long)
      ArrowTypes.DoubleType -> (l as Double) == (r as Double)
      ArrowTypes.StringType -> toString(l) == toString(r)
      else -> throw IllegalStateException("Unsupported type: $arrowType")
    }
  }
} 
```

数学表达式产生数值结果：

```rs
class AddExpression(l: Expression, r: Expression) : MathExpression(l, r) {

  override fun evaluate(l: Any?, r: Any?, arrowType: ArrowType): Any? {
    return when (arrowType) {
      ArrowTypes.Int32Type -> (l as Int) + (r as Int)
      ArrowTypes.Int64Type -> (l as Long) + (r as Long)
      ArrowTypes.DoubleType -> (l as Double) + (r as Double)
      else -> throw IllegalStateException("Unsupported type: $arrowType")
    }
  }
} 
```

### 聚合表达式

聚合表达式的工作方式不同。它们不是为每行输入产生一个输出值，而是将多行减少到一个值。这需要维护跨批次的累加器：

```rs
interface AggregateExpression {
  fun inputExpression(): Expression
  fun createAccumulator(): Accumulator
}

interface Accumulator {
  fun accumulate(value: Any?)
  fun finalValue(): Any?
} 
```

每个聚合类型都创建自己的累加器：

```rs
class MaxExpression(private val expr: Expression) : AggregateExpression {

  override fun inputExpression(): Expression = expr

  override fun createAccumulator(): Accumulator = MaxAccumulator()
}

class MaxAccumulator : Accumulator {
  var value: Any? = null

  override fun accumulate(value: Any?) {
    if (value != null) {
      if (this.value == null) {
        this.value = value
      } else {
        val isMax = when (value) {
          is Int -> value > this.value as Int
          is Long -> value > this.value as Long
          is Double -> value > this.value as Double
          else -> throw UnsupportedOperationException("MAX not supported for: ${value.javaClass}")
        }
        if (isMax) {
          this.value = value
        }
      }
    }
  }

  override fun finalValue(): Any? = value
} 
```

## 物理计划

定义了表达式后，我们可以实现物理计划操作符。

### 扫描

扫描从数据源读取。它是最简单的操作符，完全委托给数据源：

```rs
class ScanExec(val ds: DataSource, val projection: List<String>) : PhysicalPlan {

  override fun schema(): Schema = ds.schema().select(projection)

  override fun children(): List<PhysicalPlan> = listOf()

  override fun execute(): Sequence<RecordBatch> = ds.scan(projection)
} 
```

投影列表告诉数据源要读取哪些列。对于像 Parquet 这样的列式格式，这避免了读取不必要的数据。

### 投影

投影评估表达式以产生新列：

```rs
class ProjectionExec(
    val input: PhysicalPlan,
    val schema: Schema,
    val expr: List<Expression>
) : PhysicalPlan {

  override fun schema(): Schema = schema

  override fun children(): List<PhysicalPlan> = listOf(input)

  override fun execute(): Sequence<RecordBatch> {
    return input.execute().map { batch ->
      val columns = expr.map { it.evaluate(batch) }
      RecordBatch(schema, columns)
    }
  }
} 
```

对于每个输入批次，评估每个表达式以产生输出列。当一个表达式只是一个列引用时，输出列与输入列是相同的对象；不复制数据。

### 选择（过滤）

选择保留谓词为真的行：

```rs
class SelectionExec(
    val input: PhysicalPlan,
    val expr: Expression
) : PhysicalPlan {

  override fun schema(): Schema = input.schema()

  override fun children(): List<PhysicalPlan> = listOf(input)

  override fun execute(): Sequence<RecordBatch> {
    return input.execute().map { batch ->
      val result = expr.evaluate(batch) as BitVector
      val filteredFields = batch.schema.fields.indices.map { i ->
        filter(batch.field(i), result)
      }
      RecordBatch(batch.schema, filteredFields)
    }
  }

  private fun filter(v: ColumnVector, selection: BitVector): ColumnVector {
    // Count selected rows
    var count = 0
    (0 until selection.valueCount).forEach {
      if (selection.get(it) == 1) count++
    }

    // Build filtered vector
    val filtered = FieldVectorFactory.create(v.getType(), count)
    var index = 0
    (0 until selection.valueCount).forEach {
      if (selection.get(it) == 1) {
        filtered.set(index++, v.getValue(it))
      }
    }
    return filtered
  }
} 
```

谓词表达式产生一个位向量（每行一个位）。然后我们复制位被设置的值。这是一个简单的实现；生产系统优化了所有行都匹配或没有行匹配的情况。

### 哈希聚合

哈希聚合通过键对行进行分组并计算聚合。它在产生输出之前处理所有输入：

```rs
class HashAggregateExec(
    val input: PhysicalPlan,
    val groupExpr: List<Expression>,
    val aggregateExpr: List<AggregateExpression>,
    val schema: Schema
) : PhysicalPlan {

  override fun schema(): Schema = schema

  override fun children(): List<PhysicalPlan> = listOf(input)

  override fun execute(): Sequence<RecordBatch> {
    val map = HashMap<List<Any?>, List<Accumulator>>()

    // Process all input batches
    input.execute().forEach { batch ->
      val groupKeys = groupExpr.map { it.evaluate(batch) }
      val aggrInputs = aggregateExpr.map { it.inputExpression().evaluate(batch) }

      // For each row, update accumulators
      (0 until batch.rowCount()).forEach { row ->
        val key = groupKeys.map { it.getValue(row) }

        val accumulators = map.getOrPut(key) {
          aggregateExpr.map { it.createAccumulator() }
        }

        accumulators.forEachIndexed { i, acc ->
          acc.accumulate(aggrInputs[i].getValue(row))
        }
      }
    }

    // Build output batch from accumulated results
    val root = VectorSchemaRoot.create(schema.toArrow(), allocator)
    root.allocateNew()
    root.rowCount = map.size

    map.entries.forEachIndexed { rowIndex, entry ->
      val (groupKey, accumulators) = entry

      groupExpr.indices.forEach { i ->
        root.getVector(i).set(rowIndex, groupKey[i])
      }
      aggregateExpr.indices.forEach { i ->
        root.getVector(groupExpr.size + i).set(rowIndex, accumulators[i].finalValue())
      }
    }

    return sequenceOf(RecordBatch(schema, root.fieldVectors.map { ArrowFieldVector(it) }))
  }
} 
```

哈希表键是分组列值的列表。每个条目持有该组的累加器。在处理所有输入后，我们遍历映射来构建输出批次。

这是一种“哈希”聚合，因为我们使用了哈希表。对于排序数据，使用“排序”聚合会更高效，因为我们可以在分组键改变时立即输出结果，而不需要在内存中存储所有分组。

## 执行模型

KQuery 使用基于拉取的执行：根操作符对其子操作符调用 `execute()`，然后它们对其子操作符调用，依此类推。数据在请求批次时向上流动。

另一种选择是基于推的执行，其中操作符将批次推送到它们的父操作符。两种模型都有效；选择影响如何处理背压和并行性。

返回 `Sequence<RecordBatch>` 允许延迟评估。如果根节点只需要第一个批次（对于 `LIMIT 1` 查询），我们就可以避免计算后续批次。

## 下一步

物理计划是可执行的，但我们仍然需要某种东西从逻辑计划中创建它们。下一章将介绍执行此转换的查询规划器。

*本书也以 ePub、MOBI 和 PDF 格式在 [`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work) 上出售。*

**版权所有 © 2020-2025 安迪·格鲁夫。保留所有权利。**
