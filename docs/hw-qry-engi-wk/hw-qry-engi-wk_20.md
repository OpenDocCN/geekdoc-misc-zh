# 测试

> [`howqueryengineswork.com/16-testing.html`](https://howqueryengineswork.com/16-testing.html)

*本章讨论的源代码可以在[KQuery 项目](https://github.com/andygrove/how-query-engines-work)的测试目录中找到。*

查询引擎是复杂的系统，细微的 bug 可能导致查询返回错误的结果。与崩溃或明显错误不同，一个静默返回错误数据的查询尤其危险，因为用户可能会基于错误信息做出决策。严格的测试是必不可少的。

## 为什么查询引擎难以测试

几个因素使得测试查询引擎具有挑战性：

操作符和表达式的组合爆炸意味着有无限种组合方式。一个包含三个操作符，每个操作符有两个表达式的简单查询就已经有众多可能的组合。手写的测试无法涵盖所有这些。

类型转换增加了另一个维度。像`a > b`这样的表达式必须对整数、浮点数、字符串、日期等正确工作。每个比较运算符乘以每种类型组合乘以 null 处理创建了许多测试用例。

边缘情况很多：空表、单行表、全为 null 的表、极大的值、浮点数的 NaN，以及包含特殊字符的 Unicode 字符串。生产数据最终会测试到所有这些。

查询优化器可能会引入 bug。一个查询可能在未优化时工作正确，但在优化器重写后失败。或者优化器可能会生成一个与原始查询在语义上不同的计划。

## 单元测试

单元测试验证单个组件在独立情况下是否工作正确。对于一个查询引擎，这意味着在组合测试之前，独立测试表达式、操作符和数据源。

### 测试表达式

表达式测试应验证每个表达式对于有效输入产生正确的结果，并且适当地处理边缘情况。

这里是一个针对不同数值类型的大于等于表达式的测试：

```rs
@Test
fun `gteq longs`() {
    val schema = Schema(listOf(
        Field("a", ArrowTypes.Int64Type),
        Field("b", ArrowTypes.Int64Type)
    ))

    val a: List<Long> = listOf(111, 222, 333, Long.MIN_VALUE, Long.MAX_VALUE)
    val b: List<Long> = listOf(111, 333, 222, Long.MAX_VALUE, Long.MIN_VALUE)

    val batch = Fuzzer().createRecordBatch(schema, listOf(a, b))

    val expr = GtEqExpression(ColumnExpression(0), ColumnExpression(1))
    val result = expr.evaluate(batch)

    assertEquals(a.size, result.size())
    (0 until result.size()).forEach {
        assertEquals(a[it] >= b[it], result.getValue(it))
    }
} 
```

这个测试包括 MIN_VALUE 和 MAX_VALUE 来验证边界行为。类似的测试应该存在于 bytes、shorts、integers、floats、doubles 和 strings 中。每种数值类型都可以有不同的溢出或比较语义。

对于浮点类型，测试 NaN 行为至关重要：

```rs
@Test
fun `gteq doubles`() {
    val schema = Schema(listOf(
        Field("a", ArrowTypes.DoubleType),
        Field("b", ArrowTypes.DoubleType)
    ))

    val a: List<Double> = listOf(0.0, 1.0,
        Double.MIN_VALUE, Double.MAX_VALUE, Double.NaN)
    val b = a.reversed()

    val batch = Fuzzer().createRecordBatch(schema, listOf(a, b))

    val expr = GtEqExpression(ColumnExpression(0), ColumnExpression(1))
    val result = expr.evaluate(batch)

    assertEquals(a.size, result.size())
    (0 until result.size()).forEach {
        assertEquals(a[it] >= b[it], result.getValue(it))
    }
} 
```

NaN 比较遵循 IEEE 754 语义，其中 NaN 与任何东西（包括它自己）比较都返回 false。这让许多开发者感到惊讶，因此显式测试可以捕捉到处理 NaN 不正确的实现。

### 创建测试数据

测试需要一个方便的方式来创建具有任意数据的记录批次。一个接受模式列值的辅助方法可以使测试更简洁：

```rs
fun createRecordBatch(schema: Schema, columns: List<List<Any?>>): RecordBatch {
    val rowCount = columns[0].size

    val root = VectorSchemaRoot.create(schema.toArrow(), rootAllocator)
    root.allocateNew()

    (0 until rowCount).forEach { row ->
        (0 until columns.size).forEach { col ->
            val v = root.getVector(col)
            val value = columns[col][row]
            when (v) {
                is BitVector -> v.set(row, if (value as Boolean) 1 else 0)
                is TinyIntVector -> v.set(row, value as Byte)
                is SmallIntVector -> v.set(row, value as Short)
                is IntVector -> v.set(row, value as Int)
                is BigIntVector -> v.set(row, value as Long)
                is Float4Vector -> v.set(row, value as Float)
                is Float8Vector -> v.set(row, value as Double)
                is VarCharVector -> v.set(row, (value as String).toByteArray())
                else -> throw IllegalStateException()
            }
        }
    }
    root.rowCount = rowCount

    return RecordBatch(schema, root.fieldVectors.map { ArrowFieldVector(it) })
} 
```

使用这个辅助工具，测试变得声明性：定义模式，提供数据，并验证结果。

### 要测试的内容

这里是每个查询引擎都应该有的单元测试类别：

类型处理：当表达式接收到意外的类型时会发生什么？例如，对字符串计算 SUM 应该产生一个清晰的错误。

边界值：测试每种数值类型的最大和最小值。测试空字符串和非常长的字符串。

空值处理：每个表达式都必须正确处理空输入。通常，任何涉及空的操作都会产生空值（SQL 三值逻辑）。

溢出和下溢：当两个大整数相乘导致溢出时会发生什么？这种行为应该被记录和测试。

特殊浮点值：测试正负无穷大、NaN、正负零。

## 测试 SQL 解析

SQL 解析值得专门的测试，因为解析器是一个关键组件，它解释用户查询。解析器错误可能导致查询被误解，可能产生严重后果。

### 测试运算符优先级

数学表达式必须尊重运算符优先级。这些测试验证乘法绑定比加法更紧密：

```rs
@Test
fun `1 + 2 * 3`() {
    val expr = parse("1 + 2 * 3")
    val expected = SqlBinaryExpr(
        SqlLong(1),
        "+",
        SqlBinaryExpr(SqlLong(2), "*", SqlLong(3))
    )
    assertEquals(expected, expr)
}

@Test
fun `1 * 2 + 3`() {
    val expr = parse("1 * 2 + 3")
    val expected = SqlBinaryExpr(
        SqlBinaryExpr(SqlLong(1), "*", SqlLong(2)),
        "+",
        SqlLong(3)
    )
    assertEquals(expected, expr)
} 
```

解析表达式的树结构揭示了哪些操作先绑定。在`1 + 2 * 3`中，`2 * 3`形成一个子树，因为乘法有更高的优先级。

### 测试查询结构

测试应验证每个 SQL 子句是否正确解析：

```rs
@Test
fun `parse SELECT with WHERE`() {
    val select = parseSelect(
        "SELECT id, first_name, last_name FROM employee WHERE state = 'CO'"
    )
    assertEquals(
        listOf(
            SqlIdentifier("id"),
            SqlIdentifier("first_name"),
            SqlIdentifier("last_name")
        ),
        select.projection
    )
    assertEquals(
        SqlBinaryExpr(SqlIdentifier("state"), "=", SqlString("CO")),
        select.selection
    )
    assertEquals("employee", select.tableName)
}

@Test
fun `parse SELECT with aggregates`() {
    val select = parseSelect(
        "SELECT state, MAX(salary) FROM employee GROUP BY state"
    )
    assertEquals(
        listOf(
            SqlIdentifier("state"),
            SqlFunction("MAX", listOf(SqlIdentifier("salary")))
        ),
        select.projection
    )
    assertEquals(listOf(SqlIdentifier("state")), select.groupBy)
} 
```

## 集成测试

集成测试验证组件是否正确协同工作。对于一个查询引擎来说，这意味着执行完整的查询并验证结果。

### 端到端查询测试

这些测试从解析到执行的全查询路径进行测试：

```rs
@Test
fun `employees in CO using DataFrame`() {
    val ctx = ExecutionContext(mapOf())

    val df = ctx.csv(employeeCsv)
        .filter(col("state") eq lit("CO"))
        .project(listOf(col("id"), col("first_name"), col("last_name")))

    val batches = ctx.execute(df).asSequence().toList()
    assertEquals(1, batches.size)

    val batch = batches.first()
    assertEquals("2,Gregg,Langford\n" + "3,John,Travis\n", batch.toCSV())
}

@Test
fun `employees in CA using SQL`() {
    val ctx = ExecutionContext(mapOf())

    val employee = ctx.csv(employeeCsv)
    ctx.register("employee", employee)

    val df = ctx.sql(
        "SELECT id, first_name, last_name FROM employee WHERE state = 'CA'"
    )

    val batches = ctx.execute(df).asSequence().toList()
    assertEquals(1, batches.size)

    val batch = batches.first()
    assertEquals("1,Bill,Hopkins\n", batch.toCSV())
} 
```

这些测试使用一个小型静态测试文件，因此预期的结果已知。CSV 输出格式使得测试失败时的断言可读且易于比较。

### 测试复杂操作

聚合、连接和其他复杂操作需要彻底的集成测试：

```rs
@Test
fun `aggregate query`() {
    val ctx = ExecutionContext(mapOf())

    val df = ctx.csv(employeeCsv)
        .aggregate(
            listOf(col("state")),
            listOf(Max(cast(col("salary"), ArrowType.Int(32, true))))
        )

    val batches = ctx.execute(df).asSequence().toList()
    assertEquals(1, batches.size)

    val batch = batches.first()
    val expected = "CO,11500\n" + "CA,12000\n" + ",11500\n"
    assertEquals(expected, batch.toCSV())
}

@Test
fun `inner join using DataFrame`() {
    val leftSchema = Schema(listOf(
        Field("id", ArrowTypes.Int32Type),
        Field("name", ArrowTypes.StringType)
    ))
    val rightSchema = Schema(listOf(
        Field("id", ArrowTypes.Int32Type),
        Field("dept", ArrowTypes.StringType)
    ))

    val leftData = Fuzzer().createRecordBatch(
        leftSchema,
        listOf(listOf(1, 2, 3), listOf("Alice", "Bob", "Carol"))
    )
    val rightData = Fuzzer().createRecordBatch(
        rightSchema,
        listOf(listOf(1, 2, 4), listOf("Engineering", "Sales", "Marketing"))
    )

    val leftSource = InMemoryDataSource(leftSchema, listOf(leftData))
    val rightSource = InMemoryDataSource(rightSchema, listOf(rightData))

    val ctx = ExecutionContext(mapOf())

    val leftDf = DataFrameImpl(Scan("left", leftSource, listOf()))
    val rightDf = DataFrameImpl(Scan("right", rightSource, listOf()))

    val joinedDf = leftDf.join(rightDf, JoinType.Inner, listOf("id" to "id"))

    val batches = ctx.execute(joinedDf).asSequence().toList()
    assertEquals(1, batches.size)

    val batch = batches.first()
    assertEquals(2, batch.rowCount())
    assertEquals("1,Alice,Engineering\n2,Bob,Sales\n", batch.toCSV())
} 
```

连接测试创建内存中的数据源，以便精确控制输入数据。这使得预期的输出可预测，测试具有确定性。

### 比较测试

比较测试对受信任的参考实现执行相同的查询，并验证两者产生相同的结果。这对于捕捉细微的错误特别有价值。

常见的方法包括：

+   在 PostgreSQL、DuckDB 或其他已建立的数据库上运行查询并比较结果

+   比较 DataFrame API 查询与同一引擎内的等效 SQL 查询

+   对未优化的版本运行优化查询以验证优化器是否保留了语义

比较测试的挑战在于处理空值排序、浮点精度和未指定 ORDER BY 时的结果排序的差异。

## 模糊测试

手写测试不可避免地会错过边缘情况。模糊测试生成随机输入以发现人类不会想到测试的漏洞。

### 随机表达式生成

模糊器通过递归构建叶节点（列、文字）或二进制表达式来创建随机的表达式树：

```rs
fun createExpression(input: DataFrame, depth: Int, maxDepth: Int): LogicalExpr {
    return if (depth == maxDepth) {
        // return a leaf node
        when (rand.nextInt(4)) {
            0 -> ColumnIndex(rand.nextInt(input.schema().fields.size))
            1 -> LiteralDouble(rand.nextDouble())
            2 -> LiteralLong(rand.nextLong())
            3 -> LiteralString(randomString(rand.nextInt(64)))
            else -> throw IllegalStateException()
        }
    } else {
        // binary expressions
        val l = createExpression(input, depth+1, maxDepth)
        val r = createExpression(input, depth+1, maxDepth)
        return when (rand.nextInt(8)) {
            0 -> Eq(l, r)
            1 -> Neq(l, r)
            2 -> Lt(l, r)
            3 -> LtEq(l, r)
            4 -> Gt(l, r)
            5 -> GtEq(l, r)
            6 -> And(l, r)
            7 -> Or(l, r)
            else -> throw IllegalStateException()
        }
    }
} 
```

深度限制防止无界递归。随机种子应固定以实现可重复性。

### 随机计划生成

类似地，模糊器可以生成随机的查询计划：

```rs
fun createPlan(input: DataFrame,
               depth: Int,
               maxDepth: Int,
               maxExprDepth: Int): DataFrame {

    return if (depth == maxDepth) {
        input
    } else {
        // recursively create an input plan
        val child = createPlan(input, depth+1, maxDepth, maxExprDepth)
        // apply a transformation to the plan
        when (rand.nextInt(2)) {
            0 -> {
                val exprCount = 1.rangeTo(rand.nextInt(1, 5))
                child.project(exprCount.map {
                    createExpression(child, 0, maxExprDepth)
                })
            }
            1 -> child.filter(createExpression(input, 0, maxExprDepth))
            else -> throw IllegalStateException()
        }
    }
} 
```

这里是一个生成的计划的例子：

```rs
Filter: 'VejBmVBpYp7gHxHIUB6UcGx' OR 0.7762591612853446
  Filter: 'vHGbOKKqR' <= 0.41876514212913307
    Filter: 0.9835090312561898 <= 3342229749483308391
      Filter: -5182478750208008322 < -8012833501302297790
        Filter: 0.3985688976088563 AND #1
          Filter: #5 OR 'WkaZ54spnoI4MBtFpQaQgk'
            Scan: employee.csv; projection=None 
```

### 增强随机值

天真的随机数生成会错过有趣的边缘情况。增强的随机生成器故意产生边界值：

```rs
class EnhancedRandom(val rand: Random) {

    fun nextDouble(): Double {
        return when (rand.nextInt(8)) {
            0 -> Double.MIN_VALUE
            1 -> Double.MAX_VALUE
            2 -> Double.POSITIVE_INFINITY
            3 -> Double.NEGATIVE_INFINITY
            4 -> Double.NaN
            5 -> -0.0
            6 -> 0.0
            7 -> rand.nextDouble()
            else -> throw IllegalStateException()
        }
    }

    fun nextLong(): Long {
        return when (rand.nextInt(5)) {
            0 -> Long.MIN_VALUE
            1 -> Long.MAX_VALUE
            2 -> -0
            3 -> 0
            4 -> rand.nextLong()
            else -> throw IllegalStateException()
        }
    }
} 
```

通过将分布权重偏向边缘情况，模糊器比纯随机生成更快地发现错误。

### 处理无效计划

大多数随机生成的计划都是无效的。这实际上是有用的，因为它测试了错误处理。然而，如果您想特别测试执行，可以通过以下方式使模糊器“更智能”：

+   生成类型感知表达式（例如，仅比较兼容类型）

+   生成具有布尔操作数的 AND/OR 表达式

+   确保聚合表达式使用聚合函数

代价是，更智能的模糊器可能会错过错误路径中的错误。

### 有效使用模糊测试

模糊测试的一些实用技巧：

固定随机种子：使用常数种子以便失败可重复。如果使用系统时间，请记录种子。

运行多次迭代：模糊测试以概率发现错误。运行数千或数百万次迭代。

缩小失败案例：当模糊测试发现错误时，尝试将失败的输入减少到最小重现。

保持回归测试：当模糊测试发现一个错误时，将简化的案例添加为永久性测试。

## 金色测试

金色测试（也称为快照测试）捕获查询的输出并将其存储为预期结果。未来的运行将与此“金色”输出进行比较。

这种方法适用于：

+   查询计划美化打印（验证计划结构）

+   解释输出格式

+   错误信息

金色测试的缺点是可能很脆弱。任何对输出格式的更改都会破坏测试，即使底层行为是正确的。

## 测试优化

优化器错误尤其狡猾，因为未优化的查询是正确的。通过以下方式测试优化：

1.  验证优化和非优化计划产生相同的结果

1.  验证特定优化在预期时触发

1.  测试无效优化不会触发

例如，为了测试投影下推：

```rs
@Test
fun `projection pushdown reduces columns read`() {
    val plan = // build a plan that selects 3 columns from a 10 column table

    val optimized = Optimizer().optimize(plan)

    // Verify the scan only reads the 3 needed columns
    val scan = findScan(optimized)
    assertEquals(3, scan.projection.size)
}

@Test
fun `optimization preserves query semantics`() {
    val plan = // build a query plan
    val optimized = Optimizer().optimize(plan)

    val originalResult = execute(plan)
    val optimizedResult = execute(optimized)

    assertEquals(originalResult, optimizedResult)
} 
```

## 调试测试失败

当测试失败时，关键是重现和理解失败。

美化打印计划：在逻辑和物理计划上实现`pretty()`方法。当测试失败时，打印计划以了解执行了哪个查询。

记录中间结果：对于调试，添加显示通过每个操作符流动的数据的日志。

最小化重现：从一个失败的查询开始，系统地简化它同时保持失败。移除不必要的列、筛选和连接，直到你得到最小的显示错误的查询。

检查边界条件：许多错误发生在边界处。如果一个包含 100 行的测试失败，尝试 0、1 和 2 行。

验证测试数据：有时测试本身是错误的。请确保测试数据和预期结果都是正确的。

## 持续集成

CI 中的自动化测试在回归到达用户之前捕捉到它们。一个查询引擎的良好 CI 设置包括：

+   在每次提交时运行所有单元测试

+   在每次拉取请求时运行集成测试

+   每天或每周运行较长的模糊测试会话

+   跟踪测试执行时间以捕捉性能回归

测试失败应阻止合并。不稳定的测试（有时通过有时失败的测试）必须立即修复，因为它们会训练开发者忽略失败。

## 总结

测试查询引擎需要多种互补的方法。单元测试验证单个组件。集成测试验证组件协同工作。模糊测试发现人类可能遗漏的边缘情况。比较测试通过检查参考实现来捕捉语义错误。

早期投资于测试基础设施。良好的测试工具（用于创建测试数据、比较结果、美化打印计划）使编写测试更容易，这意味着可以编写更多的测试。一个经过良好测试的查询引擎让用户对其查询结果正确性充满信心。

*本书也以 ePub、MOBI 和 PDF 格式在[`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work)上出售。*

**版权所有 © 2020-2025 安迪·格鲁夫。保留所有权利。**
