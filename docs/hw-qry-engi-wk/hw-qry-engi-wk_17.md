# 查询执行

> 原文：[`howqueryengineswork.com/13-execution.html`](https://howqueryengineswork.com/13-execution.html)

*本章讨论的源代码可以在 [KQuery 项目](https://github.com/andygrove/how-query-engines-work) 的 `execution` 模块中找到。*

我们已经构建了所有组件：数据源、逻辑计划、物理计划、查询规划器和优化器。本章将它们组合成一个可工作的查询引擎。

## 执行上下文

`ExecutionContext` 是运行查询的入口点。它管理已注册的表并协调执行管道：

```rs
class ExecutionContext(val settings: Map<String, String>) {

    private val tables = mutableMapOf<String, DataFrame>()

    fun sql(sql: String): DataFrame {
        val tokens = SqlTokenizer(sql).tokenize()
        val ast = SqlParser(tokens).parse() as SqlSelect
        return SqlPlanner().createDataFrame(ast, tables)
    }

    fun csv(filename: String): DataFrame {
        return DataFrameImpl(Scan(filename, CsvDataSource(filename, ...), listOf()))
    }

    fun register(tablename: String, df: DataFrame) {
        tables[tablename] = df
    }

    fun execute(plan: LogicalPlan): Sequence<RecordBatch> {
        val optimizedPlan = Optimizer().optimize(plan)
        val physicalPlan = QueryPlanner().createPhysicalPlan(optimizedPlan)
        return physicalPlan.execute()
    }
} 
```

用户通过与上下文交互来：

1.  将数据源注册为命名表

1.  使用 SQL 或 DataFrame API 构建查询

1.  执行查询并消费结果

## 执行管道

当你执行一个查询时，它将通过几个阶段：

```rs
SQL String
    ↓ tokenize
Tokens
    ↓ parse
SQL AST
    ↓ plan
Logical Plan
    ↓ optimize
Optimized Logical Plan
    ↓ physical planning
Physical Plan
    ↓ execute
Sequence<RecordBatch> 
```

对于 DataFrame 查询，管道从逻辑计划阶段开始，因为 DataFrame API 直接构建逻辑计划。

### 阶段 1：解析（仅限 SQL）

SQL 文本变成标记，然后是语法树：

```rs
val tokens = SqlTokenizer(sql).tokenize()
val ast = SqlParser(tokens).parse() 
```

### 阶段 2：逻辑规划

SQL AST（或 DataFrame）变成逻辑计划：

```rs
val logicalPlan = SqlPlanner().createDataFrame(ast, tables).logicalPlan() 
```

### 阶段 3：优化

优化器转换逻辑计划：

```rs
val optimizedPlan = Optimizer().optimize(logicalPlan) 
```

### 阶段 4：物理规划

查询规划器创建一个可执行的物理计划：

```rs
val physicalPlan = QueryPlanner().createPhysicalPlan(optimizedPlan) 
```

### 阶段 5：执行

物理计划执行，生成记录批次：

```rs
val results: Sequence<RecordBatch> = physicalPlan.execute() 
```

## 运行查询

这里是一个完整的示例：

```rs
val ctx = ExecutionContext(mapOf())

// Register a CSV file as a table
ctx.registerCsv("employees", "/data/employees.csv")

// Execute a SQL query
val df = ctx.sql("""
    SELECT department, AVG(salary) as avg_salary
    FROM employees
    WHERE state = 'CO'
    GROUP BY department
""")

// Execute and print results
ctx.execute(df).forEach { batch ->
    println(batch.toCSV())
} 
```

或者使用 DataFrame API：

```rs
val ctx = ExecutionContext(mapOf())

val results = ctx.csv("/data/employees.csv")
    .filter(col("state") eq lit("CO"))
    .aggregate(
        listOf(col("department")),
        listOf(avg(col("salary")))
    )

ctx.execute(results).forEach { batch ->
    println(batch.toCSV())
} 
```

两种方法产生相同的物理计划和结果。

## 懒加载评估

注意到构建 DataFrame 并不会执行任何操作。DataFrame 只持有逻辑计划。执行只有在调用 `execute()` 并消费结果序列时才会发生。

这种懒加载评估有以下好处：

+   在执行之前，优化器可以看到完整的查询

+   在处理开始之前就捕捉到计划中的错误

+   资源在需要时才分配

## 消费结果

`execute()` 方法返回 `Sequence<RecordBatch>`。你可以以多种方式处理结果：

遍历批次：

```rs
ctx.execute(df).forEach { batch ->
    // Process each batch
} 
```

收集所有结果：

```rs
val allBatches = ctx.execute(df).toList() 
```

只取所需：

```rs
val firstBatch = ctx.execute(df).first() 
```

因为 `Sequence` 是懒加载的，只取第一批数据可以避免计算后续批次。这对于带有 `LIMIT` 的查询很重要。

## 示例：纽约出租车数据

让我们运行一个针对纽约出租车数据集的真实查询，这是一个常见的基准数据集，包含数百万行。

```rs
val ctx = ExecutionContext(mapOf())
ctx.registerCsv("tripdata", "/data/yellow_tripdata_2019-01.csv")

val start = System.currentTimeMillis()

val df = ctx.sql("""
    SELECT passenger_count, MAX(fare_amount)
    FROM tripdata
    GROUP BY passenger_count
""")

ctx.execute(df).forEach { batch ->
    println(batch.toCSV())
}

println("Query took ${System.currentTimeMillis() - start} ms") 
```

输出：

```rs
passenger_count,MAX
1,623259.86
2,492.5
3,350.0
4,500.0
5,760.0
6,262.5
7,78.0
8,87.0
9,92.0
0,36090.3

Query took 6740 ms 
```

## 优化影响

为了看到优化器能帮助多少，我们可以绕过它：

```rs
// With optimization (normal path)
val optimizedPlan = Optimizer().optimize(df.logicalPlan())
val physicalPlan = QueryPlanner().createPhysicalPlan(optimizedPlan)
// Query took 6740 ms

// Without optimization
val physicalPlan = QueryPlanner().createPhysicalPlan(df.logicalPlan())
// Query took 36090 ms 
```

未优化的查询大约需要五倍的时间。差异来自于投影下推：优化计划只读取它需要的列（`passenger_count`，`fare_amount`），而未优化的计划从 CSV 文件中读取所有 17 列。

对于更宽的表或更精确的筛选器，优化影响会更大。

## 与 Apache Spark 的比较

仅供参考，以下是 Apache Spark 中的相同查询：

```rs
val spark = SparkSession.builder()
    .master("local[1]")  // Single thread for fair comparison
    .getOrCreate()

val tripdata = spark.read
    .option("header", "true")
    .schema(schema)
    .csv("/data/yellow_tripdata_2019-01.csv")

tripdata.createOrReplaceTempView("tripdata")

val df = spark.sql("""
    SELECT passenger_count, MAX(fare_amount)
    FROM tripdata
    GROUP BY passenger_count
""")

df.show()
// Query took 14418 ms 
```

KQuery 对于此类查询的性能具有竞争力。Spark 对于中小型数据集有更多开销，但通过其分布式执行能力，在处理非常大的数据集时扩展性更好。

## 错误处理

错误可能出现在任何阶段：

+   解析：SQL 中的语法错误

+   规划：未知表或列名，类型不匹配

+   执行：运行时错误，如除以零、文件未找到

KQuery 目前会抛出异常来处理错误。一个生产系统会提供具有源位置和有用信息的结构化错误类型。

## 我们所构建的内容

到目前为止，我们有一个可以工作的查询引擎，它能：

+   读取 CSV 文件

+   执行 SQL 查询

+   执行 DataFrame 查询

+   优化查询计划

+   批量处理数据

剩余章节涵盖了更高级的主题：单机内的并行执行，以及集群间的分布式执行。

*本书也以 ePub、MOBI 和 PDF 格式可供购买，详情请访问 [`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work)*

**版权 © 2020-2025 安迪·格鲁夫。版权所有。**
