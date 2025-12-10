# 数据帧 API

> 原文：[`howqueryengineswork.com/06-dataframe.html`](https://howqueryengineswork.com/06-dataframe.html)

*本章讨论的源代码可以在[KQuery 项目](https://github.com/andygrove/how-query-engines-work)的`logical-plan`模块中找到。*

这更紧凑，但更难阅读。嵌套是从内到外进行的，这与我们思考查询执行的方式相反（先扫描，然后过滤，最后投影）。

## 艰难构建计划

考虑这个查询：

```rs
SELECT id, first_name, last_name, state, salary
FROM employee
WHERE state = 'CO' 
```

要构建逻辑计划，我们分别构建每个部分，然后将它们连接起来：

```rs
val csv = CsvDataSource("employee.csv")
val scan = Scan("employee", csv, listOf())
val filterExpr = Eq(Column("state"), LiteralString("CO"))
val selection = Selection(scan, filterExpr)
val projectionList = listOf(
    Column("id"),
    Column("first_name"),
    Column("last_name"),
    Column("state"),
    Column("salary")
)
val plan = Projection(selection, projectionList) 
```

这可以工作，但较为冗长，代码结构并不反映查询结构。我们可以通过嵌套构造函数来稍微改进这一点：

```rs
val plan = Projection(
    Selection(
        Scan("employee", CsvDataSource("employee.csv"), listOf()),
        Eq(Column("state"), LiteralString("CO"))
    ),
    listOf(
        Column("id"),
        Column("first_name"),
        Column("last_name"),
        Column("state"),
        Column("salary")
    )
) 
```

[上一章展示了如何将查询表示为逻辑计划。但手动构建这些计划是繁琐的。本章介绍了数据帧 API，这是一个流畅的接口，使构建逻辑计划变得自然且易于阅读。]

## 数据帧方法

数据帧封装了一个逻辑计划，并提供返回新数据帧的方法。每次方法调用都会向计划添加一个节点。这创建了一个从上到下按执行顺序读取的流畅 API：

```rs
val df = ctx.csv("employee.csv")
    .filter(Eq(Column("state"), LiteralString("CO")))
    .project(listOf(
        Column("id"),
        Column("first_name"),
        Column("last_name"),
        Column("state"),
        Column("salary")
    )) 
```

这样理解：从 CSV 文件开始，筛选出科罗拉多州的数据，投影我们想要的列。代码结构与思维模型相匹配。

## 数据帧接口

接口很简单：

```rs
interface DataFrame {

  / Apply a projection */
  fun project(expr: List<LogicalExpr>): DataFrame

  / Apply a filter */
  fun filter(expr: LogicalExpr): DataFrame

  / Aggregate */
  fun aggregate(
      groupBy: List<LogicalExpr>,
      aggregateExpr: List<AggregateExpr>
  ): DataFrame

  / Join with another DataFrame */
  fun join(right: DataFrame, joinType: JoinType, condition: LogicalExpr): DataFrame

  / Returns the schema of the data that will be produced by this DataFrame. */
  fun schema(): Schema

  / Get the logical plan */
  fun logicalPlan(): LogicalPlan
} 
```

每个转换方法（`project`、`filter`、`aggregate`、`join`）都返回一个新的数据帧。这使方法链式调用成为可能。`schema`方法暴露输出模式以供检查。`logicalPlan`方法在需要优化或执行时检索底层计划。

## 实现

实现封装了一个逻辑计划，并在每次方法调用时创建新的计划节点：

```rs
class DataFrameImpl(private val plan: LogicalPlan) : DataFrame {

  override fun project(expr: List<LogicalExpr>): DataFrame {
    return DataFrameImpl(Projection(plan, expr))
  }

  override fun filter(expr: LogicalExpr): DataFrame {
    return DataFrameImpl(Selection(plan, expr))
  }

  override fun aggregate(
      groupBy: List<LogicalExpr>,
      aggregateExpr: List<AggregateExpr>
  ): DataFrame {
    return DataFrameImpl(Aggregate(plan, groupBy, aggregateExpr))
  }

  override fun join(
      right: DataFrame,
      joinType: JoinType,
      condition: LogicalExpr
  ): DataFrame {
    return DataFrameImpl(Join(plan, right.logicalPlan(), joinType, condition))
  }

  override fun schema(): Schema {
    return plan.schema()
  }

  override fun logicalPlan(): LogicalPlan {
    return plan
  }
} 
```

每个方法都使用当前计划作为输入构建一个新的逻辑计划节点，然后将其包装在一个新的数据帧中。原始数据帧保持不变（数据帧是不可变的），因此可以从任何点分支：

```rs
val employees = ctx.csv("employee.csv")
val colorado = employees.filter(Eq(Column("state"), LiteralString("CO")))
val texas = employees.filter(Eq(Column("state"), LiteralString("TX"))) 
```

连接根据条件组合两个数据帧：

```rs
val employees = ctx.csv("employee.csv")
val departments = ctx.csv("department.csv")

val joined = employees.join(
    departments,
    JoinType.INNER,
    Eq(Column("dept_id"), Column("id"))
) 
```

连接章节详细介绍了连接类型和算法。

## 执行上下文

我们需要一个起点来构建数据帧。执行上下文从数据源创建初始数据帧：

```rs
class ExecutionContext {

  fun csv(filename: String): DataFrame {
    return DataFrameImpl(Scan(filename, CsvDataSource(filename), listOf()))
  }

  fun parquet(filename: String): DataFrame {
    return DataFrameImpl(Scan(filename, ParquetDataSource(filename), listOf()))
  }
} 
```

后续章节将扩展此上下文以处理查询执行。目前，它只是创建数据帧。

## 便捷方法

基本 API 功能正常，但仍然较为冗长。Kotlin 的特性使我们能够使其更加简洁。

辅助函数可以简洁地创建表达式：

```rs
fun col(name: String) = Column(name)
fun lit(value: String) = LiteralString(value)
fun lit(value: Long) = LiteralLong(value)
fun lit(value: Double) = LiteralDouble(value) 
```

中缀操作符允许我们自然地编写表达式：

```rs
infix fun LogicalExpr.eq(rhs: LogicalExpr): LogicalExpr = Eq(this, rhs)
infix fun LogicalExpr.neq(rhs: LogicalExpr): LogicalExpr = Neq(this, rhs)
infix fun LogicalExpr.gt(rhs: LogicalExpr): LogicalExpr = Gt(this, rhs)
infix fun LogicalExpr.gteq(rhs: LogicalExpr): LogicalExpr = GtEq(this, rhs)
infix fun LogicalExpr.lt(rhs: LogicalExpr): LogicalExpr = Lt(this, rhs)
infix fun LogicalExpr.lteq(rhs: LogicalExpr): LogicalExpr = LtEq(this, rhs)
infix fun LogicalExpr.mult(rhs: LogicalExpr): LogicalExpr = Multiply(this, rhs)
infix fun LogicalExpr.alias(name: String): LogicalExpr = Alias(this, name) 
```

现在，我们可以编写几乎像 SQL 一样的查询：

```rs
val df = ctx.csv("employee.csv")
    .filter(col("state") eq lit("CO"))
    .project(listOf(
        col("id"),
        col("first_name"),
        col("last_name"),
        col("salary"),
        (col("salary") mult lit(0.1)) alias "bonus"
    ))
    .filter(col("bonus") gt lit(1000)) 
```

这表示：读取 CSV 文件，保留州等于 CO 的行，计算 id、names、salary 以及 10%的奖金列，然后只保留奖金超过 1000 的行。

## 数据帧与 SQL

数据框（DataFrames）和 SQL 都描述了您想要的数据。为什么提供两种？

SQL 对分析师来说很熟悉，可以作为字符串嵌入到应用程序中。但 SQL 字符串对编译器来说是透明的。错误和类型错误只有在运行时才会出现。

数据框与编程语言集成。编译器会捕获方法名错误。IDE 提供自动完成功能。您可以使用常规编程结构动态构建查询：

```rs
var df = ctx.csv("employee.csv")

if (stateFilter != null) {
    df = df.filter(col("state") eq lit(stateFilter))
}

if (minSalary != null) {
    df = df.filter(col("salary") gteq lit(minSalary))
} 
```

大多数现代查询引擎都支持这两种接口。用户根据自己的需求进行选择。

## 底层计划

无论我们如何构建它，结果都是一个逻辑计划。我们的示例查询：

```rs
val df = ctx.csv("employee.csv")
    .filter(col("state") eq lit("CO"))
    .project(listOf(col("id"), col("first_name"), col("last_name"), col("salary"))) 
```

生成以下计划：

```rs
Projection: #id, #first_name, #last_name, #salary
  Filter: #state = 'CO'
    Scan: employee.csv; projection=None 
```

数据框只是构建此树的一种方便方式。一旦构建完成，计划就会经过优化和物理规划，无论它是如何创建的。

*本书也以 ePub、MOBI 和 PDF 格式在 [`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work) 上提供购买*

**版权所有 © 2020-2025 安迪·格鲁夫。保留所有权利。**
