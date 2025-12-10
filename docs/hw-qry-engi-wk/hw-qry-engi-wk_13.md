# 查询规划器

> 原文：[`howqueryengineswork.com/09-query-planner.html`](https://howqueryengineswork.com/09-query-planner.html)

*本章讨论的源代码可以在[KQuery 项目](https://github.com/andygrove/how-query-engines-work)的`query-planner`模块中找到。*

现在我们有了描述要计算什么的逻辑计划以及描述如何计算它的物理计划。查询规划器连接这些：它接受一个逻辑计划并生成一个可以执行的物理计划。

## 查询规划器的作用

查询规划器遍历逻辑计划树并创建相应的物理计划树。对于每个逻辑运算符，它创建相应的物理运算符。对于每个逻辑表达式，它创建相应的物理表达式。

一些翻译是直接的。逻辑`Scan`变为物理`ScanExec`。逻辑`Add`表达式变为物理`AddExpression`。

其他翻译涉及选择。逻辑`Aggregate`可能成为`HashAggregateExec`或`SortAggregateExec`，这取决于输入是否已排序。逻辑`Join`可能成为散列连接、排序合并连接或嵌套循环连接。这些决策对性能有重大影响。

KQuery 的查询规划器很简单：它做出固定的选择（例如，总是散列聚合）。生产查询规划器使用基于成本的优化来估计哪个物理计划将最快。

## 查询规划器类

规划器有两个主要方法：一个用于计划，一个用于表达式。

```rs
class QueryPlanner {

    fun createPhysicalPlan(plan: LogicalPlan): PhysicalPlan {
        return when (plan) {
            is Scan -> ...
            is Selection -> ...
            is Projection -> ...
            is Aggregate -> ...
            else -> throw IllegalStateException("Unknown plan: $plan")
        }
    }

    fun createPhysicalExpr(expr: LogicalExpr, input: LogicalPlan): Expression {
        return when (expr) {
            is Column -> ...
            is LiteralLong -> ...
            is BinaryExpr -> ...
            else -> throw IllegalStateException("Unknown expression: $expr")
        }
    }
} 
```

两种方法都使用模式匹配来根据类型进行分发。两者都是递归的：翻译`Projection`需要翻译其输入计划，翻译`BinaryExpr`需要翻译其子表达式。

## 翻译表达式

### 列引用

逻辑表达式通过名称引用列。物理表达式使用列索引以提高效率。规划器执行此查找：

```rs
is Column -> {
    val i = input.schema().fields.indexOfFirst { it.name == expr.name }
    if (i == -1) {
        throw SQLException("No column named '${expr.name}'")
    }
    ColumnExpression(i)
} 
```

如果列在输入模式中不存在，我们抛出错误。如果逻辑计划已验证，则不应发生这种情况，但检查提供了安全网。

### 文字

文字翻译是简单的，因为我们只需复制值：

```rs
is LiteralLong -> LiteralLongExpression(expr.n)
is LiteralDouble -> LiteralDoubleExpression(expr.n)
is LiteralString -> LiteralStringExpression(expr.str) 
```

### 二进制表达式

二进制表达式需要递归地翻译两个操作数，然后创建适当的物理运算符：

```rs
is BinaryExpr -> {
    val l = createPhysicalExpr(expr.l, input)
    val r = createPhysicalExpr(expr.r, input)
    when (expr) {
        // Comparison
        is Eq -> EqExpression(l, r)
        is Neq -> NeqExpression(l, r)
        is Gt -> GtExpression(l, r)
        is GtEq -> GtEqExpression(l, r)
        is Lt -> LtExpression(l, r)
        is LtEq -> LtEqExpression(l, r)

        // Boolean
        is And -> AndExpression(l, r)
        is Or -> OrExpression(l, r)

        // Math
        is Add -> AddExpression(l, r)
        is Subtract -> SubtractExpression(l, r)
        is Multiply -> MultiplyExpression(l, r)
        is Divide -> DivideExpression(l, r)

        else -> throw IllegalStateException("Unsupported: $expr")
    }
} 
```

### 别名

别名很有趣：它们没有物理表示。别名只是为表达式提供一个名称，以便在规划中使用。在执行时，我们评估底层表达式：

```rs
is Alias -> {
    // Aliases only affect naming during planning, not execution
    createPhysicalExpr(expr.expr, input)
} 
```

## 翻译计划

### 扫描

扫描是最简单的翻译。我们通过数据源和投影传递：

```rs
is Scan -> {
    ScanExec(plan.dataSource, plan.projection)
} 
```

### 选择（过滤器）

选择将输入计划和过滤器表达式进行翻译：

```rs
is Selection -> {
    val input = createPhysicalPlan(plan.input)
    val filterExpr = createPhysicalExpr(plan.expr, plan.input)
    SelectionExec(input, filterExpr)
} 
```

注意，`createPhysicalExpr` 接收 `plan.input`（逻辑输入），而不是 `input`（物理输入）。我们需要逻辑模式来解析列名到索引。

### 投影

投影将输入和每个投影表达式进行转换：

```rs
is Projection -> {
    val input = createPhysicalPlan(plan.input)
    val projectionExpr = plan.expr.map { createPhysicalExpr(it, plan.input) }
    val projectionSchema = Schema(plan.expr.map { it.toField(plan.input) })
    ProjectionExec(input, projectionSchema, projectionExpr)
} 
```

我们从逻辑表达式中推导输出模式，因为它们知道它们的输出类型。

### 聚合

聚合转换涉及分组表达式和聚合函数：

```rs
is Aggregate -> {
    val input = createPhysicalPlan(plan.input)
    val groupExpr = plan.groupExpr.map { createPhysicalExpr(it, plan.input) }
    val aggregateExpr = plan.aggregateExpr.map {
        when (it) {
            is Max -> MaxExpression(createPhysicalExpr(it.expr, plan.input))
            is Min -> MinExpression(createPhysicalExpr(it.expr, plan.input))
            is Sum -> SumExpression(createPhysicalExpr(it.expr, plan.input))
            is Avg -> AvgExpression(createPhysicalExpr(it.expr, plan.input))
            is Count -> CountExpression(createPhysicalExpr(it.expr, plan.input))
            else -> throw IllegalStateException("Unsupported: $it")
        }
    }
    HashAggregateExec(input, groupExpr, aggregateExpr, plan.schema())
} 
```

注意，我们总是创建 `HashAggregateExec`。一个更复杂的规划器可能会在输入已经按分组列排序时选择 `SortAggregateExec`。

## 完整示例

考虑这个查询：

```rs
SELECT department, AVG(salary)
FROM employees
WHERE state = 'CO'
GROUP BY department 
```

逻辑计划：

```rs
Aggregate: groupBy=[#department], aggr=[AVG(#salary)]
    Selection: #state = 'CO'
        Scan: employees 
```

查询规划器自上而下遍历：

1.  聚合：为输入创建物理计划，翻译表达式

    +   递归翻译选择

1.  选择：为输入创建物理计划，翻译过滤表达式

    +   递归翻译扫描

1.  扫描：直接创建 `ScanExec`

自下而上构建物理计划：

1.  `ScanExec(employeesDataSource, [])`

1.  `SelectionExec(scanExec, EqExpression(ColumnExpression(2), LiteralStringExpression("CO")))`

1.  `HashAggregateExec(selectionExec, [ColumnExpression(0)], [AvgExpression(ColumnExpression(3))], schema)`

结果是一个可执行的物理计划。

## 哪里适合优化 WHERE

这里显示的查询规划器进行直接翻译。每个逻辑运算符正好对应一个物理运算符。

实际上，优化发生在逻辑规划和物理规划之间：

1.  将 SQL 解析为逻辑计划

1.  优化逻辑计划（重新排序连接，向下推算谓词等）

1.  将优化的逻辑计划转换为物理计划

或者，一些系统执行物理优化：

1.  将 SQL 解析为逻辑计划

1.  生成多个候选物理计划

1.  估算每个的成本

1.  选择最便宜的

KQuery 使用第一种方法，具有简单的优化器（在下一章“连接”和“子查询”之后介绍）。这里的规划器假设它接收一个已经优化的逻辑计划。

## 错误处理

查询规划器应该捕获逻辑计划验证中遗漏的错误：

+   未知列名

+   不支持的表达式类型

+   类型不匹配

在 KQuery 中，这些会抛出异常。生产系统会生成带有源位置的格式化错误消息。

*本书也以 ePub、MOBI 和 PDF 格式提供购买，请访问 [`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work)*

**版权所有 © 2020-2025 安迪·格鲁夫。保留所有权利。**
