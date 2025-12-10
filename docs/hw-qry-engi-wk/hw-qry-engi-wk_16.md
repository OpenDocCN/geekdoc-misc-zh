# 查询优化

> 原文：[`howqueryengineswork.com/12-optimizations.html`](https://howqueryengineswork.com/12-optimizations.html)

*本章讨论的源代码可以在[KQuery 项目](https://github.com/andygrove/how-query-engines-work)的`optimizer`模块中找到。*

一个执行计划与所写内容完全一致的查询引擎将产生正确的结果，但可能很慢。编写 SQL 或 DataFrame 查询的用户自然地表达他们想要什么，而不是如何高效地计算。优化器将逻辑计划转换为等效但更快的计划。

## 为什么要优化？

考虑一个先连接两个表然后进行过滤的查询：

```rs
SELECT e.name, d.dept_name
FROM employees e
JOIN departments d ON e.dept_id = d.id
WHERE e.state = 'CO' 
```

这样执行实际上意味着：连接所有员工与所有部门，然后过滤到科罗拉多州。如果有 10 万名员工，其中只有 5000 人在科罗拉多州，我们将进行 95,000 次不必要的连接查找。

一个优化器认识到对`state`的过滤只触及`employees`表，可以在连接之前应用：

```rs
Before optimization:
  Filter: state = 'CO'
    Join: e.dept_id = d.id
      Scan: employees
      Scan: departments

After optimization:
  Join: e.dept_id = d.id
    Filter: state = 'CO'
      Scan: employees
    Scan: departments 
```

现在我们只连接 5000 名员工而不是 10 万名。这会产生相同的结果，但速度要快得多。

## 基于规则的优化

KQuery 使用基于规则的优化：一组改进计划的转换规则。规则按顺序应用，每个规则都接受一个逻辑计划并返回一个（希望更好）的逻辑计划。

```rs
interface OptimizerRule {
    fun optimize(plan: LogicalPlan): LogicalPlan
}

class Optimizer {
    fun optimize(plan: LogicalPlan): LogicalPlan {
        var result = plan
        result = ProjectionPushDownRule().optimize(result)
        // Additional rules would be applied here
        return result
    }
} 
```

规则通过遍历计划树并对其进行修改来工作。这种功能性的方法（构建一个新树而不是修改旧树）更简单且错误更少。

## 投影下推

投影下推通过只读取查询实际使用的列来减少内存使用。如果一个表有 50 列，但查询只引用了 3 列，我们应该只读取这 3 列。

该规则通过：

1.  从上到下遍历计划，收集每个操作符中引用的列名

1.  当达到扫描时，用只投影所需列的扫描替换它

首先，我们需要一个辅助工具从表达式提取列引用：

```rs
fun extractColumns(expr: LogicalExpr, input: LogicalPlan, accum: MutableSet<String>) {
    when (expr) {
        is Column -> accum.add(expr.name)
        is ColumnIndex -> accum.add(input.schema().fields[expr.i].name)
        is BinaryExpr -> {
            extractColumns(expr.l, input, accum)
            extractColumns(expr.r, input, accum)
        }
        is Alias -> extractColumns(expr.expr, input, accum)
        is CastExpr -> extractColumns(expr.expr, input, accum)
        is LiteralString, is LiteralLong, is LiteralDouble -> { }
        else -> throw IllegalStateException("Unsupported: $expr")
    }
} 
```

然后是规则本身：

```rs
class ProjectionPushDownRule : OptimizerRule {

    override fun optimize(plan: LogicalPlan): LogicalPlan {
        return pushDown(plan, mutableSetOf())
    }

    private fun pushDown(plan: LogicalPlan, columnNames: MutableSet<String>): LogicalPlan {
        return when (plan) {
            is Projection -> {
                extractColumns(plan.expr, plan.input, columnNames)
                val input = pushDown(plan.input, columnNames)
                Projection(input, plan.expr)
            }
            is Selection -> {
                extractColumns(plan.expr, plan.input, columnNames)
                val input = pushDown(plan.input, columnNames)
                Selection(input, plan.expr)
            }
            is Aggregate -> {
                extractColumns(plan.groupExpr, plan.input, columnNames)
                extractColumns(plan.aggregateExpr.map { it.expr }, plan.input, columnNames)
                val input = pushDown(plan.input, columnNames)
                Aggregate(input, plan.groupExpr, plan.aggregateExpr)
            }
            is Scan -> {
                val validFields = plan.dataSource.schema().fields.map { it.name }.toSet()
                val projection = validFields.filter { columnNames.contains(it) }.sorted()
                Scan(plan.path, plan.dataSource, projection)
            }
            else -> throw IllegalStateException("Unsupported: $plan")
        }
    }
} 
```

给定此计划：

```rs
Projection: #id, #first_name, #last_name
    Filter: #state = 'CO'
        Scan: employee; projection=None 
```

优化器产生：

```rs
Projection: #id, #first_name, #last_name
    Filter: #state = 'CO'
        Scan: employee; projection=[first_name, id, last_name, state] 
```

扫描现在只读取表中的四个列而不是所有列。对于像 Parquet 这样的列式格式，这大大减少了 I/O。

## 谓词下推

谓词下推将过滤器移得更接近数据源，减少了后续操作符处理的行数。

考虑：

```rs
Projection: #dept_name, #first_name, #last_name
    Filter: #state = 'CO'
        Join: #employee.dept_id = #dept.id
            Scan: employee
            Scan: dept 
```

过滤器只引用`employee`列，因此它可以移动到连接下面：

```rs
Projection: #dept_name, #first_name, #last_name
    Join: #employee.dept_id = #dept.id
        Filter: #state = 'CO'
            Scan: employee
        Scan: dept 
```

现在连接处理的行数更少。这种优化在更大的表和更选择性的谓词中变得更加重要。

实现必须分析每个谓词引用哪些表，并且只推送引用单个表的谓词到连接下面。引用连接两边的谓词不能推到它下面。

KQuery 目前不实现谓词下推，但其模式与投影下推相似：遍历树，识别机会，将过滤器向下移动重建。

## 消除公共子表达式

当相同的表达式出现多次时，我们可以计算一次并重用结果：

```rs
SELECT sum(price * qty) AS total_price,
       sum(price * qty * tax_rate) AS total_tax
FROM sales 
```

表达式`price * qty`出现在两个聚合中。我们不必每行计算两次，可以添加一个中间投影：

原始：

```rs
Aggregate: sum(#price * #qty), sum(#price * #qty * #tax_rate)
    Scan: sales 
```

优化后：

```rs
Aggregate: sum(#subtotal), sum(#subtotal * #tax_rate)
    Projection: #price * #qty AS subtotal, #tax_rate
        Scan: sales 
```

这是在投影中每行进行一次乘法（与原始聚合中的每行两次乘法）之间的权衡。对于大型数据集，这会累积起来。

KQuery 不实现此优化，但方法涉及：

1.  寻找多次出现的表达式

1.  创建一个投影，一次计算并使用生成的名称

1.  重新编写后续操作符以引用计算出的列

## 基于成本的优化

基于规则的优化无条件地应用转换。基于成本的优化估计不同计划的成本并选择最便宜的。

考虑连接顺序。对于三个表 A、B、C：

+   (A JOIN B) JOIN C

+   (A JOIN C) JOIN B

+   (B JOIN C) JOIN A

所有这些都会产生相同的结果，但性能会根据表大小和连接选择性而有很大差异。如果 A 有 100 万行，B 有 100 行，C 有 1 万行，先连接 B 和 C（最多 1 百万个中间行）然后再连接 A 可能比先从 A 开始连接要快。

基于成本的优化器需要统计信息：

+   表行数

+   列基数（不同值的数量）

+   值分布（直方图）

+   每列的最小/最大值

有统计信息，优化器可以估计：

+   过滤器将产生多少行（选择性）

+   连接将产生多少行

+   哈希表的内存需求

优化器生成候选计划，为每个计划估计成本，并选择最便宜的。

### 统计挑战

基于成本的优化听起来很棒，但存在实际挑战：

收集统计信息是昂贵的。扫描数以 TB 计的数据来构建直方图需要时间。对于即席查询，这种开销可能超过优化收益。

统计信息会过时。随着数据的变化，统计信息会偏离现实。过时的统计信息会导致糟糕的计划。

估计误差会累积。每个估计都有误差。在一个包含许多操作符的复杂计划中，误差会相乘，可能导致灾难性的糟糕计划。

一些格式提供部分统计信息。Parquet 和 ORC 文件包括每列数据块的最小/最大值和行数。这有所帮助，但不足以进行准确的基数估计。

KQuery 仅使用基于规则的优化。像 Spark、Presto 和传统数据库这样的生产系统在基于成本的优化上投入了大量资金，但这仍然是一个活跃的研究和工程领域。

## 其他优化

查询引擎实现了许多其他优化：

常量折叠：在计划时评估常量表达式。`WHERE date > '2024-01-01' AND 1 = 1`变为`WHERE date > '2024-01-01'`。

去除死列：当下游不需要时，从中间结果中移除列。

连接重排序：选择连接的顺序以最小化中间结果的大小。

限制后推：将 LIMIT 操作符后推以减少工作量。如果我们只需要 10 行，就提前停止。

分区剪枝：根据分区键跳过无法包含匹配数据的分区读取。

正确的优化组合取决于工作负载和数据特征。基于规则的简单优化提供了显著的好处，同时复杂性最小。

*本书也以 ePub、MOBI 和 PDF 格式提供购买，详情请访问[`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work)*

**版权所有 © 2020-2025 安迪·格鲁夫。保留所有权利。**
