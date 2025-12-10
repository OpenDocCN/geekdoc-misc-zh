# 逻辑计划与表达式

> 原文：[`howqueryengineswork.com/05-logical-plan.html`](https://howqueryengineswork.com/05-logical-plan.html)

*本章讨论的源代码可以在 [KQuery 项目](https://github.com/andygrove/how-query-engines-work) 的 `logical-plan` 模块中找到。*

当你编写一个 SQL 查询时，你描述了你想要的数据。查询引擎必须找出如何获取它。第一步是构建一个逻辑计划：一个表示计算但不指定确切执行方式的树结构。

考虑这个查询：

```rs
SELECT name, salary * 1.1 AS new_salary
FROM employees
WHERE department = 'Engineering' 
```

在我们执行此操作之前，我们需要一个结构化的表示。逻辑计划捕获：

+   从 `employees` 表读取

+   仅保留 `department = 'Engineering'` 的行

+   为每一行剩余的行计算 `name` 和 `salary * 1.1`

本章介绍如何将这些操作表示为逻辑计划和表达式的树。

## Why Separate Logical from Physical?

我们可以直接从 SQL 跳到执行，但将逻辑规划和物理规划分开有优势：

1.  验证：在进行任何工作之前，我们可以检查列是否存在以及类型是否兼容

1.  优化：我们可以转换逻辑计划以使其更高效

1.  灵活性：相同的逻辑计划可能会根据数据大小或可用资源以不同的方式执行

逻辑计划说“过滤行 X”，但没有指定是否使用索引、散列表或顺序扫描。这些是稍后决定的物理执行细节。

## The LogicalPlan Interface

逻辑计划表示一个关系：一组具有已知模式的行。每个计划可以作为输入有子计划，形成一个树。

```rs
interface LogicalPlan {

  / Returns the schema of the data that will be produced by this logical plan. */
  fun schema(): Schema

  /
   * Returns the children (inputs) of this logical plan. This method is used to
   * enable use of the visitor pattern to walk a query tree.
   */
  fun children(): List<LogicalPlan>
} 
```

schema() 返回输出模式，即此计划产生的列及其类型。这对于验证是必不可少的。如果后续计划引用了一个列，我们可以检查它是否存在于输入模式中。

children() 返回输入计划。扫描没有子计划（它从数据源读取）。一个过滤计划有一个子计划（它的输入）。一个连接有两个子计划（左输入和右输入）。此方法使遍历计划树成为可能。

## Printing Logical Plans

调试查询引擎需要看到计划的样子。我们将计划打印为缩进的树，其中子节点嵌套在父节点下：

```rs
fun format(plan: LogicalPlan, indent: Int = 0): String {
  val b = StringBuilder()
  0.until(indent).forEach { b.append("\t") }
  b.append(plan.toString()).append("\n")
  plan.children().forEach { b.append(format(it, indent + 1)) }
  return b.toString()
} 
```

我们的示例查询可能打印如下：

```rs
Projection: #name, #salary * 1.1 AS new_salary
  Filter: #department = 'Engineering'
    Scan: employees; projection=None 
```

从下往上阅读：扫描员工表，筛选到工程部门，投影我们想要的列。

## Logical Expressions

计划描述数据流。表达式描述计划内的计算。一个过滤计划包含一个对每一行评估为真或假的表达式。一个投影计划包含计算输出列的表达式。

表达式可以是简单的（列引用、文字值）或复杂的（嵌套算术、函数调用）。以下是常见的表达式类型：

| 表达式类型 | 示例 |
| --- | --- |
| 文字值 | `"hello"`, `12.34`, `true` |
| 列引用 | `user_id`, `first_name`, `salary` |
| 数学表达式 | `salary * 0.1`, `price + tax` |
| 比较表达式 | `age >= 21`, `status != 'inactive'` |
| 布尔表达式 | `age >= 21 AND country = 'US'` |
| 聚合表达式 | `MIN(salary)`, `MAX(salary)`, `SUM(amount)`, `COUNT(*)` |
| 标量函数 | `UPPER(name)`, `CONCAT(first_name, ' ', last_name)` |
| 别名表达式 | `salary * 1.1 AS new_salary` |

表达式形成树。表达式 `(a + b) * c` 在根处有一个乘法操作，有两个子节点：一个加法表达式（子节点为 `a` 和 `b`）和一个列引用 `c`。

## LogicalExpr 接口

在规划期间，我们需要知道表达式产生的值类型。如果你写 `a + b`，那么只有当两个列都是数值时才是有效的。接口捕捉这一点：

```rs
interface LogicalExpr {

  /
   * Return meta-data about the value that will be produced by this expression
   * when evaluated against a particular input.
   */
  fun toField(input: LogicalPlan): Field
} 
```

`toField` 方法返回表达式的输出名称和数据类型。它接受输入计划，因为某些表达式依赖于输入模式。列引用的类型是它引用的列的类型。比较表达式总是返回布尔值，无论其输入如何。

## 列表达式

最简单的表达式通过名称引用一个列：

```rs
class Column(val name: String) : LogicalExpr {

  override fun toField(input: LogicalPlan): Field {
    return input.schema().fields.find { it.name == name }
        ?: throw SQLException("No column named '$name'")
  }

  override fun toString(): String {
    return "#$name"
  }
} 
```

`toField` 实现会在输入模式中查找列。如果不存在，则是一个错误，我们会在规划阶段而不是执行阶段捕获它。

`toString` 中的 `#` 前缀是一种约定，用于在打印计划时区分列引用和文字字符串。

## 文字表达式

类似于 `salary * 1.1` 的表达式需要表示文字值 `1.1`。我们需要为每种数据类型提供文字表达式：

```rs
class LiteralString(val str: String) : LogicalExpr {

  override fun toField(input: LogicalPlan): Field {
    return Field(str, ArrowTypes.StringType)
  }

  override fun toString(): String {
    return "'$str'"
  }
}

class LiteralLong(val n: Long) : LogicalExpr {

  override fun toField(input: LogicalPlan): Field {
    return Field(n.toString(), ArrowTypes.Int64Type)
  }

  override fun toString(): String {
    return n.toString()
  }
}

class LiteralDouble(val n: Double) : LogicalExpr {

  override fun toField(input: LogicalPlan): Field {
    return Field(n.toString(), ArrowTypes.DoubleType)
  }

  override fun toString(): String {
    return n.toString()
  }
} 
```

文字表达式不依赖于输入计划，因为它们的类型是固定的。

## 二进制表达式

大多数操作符接受两个输入：比较（`=`, `<`, `>`）、布尔逻辑（`AND`, `OR`）和算术（`+`, `-`, `*`, `/`）。我们可以在这之间共享结构：

```rs
abstract class BinaryExpr(
    val name: String,
    val op: String,
    val l: LogicalExpr,
    val r: LogicalExpr
) : LogicalExpr {

  override fun toString(): String {
    return "$l $op $r"
  }
} 
```

`name` 用来标识表达式类型。`op` 是打印时的操作符符号。`l` 和 `r` 分别是左操作数和右操作数。

### 比较和布尔表达式

比较和布尔运算符总是产生布尔结果：

```rs
abstract class BooleanBinaryExpr(
    name: String,
    op: String,
    l: LogicalExpr,
    r: LogicalExpr
) : BinaryExpr(name, op, l, r) {

  override fun toField(input: LogicalPlan): Field {
    return Field(name, ArrowTypes.BooleanType)
  }
}

// Comparisons
class Eq(l: LogicalExpr, r: LogicalExpr) : BooleanBinaryExpr("eq", "=", l, r)
class Neq(l: LogicalExpr, r: LogicalExpr) : BooleanBinaryExpr("neq", "!=", l, r)
class Gt(l: LogicalExpr, r: LogicalExpr) : BooleanBinaryExpr("gt", ">", l, r)
class GtEq(l: LogicalExpr, r: LogicalExpr) : BooleanBinaryExpr("gteq", ">=", l, r)
class Lt(l: LogicalExpr, r: LogicalExpr) : BooleanBinaryExpr("lt", "<", l, r)
class LtEq(l: LogicalExpr, r: LogicalExpr) : BooleanBinaryExpr("lteq", "<=", l, r)

// Boolean logic
class And(l: LogicalExpr, r: LogicalExpr) : BooleanBinaryExpr("and", "AND", l, r)
class Or(l: LogicalExpr, r: LogicalExpr) : BooleanBinaryExpr("or", "OR", l, r) 
```

### 数学表达式

在 KQuery 中，算术表达式保留左操作数的类型。这是一个简化的方法。一个生产系统会处理类型提升）：

```rs
abstract class MathExpr(
    name: String,
    op: String,
    l: LogicalExpr,
    r: LogicalExpr
) : BinaryExpr(name, op, l, r) {

  override fun toField(input: LogicalPlan): Field {
    return Field(name, l.toField(input).dataType)
  }
}

class Add(l: LogicalExpr, r: LogicalExpr) : MathExpr("add", "+", l, r)
class Subtract(l: LogicalExpr, r: LogicalExpr) : MathExpr("subtract", "-", l, r)
class Multiply(l: LogicalExpr, r: LogicalExpr) : MathExpr("mult", "*", l, r)
class Divide(l: LogicalExpr, r: LogicalExpr) : MathExpr("div", "/", l, r)
class Modulus(l: LogicalExpr, r: LogicalExpr) : MathExpr("mod", "%", l, r) 
```

## 聚合表达式

聚合函数将多行减少到单个值：`SUM`, `MIN`, `MAX`, `AVG`, `COUNT`。它们出现在聚合计划中（稍后介绍）并具有特殊语义。

```rs
abstract class AggregateExpr(
    val name: String,
    val expr: LogicalExpr
) : LogicalExpr {

  override fun toField(input: LogicalPlan): Field {
    return Field(name, expr.toField(input).dataType)
  }

  override fun toString(): String {
    return "$name($expr)"
  }
}

class Sum(input: LogicalExpr) : AggregateExpr("SUM", input)
class Min(input: LogicalExpr) : AggregateExpr("MIN", input)
class Max(input: LogicalExpr) : AggregateExpr("MAX", input)
class Avg(input: LogicalExpr) : AggregateExpr("AVG", input) 
```

大多数聚合函数返回与输入相同的类型。`COUNT` 不同，因为它总是返回一个整数：

```rs
class Count(input: LogicalExpr) : AggregateExpr("COUNT", input) {

  override fun toField(input: LogicalPlan): Field {
    return Field("COUNT", ArrowTypes.Int32Type)
  }
} 
```

## 别名表达式

SQL 的 `AS` 关键字用于重命名表达式的输出：

```rs
class Alias(val expr: LogicalExpr, val alias: String) : LogicalExpr {

  override fun toField(input: LogicalPlan): Field {
    return Field(alias, expr.toField(input).dataType)
  }

  override fun toString(): String {
    return "$expr as $alias"
  }
} 
```

别名改变名称但保留类型。

## 逻辑计划

定义了表达式后，我们可以构建使用它们的计划。

### Scan

`Scan` 从数据源读取。它是每个查询树的叶子节点，数据进入计划的地方。

```rs
class Scan(
    val path: String,
    val dataSource: DataSource,
    val projection: List<String>
) : LogicalPlan {

  val schema = deriveSchema()

  override fun schema(): Schema {
    return schema
  }

  private fun deriveSchema(): Schema {
    val schema = dataSource.schema()
    if (projection.isEmpty()) {
      return schema
    } else {
      return schema.select(projection)
    }
  }

  override fun children(): List<LogicalPlan> {
    return listOf()
  }

  override fun toString(): String {
    return if (projection.isEmpty()) {
      "Scan: $path; projection=None"
    } else {
      "Scan: $path; projection=$projection"
    }
  }
} 
```

`projection` 参数列出了要读取的列。如果为空，则读取所有列。这种优化很重要，因为读取较少的列意味着更少的 I/O 和更少的内存。

### Selection (Filter)

`Selection` 仅保留表达式评估为真的行。这对应于 SQL 的 `WHERE` 子句。

```rs
class Selection(
    val input: LogicalPlan,
    val expr: LogicalExpr
) : LogicalPlan {

  override fun schema(): Schema {
    return input.schema()  // filtering doesn't change the schema
  }

  override fun children(): List<LogicalPlan> {
    return listOf(input)
  }

  override fun toString(): String {
    return "Filter: $expr"
  }
} 
```

架构保持不变，因为过滤只删除行，不删除列。

### Projection

`Projection` 通过表达式计算新的列。这对应于 SQL 的 `SELECT` 列。

```rs
class Projection(
    val input: LogicalPlan,
    val expr: List<LogicalExpr>
) : LogicalPlan {

  override fun schema(): Schema {
    return Schema(expr.map { it.toField(input) })
  }

  override fun children(): List<LogicalPlan> {
    return listOf(input)
  }

  override fun toString(): String {
    return "Projection: ${expr.map { it.toString() }.joinToString(", ")}"
  }
} 
```

输出架构来自表达式。如果您投影 `name` 和 `salary * 1.1 AS bonus`，输出架构有两个具有这些名称和适当类型的列。

### Aggregate

`Aggregate` 对行进行分组并计算聚合函数。这对应于 SQL 的 `GROUP BY` 与聚合函数。

```rs
class Aggregate(
    val input: LogicalPlan,
    val groupExpr: List<LogicalExpr>,
    val aggregateExpr: List<AggregateExpr>
) : LogicalPlan {

  override fun schema(): Schema {
    return Schema(
      groupExpr.map { it.toField(input) } +
      aggregateExpr.map { it.toField(input) }
    )
  }

  override fun children(): List<LogicalPlan> {
    return listOf(input)
  }

  override fun toString(): String {
    return "Aggregate: groupExpr=$groupExpr, aggregateExpr=$aggregateExpr"
  }
} 
```

输出架构首先包含分组列，然后是聚合结果。对于 `SELECT department, AVG(salary) FROM employees GROUP BY department`，输出有两列：`department` 和 `AVG(salary)`。

### Join

`Join` 根据条件结合两个输入的行。与迄今为止我们所看到的计划不同，连接有两个子节点：左输入和右输入。

```rs
class Join(
    val left: LogicalPlan,
    val right: LogicalPlan,
    val joinType: JoinType,
    val condition: LogicalExpr
) : LogicalPlan {

  override fun schema(): Schema {
    return Schema(left.schema().fields + right.schema().fields)
  }

  override fun children(): List<LogicalPlan> {
    return listOf(left, right)
  }

  override fun toString(): String {
    return "Join: type=$joinType, condition=$condition"
  }
}

enum class JoinType {
  INNER, LEFT, RIGHT, FULL, SEMI, ANTI
} 
```

输出架构结合了两个输入的列。连接类型决定了输出中出现的行：内连接只返回匹配的行，外连接包括未匹配的行并用 null 填充，等等。

连接是关系查询的基本，但伴随着显著的复杂性：多种连接类型、具有不同性能特性的各种连接算法以及优化挑战。连接章节深入探讨了这些主题。

## Putting It Together

以下是如何将我们的示例查询转换为逻辑计划：

```rs
SELECT name, salary * 1.1 AS new_salary
FROM employees
WHERE department = 'Engineering' 
```

自下而上构建：

```rs
val scan = Scan("employees", employeeDataSource, listOf())

val filter = Selection(
    scan,
    Eq(Column("department"), LiteralString("Engineering"))
)

val project = Projection(
    filter,
    listOf(
        Column("name"),
        Alias(Multiply(Column("salary"), LiteralDouble(1.1)), "new_salary")
    )
) 
```

打印：

```rs
Projection: #name, #salary * 1.1 as new_salary
  Filter: #department = 'Engineering'
    Scan: employees; projection=None 
```

此逻辑计划现在可以验证（列是否存在？），优化（能否将投影推入扫描？），并最终转换为执行物理计划。

## Serialization

查询计划有时需要序列化：通过网络发送，存储以供以后使用，或在不同语言的系统之间传递。

选项包括特定语言的序列化（Java 中的 Jackson JSON，Kotlin 中的 kotlinx.serialization）或语言无关的格式，如 Protocol Buffers 或 Avro。

一个名为 [Substrait](https://substrait.io/) 的新标准旨在为关系代数提供跨语言序列化。这很令人兴奋，因为它使得混合组件成为可能：使用 Apache Calcite 在 Java 中进行查询规划，序列化为 Substrait，在 Rust 或 C++ 引擎中执行。如果您今天正在构建查询引擎，Substrait 值得调查。

*本书也提供 ePub、MOBI 和 PDF 格式的购买，详情请访问[`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work)*

**版权所有 © 2020-2025 安迪·格鲁夫。保留所有权利。**
