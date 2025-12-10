# SQL 支持

> 原文：[`howqueryengineswork.com/07-sql-support.html`](https://howqueryengineswork.com/07-sql-support.html)

*本章讨论的源代码可以在 [KQuery 项目](https://github.com/andygrove/how-query-engines-work) 的 `sql` 模块中找到。*

上一章展示了如何使用 DataFrame API 构建查询。但大多数用户期望编写 SQL。本章涵盖了将 SQL 文本解析为逻辑计划的过程，这涉及两个步骤：解析（文本到语法树）和计划（语法树到逻辑计划）。

## 从 SQL 到逻辑计划的旅程

考虑这个查询：

```rs
SELECT id, first_name, salary * 1.1 AS new_salary
FROM employee
WHERE state = 'CO' 
```

要执行此操作，我们需要：

1.  分词：将文本分解为标记（关键字、标识符、文字、运算符）

1.  解析：构建表示查询结构的语法树

1.  计划：将语法树转换为逻辑计划

结果是与 DataFrame API 构建的同逻辑计划相同，但由 SQL 文本而不是代码构建。

## 分词

分词器（或词法分析器）将字符串转换为一系列标记。每个标记都有一个类型和一个值。

```rs
data class Token(val text: String, val type: TokenType, val endOffset: Int) 
```

标记类型包括：

+   关键字：`SELECT`、`FROM`、`WHERE`、`AND`、`OR` 等。

+   标识符：表名、列名

+   文字：字符串（`'hello'`）、数字（`42`、`3.14`）

+   符号：运算符和标点符号（`+`、`-`、`*`、`/`、`=`、`<`、`>`、`(`、`)`、`,`）

对于查询 `SELECT a + b FROM c`，分词产生：

```rs
listOf(
    Token("SELECT", Keyword.SELECT, ...),
    Token("a", Literal.IDENTIFIER, ...),
    Token("+", Symbol.PLUS, ...),
    Token("b", Literal.IDENTIFIER, ...),
    Token("FROM", Keyword.FROM, ...),
    Token("c", Literal.IDENTIFIER, ...)
) 
```

分词器处理诸如识别 `SELECT` 是一个关键字但 `employee` 是一个标识符、解析带有引号的字符串文字以及识别多字符运算符（如 `<=` 和 `!=`）等细节。

## 使用 Pratt 解析器进行解析

解析将标记转换为树结构。挑战在于正确处理运算符优先级。在 `1 + 2 * 3` 中，乘法的优先级高于加法，因此结果应该是 `1 + (2 * 3)`，而不是 `(1 + 2) * 3`。

KQuery 使用基于 Vaughan Pratt 1973 年论文“自顶向下运算符优先级”的 Pratt 解析器。Pratt 解析器优雅地处理优先级，并产生清晰、可调试的代码。

核心算法非常简单：

```rs
interface PrattParser {

    fun parse(precedence: Int = 0): SqlExpr? {
        var expr = parsePrefix() ?: return null
        while (precedence < nextPrecedence()) {
            expr = parseInfix(expr, nextPrecedence())
        }
        return expr
    }

    fun nextPrecedence(): Int
    fun parsePrefix(): SqlExpr?
    fun parseInfix(left: SqlExpr, precedence: Int): SqlExpr
} 
```

算法：

1.  解析“前缀”表达式（文字、标识符或一元运算符）

1.  当下一个运算符的优先级高于我们开始时的优先级时，将解析为具有当前表达式作为左侧的“中缀”表达式（二元运算符）

1.  当遇到优先级较低的运算符时返回

魔法在于 `parseInfix`，它递归地调用 `parse` 并带有新运算符的优先级。这自然地将优先级较高的操作分组在一起。

## SQL 表达式

解析器使用 SQL 表达式类型构建语法树：

```rs
interface SqlExpr

data class SqlIdentifier(val id: String) : SqlExpr
data class SqlString(val value: String) : SqlExpr
data class SqlLong(val value: Long) : SqlExpr
data class SqlDouble(val value: Double) : SqlExpr
data class SqlBinaryExpr(val l: SqlExpr, val op: String, val r: SqlExpr) : SqlExpr
data class SqlAlias(val expr: SqlExpr, val alias: SqlIdentifier) : SqlExpr
data class SqlFunction(val name: String, val args: List<SqlExpr>) : SqlExpr 
```

这些与逻辑表达式相似，但更接近 SQL 语法。我们使用通用的 `SqlBinaryExpr` 和字符串运算符，而不是为每个运算符创建单独的类，因为区别在逻辑计划中更为重要。

## 运算符优先级示例

考虑解析 `1 + 2 * 3`：

```rs
Tokens:      [1]  [+]  [2]  [*]  [3]
Precedence:   0   50    0   60    0 
```

加法优先级为 50，乘法优先级为 60。遍历：

1.  解析前缀：`SqlLong(1)`

1.  下一个标记 `+` 的优先级 50 > 0，因此解析中缀

1.  在 `parseInfix` 中，消费 `+`，然后递归调用 `parse(50)`

1.  解析前缀：`SqlLong(2)`

1.  下一个标记 `*` 的优先级 60 > 50，因此解析中缀

1.  消费 `*`，递归调用 `parse(60)`

1.  解析前缀：`SqlLong(3)`

1.  没有更多标记，返回 `SqlLong(3)`

1.  返回 `SqlBinaryExpr(SqlLong(2), "*", SqlLong(3))`

1.  下一个优先级是 0 < 50，因此返回

1.  返回 `SqlBinaryExpr(SqlLong(1), "+", SqlBinaryExpr(...))`

结果：`1 + (2 * 3)`，如预期。

与 `1 * 2 + 3` 进行比较：

```rs
Tokens:      [1]  [*]  [2]  [+]  [3]
Precedence:   0   60    0   50    0 
```

1.  解析前缀：`SqlLong(1)`

1.  `*` 的优先级 60 > 0，解析中缀

1.  消费 `*`，调用 `parse(60)`

1.  解析前缀：`SqlLong(2)`

1.  `+` 的优先级 50 < 60，因此返回 `SqlLong(2)`

1.  返回 `SqlBinaryExpr(SqlLong(1), "*", SqlLong(2))`

1.  `+` 的优先级 50 > 0，解析中缀

1.  消费 `+`，调用 `parse(50)`

1.  解析前缀：`SqlLong(3)`

1.  没有更多标记，返回

1.  返回 `SqlBinaryExpr(SqlBinaryExpr(...), "+", SqlLong(3))`

结果：`(1 * 2) + 3`，再次正确。

## 解析 SELECT 语句

除此之外，我们还需要解析完整的 SQL 语句。一个 SELECT 语句具有以下结构：

```rs
data class SqlSelect(
    val projection: List<SqlExpr>,
    val tableName: String,
    val selection: SqlExpr?,
    val groupBy: List<SqlExpr>,
    val having: SqlExpr?,
    val orderBy: List<SqlSort>,
    val limit: Int?
) : SqlRelation 
```

解析 SELECT 语句是直接的程序性代码：期望 `SELECT`，解析逗号分隔的表达式列表，期望 `FROM`，解析表名，可选地解析 `WHERE` 和其表达式，等等。

## SQL 计划：困难的部分

解析是机械的。规划是事情变得有趣的地方。

考虑这个查询：

```rs
SELECT id, first_name, salary/12 AS monthly_salary
FROM employee
WHERE state = 'CO' AND monthly_salary > 1000 
```

WHERE 子句引用了 `state`（表中的列）和 `monthly_salary`（在 SELECT 列表中定义的别名）。这对人类来说是自然的，但会创建一个问题：过滤器需要存在于计划不同点的列。

如果我们在投影之前过滤，`monthly_salary` 还不存在。如果我们在投影之后过滤，`state` 可能不再可用。

### 解决方案：中间投影

一种方法是在中间投影中添加列：

```rs
Projection: #id, #first_name, #monthly_salary
    Filter: #state = 'CO' AND #monthly_salary > 1000
        Projection: #id, #first_name, #salary/12 AS monthly_salary, #state
            Scan: employee 
```

内部投影计算所有需要的列，包括 `state`。然后过滤器可以引用所有内容。外部投影从最终输出中删除 `state`。

### 翻译逻辑

计划器遍历 SQL 表达式树并构建逻辑表达式：

```rs
fun createLogicalExpr(expr: SqlExpr, input: LogicalPlan): LogicalExpr {
    return when (expr) {
        is SqlIdentifier -> Column(expr.id)
        is SqlString -> LiteralString(expr.value)
        is SqlLong -> LiteralLong(expr.value)
        is SqlDouble -> LiteralDouble(expr.value)
        is SqlAlias -> Alias(createLogicalExpr(expr.expr, input), expr.alias.id)
        is SqlBinaryExpr -> {
            val l = createLogicalExpr(expr.l, input)
            val r = createLogicalExpr(expr.r, input)
            when (expr.op) {
                "=" -> Eq(l, r)
                "!=" -> Neq(l, r)
                ">" -> Gt(l, r)
                ">=" -> GtEq(l, r)
                "<" -> Lt(l, r)
                "<=" -> LtEq(l, r)
                "AND" -> And(l, r)
                "OR" -> Or(l, r)
                "+" -> Add(l, r)
                "-" -> Subtract(l, r)
                "*" -> Multiply(l, r)
                "/" -> Divide(l, r)
                else -> throw SQLException("Unknown operator: ${expr.op}")
            }
        }
        else -> throw SQLException("Unsupported expression: $expr")
    }
} 
```

### 查找列引用

为了确定过滤器需要哪些列，我们遍历表达式树：

```rs
fun findColumnReferences(expr: LogicalExpr, columns: MutableSet<String>) {
    when (expr) {
        is Column -> columns.add(expr.name)
        is Alias -> findColumnReferences(expr.expr, columns)
        is BinaryExpr -> {
            findColumnReferences(expr.l, columns)
            findColumnReferences(expr.r, columns)
        }
    }
} 
```

因此，计划器可以将过滤器中的列与投影中的列进行比较，并将任何缺失的列添加到中间投影中。

## 聚合查询

聚合查询增加了更多复杂性。考虑：

```rs
SELECT department, AVG(salary) AS avg_salary
FROM employee
WHERE state = 'CO'
GROUP BY department
HAVING avg_salary > 50000 
```

计划器必须：

1.  识别聚合函数（`AVG`）

1.  将分组表达式（`department`）与聚合分开

1.  处理 HAVING，它在聚合之后过滤

1.  确保在 SELECT 中列要么在 GROUP BY 中，要么在聚合内部

完整实现处理这些情况，但代码较为复杂。请参阅源代码库以获取详细信息。

## 为什么构建自己的解析器？

你可能会想知道为什么我们构建解析器而不是使用像 ANTLR 这样的解析器生成器或像 Apache Calcite 这样的库。

构建手写解析器的优点：

+   控制：你决定支持哪些 SQL 特性

+   错误信息：你可以生成清晰、上下文相关的错误

+   简单性：无需外部依赖或生成代码

+   学习：理解解析加深了你对该整个系统的理解

对于一个生产系统，使用现有的 SQL 解析器通常是明智的。但为了了解查询引擎的工作原理，构建解析器揭示了 SQL 的表面灵活性如何映射到结构化操作。

*本书也以 ePub、MOBI 和 PDF 格式在[`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work)上提供购买。*

**版权 © 2020-2025 安迪·格鲁夫。版权所有。**
