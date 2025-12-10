# 什么是查询引擎？

> 原文：[`howqueryengineswork.com/01-what-is-a-query-engine.html`](https://howqueryengineswork.com/01-what-is-a-query-engine.html)

如果你已经编写了代码来遍历列表或过滤数组中的项目，你实际上已经实现了一个微型查询引擎。查询引擎简单来说就是根据某些标准检索和处理数据的软件。你的`for`循环和实际查询引擎之间的区别在于规模、通用性和优化，但核心思想是相同的。

考虑以下 Python 代码，它查找所有 GPA 高于 3.5 的学生：

```rs
high_achievers = []
for student in students:
    if student.gpa > 3.5:
        high_achievers.append(student) 
```

这是在查询数据。现在想象你需要跨数百万条存储在文件中的记录执行此操作，从多个来源连接数据，分组结果，并计算聚合，同时保持合理的响应时间。这正是查询引擎所做的事情。

## 从代码到查询

上述代码是有效的，但它有限制。如果你想要更改过滤条件怎么办？你需要修改和重新编译代码。如果有人没有编程经验需要分析数据怎么办？

查询语言如 SQL 通过提供一种声明式的方式来表达你想要的数据，而不需要指定如何获取它：

```rs
SELECT name, gpa
FROM students
WHERE gpa > 3.5; 
```

这个查询表达了我们 Python 循环中的相同逻辑，但查询引擎决定如何高效地执行它。这种“是什么”与“如何做”的分离非常强大。相同的查询可以运行在小型文件或分布式服务器集群上。

## 查询引擎的解剖结构

查询引擎通过几个阶段将查询（如上面的 SQL）转换为实际结果：

1.  解析：将查询文本转换为结构化表示（如抽象语法树）

1.  规划：确定需要的操作（扫描、过滤、连接、聚合）

1.  优化：重新排序和转换操作以提高效率

1.  执行：实际上处理数据并产生结果

这个管道可能会让你想起编译器，这并非巧合。查询引擎本质上是一种专门的编译器，它将声明式查询转换为高效的执行计划。

## 一个具体的例子

让我们看看一个稍微复杂一点的查询：

```rs
SELECT department, AVG(salary)
FROM employees
WHERE hire_date > '2020-01-01'
GROUP BY department
ORDER BY AVG(salary) DESC; 
```

这个查询：

+   扫描`employees`表

+   只过滤最近雇佣的员工

+   按部门分组员工

+   计算每个部门的平均工资

+   按平均工资排序结果

查询引擎必须确定执行这些操作的最有效方式。应该在分组之前还是之后进行过滤？应该如何存储中间结果？这些决策对性能有重大影响，尤其是在大数据集上。

## SQL：通用的查询语言

SQL（结构化查询语言）自 20 世纪 70 年代以来一直是主导的查询语言。你将在以下场景中遇到它：

+   关系型数据库（PostgreSQL、MySQL、SQLite）

+   数据仓库（Snowflake、BigQuery、Redshift）

+   大数据系统（Apache Spark、Presto、Hive）

+   即使是嵌入式分析（DuckDB）

这里还有两个示例展示了 SQL 的表达能力：

找到昨天访问量最高的前 5 个页面：

```rs
SELECT page_url, COUNT(*) AS visits
FROM page_views
WHERE view_date = CURRENT_DATE - 1
GROUP BY page_url
ORDER BY visits DESC
LIMIT 5; 
```

计算月度增长：

```rs
SELECT month, revenue,
       revenue - LAG(revenue) OVER (ORDER BY month) AS growth
FROM monthly_sales
WHERE year = 2024; 
```

## 超越 SQL：DataFrame API

虽然 SQL 应用广泛，但许多查询引擎也提供了程序化 API。这些 API 在数据科学中特别受欢迎，因为查询通常动态构建或与自定义代码混合使用。

这里是使用 Apache Spark 的 DataFrame API 在 Scala 中表达相同查询的示例：

```rs
val spark = SparkSession.builder
  .appName("Example")
  .master("local[*]")
  .getOrCreate()

val result = spark.read.parquet("/data/employees")
  .filter($"hire_date" > "2020-01-01")
  .groupBy("department")
  .agg(avg("salary").as("avg_salary"))
  .orderBy(desc("avg_salary"))

result.show() 
```

DataFrame API 提供了与 SQL 相同的逻辑操作，但以方法调用的形式表达。在底层，这两种方法生成相同的查询计划。

## 为什么构建查询引擎？

理解查询引擎有助于你：

+   编写更好的查询，因为了解查询的执行方式有助于你编写高效的查询

+   调试性能问题，因为理解优化器有助于诊断慢查询

+   欣赏数据库内部结构，因为查询引擎是每个数据库的核心

+   构建数据工具，因为许多应用程序需要类似查询的功能

查询引擎还涉及计算机科学的许多领域：解析器和编译器、数据结构、算法、分布式系统和优化。构建一个查询引擎是极佳的实践。

## 本书涵盖的内容

本书从零开始构建完整的查询引擎。我们将实现：

+   用于表示数据的类型系统

+   用于读取文件的源数据连接器

+   逻辑和物理查询计划

+   SQL 解析器和规划器

+   查询优化规则

+   并行和分布式执行

查询引擎（称为 KQuery）故意设计得简单，优化用于学习而非生产使用。但这些概念直接适用于像 Apache Spark、Presto 和 DataFusion 这样的真实系统。

*本书也以 ePub、MOBI 和 PDF 格式在 [`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work) 上提供购买。*

**版权所有 © 2020-2025 安迪·格鲁夫。保留所有权利。**
