# KQuery 项目

> 原文：[`howqueryengineswork.com/00-source-code.html`](https://howqueryengineswork.com/00-source-code.html)

本书附有一个名为 KQuery（代表 Kotlin 查询）的完整功能的查询引擎。源代码可在 GitHub 上找到：

```rs
https://github.com/andygrove/how-query-engines-work 
```

每一章都引用了此仓库中的特定模块。边读代码边读书将加深你的理解。书中解释了设计决策，而代码展示了完整的实现。

## 为什么选择 Kotlin？

示例使用 Kotlin，因为它简洁易读。如果你知道 Java、Python 或任何 C 系列语言，你将很容易跟上。Kotlin 运行在 JVM 上，与 Apache Arrow 等 Java 库无缝交互。

查询引擎的概念是语言无关的。Apache Arrow DataFusion 项目在 Rust 中实现了类似的想法，你可以在任何语言中应用这些模式。

## 仓库结构

仓库组织成 Gradle 模块，每个模块对应查询引擎的一层：

| 模块 | 描述 |
| --- | --- |
| `datatypes` | 建立在 Apache Arrow 之上的类型系统 |
| `datasource` | 数据源抽象和 CSV/Parquet 读取器 |
| `logical-plan` | 逻辑计划和表达式 |
| `physical-plan` | 物理计划和表达式评估 |
| `query-planner` | 从逻辑计划到物理计划的转换 |
| `optimizer` | 查询优化规则 |
| `sql` | SQL 分词器、解析器和规划器 |
| `execution` | 查询执行引擎 |
| `examples` | 示例查询和基准测试 |

## 构建项目

先决条件：

+   JDK 11 或更高版本

+   Gradle（或使用包含的 Gradle 包装器）

构建和运行测试：

```rs
cd jvm
./gradlew build 
```

要运行特定的测试：

```rs
./gradlew :sql:test --tests "SqlParserTest" 
```

## 运行示例

`examples`模块包含你可以运行的示例查询：

```rs
./gradlew :examples:run 
```

请参阅仓库中的 README 以获取最新说明和任何其他所需设置。

*本书也以 ePub、MOBI 和 PDF 格式提供购买，请访问[`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work)*

**版权所有 © 2020-2025 安迪·格鲁夫。保留所有权利。**
