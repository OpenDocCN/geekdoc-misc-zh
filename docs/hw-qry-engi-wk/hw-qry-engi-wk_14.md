# 连接

> 原文：[`howqueryengineswork.com/10-joins.html`](https://howqueryengineswork.com/10-joins.html)

*本章讨论的源代码可以在[KQuery 项目](https://github.com/andygrove/how-query-engines-work)的`logical-plan`和`physical-plan`模块中找到。*

连接基于条件组合两个表的行。它们是关系数据库的基本操作，通常是查询中最昂贵的操作。本章涵盖了连接类型和算法，重点关注哈希连接。

## 连接类型

### 内连接

内连接返回两个表中连接条件匹配的行：

```rs
SELECT e.name, d.dept_name
FROM employees e
INNER JOIN departments d ON e.dept_id = d.id 
```

如果员工没有匹配的部门，该员工将不包括在结果中。如果部门没有员工，它也将被排除。

### 左外连接

左外连接返回左表的所有行，如果有的话，与右表匹配的行：

```rs
SELECT e.name, d.dept_name
FROM employees e
LEFT JOIN departments d ON e.dept_id = d.id 
```

没有匹配部门的员工仍然出现在结果中，`dept_name`为 NULL。

### 右外连接

右外连接是左连接的镜像：所有来自右表的行，与左表匹配：

```rs
SELECT e.name, d.dept_name
FROM employees e
RIGHT JOIN departments d ON e.dept_id = d.id 
```

没有员工的部门在员工列中显示为 NULL。

### 全外连接

全外连接返回两个表的所有行，在可能的情况下进行匹配：

```rs
SELECT e.name, d.dept_name
FROM employees e
FULL OUTER JOIN departments d ON e.dept_id = d.id 
```

未匹配的员工和未匹配的部门都出现，缺失的列用 NULL 表示。

### 交叉连接

交叉连接返回两个表的所有行的组合（笛卡尔积）：

```rs
SELECT e.name, d.dept_name
FROM employees e
CROSS JOIN departments d 
```

如果员工表有 100 行，部门表有 10 行，结果将有 1,000 行。交叉连接本身很少单独使用，但有时会出现在查询计划中的中间步骤。

### 半连接

半连接返回左表中至少有一个匹配右表行的行，但不包括右表中的列：

```rs
SELECT e.name
FROM employees e
WHERE EXISTS (SELECT 1 FROM departments d WHERE d.id = e.dept_id) 
```

半连接不能直接用标准 SQL 语法表示，但由 EXISTS 子查询引起。子查询章节详细介绍了这一点。

### 反连接

反连接返回左表中不存在右表匹配的行：

```rs
SELECT e.name
FROM employees e
WHERE NOT EXISTS (SELECT 1 FROM departments d WHERE d.id = e.dept_id) 
```

反连接由 NOT EXISTS 或 NOT IN 子查询引起。

## 连接条件

### 等值连接

大多数连接使用相等条件：

```rs
ON employees.dept_id = departments.id 
```

这些被称为等值连接。查询引擎对等值连接进行了大量优化，因为基于哈希的算法与相等比较工作得很好。

### 非等值连接

一些连接使用不等式或范围条件：

```rs
SELECT *
FROM events e
JOIN time_ranges t ON e.timestamp BETWEEN t.start_time AND t.end_time 
```

非等值连接不能使用基于哈希的算法，通常需要嵌套循环或专门的区间连接实现。

## 连接算法

连接算法的选择极大地影响了性能。三种主要方法为嵌套循环连接、排序合并连接和哈希连接。

### 嵌套循环连接

最简单的算法：对于左表中的每一行，扫描整个右表以查找匹配项。

```rs
for each row L in left_table:
    for each row R in right_table:
        if matches(L, R):
            emit(L, R) 
```

时间复杂度：O(n × m)，其中 n 和 m 是表的大小。

嵌套循环连接对于大型表简单但慢。它在以下情况下很有用：

+   一个表非常小

+   内表连接列上存在索引

+   连接条件不是相等（非等值连接）

使用索引，内循环变为索引查找而不是全表扫描，从而显著提高性能。

### 排序-合并连接

按连接键对两个表进行排序，然后合并它们：

```rs
sort left_table by join_key
sort right_table by join_key

while both tables have rows:
    if left.key == right.key:
        emit all matching combinations
        advance both
    else if left.key < right.key:
        advance left
    else:
        advance right 
```

时间复杂度：排序为 O(n log n + m log m)，合并为 O(n + m)。

当以下条件成立时，排序-合并连接是高效的：

+   数据已经按连接键排序

+   连接的结果无论如何都需要排序

+   内存有限（外部排序可以溢出到磁盘）

### 哈希连接

从一个表构建哈希表，然后用另一个表探测它：

```rs
// Build phase
hash_table = {}
for each row R in build_table:
    key = R.join_column
    hash_table[key].append(R)

// Probe phase
for each row L in probe_table:
    key = L.join_column
    for each match in hash_table[key]:
        emit(L, match) 
```

时间复杂度：O(n + m)，假设有良好的哈希分布。

当以下条件成立时，哈希连接通常是等值连接最快的算法：

+   较小的表可以放入内存

+   连接条件使用相等性

## 哈希连接详细

哈希连接是现代查询引擎的工作马。让我们更仔细地研究它。

### 选择构建方

构建方应该是较小的表。从 1,000 行构建哈希表并用 1,000,000 行探测要快得多。

查询优化器估计表大小并选择构建方。使用统计信息，它可以考虑到减少表大小的过滤器：

```rs
SELECT *
FROM large_table l
JOIN small_table s ON l.id = s.id
WHERE s.category = 'active' 
```

即使`small_table`的行数多于`large_table`，过滤后可能更小。

### 哈希表结构

对于每个唯一的连接键，哈希表存储构建方具有该键的所有行。最简单的结构是从键到行列表的哈希映射：

```rs
val hashTable = HashMap<Any, MutableList<RecordBatch>>() 
```

实际上，实现会优化内存布局以提高缓存效率。

### 处理哈希冲突

当不同的键哈希到同一个桶时，我们必须在探测阶段比较实际键值：

```rs
fun probe(key: Any): List<Row> {
    val bucket = hashTable[key.hashCode()]
    return bucket.filter { it.joinKey == key }
} 
```

良好的哈希函数最小化冲突，但探测必须始终验证相等性。

### KQuery 的哈希连接实现

KQuery 在`HashJoinExec`中实现了哈希连接。该实现支持内连接、左连接和右连接：

```rs
class HashJoinExec(
    val left: PhysicalPlan,
    val right: PhysicalPlan,
    val joinType: JoinType,
    val leftKeys: List<Int>,
    val rightKeys: List<Int>,
    val schema: Schema,
    val rightColumnsToExclude: Set<Int>
) : PhysicalPlan {

    override fun execute(): Sequence<RecordBatch> {
        // Build phase: load all right-side rows into a hash table
        val hashTable = HashMap<List<Any?>, MutableList<List<Any?>>>()

        right.execute().forEach { batch ->
            for (rowIndex in 0 until batch.rowCount()) {
                val key = rightKeys.map { keyIndex ->
                    normalizeValue(batch.field(keyIndex).getValue(rowIndex))
                }
                val row = (0 until batch.columnCount()).map {
                    batch.field(it).getValue(rowIndex)
                }
                hashTable.getOrPut(key) { mutableListOf() }.add(row)
            }
        }

        // Probe phase: iterate through left side and find matches
        return sequence {
            left.execute().forEach { leftBatch ->
                val outputRows = mutableListOf<List<Any?>>()

                for (leftRowIndex in 0 until leftBatch.rowCount()) {
                    val probeKey = leftKeys.map { keyIndex ->
                        normalizeValue(leftBatch.field(keyIndex).getValue(leftRowIndex))
                    }
                    val leftRow = (0 until leftBatch.columnCount()).map {
                        leftBatch.field(it).getValue(leftRowIndex)
                    }
                    val matchedRows = hashTable[probeKey]

                    when (joinType) {
                        JoinType.Inner -> {
                            if (matchedRows != null) {
                                for (rightRow in matchedRows) {
                                    outputRows.add(combineRows(leftRow, rightRow))
                                }
                            }
                        }
                        JoinType.Left -> {
                            if (matchedRows != null) {
                                for (rightRow in matchedRows) {
                                    outputRows.add(combineRows(leftRow, rightRow))
                                }
                            } else {
                                // No match: include left row with nulls for right columns
                                val nullRightRow = List(rightSchema.fields.size) { null }
                                outputRows.add(combineRows(leftRow, nullRightRow))
                            }
                        }
                        // Right join handled after probe phase...
                    }
                }

                if (outputRows.isNotEmpty()) {
                    yield(createBatch(outputRows))
                }
            }
        }
    }
} 
```

该实现的关键方面：

构建阶段将整个右表加载到以连接列为键的哈希表中。每个键映射到一个行列表（以处理重复键）。

探测阶段遍历左表，在哈希表中查找每行的键。对于内连接，跳过没有匹配的行。对于左连接，未匹配的行会输出，右列使用 NULL。

`rightColumnsToExclude`参数处理了连接键在两侧具有相同名称的常见情况。如果没有这个参数，输出将会有重复的列。

### 外连接

KQuery 的实现处理左外连接和右外连接：

对于左外连接，当探测行在哈希表中没有匹配时，我们输出左行，所有右列使用 NULL。这发生在探测阶段内联。

对于右外连接，我们需要跟踪哪些构建（右）行被匹配。在探测阶段完成后，我们输出未匹配的右行，对于左列使用 NULL。这需要第二次遍历或在探测期间跟踪匹配的键。

全外连接结合了两种方法：在探测期间输出未匹配的左行，然后输出未匹配的右行。

### 内存考虑事项

对于简单的哈希连接，构建侧必须适合内存。对于大型表，查询引擎使用诸如：

优雅的哈希连接：通过哈希值对两个表进行分区，然后连接匹配的分区。每个分区更小，更有可能适合内存。

混合哈希连接：尽可能将构建侧保留在内存中，将剩余部分溢出到磁盘，然后单独处理溢出分区。

自适应执行：从哈希连接开始，如果检测到内存压力，则切换到排序合并。

## 连接顺序

对于连接多个表的查询，顺序至关重要：

```rs
SELECT *
FROM orders o
JOIN customers c ON o.customer_id = c.id
JOIN products p ON o.product_id = p.id 
```

这可能执行如下：

+   (orders JOIN customers) JOIN products

+   (orders JOIN products) JOIN customers

+   (customers JOIN products) JOIN orders（通常不好）

优化器评估成本并选择最佳顺序。通常，产生较小中间结果的连接应该首先发生。

## 布隆过滤器

布隆过滤器是一种概率数据结构，可以快速测试一个元素是否可能在集合中。查询引擎使用布隆过滤器来加速连接：

1.  从构建侧键构建布隆过滤器

1.  在探测之前，检查探测键是否可能存在

1.  跳过肯定没有匹配的行

布隆过滤器有误报（可能会说“是”，而答案是“否”）但没有误报。这意味着会发生一些不必要的探测，但不会错过任何匹配。

对于选择性连接，其中大多数探测行没有匹配，布隆过滤器可以显著减少工作量。

## 总结

连接复杂且性能关键。要点：

+   哈希连接对于等值连接通常是速度最快的

+   构建侧应该是较小的表

+   连接顺序对性能影响巨大

+   内存限制可能需要将数据溢出到磁盘

+   查询优化器使用统计数据来做出明智的选择

KQuery 实现了内连接、左连接和右连接的哈希连接。该实现展示了核心算法：从一边构建哈希表，用另一边进行探测。生产系统添加了诸如溢出到磁盘和布隆过滤器之类的优化，但基本方法保持不变。

*这本书也以 ePub、MOBI 和 PDF 格式从[`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work)提供购买*

**版权 © 2020-2025 安迪·格鲁夫。保留所有权利。**
