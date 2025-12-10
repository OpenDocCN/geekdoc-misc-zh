# 子查询

> 原文：[`howqueryengineswork.com/11-subqueries.html`](https://howqueryengineswork.com/11-subqueries.html)

子查询是嵌套在其他查询中的查询。它们出现在 SELECT 列表、FROM 子句和 WHERE 子句中。支持子查询需要正确解析它们并有效地规划它们。

## 子查询类型

### 标量子查询

标量子查询返回单个值，可以在任何标量表达式有效的地方出现：

```rs
SELECT id, name,
       (SELECT AVG(salary) FROM employees) AS avg_salary
FROM employees 
```

子查询 `(SELECT AVG(salary) FROM employees)` 返回一个适用于每一行的值。如果标量子查询返回多行，则是一个错误。

### 相关子查询

相关子查询引用外部查询的列：

```rs
SELECT id, name,
       (SELECT COUNT(*) FROM orders WHERE orders.customer_id = customers.id) AS order_count
FROM customers 
```

内部查询引用外部查询的 `customers.id`。这种相关性创建了一个依赖关系：概念上，内部查询对于外部查询的每一行运行一次。

### 非相关子查询

非相关子查询是自包含的：

```rs
SELECT * FROM orders
WHERE total > (SELECT AVG(total) FROM orders WHERE region = 'West') 
```

子查询不引用外部查询，因此它可以一次性评估并替换结果。

### EXISTS 和 IN 子查询

`EXISTS` 谓词测试子查询是否返回任何行：

```rs
SELECT id FROM customers
WHERE EXISTS (SELECT 1 FROM orders WHERE orders.customer_id = customers.id) 
```

这返回至少有一个订单的客户。

`IN` 谓词测试集合中的成员资格：

```rs
SELECT * FROM products
WHERE category_id IN (SELECT id FROM categories WHERE active = true) 
```

`NOT EXISTS` 和 `NOT IN` 都提供了否定形式。

## 子查询规划

### 非相关子查询

非相关标量子查询很简单：在规划期间（或在执行开始时）执行一次，并将结果作为文字值替换。

```rs
SELECT * FROM orders WHERE total > (SELECT AVG(total) FROM orders) 
```

变为：

```rs
SELECT * FROM orders WHERE total > 42500.00  -- after evaluating subquery 
```

### 相关子查询：简单方法

一种简单的实现方式是对于外部查询的每一行执行一次相关子查询。对于订单计数示例：

```rs
SELECT id, name,
       (SELECT COUNT(*) FROM orders WHERE orders.customer_id = customers.id) AS order_count
FROM customers 
```

如果 `customers` 有 100,000 行，我们将对 `orders` 运行 100,000 个单独的查询。这非常慢。

### 去相关：将子查询转换为连接

解决方案是去相关：将相关子查询重写为连接。上面的查询变为：

```rs
SELECT c.id, c.name, COALESCE(o.order_count, 0) AS order_count
FROM customers c
LEFT JOIN (
    SELECT customer_id, COUNT(*) AS order_count
    FROM orders
    GROUP BY customer_id
) o ON c.id = o.customer_id 
```

现在我们只需扫描一次 `orders`，进行聚合和连接，这要快得多。

### EXISTS 转半连接

一个 `EXISTS` 子查询变为半连接。半连接返回左边的行，其中至少存在一个与右边的匹配，当存在多个匹配时不会重复左边的行。

```rs
SELECT id FROM foo WHERE EXISTS (SELECT 1 FROM bar WHERE foo.id = bar.id) 
```

变为：

```rs
Projection: foo.id
    LeftSemi Join: foo.id = bar.id
        Scan: foo
        Scan: bar 
```

### NOT EXISTS 转反连接

`NOT EXISTS` 变为反连接，它返回左边没有在右边匹配的行：

```rs
SELECT id FROM foo WHERE NOT EXISTS (SELECT 1 FROM bar WHERE foo.id = bar.id) 
```

变为：

```rs
Projection: foo.id
    LeftAnti Join: foo.id = bar.id
        Scan: foo
        Scan: bar 
```

### IN 转半连接

`IN` 子查询也变为半连接：

```rs
SELECT * FROM products WHERE category_id IN (SELECT id FROM categories WHERE active = true) 
```

变为：

```rs
LeftSemi Join: products.category_id = categories.id
    Scan: products
    Filter: active = true
        Scan: categories 
```

## 实现复杂性

子查询去相关是查询引擎中较为复杂的一部分。挑战包括：

识别相关性：规划器必须确定子查询中哪些列引用了外部查询。

选择正确的连接类型：EXISTS 映射到半连接，NOT EXISTS 映射到反连接，标量子查询映射到带有聚合的左外连接。

处理多个相关性：子查询可能在一个复杂查询中引用多个外部表。

保留语义：重写的查询必须产生完全相同的结果，包括对 NULL 的处理。

嵌套子查询：子查询可以包含子查询，需要递归去相关。

KQuery 目前未实现子查询。生产查询引擎在子查询支持上投入了大量努力，因为这对于 SQL 兼容性至关重要。

## 当去相关不可行时

一些相关子查询不能去相关为标准连接。这些“横向”或“依赖”子查询必须逐行评估。现代数据库支持`LATERAL`连接来处理这种情况：

```rs
SELECT c.*, recent_orders.*
FROM customers c,
LATERAL (SELECT * FROM orders WHERE customer_id = c.id ORDER BY date DESC LIMIT 3) recent_orders 
```

这返回每个客户及其最近的三张订单。`LIMIT 3`取决于我们正在处理的客户，因此不能简单地重写为连接。

处理横向连接需要逐行评估（慢）或结合连接与限制的特殊操作符。

*本书也以 ePub、MOBI 和 PDF 格式可供购买，详情请访问[`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work)*

**版权 © 2020-2025 安迪·格鲁夫。版权所有。**
