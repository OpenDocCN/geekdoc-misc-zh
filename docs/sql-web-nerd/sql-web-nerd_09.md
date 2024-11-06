| ![Tal. French Roast, 6th Avenue and 11th, Manhattan 1995.](img/tal-midriff-22.tcl) |
| --- |

## 样式

SQL for Web Nerds 的一部分，作者是 [Philip Greenspun](http://philip.greenspun.com/) |

* * *

这是一个熟悉的简单示例，来自复杂查询章节：

> ```
>  select user_id, count(*) as how_many from bboard where not exists (select 1 from bboard_authorized_maintainers bam where bam.user_id = bboard.user_id) and posting_time + 60 > sysdate group by user_id order by how_many desc; 
> ```

看起来并不简单，对吧？如果我们重新写一下呢：

> ```
>  select user_id, count(*) as how_many from bboard where not exists (select 1 from bboard_authorized_maintainers bam where bam.user_id = bboard.user_id) and posting_time + 60 > sysdate group by user_id order by how_many desc; 
> ```

如果您的代码没有正确缩进，那么您将永远无法调试它。我们如何证明使用“正确”这个词呢？毕竟，SQL 解析器不考虑额外的空格或换行符。

> **当软件结构被揭示时，软件的缩进应该是正确的 *并且* 缩进风格应该对程序员社区来说是熟悉的。**

### 所有查询的规则

如果它适合一行，可以保留在一行上：

> ```
>  select email from users where user_id = 34; 
> ```

如果它不能很好地放在一行上，给每个子句单独一行：

> ```
>  select * from news where sysdate > expiration_date and approved_p = 't' order by release_date desc, creation_date desc 
> ```

如果特定子句的内容无法放在一行上，请在打开子句的关键字后立即换行。然后将项目缩进。这是 ArsDigita Community System 的静态 .html 页面管理部分的一个示例。我们正在查询 `static_pages` 表，其中保存了 Unix 文件系统中任何 .html 文件的副本：

> ```
>  select to_char(count(*),'999G999G999G999G999') as n_pages, to_char(sum(dbms_lob.getlength(page_body)),'999G999G999G999G999') as n_bytes from static_pages; 
> ```

在这个查询中，选择列表中有两个项目，所有行的计数和`page_body`列中字节的总和（类型为 CLOB，因此需要使用 `dbms_lob.getlength` 而不是简单的 `length`）。我们希望 Oracle 使用每三位数字之间的分隔符格式化这些数字。为此，我们必须使用 `to_char` 函数和掩码 `'999G999G999G999G999'`（"G" 告诉 Oracle 根据安装的国家使用适当的字符，例如，在美国使用逗号，在欧洲使用句号）。然后我们必须给结果关联名称，以便它们易于用作 Tcl 变量。在完成所有这些之后，将两个项目放在同一行会令人困惑。

这里有另一个示例，这次来自 ArsDigita Community System 的顶级评论管理页面。我们将得到一行，其中包含每种用户提交的评论的计数：

> ```
>  select count(*) as n_total, sum(decode(comment_type,'alternative_perspective',1,0)) as n_alternative_perspectives, sum(decode(comment_type,'rating',1,0)) as n_ratings, sum(decode(comment_type,'unanswered_question',1,0)) as n_unanswered_questions, sum(decode(comment_type,'private_message_to_page_authors',1,0)) as n_private_messages from comments 
> ```

注意使用 `sum(decode` 来计算每种评论类型的数量。这给我们提供了类似于 GROUP BY 的信息，但我们同时也得到了总数以及类别总数。此外，数字会以我们选择的列名显示。当然，这种查询只在您事先知道 `comment_type` 的可能值时才有效。

+   [DECODE 的 Oracle 文档](http://www.oradoc.com/keyword/decode)

+   有关数字格式化技巧的解释，请参阅 Oracle8 Server SQL 参考 [格式转换部分](http://www.oradoc.com/keyword/format_models)

### GROUP BY 查询的规则

当你使用 GROUP BY 时，在 select 列表中先放置确定组标识的列。然后放置计算该组函数的聚合列：

> ```
>  select links.user_id, first_names, last_name, count(links.page_id) as n_links from links, users where links.user_id = users.user_id group by links.user_id, first_names, last_name order by n_links desc 
> ```

下一步：过程化

* * *

[philg@mit.edu](http://philip.greenspun.com/)

### 读者评论

> 在上面的示例中，where 子句分为两行，尽管文本建议一行：
> 
> "如果一行放不下，给每个从句单独一行：
> 
> select *
> 
> 来自 news
> 
> where sysdate > expiration_date
> 
> 并且 approved_p = 't'
> 
> 按 release_date desc, creation_date desc 排序"
> 
> 在这种情况下，当然一行更好。
> 
> -- Peter Tury，2002 年 6 月 12 日

添加评论 | 添加链接
