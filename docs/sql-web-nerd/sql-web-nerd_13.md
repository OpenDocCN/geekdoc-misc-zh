| ![](img/elvis-grave-43.tcl) |
| --- |

## 限制

部分来自 SQL for Web Nerds by [Philip Greenspun](http://philip.greenspun.com/) |

* * *

![](img/graceland-paperweight-34.tcl) Oracle 中最痛苦的限制是 VARCHAR 的最大长度为 4000 字节。对于大多数 Web 应用程序来说，这足以容纳 97%的用户输入数据。剩下的 3%非常重要，以至于你可能无法使用 VARCHAR。

Oracle8 包括一个最大可达 4GB 的 Character Large Objects（CLOB）数据类型。

> ```
> create table foobar 
> ( mykey integer,
>   moby clob );
> 
> insert into foobar values ( 1, 'foo');
> 
> ```

我第一次使用 CLOBs 是为了将我的问答论坛软件（你在[photo.net](http://www.photo.net/photo/)看到的）移植到 Oracle 8。我将其用于 MESSAGE 列。在我的 Illustra 实现中，结果表中的 12000 行中只有 46 行的消息长度超过 4000 字节（Oracle 8 中的 VARCHAR 限制）。但这 46 条消息非常有趣，有时包含其他作品的引用材料。因此，如果用户希望，允许他们发布非常长的消息似乎是值得的。

小小的注意事项：

+   CLOBs 不像字符串那样工作。例如，你不能要求一个 CLOB 列的长度。你可以通过 PL/SQL 调用来解决这个问题，但这并不是很有趣。

+   LOBs 不允许在 GROUP BY、ORDER BY、SELECT DISTINCT、聚合和连接中使用

+   `alter table bboard modify message clob;`不起作用（即使表中没有行）。如果你想使用 CLOBs，显然必须在创建表时声明。

如果你认为这些限制很糟糕，那么你还没有遇到最大的限制：Oracle SQL 解析器只能处理长度不超过 4000 个字符的字符串字面量。SQL*Plus 的限制更严格。它只能处理长度不超过 2500 个字符的字符串。实际上，从大多数 Oracle 客户端，将无法向表中插入超过 4000 个字符长的数据。一个能够完美处理 4000 个字符字符串的语句/系统，将无法完全处理 4001 个字符长的字符串。你必须完全重新设计你的工作方式，以处理*可能*很长的字符串。

我的合作伙伴 Cotton 为我定制了一个 AOLserver 的 Oracle 8 驱动程序（我首选的 RDBMS 客户端）。所以他决定使用 C 绑定变量。结果发现，这些对于超过 4000 个字符的字符串也不起作用。如果你事先知道列是 CLOB，那么 C 语言中有一种特殊的 CLOB 类型可以使用。但当然，Cotton 的 C 代码只是从我的 AOLserver Tcl 代码中获取查询。在每次插入或选择之前没有查询数据库的情况下，他无法知道哪些列将是 CLOB。

Oracle 8 最被吹捧的功能之一是您可以对表进行分区，例如，说“每个具有 order_date 列小于 1997 年 1 月 1 日的行都放在表空间 A 中；每个具有 order_date 小于 1998 年 1 月 1 日的行都放在表空间 B 中；其余的都放在表空间 C 中。”假设这些表空间都在不同的磁盘驱动器上，这意味着当您对最近一个月或两个月的订单进行 GROUP BY 时，Oracle 不会筛选多年的数据；它只需要扫描位于表空间 C 中的表的分区。分区似乎是一个好主意，或者至少多年来一直在使用它的 Informix 客户似乎是这样认为的。但如果您是一个 CLOB 成就者，您将不会使用分区。

现在，我对 CLOBs 的看法是，它们使用起来非常不愉快，几乎不值得。Cotton 花了比他的驱动程序中的其他所有功能都更长的时间来使这个功能正常工作。Informix Universal Server 允许您拥有 32,000 个字符长的 VARCHARs，我现在正在渴望那个系统...

### 参考资料

+   Oracle 服务器参考，“限制”，[`www.oradoc.com/keyword/limits`](http://www.oradoc.com/keyword/limits)

下一步：调优

* * *

[philg@mit.edu](http://philip.greenspun.com/)

### 读者评论

> MySQL 和 MS SQL 都有更高的 VARCHAR 限制：分别为 1,048,543 和 8000。这是从 http://dev.mysql.com/tech-resources/crash-me.php?res_id=38 获取的信息
> 
> -- Victor F，2004 年 8 月 21 日
> 
> 几年前，我正在处理一个 Sybase SQL Server 数据库，用于存储转录医疗报告的文本。Sybase 的好人们警告我们不要使用 TEXT 类型的列（相当于 Oracle 的 CLOB），而是将文本*行*存储在 VARCHAR 列中。 （当时，Sybase 将 VARCHAR 列限制为 255 字节。）只要您没有任何超过 255 个字符的行，这种方法就很有效。唯一的问题是您必须将文本解析为行，然后进行无限次的插入。但与使用函数操作 TEXT 数据相比，这样做的工作量更小。
> 
> -- David Smith，2005 年 6 月 29 日
> 
> 在 Oracle 11g 中，length()现在可以与 NCLOBs 一起使用。遗憾的是，select distinct 仍然不行。
> 
> -- Janek Bogucki，2009 年 7 月 2 日

添加评论
