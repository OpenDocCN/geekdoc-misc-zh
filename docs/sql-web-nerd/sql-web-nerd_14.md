| ![](img/graceland-piano-32.tcl) |
| --- |

## 索引和调优

SQL for Web Nerds 的一部分，作者是 [Philip Greenspun](http://philip.greenspun.com/) |

* * *

![夜晚的拉斯维加斯市中心（弗里蒙特街）。](img/las-vegas-downtown-at-night-18.tcl) 投资于关系数据库管理系统的一个巨大回报是您不必过多考虑计算机的内部运行。您是程序员，说出您想要的数据类型。计算机的工作是获取它，您并不真正关心如何获取。

也许在您的查询在$500,000 的数据库服务器上连续运行两个小时后，您会开始关心...

在软件开发过程中，表中很少包含大量行。没有人想要在 SQL*Plus 或 Web 表单中输入测试数据。应用程序启动后，表开始填充，人们最终会注意到站点的某个部分运行缓慢。以下是您必须采取的步骤

1.  找到运行速度太慢的 URL。

1.  如果可能的话，请从您的 Web 或应用服务器启用查询日志记录。您希望的是 Web 服务器将每个 SQL 查询和事务写入单个文件，以便您可以准确查看数据库管理系统被告知要做什么以及何时。这是使 Web 编程环境真正高效的功能，很难向选择 Web 编程环境的首席技术官类型进行宣传（即，如果您被迫使用某些闭源的 Web 连接中间件/垃圾软件，则可能无法执行此操作）。

    使用 AOLserver，在您的.ini 文件的`[ns/db/pool/**poolname**]`部分设置`Verbose=On`以启用查询日志记录。查询将显示在错误日志中（默认为"/home/nsadmin/log/server.log"）。

1.  从 Web 浏览器请求有问题的 URL。

1.  启动 Emacs 并将查询日志加载到缓冲区中；从 shell 中运行 sqlplus，使用与 Web 服务器相同的用户名/密码登录

1.  现在，您可以从服务器日志中剪切并粘贴（到 sqlplus）由支持慢 URL 的脚本执行的查询。但是，首先您必须打开跟踪，以便查看 Oracle 正在执行的操作。

    > ```
    > SQL> set autotrace on
    > Unable to verify PLAN_TABLE format or existence
    > Error enabling EXPLAIN report
    > 
    > ```

    糟糕！事实证明 Oracle 对于仅写入标准输出并不满意。对于每个想要跟踪查询的用户，您需要向 sqlplus 提供包含单个表定义的文件$ORACLE_HOME/rdbms/admin/utlxplan.sql：

    > ```
    > create table PLAN_TABLE (
    > 	statement_id 	varchar2(30),
    > 	timestamp    	date,
    > 	remarks      	varchar2(80),
    > 	operation    	varchar2(30),
    > 	options       	varchar2(30),
    > 	object_node  	varchar2(128),
    > 	object_owner 	varchar2(30),
    > 	object_name  	varchar2(30),
    > 	object_instance numeric,
    > 	object_type     varchar2(30),
    > 	optimizer       varchar2(255),
    > 	search_columns  number,
    > 	id		numeric,
    > 	parent_id	numeric,
    > 	position	numeric,
    > 	cost		numeric,
    > 	cardinality	numeric,
    > 	bytes		numeric,
    > 	other_tag       varchar2(255),
    > 	partition_start varchar2(255),
    >         partition_stop  varchar2(255),
    >         partition_id    numeric,
    > 	other		long);
    > 
    > ```

1.  再次输入"set autotrace on"（现在应该可以工作了；如果出现关于 PLUSTRACE 角色的错误，请告诉您的 dbadmin 以 SYS 身份运行$ORACLE_HOME/sqlplus/admin/plustrce.sql，然后授予您的用户该角色）。

1.  输入"set timing on"（您将获得经过时间的报告）

1.  剪切并粘贴感兴趣的查询。

现在我们已经准备好了，让我们看几个例子。

### 一个简单的 B-Tree 索引

假设我们想要询问"显示最近几分钟内请求页面的用户"。这可以支持一个漂亮的"谁现在在线？"页面，就像你在[`www.photo.net/shared/whos-online`](http://www.photo.net/shared/whos-online)看到的那样。这里是查找在最近 10 分钟内请求页面的用户的源代码（600 秒）：

> ```
>  select user_id, first_names, last_name, email from users where last_visit > sysdate - 600/86400 order by upper(last_name), upper(first_names), upper(email) 
> ```

我们正在查询用户表：

> ```
>  create table users ( user_id integer **primary key**, first_names varchar(100) not null, last_name varchar(100) not null, ... email varchar(100) not null unique, ... -- set when user reappears at site **last_visit date**, -- this is what most pages query against (since the above column -- will only be a few minutes old for most pages in a session) second_to_last_visit date, ... ); 
> ```

假设我们要查询关于用户 #37 的信息。Oracle 不需要扫描整个表，因为声明`user_id`为表的主键隐式导致构建索引。然而，`last_visit`列并没有被约束为唯一，因此 Oracle 不会自动构建索引。在 photo.net 上搜索最近访问者将需要扫描`users`表中的所有 60,000 行。我们可以添加一个 B-Tree 索引，多年来任何数据库管理系统中唯一可用的索引类型，使用以下语句：

> ```
>  create index users_by_last_visit on users (last_visit); 
> ```

现在 Oracle 可以简单地首先检查索引，并找到具有小`last_visit`值的`users`表中的行的指针。

### 跟踪/调优案例 1：我们已经插入了消息吗？这里的 SQL 来自 ArsDigita Community System 中一个古老版本的公告板系统（参见[`www.photo.net/bboard/`](http://www.photo.net/bboard/)作为示例）。在我们运行 Illustra 关系数据库管理系统的糟糕时代，执行插入操作需要很长时间，用户会不断点击浏览器上的"重新加载"。当他们都完成时，公告板中会有三份消息的副本。因此，我们修改了插入脚本，检查`bboard`表，看看是否已经存在具有`one_line`和`message`列中完全相同值的消息。因为`message`是一个 CLOB 列，你不能简单地进行"="比较，需要调用 PL/SQL 函数`dbms_lob.instr`，这是 Oracle 内置的 DBMS_LOB 包的一部分。

这里是一个 SQL*Plus 会话，查找已发布主题为"foo"且内容为"bar"的消息：

> ```
> SQL> select count(*) from bboard 
> where topic = 'photo.net'
> and one_line = 'foo'
> and dbms_lob.instr(message,'bar') > 0 ;
> 
>   COUNT(*)
> ----------
> 	 0
> 
> Execution Plan
> ----------------------------------------------------------
>    0	  SELECT STATEMENT Optimizer=CHOOSE
>    1	0   SORT (AGGREGATE)
>    2	1     TABLE ACCESS (BY INDEX ROWID) OF 'BBOARD'
>    3	2	INDEX (RANGE SCAN) OF 'BBOARD_BY_TOPIC' (NON-UNIQUE)
> 
> Statistics
> ----------------------------------------------------------
> 	  0  recursive calls
> 	  0  db block gets
>       59967  consistent gets
>       10299  physical reads
> 	  0  redo size
> 	570  bytes sent via SQL*Net to client
> 	741  bytes received via SQL*Net from client
> 	  4  SQL*Net roundtrips to/from client
> 	  1  sorts (memory)
> 	  0  sorts (disk)
> 	  1  rows processed
> 
> ```

注意到"10,299 个物理读取"。磁盘驱动器非常慢。你真的不想做超过少数物理读取。让我们看一下查询计划的核心：

> ```
>    2	1     TABLE ACCESS (BY INDEX ROWID) OF 'BBOARD'
>    3	2	INDEX (RANGE SCAN) OF 'BBOARD_BY_TOPIC' (NON-UNIQUE)
> 
> ```

看起来 Oracle 正在命中`bboard_by_topic`索引，用于"仅有主题为'photo.net'的行的 ROWID"。然后使用 ROWID，一个内部的 Oracle 指针，从 BBOARD 表中提取实际的行。据推测，Oracle 将仅计算那些 ONE_LINE 和 MESSAGE 列适当的行。在一个有 500 个不同讨论组的安装中，这可能并不那么糟糕。命中索引将消除 499/500 行。但 BBOARD_BY_TOPIC 不是一个非常有选择性的索引。让我们用查询`select topic, count(*) from bboard group by topic order by count(*) desc`来调查选择性：

> | 主题 | 计数(*) |
> | --- | --- |
> | photo.net | 14159 |
> | 自然摄影 | 3289 |
> | 中画幅摘要 | 1639 |
> | 向 Philip 询问 | 91 |
> | 网页/数据库 | 62 |

`bboard`表只有大约 19,000 行，而 photo.net 主题有 14,000 行，大约占了 75%。因此，索引对我们没什么好处。实际上，你本来希望 Oracle 不使用索引。如果需要检查的行数超过 20%，则全表扫描通常比索引扫描快。为什么 Oracle 没有进行全表扫描？因为表尚未"分析"。对于基于成本的优化器没有统计信息，所以使用了较旧的基于规则的优化器。如果想使用高级的基于成本的优化器，你必须定期告诉 Oracle 为表建立统计信息：

> ```
> SQL> analyze table bboard compute statistics;
> 
> Table analyzed.
> 
> SQL> select count(*) from bboard 
> where topic = 'photo.net'
> and one_line = 'foo'
> and dbms_lob.instr(message,'bar') > 0 ;
> 
>   COUNT(*)
> ----------
> 	 0
> 
> Execution Plan
> ----------------------------------------------------------
>    0	  SELECT STATEMENT Optimizer=CHOOSE (Cost=1808 Card=1 Bytes=828)
>    1	0   SORT (AGGREGATE)
>    2	1     TABLE ACCESS (FULL) OF 'BBOARD' (Cost=1808 Card=1 Bytes=828)
> 
> Statistics
> ----------------------------------------------------------
> 	  0  recursive calls
> 	  4  db block gets
>       74280  consistent gets
>       12266  physical reads
> 	  0  redo size
> 	572  bytes sent via SQL*Net to client
> 	741  bytes received via SQL*Net from client
> 	  4  SQL*Net roundtrips to/from client
> 	  1  sorts (memory)
> 	  0  sorts (disk)
> 	  1  rows processed
> 
> ```

最终的数字看起来并不好。但至少成本优化器已经发现主题索引不值多少钱。现在我们只是在扫描整个`bboard`表。在将 20,000 行从 Illustra 转移到 Oracle 期间的 photo.net 升级过程中，我们没有创建任何索引。这加快了加载速度，但随后我们非常高兴地看到系统无死锁地运行，忘记了为了使这个查询快速而在 Illustra 系统上明确使用的索引。

> ```
> SQL> create index bboard_index_by_one_line on bboard ( one_line );
> 
> Index created.
> 
> ```

Bboard 帖子现在按主题行索引，这应该是一个非常有选择性的列，因为不太可能有许多用户选择给他们的问题相同的标题。现在，这个特定的查询将会更快，但插入和更新将会变慢。为什么？每次插入或更新都必须更新硬盘上的`bboard`表块和`bboard_index_by_one_line`块，以确保索引始终具有关于表中内容的最新信息。如果我们有多个物理磁盘驱动器，我们可以指示 Oracle 将索引保留在单独的表空间中，数据库管理员已将其放置在单独的磁盘上：

> ```
> SQL> drop index bboard_index_by_one_line;
> 
> SQL> create index bboard_index_by_one_line 
>      on bboard ( one_line )
>      tablespace philgidx;
> 
> Index created.
> 
> ```

现在索引将被保存在不同的表空间（`philgidx`）中，与主表不同。在插入和更新期间，数据将并行写入两个单独的磁盘驱动器。让我们再试一次这个查询：

> ```
> SQL> select count(*) from bboard 
> where topic = 'photo.net'
> and one_line = 'foo'
> and dbms_lob.instr(message,'bar') > 0 ;
> 
>   COUNT(*)
> ----------
> 	 0
> 
> Execution Plan
> ----------------------------------------------------------
>    0	  SELECT STATEMENT Optimizer=CHOOSE (Cost=2 Card=1 Bytes=828)
>    1	0   SORT (AGGREGATE)
>    2	1     TABLE ACCESS (BY INDEX ROWID) OF 'BBOARD' (Cost=2 Card=1 Bytes=828)
>    3	2	INDEX (RANGE SCAN) OF 'BBOARD_INDEX_BY_ONE_LINE' (NON-UNIQUE) (Cost=1 Card=1)
> 
> Statistics
> ----------------------------------------------------------
> 	  0  recursive calls
> 	  0  db block gets
> 	  3  consistent gets
> 	  3  physical reads
> 	  0  redo size
> 	573  bytes sent via SQL*Net to client
> 	741  bytes received via SQL*Net from client
> 	  4  SQL*Net roundtrips to/from client
> 	  1  sorts (memory)
> 	  0  sorts (disk)
> 	  1  rows processed
> 
> ```

我们已将物理读取次数从 12266 降至 3。Oracle 正在检查`one_line`上的索引，然后使用从索引中检索到的 ROWID 在主表中查找。建立两列的连接索引可能会更好：发布者的用户 ID 和主题行，但在这一点上，你可能会做出 3 次物理读取是可以接受的工程决策。

### 跟踪/调优案例 2：新问题

在每个论坛页面的顶部，例如[`www.photo.net/bboard/q-and-a.tcl?topic=photo.net`](http://www.photo.net/bboard/q-and-a.tcl?topic=photo.net)，ArsDigita 社区系统显示了最近几天（可配置，但默认为 7 天）提出的问题。论坛积累了 30,000 条消息后，此页面变得明显缓慢。

> ```
> SQL> select msg_id, one_line, sort_key, email, name 
> from bboard 
> where topic = 'photo.net' 
> and refers_to is null
> and posting_time > (sysdate - 7)
> order by sort_key desc;
> 
> ...
> 
> 61 rows selected.
> 
> Execution Plan
> ----------------------------------------------------------
>    0	  SELECT STATEMENT Optimizer=CHOOSE (Cost=1828 Card=33 Bytes=27324)
> 
>    1	0   SORT (ORDER BY) (Cost=1828 Card=33 Bytes=27324)
>    2	1     TABLE ACCESS (FULL) OF 'BBOARD' (Cost=1808 Card=33 Bytes=27324)
> 
> Statistics
> ----------------------------------------------------------
> 	  0  recursive calls
> 	  4  db block gets
>       13188  consistent gets
>       12071  physical reads
> 	  0  redo size
>        7369  bytes sent via SQL*Net to client
>        1234  bytes received via SQL*Net from client
> 	  8  SQL*Net roundtrips to/from client
> 	  2  sorts (memory)
> 	  0  sorts (disk)
> 	 61  rows processed
> 
> ```

为了获取 61 行数据，需要进行全表扫描和 12,071 次物理读取！是时候对这个查询进行改进了。由于查询的 WHERE 子句包含 topic、refers_to 和 posting_time，显而易见的尝试是在所有三列上构建一个连接索引：

> ```
> SQL> create index bboard_for_new_questions 
>      on bboard ( topic, refers_to, posting_time ) 
>      tablespace philgidx;
> 
> Index created.
> 
> SQL> select msg_id, one_line, sort_key, email, name 
> from bboard 
> where topic = 'photo.net' 
> and refers_to is null
> and posting_time > (sysdate - 7)
> order by sort_key desc;
> 
> ...
> 
> 61 rows selected.
> 
> Execution Plan
> ----------------------------------------------------------
>    0	  SELECT STATEMENT Optimizer=CHOOSE (Cost=23 Card=33 Bytes=27324)
> 
>    1	0   SORT (ORDER BY) (Cost=23 Card=33 Bytes=27324)
>    2	1     TABLE ACCESS (BY INDEX ROWID) OF 'BBOARD' (Cost=3 Card=33 Bytes=27324)
>    3	2	INDEX (RANGE SCAN) OF 'BBOARD_FOR_NEW_QUESTIONS' (NON-UNIQUE) (Cost=2 Card=33)
> 
> Statistics
> ----------------------------------------------------------
> 	  0  recursive calls
> 	  0  db block gets
> 	 66  consistent gets
> 	 60  physical reads
> 	  0  redo size
>        7369  bytes sent via SQL*Net to client
>        1234  bytes received via SQL*Net from client
> 	  8  SQL*Net roundtrips to/from client
> 	  2  sorts (memory)
> 	  0  sorts (disk)
> 	 61  rows processed
> 
> ```

60 次读取比 12,000 次好。但是有一个清理工作要做。如果我们要保留这个 BBOARD_FOR_NEW_QUESTIONS 索引，而这个索引的第一列是 TOPIC，那么就没有理由再保留 BBOARD_BY_TOPIC 索引了。即使 SQL 只基于 TOPIC 列进行限制，查询优化器也可以使用 BBOARD_FOR_NEW_QUESTIONS。冗余的索引不会导致任何服务失败，但会减慢插入速度。

> ```
> SQL> drop index bboard_by_topic;
> 
> Index dropped.
> 
> ```

我们对自己感到非常满意，所以决定在`bboard`的`refers_to`列上建立一个索引，理由是没有人会单独查询`refers_to`而不查询`topic`。因此他们可以直接使用`bboard_for_new_questions`索引的前两列。以下是一个寻找未回答问题的查询：

> ```
> SQL> select msg_id, one_line, sort_key, email, name
> from bboard bbd1
> where topic = 'photo.net'
> and 0 = (select count(*) from bboard bbd2 where bbd2.refers_to = bbd1.msg_id)
> and refers_to is null
> order by sort_key desc;
> 
> ...
> 
> 57 rows selected.
> 
> Execution Plan
> ----------------------------------------------------------
>    0	  SELECT STATEMENT Optimizer=CHOOSE (Cost=49 Card=33 Bytes=27324)
> 
>    1	0   SORT (ORDER BY) (Cost=49 Card=33 Bytes=27324)
>    2	1     FILTER
>    3	2	TABLE ACCESS (BY INDEX ROWID) OF 'BBOARD' (Cost=29 Card=33 Bytes=27324)
>    4	3	  INDEX (RANGE SCAN) OF 'BBOARD_FOR_NEW_QUESTIONS' (NON-UNIQUE) (Cost=2 Card=33)
>    5	2	INDEX (FULL SCAN) OF 'BBOARD_FOR_NEW_QUESTIONS' (NON-UNIQUE) (Cost=26 Card=7 Bytes=56)
> 
> Statistics
> ----------------------------------------------------------
> 	  0  recursive calls
> 	  0  db block gets
>      589843  consistent gets
>      497938  physical reads
> 	  0  redo size
>        6923  bytes sent via SQL*Net to client
>        1173  bytes received via SQL*Net from client
> 	  7  SQL*Net roundtrips to/from client
> 	  2  sorts (memory)
> 	  0  sorts (disk)
> 	 57  rows processed
> 
> ```

糟糕！497,938 次物理读取。让我们尝试使用索引：

> ```
> SQL> create index bboard_index_by_refers_to 
>      on bboard ( refers_to )
>      tablespace philgidx;
> 
> Index created.
> 
> SQL> select msg_id, one_line, sort_key, email, name
> from bboard bbd1
> where topic = 'photo.net'
> and 0 = (select count(*) from bboard bbd2 where bbd2.refers_to = bbd1.msg_id)
> and refers_to is null
> order by sort_key desc;
> 
> ...
> 
> 57 rows selected.
> 
> Execution Plan
> ----------------------------------------------------------
>    0	  SELECT STATEMENT Optimizer=CHOOSE (Cost=49 Card=33 Bytes=27324)
>    1	0   SORT (ORDER BY) (Cost=49 Card=33 Bytes=27324)
>    2	1     FILTER
>    3	2	TABLE ACCESS (BY INDEX ROWID) OF 'BBOARD' (Cost=29 Card=33 Bytes=27324)
>    4	3	  INDEX (RANGE SCAN) OF 'BBOARD_FOR_NEW_QUESTIONS' (NON-UNIQUE) (Cost=2 Card=33)
>    5	2	INDEX (RANGE SCAN) OF 'BBOARD_INDEX_BY_REFERS_TO' (NON-UNIQUE) (Cost=1 Card=7 Bytes=56)
> 
> Statistics
> ----------------------------------------------------------
> 	  0  recursive calls
> 	  0  db block gets
>        8752  consistent gets
>        2233  physical reads
> 	  0  redo size
>        6926  bytes sent via SQL*Net to client
>        1173  bytes received via SQL*Net from client
> 	  7  SQL*Net roundtrips to/from client
> 	  2  sorts (memory)
> 	  0  sorts (disk)
> 	 57  rows processed
> 
> ```

这仍然是一个相当昂贵的查询，但比以前快了 200 倍，执行时间只需几秒钟。考虑到这是一个不经常请求的页面，这可能已经足够快了。

### 追踪/调优案例 3：强制 Oracle 缓存全表扫描

你可能有一个网站，基本上为用户提供对一个巨大表的访问。为了最大灵活性，可能需要对每个查询进行顺序扫描这个表。一般来说，Oracle 不会缓存在全表扫描期间检索的块。Oracle 调优指南建议在你的 SQL 中包含以下缓存提示：

> ```
> select /*+ FULL (students) CACHE(students) */ count(*) from students;
> 
> ```

但是你会发现，如果你的缓冲区缓存（由 db_block_buffers 控制；见上文）不足以容纳整个表，这种方法是行不通的。Oracle 很聪明，会忽略你的提示。在重新配置 Oracle 安装以拥有更大的缓冲区缓存后，你可能会发现 Oracle 仍然在忽略你的缓存提示。这是因为你还需要

> ```
> analyze table students compute statistics;
> 
> ```

然后 Oracle 将按照调优指南的要求工作。如果你仔细考虑一下，这是有道理的，因为除非 Oracle 大致知道表有多大，否则它不可能开始将东西塞入缓存。

### 如果仍然太慢

![撒玛利亚人。爱尔兰都柏林。](img/dublin-samaritans-18.tcl) 如果你的应用程序仍然太慢，你需要与数据库管理员交谈。如果你既是数据库管理员又是程序员，你需要雇佣一个数据库管理员（"dba"）。

一位专业的数据库管理员擅长找出那些效率低下的查询，并建立索引使其更快。数据库管理员可能会建议您对表进行分区，以便将不经常使用的数据保存在单独的磁盘驱动器上。数据库管理员可以为您在单独的物理磁盘驱动器上创建额外的表空间。通过将分区和索引移动到这些单独的磁盘驱动器上，数据库管理员可以将您的应用程序的速度提高 2 到 3 倍。

2 到 3 倍的提速？听起来不错，直到你想到将信息从磁盘移到 RAM 会使速度提高 10 万倍。这对于数据库更新来说并不是真正可能的，因为必须将其记录在持久介质上（例外情况：高级 EMC 磁盘阵列，其中包含写入缓存和电池以确保写入缓存中的信息的持久性）。但是，对于查询来说相对容易。作为程序员，您可以添加索引并提供优化提示，以增加您的查询从 Oracle 块缓存中得到满足的可能性。数据库管理员可以增加分配给 Oracle 的服务器 RAM 的数量。如果这样做不起作用，数据库管理员可以外出并订购更多的 RAM！

> *1999 年，运行在典型 ArsDigita 服务器上的 Oracle 获得 1 GB 的 RAM。*

### 参考

+   Guy Harrison 的[Oracle SQL 高性能调优](http://www.amazon.com/exec/obidos/ASIN/0136142311/pgreenspun-20)

+   [Oracle8 服务器调优](http://www.oradoc.com/keyword/tuning)

下一步：数据仓库

* * *

[philg@mit.edu](http://philip.greenspun.com/)添加评论
