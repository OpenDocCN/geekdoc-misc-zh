| ![修复麦金塔连接互联网时不崩溃](img/fixing-a-macintosh-23.tcl) |
| --- |

## 触发器

SQL for Web Nerds 的一部分，由 [Philip Greenspun](http://philip.greenspun.com/) 撰写 | ![伊芙准备阻止麦金塔崩溃](img/macintosh-repair-toolkit-30.tcl) |

* * *

触发器是一段代码片段，您告诉 Oracle 在修改表之前或之后运行。触发器有能力

+   确保某列填充了默认信息

+   确保插入另一个表中的审计行

+   在发现新信息与数据库中的其他内容不一致后，引发一个错误，导致整个事务回滚

考虑`general_comments`表：

> ```
>  create table general_comments ( comment_id integer primary key, on_what_id integer not null, on_which_table varchar(50), user_id not null references users, comment_date date not null, ip_address varchar(50) not null, **modified_date date not null**, content clob, -- is the content in HTML or plain text (the default) html_p char(1) default 'f' check(html_p in ('t','f')), approved_p char(1) default 't' check(approved_p in ('t','f')) ); 
> ```

用户和管理员都能编辑评论。我们想确保知道评论的最后修改时间，以便我们可以为管理员提供“最近修改的评论页面”。我们不想逐个检查所有插入或更新评论的 Web 脚本，我们可以在 Oracle 中指定一个不变量，“每当有人触摸`general_comments`表后，确保`modified_date`列被设置为当前日期时间”。以下是触发器定义：

> ```
>  create trigger general_comments_modified before insert or update on general_comments for each row begin :new.modified_date := sysdate; end; / show errors 
> ```

我们正在使用 PL/SQL 编程语言，详见程序语言章节。在这种情况下，它是一个简单的`begin-end`块，将`modified_date`的`:new`值设置为调用`sysdate`函数的结果。

在使用 SQL*Plus 时，您必须提供一个 / 字符来让程序评估触发器或 PL/SQL 函数定义。然后，如果您希望 SQL*Plus 打印出出了什么问题，您必须说“show errors”。除非您期望一直写出完美的代码，否则在您的 .sql 文件中留下这些 SQL*Plus 咒语可能会很方便。

### 审计表示例

![赌博会计。爱尔兰，都柏林。](img/dublin-turf-accountants-25.tcl) 触发器的典型示例是填充审计表。例如，在 ArsDigita Community System 的数据仓库部分，我们保留用户查询的表格。通常查询的 SQL 代码保存在 `query_columns` 表中。然而，有时用户可能会手动编辑生成的 SQL 代码，这种情况下我们只需将其存储在 `query_sql`queries 表中。查询的 SQL 代码对于业务可能非常重要，可能已经演变了多年。即使我们有良好的关系型数据库备份，我们也不希望因为粗心的鼠标点击而将其删除。因此，我们添加了一个 `queries_audit` 表来保存 `query_sql` 列的历史值：

> ```
>  create table queries ( query_id integer primary key, query_name varchar(100) not null, query_owner not null references users, definition_time date not null, -- if this is non-null, we just forget about all the query_columns -- stuff; the user has hand edited the SQL query_sql varchar(4000) ); create table queries_audit ( query_id integer not null, audit_time date not null, query_sql varchar(4000) ); 
> ```

首先注意到`queries_audit`没有主键。如果我们将`query_id`作为主键，我们只能存储每个查询的一个历史记录，这不是我们的意图。

如何保持这个表的填充？我们可以通过确保每个可能更新`query_sql`列的 Web 脚本在适当时插入`queries_audit`中的一行来实现。但是在将我们的代码交给其他程序员后如何强制执行这一点呢？最好让关系数据库管理系统来执行审计：

> ```
>  create or replace trigger queries_audit_sql before update on queries for each row when (old.query_sql is not null and (new.query_sql is null or old.query_sql <> new.query_sql)) begin insert into queries_audit (query_id, audit_time, query_sql) values (:old.query_id, sysdate, :old.query_sql); end; 
> ```

行级触发器的结构如下：

> ```
>  CREATE OR REPLACE TRIGGER ***trigger name*** ***when*** ON ***which table*** FOR EACH ROW ***conditions for firing*** begin ***stuff to do*** end; 
> ```

让我们回过头来看看我们的触发器：

+   它被命名为`queries_audit_sql`；只要不与其他触发器的名称冲突，这实际上并不重要。

+   它将在`update`之前运行，即只有当有人执行 SQL UPDATE 语句时才会运行。

+   它只会在有人更新`queries`表时运行。

+   它只会在`query_sql`的旧值不为 null 时运行；我们不希望用 NULL 填充我们的审计表。

+   它只会在`query_sql`的新值与旧值不同时运行；我们不希望因为有人恰好在更新`queries`中的另一列而填充我们的审计表。请注意，SQL 的三值逻辑迫使我们为`new.query_sql is null`添加额外的测试，因为当`new.query_sql`为 NULL 时，`old.query_sql <> new.query_sql`不会评估为 true（用户完全清除自定义 SQL；这是一个非常重要的审计案例）。

### 参考

+   Oracle 应用程序开发人员指南，[使用数据库触发器](http://www.oradoc.com/keyword/triggers)

下一步：视图

* * *

[philg@mit.edu](http://philip.greenspun.com/)添加评论
