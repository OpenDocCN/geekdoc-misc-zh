| ![电锯。富尔顿鱼市。曼哈顿 1994 年（火灾前）。](img/fulton-fish-market-65.tcl) |
| --- |

## 事务

Web 极客的 SQL 的一部分，由[Philip Greenspun](http://philip.greenspun.com/)编写 | ![传单。1995 年曼哈顿。](img/handbills-38.tcl) |

* * *

在介绍中，我们讨论了通过在 SQL*Plus 中输入数据来将数据插入数据库的一些示例：

> ```
>  insert into mailing_list (name, email) values ('Philip Greenspun','philg@mit.edu'); 
> ```

一般来说，这并不是操作的方式。作为一个程序员，你编写的代码会在用户提交讨论论坛帖子或分类广告时执行。SQL 语句的结构保持不变，但`values`后面的字符串文字不同。

访问关系数据库的最简单和最直接的接口涉及到使用 C、Java、Lisp、Perl 或 Tcl 等过程式程序将一串 SQL 组合成字符串，然后发送到 RDBMS。以下是 ArsDigita 社区系统如何构建点击日志中的新条目的方式：

> ```
>  insert into clickthrough_log (local_url, foreign_url, entry_date, click_count) values ('$local_url', '$foreign_url', trunc(sysdate), 1)" 
> ```

INSERT 语句添加一行，填充四个列表列。其中两个值来自于 Web 服务器中设置的本地变量，`$local_url`和`$foreign_url`。因为这些是字符串，所以必须用单引号括起来。其中一个值是动态的，直接来自 Oracle：`trunc(sysdate)`。回想一下，在 Oracle 中，`date`数据类型精确到秒。我们只想要每年的这一天的一个这样的行，因此将日期截断到午夜。最后，因为这是当天的第一次点击，我们为`click_count`插入一个常量值 1。

### 原子性

每个 SQL 语句都作为一个原子事务执行。例如，假设你尝试清除一些旧数据

> ```
>  delete from clickthrough_log where entry_date + 120 < sysdate; 
> ```

（删除超过 120 天的点击记录），而`clickthrough_log`中有 3500 行记录超过 120 天。如果你的电脑在执行这个 DELETE 的过程中半途而废，即在事务提交之前失败了，你会发现没有任何一行被删除。要么所有的 3500 行都会消失，要么一个也不会消失。

更有趣的是，你可以将一个事务包裹在多个 SQL 语句周围。例如，当用户正在编辑评论时，ArsDigita 社区系统会记录之前的内容是什么：

> ```
>  ns_db dml $db "begin transaction" # insert into the audit table ns_db dml $db "insert into general_comments_audit (comment_id, user_id, ip_address, audit_entry_time, modified_date, content) select comment_id, user_id, '[ns_conn peeraddr]', sysdate, modified_date, content from general_comments where comment_id = $comment_id" # change the publicly viewable table ns_db dml $db "update general_comments set content = '$QQcontent', html_p = '$html_p' where comment_id = $comment_id" # commit the transaction ns_db dml $db "end transaction" 
> ```

这在数据库行业通常被称为*审计*。数据库本身用于跟踪被更改的内容以及由谁更改的。

让我们逐个部分地看一下这些部分。我们正在查看一个 Tcl 程序，在想与 Oracle 通信时调用 AOLserver API 过程。我们已经配置系统以颠倒正常的 Oracle 世界顺序，即除非另有提交，否则一切都在事务中。`begin transaction`和`end transaction`语句永远不会传递到 Oracle；它们只是给我们的 Oracle 驱动的指令，让 Oracle 进入然后退出自动提交模式。

事务包装器被强加在两个 SQL 语句周围。第一个语句将一行插入`general_comments_audit`。我们可以简单地从 Tcl 查询`general_comments`表，然后使用返回的数据创建一个标准的 INSERT。但是，如果您实际上要做的是将数据从 RDBMS 内的一个地方移动到另一个地方，那么将其全部拖到应用程序中再塞回去是极其不合适的。最好使用"INSERT ... SELECT"形式。

请注意，我们从`general_comments`查询的两列在表中不存在：`sysdate`和`'[ns_conn peeraddr]'`。在 SQL 中，将函数调用或常量放在选择列表中是合法的，就像您在查询章节开头讨论 Oracle 的单行系统表`dual`时看到的那样。为了提醒您：

> ```
>  select sysdate from dual; SYSDATE ---------- 1999-01-14 
> ```

您可以在单个查询中计算多个值：

> ```
>  select sysdate, 2+2, atan2(0, -1) from dual; SYSDATE 2+2 ATAN2(0,-1) ---------- ---------- ----------- 1999-01-14 4 3.14159265 
> ```

这种方法在上面的事务中很有用，其中我们将表中的信息与常量和函数调用结合在一起。这里是一个更简单的例子：

> ```
>  select posting_time, 2+2 from bboard where msg_id = '000KWj'; POSTING_TI 2+2 ---------- ---------- 1998-12-13 4 
> ```

让我们回到我们的评论编辑事务并查看基本结构：

+   开启一个事务

+   将从评论表的 SELECT 语句返回的内容插入到审核表中

+   更新评论表

+   关闭事务

假设在 INSERT 过程中出现问题。存储审核表的表空间已满，无法添加行。将 INSERT 和 UPDATE 放在同一个 RDBMS 事务中确保如果一个出现问题，另一个不会应用于数据库。

### 一致性

假设我们查看了公告板上的一条消息，并决定其内容如此令人反感，我们希望从系统中删除该用户：

> ```
>  select user_id from bboard where msg_id = '000KWj'; USER_ID ---------- 39685 delete from users where user_id = 39685; * ERROR at line 1: ORA-02292: integrity constraint (PHOTONET.SYS_C001526) violated - child record found 
> ```

Oracle 阻止我们删除用户 39685，因为这样做会使数据库处于不一致状态。这是 bboard 表的定义：

> ```
>  create table bboard ( msg_id char(6) not null primary key, refers_to char(6), ... user_id integer not null **references users**, one_line varchar(700), message clob, ... ); 
> ```

`user_id`列被限制为非空。此外，此列中的值必须对应于`users`表中的某一行（`引用 users`）。在我们删除`users`表中 msg_id 000KWj 的作者之前，我们要求 Oracle 将 RDBMS 保持在不一致的状态。

### 互斥

![爱尔兰都柏林的学士步行街。](img/dublin-bachelors-walk-11.tcl) 当您同时执行多个副本相同程序时，您必须考虑*互斥*。如果一个程序必须

+   从数据库中读取一个值

+   根据该值执行计算

+   根据计算更新数据库中的值

然后，您希望通过此段确保一次只执行一个程序副本。

ArsDigita 社区系统的/bboard 模块必须执行此操作。顺序是

+   从`msg_id_generator`表中读取最后一个消息 ID

+   使用一组奇怪的 Tcl 脚本增加消息 ID

+   更新`msg_id_generator`表中的`last_msg_id`列

首先，与锁有关的任何事情只有在这三个操作在事务中组合在一起时才有意义。其次，为了避免死锁，事务必须在事务开始时获取所有需要的资源（包括锁）。Oracle 中的 SELECT 不会获取任何锁，但 SELECT .. FOR UPDATE 会。这是向`bboard`表插入消息的事务的开始（来自/bboard/insert-msg.tcl）：

> ```
>  select last_msg_id from msg_id_generator **for update of last_msg_id** 
> ```

### 互斥（大锤）

`for update`子句并非万能之策。例如，在行动网络（在菲利普和亚历克斯网络出版指南第十六章中描述）中，我们需要确保双击用户不会向政客生成重复的传真。检查用户是否已经回应的测试是

> ```
>  select count(*) from an_alert_log where member_id = $member_id and entry_type = 'sent_response' and alert_id = $alert_id 
> ```

默认情况下，Oracle 一次锁定一行，并不希望您在 SELECT COUNT(*)中加入 FOR UPDATE 子句。这将导致 Oracle 在表中的每一行记录锁定。更有效的方法是简单地开始事务

> ```
>  lock table an_alert_log in exclusive mode 
> ```

这是一个大锤，您不希望持有表锁超过瞬间。因此，获得表锁的页面结构应该是

+   开启一个事务

+   锁定表

+   选择计数(*)

+   如果计数为 0，则插入一行记录用户已回应的事实

+   提交事务（释放表锁）

+   继续执行剩余的脚本

+   ...

### 如果我只想要一些唯一的数字怎么办？

真的需要这么难吗？如果您只想要一些唯一的整数，每个都将用作主键？考虑一个用于保存网站新闻项目的表：

> ```
>  create table news ( title varchar(100) not null, body varchar(4000) not null, release_date date not null, ... ); 
> ```

你可能认为可以使用`title`列作为键，但考虑以下文章：

> ```
>  insert into news (title, body, release_date) values ('French Air Traffic Controllers Strike', 'A walkout today by controllers left travelers stranded..', '1995-12-14'); insert into news (title, body, release_date) values ('French Air Traffic Controllers Strike', 'Passengers at Orly faced 400 canceled flights ...', '1997-05-01'); insert into news (title, body, release_date) values ('Bill Clinton Beats the Rap', 'Only 55 senators were convinced that President Clinton obstructed justice ...', '1999-02-12'); insert into news (title, body, release_date) values ('Bill Clinton Beats the Rap', 'The sexual harassment suit by Paula Jones was dismissed ...', '1998-12-02); 
> ```

看起来，至少就头条新闻而言，报道的内容很少是真正新的。我们能否添加

> ```
>  primary key (title, release_date)
> ```

在我们的表定义的末尾？绝对是的。但是按标题和日期进行键入将导致一些笨拙的 URL 用于编辑或批准新闻文章。如果您的网站允许公共建议，您可能会发现来自多个用户的提交发生冲突。如果您允许对新闻文章发表评论，这是 ArsDigita 社区系统的一个标准功能，每条评论必须引用一篇新闻文章。如果您需要更正`title`列中的拼写错误或更改`release_date`，您必须确保同时更新评论表和新闻表。

传统的数据库设计可以避开所有这些问题，就是使用生成的键。如果您因为不得不携带 MIT 的学生 ID 或医院的患者 ID 而感到烦恼，现在您明白了原因：程序员们正在使用生成的键，并通过暴露软件内部的这部分使他们的生活变得更轻松。

这是 ArsDigita 社区系统的新闻模块的工作原理，摘自[`software.arsdigita.com/www/doc/sql/news.sql`](http://software.arsdigita.com/www/doc/sql/news.sql)：

> ```
>  create sequence news_id_sequence start with 1; create table news ( news_id integer primary key, title varchar(100) not null, body varchar(4000) not null, release_date date not null, ... ); 
> ```

我们正在利用非标准但非常有用的 Oracle *sequence* 功能。在几乎任何 Oracle SQL 语句中，你都可以请求序列的当前值或下一个值。

> ```
>  SQL> create sequence foo_sequence; Sequence created. SQL> select foo_sequence.currval from dual; ERROR at line 1: ORA-08002: sequence FOO_SEQUENCE.CURRVAL is not yet defined in this session 
> ```

糟糕！看起来在我们当前的会话中至少请求了一个密钥之前，我们不能请求当前值。

> ```
>  SQL> select foo_sequence.nextval from dual; NEXTVAL ---------- 1 SQL> select foo_sequence.nextval from dual; NEXTVAL ---------- 2 SQL> select foo_sequence.nextval from dual; NEXTVAL ---------- 3 SQL> select foo_sequence.**currval** from dual; CURRVAL ---------- 3 
> ```

你可以直接在插入中使用序列生成器，例如，

> ```
>  insert into news (news_id, title, body, release_date) values (**news_id_sequence.nextval**, 'Tuition Refund at MIT', 'Administrators were shocked and horrified ...', '1998-03-12); 
> ```

*这个故事的背景：[`philip.greenspun.com/school/tuition-free-mit.html`](http://philip.greenspun.com/school/tuition-free-mit.html)*

在 ArsDigita 社区系统的实现中，`news_id` 实际上是在/news/post-new-2.tcl 中生成的：

> ```
>  set news_id [database_to_tcl_string $db "select news_id_sequence.nextval from dual"] 
> ```

这样实际执行数据库插入的页面，/news/post-new-3.tcl，可以确定用户何时不小心点击了两次提交：

> ```
>  if [catch { ns_db dml $db "insert into news (news_id, title, body, html_p, approved_p, release_date, expiration_date, creation_date, creation_user, creation_ip_address) values ($news_id, '$QQtitle', '$QQbody', '$html_p', '$approved_p', '$release_date', '$expiration_date', sysdate, $user_id, '$creation_ip_address')" } errmsg] { # insert failed; let's see if it was because of duplicate submission if { [database_to_tcl_string $db "select count(*) from news where news_id = $news_id"] == 0 } { # some error other than dupe submission ad_return_error "Insert Failed" "The database ..." return } # we don't bother to handle the cases where there is a dupe submission # because the user should be thanked or redirected anyway } 
> ```

根据我们的经验，在插入时生成密钥的标准技术会导致数据库中有大量重复信息。

### 序列注意事项

Oracle 序列被优化为速度。因此，它们提供了 Oracle 认为对于主键生成所需的最小保证，没有更多。

如果你请求一些 nextvals 并回滚你的事务，序列不会回滚。

你不能依赖序列值是连续的。它们将是唯一的。它们将单调递增。但可能会有间隙。这些间隙是因为 Oracle 默认将 20 个序列值加载到内存中，并将这些值记录为在磁盘上使用。这使得 nextval 非常快，因为新值只需在 RAM 中标记为使用，而不是在磁盘上。但是假设有人在你的数据库服务器仅分发了两个序列值后拔掉了插头。如果你的数据库管理员和系统管理员合作得很好，计算机将重新运行 Oracle。但序列中会有 18 个值的间隙（例如，从 2023 到 2041）。这是因为 Oracle 记录了在磁盘上使用的 20 个值，但只分发了 2 个。

### 更多

+   Oracle8 服务器应用程序开发人员指南，[控制事务](http://www.oradoc.com/keyword/controlling_transactions)

+   Oracle8 服务器 SQL 参考，[CREATE SEQUENCE 部分](http://www.oradoc.com/keyword/createsequence)

下一步：触发器

* * *

[philg@mit.edu](http://philip.greenspun.com/)添加评论
