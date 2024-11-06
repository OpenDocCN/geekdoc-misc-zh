| ![405 号高速公路上的交通。加利福尼亚州洛杉矶。从盖蒂中心眺望。](img/los-angeles-traffic-44.tcl) |
| --- |

## 查询

部分来自 Web 极客的 SQL 的内容，作者是[菲利普·格林斯潘](http://philip.greenspun.com/) | ![俯瞰城市的仙人掌花园。盖蒂中心。加利福尼亚州洛杉矶。](img/getty-center-cactus-garden-7.tcl) |

* * *

如果您启动 SQL*Plus，可以立即开始浏览 SELECT 语句。您甚至不需要定义表；Oracle 为您提供了内置的`dual`表，用于在您对常量或函数感兴趣时：

> ```
>  SQL> select 'Hello World' from dual; 'HELLOWORLD ----------- Hello World SQL> select 2+2 from dual; 2+2 ---------- 4 SQL> select sysdate from dual; SYSDATE ---------- 1999-02-14 
> ```

... 或测试您对三值逻辑的了解（请参阅“数据建模”章节）：

> ```
>  SQL> select 4+NULL from dual; 4+NULL ---------- 
> ```

（任何涉及 NULL 的表达式都会评估为 NULL）。

对于这些目的，`dual`表并没有什么神奇之处；你可以使用`bboard`表而不是`dual`表来计算函数：

> ```
>  select sysdate,2+2,atan2(0, -1) from bboard; SYSDATE 2+2 ATAN2(0,-1) ---------- ---------- ----------- 1999-01-14 4 3.14159265 1999-01-14 4 3.14159265 1999-01-14 4 3.14159265 1999-01-14 4 3.14159265 ... 1999-01-14 4 3.14159265 1999-01-14 4 3.14159265 1999-01-14 4 3.14159265 55010 rows selected. 
> ```

但并不是每个人都想要 55010 份相同结果的副本。`dual`表在 Oracle 安装期间预定义，虽然它只是一个普通的表，但它保证只包含一行，因为没有用户具有足够的权限向`dual`表插入或删除行。

### 超越 Hello World

要超越 Hello World，选择一个感兴趣的表。正如我们在介绍中看到的，

> ````
> select * from users;
> 
> ````

将从`users`表的每一行检索所有信息。这对于玩具系统来说很好，但在任何生产系统中，最好从

> ```
>  SQL> select count(*) from users; COUNT(*) ---------- 7352 
> ```

您实际上不想查看 7352 行数据，但您想看看用户表中的内容，首先请 SQL*Plus 查询 Oracle 的数据字典，并找出`users`表中有哪些列：

> ```
>  SQL> describe users Name Null? Type ------------------------------- -------- ---- USER_ID NOT NULL NUMBER(38) FIRST_NAMES NOT NULL VARCHAR2(100) LAST_NAME NOT NULL VARCHAR2(100) PRIV_NAME NUMBER(38) EMAIL NOT NULL VARCHAR2(100) PRIV_EMAIL NUMBER(38) EMAIL_BOUNCING_P CHAR(1) PASSWORD NOT NULL VARCHAR2(30) URL VARCHAR2(200) ON_VACATION_UNTIL DATE LAST_VISIT DATE SECOND_TO_LAST_VISIT DATE REGISTRATION_DATE DATE REGISTRATION_IP VARCHAR2(50) ADMINISTRATOR_P CHAR(1) DELETED_P CHAR(1) BANNED_P CHAR(1) BANNING_USER NUMBER(38) BANNING_NOTE VARCHAR2(4000) 
> ```

数据字典只是 Oracle 用来存储有关已定义对象（表、触发器等）信息的一组内置表。因此，当您键入`describe`时，SQL*Plus 并没有执行任何黑魔法；它只是查询`user_tab_columns`，这是 Oracle 数据字典中一些表的视图。您可以显式执行相同操作，但有点繁琐。

> ```
>  column fancy_type format a20 select column_name, data_type || '(' || data_length || ')' as fancy_type from user_tab_columns where table_name = 'USERS' order by column_id; 
> ```

在这里，我们必须确保将表名（"USERS"）全部大写。Oracle 在查询中对表和列名不区分大小写，但数据字典记录名称为大写。现在我们知道表中列的名称，探索将会很容易。

### 来自单表的简单查询

从单表进行简单查询的结构如下：

+   select 列表（我们报告中的哪些列）

+   表的名称

+   where 子句（我们想要查看哪些行）

+   order by 子句（我们希望如何排列行）

让我们看一些例子。首先，让我们看看有多少来自 MIT 的用户在我们的网站上注册了：

> ```
>  SQL> select email from users where email like '%mit.edu'; EMAIL ------------------------------ philg@mit.edu andy@california.mit.edu ben@mit.edu ... wollman@lcs.mit.edu ghomsy@mit.edu hal@mit.edu ... jpearce@mit.edu richmond@alum.mit.edu andy_roo@mit.edu kov@mit.edu fletch@mit.edu lsandon@mit.edu psz@mit.edu philg@ai.mit.edu philg@martigny.ai.mit.edu andy@californnia.mit.edu ty@mit.edu teadams@mit.edu 68 rows selected. 
> ```

`email like '%mit.edu'` 表示“每一行的电子邮件列都以 'mit.edu' 结尾”。百分号是 Oracle 的通配符，表示“零个或多个字符”。下划线是表示“正好一个字符”的通配符：

> ```
>  SQL> select email from users where email like '___@mit.edu'; EMAIL ------------------------------ kov@mit.edu hal@mit.edu ... ben@mit.edu psz@mit.edu 
> ```

假设我们在上面的报告中注意到一些相似的电子邮件地址。也许是时候尝试使用 ORDER BY 子句了：

> ```
>  SQL> select email from users where email like '%mit.edu' order by email; EMAIL ------------------------------ andy@california.mit.edu andy@californnia.mit.edu andy_roo@mit.edu ... ben@mit.edu ... hal@mit.edu ... philg@ai.mit.edu philg@martigny.ai.mit.edu philg@mit.edu 
> ```

现在我们可以看到，这个用户表是通过从 1995 年开始对预先生成的 ArsDigita Community Systems 帖子进行处理而生成的。在那些糟糕的旧日子里，用户在每次发布帖子时都要输入他们的电子邮件地址和姓名。由于拼写错误和人们故意选择在不同时间使用不同地址，我们可以看到我们将不得不构建某种应用程序来帮助人类合并用户表中的一些行（例如，“philg”的所有三个出现实际上是同一个人（我））。

### 限制结果

假设您在 1998 年 9 月被 Yahoo 特别介绍，并想查看当月有多少用户注册：

> ```
>  SQL> select count(*) from users where registration_date >= '1998-09-01' and registration_date < '1998-10-01'; COUNT(*) ---------- 920 
> ```

我们在 WHERE 子句中结合了��个限制条件，并使用 AND 添加了另一个限制条件：

> ```
>  SQL> select count(*) from users where registration_date >= '1998-09-01' and registration_date < '1998-10-01' and email like '%mit.edu'; COUNT(*) ---------- 35 
> ```

OR 和 NOT 也可以在 WHERE 子句中使用。例如，以下查询将告诉我们有多少个分类广告没有到期日期，或者到期日期晚于当前日期/时间。

> ```
>  select count(*) from classified_ads where expires >= sysdate or expires is null; 
> ```

### 子查询

您可以查询一个表，根据另一个表中的信息限制返回的行。例如，查找至少发布过一条分类广告的用户：

> ```
>  select user_id, email from users where 0 < (select count(*) from classified_ads where classified_ads.user_id = users.user_id); USER_ID EMAIL ---------- ----------------------------------- 42485 twm@meteor.com 42489 trunghau@ecst.csuchico.edu 42389 ricardo.carvajal@kbs.msu.edu 42393 gon2foto@gte.net 42399 rob@hawaii.rr.com 42453 stefan9@ix.netcom.com 42346 silverman@pon.net 42153 gallen@wesleyan.edu ... 
> ```

从概念上讲，对于 `users` 表中的每一行，Oracle 都会针对 `classified_ads` 运行子查询，以查看与该特定用户 ID 关联的广告数量。请记住，这仅仅是 *概念上*；Oracle SQL 解析器可能选择以更有效的方式执行此查询。

描述相同结果集的另一种方法是使用 EXISTS：

> ```
>  select user_id, email from users where exists (select 1 from classified_ads where classified_ads.user_id = users.user_id); 
> ```

这可能对 Oracle 执行更有效，因为它没有被指示实际计算每个用户的分类广告数量，而只是检查是否存在任何广告。将 EXISTS 视为一个布尔函数

1.  以其唯一参数为 SQL 查询

1.  如果查询返回任何行，无论这些行的内容如何，都返回 TRUE（这就是为什么我们可以在子查询的选择列表中使用常量 1）

### JOIN

一个专业的 SQL 程序员不太可能以前述方式查询已发布分类广告的用户。SQL 程序员知道，不可避免地，发布者将希望从分类广告表中获取信息以及用户表中的信息。例如，我们可能想要查看用户以及每个用户的广告发布顺序：

> ```
>  select users.user_id, users.email, classified_ads.posted from users, classified_ads where users.user_id = classified_ads.user_id order by users.email, posted; USER_ID EMAIL POSTED ---------- ----------------------------------- ---------- 39406 102140.1200@compuserve.com 1998-09-30 39406 102140.1200@compuserve.com 1998-10-08 39406 102140.1200@compuserve.com 1998-10-08 39842 102144.2651@compuserve.com 1998-07-02 39842 102144.2651@compuserve.com 1998-07-06 39842 102144.2651@compuserve.com 1998-12-13 ... 41284 yme@inetport.com 1998-01-25 41284 yme@inetport.com 1998-02-18 41284 yme@inetport.com 1998-03-08 35389 zhupanov@usa.net 1998-12-10 35389 zhupanov@usa.net 1998-12-10 35389 zhupanov@usa.net 1998-12-10 
> ```

由于 JOIN 限制，`where users.user_id = classified_ads.user_id`，我们只看到那些至少发布过一条分类广告的用户，即在 `classified_ads` 表中可能找到匹配行的用户。这与上面的子查询具有相同的效果。

`order by users.email, posted`是确保行按用户分组，然后按发布时间升序打印的关键。

### 外连接

假设我们想要所有用户的按字母顺序排列的列表，对于那些已发布分类广告的用户，还要显示发布日期。我们不能简单地进行 JOIN，因为这将排除未发布任何广告的用户。我们需要的是一个外连接，其中 Oracle 将在无法在`classified_ads`表中找到对应行时“插入 NULL”。

> ```
>  select users.user_id, users.email, classified_ads.posted from users, classified_ads where users.user_id = classified_ads.user_id(+) order by users.email, posted; ... USER_ID EMAIL POSTED ---------- ----------------------------------- ---------- 52790 dbrager@mindspring.com 37461 dbraun@scdt.intel.com 52791 dbrenner@flash.net 47177 dbronz@free.polbox.pl 37296 dbrouse@enter.net 47178 dbrown@cyberhighway.net 36985 dbrown@uniden.com 1998-03-05 36985 dbrown@uniden.com 1998-03-10 34283 dbs117@amaze.net 52792 dbsikorski@yahoo.com ... 
> ```

`classified_ads.user_id`后面的加号是我们对 Oracle 的指示，即“如果无法满足此 JOIN 约束，则添加 NULL 行”。

### 将简单查询扩展为 JOIN

假设您有一个来自一张表的查询几乎返回您所需的所有内容，除了另一张表中的一列。以下是一种开发 JOIN 的方法，而不会危及破坏您的应用程序：

1.  将新表添加到您的 FROM 子句中

1.  添加一个 WHERE 约束以防止 Oracle 构建笛卡尔积

1.  在 SELECT 列表和查询的其他部分中寻找模糊的列名；如果需要，用表名作为前缀

1.  测试一下，确保在添加额外信息时没有破坏任何内容

1.  在 SELECT 列表中添加一个新列

这是我们在麻省理工学院开设的课程的第 2 个问题集的一个示例（参见[`www.photo.net/teaching/psets/ps2/ps2.adp`](http://www.photo.net/teaching/psets/ps2/ps2.adp)）。学生们构建一个会议室预订系统。他们通常定义两个表：`rooms`和`reservations`。顶层页面应该向用户显示他或她当前持有的预订：

> ```
>  select room_id, start_time, end_time from reservations where user_id = 37 
> ```

这会生成一个不可接受的页面，因为房间是通过 ID 号而不是名称引用的。名称信息在`rooms`表中，所以我们必须将其转换为 JOIN。

#### 第 1 步：将新表添加到 FROM 子句中

> ```
>  select room_id, start_time, end_time from reservations**, rooms** where user_id = 37 
> ```

我们陷入了���境，因为 Oracle 现在将会将`rooms`中的每一行与`reservations`中的每一行进行连接，其中`user_id`与已登录用户的匹配。

#### 第 2 步：向 WHERE 子句添加约束

> ```
>  select room_id, start_time, end_time from reservations, rooms where user_id = 37 **and reservations.room_id = rooms.room_id** 
> ```

#### 第 3 步：查找定义模糊的列

`reservations`和`rooms`都包含名为`room_id`的列。因此，我们需要在 SELECT 列表中的`room_id`列前加上“reservations.”。请注意，我们不必在`reservations`中加上`start_time`和`end_time`，因为这些列只存在于`reservations`中。

> ```
>  select **reservations.room_id**, start_time, end_time from reservations, rooms where user_id = 37 and reservations.room_id = rooms.room_id 
> ```

#### 第 4 步：测试

测试查询，确保没有破坏任何内容。你应该得到与之前相同的行和列。

#### 第 5 步：在 SELECT 列表中添加一个新列

我们终于准备好做我们设定的事情了：将`room_name`添加到我们查询的列列表中。

> ```
>  select reservations.room_id, start_time, end_time, **rooms.room_name** from reservations, rooms where user_id = 37 and reservations.room_id = rooms.room_id 
> ```

### 参考

+   Oracle8 Server SQL 参考，[SELECT 命令部分](http://www.oradoc.com/keyword/select)

接下来：复杂查询

* * *

[philg@mit.edu](http://philip.greenspun.com/)添加评论
