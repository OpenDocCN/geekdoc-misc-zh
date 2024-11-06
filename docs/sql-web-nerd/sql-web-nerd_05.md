| ![唐人街。加利福尼亚州旧金山](img/san-francisco-chinatown-43.tcl) |
| --- |

## 复杂查询

来自 SQL for Web Nerds 的一部分，作者是[Philip Greenspun](http://philip.greenspun.com/) | ![金门大桥。加利福尼亚州旧金山。](img/golden-gate-duo-87.tcl) |

* * *

假设您想要开始将多行信息合并在一起。例如，您对将用户与其分类广告进行 JOIN 感兴趣。这将为每个发布的广告给出一行。但是您想要将特定用户的所有行合并在一起，并只查看最近的发布时间。您需要的是 GROUP BY 结构：

> ```
>  select users.user_id, users.email, max(classified_ads.posted) from users, classified_ads where users.user_id = classified_ads.user_id group by users.user_id, users.email order by upper(users.email); USER_ID EMAIL MAX(CLASSI ---------- ----------------------------------- ---------- 39406 102140.1200@compuserve.com 1998-10-08 39842 102144.2651@compuserve.com 1998-12-13 41426 50@seattle.va.gov 1997-01-13 37428 71730.345@compuserve.com 1998-11-24 35970 aaibrahim@earthlink.net 1998-11-08 36671 absolutsci@aol.com 1998-10-06 35781 alevy@agtnet.com 1997-07-14 40111 alexzorba@aol.com 1998-09-25 39060 amchiu@worldnet.att.net 1998-12-11 35989 andrew.c.beckner@bankamerica.com 1998-08-13 33923 andy_roo@mit.edu 1998-12-10 
> ```

`group by users.user_id, users.email` 告诉 SQL “将这两列中具有相同值的所有行合并在一起”。除了被分组的列之外，我们还可以对没有被分组的列运行聚合函数。例如，上面的 MAX 应用于特定组中行的发布日期。我们还可以使用 COUNT 来一目了然地查看用户的活跃程度和最近的活跃情况：

> ```
>  select users.user_id, users.email, count(*), max(classified_ads.posted) from users, classified_ads where users.user_id = classified_ads.user_id group by users.user_id, users.email order by upper(users.email); USER_ID EMAIL COUNT(*) MAX(CLASSI ---------- ----------------------------------- ---------- ---------- 39406 102140.1200@compuserve.com 3 1998-10-08 39842 102144.2651@compuserve.com 3 1998-12-13 41426 50@seattle.va.gov 1 1997-01-13 37428 71730.345@compuserve.com 3 1998-11-24 35970 aaibrahim@earthlink.net 1 1998-11-08 36671 absolutsci@aol.com 2 1998-10-06 35781 alevy@agtnet.com 1 1997-07-14 40111 alexzorba@aol.com 1 1998-09-25 39060 amchiu@worldnet.att.net 1 1998-12-11 35989 andrew.c.beckner@bankamerica.com 1 1998-08-13 33923 andy_roo@mit.edu 1 1998-12-10 
> ```

一个真正对这些内容感兴趣的出版商可能不会对这些按字母顺序排列的结果感兴趣。让我们找到我们最近活跃的用户。同时，让我们摆脱报告顶部那个难看的“MAX(CLASSI”：

> ```
>  select users.user_id, users.email, count(*) **as how_many**, max(classified_ads.posted) **as how_recent** from users, classified_ads where users.user_id = classified_ads.user_id group by users.user_id, users.email order by **how_recent desc, how_many desc**; USER_ID EMAIL HOW_MANY HOW_RECENT ---------- ----------------------------------- ---------- ---------- 39842 102144.2651@compuserve.com 3 1998-12-13 39968 mkravit@mindspring.com 1 1998-12-13 36758 mccallister@mindspring.com 1 1998-12-13 38513 franjeff@alltel.net 1 1998-12-13 34530 nverdesoto@earthlink.net 3 1998-12-13 34765 jrl@blast.princeton.edu 1 1998-12-13 38497 jeetsukumaran@pd.jaring.my 1 1998-12-12 38879 john.macpherson@btinternet.com 5 1998-12-12 37808 eck@coastalnet.com 1 1998-12-12 37482 dougcan@arn.net 1 1998-12-12 
> ```

请注意，我们能够在 ORDER BY 子句中使用我们的*关联名称*“how_recent”和“how_many”。ORDER BY 子句中的 `desc`（“降序”）指令指示 Oracle 将最大值放在顶部。默认排序顺序是从最小到最大（“升序”）。

经过仔细检查，结果令人困惑。我们指示 Oracle 首先按日期排名，其次按帖子数量排名。然而，对于 1998-12-13，我们并没有看到两个帖子总数为三的用户排在前面。这是因为 Oracle 的日期精确到秒，即使小时、分钟和秒的细节没有被 SQL*Plus 显示出来。一个更好的查询应该包括以下子句

> ```
>  order by **trunc**(how_recent) desc, how_many desc 
> ```

其中内置的 Oracle 函数`trunc`将每个日期截断到当天的午夜。

### 寻找共同主持人：HAVING 子句

WHERE 子句限制了返回的行。HAVING 子句类似地作用于行的组。例如，假设我们对那些在我们的讨论论坛上做出了重大贡献的用户感兴趣：

> ```
>  select user_id, count(*) as how_many from bboard group by user_id order by how_many desc; USER_ID HOW_MANY ---------- ---------- 34474 1922 35164 985 41112 855 37021 834 34004 823 37397 717 40375 639 ... 33963 1 33941 1 33918 1 7348 rows selected. 
> ```

七千三百行。考虑到我们只对提名几个人感兴趣，这太大了。让我们限制到更近期的活动。三年前的帖子并不一定代表对社区现在的兴趣。

> ```
>  select user_id, count(*) as how_many from bboard **where posting_time + 60 > sysdate** group by user_id order by how_many desc; USER_ID HOW_MANY ---------- ---------- 34375 80 34004 79 37903 49 41074 46 ... 1120 rows selected. 
> ```

我们想要删除行，而不是组，所以我们用 WHERE 子句来实现。让我们摆脱那些已经担任维护者的人。

> ```
>  select user_id, count(*) as how_many from bboard **where not exists (select 1 from bboard_authorized_maintainers bam where bam.user_id = bboard.user_id)** and posting_time + 60 > sysdate group by user_id order by how_many desc; 
> ```

用户 ID 的概念对于行和组都是有意义的，因此我们可以通过上面的额外 WHERE 子句限制我们的结果，或者让关系数据库管理系统生成组，然后我们将要求使用 HAVING 子句将它们丢弃：

> ```
>  select user_id, count(*) as how_many from bboard where posting_time + 60 > sysdate group by user_id **having not exists (select 1 from bboard_authorized_maintainers bam where bam.user_id = bboard.user_id)** order by how_many desc; 
> ```

这并没有解决我们令人烦恼的大量查询结果的根本原因：我们不想看到`how_many`少于 30 的群体。以下是“显示过去 60 天内至少发布 30 条消息的用户，并按多言排名降序排列”的 SQL：

> ```
>  select user_id, count(*) as how_many from bboard where posting_time + 60 > sysdate group by user_id **having count(*) >= 30** order by how_many desc; USER_ID HOW_MANY ---------- ---------- 34375 80 34004 79 37903 49 41074 46 42485 46 35387 30 42453 30 7 rows selected. 
> ```

我们必须在 HAVING 子句中执行此操作，因为组中的行数是一个在 WHERE 子句操作的逐行级别上没有意义的概念。

Oracle 8 的 SQL 解析器太弱了，无法允许您在 HAVING 子句中使用`how_many`关联变量。因此，您必须重复`count(*)`咒语。

### 集合操作：UNION、INTERSECT 和 MINUS Oracle 提供了可用于组合两个或多个单独 SELECT 语句生成的行的集合操作。UNION 汇总了两个查询返回的行，删除任何重复行。INTERSECT 通过删除两个查询结果集中不存在的任何行来组合两个查询的结果集。MINUS 通过从中减去在第二个查询中也找到的任何行，将两个查询的结果组合起来。在这三个操作中，UNION 在实践中最有用。

在 ArsDigita 社区系统的工单跟踪器中，报告错误或请求功能的人将获得一系列潜在的截止日期选项。对于一些项目，常见的项目截止日期存储在`ticket_deadlines`表中。这些应该显示在 HTML SELECT 表单元素中。但是，我们还希望一些选项，如“今天”，“明天”，“下周”和“下个月”。处理这些的最简单方法是查询`dual`表来执行一些日期算术。每个查询将返回一行，如果我们将它们与来自`ticket_deadlines`的查询联合起来，我们可以拥有一个非常简单的 Web 脚本来呈现这些选项：

> ```
>  select 'today - ' || to_char(trunc(sysdate),'Mon FMDDFM'), trunc(sysdate) as deadline from dual UNION select 'tomorrow - '|| to_char(trunc(sysdate+1),'Mon FMDDFM'), trunc(sysdate+1) as deadline from dual UNION select 'next week - '|| to_char(trunc(sysdate+7),'Mon FMDDFM'), trunc(sysdate+7) as deadline from dual UNION select 'next month - '|| to_char(trunc(ADD_MONTHS(sysdate,1)),'Mon FMDDFM'), trunc(ADD_MONTHS(sysdate,1)) as deadline from dual UNION select name || ' - ' || to_char(deadline, 'Mon FMDDFM'), deadline from ticket_deadlines where project_id = :project_id and deadline >= trunc(sysdate) order by deadline 
> ```

将会产生类似于以下的东西

INTERSECT 和 MINUS 运算符很少使用。以下是一些人为的示例。假设您通过 Web 用户收集比赛参赛作品，每个作品都在单独的表中：

> ```
>  create table trip_to_paris_contest ( user_id references users, entry_date date not null ); create table camera_giveaway_contest ( user_id references users, entry_date date not null ); 
> ```

现在让我们填充一些虚拟数据：

> ```
>  -- all three users love to go to Paris insert into trip_to_paris_contest values (1,'2000-10-20'); insert into trip_to_paris_contest values (2,'2000-10-22'); insert into trip_to_paris_contest values (3,'2000-10-23'); -- only User #2 is a camera nerd insert into camera_giveaway_contest values (2,'2000-05-01'); 
> ```

假设我们网站上有一个新的比赛。这次我们将送出一次到曼尼托巴省丘吉尔拍摄北极熊的旅行。我们假设最感兴趣的用户将是那些同时参加了旅行和摄影比赛的用户。让我们获取他们的用户 ID，以便通过电子邮件（垃圾邮件）通知他们有关新比赛的消息：

> ```
>  select user_id from trip_to_paris_contest intersect select user_id from camera_giveaway_contest; USER_ID ---------- 2 
> ```

或者假设我们要组织一次去巴黎的个人旅行，并希望找到有人愿意分享 Crillon 酒店房间费用的人。我们可以假设任何参加巴黎之行比赛的人都有兴趣去。因此，也许我们应该先给他们所有人发电子邮件。另一方面，如果一个人的伴侣不断用电子闪光灯拍照，那么怎么能享受一个安静的晚上呢？我们对参加巴黎之行比赛但*没有*参加相机赠送活动的人感兴趣：

> ```
>  select user_id from trip_to_paris_contest **minus** select user_id from camera_giveaway_contest; USER_ID ---------- 1 3 
> ```

接下来：事务

* * *

[philg@mit.edu](http://philip.greenspun.com/)

### 读者评论

> 在使用 UNION 的较为复杂的情况下，您可以使用 UNION ALL，指示 Oracle 不要删除重复项，并在您知道不会有重复行（或者可能不在乎）时节省排序。
> 
> -- Neal Sidhwaney，2002 年 12 月 10 日
> 
> MINUS 的另一个使用示例显示在以下看起来疯狂的（仅适用于 Oracle [1]）查询中，该查询选择子查询的第 91 到 100 行。
> 
> ```
> with subq as (select * from my_table order by my_id)
> 
> select * from subq 
> where rowid in (select rowid from subq 
>                 where rownum <= 100="" minus="" select="" rowid="" from="" subq="" where="" rownum="" <="90)" pre="">
> 
> *[1] The Oracle dependencies in this query are rowid and rownum. Other databases have other means of limiting query results by row position.* 
> 
> 		
> 
> -- Kevin Murphy, February 10, 2003
> ```
> 
> 而在 PostgreSQL（以及 MySQL 也是如此）中，只需简单地：
> 
> select * from my_table order by my_id limit 90,10
> 
> 对于 Oracle 来说，一个更简单的方法（根据我在 devshed.com 论坛上随机搜索到的一篇帖子）是这样的：
> 
> select * from my_table order by my_id where rownum between 90,100
> 
> （尽管如何使用 MINUS 的整个要点都很重要）
> 
> -- Gabriel Ricard，2003 年 2 月 26 日
> 
> 糟糕。我错了。Phil 给我发了电子邮件，解释说我的 rownum 示例行不通（这只是表明并非互联网上的所有内容都是正确的！）。
> 
> -- Gabriel Ricard，2003 年 3 月 17 日

添加评论
