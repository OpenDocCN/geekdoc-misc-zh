| ![在加利福尼亚州圣迭戈度过的晚上。](img/out-for-the-evening-18.tcl) |
| --- |

## 日期

部分来自 SQL for Web Nerds 的内容，作者是[Philip Greenspun](http://philip.greenspun.com/)，更新于 2003 年 6 月 13 日。

* * *

![哈利和卡特琳娜的婚礼。普莱西德湖。1999 年 9 月 4 日。](img/harry-and-katerina-wedding-81.tcl) 在 Oracle 中表示日期时间信息时，非常重要的是要知道你正在使用的 Oracle 服务器版本。从第 9 版开始，可以使用 ANSI SQL 数据类型如`timestamp`和`interval`来表示时间点和时间间隔。较早版本的 Oracle 使用`date`数据类型表示时间点，精确到一秒，并将时间间隔表示为数字（其中 1 = 一天）。

我们强烈建议在构建新应用程序时使用新提供的 ANSI 数据类型。这些比较干净且更强大，比较老式的 Oracle 特定方式更容易移植应用程序到其他 RDBMS（关系数据库管理系统）。

如果你被迫使用较旧版本的 Oracle 或者在为较旧的数据模型编写查询和事务，请访问`philip.greenspun.com/sql/dates-pre-9`。

### 按日期查询

假设我们有以下表来记录用户注册情况：

> ```
>  create table users ( user_id integer primary key, first_names varchar(50), last_name varchar(50) not null, email varchar(100) not null unique, -- we encrypt passwords using operating system crypt function password varchar(30) not null, -- we only need precision to within one second registration_date timestamp(0) ); -- add some sample data insert into users (user_id, first_names, last_name, email, password, registration_date) values (1,'schlomo','mendelowitz','schlomo@mendelowitz.com','67xui2', to_timestamp('2003-06-13 09:15:00','YYYY-MM-DD HH24:MI:SS')); insert into users (user_id, first_names, last_name, email, password, registration_date) values (2,'George Herbert Walker','Bush','former-president@whitehouse.gov','kl88q', to_timestamp('2003-06-13 15:18:22','YYYY-MM-DD HH24:MI:SS')); 
> ```

让我们查询注册在最后一天的人：

> ```
>  column email format a35 column registration_date format a25 select email, registration_date from users where registration_date > current_date - interval '1' day; EMAIL REGISTRATION_DATE ----------------------------------- ------------------------- schlomo@mendelowitz.com 13-JUN-03 09.15.00 AM former-president@whitehouse.gov 13-JUN-03 03.18.22 PM 
> ```

注意注册日期以非标准格式显示，无法按字典顺序排序，并且年份不是四位数。此时，你应该责备你的数据库管理员没有以更合理的默认设置配置 Oracle。不过，你现在可以自己解决这个问题：

> ```
>  alter session set nls_timestamp_format = 'YYYY-MM-DD HH24:MI:SS'; select email, registration_date from users where registration_date > current_date - interval '1' day; EMAIL REGISTRATION_DATE ----------------------------------- ---------------------- schlomo@mendelowitz.com **2003-06-13 09:15:00** former-president@whitehouse.gov **2003-06-13 15:18:22** 
> ```

你可以查询更短的时间间隔：

> ```
>  select email, registration_date from users where registration_date > current_date - interval '1' hour; EMAIL REGISTRATION_DATE ----------------------------------- ------------------------- former-president@whitehouse.gov 2003-06-13 15:18:22 select email, registration_date from users where registration_date > current_date - interval '1' minute; no rows selected select email, registration_date from users where registration_date > current_date - interval '1' second; no rows selected 
> ```

你可以明确指定时间戳的格式：

> ```
>  select email, to_char(registration_date,'Day, Month DD, YYYY') as reg_day from users order by registration_date; EMAIL REG_DAY ----------------------------------- ----------------------------- schlomo@mendelowitz.com Friday , June 13, 2003 former-president@whitehouse.gov Friday , June 13, 2003 
> ```

糟糕。Oracle 默认会填充某些字段，以便报告能够整齐排列。我们必须自己修剪字符串：

> ```
>  select email, trim(to_char(registration_date,'Day')) || ', ' || trim(to_char(registration_date,'Month')) || ' ' || trim(to_char(registration_date,'DD, YYYY')) as reg_day from users order by registration_date; EMAIL REG_DAY ----------------------------------- ---------------------------- schlomo@mendelowitz.com Friday, June 13, 2003 former-president@whitehouse.gov Friday, June 13, 2003 
> ```

### 一些非常奇怪的事情

Oracle 可能抵制 ANSI 日期时间数据类型和算术的一个原因是，它们可能让程序员的生活变得非常奇怪。

> ```
>  alter session set nls_date_format = 'YYYY-MM-DD'; -- old select add_months(to_date('2003-07-31','YYYY-MM-DD'),-1) from dual; ADD_MONTHS ---------- 2003-06-30 -- new select to_timestamp('2003-07-31','YYYY-MM-DD') - interval '1' month from dual; ERROR at line 1: ORA-01839: date not valid for month specified -- old select to_date('2003-07-31','YYYY-MM-DD') - 100 from dual; TO_DATE('2 ---------- 2003-04-22 -- new (broken) select to_timestamp('2003-07-31','YYYY-MM-DD') - interval '100' day from dual; ERROR at line 1: ORA-01873: the leading precision of the interval is too small -- new (note the extra "(3)") select to_timestamp('2003-07-31','YYYY-MM-DD') - interval '100' day**(3)** from dual; TO_TIMESTAMP('2003-07-31','YYYY-MM-DD')-INTERVAL'100'DAY(3) ------------------------------------------------------------- 2003-04-22 00:00:00 
> ```

### 一些极其痛苦的事情

在表中计算行之间的时间间隔可能非常痛苦，因为标准 SQL 中没有办法引用“报告中上一行的这一列的值”。在命令式计算机语言（如 C＃，Java 或 Visual Basic）中，读取来自 SQL 数据库的行时可以很容易地做到这一点，但在纯 SQL 中做到这一点很困难。

让我们向用户表中再添加几行，看看这是如何工作的。

> ```
>  insert into users (user_id, first_names, last_name, email, password, registration_date) values (3,'Osama','bin Laden','50kids@aol.com','dieusa', to_timestamp('2003-06-13 17:56:03','YYYY-MM-DD HH24:MI:SS')); insert into users (user_id, first_names, last_name, email, password, registration_date) values (4,'Saddam','Hussein','livinlarge@saudi-online.net','wmd34', to_timestamp('2003-06-13 19:12:43','YYYY-MM-DD HH24:MI:SS')); 
> ```

假设我们对注册之间的平均时间长度感兴趣。由于行数很少，我们可以将所有数据查询出来并直接查看：

> ```
>  select registration_date from users order by registration_date; REGISTRATION_DATE ------------------------- 2003-06-13 09:15:00 2003-06-13 15:18:22 2003-06-13 17:56:03 2003-06-13 19:12:43 
> ```

然而，如果我们有大量数据，我们需要进行自连接。

> ```
>  column r1 format a21 column r2 format a21 select u1.registration_date as r1, u2.registration_date as r2 from users u1, users u2 where u2.user_id = (select min(user_id) from users where registration_date > u1.registration_date) order by r1; R1 R2 --------------------- --------------------- 2003-06-13 09:15:00 2003-06-13 15:18:22 2003-06-13 15:18:22 2003-06-13 17:56:03 2003-06-13 17:56:03 2003-06-13 19:12:43 
> ```

注意，为了找到配对的“下一行”，我们使用了 `user_id` 列，我们知道它是连续且唯一的，而不是使用 registration_date 列，因为两个用户可能恰好在同一时间注册。

现在我们从同一报告中的相邻行的信息开始配对，可以开始计算间隔了：

> ```
>  column reg_gap format a21 select u1.registration_date as r1, u2.registration_date as r2, u2.registration_date-u1.registration_date as reg_gap from users u1, users u2 where u2.user_id = (select min(user_id) from users where registration_date > u1.registration_date) order by r1; R1 R2 REG_GAP --------------------- --------------------- --------------------- 2003-06-13 09:15:00 2003-06-13 15:18:22 +000000000 06:03:22 2003-06-13 15:18:22 2003-06-13 17:56:03 +000000000 02:37:41 2003-06-13 17:56:03 2003-06-13 19:12:43 +000000000 01:16:40 
> ```

报告的每一行的间隔都返回为天、小时、分钟和秒。在这一点上，你期望能够对间隔进行平均计算：

> ```
>  select avg(reg_gap) from (select u1.registration_date as r1, u2.registration_date as r2, u2.registration_date-u1.registration_date as reg_gap from users u1, users u2 where u2.user_id = (select min(user_id) from users where registration_date > u1.registration_date)) ERROR at line 1: ORA-00932: inconsistent datatypes: expected NUMBER got INTERVAL 
> ```

糟糕。Oracle 不够聪明，不能聚合时间间隔。而且可悲的是，似乎没有一种简单的方法将时间间隔转换为秒数，例如，适合平均计算。如果你找到了解决方法，请告诉我！

我们应该放弃吗？如果你有很强的胃口，你可以在创建间隔之前将时间戳转换为旧式的 Oracle 日期字符。这将给我们一个作为一天的一部分的结果：

> ```
>  select avg(reg_gap) from (select u1.registration_date as r1, u2.registration_date as r2, to_date(to_char(u2.registration_date,'YYYY-MM-DD HH24:MI:SS'),'YYYY-MM-DD HH24:MI:SS') - to_date(to_char(u1.registration_date,'YYYY-MM-DD HH24:MI:SS'),'YYYY-MM-DD HH24:MI:SS') as reg_gap from users u1, users u2 where u2.user_id = (select min(user_id) from users where registration_date > u1.registration_date)) AVG(REG_GAP) ------------ .13836034 
> ```

如果我们要继续使用这个丑陋的查询，我们应该创建一个视图：

> ```
>  create view registration_intervals as select u1.registration_date as r1, u2.registration_date as r2, to_date(to_char(u2.registration_date,'YYYY-MM-DD HH24:MI:SS'),'YYYY-MM-DD HH24:MI:SS') - to_date(to_char(u1.registration_date,'YYYY-MM-DD HH24:MI:SS'),'YYYY-MM-DD HH24:MI:SS') as reg_gap from users u1, users u2 where u2.user_id = (select min(user_id) from users where registration_date > u1.registration_date) 
> ```

现在我们可以计算平均时间间隔（以分钟为单位）：

> ```
>  select 24*60*avg(reg_gap) as avg_gap_minutes from registration_intervals; AVG_GAP_MINUTES --------------- 199.238889 
> ```

### 报告

下面是使用 `to_char` 函数和 GROUP BY 生成销售报告的示例，按日历季度分组：

> ```
>  select to_char(shipped_date,'YYYY') as shipped_year, to_char(shipped_date,'Q') as shipped_quarter, sum(price_charged) as revenue from sh_orders_reportable where product_id = 143 and shipped_date is not null group by to_char(shipped_date,'YYYY'), to_char(shipped_date,'Q') order by to_char(shipped_date,'YYYY'), to_char(shipped_date,'Q'); SHIPPED_YEAR SHIPPED_QUARTER REVENUE -------------------- -------------------- ---------- 1998 2 1280 1998 3 1150 1998 4 350 1999 1 210 
> ```

这表明 Oracle 有各种花哨的日期格式（在他们的在线文档中介绍）。我们使用 “Q” 掩码来获取日历季度。我们可以看到该产品在 1998 年第二季度开始发货，收入在 1998 年第四季度下降。

### 更多

+   ["新数据类型，新可能性"](http://www.oreillynet.com/lpt/a/2992) by Steven Feuerstein

下一步：限制

* * *

[philg@mit.edu](http://philip.greenspun.com/)

### 读者评论

> 你说：>> 在标准 SQL 中没有办法引用“报告中上一行的此列的值”。
> 
> 至少在 Oracle 8i SQL 中，有一种方式可以引用这个，我肯定它不是标准的，但仍然有用，所以我在这里呈现它。
> 
> 它被称为 Analytic Function。有几个，但在这个示例中演示的是 LAST_VALUE。
> 
> SELECT r1, r2, r2 - r1 reg_gap FROM (SELECT u1.update_date AS r1, LAST_VALUE (update_date) OVER (ORDER BY update_date ASC ROWS BETWEEN CURRENT ROW AND 1 FOLLOWING) AS r2 FROM users u1 WHERE u1.user_id > 100000) WHERE r1 <> r2 ORDER BY r1
> 
> 从内向外，我从用户表中获取 update_date，并使用 LAST_VALUE 函数，要求包括当前行和下一个按时间顺序排列的行在内的最后一个 update_date 值。
> 
> 我使用了更高级别的查询来做差，只是为了避免重复使用冗长的函数，但我本可以一次完成。
> 
> 结果是一样的：
> 
> "R1" "R2" "REG_GAP" 11/10/2003 5:19:00 PM 11/10/2003 8:23:24 PM 0.128055555555556 11/10/2003 8:23:24 PM 11/12/2003 7:53:10 AM 1.47900462962963 11/12/2003 7:53:10 AM 2/13/2004 3:44:47 PM 93.3275115740741
> 
> 尽管如我所说，我使用的是 8i，所以我没有间隔类型。
> 
> 要了解更多关于分析函数的信息，请查看 Oracle 文档 SQL 参考。
> 
> KSF
> 
> -- K SF，2004 年 9 月 1 日
> 
> "一些深刻痛苦的事情--计算表中行之间的时间间隔"非常有用，谢谢。有些人可能需要以下技术来建立一个顺序数字标识符。（在示例中，你假设了“user_id”列，我们知道它是顺序且唯一的）
> 
> 声明 @tmp (registration_date datetime)
> 
> 插入 @tmp
> 
> 从用户中选择 identity(int,1,1) as Sequence, registration_date into #x order by registration_date
> 
> ...（现在在示例中使用 #x 而不是 users）
> 
> 删除表 #x
> 
> -- Steve Davis，2006 年 1 月 29 日
> 
> 你说：“糟糕。Oracle 默认填充一些字段，以便报告整齐排列。我们必须自己修剪字符串。” 不完全正确：可以在格式字符串中使用 FM 修饰符指示 Oracle 自动修剪结果字符串中的空格，就像这样：
> 
> ```
> SQL> select to_char(sysdate,'Day, Month DD, YYYY') from dual;
> 
> TO_CHAR(SYSDATE,'DAY,MONTHDD,
> -----------------------------
> Monday   , May       22, 2006
> 
> SQL> select to_char(sysdate,'FMDay, Month DD, YYYY') from dual;
> 
> TO_CHAR(SYSDATE,'FMDAY,MONTHD
> -----------------------------
> Monday, May 22, 2006
> 
> ```
> 
> 请注意，FM 是一个开关 - 格式字符串中的第二个 FM 取消了第一个的效果。
> 
> -- Vladimir Zakharychev，2006 年 5 月 22 日
> 
> 一点也不漂亮，但它起作用...
> 
> ```
> CREATE OR REPLACE FUNCTION interval_to_seconds(x INTERVAL DAY TO SECOND ) RETURN NUMBER IS
> s VARCHAR2(26);
> days_s VARCHAR2(26);
> time_s VARCHAR2(26);
> N NUMBER(10,6);
> BEGIN
>   s := TO_CHAR(x);
>   days_s := SUBSTR(s,2,INSTR(s,' ')-2);
>   time_s := SUBSTR(s,2+LENGTH(days_s)+1);
>   N := 86400*TO_NUMBER(days_s) + 3600*TO_NUMBER(SUBSTR(time_s,1,2)) + 60*TO_NUMBER(SUBSTR(time_s,4,2)) + TO_NUMBER(SUBSTR(time_s,7));
>   IF SUBSTR(s,1,1) = '-' THEN
>      N := - N; 
>   END IF;
>   RETURN N; 
> END;
> 
> ```
> 
> -- Andre Mostert，2006 年 6 月 20 日
> 
> 1.根据日期找到每个季度的第一个星期一？**选择 Next_day(trunc(to_date(sysdate,'DD-MON-YYYY'), 'Q')-1,'Monday') from dual**
> 
> -- Mohamed Kaleel，2007 年 4 月 13 日
> 
> 计算间隔中的秒数：
> 
> 函数 seconds_from_interval(invInterval IN INTERVAL DAY TO SECOND) 返回 NUMBER IS BEGIN
> 
> 返回 EXTRACT (DAY FROM invInterval) * 86400 +
> 
> 从 invInterval 中提取（HOUR）* 3600 +
> 
> 从 invInterval 中提取（MINUTE）* 60 +
> 
> 从 invInterval 中提取（SECOND）;
> 
> END seconds_from_interval;
> 
> -- Bob Jarvis，2008 年 3 月 4 日

添加评论
