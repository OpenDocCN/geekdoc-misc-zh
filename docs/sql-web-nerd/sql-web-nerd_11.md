| ![夏威夷](img/trees-34.4.jpg) |
| --- |

## Oracle SQL 中的树

SQL for Web Nerds 的一部分，由 [Philip Greenspun](http://philip.greenspun.com/) 著

* * *

![在夏利峡谷的树](img/canyon-de-chelly-tree-5.4.jpg) 表面上看，关系型数据库管理系统似乎是表示和操作树的非常糟糕的工具。本章旨在实现以下目标：

+   向你展示 SQL 数据库中的一行可以被视为一个对象

+   向你展示从一个对象到另一个对象的指针可以通过在常规数据库列中存储整数键来表示

+   演示 Oracle 的树扩展（CONNECT BY ... PRIOR）

+   向您展示如何通过 PL/SQL 解决 CONNECT BY 的限制

Oracle 中树的典型示例是组织图。

> ```
>  create table corporate_slaves ( slave_id integer primary key, supervisor_id references corporate_slaves, name varchar(100) ); insert into corporate_slaves values (1, NULL, 'Big Boss Man'); insert into corporate_slaves values (2, 1, 'VP Marketing'); insert into corporate_slaves values (3, 1, 'VP Sales'); insert into corporate_slaves values (4, 3, 'Joe Sales Guy'); insert into corporate_slaves values (5, 4, 'Bill Sales Assistant'); insert into corporate_slaves values (6, 1, 'VP Engineering'); insert into corporate_slaves values (7, 6, 'Jane Nerd'); insert into corporate_slaves values (8, 6, 'Bob Nerd'); SQL> column name format a20 SQL> select * from corporate_slaves; SLAVE_ID SUPERVISOR_ID NAME ---------- ------------- -------------------- 1 Big Boss Man 2 1 VP Marketing 3 1 VP Sales 4 3 Joe Sales Guy 6 1 VP Engineering 7 6 Jane Nerd 8 6 Bob Nerd 5 4 Bill Sales Assistant 8 rows selected. 
> ```

![约书亚树国家公园](img/joshua-tree-78.tcl) `supervisor_id` 中的整数实际上是指向 `corporate_slaves` 表中其他行的指针。需要显示组织图表吗？只有标准 SQL 可用，您将使用客户端语言（例如 C、Lisp、Perl 或 Tcl）编写程序来执行以下操作：

1.  查询 Oracle，找到雇员 `where supervisor_id is null`，将其称为 `$big_kahuna_id`

1.  查询 Oracle，找到那些 `supervisor_id = $big_kahuna_id` 的雇员

1.  对于每个下属，再次查询 Oracle 以找到他们的下属。

1.  反复执行直到找不到下属，然后回溯到上一级

使用 Oracle CONNECT BY 子句，您可以一次获取所有行：

> ```
>  select name, slave_id, supervisor_id from corporate_slaves connect by prior slave_id = supervisor_id; NAME SLAVE_ID SUPERVISOR_ID -------------------- ---------- ------------- Big Boss Man 1 VP Marketing 2 1 VP Sales 3 1 Joe Sales Guy 4 3 Bill Sales Assistant 5 4 VP Engineering 6 1 Jane Nerd 7 6 Bob Nerd 8 6 VP Marketing 2 1 VP Sales 3 1 Joe Sales Guy 4 3 Bill Sales Assistant 5 4 Joe Sales Guy 4 3 Bill Sales Assistant 5 4 VP Engineering 6 1 Jane Nerd 7 6 Bob Nerd 8 6 Jane Nerd 7 6 Bob Nerd 8 6 Bill Sales Assistant 5 4 20 rows selected. 
> ```

这看起来有点奇怪。看起来 Oracle 已经生成了所有可能的树和子树。让我们添加一个 START WITH 子句：

> ```
>  select name, slave_id, supervisor_id from corporate_slaves connect by prior slave_id = supervisor_id start with slave_id in (select slave_id from corporate_slaves where supervisor_id is null); NAME SLAVE_ID SUPERVISOR_ID -------------------- ---------- ------------- Big Boss Man 1 VP Marketing 2 1 VP Sales 3 1 Joe Sales Guy 4 3 Bill Sales Assistant 5 4 VP Engineering 6 1 Jane Nerd 7 6 Bob Nerd 8 6 8 rows selected. 
> ```

![日出时的树。加利福尼亚州的大瑟尔](img/big-sur-trees-74.tcl) 请注意，我们在 START WITH 子句中使用了一个子查询来找出谁是大领导。在接下来的例子中，我们将只为简洁起见硬编码 `slave_id` 1。

虽然这些人是按正确的顺序排列的，但从前面的报告中很难看出谁为谁工作。Oracle 提供了一个神奇的伪列，只有当查询包含 CONNECT BY 时才有意义。该伪列是 `level`：

> ```
>  select name, slave_id, supervisor_id**, level** from corporate_slaves connect by prior slave_id = supervisor_id start with slave_id = 1; NAME SLAVE_ID SUPERVISOR_ID LEVEL -------------------- ---------- ------------- ---------- Big Boss Man 1 1 VP Marketing 2 1 2 VP Sales 3 1 2 Joe Sales Guy 4 3 3 Bill Sales Assistant 5 4 4 VP Engineering 6 1 2 Jane Nerd 7 6 3 Bob Nerd 8 6 3 8 rows selected. 
> ```

`level` 列可用于缩进。在这里，我们将使用连接运算符 (`||`) 在名字列前添加空格：

> ```
>  column padded_name format a30 select **lpad(' ', (level - 1) * 2) ||** name as padded_name, slave_id, supervisor_id, level from corporate_slaves connect by prior slave_id = supervisor_id start with slave_id = 1; PADDED_NAME SLAVE_ID SUPERVISOR_ID LEVEL ------------------------------ ---------- ------------- ---------- Big Boss Man 1 1 VP Marketing 2 1 2 VP Sales 3 1 2 Joe Sales Guy 4 3 3 Bill Sales Assistant 5 4 4 VP Engineering 6 1 2 Jane Nerd 7 6 3 Bob Nerd 8 6 3 8 rows selected. 
> ```

如果你想限制你的报告，你可以使用标准的 WHERE 子句：

> ```
>  select lpad(' ', (level - 1) * 2) || name as padded_name, slave_id, supervisor_id, level from corporate_slaves **where level <= 3** connect by prior slave_id = supervisor_id start with slave_id = 1; PADDED_NAME SLAVE_ID SUPERVISOR_ID LEVEL ------------------------------ ---------- ------------- ---------- Big Boss Man 1 1 VP Marketing 2 1 2 VP Sales 3 1 2 Joe Sales Guy 4 3 3 VP Engineering 6 1 2 Jane Nerd 7 6 3 Bob Nerd 8 6 3 7 rows selected. 
> ```

假设您希望同一级别的人按字母顺序排序。不幸的是，ORDER BY 子句与 CONNECT BY 结合使用效果不是很好：

> ```
>  select lpad(' ', (level - 1) * 2) || name as padded_name, slave_id, supervisor_id, level from corporate_slaves connect by prior slave_id = supervisor_id start with slave_id = 1 **order by level, name**; PADDED_NAME SLAVE_ID SUPERVISOR_ID LEVEL ------------------------------ ---------- ------------- ---------- Big Boss Man 1 1 VP Engineering 6 1 2 VP Marketing 2 1 2 VP Sales 3 1 2 Bob Nerd 8 6 3 Jane Nerd 7 6 3 Joe Sales Guy 4 3 3 Bill Sales Assistant 5 4 4 select lpad(' ', (level - 1) * 2) || name as padded_name, slave_id, supervisor_id, level from corporate_slaves connect by prior slave_id = supervisor_id start with slave_id = 1 **order by name**; PADDED_NAME SLAVE_ID SUPERVISOR_ID LEVEL ------------------------------ ---------- ------------- ---------- Big Boss Man 1 1 Bill Sales Assistant 5 4 4 Bob Nerd 8 6 3 Jane Nerd 7 6 3 Joe Sales Guy 4 3 3 VP Engineering 6 1 2 VP Marketing 2 1 2 VP Sales 3 1 2 
> ```

SQL 是一种面向集合的语言。在 CONNECT BY 查询的结果中，顺序是有价值的。因此，也没有必要使用 ORDER BY 子句。

### JOIN 与 CONNECT BY 不兼容

![爱尔兰卡林福德。](img/carlingford-83.tcl) 如果我们尝试构建一个报告，显示每个员工及其主管的姓名，我们将看到 Oracle 提供的少数几个信息丰富的错误消息之一：

> ```
>  select lpad(' ', (level - 1) * 2) || cs1.name as padded_name, cs2.name as supervisor_name from corporate_slaves cs1, corporate_slaves cs2 where cs1.supervisor_id = cs2.slave_id(+) connect by prior cs1.slave_id = cs1.supervisor_id start with cs1.slave_id = 1; ERROR at line 4: ORA-01437: cannot have join with CONNECT BY 
> ```

我们可以通过创建一个视图来解决这个特���问题：

> ```
>  create or replace view connected_slaves as select lpad(' ', (level - 1) * 2) || name as padded_name, slave_id, supervisor_id, level as the_level from corporate_slaves connect by prior slave_id = supervisor_id start with slave_id = 1; 
> ```

请注意，我们不得不重命名 `level`，以免最终得到一个以保留字命名的视图列。视图的工作方式与原始查询相同：

> ```
>  select * from connected_slaves; PADDED_NAME SLAVE_ID SUPERVISOR_ID THE_LEVEL ------------------------------ ---------- ------------- ---------- Big Boss Man 1 1 VP Marketing 2 1 2 VP Sales 3 1 2 Joe Sales Guy 4 3 3 Bill Sales Assistant 5 4 4 VP Engineering 6 1 2 Jane Nerd 7 6 3 Bob Nerd 8 6 3 8 rows selected. 
> ```

但是现在我们可以进行 JOIN 操作了

> ```
>  select padded_name, corporate_slaves.name as supervisor_name from connected_slaves, corporate_slaves where connected_slaves.supervisor_id = corporate_slaves.slave_id(+); PADDED_NAME SUPERVISOR_NAME ------------------------------ -------------------- Big Boss Man VP Marketing Big Boss Man VP Sales Big Boss Man Joe Sales Guy VP Sales Bill Sales Assistant Joe Sales Guy VP Engineering Big Boss Man Jane Nerd VP Engineering Bob Nerd VP Engineering 8 rows selected. 
> ```

如果您有敏锐的眼睛，您会注意到我们实际上进行了 OUTER JOIN，这样我们的结果不会排除大老板。

### Select-list 子查询 *可以* 与 CONNECT BY 一起使用

与 VIEW 和 JOIN 不同，我们可以在选择列表中添加子查询：

> ```
>  select lpad(' ', (level - 1) * 2) || name as padded_name, (select name from corporate_slaves cs2 where cs2.slave_id = cs1.supervisor_id) as supervisor_name from corporate_slaves cs1 connect by prior slave_id = supervisor_id start with slave_id = 1; PADDED_NAME SUPERVISOR_NAME ------------------------------ -------------------- Big Boss Man VP Marketing Big Boss Man VP Sales Big Boss Man Joe Sales Guy VP Sales Bill Sales Assistant Joe Sales Guy VP Engineering Big Boss Man Jane Nerd VP Engineering Bob Nerd VP Engineering 8 rows selected. 
> ```

在 Oracle 中的一般规则是，您可以在选择列表中的任何地方有一个返回单行的子查询。

### 这个人是为我工作的吗？

假设您已经构建了一个企业内部 Web 服务。有些内容您的软件应该向员工的老板（或老板的老板）展示，而不应该向下属或同事展示。在这里，我们试图弄清楚市场副总裁（#2）是否对简·纳德（#7）具有监督权限：

> ```
>  select count(*) from corporate_slaves where slave_id = 7 and level > 1 start with slave_id = 2 connect by prior slave_id = supervisor_id; COUNT(*) ---------- 0 
> ```

显然不是。请注意，我们从市场副总裁（#2）开始，并规定 `level > 1` 以确保我们永远不会得出某人监督自己的结论。让我们问一下大老板（#1）是否对简·纳德有权：

> ```
>  select count(*) from corporate_slaves where slave_id = 7 and level > 1 start with slave_id = 1 connect by prior slave_id = supervisor_id; COUNT(*) ---------- 1 
> ```

即使大老板不是简·纳德的直接主管，要求 Oracle 计算相关子树仍然给我们带来了正确的结果。在 ArsDigita Community System Intranet 模块中，我们决定这个计算太重要，不能仅作为个别网页中的查询。我们将问题集中在一个 PL/SQL 过程中：

> ```
>  create or replace function intranet_supervises_p (query_supervisor IN integer, query_user_id IN integer) return varchar is n_rows_found integer; BEGIN select count(*) into n_rows_found from intranet_users where user_id = query_user_id and level > 1 start with user_id = query_supervisor connect by supervisor = PRIOR user_id; if n_rows_found > 0 then return 't'; else return 'f'; end if; END intranet_supervises_p; 
> ```

### 家族谱系

如果图表比员工-主管关系更复杂怎么办？例如，假设您正在表示一个家族谱系。即使不考虑离婚和再婚、南非异国情调的生育诊所等，我们仍然需要为每个节点添加多个指针：

> ```
>  create table family_relatives ( relative_id integer primary key, **spouse references family_relatives, mother references family_relatives, father references family_relatives,** -- in case they don't know the exact birthdate birthyear integer, birthday date, -- sadly, not everyone is still with us deathyear integer, first_names varchar(100) not null, last_name varchar(100) not null, sex char(1) check (sex in ('m','f')), -- note the use of multi-column check constraints check ( birthyear is not null or birthday is not null) ); -- some test data insert into family_relatives (relative_id, first_names, last_name, sex, spouse, mother, father, birthyear) values (1, 'Nick', 'Gittes', 'm', NULL, NULL, NULL, 1902); insert into family_relatives (relative_id, first_names, last_name, sex, spouse, mother, father, birthyear) values (2, 'Cecile', 'Kaplan', 'f', 1, NULL, NULL, 1910); update family_relatives set spouse = 2 where relative_id = 1; insert into family_relatives (relative_id, first_names, last_name, sex, spouse, mother, father, birthyear) values (3, 'Regina', 'Gittes', 'f', NULL, 2, 1, 1934); insert into family_relatives (relative_id, first_names, last_name, sex, spouse, mother, father, birthyear) values (4, 'Marjorie', 'Gittes', 'f', NULL, 2, 1, 1936); insert into family_relatives (relative_id, first_names, last_name, sex, spouse, mother, father, birthyear) values (5, 'Shirley', 'Greenspun', 'f', NULL, NULL, NULL, 1901); insert into family_relatives (relative_id, first_names, last_name, sex, spouse, mother, father, birthyear) values (6, 'Jack', 'Greenspun', 'm', 5, NULL, NULL, 1900); update family_relatives set spouse = 6 where relative_id = 5; insert into family_relatives (relative_id, first_names, last_name, sex, spouse, mother, father, birthyear) values (7, 'Nathaniel', 'Greenspun', 'm', 3, 5, 6, 1930); update family_relatives set spouse = 7 where relative_id = 3; insert into family_relatives (relative_id, first_names, last_name, sex, spouse, mother, father, birthyear) values (8, 'Suzanne', 'Greenspun', 'f', NULL, 3, 7, 1961); insert into family_relatives (relative_id, first_names, last_name, sex, spouse, mother, father, birthyear) values (9, 'Philip', 'Greenspun', 'm', NULL, 3, 7, 1963); insert into family_relatives (relative_id, first_names, last_name, sex, spouse, mother, father, birthyear) values (10, 'Harry', 'Greenspun', 'm', NULL, 3, 7, 1965); 
> ```

在应用员工示例中的教训时，我们现在面临的最明显问题是要遵循母亲还是父亲的指针：

> ```
>  column full_name format a25 -- follow patrilineal (start with my mom's father) select lpad(' ', (level - 1) * 2) || first_names || ' ' || last_name as full_name from family_relatives connect by prior relative_id = father start with relative_id = 1; FULL_NAME ------------------------- Nick Gittes Regina Gittes Marjorie Gittes -- follow matrilineal (start with my mom's mother) select lpad(' ', (level - 1) * 2) || first_names || ' ' || last_name as full_name from family_relatives connect by prior relative_id = mother start with relative_id = 2; FULL_NAME ------------------------- Cecile Kaplan Regina Gittes Suzanne Greenspun Philip Greenspun Harry Greenspun Marjorie Gittes 
> ```

这是官方 Oracle 文档对 CONNECT BY 的说法：

> 指定层次结构的父行和子行之间的关系。条件可以是 "Conditions" 中描述的任何条件。然而，条件的某部分必须使用 PRIOR 运算符来引用父行。包含 PRIOR 运算符的条件部分必须具有以下形式之一：
> 
> ```
> PRIOR expr comparison_operator expr 
> expr comparison_operator PRIOR expr 
> 
> ```

没有规定 `comparison_operator` 必须仅仅是等号。让我们再次从我妈的爸爸开始，但是 CONNECT BY 可以使用多个列：

> ```
>  -- follow both select lpad(' ', (level - 1) * 2) || first_names || ' ' || last_name as full_name from family_relatives connect by prior relative_id **in (mother, father)** start with relative_id = 1; FULL_NAME ------------------------- Nick Gittes Regina Gittes Suzanne Greenspun Philip Greenspun Harry Greenspun Marjorie Gittes 
> ```

而不是随意从 Nick 爷爷开始，让我们让 Oracle 显示所有以父母未知的人开始的树：

> ```
>  select lpad(' ', (level - 1) * 2) || first_names || ' ' || last_name as full_name from family_relatives connect by prior relative_id in (mother, father) start with relative_id **in (select relative_id from family_relatives where mother is null and father is null);** FULL_NAME ------------------------- Nick Gittes Regina Gittes Suzanne Greenspun Philip Greenspun Harry Greenspun Marjorie Gittes Cecile Kaplan Regina Gittes Suzanne Greenspun Philip Greenspun Harry Greenspun Marjorie Gittes Shirley Greenspun Nathaniel Greenspun Suzanne Greenspun Philip Greenspun Harry Greenspun Jack Greenspun Nathaniel Greenspun Suzanne Greenspun Philip Greenspun Harry Greenspun 22 rows selected. 
> ```

### PL/SQL 而不是 JOIN

![新罕布什尔州 16 号公路 Glen Ellis 瀑布上的树枝](img/glen-ellis-tree-branch-86.tcl) 上述报告很有趣，但令人困惑，因为很难看出树在哪里结婚。如上所述，您不能使用 CONNECT BY 进行 JOIN。我们演示了将 CONNECT BY 嵌入视图中的解决方法。一个更通用的解决方法是使用 PL/SQL：

> ```
>  create or replace function family_spouse_name (v_relative_id family_relatives.relative_id%TYPE) return varchar is v_spouse_id integer; spouse_name varchar(500); BEGIN select spouse into v_spouse_id from family_relatives where relative_id = v_relative_id; if v_spouse_id is null then return null; else select (first_names || ' ' || last_name) into spouse_name from family_relatives where relative_id = v_spouse_id; return spouse_name; end if; END family_spouse_name; / show errors column spouse format a20 select lpad(' ', (level - 1) * 2) || first_names || ' ' || last_name as full_name, **family_spouse_name(relative_id) as spouse** from family_relatives connect by prior relative_id in (mother, father) start with relative_id in (select relative_id from family_relatives where mother is null and father is null); FULL_NAME SPOUSE ------------------------- -------------------- Nick Gittes Cecile Kaplan Regina Gittes Nathaniel Greenspun Suzanne Greenspun Philip Greenspun Harry Greenspun Marjorie Gittes Cecile Kaplan Nick Gittes Regina Gittes Nathaniel Greenspun Suzanne Greenspun Philip Greenspun Harry Greenspun Marjorie Gittes Shirley Greenspun Jack Greenspun Nathaniel Greenspun Regina Gittes Suzanne Greenspun Philip Greenspun Harry Greenspun Jack Greenspun Shirley Greenspun Nathaniel Greenspun Regina Gittes Suzanne Greenspun Philip Greenspun Harry Greenspun 
> ```

### PL/SQL 而不是 JOIN 和 GROUP BY

假设除了在网页中显示家谱之外，我们还想在有关家庭成员的故事可用时显示一个标志。首先，我们需要一种表示故事的方式：

> ```
>  create table family_stories ( family_story_id integer primary key, story clob not null, item_date date, item_year integer, access_control varchar(20) check (access_control in ('public', 'family', 'designated')), check (item_date is not null or item_year is not null) ); -- a story might be about more than one person create table family_story_relative_map ( family_story_id references family_stories, relative_id references family_relatives, primary key (relative_id, family_story_id) ); -- put in a test story insert into family_stories (family_story_id, story, item_year, access_control) values (1, 'After we were born, our parents stuck the Wedgwood in a cabinet and bought indestructible china. Philip and his father were sitting at the breakfast table one morning. Suzanne came downstairs and, without saying a word, took a cereal bowl from the cupboard, walked over to Philip and broke the bowl over his head. Their father immediately started laughing hysterically.', 1971, 'public'); insert into family_story_relative_map (family_story_id, relative_id) values (1, 8); insert into family_story_relative_map (family_story_id, relative_id) values (1, 9); insert into family_story_relative_map (family_story_id, relative_id) values (1, 7); 
> ```

要显示家庭成员列表旁边的故事数量，我们通常会进行 OUTER JOIN，然后按除了`count(family_story_id)`之外的列进行 GROUP BY。然而，为了不干扰 CONNECT BY，我们创建另一个 PL/SQL 函数：

> ```
>  create or replace function family_n_stories (v_relative_id family_relatives.relative_id%TYPE) return integer is n_stories integer; BEGIN select count(*) into n_stories from family_story_relative_map where relative_id = v_relative_id; return n_stories; END family_n_stories; / show errors select lpad(' ', (level - 1) * 2) || first_names || ' ' || last_name as full_name, family_n_stories(relative_id) as n_stories from family_relatives connect by prior relative_id in (mother, father) start with relative_id in (select relative_id from family_relatives where mother is null and father is null); FULL_NAME N_STORIES ------------------------- ---------- Nick Gittes 0 ... Shirley Greenspun 0 Nathaniel Greenspun 1 Suzanne Greenspun 1 Philip Greenspun 1 Harry Greenspun 0 ... 
> ```

![Point Lobos 的树。加利福尼亚海岸，卡梅尔以南。](img/point-lobos-tree-25.tcl)

### 逆向工作

从最年轻的一代开始逆向工作是什么样子？

> ```
>  select lpad(' ', (level - 1) * 2) || first_names || ' ' || last_name as full_name, family_spouse_name(relative_id) as spouse from family_relatives connect by relative_id in (prior mother, prior father) start with relative_id = 9; FULL_NAME SPOUSE ------------------------- -------------------- Philip Greenspun Regina Gittes Nathaniel Greenspun Nick Gittes Cecile Kaplan Cecile Kaplan Nick Gittes Nathaniel Greenspun Regina Gittes Shirley Greenspun Jack Greenspun Jack Greenspun Shirley Greenspun 
> ```

我们应该能够查看所有从叶子开始的树，但是 Oracle 似乎表现出奇怪的行为：

> ```
>  select lpad(' ', (level - 1) * 2) || first_names || ' ' || last_name as full_name, family_spouse_name(relative_id) as spouse from family_relatives connect by relative_id in (prior mother, prior father) start with relative_id not in (select mother from family_relatives union select father from family_relatives); no rows selected 
> ```

出了什么问题？如果我们单独尝试子查���，我们会得到一个合理的结果。这里是至少在`mother`或`father`列中出现一次的所有`relative_id`s。

> ```
>  select mother from family_relatives union select father from family_relatives MOTHER ---------- 1 2 3 5 6 7 7 rows selected. 
> ```

答案就在底部的额外空行中。在这个结果集中有一个 NULL。实验表明 Oracle 在处理 NULL 和 IN 和 NOT IN 时表现不对称：

> ```
>  SQL> select * from dual where 1 in (1,2,3,NULL); D - X SQL> select * from dual where 1 not in (2,3,NULL); no rows selected 
> ```

答案隐藏在 Oracle 的 NOT IN 文档中："如果集合中的任何成员为 NULL，则评估为 FALSE。" 在这种情况下正确的查询是？

> ```
>  select lpad(' ', (level - 1) * 2) || first_names || ' ' || last_name as full_name, family_spouse_name(relative_id) as spouse from family_relatives connect by relative_id in (prior mother, prior father) start with relative_id not in (select mother from family_relatives where mother is not null union select father from family_relatives where father is not null); FULL_NAME SPOUSE ------------------------- -------------------- Marjorie Gittes Nick Gittes Cecile Kaplan Cecile Kaplan Nick Gittes Suzanne Greenspun Regina Gittes Nathaniel Greenspun Nick Gittes Cecile Kaplan Cecile Kaplan Nick Gittes Nathaniel Greenspun Regina Gittes Shirley Greenspun Jack Greenspun Jack Greenspun Shirley Greenspun Philip Greenspun Regina Gittes Nathaniel Greenspun Nick Gittes Cecile Kaplan Cecile Kaplan Nick Gittes Nathaniel Greenspun Regina Gittes Shirley Greenspun Jack Greenspun Jack Greenspun Shirley Greenspun Harry Greenspun Regina Gittes Nathaniel Greenspun Nick Gittes Cecile Kaplan Cecile Kaplan Nick Gittes Nathaniel Greenspun Regina Gittes Shirley Greenspun Jack Greenspun Jack Greenspun Shirley Greenspun 24 rows selected. 
> ```

### 性能和调优

![Elke 爬树。1993 年，不列颠哥伦比亚省维多利亚。](img/elke-in-tree-60.tcl) Oracle 在从 CONNECT BY 生成结果时没有得到树精灵的帮助。如果您不希望树查询花费 O(N²) 的时间，您需要构建索引，让 Oracle 能够非常快速地回答形式为 "Parent X 的所有子代是什么？" 的问题。

对于公司奴隶表，您可能需要两个连接的索引：

> ```
>  create index corporate_slaves_idx1 on corporate_slaves (slave_id, supervisor_id); create index corporate_slaves_idx2 on corporate_slaves (supervisor_id, slave_id); 
> ```

### 参考

![亚利桑那州北部石化森林中的一棵树。](img/petrified-forest-tree-15.4.jpg)

+   [CONNECT BY 的 SQL 参考部分](http://www.oradoc.com/keyword/connectby)

+   [PL/SQL 用户指南和参考资料](http://www.oradoc.com/keyword/plsql)

### 无谓的照片

![约书亚树国家公园](img/joshua-tree-79.tcl)![莫哈韦沙漠。约书亚树国家公园](img/joshua-tree-40.tcl)![佛罗伦萨的博博利花园](img/boboli-tree-lane-72.tcl)![佛蒙特州皮查姆附近的枫树](img/maple-trees-12.tcl)

![约书亚树。约书亚树国家公园。](img/joshua-tree-10.4.jpg)

下一个：日期

* * *

[philg@mit.edu](http://philip.greenspun.com/)

### 读者评论

> Oracle9i 在连接上执行 CONNECT BY。它还添加了一个"ORDER SIBLINGS BY"子句，修复了阻止您对查询的每个级别进行排序的遗漏。
> 
> 在 Dartmouth 找不到这篇文章:(，看起来真的很有趣！
> 
> -- Andrew Wolfe, March 24, 2004
> 
> 感兴趣的读者应该查看 Joe Celko 关于在 SQL 中表示树的嵌套集模型。不需要被锁定在专有的 SQL 方言中，而且查询速度可能快上几个数量级！
> 
> 这里有一些链接...
> 
> + http://www.intelligententerprise.com/001020/celko.jhtml
> 
> + http://www.dbmsmag.com/9603d06.html
> 
> + http://www.dbmsmag.com/9604d06.html
> 
> + http://www.dbmsmag.com/9605d06.html
> 
> + http://www.dbmsmag.com/9606d06.html
> 
> + http://www.sqlteam.com/Forums/topic.asp?TOPIC_ID=14099
> 
> + http://www.dbazine.com/oracle/or-articles/tropashko4
> 
> + http://mrnaz.com/static/articles/trees_in_sql_tutorial/mptt_overview.php
> 
> 致敬，Mattster
> 
> -- Matt Anon, April 3, 2007

添加评论

### 相关链接

+   [在 SQL 中表示 m 叉树](http://www.cs.dartmouth.edu/~apd/archives/000019.html)- 这种方法允许非常快速地检索后代和修改 m 叉树。不需要自引用或嵌套的选择语句来检索一些或所有后代。节点的标记使得可以非常简单快速地查询节点的 DFS 顺序。它在某种程度上受到哈夫曼编码的启发。 （由 Anthony D'Auria 贡献）

+   [失效链接](http://web.archive.org/web/*/http://www.cs.dartmouth.edu/~apd/archives/000019.html)- 上面的链接到达特茅斯学院的链接似乎已经失效，但 Web Archive 保存了页面的副本 （由 Tom Lebr 贡献）

添加链接
