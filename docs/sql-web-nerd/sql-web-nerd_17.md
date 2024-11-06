| ![](img/fountain-eccentric-50.tcl) |
| --- |

## 我没事，你有点怪

部分来自 Web 网络极客的 SQL 作者[菲利普·格林斯潘](http://philip.greenspun.com/) |

* * *

![规则。慕田峪（中国长城）](img/mutianyu-cablecar-rules-24.tcl) 规范化是一种将数据拆分直到每个表都代表关于一种类型事物的命题的方法。规范化是数据库管理系统学术课程和工作面试中备受喜爱的主题，因为（1）它具有正式主义的外观，（2）易于测试。如果你告诉别人你上过数据库管理系统课程，然后在他们问你数据是否符合第三范式时一脸茫然，你将永远得不到数据库极客的尊重。很多想法看起来都是常识，很多争论都是上世纪 60 年代在关系数据库管理系统出现之前就存在的。然而，中期 1990 年代的面向对象关系数据库热潮重新唤起了一些这些问题，因此值得研究规范化。

### 怪异

假设你决心娶电影女演员温娜·赖德，她于 1971 年 10 月 29 日出生，原名"温娜·霍洛维茨"。由于好莱坞和硅谷的融合，你设法在奥斯卡颁奖典礼上获得了一个座位。在与赖德女士交谈时，你希望既了解她的作品，又显得轻松自然。于是你决定建立一个小数据库，在颁奖之前为自己提供指导，并在需要时通过 WAP 手机提供相同的数据，以防在与赖德女士的对话中遇到困难。

| 电影 ID | 标题 | 发行年份 | 制片人 | 导演 | 编剧 | 作曲家 | Steadicam 操作员 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | 异形 4：复活 | 1997 | 比尔·巴达拉托 | 让-皮埃尔·让内 | 乔斯·韦登 | 约翰·弗里泽尔 | 大卫·艾默里奇斯 |
| 2 | 无辜年代 | 1993 | 巴巴拉·德·菲纳 | 马丁·斯科塞斯 | 艾迪丝·沃顿、杰伊·考克斯和马丁·斯科塞斯 | 艾尔默·伯恩斯坦 | 拉里·麦康基 |
| 3 | 青春狂想曲 | 1989 | 丹尼斯·迪诺维 | 迈克尔·莱曼 | 丹尼尔·沃特斯 | 大卫·纽曼 | -- |

如果你记住这些内容，你可以用这样的问题吸引赖德女士的注意：“你不觉得《无辜年代》中拉里·麦康基的 Steadicam 工作比《异形 4》中大卫·艾默里奇斯的要好得多吗？”或者如果你想展示你对美国文学的了解，可以说：“杰伊·考克斯和马丁·斯科塞斯创作的剧本之丰富程度令人惊讶，考虑到他们从艾迪丝·沃顿原著中开始时的材料之薄弱。”

假设 Winona Ryder 对您的知识印象深刻到足以回到您在 Regent Beverly Wilshire 套房的地方。利用房间内的以太网连接，您在笔记本电脑上留下了一个远程 Emacs 窗口。Ryder 女士在您的辅导应用程序源代码中看到您的 SQL 查询，并大声喊道“嘿，这些数据甚至不符合第一范式（1NF）。”

这是一个错误。如果你的数据不符合第一范式，甚至没有一个 DBMS 专家术语来描述你所拥有的数据。粗略地说，你的数据是*异常的*。你的数据模型有什么问题？对于《异形》和《Heathers》，你在`Writer`列中有一个名字。对于《无辜之年》，你有三个名字。这被称为*重复组*或*多值列*，它有以下问题：

+   如果列中的值数量超出预期而增长，你可能没有足够的空间

+   表名、列名和键值的组合不再指定一个数据

+   基本的 INSERT、UPDATE 和 SELECT 操作不足以操作多值列

+   程序员的大脑必须同时适应表行中无序数据和多值列内有序数据

+   设计的不透明性。如果您使用多值列，人们永远不知道在查看设计内部时会发生什么；您是使用多个表来表示一对多关系还是多值列？

这些问题意味着多值列是无用的吗？可能不是。Oracle 在其服务器的 8.0 版本中引入了对多值列的*两种*支持：

> ```
> For modelling one-to-many relationships, Oracle supports two collection
> datatypes: varrays and nested tables. For example, a purchase order has
> an arbitrary number of line items, so you may want to put the line items
> into a collection.
> 
>    Varrays have a maximum number of elements, although you can change
>    the upper bound. The order of elements is defined. Varrays are stored
>    as opaque objects (that is, raw or BLOB).
> 
>    Nested tables can have any number of elements, and you can select,
>    insert, delete, and so on the same as with regular tables. The order
>    of the elements is not defined. Nested tables are stored in a storage
>    table with every element mapping to a row in the storage table.
> 
> If you need to loop through the elements in order, store only a fixed
> number of items, or retrieve and manipulate the entire collection as a
> value, then use varrays.
> 
> If you need to run efficient queries on collections, handle arbitrary
> numbers of elements, or do mass insert/update/delete operations, then
> use nested tables. If the collections are very large and you want to
> retrieve only subsets, you can model the collection as a nested table
> and retrieve a locator for the result set.
> 
> For example, a purchase order object may have a nested table of line
> items, while a rectangle object may contain a varray with 4 coordinates.
> 
> ```

使用嵌套表选项，Oracle 只是在做一个关系数据库纯粹主义者一开始就会告诉你要做的事情：使用多个表来表示一对多关系。

### 第一范式

如果你看过《The Crucible》，Winona Ryder 扮演 Abigail Wiliams，你会记得以下场景：

> **Abigail:** 我只是上帝的手指，约翰。如果他要谴责伊丽莎白，她将被谴责。反对规范化的论点继续影响从业者。Fabian Pascal 说，这样做代价高昂，揭示了即使自称是该领域专家的人对健全数据库原则的理解不足。这既是 SQL 实现中的一个主要原因，也是技术倒退的结果，比如 ODBMS 和 OLAP，这些问题已经开始困扰 Salem 镇的 SQL DBMS。

离开酒店房间之前，Ryder 女士将您的电影数据库重新设计为第一范式：

电影事实

| 电影 ID | 标题 | 发行年份 | 制片人 | 导演 | 作曲家 | Steadicam 操作员 |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 异形：复活 | 1997 | Bill Badalato | Jean-Pierre Jeunet | John Frizzell | David Emmerichs |
| 2 | 无辜之年 | 1993 | Barbara De Fina | Martin Scorsese | Elmer Bernstein | Larry McConkey |
| 3 | Heathers | 1989 | Denise Di Novi | Michael Lehmann | David Newman | -- |

电影编剧

| 电影 ID | 编剧 |
| --- | --- |
| 1 | 乔斯·惠登 |
| 2 | 伊迪丝·华顿 |
| 2 | 杰伊·考克斯 |
| 2 | 马丁·斯科塞斯 |
| 3 | 丹尼尔·沃特斯 |

### 活动注册

由于你的数据模型异常，导致未能赢得薇诺娜·赖德的青睐，你决定进行全国巡回演讲。你将进行三场不同的讲座：

+   如何在好莱坞追到犹太女孩

+   利用你的 SQL 编程技能在奥斯卡颁奖典礼上获得座位

+   我从薇诺娜·赖德身上学到的规范化知识

这三个讲座将在不同城市举行约 20 次。我们将称特定的讲座为一个*事件*。与其雇佣员工为每场讲座处理注册，不如构建一个基于数据库的 Web 应用程序：

> ```
> -- one row for every different talk that we give
> 
> create table talks (
> 	talk_id		integer primary key,
> 	talk_title	varchar(100) not null,
> 	description	varchar(4000),
> 	speaker_name	varchar(100),
> 	speaker_bio	varchar(4000)
> );
> 
> -- one row for every time that we give a talk
> 
> create table events (
>        event_id		integer primary key,
>        -- which of the three talks will we give
>        talk_id		references talks,
>        -- Location
>        venue_name	varchar(200) not null,
>        street_address	varchar(200) not null,
>        city             varchar(100) not null,
>        -- state if this is in the US
>        usps_abbrev      char(2),
>        -- country code is this is a foreign city
>        iso		char(2) default 'us',
>        -- Date and time
>        start_time	date not null,
>        end_time		date not null,
>        ticket_price	number
> );
> 
> ```

这个数据模型处于第一范式。没有多值列。但是，它存在一些缺陷。假设你飞到纽约市，在三天内分别进行三场讲座。每次你都在同一个地点演讲：Radio City Music Hall。由于`events`表的设计方式，你将会三次记录 Radio City Music Hall 的街道地址。如果街道地址发生变化，你需要在三个地方进行更改。如果你考虑使用一个新的场地，并想输入街道地址、城市和国家代码或州缩写，除非你已经为特定时间安排了一个活动，否则你无处存储这些信息。如果数据库中只有一个特定场地安排的活动，删除该活动也会删除该场地的所有信息。

### 第二范式

如果所有列都对*整个键*具有功能依赖性，数据模型就处于第二范式。不太正式地说，第二范式表是指处于第一范式的表，其键确定了所有非键列的值。

> ```
> -- one row for every different talk that we give
> 
> create table talks (
> 	talk_id		integer primary key,
> 	talk_title	varchar(100) not null,
> 	description	varchar(4000),
> 	speaker_name	varchar(100),
> 	speaker_bio	varchar(4000)
> );
> 
> -- one row for every place where we give a talk
> 
> create table venues (
>        venue_id		integer primary key,
>        venue_name	varchar(200) not null,
>        street_address	varchar(200) not null,
>        city             varchar(100) not null,
>        -- state if this is in the US
>        usps_abbrev      char(2),
>        -- country code
>        iso		char(2) default 'us'
> );
> 
> -- one row for every time that we give a talk
> 
> create table events (
>        event_id		integer primary key,
>        -- which of the three talks will we give
>        talk_id		references talks,
>        -- Location
>        venue_id		references venues,
>        -- Date and time
>        start_time	date not null,
>        end_time		date not null,
>        ticket_price	number
> );
> 
> ```

注意，任何处于第二范式的数据模型也同时符合第一范式。

### 第三范式

如果所有列都*直接*依赖于整个键，数据模型就处于第三范式。这与第二范式有何不同？例如，假设讲座的价格是讲座内容和时长的函数。因此，`start_time` 和 `end_time` 的组合将决定 `ticket_price` 列的值。如果我们再添加一张表，我们的数据模型将处于第三范式：

> ```
> create table ticket_price (
>        up_to_n_minutes	  	integer,
>        price			number
> );
> 
> ```

注意，任何处于第三范式的数据模型也同时符合第二范式。

### 参考

+   [《Access 数据库设计与编程》第四章](http://www.oreilly.com/catalog/accessdata2/chapter/ch04.html)

+   [《Transact-SQL 编程》第一章](http://www.oreilly.com/catalog/wintrnssql/chapter/ch01.html)

下一步：后记

* * *

mbooth@arsdigita.com[philg@mit.edu](http://philip.greenspun.com/)添加评论 | 添加链接
