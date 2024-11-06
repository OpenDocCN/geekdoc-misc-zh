| ![通往梵蒂冈博物馆的圆形楼梯。由乔治·莫莫于 1932 年设计](img/vatican-museum-staircase-4.tcl) |
| --- |

## 数据仓库

SQL for Web Nerds 的一部分，作者是[Philip Greenspun](http://philip.greenspun.com/)。

* * *

![汤姆·亨廷顿在瀑布中。大峡谷国家公园。](img/tom-in-waterfall-41.tcl) 在前面的章节中，你已经不知不觉地沉浸在在线事务处理（OLTP）的世界中。这个世界带有一些假设：

1.  只存储一条信息。如果数据库中有 N 个副本，而你需要更改它，你可能会忘记在所有 N 个地方更改。请注意，只在一个地方存储信息还可以使更新变得快速。

1.  如果查询复杂也没关系，因为它们很少由专业程序员撰写。

1.  绝不要顺序扫描大表；如果 Oracle 执行任何操作需要超过一秒钟的时间，请重新阅读调优章节。

如果要预订订单、向页面添加用户评论、记录点击次数或查看某人是否有权限下载文件，这些都是可以遵循的绝妙规则。

如果你想从数据中获得一些答案，你可能会继续遵循这些规则。写下一份重要的问题清单并构建一些报告页面。你可能需要物化视图来加快这些报告的速度，你的查询可能会很复杂，但你不需要因为业务要求回答一堆问题而离开 OLTP 世界。

为什么有人会离开 OLTP 世界？当你不知道要问什么问题时，数据仓库是有用的。

### 促进探索的含义

![鲍威尔之行的再现。熔岩瀑布。大峡谷国家公园。1999 年 8 月。](img/grand-canyon-powell-reenactment-38.tcl) 只有当非技术人员能够进行数据探索时，数据探索才有用。这意味着技能很弱的人要么撰写查询，要么通过菜单指定查询。你不能让市场执行官查看一个包含 600 个表的数据模型并挑选相关列。你不能让销售员从`customers`和`orders`表的组合中找出“这是一个重复客户还是新客户？”的答案。

如果数据探索环境要有用，它必须满足以下标准：

+   复杂的问题可以通过简单的 SQL 查询来解决

+   不同的问题意味着非常相似的 SQL 查询结构

+   非常不同的问题需要非常相似的处理时间来回答

+   探索可以在任何地方的任何计算机上进行

目标是让业务专家坐在网络浏览器前，使用一系列表单指定查询，并在合理的时间内获得结果。

使用我们标准的 OLTP 数据模型将无法实现这一点。回答一个特定问题可能需要在四五个额外的表中进行连接，这可能导致处理时间增加 10,000 倍。即使一个新手用户可以被引导从 600 个表中选择 7 路连接，但他们无法理解或预测查询处理时间。最后还有一个问题，你是否希望新手查询你的 OLTP 表。如果他们只是输入 SELECT，他们可能不会造成太大的长期伤害，但短期的处理负荷可能导致系统感觉受损。

是时候学习*数据仓库*了。

### 经典零售数据仓库

> "另一个构建自己语言的社会群体是商界。... [商人] 正在说着一种对他来说熟悉而珍贵的语言。它的重要名词和动词赋予普通事件高度冒险性；高管们在墨水橡皮擦中穿行，像骑士一样装饰华丽。我们应该宽容——每个有精神的人都想骑着白马。... 商业中许多专业术语似乎更多地设计用来表达使用者的梦想，而不是表达他的确切含义。"
> 
> -- [《风格要素》](http://www.amazon.com/exec/obidos/ASIN/020530902X/pgreenspun-20) 最后一章，斯特朗克和怀特

让我们想象一场沃尔玛的首席信息官和来自赛贝斯的销售人员之间的对话。我们选择这些公司是为了具体性，但它们代表着“大型管理信息系统（MIS）用户”和“大型关系数据库管理系统（RDBMS）供应商”。

> 沃尔玛：“我想同时跟踪所有商店的销售情况。”
> 
> 赛贝斯：“您需要我们出色的 RDBMS 软件。您可以在收银机结账时将���据存入，同时可以在办公室立即查询数据。这就是并发控制的美妙之处。”

因此，沃尔玛购买了一台价值 100 万美元的 Sun E10000 多 CPU 服务器和一份价值 50 万美元的赛贝斯许可证。他们购买了[《智者的数据库设计》](http://www.amazon.com/exec/obidos/ASIN/1558605150/pgreenspun-20) 并建立了一个规范化的 SQL 数据模型：

> ```
> create table product_categories (
> 	product_category_id	integer primary key,
> 	product_category_name	varchar(100) not null
> );
> 
> create table manufacturers (
> 	manufacturer_id		integer primary key,
> 	manufacturer_name	varchar(100) not null
> );
> 
> create table products (
> 	product_id		integer primary key,
> 	product_name		varchar(100) not null,
> 	product_category_id	references product_categories,
> 	manufacturer_id		references manufacturers
> );
> 
> create table cities (
> 	city_id			integer primary key,
> 	city_name		varchar(100) not null,
> 	state			varchar(100) not null,
> 	population		integer not null
> );
> 
> create table stores (
> 	store_id		integer primary key,
> 	city_id			references cities,
> 	store_location		varchar(200) not null,
> 	phone_number		varchar(20)	
> );
> 
> create table sales (
> 	product_id	not null references products,
> 	store_id	not null references stores,
> 	quantity_sold	integer not null,
> 	-- the Oracle "date" type is precise to the second
> 	-- unlike the ANSI date datatype
> 	date_time_of_sale	date not null
> );
> 
> -- put some data in 
> 
> insert into product_categories values (1, 'toothpaste');
> insert into product_categories values (2, 'soda');
> 
> insert into manufacturers values (68, 'Colgate');
> insert into manufacturers values (5, 'Coca Cola');
> 
> insert into products values (567, 'Colgate Gel Pump 6.4 oz.', 1, 68);
> insert into products values (219, 'Diet Coke 12 oz. can', 2, 5);
> 
> insert into cities values (34, 'San Francisco', 'California', 700000);
> insert into cities values (58, 'East Fishkill', 'New York', 30000);
> 
> insert into stores values (16, 34, '510 Main Street', '415-555-1212');
> insert into stores values (17, 58, '13 Maple Avenue', '914-555-1212');
> 
> insert into sales values (567, 17, 1, to_date('1997-10-22 09:35:14', 'YYYY-MM-DD HH24:MI:SS'));
> insert into sales values (219, 16, 4, to_date('1997-10-22 09:35:14', 'YYYY-MM-DD HH24:MI:SS'));
> insert into sales values (219, 17, 1, to_date('1997-10-22 09:35:17', 'YYYY-MM-DD HH24:MI:SS'));
> 
> -- keep track of which dates are holidays
> -- the presence of a date (all dates will be truncated to midnight)
> -- in this table indicates that it is a holiday
> create table holiday_map (
> holiday_date		date primary key
> );
> 
> -- where the prices are kept
> create table product_prices (
> product_id	not null references products,
> from_date	date not null,
> price		number not null
> );
> 
> insert into product_prices values (567,'1997-01-01',2.75);
> insert into product_prices values (219,'1997-01-01',0.40);
> 
> ```

现在我们有什么？

销售表

| 产品 ID | 商店 ID | 销售数量 | 销售日期/时间 |
| --- | --- | --- | --- |
| 567 | 17 | 1 | 1997-10-22 09:35:14 |
| 219 | 16 | 4 | 1997-10-22 09:35:14 |
| 219 | 17 | 1 | 1997-10-22 09:35:17 |
| ... |

产品表

| 产品 ID | 产品名称 | 产品类别 | 制造商 ID |
| --- | --- | --- | --- |
| 567 | 高露洁凝胶泵 6.4 盎司 | 1 | 68 |
| 219 | 健怡可乐 12 盎司罐装 | 2 | 5 |
| ... |

产品类别表

| 产品类别 ID | 产品类别名称 |
| --- | --- |
| 1 | 牙膏 |
| 2 | 苏打 |
| ... |

制造商表

| 制造商 ID | 制造商名称 |
| --- | --- |
| 68 | 高露洁 |
| 5 | 可口可乐 |
| ... |

商店表

| 店铺 ID | 城市 ID | 店铺位置 | 电话号码 |
| --- | --- | --- | --- |
| 16 | 34 | 主街 510 号 | 415-555-1212 |
| 17 | 58 | 枫树大道 13 号 | 914-555-1212 |
| ... |

城市表

| 城市 ID | 城市名称 | 州 | 人口 |
| --- | --- | --- | --- |
| 34 | 旧金山 | 加利福尼亚 | 700,000 |
| 58 | 伊斯特菲什基尔 | 纽约 | 30,000 |
| ... |

几个月后，一位 WalMart 高管，我们称她为 Jennifer Amolucre，问道：“我注意到最近有一次高露洁促销活动，针对的是居住在小镇的人群。昨天我们在这些小镇上销售了多少高露洁牙膏？一个月前的同一天又销售了多少？”

此时，请反思一下，由于数据模型是规范化的，这些信息无法从扫描一个表中获取。规范化的数据模型是指行中的所有信息仅依赖于主键。例如，城市人口不包含在`stores`表中。这些信息仅在`cities`表中每个城市存储一次，而`stores`表中仅保留`city_id`。这确保了事务处理的效率。如果 Walmart 需要更新一个城市的人口，只需触及磁盘上的一个记录。随着计算机变得更快，更有趣的是这种方法的一致性。只有将城市人口保存在一个地方，就不会有更新应用于某些记录而不应用于其他记录的风险。如果同一城市有多家商店，那么所有商店的人口将始终从同一个位置提取。

Amolucre 女士的查询将类似于这样...

> ```
>  select sum(sales.quantity_sold) from sales, products, product_categories, manufacturers, stores, cities where manufacturer_name = 'Colgate' and product_category_name = 'toothpaste' and cities.population < 40000 and trunc(sales.date_time_of_sale) = trunc(sysdate-1) -- restrict to yesterday and sales.product_id = products.product_id and sales.store_id = stores.store_id and products.product_category_id = product_categories.product_category_id and products.manufacturer_id = manufacturers.manufacturer_id and stores.city_id = cities.city_id; 
> 
> ```

对于一个新手来说，这个查询可能很难阅读，并且由于是对一些相当大的表进行 6 路连接，执行起来可能需要相当长的时间。此外，这些表在执行 Amolucre 女士的查询时正在更新。

就在 Jennifer Amolucre 寻求市场信息的任务建立之后，店铺员工注意到一天中有时无法为顾客结账。任何尝试更新数据库都会导致计算机在 20 分钟内冻结。最终，数据库管理员意识到每次运行 Amolucre 女士的牙膏查询时系统都会崩溃。他们向 Sybase 技术支持投诉。

> Walmart：“我们输入牙膏查询，我们的系统卡住了。”
> 
> Sybase：“当然会！你建立了一个在线事务处理（OLTP）系统。你不能输入一个决策支持系统（DSS）查询然后期望一切正常运行！”
> 
> Walmart：“但我以为 SQL 和你们的关系型数据库管理系统的整个重点是用户可以同时查询和插入。”
> 
> Sybase：“嗯，并不完全是这样。如果你从数据库中读取数据，那么没有人可以向数据库写入数据。如果你向数据库写入数据，那么没有人可以从数据库中读取数据。因此，如果你有一个需要运行 20 分钟的查询，并且没有指定特殊的锁定指令，那么在这 20 分钟���没有人可以更新这些表。”
> 
> Walmart：“听起来像是一个 bug。”
> 
> Sybase：“实际上这是一个特性。我们称之为*悲观锁定*。”
> 
> Walmart：“你能修复你的系统，使其不会锁死吗？”
> 
> Sybase：“不行。但我们制作了这个很棒的加载工具，让你可以以每小时 100 GB 的速度将所有数据从你的 OLTP 系统复制到一个单独的 DSS 系统。”

由于你正在阅读这本书，你可能正在使用 Oracle，这是少数几个通过版本控制而不是锁定实现并发用户一致性的数据库管理系统之一（另一个显著的例子是免费开源的 PostgreSQL RDBMS）。然而，即使你正在使用 Oracle，在那里读者永远不用等待写入者，写入者也永远不用等待读者，你可能仍然不希望在市场人员输入昂贵查询时使事务处理操作变慢。

基本上 IT 供应商希望 Walmart 建立另一个 RDBMS 安装在另一台计算机上。Walmart 需要购买另外 100 万美元的计算机硬件。他们需要购买另一个 RDBMS 许可证。他们还需要雇佣程序员确保每晚将 OLTP 数据复制并填充到 DSS 系统中——*数据提取*。Walmart 现在正在建立*数据仓库*。

### 洞察 1

数据仓库是一个单独的 RDBMS 安装，其中包含来自在线系统的数据副本。如果你有大量额外的计算能力，物理上分离的数据仓库并不是绝对必要的。使用乐观锁定的数据库管理系统，你甚至可能只需保留一份数据副本。

### 只要我们在复制……

只要你从 OLTP 系统复制数据到 DSS 系统（“数据仓库”），你可以考虑为更快的检索组织和索引数据。在生产表上添加额外的索引是不好的，因为它们会减慢插入和更新速度。每次向表中添加或修改一行时，关系数据库管理系统都必须更新索引以保持一致。但在数据仓库中，数据是静态的。你只需构建一次索引，它们占用空间，有时会加快查询速度，就是这样。

如果你知道 Jennifer Amolucre 每天都会执行牙膏查询，你可以为她冗余化数据模型。例如，如果你向 `stores` 表添加一个 `town_population` 列，并从 `cities` 表复制数据，你会牺牲一些数据模型的清洁度，但现在 Amolucre 女士的查询只需要进行 5 次连接。如果你向 `sales` 表添加 `manufacturer` 和 `product_category` 列，你就不需要在 `products` 表中进行连接。

### 冗余化何时结束？

一旦你放弃了数据仓库中的数据模型需要与 OLTP 系统中的数据模型有些相似的观念，你就开始考虑进一步重新组织数据模型的问题。记住，我们试图确保具有有限 SQL 经验的人可以提出新问题，即许多不同的问题可以用形态上相似的 SQL 来回答。理想情况下，构建 SQL 查询的任务应该被简化到可以从菜单系统中完成。此外，我们正在努力提供可预测的响应时间。对问题进行轻微修改不应该导致系统响应时间增加千倍。

OLTP 数据模型的不可简化问题在于对新手来说构建查询很困难。鉴于计算机系统并非无限快速，一个实际的问题是，对 OLTP 表的查询响应时间会以新手无法预测的方式变化。

比如说，Bill Novice 想要查看 OLTP 模型上的节假日与非节假日的销售情况。Bill 需要去查看数据模型，而在一个生产系统上，数据模型会包含数百个表，以找出其中是否有任何表包含日期是否是节假日的信息。然后他需要在查询中使用它，这对于 Oracle `date` 数据类型的特殊性来说并不明显：

> ```
> select sum(sales.quantity_sold) 
> from sales, holiday_map
> where trunc(sales.date_time_of_sale) = trunc(holiday_map.holiday_date)
> 
> ```

那个问题相当简单，因为 JOIN 到 `holiday_map` 表会剔除不是节假日的日期的销售。要与非节假日的销售进行比较，他将需要想出一个不同的查询策略，一个剔除了节假日销售的策略。以下是一种方式：

> ```
> select sum(sales.quantity_sold) 
> from sales
> where trunc(sales.date_time_of_sale) 
> not in
> (select holiday_date from holiday_map)
> 
> ```

请注意，这个查询的形态（结构）与询问节假日销售的完全不同。

现在假设 Bill 感兴趣的是那些总体销售额 tended to be high 的商店的单位销售量。首先，Bill 必须试验一种方法来询问数据库中的大卖店。可能这将涉及到按 `store_id` 列对 `sales` 表进行分组：

> ```
> select store_id 
> from sales
> group by store_id
> having sum(quantity_sold) > 1000
> 
> ```

现在我们知道如何找到总销售量超过 1000 个单位的商店，所以我们可以将此作为子查询添加：

> ```
> select sum(quantity_sold) 
> from sales
> where store_id in
> (select store_id 
>  from sales
>  group by store_id
>  having sum(quantity_sold) > 1000)
> 
> ```

从形态学上看，这与前面的非假日查询并没有太大的不同。比尔不得不弄清楚如何使用 GROUP BY 和 HAVING 结构，但除此之外，这是一个带有子查询的单表查询。然而，请考虑执行时间。`sales`表可能包含数百万行。`holiday_map`表可能只包含 50 或 100 行，这取决于 OLTP 系统运行了多长时间。执行这些子查询最明显的方法将是对主查询检查的每一行执行子查询。在“大商店”查询的情况下，子查询需要扫描和排序整个`sales`表。因此，执行此查询的时间可能比执行“非假日销售”查询的时间长 10,000 倍。比尔·新手应该期望这种行为吗？他是否应该考虑这个问题？OLTP 系统是否会因为他没有认真考虑而停滞不前？

几乎所有试图增加决策支持查询之间相似性和可预测性的组织最终都会拥有一个*维度数据仓库*。这需要一个与 OLTP 数据模型几乎没有关联的新数据模型。

### 维度数据建模：第一步

维度数据建模始于一个*事实表*。这是我们记录发生了什么的地方，例如，有人在 East Fishkill 购买了一罐 Diet Coke。在事实表中，我们想要的是关于销售的事实，理想情况下是数值的、连续值的和可加的。最后两个属性很重要，因为典型的事实表会增长到十亿行或更多。人们看到总和或平均值会比看细节更开心。一个重要的决定是确定事实表的粒度。如果沃尔玛不在乎 Diet Coke 是在上午 10:31 还是上午 10:33 卖出的，那么在事实表中单独记录每次销售就太细粒度了。CPU 时间、磁盘带宽和磁盘空间将被不必要地消耗。让我们按照每天在一个商店中销售任何特定产品的方式进行聚合。因此，我们只会在事实表中记录一行，记录在 11 月 30 日在 East Fishkill 销售了 200 罐 Diet Coke，即使这 200 罐是在 113 个不同的时间卖给 113 个不同的顾客。

> ```
> create table sales_fact (
> 	sales_date	date not null,
> 	product_id	integer,
> 	store_id	integer,
> 	unit_sales	integer,
> 	dollar_sales	number
> );
> 
> ```

到目前为止，我们可以通过查询将`sales`、`products`和`product_prices`（用于填充`dollar_sales`列）表 JOIN 在一起，从而组合出这个表格。这个 JOIN 将按照`product_id`、`store_id`和截断的`date_time_of_sale`进行分组。构建这个查询将需要一名专业的程序员，但请记住，这项工作只需要做一次。将使用数据仓库的营销专家将从`sales_fact`表中查询。

仅构建这个表，我们已经让市场营销变得更容易。假设他们想要按产品总销售额。在 OLTP 数据模型中，这将需要与`product_prices`表以及不同日期相同产品的不同价格纠缠。有了销售事实表，查询很简单：

> ```
> select product_id, sum(dollar_sales)
> from sales_fact
> group by product_id
> 
> ```

我们有一个*事实表*。在维度数据仓库中，总是只有一个这样的表。所有其他表都定义了*维度*。每个维度包含有关事实的额外信息，通常是可以直接放入报告的人类可读的文本字符串。例如，让我们定义时间维度：

> ```
> create table time_dimension (
> 	time_key		integer primary key,
> 	-- just to make it a little easier to work with; this is 
> 	-- midnight (TRUNC) of the date in question
> 	oracle_date		date not null,
> 	day_of_week		varchar(9) not null, -- 'Monday', 'Tuesday'...
> 	day_number_in_month	integer not null, -- 1 to 31
> 	day_number_overall	integer not null, -- days from the epoch (first day is 1)
> 	week_number_in_year	integer not null, -- 1 to 52
> 	week_number_overall	integer not null, -- weeks start on Sunday
> 	month			integer not null, -- 1 to 12
> 	month_number_overall	integer not null,
> 	quarter			integer not null, -- 1 to 4
> 	fiscal_period		varchar(10),
> 	holiday_flag		char(1) default 'f' check (holiday_flag in ('t', 'f')),
> 	weekday_flag		char(1) default 'f' check (weekday_flag in ('t', 'f')),
> 	season			varchar(50),
> 	event			varchar(50)
> );
> 
> ```

为什么定义时间维度很有用？如果我们将销售事实的日期保留为 Oracle 日期列，要询问节假日与非节假日销售情况仍然很痛苦。我们需要了解`holiday_map`表的存在以及如何使用它。假设我们重新定义事实表如下：

> ```
> create table sales_fact (
> 	time_key integer not null references time_dimension,
> 	product_id	integer,
> 	store_id	integer,
> 	unit_sales	integer,
> 	dollar_sales	number
> );
> 
> ```

不再在事实表中存储 Oracle 日期，而是保留一个指向时间维度条目的整数键。时间维度存储每天的以下信息：

+   这一天是否是假日

+   这一天属于哪个财政期间

+   这一天是否属于"圣诞季节"或不属于

如果我们想要按季节报告销售情况，查询很简单：

> ```
> select td.season, sum(f.dollar_sales)
> from sales_fact f, time_dimension td
> where f.time_key = td.time_key
> group by td.season
> 
> ```

如果我们想要按财季报告销售额或按星期几报告销售额，SQL 结构与上述相同。然而，如果我们想要按制造商报告销售额，我们意识到我们需要另一个维度：*产品*。不要存储引用 OLTP `products`表的`product_id`，最好使用引用产品维度的合成产品键，其中来自 OLTP `products`、`product_categories`和`manufacturers`表的数据被聚合。

由于我们是沃尔玛，一个多店铺连锁店，我们会想要一个*商店*维度。这个表将从 OLTP 系统中的`stores`和`cities`表中聚合信息。以下是我们如何在 Oracle 表中定义商店维度：

> ```
> create table stores_dimension (
> 	stores_key		integer primary key,
> 	name			varchar(100),
> 	city			varchar(100),
> 	county			varchar(100),
> 	state			varchar(100),
> 	zip_code		varchar(100),
> 	date_opened		date,
> 	date_remodeled		date,
> 	-- 'small', 'medium', 'large', or 'super'
> 	store_size		varchar(100),
> 	...
> );
> 
> ```

这个新维度让我们有机会比较大型商店与小型商店、新旧商店以及不同地区商店的销售情况。我们可以按地理区域聚合销售额，从州一级开始，逐渐深入到县、城市或邮政编码。以下是我们如何按城市查询销售额：

> ```
> select sd.city, sum(f.dollar_sales)
> from sales_fact f, stores_dimension sd
> where f.stores_key = sd.stores_key
> group by sd.city
> 
> ```

维度可以组合。要按季度报告城市销售情况，我们将使用以下查询：

> ```
> select sd.city, td.fiscal_period, sum(f.dollar_sales)
> from sales_fact f, stores_dimension sd, time_dimension td
> where f.stores_key = sd.stores_key
> and f.time_key = td.time_key
> group by sd.stores_key, td.fiscal_period
> 
> ```

（与上一个查询相比额外的 SQL 显示为粗体）。

通用沃尔玛式数据仓库中的最终维度是*促销*。营销人员希望知道降价提高了销售额多少，提高了多少销售额是永久的，以及促销产品在同一商店销售的其他产品中占据了多少份额。促销维度表中的列将包括促销类型（优惠券或销售价格）、广告的全面信息（广告类型、出版物名称、出版物类型）、店内展示的全面信息、促销成本等。

此时值得退一步看看，注意到数据仓库包含的信息比 OLTP 系统少，但实际上更有用，因为查询更容易构建且执行速度更快。设计一个好的数据仓库的大部分艺术在于定义维度。日常业务的哪些方面可以压缩和以块的形式处理？业务的哪些方面是有趣的？

### 真实案例：Levis Strauss 的数据仓库

1998 年，ArsDigita 公司建立了一个网络服务，作为 Levi Strauss 经营的一个实验性定制服装工厂的前端。用户会访问我们的网站，选择一种卡其裤的款式，输入腰围、内长、身高、体重和鞋码，最后用信用卡结账。我们的服务器将尝试通过 CyberCash 对信用卡进行授权。工厂 IT 系统会定期轮询我们服务器的 Oracle 数据库，以便在成功授权订单后的 10 分钟内开始裁剪裤子。

工厂和网络服务的整个目的是测试和分析消费者对这种购买服装方式的反应。因此，几乎从一开始就将数据仓库建立到项目中。

我们没有购买任何额外的硬件或软件来支持数据仓库。公共网站由一台中档的惠普 Unix 服务器支持，该服务器有足够的剩余容量来运行数据仓库。我们创建了一个新的“dw”Oracle 用户，将 OLTP 表上的 SELECT 授权给“dw”用户，并编写了程序将所有数据从 OLTP 系统复制到由“dw”用户拥有的星型模式表中。对于查询，我们向机器添加了一个 IP 地址，并运行了绑定到该第二 IP 地址的 Web 服务器程序。

这就是我们向客户（Levi Strauss）解释我们的工程决策的方式：

> ```
> We employ a standard star join schema for the following reasons:
> 
> * Many relational database management systems, including Oracle 8.1,
> are heavily optimized to execute queries against these schemata.
> 
> * This kind of schema has been proven to scale to the world's
> largest data warehouses.
> 
> * If we hired a data warehousing nerd off the street, he or she
> would have no trouble understanding our schema.
> 
> In a star join schema, there is one fact table ("we sold a pair of
> khakis at 1:23 pm to Joe Smith") that references a bunch of dimension
> tables.  As a general rule, if we're going to narrow our interest
> based on a column, it should be in the dimension table.  I.e., if
> we're only looking at sales of grey dressy fabric khakis, we should
> expect to accomplish that with WHERE clauses on columns of a product
> dimension table.  By contrast, if we're going to be aggregating
> information with a SUM or AVG command, these data should be stored in
> the columns of the fact table.  For example, the dollar amount of the
> sale should be stored within the fact table.  Since we have so few
> prices (essentially only one), you might think that this should go in
> a dimension.  However, by keeping it in the fact table we're more
> consistent with traditional data warehouses.
> 
> ```

在与 Levi's 高管进行一些讨论后，我们设计了以下维度表：

+   **时间**

    用于比较销售按季节、季度或假日

+   **产品**

    用于比较销售按颜色或风格

+   **运送至**

    用于比较按区域或州销售的查询

+   **促销**

    用于确定折扣与销售之间关系的查询

+   **消费者**

    用于比较首次购买和重复购买者的销售查询

+   **用户体验**

    对于查询返回、交换和接受商品的情况（与其他维度结合使用时最有用，例如，特定颜色更可能导致交换请求）

这些维度使我们能够回答诸如

+   在国家的哪些地区，褶皱裤最受欢迎？（事实表与产品和收货维度连接）

+   有多少裤子是用优惠券购买的，这种情况每个季度如何变化？（事实表与促销和时间维度连接）

+   假日和非假日分别销售了多少裤子？（事实表与时间维度连接）

#### 维度表

`time_dimension`表与上面给出的示例相同。

> ```
> create table time_dimension (
> 	time_key		integer primary key,
> 	-- just to make it a little easier to work with; this is 
> 	-- midnight (TRUNC) of the date in question
> 	oracle_date		date not null,
> 	day_of_week		varchar(9) not null, -- 'Monday', 'Tuesday'...
> 	day_number_in_month	integer not null, -- 1 to 31
> 	day_number_overall	integer not null, -- days from the epoch (first day is 1)
> 	week_number_in_year	integer not null, -- 1 to 52
> 	week_number_overall	integer not null, -- weeks start on Sunday
> 	month			integer not null, -- 1 to 12
> 	month_number_overall	integer not null,
> 	quarter			integer not null, -- 1 to 4
> 	fiscal_period		varchar(10),
> 	holiday_flag		char(1) default 'f' check (holiday_flag in ('t', 'f')),
> 	weekday_flag		char(1) default 'f' check (weekday_flag in ('t', 'f')),
> 	season			varchar(50),
> 	event			varchar(50)
> );
> 
> ```

我们使用单个 INSERT 语句填充了`time_dimension`表。核心工作由 Oracle 日期格式化函数完成。一个辅助表`integers`用于提供一系列数字，以添加到起始日期（我们选择了 1998 年 7 月 1 日，比我们的第一个真实订单早几天）。

> ```
> -- Uses the integers table to drive the insertion, which just contains
> -- a set of integers, from 0 to n.
> -- The 'epoch' is hardcoded here as July 1, 1998.
> 
> -- d below is the Oracle date of the day we're inserting.
> insert into time_dimension
> (time_key, oracle_date, day_of_week, day_number_in_month, 
>  day_number_overall, week_number_in_year, week_number_overall,
>  month, month_number_overall, quarter, weekday_flag)
> select n, d, rtrim(to_char(d, 'Day')), to_char(d, 'DD'), n + 1,
>        to_char(d, 'WW'),
>        trunc((n + 3) / 7), -- July 1, 1998 was a Wednesday, so +3 to get the week numbers to line up with the week
>        to_char(d, 'MM'), trunc(months_between(d, '1998-07-01') + 1),
>        to_char(d, 'Q'), decode(to_char(d, 'D'), '1', 'f', '7', 'f', 't')
> from (select n, to_date('1998-07-01', 'YYYY-MM-DD') + n as d
>       from integers);
> 
> ```

记住你在日期章节学到的 Oracle 日期细节。如果您向 Oracle 日期添加一个数字，您将得到另一个 Oracle 日期。因此，将 3 添加到“1998-07-01”将得到“1998-07-04”。

还有几个字段需要填充，我们无法使用 Oracle 日期函数推导出来：季节、财政期、假日标志、事件。财政期取决于李维斯选择的财政年度。`event`列被保留用于李维斯营销团队特别感兴趣的任意时间段，例如，促销期。实际上，它没有被使用。

要更新`holiday_flag`字段，我们使用了两个辅助表，一个用于“固定”假日（每年同一天发生的假日），另一个用于“浮动”假日（日期会变动的假日）。

> ```
> create table fixed_holidays (
> 	month			integer not null check (month >= 1 and month <= 12),="" day="" integer="" not="" null="" check="" (day="">= 1 and day <= 31),="" name="" varchar(100)="" not="" null,="" primary="" key="" (month,="" day)="" );="" --="" specifies="" holidays="" that="" fall="" on="" the="" nth="" day_of_week="" in="" month.="" negative="" means="" count="" backwards="" from="" end.="" create="" table="" floating_holidays="" (="" month="" integer="" null="" check="" (month="">= 1 and month <= 12),="" day_of_week="" varchar(9)="" not="" null,="" nth="" integer="" name="" varchar(100)="" primary="" key="" (month,="" day_of_week,="" nth)="" );="" <="" pre="">
> ```

一些例假日：

> ```
> insert into fixed_holidays (name, month, day) 
>    values ('New Year''s Day', 1, 1);
> insert into fixed_holidays (name, month, day)
>    values ('Christmas', 12, 25);
> insert into fixed_holidays (name, month, day)
>    values ('Veteran''s Day', 11, 11);
> insert into fixed_holidays (name, month, day)
>    values ('Independence Day', 7, 4);
> 
> insert into floating_holidays (month, day_of_week, nth, name)
>    values (1, 'Monday', 3, 'Martin Luther King Day');
> insert into floating_holidays (month, day_of_week, nth, name)
>    values (10, 'Monday', 2, 'Columbus Day');
> insert into floating_holidays (month, day_of_week, nth, name)
>    values (11, 'Thursday', 4, 'Thanksgiving');
> insert into floating_holidays (month, day_of_week, nth, name)
>    values (2, 'Monday', 3, 'President''s Day');
> insert into floating_holidays (month, day_of_week, nth, name)
>    values (9, 'Monday', 1, 'Labor Day');
> insert into floating_holidays (month, day_of_week, nth, name)
>    values (5, 'Monday', -1, 'Memorial Day');
> 
> ```

一个极其聪明的人，最近阅读了[SQL for Smarties](http://www.amazon.com/exec/obidos/ASIN/1558605762/pgreenspun-20)，可能能够想出一个 SQL 语句来更新`time_dimension`行中的`holiday_flag`。然而，没有必要让你的大脑如此努力工作。请记住，Oracle 包含两种过程语言，Java 和 PL/SQL。您可以在您选择的过程语言中实现以下伪代码：

> ```
> foreach row in "select name, month, day from fixed_holidays"
>     update time_dimension 
>       set holiday_flag = 't'
>       where month = row.month and day_number_in_month = row.day;
> end foreach
> 
> foreach row in "select month, day_of_week, nth, name from floating_holidays"
>     if row.nth > 0 then
> 	# If nth is positive, put together a date range constraint
>         # to pick out the right week.
>         ending_day_of_month := row.nth * 7
>         starting_day_of_month := ending_day_of_month - 6
> 
> 	update time_dimension
>           set holiday_flag = 't'
>           where month = row.month
>             and day_of_week = row.day_of_week
>             and starting_day_of_month <= day_number_in_month
>             and day_number_in_month <= ending_day_of_month;
>     else
> 	# If it is negative, get all the available dates 
>         # and get the nth one from the end.
>         i := 0;
>         foreach row2 in "select day_number_in_month from time_dimension
>                          where month = row.month
>                            and day_of_week = row.day_of_week
>                          order by day_number_in_month desc"
>             i := i - 1;
>             if i = row.nth then
>                 update time_dimension 
>                   set holiday_flag = 't' 
>                   where month = row.month
>                     and day_number_in_month = row2.day_number_in_month
>                 break;
>             end if
>         end foreach
>     end if
> end foreach	
> 
> ```

##### 产品维度产品维度包含每种颜色、款式、袖口、褶皱等唯一组合的一行。

> ```
> create table product_dimension ( 
> 	product_key     integer primary key, 
> 	-- right now this will always be "ikhakis" 
> 	product_type    varchar(20) not null, 
> 	-- could be "men", "women", "kids", "unisex adults" 
> 	expected_consumers      varchar(20), 
> 	color           varchar(20), 
> 	-- "dressy" or "casual" 
> 	fabric          varchar(20), 
> 	-- "cuffed" or "hemmed" for pants 
> 	-- null for stuff where it doesn't matter 
> 	cuff_state      varchar(20), 
> 	-- "pleated" or "plain front" for pants 
> 	pleat_state     varchar(20) 
> );
> 
> ```

为了填充这个维度，我们为维度表中的每个字段创建了一个单列表，并使用没有 WHERE 子句的多表连接。这会生成每个字段所有可能值的笛卡尔积：

> ```
> create table t1 (expected_consumers varchar(20));
> create table t2 (color varchar(20));
> create table t3 (fabric varchar(20));
> create table t4 (cuff_state varchar(20));
> create table t5 (pleat_state varchar(20));
> 
> insert into t1 values ('men');
> insert into t1 values ('women');
> insert into t1 values ('kids');
> insert into t1 values ('unisex');
> insert into t1 values ('adults');
> [etc.]
> 
> insert into product_dimension
> (product_key, product_type, expected_consumers, 
> color, fabric, cuff_state, pleat_state)
> select 
>   product_key_sequence.nextval, 
>   'ikhakis',
>   t1.expected_consumers, 
>   t2.color, 
>   t3.fabric,
>   t4.cuff_state, 
>   t5.pleat_state
> from t1,t2,t3,t4,t5;
> 
> ```

注意，Oracle 序列`product_key_sequence`用于为每行生成唯一的整数键，当它被插入维度时。

##### 促销维度 促销维度的构建艺术是将优惠券的世界划分为广泛的类别，例如，“10 到 20 美元之间”。这种分类取决于市场执行人员并不在乎 3.50 美元和 3.75 美元优惠券之间的差异的学习。

> ```
> create table promotion_dimension ( 
> 	promotion_key           integer primary key, 
> 	-- can be "coupon" or "no coupon" 
> 	coupon_state            varchar(20), 
> 	-- a text string such as "under $10" 
> 	coupon_range            varchar(20) 
> ); 
> 
> ```

单独的`coupon_state`和`coupon_range`列允许将销售数据报告分解为全价/折扣或一堆行，每行代表一个优惠券大小范围。

##### 消费者维度 我们对客户的人口统计数据没有太多访问权限。由于这是一个新服务，我们没有太多历史。因此，我们的消费者维度非常简单。它用于记录事实表中的销售是向新客户还是向重复客户。

> ```
> create table consumer_dimension (
> 	consumer_key            integer primary key,
> 	-- 'new customer' or 'repeat customer'
> 	repeat_class            varchar(20)
> );
> 
> ```

##### 用户体验维度 如果我们有兴趣构建一个关于考虑购买的平均时间与最终是否保留购买的报告，`user_experience_dimension`表将有所帮助。

> ```
> create table user_experience_dimension ( 
> 	user_experience_key     integer primary key, 
> 	-- 'shipped on time', 'shipped late' 
> 	on_time_status          varchar(20), 
> 	-- 'kept', 'returned for exchange', 'returned for refund' 
> 	returned_status         varchar(30) 
> ); 
> 
> ```

##### 收货维度 在数据仓库中经典的最强大的维度之一，我们的`ship_to_dimension`表允许我们按地区或州分组销售。

> ```
> create table ship_to_dimension ( 
> 	ship_to_key     integer primary key, 
> 	-- e.g., Northeast 
> 	ship_to_region  varchar(30) not null, 
> 	ship_to_state   char(2) not null 
> ); 
> 
> create table state_regions ( 
> 	state           char(2) not null primary key, 
> 	region          varchar(50) not null 
> ); 
> 
> -- to populate: 
> insert into ship_to_dimension
> (ship_to_key, ship_to_region, ship_to_state) 
> select ship_to_key_sequence.nextval, region, state 
> from state_regions; 
> 
> ```

请注意，我们在这里抛弃了大量细节。如果这是一款针对 Levi Strauss 的全面产品，他们可能会希望至少为县、城市和邮政编码添加额外的列。这些列将允许区域销售经理查看州内的销售情况。

（在制造批发商的数据仓库中，收货维度将包含客户公司名称、接收物品的客户公司的部门、销售订单的销售人员的销售区等列。）

#### 事实表

我们事实表的粒度是一个订单。这比上面介绍的经典的沃尔玛风格数据仓库更精细，那里的事实是在一天内在一个商店销售的特定 SKU 的数量（即，同一物品在一天内的所有订单被聚合）。我们决定这样做是因为 1998 年数据仓库业务中的常识是，高达十亿行的事实表是可以管理的。我们的零售价格是 40 美元，很难预见工厂一天能生产超过 1000 条裤子。因此，每个订单预算一行似乎并不奢侈。

鉴于这个项目的实验性质，我们没有自欺欺人地认为我们第一次就能做对。由于我们记录了每个订单一行，我们能够通过在数据仓库中包含指向 OLTP 数据库的指针：`order_id`和`consumer_id`来作弊。我们从未使用过这些，但知道如果我们无法为市场执行人员提供所需的答案，代价将是一些定制的 SQL 编码，而不是重建整个数据仓库。

> ```
> create table sales_fact ( 
> 	-- keys over to the OLTP production database 
> 	order_id                integer primary key, 
> 	consumer_id             integer not null, 
> 	time_key                not null references time_dimension, 
> 	product_key             not null references product_dimension, 
> 	promotion_key           not null references promotion_dimension, 
> 	consumer_key            not null references consumer_dimension, 
> 	user_experience_key     not null references user_experience_dimension, 
> 	ship_to_key             not null references ship_to_dimension, 
> 	-- time stuff 
> 	minutes_login_to_order          number, 
> 	days_first_invite_to_order      number, 
> 	days_order_to_shipment          number, 
> 	-- this will be NULL normally (unless order was returned) 
> 	days_shipment_to_intent         number, 
> 	pants_id                integer, 
> 	price_charged           number, 
> 	tax_charged             number, 
> 	shipping_charged        number 
> );
> 
> ```

定义了事实表后，我们用一个单独的插入语句填充了它：

> ```
> -- find_product, find_promotion, find_consumer, and find_user_experience
> -- are PL/SQL procedures that return the appropriate key from the dimension
> -- tables for a given set of parameters
> 
> insert into sales_fact 
>  select o.order_id, o.consumer_id, td.time_key,  
>         find_product(o.color, o.casual_p, o.cuff_p, o.pleat_p),  
>         find_promotion(o.coupon_id),  
>         find_consumer(o.pants_id),  
>         find_user_experience(o.order_state, o.confirmed_date, o.shipped_date),
>         std.ship_to_key, 
>         minutes_login_to_order(o.order_id, usom.user_session_id),  
>         decode(sign(o.confirmed_date - gt.issue_date), -1, null, round(o.confirmed_date - gt.issue_date, 6)),  
>         round(o.shipped_date - o.confirmed_date, 6),  
>         round(o.intent_date - o.shipped_date, 6), 
>         o.pants_id, o.price_charged, o.tax_charged, o.shipping_charged 
>  from khaki.reportable_orders o, ship_to_dimension std,  
>       khaki.user_session_order_map usom, time_dimension td,  
>       khaki.addresses a, khaki.golden_tickets gt 
>  where o.shipping = a.address_id 
>         and std.ship_to_state = a.usps_abbrev 
>         and o.order_id = usom.order_id(+) 
>         and trunc(o.confirmed_date) = td.oracle_date 
>         and o.consumer_id = gt.consumer_id; 
> 
> ```

正如顶部的注释所指出的，这里的大部分工作是由 PL/SQL 过程完成的，比如`find_product`，它会在维度表中找到适合这个特定订单的正确行。

前面的插入将从在线事务处理系统的表中加载一个空的数据仓库。保持数据仓库与 OLTP 领域中发生的事情保持同步需要类似的带有额外限制 WHERE 子句的 INSERT，限制订单仅为那些订单 ID 大于当前数据仓库中订单 ID 的最大值的订单。这是一个安全的事务，可以根据需要每天执行多次--即使同时进行两个 INSERT 也不会因为`order_id`上的主键约束而使数据仓库出现重复行。在数据仓库世界中，每天更新一次是传统的，所以我们使用 Oracle 的`dbms_job`包安排了每 24 小时进行一次更新（[`www.oradoc.com/ora816/server.816/a76956/jobq.htm#750`](http://www.oradoc.com/ora816/server.816/a76956/jobq.htm#750)）。

#### 示例查询

我们已经（1）定义了星型模式，（2）填充了维度表，（3）加载了事实表，并（4）安排了定期更新事实表。现在我们可以继续进行数据仓库的有趣部分：获取信息。

仅使用`sales_fact`表，我们可以询问

+   订单总数，迄今为止的总收入，已支付的税款，迄今为止的运输成本，每个售出物品的平均售价，以及平均发货天数：

    > ```
    > select count(*) as n_orders,
    >        round(sum(price_charged)) as total_revenue,
    >        round(sum(tax_charged)) as total_tax,
    >        round(sum(shipping_charged)) as total_shipping,
    >        round(avg(price_charged),2) as avg_price,
    >        round(avg(days_order_to_shipment),2) as avg_days_to_ship 
    > from sales_fact;
    > 
    > ```

+   从登录到订单的平均分钟数（我们排除了持续时间超过 30 分钟的用户会话，以避免由于中断购物会话去吃午餐或睡几个小时而使结果产生偏差）：

    > ```
    > select round(avg(minutes_login_to_order), 2)
    > from sales_fact
    > where minutes_login_to_order < 30
    > 
    > ```

+   从首次通过电子邮件被邀请到网站到第一笔订单的平均天数（排除超过 2 周的时间段以消除异常值）：

    > ```
    > select round(avg(days_first_invite_to_order), 2)
    > from sales_fact
    > where days_first_invite_to_order < 14
    > 
    > ```

与`ship_to_dimension`表连接，让我们询问有多少裤子被运送到美国各地区：

> ```
> select ship_to_region, count(*) as n_pants 
> from sales_fact f, ship_to_dimension s 
> where f.ship_to_key = s.ship_to_key 
> group by ship_to_region 
> order by n_pants desc
> 
> ```
> 
> | 地区 | 售出裤子数 |
> | --- | --- |
> | 新英格兰地区 |   612 |
> | 纽约和新泽西地区 |   321 |
> | 中大西洋地区 |   318 |
> | 西部地区 |   288 |
> | 东南地区 |   282 |
> | 南部地区 |   193 |
> | 大湖地区 |   177 |
> | 西北地区 |   159 |
> | 中部地区 |   134 |
> | 北中部地区 |   121 |

注意：这些数据基于来自 Levi's 网站的随机订单子集，并且我们还对报告数值进行了手动更改。这些数字在这里是为了让您了解这些查询的作用，而不是为了深入了解 Levi's 定制服装业务。

通过与`time_dimension`连接，我们可以询问每周每天售出多少裤子：

> ```
> select day_of_week, count(*) as n_pants 
> from sales_fact f, time_dimension t 
> where f.time_key = t.time_key 
> group by day_of_week 
> order by n_pants desc
> 
> ```
> 
> | 星期几 | 售出裤子数 |
> | --- | --- |
> | 星期四 |   3428 |
> | 星期三 |   2823 |
> | 星期二 |   2780 |
> | 星期一 |   2571 |
> | 星期五 |   2499 |
> | 星期六 |   1165 |
> | 星期日 |   814 |

我们可以用"时尚"或"休闲"面料制作裤子。与`product_dimension`表连接可以告诉我们每种选项在颜色方面的受欢迎程度：

> ```
> select color, count(*) as n_pants, sum(decode(fabric,'dressy',1,0)) as n_dressy 
> from sales_fact f, product_dimension p 
> where f.product_key = p.product_key 
> group by color 
> order by n_pants desc
> 
> ```
> 
> | 颜色 | 售出裤子 |   % 时尚 |
> | --- | --- | --- |
> | 深黄褐 |   486 |   100 |
> | 浅黄褐 |   305 |   49 |
> | 深灰 |   243 |   100 |
> | 黑色 |   225 |   97 |
> | 海军蓝 |   218 |   61 |
> | 中黄褐 |   209 |   0 |
> | 橄榄绿 |   179 |   63 |

注：100%和 0%表示这些颜色只有一种面料可用。

这是数据仓库如何导致实际结果的一个很好案例。如果这些是来自 Levi's 仓库的真实数字，那么制造人员会发现，97%的黑色裤子销售量都是同一种面料风格。如果消费者对休闲黑色面料的需求如此之少，保留这种库存可能就没有意义。

#### 查询生成：商业闭源路线

如果所有用户都必须学习 SQL 语法和如何运行 SQL*PLUS，那么数据仓库的承诺就无法实现。在接受了 10 年的查询工具广告后，我们决定，基于表单的查询工具的状态必须真正先进。因此，我们建议 Levi Strauss 使用 Seagate Crystal Reports 和 Crystal Info 来分析他们的数据。然而，这些打包工具最终并没有很好地符合 Levi's 想要实现的目标。首先，构建查询并不比编写 SQL 语句语义上更简单。我们请来的 Crystal Reports 顾问说，他的大多数客户最终都让程序员设置报表查询，业务人员每天只需针对新数据运行报表。如果专业程序员必须构建查询，那么使用我们的标准 Web 开发工具编写更多管理页面就同样容易，每页大约需要 15 分钟。其次，无法确保数据仓库查询在互联网上的任何地方对授权用户可用。最后，允许从运行 Crystal Reports 的 Windows 机器通过 Levi's 防火墙到我们在 Web 上的 Oracle 数据仓库的 SQL*Net 连接存在安全和社会问题。

由于不确定其他商业产品是否更好，也不想让客户失望，我们扩展了 ArsDigita 社区系统，增加了一个仅作为 Web 工具运行的数据仓库查询模块。这是一个免费的开源系统，随标准 ACS 软件包一起提供，您可以从[`www.arsdigita.com/download/`](http://www.arsdigita.com/download/)下载。

#### 查询生成：开源 ACS 路线

ArsDigita 社区系统中的"dw"模块旨在实现以下目标：

1.  天真的用户可以自己构建简单的查询

1.  专业程序员可以帮助那些天真的用户

1.  没有技能的用户可以重新执行保存的查询

我们在`queries`表中每个查询保留一行：

> ```
> create table queries ( 
>         query_id        integer primary key, 
>         query_name      varchar(100) not null, 
>         query_owner     not null references users, 
>         definition_time date not null, 
>         -- if this is non-null, we just forget about all the query_columns 
>         -- stuff; the user has hand-edited the SQL 
>         query_sql       varchar(4000) 
> ); 
> 
> ```

除非 `query_sql` 列填充了手工编辑的查询，否则查询将通过查看 `query_columns` 表中的多行来构建：

> ```
> -- this specifies the columns we we will be using in a query and 
> -- what to do with each one, e.g., "select_and_group_by" or 
> -- "select_and_aggregate" 
>  
> -- "restrict_by" is tricky; value1 contains the restriction value, e.g., '40' 
> -- or 'MA' and value2 contains the SQL comparion operator, e.g., "=" or ">" 
>  
> create table query_columns ( 
>         query_id        not null references queries, 
>         column_name     varchar(30), 
>         pretty_name     varchar(50), 
>         what_to_do      varchar(30), 
>         -- meaning depends on value of what_to_do 
>         value1          varchar(4000), 
>         value2          varchar(4000) 
> ); 
>  
> create index query_columns_idx on query_columns(query_id); 
> 
> ```

最初，`query_columns` 的定义看起来很奇怪。它指定了列的名称但没有表。该模块是基于一个简化假设的，即我们有一个巨大的视图 `ad_hoc_query_view`，其中包含了所有维度表的列以及事实表的列。

这是我们为 Levi's 数据仓库创建视图的方法：

> ```
> create or replace view ad_hoc_query_view  
> as  
> select minutes_login_to_order, days_first_invite_to_order, 
>        days_order_to_shipment, days_shipment_to_intent, pants_id,
>        price_charged, tax_charged, shipping_charged, 
>        oracle_date, day_of_week,
>        day_number_in_month, week_number_in_year, week_number_overall,
>        month, month_number_overall, quarter, fiscal_period, 
>        holiday_flag, weekday_flag, season, color, fabric, cuff_state,
>        pleat_state, coupon_state, coupon_range, repeat_class, 
>        on_time_status, returned_status, ship_to_region, ship_to_state 
> from sales_fact f, time_dimension t, product_dimension p, 
>      promotion_dimension pr, consumer_dimension c, 
>      user_experience_dimension u, ship_to_dimension s 
> where f.time_key = t.time_key 
> and f.product_key = p.product_key 
> and f.promotion_key = pr.promotion_key 
> and f.consumer_key = c.consumer_key 
> and f.user_experience_key = u.user_experience_key 
> and f.ship_to_key = s.ship_to_key; 
> 
> ```

乍一看，这似乎是导致 Oracle 性能下降的通行证。对于每个数据仓库查询，我们都将进行七路连接，无论我们是否需要一些维度表中的信息。

我们可以按如下方式测试这一假设：

> ```
> -- tell SQL*Plus to turn on query tracing
> set autotrace on
> 
> -- let's look at how many pants of each color
> -- were sold in each region
> 
> SELECT ship_to_region, color, count(pants_id)
> FROM ad_hoc_query_view
> GROUP BY ship_to_region, color;
> 
> ```

Oracle 将首先返回查询结果...

> | ship_to_region | 颜色 | count(pants_id) |
> | --- | --- | --- |
> | 中部地区 | 黑色 | 46 |
> | 中部地区 | 深灰 | 23 |
> | 中部地区 | 深棕 | 39 |
> | .. |
> | 西部地区 | 中棕 | 223 |
> | 西部地区 | 深蓝 | 245 |
> | 西部地区 | 橄榄绿 | 212 |

... 然后解释这些结果是如何得到的：

> ```
> Execution Plan 
> ---------------------------------------------------------- 
>    0      SELECT STATEMENT Optimizer=CHOOSE (Cost=181 Card=15 Bytes=2430) 
>    1    0   SORT (GROUP BY) (Cost=181 Card=15 Bytes=2430) 
>    2    1     NESTED LOOPS (Cost=12 Card=2894 Bytes=468828) 
>    3    2       HASH JOIN (Cost=12 Card=885 Bytes=131865) 
>    4    3         TABLE ACCESS (FULL) OF 'PRODUCT_DIMENSION' (Cost=1 Card=336 Bytes=8400) 
>    5    3         HASH JOIN (Cost=6 Card=885 Bytes=109740) 
>    6    5           TABLE ACCESS (FULL) OF 'SHIP_TO_DIMENSION' (Cost=1 Card=55 Bytes=1485) 
>    7    5           NESTED LOOPS (Cost=3 Card=885 Bytes=85845) 
>    8    7             NESTED LOOPS (Cost=3 Card=1079 Bytes=90636) 
>    9    8               NESTED LOOPS (Cost=3 Card=1316 Bytes=93436) 
>   10    9                 TABLE ACCESS (FULL) OF 'SALES_FACT' (Cost=3 Card=1605 Bytes=93090) 
>   11    9                 INDEX (UNIQUE SCAN) OF 'SYS_C0016416' (UNIQUE) 
>   12    8               INDEX (UNIQUE SCAN) OF 'SYS_C0016394' (UNIQUE) 
>   13    7             INDEX (UNIQUE SCAN) OF 'SYS_C0016450' (UNIQUE) 
>   14    2       INDEX (UNIQUE SCAN) OF 'SYS_C0016447' (UNIQUE) 
> 
> ```

正如你从加粗的表名中看到的那样，Oracle 足够聪明，仅检查与我们的查询相关的表：`product_dimension`，因为我们询问了颜色；`ship_to_dimension`，因为我们询问了地区；`sales_fact`，因为我们要求计算出售的裤子数量。底线：Oracle 进行了三路连接，而不是视图指定的七路连接。

从存储在 `query_columns` 中的信息生成到 `ad_hoc_query_view` 的 SQL 查询最容易通过诸如 Java、PL/SQL、Perl 或 Tcl（这里是伪代码）等过程化语言的函数来完成：

> ```
> proc generate_sql_for_query(a_query_id)
>     select_list_items list;
>     group_by_items list;
>     order_clauses list;
> 
>     foreach row in "select column_name, pretty_name
>                     from query_columns  
>                     where query_id = a_query_id 
>                       and what_to_do = 'select_and_group_by'"] 
>         if row.pretty_name is null then
>             append_to_list(group_by_items, row.column_name)
>         else
>             append_to_list(group_by_items, row.column_name || ' as "' || row.pretty_name || '"'
>         end if
>     end foreach
> 
>     foreach row in "select column_name, pretty_name, value1 
>                     from query_columns  
>                     where query_id = a_query_id 
>                       and what_to_do = 'select_and_aggregate'"
>          if row.pretty_name is null then
> 	    append_to_list(select_list_items, row.value1 || row.column_name)
>          else
>             append_to_list(select_list_items, row.value1 || row.column_name || ' as "' || row.pretty_name || '"'
>          end if
>     end foreach
> 
>     foreach row in "select column_name, value1, value2 
>                     from query_columns  
>                     where query_id = a_query_id 
>                       and what_to_do = 'restrict_by'"
>         append_to_list(where_clauses, row.column_name || ' ' || row.value2 || ' ' || row.value1)
>     end foreach
>  
>     foreach row in "select column_name 
>                     from query_columns  
>                     where query_id = a_query_id 
>                       and what_to_do = 'order_by'"] 
>         append_to_list(order_clauses, row.column_name)
>     end foreach
>  
>     sql := "SELECT " || join(select_list_items, ', ') || 
>            " FROM ad_hoc_query_view"
> 
>     if list_length(where_clauses) > 0 then
>         append(sql, ' WHERE ' || join(where_clauses, ' AND '))
>     end if
>  
>     if list_length(group_by_items) > 0 then
>         append(sql, ' GROUP BY ' || join(group_by_items, ', '))
>     end if 
>  
>     if list_length(order_clauses) > 0 then
>         append(sql, ' ORDER BY ' || join(order_clauses, ', '))
>     end if
>  
>     return sql
> end proc
> 
> ```

这在实践中效果如何？假设我们要进行区域性广告活动。模特应该穿褶皱还是平纹裤子？我们需要查看最近按地区销售情况。使用 ACS 查询工具，用户可以使用 HTML 表单指定以下内容：

+   pants_id ：选择并使用计数进行聚合

+   ship_to_region ：选择并按组进行

+   pleat_state ：选择并按组进行

前述伪代码将其转换为

> ```
> SELECT ship_to_region, pleat_state, count(pants_id)
> FROM ad_hoc_query_view
> GROUP BY ship_to_region, pleat_state
> 
> ```

这将报告追溯到时间之初的销售情况。如果我们没有足够聪明地预见到我们的基于表单的界面需要时间窗口，那么“手动编辑 SQL”选项将为我们节省时间。专业程序员可以花几分钟来添加

> ```
> SELECT ship_to_region, pleat_state, count(pants_id)
> FROM ad_hoc_query_view
> WHERE oracle_date > sysdate - 45
> GROUP BY ship_to_region, pleat_state
> 
> ```

现在我们将结果限制为最近 45 天：

> | ship_to_region | pleat_state | count(pants_id) |
> | --- | --- | --- |
> | 中部地区 | 平纹 | 8 |
> | 中部地区 | 褶皱 | 26 |
> | 大湖地区 | 平纹 | 14 |
> | 大湖地区 | 褶皱 | 63 |
> | 中大西洋地区 | 平纹 | 56 |
> | 中大西洋地区 | 褶皱 | 162 |
> | 纽约和新泽西地区 | 平纹 | 62 |
> | 纽约和新泽西地区 | 褶皱 | 159 |
> | 新英格兰地区 | 平纹 | 173 |
> | 新英格兰地区 | 褶皱 | 339 |
> | 北中部地区 | 纯色 | 7 |
> | 中北部地区 | 折褶 | 14 |
> | 西北地区 | 平面前 | 20 |
> | 西北地区 | 折褶 | 39 |
> | 东南部地区 | 平面前 | 51 |
> | 东南部地区 | 折褶 | 131 |
> | 南部地区 | 平面前 | 13 |
> | 南部地区 | 折褶 | 80 |
> | 西部地区 | 平面前 | 68 |
> | 西部地区 | 折褶 | 120 |

如果我们稍微费点眼力和脑力，我们就会发现在五大湖和南部，平面前的裤子非常不受欢迎，但在新英格兰和西部更受欢迎。在地区内看到百分比会更好，但是标准 SQL 不允许将结果与周围行的值相结合。我们需要参考[“用于分析的 SQL”章节](http://oradoc.photo.net/ora816/server.816/a76994/analysis.htm#1020)中的 Oracle 数据仓库文档，了解使此成为可能的 SQL 扩展：

> ```
> SELECT 
>   ship_to_region, 
>   pleat_state, 
>   count(pants_id),
>   ratio_to_report(count(pants_id)) over (partition by ship_to_region) as percent_in_region
> FROM ad_hoc_query_view
> WHERE oracle_date > sysdate - 45
> GROUP BY ship_to_region, pleat_state
> 
> ```

我们要求 Oracle 对结果进行窗口化（“partition by ship_to_region”）并将每行的裤子数量与区域组内所有行的总和进行比较。这是结果：

> | ship_to_region | 折褶状态 | 计数(裤子编号) | 区域内百分比 |
> | --- | --- | --- | --- |
> | ... |
> | 五大湖地区 | 平面前 | 14 | .181818182 |
> | 五大湖地区 | 折褶 | 63 | .818181818 |
> | ... |
> | 新英格兰地区 | 平面前 | 173 | .337890625 |
> | 新英格兰地区 | 折褶 | 339 | .662109375 |
> | ... |

这并不是我们想要的。这些“百分比”是 1 的分数，并且精度远远超出了我们想要的范围。我们尝试在这个 SQL 语句的各个地方插入 Oracle 内置的 `round` 函数，但是我们所有的努力都只换来了一句报错：“ERROR at line 5: ORA-30484: missing window specification for this function”。我们不得不添加额外的 SELECT 层，即时视图，才能获得我们想要的报告：

> ```
> select ship_to_region, pleat_state, n_pants, round(percent_in_region*100) 
> from
> (SELECT 
>    ship_to_region, 
>    pleat_state, 
>    count(pants_id) as n_pants,
>    ratio_to_report(count(pants_id))
>         over (partition by ship_to_region) as percent_in_region
>  FROM ad_hoc_query_view
>  WHERE oracle_date > sysdate - 45
>  GROUP BY ship_to_region, pleat_state)
> 
> ```

返回

> | ship_to_region | 折褶状态 | 计数(裤子编号) | 区域内百分比 |
> | --- | --- | --- | --- |
> | ... |
> | 五大湖地区 | 平面前 | 14 | 18 |
> | 五大湖地区 | 折褶 | 63 | 82 |
> | ... |
> | 新英格兰地区 | 平面前 | 173 | 34 |
> | 新英格兰地区 | 折褶 | 339 | 66 |
> | ... |

### 如果你负责这个项目呢？

如果你负责一个数据仓储项目，你需要准备好必要的工具。不要因此感到畏缩。上面描述的整个 Levi Strauss 系统是由两名程序员在三天内实现的。

你需要的第一个工具是智慧和思考。如果你选择了正确的维度并将所需数据放入其中，那么你的数据仓库将会很有用。如果你的维度选错了，你甚至都不能问出有趣的问题。如果你不够聪明或思考不够深入，那么最好的做法可能是找到一家在你行业建立数据仓库方面有专业知识的精品咨询公司。让他们布置初始的星型模式。他们可能不会做得完全正确，但足够接受一段时间。如果找不到专家，《数据仓库工具包》（Ralph Kimball 1996）中包含了 10 种不同类型企业的示例模式。

你需要一些地方来存储你的数据并查询出其中的部分。由于你在使用 SQL，你唯一的选择就是关系数据库管理系统。有一些专业厂商历史上制作了增强型数据仓库的关系数据库管理系统，例如能够基于当前行的信息和以前输出行的信息来计算值的能力。这种方式摆脱了 E.F. Codd 在 1970 年勾勒出的严格的无序集合论世界观，但已被证明是有用的。从 8.1.6 版本开始，Oracle 将大多数有用的第三方功能加入到了他们的标准产品中。因此，现代数据仓库中除了最小和最大的之外，几乎都是使用 Oracle 构建的（参见[“SQL for Analysis”章节](http://oradoc.photo.net/ora816/server.816/a76994/analysis.htm#1020)以及[Oracle8i 数据仓库指南](http://oradoc.photo.net/ora816/server.816/a76994/toc.htm)中的卷 Oracle 文档）。

Oracle 包含了两个功能，可以让您构建和使用数据仓库而不需要投资于单独的硬件。第一个是自 1980 年代末以来 Oracle 采用的乐观锁定系统。如果有人在进行复杂的查询，它不会影响需要更新相同表的事务。基本上，每个查询都在其启动查询时数据库的快照中运行。第二个 Oracle 功能是*物化视图*或*摘要*。可以指示数据库保留按季度销售的摘要，例如。如果有人请求涉及季度销售的查询，将查询小的摘要表而不是全面的销售表。这可能会快 100 到 1000 倍。

数据仓库项目的一个典型目标是提供公司不同信息系统的统一视图。唯一的方法是从所有这些信息系统中提取数据，并清理这些数据以确保一致性和准确性。当涉及来自不同供应商的关系数据库管理系统（RDBMS）时，这被认为是一项具有挑战性的任务，尽管表面上看起来可能并不是这样。毕竟，每个 RDBMS 都附带一个 C 库。你可以编写一个 C 程序在 X 品牌数据库上执行查询，并在 Y 品牌数据库上执行插入操作。Perl 和 Tcl 具有方便的功能来转换文本字符串，并且这些脚本语言与 DBMS C 库之间有数据库连接接口。因此，你可以编写一个 Perl 脚本。公司内的大多数数据库都可以通过网络访问，至少在公司内部网络中是这样。Oracle 包括一个 Java 虚拟机和 Java 库，用于获取网页并解析 XML。因此，你可以编写一个在数据仓库 Oracle 安装中运行的 Java 或 PL/SQL 程序来获取外部信息并将其带回（请参阅有关外部和遗留数据的章节）。

如果你不喜欢编程或者遇到一个涉及旧主机的棘手连接问题，有一些公司提供可以帮助的软件。对于高端主机产品，Oracle 公司本身提供一些有用的分层产品。对于低端“比 Perl 更方便”的产品，Data Junction ([www.datajunction.com](http://www.datajunction.com)) 是有用的。

在已建立的数据仓库中，有各种有用的查询工具。理论上，如果你的数据模型组织得足够好，非技术用户将能够通过图形用户界面或 Web 浏览器进行导航。最知名的查询工具是 Crystal Reports ([www.seagatesoftware.com](http://www.seagatesoftware.com))，我们曾试图在 Levi Strauss 示例中使用它。请参阅[`www.arsdigita.com/doc/dw`](http://www.arsdigita.com/doc/dw) 了解免费开源 ArsDigita 社区系统数据仓库查询模块的详细信息。

所有这些有一个底线吗？如果你能够清晰地思考你的组织及其业务，构建正确的维度并合理地编写 SQL 程序，你将可以仅通过原始 RDBMS 取得成功。额外的软件工具可能会使项目变得稍微不那么痛苦或稍微缩短时间，但它们并不是至关重要的。

### 更多信息

数据仓库的构建是一种类似行会的活动。大部分专家知识都包含在专门从事某种类型公司数据仓库构建的公司中。例如，有些公司专门为超市建立数据仓库，有些公司专门为百货商店建立数据仓库。使这个行会保持紧密的一部分原因是关于这个主题的教科书和期刊文章的质量较差。大部分关于数据仓库的书籍是由不懂 SQL 的人编写的，也是为这样的人编写的。这些书籍关注于（1）你可以从供应商那里购买的东西，（2）在数据仓库完成后你可以通过图形用户界面做的事情，以及（3）如何在大型组织中导航，以便说服其他人同意提供数据、资金和宽松的时间表。

我们发现的唯一值得一读的关于数据仓库的入门书籍是 Ralph Kimball 的[数据仓库工具包](http://www.amazon.com/exec/obidos/ASIN/0471153370/pgreenspun-20)。Kimball 还是一本关于点击流数据仓库的鼓舞人心的书籍的作者：[数据 Webhouse 工具包](http://www.amazon.com/exec/obidos/ASIN/0471376809/pgreenspun-20)。如果你对将经典的维度数据仓库技术应用于用户活动分析感兴趣，后一本书很不错。

这并不是一本书，也不适合初学者，但是官方 Oracle 服务器文档中的[Oracle8i 数据仓库指南](http://oradoc.photo.net/ora816/server.816/a76994/toc.htm)对于数据仓库的构建非常有用。

消费者购买行为数据可从 A.C. Nielsen ([www.acnielsen.com](http://www.acnielsen.com/))、Information Resources Incorporated (IRI; [www.infores.com](http://www.infores.com))以及[`dir.yahoo.com/Business_and_Economy/Business_to_Business/Marketing_and_Advertising/Market_Research/`](http://dir.yahoo.com/Business_and_Economy/Business_to_Business/Marketing_and_Advertising/Market_Research/)中列出的其他公司获取。

### 参考

+   [Oracle8i 数据仓库指南](http://oradoc.photo.net/ora816/server.816/a76994/toc.htm)，特别是[“分析用 SQL”章节](http://oradoc.photo.net/ora816/server.816/a76994/analysis.htm#1020)

+   Oracle 应用开发人员指南中的 ROLLUP 示例：[`www.oradoc.com/keyword/rollup`](http://www.oradoc.com/keyword/rollup)

下一步：外部和遗留数据

* * *

[philg@mit.edu](http://philip.greenspun.com/)

### 读者评论

> 我真的很喜欢沃尔玛/Sybase 的例子，因为沃尔玛实际上运行着世界上最大的商业数据仓库，包括两年的详细数据，数十亿行的详细数据。当然，它不是使用像 Sybase/Oracle 这样的 OLTP 系统，而是一个决策支持数据库，Teradata。
> 
> -- Dieter Noeth，2003 年 5 月 14 日
> 
> 我要争辩一下：http://www.wintercorp.com/vldb/2003_TopTen_Survey/TopTenWinners.asp 显示法国电信拥有最大的 Oracle DSS 系统。沃尔玛不在前十名中，而令人惊讶的是，被挤压的竞争对手 Kmart 却在其中。
> 
> -- 无论如何，2004 年 1 月 7 日
> 
> 你对 Sybase 的评论是幼稚且不正确的。也许你在与 Sybase 支持打交道时遇到了困难，我不确定我能否改变这种情况。多年来，Sybase IQ 一直是世界上一些最大数据仓库的祸根。查询性能和可伸缩性显然是所有 Sybase IQ 实施的亮点。Sybase 客户 comScore Networks 在 2003 年冬季公司十佳计划中获得了最大数据库大小和最多行/记录的大奖，该奖项是针对使用 Sybase IQ 这一高度可扩展的分析引擎的基于 Microsoft Windows 的系统。在 UNIX 类别中，其他获得 Winter Corporation 十佳奖的 Sybase 客户包括 Nielsen Media Research 和韩国客户健康保险审查机构（HIRA）、LG Card、三星卡和韩国初亨银行。http://www.sybase.be/belgium/press/20031111-ipg-IQwintercorp.jsp 我感谢你给了我在这个页面上发表评论的机会。
> 
> -- Subraya Pai，2004 年 5 月 9 日
> 
> Crystal Reports 不是通常用于数据仓库的自由查询报表工具，所以也许这就是你的最终客户对它不太满意的原因。更适合这项任务的工具包括 BusinessObjects（几个月前也收购了 CrystalReports）、Brio（大约一年前被 Hyperion 收购）、Microstrategy、Oracle Discoverer 和 Cognos。所有这些工具都允许您构建关于数据仓库数据模型的元数据，并以用户熟悉的术语呈现给最终用户（没有晦涩的数据库表列名，预定义的过滤条件等）。对于最终用户来说，只需将“对象”拖放到其报表中并“按下”按钮即可。该工具将生成适当的 SQL，查询数据库（其中一些甚至会重新编写查询，如果您有聚合表，允许您在报表查询结果中“连接”不同查询和数据库或将存储过程作为数据源），允许您对结果集进行简单计算（类似于 Excel）等等。
> 
> 致敬，乔治
> 
> -- 乔治·布雷亚祖，2004 年 11 月 15 日
> 
> 这篇文章被认为是数据仓库领域的一篇好文章。
> 
> 我想说有一种查询语言叫做多维表达式 MDX。它现在是 OLAP 的标准查询语言。它类似于 Sql，但在分组和更多函数方面具有更多功能，以便简化 OLAP 操作。最常见的函数是 ROLLUP 和 CUBE>>>>>>>>>>>>>>>>>>>>>>>>>>>等等。感谢大家......
> 
> -- drtech dr，2008 年 12 月 22 日
> 
> 很好且有用的文章..感谢分享..
> 
> -- mitesh trivedi，2010 年 2 月 9 日

添加评论

### 相关链接

+   [优化数据仓库](http://www.dwoptimize.com/2007/06/components-of-data-warehouse.html)- 使用并行性、分区和跨整个应用程序堆栈的聚合摘要来优化大型数据仓库的性能和可用性，包括 ETL、数据库和报告。 （由 Jag Singh 贡献）

+   [DBMS 2 关于数据仓库](http://www.dbms2.com/category/analytics-technologies/data-warehouse)- 数据仓库技术、发展和趋势，来自现在是数据库管理新闻和分析的行业领先来源。 （由 Curt Monash 贡献）

添加链接
