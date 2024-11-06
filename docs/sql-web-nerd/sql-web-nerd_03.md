| ![1995 年曼哈顿 IMTA 秀](img/legs-overview-20.tcl) |
| --- |

## 数据建模

SQL for Web Nerds 的一部分，由 [Philip Greenspun](http://philip.greenspun.com/) 编写 | ![1995 年曼哈顿 IMTA 秀](img/little-boy-61.tcl) |

* * *

![1995 年曼哈顿 IMTA 秀上患水痘的 14 岁 Christina Perreault，由 Francesca Milano 化妆。](img/chicken-pox-51.tcl) 数据建模是关系数据库世界中最困难且最重要的活动。如果数据模型错误，您的应用程序可能无法满足用户需求，可能不可靠，可能会用垃圾填满数据库。那么为什么我们要从工作中最具挑战性的部分开始 SQL 教程呢？因为在定义一些表之前，您无法进行查询、插入和更新。而定义表就是*数据建模*。

在数据建模时，您告诉关系数据库管理系统以下内容：

+   您将存储哪些数据元素

+   每个元素可以有多大

+   每个元素可以包含什么样的信息

+   哪些元素可能为空白

+   哪些元素受限于固定范围

+   各种表是否以及如何链接

### 三值逻辑

大多数计算机语言的程序员都熟悉布尔逻辑。一个变量可以是真或假。然而，在 SQL 中普遍存在的是*三值逻辑*的陌生概念。一列可以是真、假或 NULL。在构建数据模型时，您必须积极决定是否允许列的 NULL 值，以及如果允许，它代表什么。

例如，考虑一个用于记录用户提交评论到网站的表。出版商已经做出了以下规定：

+   评论在编辑批准之前不会发布

+   管理页面将向编辑显示所有待批准的评论，即已提交但尚未被编辑批准或拒绝的评论

这是数据模型：

> ```
>  create table user_submitted_comments ( comment_id integer primary key, user_id not null references users, submission_time date default sysdate not null, ip_address varchar(50) not null, content clob, approved_p char(1) check(approved_p in ('t','f')) ); 
> ```

这个模型中的隐含假设是`approved_p`可以为 NULL，并且如果在 INSERT 期间没有显式设置，那就是默认值。那么检查约束呢？它似乎将`approved_p`限制为“t”或“f”的值。然而，NULL 是一个特殊值，如果我们想要防止`approved_p`取 NULL 值，我们必须添加一个显式的`not null`约束。

如何处理查询中的 NULL 值？让我们在`user_submitted_comments`中填充一些示例数据并查看：

> ```
>  insert into user_submitted_comments (comment_id, user_id, ip_address, content) values (1, 23069, '18.30.2.68', 'This article reminds me of Hemingway'); Table created. SQL> select first_names, last_name, content, user_submitted_comments.approved_p from user_submitted_comments, users where user_submitted_comments.user_id = users.user_id; FIRST_NAMES LAST_NAME CONTENT APPROVED_P ------------ --------------- ------------------------------------ ------------ Philip Greenspun This article reminds me of Hemingway 
> ```

我们已成功将`user_submitted_comments`和`users`表 JOIN 起来，以获取评论内容和提交评论的用户姓名。请注意，在选择列表中，我们必须明确请求`**user_submitted_comments**.approved_p`。这是因为`users`表也有一个`approved_p`列。

当我们插入评论行时，没有为 `approved_p` 列指定值。因此我们期望该值为 NULL，事实上似乎也是这样。Oracle 的 SQL*Plus 应用程序用空白表示 NULL 值。

对于管理页面，我们将只显示 `approved_p` 列为 NULL 的评论：

> ```
>  SQL> select first_names, last_name, content, user_submitted_comments.approved_p from user_submitted_comments, users where user_submitted_comments.user_id = users.user_id **and user_submitted_comments.approved_p = NULL**; no rows selected 
> ```

"未选择任何行"? 这很奇怪。我们确实知道在评论表中有一行，而且它的 `approved_p` 列被设置为 NULL。如何调试查询？首先要做的是简化，删除 JOIN：

> ```
>  SQL> select * from user_submitted_comments where approved_p = NULL; no rows selected 
> ```

这里发生的情况是，涉及到 NULL 的任何表达式都会求值为 NULL，包括看起来像是 "NULL = NULL" 的表达式。WHERE 子句正在寻找求值为真的表达式。你需要使用的是特殊的测试 IS NULL：

> ```
>  SQL> select * from user_submitted_comments where approved_p **is NULL**; COMMENT_ID USER_ID SUBMISSION_T IP_ADDRESS ---------- ---------- ------------ ---------- CONTENT APPROVED_P ------------------------------------ ------------ 1 23069 2000-05-27 18.30.2.68 This article reminds me of Hemingway 
> ```

SQL 程序员之间的格言是，你只能在 UPDATE 语句中使用 "= NULL"（将列的值设置为 NULL）。在 WHERE 子句中使用 "= NULL" 是毫无意义的。

底线是，作为数据建模者，你将不得不决定哪些列可以是 NULL，以及该值的含义是什么。

### 回到邮件列表

让我们回到引言中的邮件列表数据模型：

> ```
>  create table mailing_list ( email varchar(100) not null primary key, name varchar(100) ); create table phone_numbers ( email varchar(100) not null references mailing_list, number_type varchar(15) check (number_type in ('work','home','cell','beeper')), phone_number varchar(20) not null ); 
> ```

这个数据模型将你锁定在一些现实中：

+   你不会向邮件列表中的人发送任何实体的新年贺卡；你没有任何方法存储他们的地址。

+   你将不会向那些工作在拥有复杂 Lotus Notes 配置的公司的人发送任何电子邮件；有时 Lotus Notes 会导致电子邮件地址超过 100 个字符。

+   你有可能使数据库充斥着垃圾，因为你没有以任何方式限制电话号码。美国用户可能会因错误而添加或删除数字。国际用户可能会输错国家代码。

+   你有可能无法为富人服务，因为 `number_type` 列可能受到太多限制。假设威廉·H·盖茨三世想记录一些额外的电话号码，类型为 "boat"、"ranch"、"island" 和 "private_jet"。`check (number_type in ('work','home','cell','beeper'))` 语句阻止盖茨先生这样做。

+   你有可能在数据库中有些人的记录，而他们的名字你并不知道，因为 `mailing_list` 的 `name` 列可以是 NULL。

+   更改用户的电子邮件地址不会是最简单的操作。你在两个表中都使用 `email` 作为键，因此必须更新两个表。`references mailing_list` 防止你只更新 `mailing_list` 而在 `phone_numbers` 中留下孤立的行。但如果用户频繁更改他们的电子邮件地址，你可能不希望以这种方式处理。

+   由于您没有为存储密码或任何其他身份验证手段提供任何准备，如果允许用户更新其信息，您会面临允许恶意更改的轻微风险。（风险并不像看起来那么大，因为您可能不会发布完整的邮寄名单；攻击者必须猜测您邮寄名单上的人名。）

这些不一定是您希望陷入的不良现实。然而，一个优秀的数据建模者认识到.sql 文件中的每一行代码对网络服务都有深远的影响。

### 用触发器掩盖您的错误

假设您一直在使用上述数据模型来收集希望在您添加新文章时收到提醒的网站读者的姓名。您已经两个月没有发送任何通知了。您想要发送给过去两个月内注册的所有人一个“欢迎来到我的网络服务；感谢您的注册；这里有什么新内容”的消息。您想要给较早注册的订阅者发送一个简单的“这里有什么新内容”的消息。但是您无法这样做，因为您没有存储注册日期。很容易修复表：

> ```
>  alter table mailing_list add (registration_date date); 
> ```

但是如果您有 15 个不同的 Web 脚本使用这个表怎么办？查询它的不是问题。如果它们不请求新列，它们将不会得到它，也不会意识到表已经更改（这是关系数据库管理系统的一个重要卖点之一）。但是更新表的脚本都需要更改。如果您错过了一个脚本，您可能会陷入一个表中各种随机行缺少关键信息的困境。

Oracle 为您的问题提供了解决方案：*触发器*。触发器是告诉 Oracle“每当有人触及这个表，我希望您执行以下代码片段”的一种方式。以下是我们如何定义触发器`mailing_list_registration_date`：

> ```
>  create trigger mailing_list_registration_date before insert on mailing_list for each row when (new.registration_date is null) begin :new.registration_date := sysdate; end; 
> ```

请注意，触发器仅在有人尝试插入具有 NULL 注册日期的行时才运行。如果出于某种原因您需要从另一个数据库复制记录，并且它们具有注册日期，您不希望此触发器用复制的日期覆盖它。

关于这个触发器的第二点要注意的是它是`for each row`运行的。这被称为“行级触发器”，而不是“语句级触发器”，后者每个事务只运行一次，通常不是您想要的。

第三点是我们正在使用魔术 Oracle 过程`sysdate`，它将返回当前时间。Oracle 的`date`类型精确到秒，即使默认只显示日期。

第四点是，从 Oracle 8 开始，我们可以通过在列的定义中添加`default sysdate`指令来更清晰地执行此操作。

值得注意的最后一点是`:new.`语法。这使您可以引用正在插入的新值。还有一个类似的`:old.`功能，对于更新触发器很有用：

> ```
>  create or replace trigger mailing_list_update before update on mailing_list for each row when (new.name <> old.name) begin -- user is changing his or her name -- record the fact in an audit table insert into mailing_list_name_changes (old_name, new_name) values (:old.name, :new.name); end; / show errors 
> ```

这次我们使用了`create or replace`语法。这样我们就不必在想要更改触发器定义时`drop trigger mailing_list_update`。我们使用 SQL 注释快捷键"--"添加了一条注释。在触发器定义中使用了`new.`和`old.`，限制了触发器运行的条件。在`begin`和`end`之间，我们处于一个 PL/SQL 块中。这是 Oracle 的过程化语言，稍后会描述，其中`new.name`表示"从`new`中的记录中的`name`元素"。所以你必须使用`:new`。正是这些晦涩的地方导致了有能力的 Oracle 顾问每小时收费 200 美元以上。

"/"和`show errors`在最后是给 Oracle 的 SQL*Plus 程序的指令。斜杠表示"我已经输入完这段 PL/SQL，请评估我刚刚输入的内容。" "show errors"表示"如果你发现我刚刚输入的内容有任何问题，请告诉我"。

### 讨论论坛--菲尔格的个人奥德赛

1995 年，我建立了一个分级讨论论坛，详细描述在`philip.greenspun.com/wtr/dead-trees/53013.htm`中。这是我存储帖子的方式：

> ```
>  create table bboard ( msg_id char(6) not null primary key, refers_to char(6), email varchar(200), name varchar(200), one_line varchar(700), message clob, notify char(1) default 'f' check (notify in ('t','f')), posting_time date, sort_key varchar(600) ); 
> ```

系统内部采用德国排序：消息通过`msg_id`唯一标识，通过`refers_to`相互引用（即说"我是对消息 X 的回复"），通过`sort_key`列可以方便地显示一个主题串。

`email`和`name`列允许意大利式混乱；用户可以保持匿名，冒充"president@whitehouse.gov"或给出任何名字。

当我建立系统时，这似乎是个好主意。我关心的是它能够可靠运行。我不在乎用户是否输入虚假内容；管理页面使得删除这样的帖子非常容易，而且，无论如何，如果有人有有趣的东西要说但需要保持匿名，为什么系统要拒绝他们的帖子呢？

10 万个帖子后，作为[photo.net](http://www.photo.net/)问答论坛的管理员，我开始看到我的数据建模错误的规模。

首先，匿名帖子和虚假电子邮件地址并不是来自微软员工揭露他们邪恶老板的黑暗真相。它们来自一些失败者，试图但失败地想要搞笑或者希望羞辱其他读者。一些虚假地址来自于被垃圾邮件潮水吓到的人们（在 1995 年并不是一个严重的问题）。

其次，我没有意识到我的电子邮件警报系统、虚假电子邮件地址和 Unix 邮件程序的结合会导致我的个人邮箱被填满无法发送到"asdf@asdf.com"或"duh@duh.net"的消息。

虽然解决方案涉及更改一些 Web 脚本，但基本上修复的方法是添加一列来存储发帖的 IP 地址：

> ```
>  alter table bboard add (originating_ip varchar(16)); 
> ```

保留这些数据使我能够看到大多数匿名发帖者是那些使用论坛已经一段时间的人，通常来自相同的 IP 地址。我只是给他们发送邮件，要求他们停止，解释了电子邮件退信的问题。

经营 photo.net 社区四年后，我们意识到我们需要一些方法来

+   为已更改其电子邮件地址的用户显示站点历史记录

+   阻止问题用户给管理员和社区带来负担

+   仔细地将用户贡献的内容在 photo.net 的各个子系统中紧密联系在一起

对于任何有经验的数据库极客来说，解决方案是显而易见的：一个规范的用户表，然后引用它的内容表。这里是一个简化版本的数据模型，取自一个用于构建在线社区的工具包，描述在`philip.greenspun.com/panda/community`中：

> ```
>  create table users ( user_id integer not null primary key, first_names varchar(100) not null, last_name varchar(100) not null, email varchar(100) not null unique, .. ); create table bboard ( msg_id char(6) not null primary key, refers_to char(6), topic varchar(100) not null references bboard_topics, category varchar(200), -- only used for categorized Q&A forums originating_ip varchar(16), -- stored as string, separated by periods user_id integer not null references users, one_line varchar(700), message clob, -- html_p - is the message in html or not html_p char(1) default 'f' check (html_p in ('t','f')), ... ); create table classified_ads ( classified_ad_id integer not null primary key, user_id integer not null references users, ... ); 
> ```

请注意，贡献者的姓名和电子邮件地址不再出现在`bboard`表中。这并不意味着我们不知道谁发布了消息。事实上，这个数据模型甚至不能表示匿名帖子：`user_id integer not null references users`要求每个帖子都与一个用户 ID 相关联，并且`users`表中实际上有一个具有该 ID 的行。

首先，让我们谈谈将一个每天有 60 万次点击的网络服务从一个数据模型移动到另一个数据模型是多么有趣。在这种情况下，请注意原始的`bboard`数据模型只有一个`name`列。社区系统有单独的列用于名字和姓氏。一个转换脚本可以轻松地拆分"Joe Smith"，但是对于 William Henry Gates III 该怎么办呢？

我们如何复制匿名帖子？请记住，Oracle 不灵活也不智能。我们说我们希望`bboard`表中的每一行都引用`users`表中的一行。Oracle 将中止任何可能违反完整性约束的事务。因此，我们要么放弃所有这些匿名帖子（以及引用它们的任何非匿名帖子），要么创建一个名为"Anonymous"的用户，并将所有匿名帖子分配给该用户。这种解决方案的技术术语是*kludge*。

长期用���中比匿名帖子更困难的问题是那些在打字或保持工作方面有困难的用户。考虑一个已经自我识别为

1.  Joe Smith; jsmith@ibm.com

1.  Jo Smith; jsmith@ibm.com (姓名拼写错误)

1.  Joseph Smith; jsmth@ibm.com (电子邮件中的拼写错误)

1.  Joe Smith; cantuseworkaddr@hotmail.com (IBM 的新政策)

1.  Joe Smith-Jones; joe_smithjones@hp.com (结婚，改名字，换工作)

1.  Joe Smith-Jones; jsmith@somedivision.hp.com (有效但不是规范的公司电子邮件地址)

1.  Josephina Smith; jsmith@somedivision.hp.com (性别变更；离婚)

1.  Josephina Smith; josephina_smith@hp.com (新的公司地址)

1.  Siddhartha Bodhisattva; josephina_smith@hp.com (哲学观念的改变)

1.  Siddhartha Bodhisattva; thinkwaitfast@hotmail.com（暂时旅行以寻找启示）

当代社区成员都认识这些帖子来自同一个人，但要构建一个良好的半自动合并该人的帖子到一个用户记录中的方法是非常具有挑战性的。

一旦我们将所有内容复制到这个新的*规范化*数据模型中，注意到我们不能再次陷入同样的困境。如果一个用户贡献了 1000 篇帖子，我们不会有 1000 条不同的记录来记录该用户的姓名和电子邮件地址。如果一个用户换工作了，我们只需要更新一个表中的一行中的一个列。

新数据模型中的`html_p`列值得一提。在 1995 年，我并不了解用户提交数据的问题。一些用户会提交纯文本，看起来很简单，但实际上你不能简单地将其输出为 HTML。如果用户 A 键入<或>字符，它们可能会被用户 B 的 Web 浏览器吞噬。这有关紧要吗？考虑"<g>"在各个在线圈子中被解释为"咧嘴笑"的缩写，但在 Netscape Navigator 中被解释为未识别（因此被忽略）的 HTML 标签。比较以下含义

> "我们不应认为比尔·盖茨拥有的财富比 1 亿最贫困的美国人*加起来*还要多是不公平的。毕竟，他发明了个人电脑、图形用户界面和互联网。"

with

> "我们不应认为比尔·盖茨拥有的财富比 1 亿最贫困的美国人*加起来*还要多是不公平的。毕竟，他发明了个人电脑、图形用户界面和互联网。<g>"

对我来说，确保这些字符永远不会被解释为标记是很容易的。事实上，使用 AOLserver，只需调用内置过程`ns_quotehtml`就可以做到。然而，考虑一个情况，一个书呆子发布了一些 HTML。其他用户会看到

> "想要了解更多我卓越的思考和谦逊，请查看<a href="http://philip.greenspun.com/">我的主页</a>。"

我发现唯一真正的解决方案是询问用户提交的内容是 HTML 片段还是纯文本，在数据库中的`html_p`列中显示用户告诉我们的内容，并向用户展示一个可预览内容的批准页面。

这个数据模型完美吗？永久吗？绝对是。它至少会持续...哇！等一下。我不知道 Dave Clark 正在用 IPv6 ([`www.faqs.org/rfcs/rfc2460.html`](http://www.faqs.org/rfcs/rfc2460.html)) 替换自 1980 年左右以来世界一直在运行的原始互联网协议。在不久的将来，我们将拥有 128 位长的 IP 地址。这是 16 字节，每个字节需要两个十六进制字符来表示。因此我们需要 32 个字符，再加上至少 7 个用于分隔十六进制数字的句号。我们可能还需要几个字符来表示“这是一个十六进制表示”。因此，我们全新的数据模型实际上存在严重的缺陷。修复起来有多容易？在 Oracle 中：

> ```
>  alter table bboard modify (originating_ip varchar(50)); 
> ```

你不会总是这么轻松。Oracle 不会让你将列从最大长度为 50 个字符缩减到 16 个字符，即使没有任何行的值长于 16 个字符。Oracle 也让添加一个约束为`not null`的列变得困难。

### 代表网站核心内容

无限制的互联网讨论通常是有用的，有时也是引人入胜的，但一个好的网站的支柱通常是一组精心编写的扩展文档。从历史上看，这些文档往往存储在 Unix 文件系统中，且不经常更改。因此，我将它们称为*静态页面*。在 photo.net 服务器上的静态页面示例包括本书章节，摄影师光线教程在 [`www.photo.net/making-photographs/light`](http://www.photo.net/making-photographs/light)。

我们有一些重要的目标要考虑。我们希望数据库中的数据

+   帮助社区专家确定哪些文章需要修订，以及社区整体最看重哪些新文章。

+   帮助贡献者共同撰写草稿文章或旧文章的新版本。

+   收集和组织读者的评论和讨论，不仅用于展示给其他读者，还用于帮助作者保持内容的更新。

+   收集和组织读者提交的有关更广泛互联网上相关内容（即链接）的建议。

+   帮助读者指向可能对他们感兴趣的新内容或对他们来说是新的内容，这是基于他们之前阅读的内容或基于他们认为有趣的内容类型。

这些重要目标导致了一些更具体的目标：

+   我们将需要一个保存静态页面本身的表。

+   由于每页可能有许多评论，我们需要一个单独的表来保存用户提交的评论。

+   由于每页可能有许多相关链接，我们需要一个单独的表来保存用户提交的链接。

+   由于一个页面可能有许多作者，我们需要一个单独的表来注册作者-页面的多对一关系。

+   考虑到“帮助读者找到他们感兴趣的内容”目标，似乎我们需要存储页面所属的类别或类别。由于一个页面可能有多个类别，我们需要一个单独的表来保存页面和类别之间的映射。

> ```
>  create table static_pages ( page_id integer not null primary key, url_stub varchar(400) not null unique, original_author integer references users(user_id), page_title varchar(4000), page_body clob, obsolete_p char(1) default 'f' check (obsolete_p in ('t','f')), members_only_p char(1) default 'f' check (members_only_p in ('t','f')), price number, copyright_info varchar(4000), accept_comments_p char(1) default 't' check (accept_comments_p in ('t','f')), accept_links_p char(1) default 't' check (accept_links_p in ('t','f')), last_updated date, -- used to prevent minor changes from looking like new content publish_date date ); create table static_page_authors ( page_id integer not null references static_pages, user_id integer not null references users, notify_p char(1) default 't' check (notify_p in ('t','f')), unique(page_id,user_id) ); 
> ```

请注意，我们在这个表中使用一个生成的整数`page_id`键。我们本可以用`url_stub`（文件名）作为表的键，但这样会使在 Unix 文件系统中重新组织文件变得非常困难（这在 Web 服务器上实际上很少发生；它会破坏来自外部站点的链接）。

当您需要向`static_pages`插入新行时，如何生成这些唯一的整数键？您可以

+   锁定表

+   找到迄今为止的最大`page_id`

+   加一以创建一个新的唯一`page_id`

+   插入行

+   提交事务（释放表锁）

更好的方法是使用 Oracle 内置的序列生成功能：

> ```
>  create sequence page_id_sequence start with 1; 
> ```

然后我们可以通过在 INSERT 语句中使用`page_id_sequence.nextval`来获得新的页面 ID（详见事务章节以获取有关序列的更全面讨论）。

* * *

### 参考

这里是 Oracle 中可用的数据建模工具的摘要，每个都链接到 Oracle 文档。本参考部分涵盖以下内容：

+   数据类型

+   用于创建、修改和删除表的语句

+   约束

#### 数据类型

对于为表定义的每一列，您必须指定该列的数据类型。以下是您的选项：

> | 字符数据 |
> | --- |
> 
> | char(n) | 固定长度的字符字符串，例如，`char(200)`将占用 200 字节，无论实际字符串有多长。当数据确实是固定大小时，这种方法效果很好，例如，当您将用户的性别记录为“m”或“f”时。当数据长度可变时，这种方法效果很差。它不仅在磁盘和内存缓存中浪费空间，而且使比较失败。例如，假设您将“rating”插入到`char(30)`类型的`comment_type`列中，然后您的 Tcl 程序查询数据库。Oracle 将此列值返回给过程化语言客户端，用足够的空格填充以使总共达到 30 个字符。因此，如果您在 Tcl 中有一个比较，比如`$comment_type == "rating"`，比较将失败，因为`$comment_type`实际上是“rating”后面跟着 24 个空格。
> 
> Oracle8 中 char 的最大长度为 2000 字节。
> 
> | varchar(n) | Oracle8 中的可变长度字符字符串，最长可达 4000 字节。这些存储方式旨在最大程度地减少磁盘空间的使用，即，如果你只在`varchar(4000)`类型的列中放入一个字符，Oracle 在磁盘上只消耗两个字节。你不将所有列都设为`varchar(4000)`的原因是 Oracle 的索引系统限制了大约 700 字节的索引键。 |
> | --- | --- |
> | clob | 一个可变长度的字符字符串，在 Oracle8 中最长可达 4GB。CLOB 数据类型对于接受来自诸如讨论论坛之类的应用程序的用户输入非常有用。遗憾的是，Oracle8 对于如何插入、修改和查询 CLOB 数据有巨大的限制。如果可以的话，请使用`varchar(4000)`，如果不行就准备受苦吧。在一次极好的演示中展示了当公司不遵循《神话般的程序员月份》的教训时会发生什么，常规字符串函数无法在 CLOB 上工作。您需要调用 DBMS_LOB 包中同名的函数。这些函数接受相同的参数，但顺序不同。如果没有先阅读[Oracle8 服务器应用程序开发人员指南中的 DBMS_LOB 部分](http://www.oradoc.com/keyword/dbms_lob)，您将永远无法编写出可工作的代码。 |
> | nchar, nvarchar, nclob | n 前缀代表“国家字符集”。这些工作方式类似于 char、varchar 和 clob，但适用于多字节字符（例如 Unicode；参见[`www.unicode.org`](http://www.unicode.org)）。 |
> | 数值数据 |
> | number | Oracle 实际上只有一个内部数据类型用于存储数字。它可以处理 38 位精度和指数范围从-130 到+126。如果您想要更精确，可以指定精度和标度限制。例如，`number(3,0)`表示“将所有内容四舍五入为整数[标度 0]，接受范围从-999 到+999 的数字”。如果您是美国人并且商业头脑，`number(9,2)`可能很适合用于存储美元和美分的价格（除非您在向比尔·盖茨出售商品，在这种情况下，由于 9 的精度限制可能会限制）。如果您*是* [比尔·盖茨](http://www.photo.net/bg/)，您可能不想被无关紧要的数字分散注意力：告诉 Oracle 将所有内容四舍五入到最接近的百万，使用`number(38,-6)`。 |
> | integer | 就存储消耗和行为而言，这与`number(38)`没有任何不同，但我认为它读起来更好，更符合 ANSI SQL（如果有人实际上实现了它的话）。 |
> | 日期和日期/时间间隔（9i 版本及更新版本） |
> | timestamp | 一个记录了亚秒精度的时间点。在创建列时，您可以指定从 0（单秒精度）到 9（纳秒精度）的精度位数。Oracle 的日历可以处理公元前 4712 年 1 月 1 日至公元 9999 年 12 月 31 日之间的日期。您可以使用`to_timestamp`函数输入值，并使用`to_char`函数查询这些值。Oracle 提供了几种此数据类型的变体，用于处理跨多个时区聚合的数据。 |
> | interval year to month | 一段时间，以年和月表示。 |
> | interval day to second | 一段时间，以天、小时、分钟和秒表示。如果需要，可以精确到纳秒。 |
> | 日期和日期/时间间隔（8i 及更早版本） |
> | date | 自 9i 版本起已过时。一个时间点，以秒为精度记录，介于公元前 4712 年 1 月 1 日和公元 4712 年 12 月 31 日之间。您可以使用`to_date`函数输入值，并使用`to_char`函数查询出来。如果不使用这些函数，您将受限于使用默认系统格式掩码指定日期，通常为'DD-MON-YY'。这是一��引发 2000 年问题的好方法，因为 2000 年 1 月 23 日将被表示为'23-JAN-00'。在维护更好的系统中，这通常是 ANSI 的默认格式：'YYYY-MM-DD'，例如，2000 年 1 月 23 日表示为'2000-01-23'。 |
> | number | 嘿，这不是一个打字错误吗？`number`在日期部分做什么？它在这里是因为在 9i 版本之前的 Oracle 版本中代表日期时间间隔，尽管他们的文档从未明确说明这一点。如果您将数字添加到日期中，您将得到新的日期。例如，明天的这个时间是`sysdate+1`。要查询最近一小时提交的内容，您可以限制为`submitted_date > sysdate - 1/24`。 |
> | 二进制数据 |
> | blob | BLOB 代表“二进制大对象”。虽然它不一定非常大，但是 Oracle 允许您存储高达 4 GB 的数据。BLOB 数据类型被设置为允许存储图像、声音录音和其他固有的二进制数据。实际上，它也被欺诈性应用软件供应商使用。他们花几年时间把一些自己的恶劣格式凑在一起。他们的 MBA 高管客户要求整个系统基于关系数据库管理系统。软件供应商学会了足够的 Oracle 知识来“把所有东西都塞进一个 BLOB 中”。然后所有的市场营销和销售人员都很高兴，因为应用现在是从 Oracle 而不是文件系统中运行的。不幸的是，程序员和用户得不到太多帮助，因为你不能很有效地使用 SQL 来查询或更新 BLOB 中的内容。 |
> | bfile | 一个由操作系统（通常是 Unix）存储并由 Oracle 跟踪的二进制文件。当您需要从 SQL（故意对外部世界发生的事情一无所知）和只能从标准文件读取的应用程序（例如典型的 Web 服务器）中获取信息时，这些将非常有用。bfile 数据类型是相当新的，但在我看来已经过时了：Oracle 8.1（8i）让外部应用程序可以查看数据库中的内容，就好像它是 Windows NT 服务器上的文件一样。那么为什么不将所有内容都保留为 BLOB 并启用 Oracle 的 Internet 文件系统呢？ |

尽管有这么多数据类型，Oracle 还存在一些折磨开发人员的明显缺陷。例如，没有布尔数据类型。需要一个`approved_p`列的开发人员被迫使用`char(1) check(this_column in ('t','f'))`，然后，而不是简洁的查询`where approved_p`，被迫使用`where approved_p = 't'`。

Oracle8 包括有限的能力来创建自己的数据类型。涵盖这些内容超出了本书的范围。请参阅 Oracle8 Server Concepts，[User-Defined Datatypes](http://www.oradoc.com/keyword/user_datatypes)。

#### 表

基础知识：

> ```
>  CREATE TABLE your_table_name ( the_key_column key_data_type PRIMARY KEY, a_regular_column a_data_type, an_important_column a_data_type NOT NULL, ... up to 996 intervening columns in Oracle8 ... the_last_column a_data_type ); 
> ```

即使在上面这个简单的示例中，也有一些值得注意的地方。首先，我喜欢在最顶部定义关键列。其次，`primary key` 约束具有一些强大的效果。它强制`the_key_column`为非空。它会在`the_key_column`上创建一个索引，这会减慢对`your_table_name`的更新速度，但在有人查询具有特定`the_key_column`值的行时，会提高访问速度。Oracle 在插入任何新行时会检查此索引，并在`the_key_column`已经存在具有相同值的行时中止事务。第三，注意在最后一行的定义后没有逗号。如果你粗心大意地留下逗号，Oracle 将给出一个非常令人困惑的错误消息。

如果第一次没有做对，你可能会想要

> ```
>  alter table your_table_name add (new_column_name a_data_type any_constraints); 
> ```

或

> ```
>  alter table your_table_name modify (existing_column_name new_data_type new_constraints); 
> ```

在 Oracle 8i 中，你可以删除一列：

> ```
>  alter table your_table_name drop column existing_column_name; 
> ```

（参见[`www.oradoc.com/keyword/drop_column`](http://www.oradoc.com/keyword/drop_column)）。

如果你仍处于原型阶段，你可能会发现简单地

> ```
>  drop table your_table_name; 
> ```

并重新创建它。随时，你可以通过查询 Oracle 的*数据字典*来查看在数据库中定义的内容：

> ```
>  SQL> select table_name from user_tables order by table_name; TABLE_NAME ------------------------------ ADVS ADV_CATEGORIES ADV_GROUPS ADV_GROUP_MAP ADV_LOG ADV_USER_MAP AD_AUTHORIZED_MAINTAINERS AD_CATEGORIES AD_DOMAINS AD_INTEGRITY_CHECKS BBOARD ... STATIC_CATEGORIES STATIC_PAGES STATIC_PAGE_AUTHORS USERS ... 
> ```

之后，你通常会在 SQL*Plus 中键入`describe table_name_of_interest`：

> ```
>  SQL> describe users; Name Null? Type ------------------------------- -------- ---- USER_ID NOT NULL NUMBER(38) FIRST_NAMES NOT NULL VARCHAR2(100) LAST_NAME NOT NULL VARCHAR2(100) PRIV_NAME NUMBER(38) EMAIL NOT NULL VARCHAR2(100) PRIV_EMAIL NUMBER(38) EMAIL_BOUNCING_P CHAR(1) PASSWORD NOT NULL VARCHAR2(30) URL VARCHAR2(200) ON_VACATION_UNTIL DATE LAST_VISIT DATE SECOND_TO_LAST_VISIT DATE REGISTRATION_DATE DATE REGISTRATION_IP VARCHAR2(50) ADMINISTRATOR_P CHAR(1) DELETED_P CHAR(1) BANNED_P CHAR(1) BANNING_USER NUMBER(38) BANNING_NOTE VARCHAR2(4000) 
> ```

请注意，Oracle 显示的是其内部数据类型，而不是你给定的数据类型，例如，`number(38)` 而不是 `integer`，`varchar2` 而不是指定的 `varchar`。

#### 约束

当你定义表时，可以通过在数据类型后添加一些魔术词来约束单行：

+   `not null`；要求此列有一个值

+   `unique`；两行不能在此列中具有相同的值（在 Oracle 中的副作用：创建索引）

+   `primary key`；与`unique`相同，只是此列不能有空值，其他表可以引用此列

+   `check`；限制列的值范围，例如，`rating integer check(rating > 0 and rating <= 10)`

+   `references`；此列只能包含另一个表的主键列中存在的值，例如，在`bboard`表中，`user_id not null references users` 强制`user_id`列只能指向有效的用户。一个有趣的转折是，你不必为`user_id`指定数据类型；Oracle 会将此列分配给外键具有的数据类型（在本例中为`integer`）。

约束可以应用于多列：

> ```
>  create table static_page_authors ( page_id integer not null references static_pages, user_id integer not null references users, notify_p char(1) default 't' check (notify_p in ('t','f')), unique(page_id,user_id) ); 
> ```

Oracle 允许我们保留具有相同`page_id`的行和具有相同`user_id`的行，但不允许具有两列中相同值的行（这是没有意义的；一个人不能多次成为文档的作者）。假设你运行一个大学的杰出讲座系列。你希望演讲者是其他大学的教授或至少是博士。另一方面，如果有人控制足够的资金，无论是他自己的还是他公司的，他都可以参加。Oracle 随时待命：

> ```
>  create table distinguished_lecturers ( lecturer_id integer primary key, name_and_title varchar(100), personal_wealth number, corporate_wealth number, check (instr(upper(name_and_title),'PHD') <> 0 or instr(upper(name_and_title),'PROFESSOR') <> 0 or (personal_wealth + corporate_wealth) > 1000000000) ); insert into distinguished_lecturers values (1,'Professor Ellen Egghead',-10000,200000); 1 row created. insert into distinguished_lecturers values (2,'Bill Gates, innovator',75000000000,18000000000); 1 row created. insert into distinguished_lecturers values (3,'Joe Average',20000,0); ORA-02290: check constraint (PHOTONET.SYS_C001819) violated 
> ```

正如期望的那样，Oracle 阻止我们向`distinguished_lecturers`表中插入一些随机的普通失败者，但错误消息令人困惑，因为它引用了一个名为"SYS_C001819"的约束，并由 PHOTONET 用户拥有。我们可以在定义时为我们的约束命名：

> ```
>  create table distinguished_lecturers ( lecturer_id integer primary key, name_and_title varchar(100), personal_wealth number, corporate_wealth number, **constraint ensure_truly_distinguished** check (instr(upper(name_and_title),'PHD') <> 0 or instr(upper(name_and_title),'PROFESSOR') <> 0 or (personal_wealth + corporate_wealth) > 1000000000) ); insert into distinguished_lecturers values (3,'Joe Average',20000,0); ORA-02290: check constraint (PHOTONET.ENSURE_TRULY_DISTINGUISHED) violated 
> ```

现在错误消息对应用程序员来说更容易理解。

#### 使用触发器创建更复杂的约束

Oracle 默认的数据约束机制并不总是足够。例如，ArsDigita 社区系统的拍卖模块有一个名为`au_categories`的表。`category_keyword`列是在 URL 中引用类别的唯一简写方式。然而，这一列可能为空，因为它不是表的主键。引用类别的简写方法是可选的。

> ```
>  create table au_categories ( category_id integer primary key, -- shorthand for referring to this category, -- e.g. "bridges", for use in URLs category_keyword varchar(30), -- human-readable name of this category, -- e.g. "All types of bridges" category_name varchar(128) not null ); 
> ```

我们无法向`category_keyword`列添加唯一约束。这将允许表只有一行`category_keyword`为空的情况。因此，我们添加一个触发器，可以执行任意的 PL/SQL 表达式，并在必要时引发错误以阻止插入：

> ```
>  create or replace trigger au_category_unique_tr before insert on au_categories for each row declare existing_count integer; begin select count(*) into existing_count from au_categories where category_keyword = :new.category_keyword; if existing_count > 0 then raise_application_error(-20010, 'Category keywords must be unique if used'); end if; end; 
> ```

此触发器查询表以查找是否已插入任何匹配的关键字。如果有，它调用内置的 Oracle 过程`raise_application_error`来中止事务。

### 正统的 Oracle 宗教

+   Oracle8 服务器应用程序开发人员指南，[选择数据类型](http://www.oradoc.com/keyword/datatype_selection)

+   Oracle8 服务器概念，[内置数据类型](http://www.oradoc.com/keyword/builtin_datatypes)

+   Oracle8 服务器概念，[用户定义数据类型](http://www.oradoc.com/keyword/user_datatypes)

下一步：查询

* * *

[philg@mit.edu](http://philip.greenspun.com/)添加评论
