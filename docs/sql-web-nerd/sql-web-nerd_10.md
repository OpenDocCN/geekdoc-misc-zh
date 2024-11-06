| ![保安人员正在查看新闻。1998 年麻省理工学院毕业典礼。](img/press-check-2.tcl) |
| --- |

## 转向过程化世界

SQL for Web Nerds 的一部分，由[Philip Greenspun](http://philip.greenspun.com/)编写 |

* * *

![1998 年麻省理工学院毕业典礼](img/mit-graduation-stand-on-line-50.tcl) 声明性语言可能非常强大且可靠，但有时以过程化方式思考会更容易。一种方法是在数据库客户端中使用过程化语言。例如，使用 AOLserver 时，我们通常使用 Tcl 编程，这是一种过程化语言，并读取 SQL 查询的结果。例如，在 ArsDigita 社区系统的/news 模块中，我们想要

+   查询当前新闻

+   循环遍历返回的行，并为每一行显示一行（带有指向显示完整故事的页面的链接）

+   对于前三行，查看新闻故事是否非常简短。如果是，就在此页面上显示它

应该让 SQL 程序员思考的上述词语在最后一个项目符号中：*if*和*for the first three rows*。在标准 SQL 中没有清晰的方法来说“只对前 N 行执行此操作”或“如果其数据与某个模式匹配，则为特定行执行某些特殊操作”。

这是 AOLserver Tcl 程序。请注意，根据`news`表项的内容，Tcl 程序可能会执行 SQL 查询（以确定简短新闻项是否有用户评论）。

> ```
>  set selection [ns_db select $db "select * from news where sysdate between release_date and expiration_date and approved_p = 't' order by release_date desc, creation_date desc"] while { [ns_db getrow $db $selection] } { set_variables_after_query # we use the luxury of Tcl to format the date nicely ns_write "<li>[util_AnsiDatetoPrettyDate $release_date]: " if { $counter <= 3 && [string length $body] < 300 } { # it is one of the top three items and it is rather short # so, let's consider displaying it right here # first, let's go back to Oracle to find out if there are any # comments on this item set n_comments [database_to_tcl_string $db_sub "select count(*) from general_comments where on_what_id = $news_id and on_which_table = 'news'"] if { $n_comments > 0 } { # there are some comments; just show the title ns_write "<a href=\"item.tcl?news_id=$news_id\">$title</a>\n" } else { # let's show the whole news item ns_write "$title\n<blockquote>\n[util_maybe_convert_to_html $body $html_p]\n" if [ad_parameter SolicitCommentsP news 1] { ns_write "<br><br>\n<A HREF=\"comment-add.tcl?news_id=$news_id\">comment</a>\n" } ns_write "</blockquote>\n" } } else { ns_write "<a href=\"item.tcl?news_id=$news_id\">$title</a>\n" } } 
> ```

假设您的新闻表中有一百万行，您想要五行，但是您只能通过一点程序逻辑来确定哪五行。把那一百万行数据从数据库服务器传送到客户端应用程序，然后丢弃 999,995 行真的有意义吗？

或者假设您正在查询一个百万行的表，并且希望结果以奇怪的顺序返回。在客户端程序中构建一个百万行数据结构，对它们进行排序，然后将排序后的行返回给用户有意义吗？

访问[`www.scorecard.org/chemical-profiles/`](http://www.scorecard.org/chemical-profiles/)并搜索“苯”。请注意，有 328 种化学品的名称包含字符串“苯”：

> ```
>  select count(*) from chemical where upper(edf_chem_name) like upper('%benzene%'); COUNT(*) ---------- 328 
> ```

我们想要显示它们的方式是

+   在顶部精确匹配

+   换行

+   以查询字符串开头的化学品

+   换行

+   包含查询字符串的化学品

在每一类化学品中，我们希望按字母顺序排序。但是，如果化学品名称前面有数字或特殊字符，则我们希望在排序时忽略这些字符。

您能用一次查询完成所有操作吗？并且让它们以所需顺序从数据库返回吗？

如果您可以在数据库内部运行一个过程，那么您可以。对于每一行，该过程将计算反映匹配好坏的分数。要正确排序，您只需要按照此分数进行排序。要正确处理换行符，您只需要让应用程序程序监视分数的变化。对于对等得分匹配按字母顺序进行微调，只需编写另一个过程，该过程将返回去除前导特殊字符的化学名称，然后按结果排序。看起来是这样的：

> ```
>  select edf_chem_name, edf_substance_id, score_chem_name_match_score(upper(edf_chem_name),upper('%benzene%')) as match_score from chemical where upper(edf_chem_name) like upper('%benzene%'); order by score_chem_name_match_score(upper(edf_chem_name),upper('benzene')), score_chem_name_for_sorting(edf_chem_name) 
> ```

我们指定`score_chem_name_match_score`过程接受两个参数：一个是当前行的化学名称，另一个是用户的查询字符串。对于精确匹配返回 0，对于名称以查询字符串开头的化学品返回 1，其他情况返回 2（请记住，这仅在查询中使用，LIKE 子句确保每个化学名称至少包含查询字符串）。一旦我们定义了这个过程，就可以从 SQL 查询中调用它，就像我们可以调用内置的 SQL 函数`upper`一样。

那么这是可能的吗？是的，在所有“企业级”关系数据库管理系统中。从历史上看，每个 DBMS 都有一种专有的语言用于这些*存储过程*。从 1997 年开始，DBMS 公司开始在数据库服务器中加入 Java 字节码解释器。Oracle 在 1999 年 2 月的 8.1 版本中添加了 Java 在服务器中的功能。但是，如果您正在查看旧系统，例如 Scorecard，您将看到 Oracle 古老的 PL/SQL 语言中的过程：

> ```
>  create or replace function score_chem_name_match_score (chem_name IN varchar, query_string IN varchar) return integer AS BEGIN IF chem_name = query_string THEN return 0; ELSIF instr(chem_name,query_string) = 1 THEN return 1; ELSE return 2; END IF; END score_chem_name_match_score; 
> ```

请注意，PL/SQL 是一种强类型语言。我们声明我们期望的参数是什么，它们是 IN 还是 OUT，以及它们必须是什么类型。我们说`score_chem_name_match_score`将返回一个整数。我们可以说 PL/SQL 变量应该与表中的列具有相同的类型：

> ```
>  create or replace function score_chem_name_for_sorting (chem_name IN varchar) return varchar AS stripped_chem_name chem_hazid_ref.edf_chem_name%TYPE; BEGIN stripped_chem_name := ltrim(chem_name,'1234567890-+()[],'' #'); return stripped_chem_name; END score_chem_name_for_sorting; 
> ```

本地变量`stripped_chem_name`将与`chem_hazid_ref`表中的`edf_chem_name`列具有相同的类型。

如果您正在使用 Oracle 应用程序 SQL*Plus 定义 PL/SQL 函数，您必须用只包含字符“/”的行终止每个定义。如果 SQL*Plus 报告在评估您的定义时出现错误，那么如果您想要更多解释，您必须键入“show errors”。除非您期望始终编写完美的代码，否则将这些 SQL*Plus 咒语留在您的.sql 文件中可能会很方便。这里是一个例子：

> ```
>  -- note that we prefix the incoming arg with v_ to keep it -- distinguishable from the database column of the same name -- this is a common PL/SQL convention create or replace function user_group_name_from_id (v_group_id IN integer) return varchar IS -- instead of worrying about how many characters to -- allocate for this local variable, we just tell -- Oracle "make it the same type as the group_name -- column in the user_groups table" v_group_name user_groups.group_name%TYPE; BEGIN if v_group_id is null then return ''; end if; -- note the usage of INTO below, which pulls a column -- from the table into a local variable select group_name into v_group_name from user_groups where group_id = v_group_id; return v_group_name; END; / show errors 
> ```

### 在 PL/SQL 和 Java 之间进行选择

如何在 PL/SQL 和 Java 之间进行选择？很简单：您无法选择。在许多重要的地方，例如触发器，Oracle 强制您指定 PL/SQL 块。因此，您必须至少学习 PL/SQL 的基础知识。如果您要构建重要的包，Java 可能是一个更好的长期选择。

### 参考

+   概述：Oracle8 服务器应用程序开发人员指南，“使用过程和包”位于[`www.oradoc.com/keyword/using_procedures_and_packages`](http://www.oradoc.com/keyword/using_procedures_and_packages)

+   PL/SQL 用户指南和参考资料位于[`www.oradoc.com/keyword/plsql`](http://www.oradoc.com/keyword/plsql)

+   Java 存储过程开发人员指南位于[`www.oradoc.com/keyword/java_stored_procedures`](http://www.oradoc.com/keyword/java_stored_procedures)

下一步：trees

* * *

[philg@mit.edu](http://philip.greenspun.com/)添加评论
