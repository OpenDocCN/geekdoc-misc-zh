| ![查尔斯赛艇赛，1998 年 10 月 18 日星期日。从步行桥到哈佛商学院](img/hoc-10.tcl) |
| --- |

## 附录 B：使用 Oracle 完成真正的工作

由[菲利普·格林斯潘](http://philip.greenspun.com/)撰写，属于 Web 书呆子的 SQL |

* * *

考虑约翰·Q·书呆子，他拥有真正的 SQL 专业知识和麻省理工学院的博士学位。约翰能从 Oracle 中获得多少有用的工作？没有。约翰·Q·书呆子只知道如何从 SQL*Plus 中操作 Oracle。本附录涵盖了一些小细节，比如如何将数据导入或导出 Oracle。它被组织成一个常见问题解答。

### 如何将数据导入 Oracle？

+   答案 1：启动 SQL*Plus。快速输入。

+   答案 2：如果你需要每秒加载 1000+ 行，这在数据仓库领域是一个相当常见的需求，请阅读 Oracle8 服务器实用程序，[SQL*Loader 部分](http://www.oradoc.com/keyword/sql_loader)。

+   答案 3：如果 SQL*Loader 让你感觉像要拔光头发一样，那就使用 Perl DBD/DBI（一个可从 [`www.cpan.org`](http://www.cpan.org) 获取的模块；在 [高级 Perl 编程](http://www.amazon.com/exec/obidos/ASIN/1565922204/pgreenspun-20) 中有解释（Srinivasan 1997; O'Reilly)。

+   答案 4：如果你的数据被困在另一个关系数据库管理系统中，请考虑使用诸如 Data Junction ([`www.datajunction.com`](http://www.datajunction.com)) 这样的高级 GUI 工具。这些是基于 PC 的应用程序，可以同时打开到你的 Oracle 数据库和其他关系数据库管理系统的连接。它们通常可以显示其他数据库中可用的内容，并将你认为必要的内容拖放到 Oracle 中。

+   答案 5：如果你的数据在另一个 Oracle 数据库中，请阅读 Oracle 服务器实用程序手册中关于 `exp` 和 `imp` 的内容（[`www.oradoc.com/keyword/export_import`](http://www.oradoc.com/keyword/export_import)）。

+   答案 6：如果你的数据来自电子邮件，配置你的邮件客户端以分叉一个 Perl DBD/DBI 脚本，然后解析出头部和其他杂乱内容，打开 Oracle，然后发送一个插入语句。由于分叉和打开 Oracle，这比在具有数据库连接池的线程化 Web 服务器中运行的 Web 脚本效率低 1/100。但是，你可能不会每秒收到 40 封电子邮件，所以这并不重要。旧的开源 ArsDigita 社区系统包括一个 Perl 脚本，你可以用作起点。详情请参见 `philip.greenspun.com/ancient-history/software/acs-3.4.10.tar.tgz`。

### 如何从 Oracle 中获取数据？

+   如果你想在网上发布数据，请查看菲利普和亚历克斯的网络发布指南第十三章中阐述的方法（`philip.greenspun.com/panda/databases-interfacing`）。

+   如果您要将数据发送到另一个 Oracle 安装，请使用`exp`，在 Oracle8 Server Utilities 手册的[`exp`和`imp`部分](http://www.oradoc.com/keyword/export_import)有文档记录。

* * *

[philg@mit.edu](http://philip.greenspun.com/) 添加评论
