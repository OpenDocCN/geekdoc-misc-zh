| ![](img/17-17.tcl) |
| --- |

## 外部和遗留数据

部分来自 Web 网络爱好者的 SQL（本章由 Michael Booth 和[Philip Greenspun](http://philip.greenspun.com/)编写）|

* * *

![](img/1-1.tcl) 世界上大部分有用的数据要么存储在您无法控制的服务器上，要么存储在除 Oracle 之外的数据库管理系统中。无论哪种方式，从本地 Oracle 数据库的角度来看，我们将这些数据称为*外部数据*。您的目标始终是相同的：**将外部数据视为存储在本地 SQL 表中一样处理**。

将外部数据物理或虚拟地拖回您的 Oracle 洞穴的好处如下：

+   新开发人员不必考虑数据来自何处。

+   开发人员可以使用他们每天使用的相同查询语言处理外部数据：SQL。

+   开发人员可以使用他们每天使用的相同编程工具和系统。他们可能使用 COBOL，他们可能使用 C，他们可能使用 Java，他们可能使用 Common Lisp，他们可能使用 Perl 或 Tcl，但您可以肯定他们已经学会如何从这些工具向 Oracle 发送 SQL 查询，因此他们将能够使用外部数据。

一个很好的概念性方式来看待我们试图实现的目标是构建外部数据的 SQL 视图。标准的 SQL 视图可能会对初学者程序员隐藏一个 5 路连接。*外部表*隐藏了数据来自外部来源的事实。

我们将使外部数据在本地可用的系统称为*聚合架构*。在设计个体聚合架构时，您需要解决以下问题：

1.  一致性：您的数据的本地版本与外部数据不同步是否可以接受？如果可以，程度如何？

1.  可更新性：您的本地视图是否可更新？即，程序员是否可以通过更新本地视图在外部数据库管理系统上执行事务？

1.  社交：外部数据提供者愿意让您进入他或她的数据库的程度如何？

### 退化聚合

如果外部数据存储在 Oracle 数据库中，并且管理该数据库的人员愿意合作，您可以练习一种退化形式的聚合：Oracle 到 Oracle 的通信。

最退化的退化聚合形式是当外部数据位于同一 Oracle 安装中但由不同用户拥有时。具体来说，假设您在 Eli Lilly 公司的数据仓库部门工作，该部门隶属于市场营销部门。您的 Oracle 用户名是"marketing"。您感兴趣的外部数据位于由"sales"用户拥有的`prozac_orders`表中。在这种情况下，您的聚合架构如下：

1.  以外部数据所有者（sales）的身份连接到 Oracle 并授予 MARKETING 对 PROZAC_ORDERS 的 SELECT 权限

1.  作为本地用户（marketing）连接到 Oracle 并键入 SELECT * FROM SALES.PROZAC_ORDERS

完成。

### 稍微不那么退化的聚合

现在想象一下，Prozac 订单是在专用的在线事务处理（OLTP）数据库安装上处理的，而您的数据仓库（DW）在一个物理上独立的计算机上运行。OLTP 和 DW 系统都在运行 Oracle 数据库服务器，并通过网络连接。您需要采取以下步骤：

1.  在 OLTP 系统上设置 SQL*Net (Net8)

1.  设置 DW Oracle 服务器作为 OLTP 服务器的客户端。如果您没有使用 Oracle 命名服务，您必须编辑 $ORACLE_HOME/network/admin/tnsnames.ora 文件以引用 OLTP 系统。

1.  在 OLTP 系统上创建一个名为"marketing"的用户

1.  在 OLTP 系统上，以"sales"身份登录并授予 MARKETING 对 PROZAC_ORDERS 的 SELECT 权限

1.  在 DW 系统上，创建一个名为"OLTP"的到 OLTP 系统的数据库链接：CREATE DATABASE LINK OLTP CONNECT TO MARKETING IDENTIFIED BY *marketing 的密码* USING 'OLTP';

1.  在 DW 系统上，以"marketing"身份登录并键入 SELECT * FROM SALES.PROZAC_ORDERS@OLTP;

在这两种退化情况下，没有一致性问题。外部数据是实时从其规范数据库中查询的。这是因为社会协议的存在。外部数据的所有者愿意授予您无限访问权限。同样，社会问题决定了可更新性问题。只有在 SELECT 上授予权限，外部表才不可更新。

### 非 Oracle-Oracle 聚合

如果外部数据没有存储在 Oracle 数据库中，或者虽然存储在其中但您无法说服所有者给您访问权限，那该怎么办？您将需要一种计算机程序，它知道如何获取部分或全部外部数据并将其填充到本地的 Oracle 表中。让我们从一个具体的例子开始。

假设您在硅谷蓝十字工作。维度数据仓库揭示了股市困境和临床抑郁之间的强烈相关性。在股票波动较大的新上市公司工作的人在他们的虚拟财富被证明是虚幻时往往会陷入沮丧。蓝十字的人认为，他们可以通过在被保险人的雇主股票在一天内下跌超过 10% 时自动开具 Prozac 处方来节省医疗费用和医生就诊次数。要找到开心药丸的候选人，以下查询应该足够：

> ```
> select patients.first_names, patients.last_name, stock_quotes.percent_change
> from patients, employers, stock_quotes
> where patients.employer_id = employers.employer_id
> and employers.ticker_symbol = stock_quotes.ticker_symbol
> and stock_quotes.percent_change < -0.10
> order by stock_quotes.percent_change
> 
> ```

`stock_quotes` 表在这里是外部表。Blue Cross 没有运营股票交易所。因此，权威的价格变动数据必须从外部来源获取。想象一下，外部来源是 http://quote.yahoo.com/。对于像 Ariba（股票代码 ARBA）这样的软件公司，我们需要在 Web 浏览器中访问 [`quote.yahoo.com/q?s=arba`](http://quote.yahoo.com/q?s=arba) 来获取报价。这是使用带有形式变量 "s" 的参数 "arba" 调用方法 "q"。结果以人类可读的 HTML 页面的形式返回，其中包含大量的呈现标记和英文文本。如果 Yahoo 给我们提供机器可读的结果会更方便，例如，以逗号分隔的值列表或 XML 文档。但是，只要 HTML 页面的结构不因报价而变化，并且百分比变化数字可以用正则表达式或其他计算机程序提取出来，它仍然可以使用。

设计此问题的聚合架构时有哪些问题？首先是一致性。拥有最新的股票报价会很好，但另一方面，反复查询相同的符号似乎有点愚蠢。实际上，在美国股市关闭后的东部时间下午 4:30 之后，没有任何理由在第二天上午 9:30 之前询问相同的符号的新报价。在对缓存做出一些合理假设后，一旦 `stock_quotes` 表被使用了几次，查询将能够执行得更快，因为报价数据将从本地缓存中提取，而不是从互联网上获取。

我们不必过多考虑可更新性。Blue Cross 不经营股票交易所，因此 Blue Cross 无法更新股票价格。我们的本地视图将不可更新。

这个社会问题乍看起来很简单。Yahoo 可以向公共互联网上的任何客户提供报价。乍一看，我们的计算机程序似乎只能一次请求一个报价。然而，如果我们获取 [`quote.yahoo.com/q?s=arba**+ibm**`](http://quote.yahoo.com/q?s=arba+ibm)，我们可以同时获得两个报价。甚至可能一次性获取所有被保险人的雇主的股价，放在一个大页面上。一个潜在的麻烦在于 Yahoo 在其服务条款 [`docs.yahoo.com/info/terms/`](http://docs.yahoo.com/info/terms/) 中规定了。

> ```
> 10\. NO RESALE OF SERVICE
> 
> You agree not to reproduce, duplicate, copy, sell, resell or exploit for
> any commercial purposes, any portion of the Service, use of the Service,
> or access to the Service.
> 
> ```

#### 我们的程序在哪里和何时运行

我们需要编写一个计算机程序（“抓取程序”），它可以从 Yahoo 获取 HTML 页面，提取价格变动数据，并将其放入 `stock_quotes` 表中。我们还需要一个更通用的计算机程序（“检查程序”），它可以查看所需的外部数据，查看 `stock_quotes` 中缓存数据的年龄，并在必要时运行抓取程序。

Oracle 内置了三种图灵完备的计算机语言：C、Java、PL/SQL。“图灵完备”意味着可以为任何计算机编写的任何程序都可以编写为在 Oracle 内运行。由于最终希望将外部数据与 Oracle 内部数据结合起来，因此在数据库内运行所有聚合代码是有意义的。Oracle 包含了用于方便检索 Web 页面的内置函数（参见 [`oradoc.photo.net/ora816/server.816/a76936/utl_http.htm#998100`](http://oradoc.photo.net/ora816/server.816/a76936/utl_http.htm#998100)）。

在理想的世界中，您可以定义一个数据库触发器，每次查询将要从 `stock_quotes` 表中选择时触发。这个触发器将以某种方式找出需要哪些行的外部表。它将运行检查程序，以确保缓存的数据都不太旧，而检查程序可能反过来会运行抓取程序。

为什么这不起作用？截至 Oracle 版本 8.1.6，无法定义对 SELECT 的触发器。即使可以，触发程序也无法探索正在执行的 SQL 查询或询问 SQL 优化器将要求哪些行。

PostgreSQL 关系型数据库管理系统具有一个“规则系统”（参见 [`www.postgresql.org/docs/programmer/x968.htm`](http://www.postgresql.org/docs/programmer/x968.htm)），它可以拦截和转换 SELECT 查询。它接收 SQL 解析器的输出，应用一个或多个转换规则，并产生一组新的要执行的查询。例如，一条规则可能指定任何针对表“foo”的 SELECT 应该改为从表“bar”中进行 SELECT；这就是 Postgres 实现视图的方式。目前，对 SELECT 可应用的唯一转换是用单个替代 SELECT 替换它 - 但 PostgreSQL 是开源软件，任何人都可以自由增强它。

长期的解决方案是等待关系型数据库管理系统供应商增强其产品。帮助即将到来。好消息是，ANSI/ISO SQL-99 标准的一部分要求关系型数据库管理系统供应商，包括 Oracle，在外部数据源上提供支持。坏消息是，SQL-99 标准正在分阶段发布，包装器扩展将在 2001 年之前发布，并且可能需要几年时间才能商业关系型数据库管理系统实现新标准。

短期的解决方案是在将查询发送到 Oracle 之前运行一个过程：

> ```
> call checker.stock_quotes( 0.5 )
> 
> select patients.first_names, patients.last_name, stock_quotes.percent_change ...
> 
> ```

我们的检查器是一个名为`checker.stock_quotes`的 Oracle 存储过程。它检查`stock_quotes`中的每个股票代码，并在报价比指定的时间间隔（以天为单位）旧时调用获取器。如果我们想要向表中添加一个新的`ticker_symbol`，我们调用一个不同版本的`checker.stock_quotes`：

> ```
> call checker.stock_quotes( 0.5, 'IBM' )
> 
> ```

如果没有半天内更新的 IBM 条目，检查器将要求获取 IBM 的股票报价。

### 聚合示例

在 Oracle 实现 SQL-99 包装器扩展之前，Blue Cross 将提供大量 Prozac。因此，让我们构建一个使用 Java 存储过程来执行检查和获取的`stock_quotes`外部表。我们将从数据模型开始：

> ```
> create table stock_quotes (
> 	ticker_symbol		varchar(20) primary key,
> 	last_trade		number,
>         -- the time when the last trade occurred (reported by Yahoo)
> 	last_trade_time		date,
> 	percent_change 		number,
>         -- the time when we pulled this data from Yahoo
> 	last_modified		date not null	
> );
> 
> ```

这是一个简化版本，我们只存储每个股票代码的最新价格报价。在实际应用程序中，我们肯定希望维护一个旧报价的存档，也许可以使用触发器在更新`stock_quotes`时填充审计表。即使您的外部来源提供其自己的历史记录，获取它们也比从自己的审计表中获取数据慢、不可靠且更复杂。

我们将创建一个单独的源代码文件，`StockUpdater.java`。Oracle 8.1.6 包括一个 Java 编译器以及一个虚拟机，因此当这个文件准备好时，我们可以将其加载到 Oracle 中，并用一个命令编译它：

> ```
> bash-2.03$ loadjava -user *username/password* -resolve -force StockUpdater.java
>     ORA-29535: source requires recompilation
>     StockUpdater:171: Class Perl5Util not found.
>     StockUpdater:171: Class Perl5Util not found.
>     StockUpdater:218: Class PatternMatcherInput not found.
>     StockUpdater:218: Class PatternMatcherInput not found.
>      Info: 4 errors
> loadjava: 6 errors
> bash-2.03$ 
> 
> ```

噢。`-resolve`选项告诉 Oracle 的`loadjava`实用程序立即编译和链接类，但`StockUpdater`依赖于尚未加载到 Oracle 中的类。大多数 Java 虚拟机都设计成通过搜索文件系统在运行时自动定位和加载类，但 Oracle JVM 要求预先将每个类加载到数据库中。

我们需要获取`Perl5Util`和`PatternMatcherInput`类。这些是 Oro 库的一部分，一个开源的正则表达式库，可以从[`jakarta.apache.org/oro/index.html`](http://jakarta.apache.org/oro/index.html)获取。当我们下载并解压分发时，会找到一个包含我们所需类的 JAR 文件。我们将整个 JAR 文件加载到 Oracle 中，然后再尝试加载`StockUpdater`。

> ```
> bash-2.03$ loadjava -user *username/password* -resolve jakarta-oro-2.0.jar
> bash-2.03$ loadjava -user *username/password* -resolve -force StockUpdater.java
> bash-2.03$ 
> 
> ```

这些命令执行需要一段时间。完成后，我们可以通过运行以下 SQL 查询来检查结果：

> ```
> SELECT RPAD(object_name,31) ||
>        RPAD(object_type,14) ||
>        RPAD(status,8)
>        "Java User Objects"
>   FROM user_objects
>  WHERE object_type LIKE 'JAVA %';
> 
> ```

这是查询的输出的一小部分：

> ```
> Java User Objects
> ----------------------------------------------------
> StockUpdater		       JAVA CLASS    VALID
> StockUpdater		       JAVA SOURCE   VALID
> org/apache/oro/text/awk/OrNode JAVA CLASS    VALID
> org/apache/oro/text/regex/Util JAVA CLASS    VALID
> org/apache/oro/util/Cache      JAVA CLASS    VALID
> org/apache/oro/util/CacheFIFO  JAVA CLASS    VALID
> ...
> 
> ```

我们的源代码标记为`VALID`，并且有一个关联的类也是`VALID`。还有一堆`VALID`正则表达式类。一切正常。

如果我们愿意，我们可以使用独立的 Java 编译器编译`StockUpdater`类，然后将生成的类文件加载到 Oracle 中。我们不需要使用内置的 Oracle 编译器。

`-force`选项强制`loadjava`覆盖任何具有相同名称的现有类，因此如果我们更改我们的类，则不一定需要在加载新类之前删除旧版本。如果我们确实想删除 Oracle 的存储 Java 类之一，我们可以使用`dropjava`实用程序。

#### 调用我们的存储过程

![聚合架构的图示](img/agg-arch.gif)

> **图 15-1**：聚合架构。客户端应用程序通过使用 SQL 查询 Oracle 表来获取数据。为了保持外部表的最新状态，应用程序调用运行在 Oracle 内部的 Java 存储过程 Checker 和 Fetcher。Checker 通过两层 PL/SQL 调用：一层是将 PL/SQL 调用转换为 Java 调用的调用规范，另一层是提供自主事务以运行聚合代码的包装过程。

为了从 SQL 调用 Java 存储过程，我们需要定义*调用规范*，这是静态 Java 方法的 PL/SQL 前端。以下是一个调用规范的示例：

> ```
>     PROCEDURE stock_quotes_spec ( interval IN number )
>       	AS LANGUAGE JAVA
>       	NAME 'StockUpdater.checkAll( double )';
> 
> ```

这段代码的含义是：“当程序员调用这个 PL/SQL 过程时，调用 Java 类`StockUpdater`的`checkAll`方法。” `checkAll`方法必须是`static`的：Oracle 不会自动构造一个新的`StockUpdater`对象。

我们不允许开发人员直接使用调用规范。相反，我们让他们调用一个单独的 PL/SQL 过程来启动*自主事务*。我们需要这样做是因为应用程序可能在一个大事务中调用检查器。检查器使用获取器向`stock_quotes`表添加新数据。现在问题是：何时提交对`stock_quotes`表的更改？有三种选择：

1.  使获取器发出 COMMIT。这将提交对`stock_quotes`的更改。它还将提交在调用检查器之前进行的任何更改。这是一个非常糟糕的主意。

1.  使获取器更新`stock_quotes`而不发出 COMMIT。这也是一个不好的主意：如果调用例程决定中止事务，则新的股票报价数据将丢失。

1.  在独立的事务中运行检查器和获取器。获取器可以提交或回滚更改，而不会影响主事务。Oracle 为此提供了`AUTONOMOUS_TRANSACTION`声明，但该声明在调用规范中不起作用 - 它仅适用于常规的 PL/SQL 过程。因此，我们需要一个单独的粘合代码层来启动自主事务。

这里是定义所有 PL/SQL 过程的 SQL 代码：

> ```
> CREATE OR REPLACE PACKAGE checker AS
>     PROCEDURE stock_quotes( interval IN number );
>     PROCEDURE stock_quotes( interval IN number, ticker_symbol IN varchar );
> END checker;
> /
> show errors
> 
> CREATE OR REPLACE PACKAGE BODY checker AS
> 
>     -- Autonomous transaction wrappers
>     PROCEDURE stock_quotes ( interval IN number )
>     IS
>         PRAGMA AUTONOMOUS_TRANSACTION;
>     BEGIN
>         stock_quotes_spec( interval );
>     END;
>     
>     PROCEDURE stock_quotes ( interval IN number, ticker_symbol IN varchar )
>     IS
>         PRAGMA AUTONOMOUS_TRANSACTION;
>     BEGIN
>         stock_quotes_spec( interval, ticker_symbol );
>     END;
> 
>     -- Call specs
>     PROCEDURE stock_quotes_spec ( interval IN number )
>       	AS LANGUAGE JAVA
>       	NAME 'StockUpdater.checkAll( double )';
>     
>     PROCEDURE stock_quotes_spec ( interval IN number, ticker_symbol IN varchar )
>       	AS LANGUAGE JAVA
>       	NAME 'StockUpdater.checkOne( double, java.lang.String )';
> 
> END checker;
> /
> show errors
> 
> ```

我们将这些例程放在一个名为`checker`的*包*中。包允许我们将过程和数据类型分组在一起。我们在这里使用一个包是因为打包的过程定义可以*重载*。`checker.stock_quotes`过程可以使用一个或两个参数调用，并且在每种情况下将运行不同版本。`stock_quotes_spec`过程也有两个版本。

#### 在 Java 中编写一个 Checker

我们准备开始查看 `StockUpdater.java` 文件本身。它以典型的 Java 方式开始：

> ```
> // Standard Java2 classes, already included in Oracle
> import java.sql.*;
> import java.util.*;
> import java.io.*;
> import java.net.*;
> 
> // Regular expression classes
> import org.apache.oro.text.perl.*;
> import org.apache.oro.text.regex.*;
> 
> public class StockUpdater {
> 
> ```

然后我们有两个检查例程，首先是更新整个表格的例程：

> ```
>     public static void checkAll( double interval ) 
>     throws SQLException {
> 	
> 	// Query the database for the ticker symbols that haven't
> 	// been updated recently
> 	String sql = new String( "SELECT ticker_symbol " +
>                                  "FROM stock_quotes " +
> 				 "WHERE (sysdate - last_modified) > " + 
> 				    String.valueOf( interval ) );
> 
> 	// Build a Java List of the ticker symbols
> 
> 	// Use JDBC to execute the given SQL query.
> 	Connection conn = getConnection();
> 	Statement stmt = conn.createStatement();
> 	stmt.execute( sql );
> 	ResultSet res = stmt.getResultSet();
> 	
> 	// Go through each row of the result set and accumulate a list
> 	List tickerList = new ArrayList();
> 	while ( res.next() ) {
> 	    String symbol = res.getString( "ticker_symbol" );
> 	    if ( symbol != null ) {
> 		tickerList.add( symbol );
> 	    }
> 	}
> 	stmt.close();
> 
> 	System.out.println( "Found a list of " + tickerList.size() + " symbols.");
> 		
> 	// Pass the List of symbols on to the fetcher
> 	fetchList( tickerList );
>     }
> 
> ```

这个例程使用 JDBC 访问 `stock_quotes` 表。JDBC 调用会抛出 `SQLException` 类型的异常，我们不需要捕获它们；相反，我们将它们传播回调用程序员，以指示出现了问题。我们还会将调试信息打印到标准输出。当在 Oracle 外部运行这个类时，调试消息将显示在屏幕上。在 Oracle 内部，我们可以提前发出一些 SQL*Plus 命令来查看它们：

> ```
> SET SERVEROUTPUT ON
> CALL dbms_java.set_output(5000);
> 
> ```

标准输出将被回显到屏幕上，每次回显 5000 个字符。

第二个检查例程逐个处理一个股票代码，并用于将一个新的股票代码添加到表中：

> ```
>     public static void checkOne( double interval, String tickerSymbol ) 
>     throws SQLException {
> 
>         // Set up a list in case we need it
>         List tickerList = new ArrayList();
> 	tickerList.add( tickerSymbol );
> 
> 	// Query the database to see if there's recent data for this tickerSymbol
> 	String sql = new String( "SELECT " +
>                                  "  ticker_symbol, " +
>                                  "  (sysdate - last_modified) as staleness " +
> 				 "FROM stock_quotes " +
> 				 "WHERE ticker_symbol = '" + tickerSymbol + "'");
> 	Connection conn = getConnection();
> 	Statement stmt = conn.createStatement();
> 	stmt.execute( sql );
> 	ResultSet res = stmt.getResultSet();
> 	
> 	if ( res.next() ) {
> 	    // A row came back, so the ticker is in the DB
> 	    // Is the data recent?
> 	    if ( res.getDouble("staleness") > interval ) {
> 		// Fetch fresh data
> 		fetchList( tickerList );
> 	    }
> 
> 	} else {
> 	    // The stock isn't in the database yet
> 	    // Insert a blank entry
> 	    stmt.executeUpdate( "INSERT INTO stock_quotes " +
> 				"(ticker_symbol, last_modified) VALUES " +
> 				"('" + tickerSymbol + "', sysdate)" );
> 	    conn.commit();
> 	    
> 	    // Now refresh the blank entry to turn it into a real entry
>             fetchList( tickerList );
> 	}
> 	stmt.close();
>     }
> 
> ```

#### 在 Java 中编写一个抓取器

抓取器被实现为一个名为 `fetchList` 的长 Java 方法。它首先从雅虎那里检索一个网页。为了速度和简单起见，我们从一个页面中提取所有的股票报价。

> ```
>     /** Accepts a list of stock tickers and retrieves stock quotes from Yahoo Finance
> 	at http://quote.yahoo.com/
>     */
>     private static void fetchList( List tickerList ) 
>     throws SQLException {
> 	
> 	// We need to pass Yahoo a string containing ticker symbols separated by "+"
> 	String tickerListStr = joinList( tickerList, "+" );
> 
> 	if ( tickerListStr.length() == 0 ) {
> 	    // We don't bother to fetch a page if there are no ticker symbols
> 	    System.out.println("Fetcher: no ticker symbols were supplied");
> 	    return;
> 	}
> 
> 	try {
> 	    // Go get the Web page
> 	    String url = "http://quote.yahoo.com/q?s=" + tickerListStr;
> 	    String yahooPage = getPage( url );
> 
> ```

抓取器使用一个名为 `getPage` 的辅助函数来检索雅虎的 HTML，我们将其塞入 `yahooPage` 变量中。现在我们可以使用 Perl 5 正则表达式来提取我们需要的值。我们创建一个新的 `Perl5Util` 对象，并使用 `split()` 和 `match()` 方法来提取页面中数据的部分：

> ```
>             // ... continuing the definition of fetchList ...
> 
> 	    // Get a regular expression matcher
> 	    Perl5Util regexp = new Perl5Util();
> 
> 	    // Break the page into sections using </table> tags as boundaries
> 	    Vector allSections = regexp.split( "/<\\/table>/", yahooPage );
> 
> 	    // Pick out the section which contains the word "Symbol"
> 	    String dataSection = "";
> 	    boolean foundSymbolP = false;
> 	    Iterator iter = allSections.iterator();
> 	    while ( iter.hasNext() ) {
> 		dataSection = (String) iter.next();
> 		if ( regexp.match( "/<th.*?>Symbol<\\/th>/", dataSection )) {
> 		    foundSymbolP = true;
> 		    break;
> 		}
> 	    }
> 
> 	    // If we didn't find the section we wanted, throw an error
> 	    if ( ! foundSymbolP ) {
> 		throw new SQLException( "Couldn't find the word 'Symbol' in " + url );
> 	    }
> 
> ```

我们需要从页面中提取出今天的日期。这是页面被检索时的日期，我们称之为“抓取日期”。每个股票报价也有一个独立的时间戳，我们称之为“报价日期”。我们使用我们自己的一个小类 (`OracleDate`) 来表示日期，并使用一个辅助函数 (`matchFetchDate`) 来执行正则表达式匹配。

> ```
> 	    OracleDate fetchDate = matchFetchDate( dataSection );
> 	    if ( fetchDate == null ) {
> 		throw new SQLException("Couldn't find the date in " + url);
> 	    }
> 	    System.out.println("The date appears to be: '" + fetchDate.getDate() + "'");	    
> 
> ```

如果我们无法匹配到抓取日期，我们会抛出一个异常，告诉客户端程序员抓取器没有工作。也许是网络出了问题，或者雅虎的服务器出了故障，或者雅虎的图形设计师决定重新设计页面布局。

我们准备提取股票报价本身。它们在一个 HTML 表格中，每个报价一行。我们设置了一个单独的 JDBC 语句，它将一遍又一遍地执行，使用占位符来表示数据：

> ```
> 	    String update_sql = "UPDATE stock_quotes SET " + 
> 		"last_trade = ?, " +
> 		"last_trade_time = to_date(?, ?), " +
> 		"percent_change = ?, " +
> 		"last_modified = sysdate " +
> 		"WHERE ticker_symbol = ? ";
> 	    Connection conn = getConnection();
> 	    PreparedStatement stmt = conn.prepareStatement( update_sql );
> 
> ```

现在我们逐行分析 HTML 表格，使用一个巨大的正则表达式来表示整个表格行。通过使用 `PatternMatcherInput` 对象，我们可以让 `regexp.match()` 遍历 `dataSection` 字符串，并返回一个接一个的匹配，直到没有更多匹配为止。对于我们找到的每一个股票报价，我们会清理数据并执行数据库插入操作。

> ```
> 	    // Use a special object to make the regexp search run repeatedly
> 	    PatternMatcherInput matchInput = new PatternMatcherInput( dataSection );
> 
> 	    // Search for one table row after another
> 	    while ( regexp.match( "/<tr.*?>.*?" +
> 				  "<td nowrap.*?>(.*?)<\\/td>.*?" + 
> 				  "<td nowrap.*?>(.*?)<\\/td>.*?" + 
> 				  "<td nowrap.*?>(.*?)<\\/td>.*?" + 
> 				  "<td nowrap.*?>(.*?)<\\/td>.*?" + 
> 				  "<td nowrap.*?>(.*?)<\\/td>.*?" + 
> 				  "<\\/tr>/s" , matchInput )) {
> 		// Save the regexp groups into variables
> 		String tickerSymbol = regexp.group(1);
> 		String timeStr = regexp.group(2);
> 		String lastTrade = regexp.group(3);
> 		String percentChange = regexp.group(5);
> 
> 		// Filter the HTML from the ticker symbol		
> 		tickerSymbol = regexp.substitute("s/<.*?>//g", tickerSymbol);
> 		stmt.setString( 5, tickerSymbol );
> 
> 		// Parse the time stamp
> 		OracleDate quoteDate = matchQuoteDate( timeStr, fetchDate );
> 		if ( quoteDate == null ) {
> 		    throw new SQLException("Bad date format");
> 		}
> 		stmt.setString( 2, quoteDate.getDate() );
> 		stmt.setString( 3, quoteDate.getDateFormat() );
> 		
> 		// Parse the lastTrade value, which may be a fraction
> 		stmt.setFloat( 1, parseFraction( lastTrade ));
> 
> 		// Filter HTML out of percentChange, and remove the % sign
> 		percentChange = regexp.substitute( "s/<.*?>//g", percentChange);
> 		percentChange = regexp.substitute( "s/%//g", percentChange);
> 		stmt.setFloat( 4, Float.parseFloat( percentChange ));
> 
> 		// Do the database update
> 		stmt.execute();
> 	    }
> 
> 	    stmt.close();
>             // Commit the changes to the database
> 	    conn.commit();
> 
> 	} catch ( Exception e ) { 
> 	    throw new SQLException( e.toString() );
> 	}
>     } // End of the fetchList method
> 
> ```

#### 抓取器的辅助例程

抓取器使用 `getPage` 方法加载 HTML 页面，该方法使用 Java 标准库中的 `URL` 类。对于一个简单的 HTTP GET，这个例程就是我们需要的。

> ```
>     /** Fetch the text of a Web page using HTTP GET
>      */
>     private static String getPage( String urlString ) 
>     throws MalformedURLException, IOException {
> 	URL url = new URL( urlString );
> 	BufferedReader pageReader = 
> 	    new BufferedReader( new InputStreamReader( url.openStream() ) );
> 	String oneLine;
> 	String page = new String();
> 	while ( (oneLine = pageReader.readLine()) != null ) {
> 	    page += oneLine + "\n";
> 	}
> 	return page;
>     }
> 
> ```

日期及其 Oracle 格式字符串存储在`OracleDate`对象中。 `OracleDate`是一个“内部类”，定义在 StockUpdater 类内部。 因为它是一个私有类，所以在 StockUpdater 之外看不到或使用它。 如果以后我们认为`OracleDate`对其他程序员有用，我们可以通过将定义移动到自己的文件中将其转换为公共类。

> ```
>     /** A class which represents Oracle timestamps. */
>     private static class OracleDate {
> 	/** A string representation of the date */	
> 	private String date;
> 	/** The date format, in Oracle's notation */
> 	private String dateFormat;
> 
> 	/** Methods for accessing the date and the format */
> 	String getDate() { return date; }
> 	String getDateFormat() { return dateFormat; }
> 	void setDate( String newDate ) { date = newDate; }
> 	void setDateFormat( String newFormat ) { dateFormat = newFormat; }
> 
> 	/** A constructor that builds a new OracleDate */
> 	OracleDate( String newDate, String newFormat ) {
> 	    setDate( newDate );
> 	    setDateFormat( newFormat );
> 	}    	
>     }
> 
> ```

要从网页中提取日期，我们有一些名为`matchFetchDate`和`matchQuoteDate`的例程：

> ```
>     /** Search through text from a Yahoo quote page to find a date stamp */
>     private static OracleDate matchFetchDate( String text ) {
> 	Perl5Util regexp = new Perl5Util();
> 
> 	if ( regexp.match("/<p>\\s*(\\S+\\s+\\S+\\s+\\d+\\s+\\d\\d\\d\\d)\\s+[0-9:]+[aApP][mM][^<]*<table>/", text) ) {
> 	    return new OracleDate( regexp.group(1), "Day, Month DD YYYY" );
> 
> 	} else {
> 	    return null;
> 	}
>     }
> 	
> 
>     /** Search through the time column from a single Yahoo stock quote
> 	and set the time accordingly.  */
>     private static OracleDate matchQuoteDate( String timeText, OracleDate fetchDate ) {
> 	Perl5Util regexp = new Perl5Util();
> 
> 	if ( regexp.match("/\\d?\\d:\\d\\d[aApP][mM]/", timeText) ) {
> 	    // When the time column of the stock quote doesn't include the day,
> 	    // the day is pulled from the given fetchDate.
> 	    String date = fetchDate.getDate() + " " + timeText;
> 	    String format = fetchDate.getDateFormat() + " HH:MIam";
> 	    return new OracleDate( date, format );
> 
> 	} else if ( regexp.match("/[A-Za-z]+ +\\d\\d?/", timeText )) {
> 	    // After midnight but before the market opens, Yahoo reports the date
> 	    // rather than the time. 
> 	    return new OracleDate( timeText, "Mon DD" );
> 
> 	} else {
> 	    return null;
> 	}
>     }
> 
> ```

从 Yahoo 返回的股价通常包含分数，这些分数具有特殊的 HTML 标记。 `parseFraction`方法将 HTML 拆分并将股价作为 Java `float`返回：

> ```
>     /** Convert some HTML from the Yahoo quotes page to a float, handling
> 	fractions if necessary */
>     private static float parseFraction( String s ) {	
> 	Perl5Util regexp = new Perl5Util();
> 	if ( regexp.match( "/^\\D+(\\d+)\\s*<sup>(\\d*)</sup>/<sub>(\\d*)</sub>/", s)) {
> 	    // There's a fraction
> 	    float whole_num = Float.parseFloat( regexp.group(1) );
> 	    float numerator = Float.parseFloat( regexp.group(2) );
> 	    float denominator = Float.parseFloat( regexp.group(3) );
> 	    return whole_num + numerator / denominator;
> 	    
> 	} else {
> 	    // There is no fraction
> 	    // strip the HTML and go
> 	    return Float.parseFloat( regexp.substitute( "s/<.*?>//g", s) );
> 	}
>     }
> 
> ```

#### 杂项

我们所有的方法都通过调用`getConnection()`来获取它们的 JDBC 连接。 通过将所有数据库连接请求路由通过这个方法，我们的类将能够在数据库内部或外部运行 - `getConnection`检查其环境并相应地设置连接。 将 Java 加载到 Oracle 是一个繁琐的过程，因此能够从外部 JVM 调试代码是很好的。

> ```
>     public static Connection getConnection() 
>     throws SQLException {
> 
> 	Connection conn;
> 
> 	// In a real program all of these constants should 
> 	// be pulled from a properties file:
> 	String driverClass = "oracle.jdbc.driver.OracleDriver";
> 	String connectString = "jdbc:oracle:oci8:@ora8i_ipc";
> 	String databaseUser = "username";
> 	String databasePassword = "password";
> 	
> 	try {
> 	    // Figure out what environment we're running in
> 	    if ( System.getProperty("oracle.jserver.version") == null ) {
> 		// We're not running inside Oracle
> 		DriverManager.registerDriver( (java.sql.Driver) Class.forName(driverClass).newInstance() );
> 		conn = DriverManager.getConnection( connectString, databaseUser, databasePassword );
> 		
> 	    } else {
> 		// We're running inside Oracle
> 		conn = DriverManager.getConnection( "jdbc:default:connection:" );
> 	    }
> 	    
> 	    // The Oracle JVM automatically has autocommit=false,
> 	    // and we want to be consistent with this if we're in an external JVM
> 	    conn.setAutoCommit( false );
> 	    
> 	    return conn;
> 
> 	} catch ( Exception e ) {
> 	    throw new SQLException( e.toString() );
> 	}
>     }
> 
> ```

要从命令行调用`StockUpdater`，我们还需要提供一个`main`方法：

> ```
>     /** This method allows us to call the class from the command line
>      */
>     public static void main(String[] args)
>     throws SQLException {
> 	if ( args.length == 1 ) {
> 	    checkAll( Double.parseDouble( args[0] ));
> 	} else if ( args.length == 2 ) {
> 	    checkOne( Double.parseDouble(args[0]), args[1] );
> 	} else {
> 	    System.out.println("Usage: java StockUpdater update_interval [stock_ticker]");
> 	}
>     }
> 
> ```

最后，抓取程序需要一个可以将字符串连接在一起的实用程序。 它类似于 Perl 或 Tcl 中的“join”命令。

> ```
>     /** Builds a single string by taking a list of strings
>         and sticking them together with the given separator.
> 	If any of the elements of the list is not a String,
>         an empty string in inserted in place of that element.
>     */
>     public static String joinList( List stringList, String separator ) {
> 	
> 	StringBuffer joinedStr = new StringBuffer();
> 
> 	Iterator iter = stringList.iterator();
> 	boolean firstItemP = true;	
> 	while ( iter.hasNext() ) {	    
> 	    if ( firstItemP ) {
> 		firstItemP = false;
> 	    } else {
> 		joinedStr.append( separator );
> 	    }
> 
>             Object s = iter.next();
>             if ( s != null && s instanceof String ) {
>                 joinedStr.append( (String) s );
>             }
> 	}
> 	return joinedStr.toString();
>     }
> } // End of the StockUpdater class
> 
> ```

#### 外部表的实际操作

现在我们已经实现了所有这些，我们可以在 SQL*Plus 中查看我们的外部表：

> ```
> SQL> select ticker_symbol, last_trade,
>      (sysdate - last_modified)*24 as hours_old
>      from stock_quotes;
> 
> TICKER_SYMBOL	     LAST_TRADE  HOURS_OLD
> -------------------- ---------- ----------
> AAPL			22.9375 3.62694444
> IBM			112.438 3.62694444
> MSFT			  55.25 3.62694444
> 
> ```

这些数据已经超过三个小时了。 让我们请求在最近一个小时内的数据：

> ```
> SQL> call checker.stock_quotes( 1/24 );
> 
> Call completed.
> 
> SQL> select ticker_symbol, last_trade,
>      (sysdate - last_modified)*24 as hours_old
>      from stock_quotes;
> 
> TICKER_SYMBOL	     LAST_TRADE  HOURS_OLD
> -------------------- ---------- ----------
> AAPL			 23.625 .016666667
> IBM			114.375 .016666667
> MSFT			55.4375 .016666667
> 
> ```

这样更好。 但我对英特尔公司很好奇。

> ```
> SQL> call checker.stock_quotes( 1/24, 'INTC' );
> 
> Call completed.
> 
> SQL> select ticker_symbol, last_trade,
>      (sysdate - last_modified)*24 as hours_old
>      from stock_quotes;
> 
> TICKER_SYMBOL	     LAST_TRADE  HOURS_OLD
> -------------------- ---------- ----------
> AAPL			 23.625 .156666667
> IBM			114.375 .156666667
> MSFT			55.4375 .156666667
> INTC			     42 .002777778
> 
> ```

### 参考

+   在这个领域的开创性工作是在 1990 年代中期由 IBM Almaden 研究中心的大蒜项目完成的。 这是同一个开发了 System R 的实验室，这是第一个关系数据库管理系统，最终成为 IBM 的 DB2 产品。 要了解 IBM 在包装传统数据库和外部网站方面的想法是如何展开的，请访问[`www.almaden.ibm.com/cs/garlic/`](http://www.almaden.ibm.com/cs/garlic/)。

+   Java 存储过程开发人员指南位于[`www.oradoc.com/keyword/java_stored_procedures`](http://www.oradoc.com/keyword/java_stored_procedures)。

+   PL/SQL 用户指南和参考资料位于[`www.oradoc.com/keyword/plsql`](http://www.oradoc.com/keyword/plsql)。

+   Sun 的 Java2 文档位于[`java.sun.com/j2se/1.3/docs/index.html`](http://java.sun.com/j2se/1.3/docs/index.html)。

接下来：规范化

* * *

mbooth@arsdigita.com[philg@mit.edu](http://philip.greenspun.com/)

### 读者评论

> 好吧，我认为这个页面的时效性已经到期了，所以我可以指出（遗憾的是！）我的电子邮件地址不再是 mbooth@arsdigita.com。
> 
> 你可以在[michaelfbooth.com](http://michaelfbooth.com)找到我。
> 
> -- 迈克尔·布斯，2007 年 11 月 15 日

添加评论 | 添加链接
