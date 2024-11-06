# Databricks 参考应用程序

在 Databricks，我们正在开发一套演示如何使用 Apache Spark 的参考应用程序。本书/存储库包含了参考应用程序。

+   在 Github 存储库中查看代码：[`github.com/databricks/reference-apps`](https://github.com/databricks/reference-apps)

+   在这里阅读文档：[`databricks.gitbooks.io/databricks-spark-reference-applications/`](http://databricks.gitbooks.io/databricks-spark-reference-applications/)

+   在这里提交反馈或问题：[`github.com/databricks/reference-apps/issues`](https://github.com/databricks/reference-apps/issues)

参考应用程序将吸引那些希望通过示例学习 Spark 并通过示例学习更好的人。浏览这些应用程序，看看参考应用程序的特性与您想构建的特性相似之处，并重新设计代码示例以满足您的需求。此外，这旨在成为在您的系统中使用 Spark 的实用指南，因此这些应用程序提到了与 Spark 兼容的其他技术 - 例如用于存储大数据集的文件系统。

+   [日志分析应用程序](http://databricks.gitbooks.io/databricks-spark-reference-applications/content/logs_analyzer/index.html) - 日志分析参考应用程序包含一系列教程，通过示例学习 Spark，以及一个最终应用程序，可用于监视 Apache 访问日志。这些示例在批处理模式下使用 Spark，涵盖了 Spark SQL 以及 Spark Streaming。

+   [Twitter 流语言分类器](http://databricks.gitbooks.io/databricks-spark-reference-applications/content/twitter_classifier/index.html) - 该应用程序演示了如何使用 Spark MLLib 获取和训练推文的语言分类器。然后使用 Spark Streaming 调用训练过的分类器，并过滤出与指定群集匹配的实时推文。有关如何构建和运行此应用程序的说明 - 请参阅[twitter_classifier/scala/README.md](https://github.com/databricks/reference-apps/blob/master/twitter_classifier/scala/README.md)。

+   [使用 Cassandra 进行天气时间序列数据应用](http://databricks.gitbooks.io/databricks-spark-reference-applications/content/timeseries/index.html) - 该参考应用程序与天气数据一起工作，该数据是在特定时间点针对特定气象站采集的。该应用程序演示了几种利用集成了 Apache Cassandra 和 Apache Kafka 的 Spark Streaming 进行快速、容错、流式计算的时间序列数据的策略。

这些参考应用程序受到[此处](http://databricks.gitbooks.io/databricks-spark-reference-applications/content/LICENSE)的许可条款的保护。
