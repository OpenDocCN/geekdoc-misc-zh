# 进一步资源

> 原文：[`howqueryengineswork.com/18-further-resources.html`](https://howqueryengineswork.com/18-further-resources.html)

我希望您觉得这本书有用，并且现在对查询引擎的内部结构有了更好的理解。如果您觉得某些主题没有得到充分或完全的覆盖，我很乐意听到您的意见，这样我可以在本书的将来修订版中考虑添加更多内容。

可以在[Leanpub 网站上的公共论坛](https://community.leanpub.com/t/feedback/2160)上发布反馈，或者您可以直接通过 twitter 在[@andygrove_io](https://twitter.com/andygrove_io)上给我发消息。

## 开源项目

有许多包含查询引擎的开源项目，与这些项目合作是学习更多关于这个主题的好方法。以下是一些流行的开源查询引擎的例子。

+   Apache Arrow

+   Apache Calcite

+   Apache Drill

+   Apache Hadoop

+   Apache Hive

+   Apache Impala

+   Apache Spark

+   Facebook Presto

+   NVIDIA RAPIDS 加速器用于 Apache Spark

## YouTube

我最近发现了 Andy Pavlo 的讲座系列，这些讲座可在 YouTube 上找到([这里](https://www.youtube.com/playlist?list=PLSE8ODhjZXjasmrEd2_Yi1deeE360zv5O))。这不仅仅涵盖了查询引擎，还包括了大量的查询优化和执行内容。我强烈推荐观看这些视频。

## 示例数据

早期章节引用了[纽约市出租车和豪华轿车委员会行程记录数据集](https://www1.nyc.gov/site/tlc/about/tlc-trip-record-data.page)。黄色和绿色出租车的行程记录包括捕获接车和送车日期/时间、接车和送车地点、行程距离、详细费用、费率类型、支付类型和司机报告的乘客数量。

当本书首次出版时，数据是以 CSV 格式提供的，但现在已转换为 Parquet 格式。仍然可以在网上找到这些文件的 CSV 版本。截至 2025 年 12 月，以下位置包含这些数据：

+   https://github.com/DataTalksClub/nyc-tlc-data/releases

+   https://catalog.data.gov/dataset/2019-yellow-taxi-trip-data

+   https://www.kaggle.com/code/haydenbailey/newyork-yellow-taxi

[KQuery 项目](https://github.com/andygrove/how-query-engines-work)包含了将这些 CSV 文件转换为 Parquet 格式的源代码。*本书也以 ePub、MOBI 和 PDF 格式在[`leanpub.com/how-query-engines-work`](https://leanpub.com/how-query-engines-work)上提供购买。*

**版权所有 © 2020-2025 安迪·格罗夫。保留所有权利。**
