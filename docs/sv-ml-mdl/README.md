# 机器学习模型托管指南

机器学习是当今软件工程中最热门的事物。每天都会出现大量关于机器学习的出版物，新的机器学习产品也不断出现。[亚马逊](http://bit.ly/what-is-amazon-ml)、[微软](http://bit.ly/azure-ml-modules)、[谷歌](http://bit.ly/google-cloud-ml)、[IBM](http://bit.ly/IBM-ml)等公司已经推出了作为托管云服务的机器学习产品。

然而，机器学习中一个未受到足够关注的领域是模型服务——如何为使用机器学习训练的模型提供服务。

这个问题的复杂性源于企业中通常模型训练和模型服务是由两个不同职能、关注点和工具的群体负责。因此，这两个活动之间的过渡通常并不简单。此外，随着新的机器学习工具的出现，通常会迫使开发人员创建与新工具兼容的新模型服务框架。

本书介绍了一种略有不同的模型服务方法，基于训练的机器学习模型的标准化基于文档的中间表示的引入，并在流处理上下文中使用这种表示进行服务。它提出了一个实现数据和模型的受控流的整体架构，不仅能够实时提供模型作为处理输入流的一部分，还能够在不重新启动现有应用程序的情况下更新模型。

# 本书适合谁？

本书适用于对支持实时模型更新的机器学习模型进行实时服务方法感兴趣的人。它逐步描述了导出模型的选项，要导出的内容以及如何使用这些模型进行实时服务。

本书还适用于那些试图使用现代流处理引擎和框架（如 Apache Flink、Apache Spark Streaming、Apache Beam、Apache Kafka Streams 和 Akka Streams）实现这些解决方案的人。它提供了一组使用这些技术进行模型服务实现的实际示例。

# 为什么模型服务如此困难？

在机器学习实施方面，组织通常雇佣两组非常不同的人员：数据科学家，他们通常负责创建和训练模型，以及软件工程师，他们专注于模型评分。这两组通常使用完全不同的工具。数据科学家使用 R、Python、笔记本等工具，而软件工程师通常使用 Java、Scala、Go 等工具。他们的活动受到不同的关注：数据科学家需要处理大量数据、数据清洗问题、模型设计和比较等问题；软件工程师关注生产问题，如性能、可维护性、监控、可扩展性和故障转移。

目前对这些差异有相当深入的了解，并导致许多“专有”模型评分解决方案，例如[Tensorflow 模型服务](https://tensorflow.github.io/serving/)和[基于 Spark 的模型服务](http://bit.ly/2xy47wV)。此外，所有托管的机器学习实施（[亚马逊](http://bit.ly/what-is-amazon-ml)、[微软](http://bit.ly/azure-ml-modules)、[谷歌](http://bit.ly/google-cloud-ml)、[IBM](http://bit.ly/IBM-ml)等）都提供模型服务功能。

# 工具的泛滥使情况变得更糟

在他最近的[演讲](http://bit.ly/ted-dunning-ffsf-2017)中，Ted Dunning 描述了数据科学家有多种工具可供选择，他们倾向于使用不同的工具来解决不同的问题（因为每个工具都有其独特的优势，而且工具数量每天都在增加），因此他们对工具标准化并不感兴趣。这给试图使用支持特定机器学习技术的“专有”模型服务工具的软件工程师带来了问题。随着数据科学家评估和引入新的机器学习技术，软件工程师被迫引入支持这些额外技术的模型评分的新软件包。

处理这些问题的方法之一是在专有系统之上引入[API 网关](https://github.com/ucbrise/clipper)。尽管这将后端系统的差异隐藏在统一的 API 背后，但对于模型服务仍需要安装和维护实际的模型服务实现。

# 模型标准化来拯救

要克服这些复杂性，[数据挖掘组织](http://dmg.org/)引入了两种模型表示标准：[预测模型标记语言（PMML）](http://dmg.org/pmml/v4-1/GeneralStructure.html)和[分析便携格式（PFA）](http://dmg.org/pfa/)

[数据挖掘组织定义 PMML](http://dmg.org/pmml/pmml-v4-3.html)为：

> 是一种基于[XML](http://www.w3.org/TR/REC-xml/)的语言，为应用程序提供了定义统计和数据挖掘模型以及在符合 PMML 的应用程序之间共享模型的方式。
> 
> PMML 为应用程序提供了一种独立于供应商的定义模型的方法，因此专有问题和不兼容性不再是应用程序之间交换模型的障碍。它允许用户在一个供应商的应用程序中开发模型，并使用其他供应商的应用程序来可视化、分析、评估或以其他方式使用这些模型。以前，这是非常困难的，但有了 PMML，符合标准的应用程序之间的模型交换现在变得简单。由于 PMML 是基于 XML 的标准，规范以[XML Schema](http://dmg.org/pmml/v4-3/pmml-4-3.xsd)的形式呈现。

[数据挖掘组描述 PFA](http://dmg.org/pfa/)如下：

> 是统计模型和数据转换引擎的新兴标准。PFA 结合了跨系统易于移植性和算法灵活性：模型、预处理和后处理都是可以任意组合、链接或构建成复杂工作流程的函数。PFA 可以简单到原始数据转换，也可以复杂到一套并发数据挖掘模型，所有这些都可以描述为 JSON 或 YAML 配置文件。

今天在机器学习中另一个事实上的标准是[TensorFlow](https://www.tensorflow.org/)——一个用于机器智能的开源软件库。Tensorflow 可以定义如下：

> 在高层次上，TensorFlow 是一个允许用户将任意计算表示为数据流图的 Python 库。图中的节点代表数学运算，而边代表从一个节点传递到另一个节点的数据。在 TensorFlow 中，数据被表示为张量，即多维数组。

TensorFlow 于 2015 年由 Google 发布，旨在使开发人员更容易设计、构建和训练深度学习模型，自那时起，它已成为最常用的机器学习软件库之一。您还可以将 TensorFlow 用作其他流行机器学习库的后端，例如[Keras](https://keras.io/)。TensorFlow 允许以协议缓冲区格式（文本和二进制）导出训练好的模型，您可以将其用于在机器学习和模型服务之间传输模型。为了使 TensorFlow 更加友好于 Java，于 2017 年发布了[TensorFlow Java APIs](http://bit.ly/tensorflow-java-apis)，这使得可以使用任何基于 Java 虚拟机（JVM）的语言对 TensorFlow 模型进行评分。

所有上述的模型导出方法都是为需要提供服务的模型设计的平台中立描述。引入这些模型导出方法导致了几个专门用于“通用”模型服务的软件产品的创建，例如，[Openscoring](http://openscoring.io/) 和 [Open Data Group](https://www.opendatagroup.com/)。

这种标准化的另一个结果是创建基于这些格式的通用“评估器”的开源项目。[JPMML](https://github.com/jpmml/jpmml-evaluator) 和 [Hadrian](https://github.com/opendatagroup/hadrian) 是两个越来越多被采用用于构建模型服务实现的例子，比如这些示例项目：[ING](http://bit.ly/erik-de-noojj-ffsf-2017), [R implementation](http://fastdatageek.blogspot.com/2014/03/), [SparkML support](https://github.com/jpmml/jpmml-evaluator-spark), [Flink support](https://github.com/FlinkML/flink-jpmml)，等等。

此外，因为模型不是表示为代码而是表示为数据，使用这种模型描述允许对模型进行操作，作为我们提出的解决方案的基础的一种特殊类型的数据。

# 为什么写这本书

本书描述了在流式应用程序中为机器学习产生的模型提供服务的问题。它展示了如何将训练好的模型导出为 TensorFlow 和 PMML 格式，并在几个流行的流式引擎和框架中使用它们进行模型服务。

我故意不偏袒任何特定解决方案。相反，我概述了一些优缺点的选项。选择最佳解决方案在很大程度上取决于您试图解决的具体用例，更准确地说：

+   要提供服务的模型数量。增加模型数量将使您更倾向于使用基于键的方法，比如 Flink 基于键的连接。

+   每个模型要评分的数据量。增加数据量建议使用基于分区的方法，比如 Spark 或 Flink 基于分区的连接。

+   将用于对每个数据项进行评分的模型数量。您需要一个能够轻松支持使用复合键将每个数据项与多个模型匹配的解决方案。

+   评分过程中的计算复杂性以及评分结果的额外处理。随着复杂性的增加，负载也会增加，这表明应该使用流式引擎而不是流式库。

+   可扩展性要求。如果要求较低，使用像 Akka 和 Kafka Streams 这样的流式库可能是一个更好的选择，因为相对于 Spark 和 Flink 这样的引擎，它们相对简单，易于采用，并且相对容易维护这些应用程序。

+   您组织现有的专业知识，这可能表明在其他所有考虑因素相等的情况下，可能会做出次优选择，但对于您的组织来说更为舒适。

我希望这本书能为您实现自己解决方案提供所需的指导。

# 本书的组织方式

本书组织如下：

+   第一章 描述了整体提议的架构。

+   第二章 讨论了使用 TensorFlow 和 PMML 示例导出模型。

+   第三章 描述了所有解决方案中使用的常见组件。

+   第四章 到 第八章 描述了不同流处理引擎和框架的模型服务实现。

+   第九章 涵盖了模型服务实现的监控方法。

# 有关代码的说明

该书包含许多代码片段。您可以在以下 Git 存储库中找到完整的代码：

+   [Python 示例](https://github.com/typesafehub/fdp-tensorflow-python-examples) 是包含导出 TensorFlow 模型代码的 Python 代码的存储库，描述在 第二章 中。

+   [Beam 模型服务器](https://github.com/typesafehub/fdp-beam-modelServer) 是包含 第五章 中描述的 Beam 解决方案代码的存储库。

+   [模型服务](https://github.com/typesafehub/fdp-modelserver) 是包含书中描述的其余代码的存储库。

# 致谢

我要感谢那些在撰写本书和改进书籍方面帮助我的人，特别是：

+   Konrad Malawski，对 Akka 实现和整体审查的帮助

+   Dean Wampler，对整本书进行了彻底审查并提供了许多有用的建议

+   Trevor Grant，进行技术审查

+   整个 Lightbend Fast Data 团队，特别是 Stavros Kontopoulos、Debasish Ghosh 和 Jim Powers，对原始文本和代码提出了许多有用的评论和建议
