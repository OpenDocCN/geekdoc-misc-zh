# 第三章 实现模型评分

如图 1-1 所示，我们实现的整体架构是读取两个输入流，模型流和数据流，然后将它们连接起来生成结果流。

如今有两种主要选项用于实现这种基于流的应用程序：流处理引擎或流处理库：

+   [现代流处理引擎](http://bit.ly/bigdata-stream-processing)（SPEs）利用集群架构。它们将计算组织成一组运算符，这样可以实现执行并行性；不同的运算符可以在不同的线程或不同的机器上运行。引擎管理集群机器之间的运算符分发。此外，SPE 通常实现了检查点，允许在发生故障时无缝重新启动执行。

+   另一方面，流处理库（SPL）是一个库，通常是领域特定语言（DSL），用于简化构建流式应用程序的构造。这些库通常不支持分布和/或集群；这通常留给开发人员自行解决。

尽管它们非常不同，因为它们都有“stream”一词，它们经常可以互换使用。实际上，正如[Jay Kreps 的博客](https://www.confluent.io/blog/introducing-kafka-streams-stream-processing-made-simple/)中概述的那样，它们是构建流式应用程序的两种非常不同的方法，选择其中一种是权衡功能和简单性之间的折衷。Flink 和 Kafka Streams 的[比较](http://bit.ly/2yFAMRn)概述了这两种方法之间的主要区别，其中包括

> 它们部署和管理的方式（通常是组织角度拥有这些应用程序的人的职能）以及并行处理（包括容错）的协调方式。这些是核心差异——它们根植于这两种方法的架构中。

使用 SPE 非常适合需要这些引擎提供的功能的应用程序，包括通过跨集群的并行性实现可伸缩性和高吞吐量，事件时间语义，检查点，内置支持监控和管理，以及混合流和批处理。使用引擎的缺点是您受到它们提供的编程和部署模型的限制。

相比之下，SPL 提供了一种编程模型，允许开发人员根据其精确需求构建应用程序或微服务，并将它们部署为简单的独立 Java 应用程序。但在这种情况下，开发人员需要自行实现可伸缩性、高可用性和监控解决方案（Kafka Streams 通过使用 Kafka 支持其中一些）。

今天最流行的[SPEs](http://bit.ly/codecentric-SPEs)包括：[Apache Spark](https://spark.apache.org/)、[Apache Flink](https://flink.apache.org/)、[Apache Beam](https://beam.apache.org/)，而最流行的流库是[Apache Kafka Streams](https://kafka.apache.org/documentation/streams/)和[Akka Streams](http://doc.akka.io/docs/akka/current/scala/stream/index.html)。在接下来的章节中，我将展示如何使用它们中的每一个来实现我们的模型服务架构。

我的实现中有几个常见的工件，无论使用哪种流引擎/框架都会用到：模型表示、模型流、数据流、模型工厂和测试工具，所有这些都在以下部分中描述。

# 模型表示

在深入具体实现细节之前，您必须决定模型的表示方式。这里的问题是是否有必要引入特殊的抽象来简化在特定流库中使用模型。

我决定将模型服务表示为一个可以在流处理管道的任何位置使用的“普通”函数。此外，将模型表示为一个简单函数允许对模型进行功能组合，这使得组合多个模型进行处理变得更简单。此外，比较示例 2-2、2-4 和 2-6 表明，不同的模型类型（PMML 与 TensorFlow）和不同的表示形式（保存的模型与普通图）导致模型评分管道的基本结构相同，可以使用 Scala trait 通用描述，如示例 3-1 所示。

##### 示例 3-1。模型表示

```
trait Model {
 def score(input : AnyVal) : AnyVal
 def cleanup() : Unit
 def toBytes() : Array[Byte]
 def getType : Long
}
```

该 trait 的基本方法如下：

+   `score()`是模型实现的基本方法，将输入数据转换为结果或分数。

+   `cleanup()`是一个模型实现者释放与模型执行-模型生命周期支持相关的所有资源的钩子。

+   `toBytes()`是用于模型内容序列化的支持方法（用于检查点）。

+   `getType()`是一个支持方法，返回用于查找适当的模型工厂类的模型类型索引（请参阅接下来的部分）。

这个 trait 可以使用 JPMML 或 TensorFlow Java API 实现，并在需要模型评分的任何地方使用。

# 模型流

还需要定义一种表示模型在流中的格式。我决定使用[Google protocol buffers](https://developers.google.com/protocol-buffers/)（简称“protobuf”）来表示模型，如示例 3-2 所示。

##### 示例 3-2。模型更新的 Protobuf 定义

```
syntax = "proto3";
// Description of the trained model
message ModelDescriptor {
   // Model name
   string name = 1;
   // Human-readable description
   string description = 2;
   // Data type for which this model is applied
   string dataType = 3;
   // Model type
   enum ModelType {
       TENSORFLOW  = 0;
       TENSORFLOWSAVED = 1;
       PMML = 2;
   };
   ModelType modeltype = 4;
   oneof MessageContent {
       bytes data = 5;
       string location = 6;
   }
}
```

这里的模型（模型内容）可以表示为字节数组的内联或作为存储模型的位置的引用。除了模型数据外，我们的定义还包含以下字段：

`名称`

可用于监视或 UI 应用程序的模型名称。

`描述`

一个可供 UI 应用程序使用的人类可读的模型描述。

`数据类型`

适用于此模型的数据类型（我们的模型流可以包含多个不同的模型，每个模型用于流中特定的数据）。有关此字段利用的更多详细信息，请参阅第四章。

`模型类型`

目前，我仅定义了三种模型类型，PMML 和两种 TensorFlow 类型，图和保存的模型。

在实现过程中，使用[ScalaPB](https://scalapb.github.io/)进行 protobuf 编组、生成和处理。

## 数据流

与模型流类似，protobuf 用于数据源定义和编码。显然，具体定义取决于您正在处理的实际数据流。对于我们的[葡萄酒质量数据集](https://archive.ics.uci.edu/ml/datasets/wine+quality)，protobuf 看起来像示例 3-3。

##### [示例 3-3](https://scalapb.github.io/)。数据源的 Protobuf 定义

```
syntax = "proto3";
// Description of the wine parameters
message WineRecord {
   double fixed_acidity = 1;
   double volatile_acidity = 2;
   double citric_acid = 3;
   double residual_sugar = 4;
   double chlorides = 5;
   double free_sulfur_dioxide = 6;
   double total_sulfur_dioxide = 7;
   double density = 8;
   double pH = 9;
   double sulphates = 10;
   double alcohol = 11;
   // Data type for this record
   string dataType = 12;
}
```

注意，`数据类型`字段被添加到模型和数据定义中。该字段用于标识记录类型（在多个数据类型和模型的情况下）以匹配相应的模型。

在这个简单的案例中，我只使用了一个具体的数据类型，因此示例 3-3 显示了直接数据编码。如果需要支持多个数据类型，则可以使用 protobuf 的 [`oneof`](http://bit.ly/googledev-proto3) 构造，如果所有记录都通过同一流程，或者可以引入分别使用不同 Kafka 主题管理的分离流程，每个数据类型一个。

当给定记录使用单个模型进行评分时，基于提议的数据类型的数据和模型流之间的联系效果很好。如果此关系是一对多的，即每个记录都需要由多个模型评分，则可以为每个接收到的记录生成一个复合键（数据类型与模型 ID）。

# 模型工厂

如上所述，流中的模型以 protobuf 消息的形式传递，该消息可以包含模型的完整表示或对模型位置的引用。为了从 protobuf 消息中通用地创建模型，我引入了一个额外的特质`ModelFactory`，它支持根据模型描述符构建模型（模型更新的 protobuf 定义的内部表示，见示例 3-2；该类的实际代码稍后在本书中展示）。这个接口的另一个用途是支持[检查点](https://en.wikipedia.org/wiki/Application_checkpointing)的序列化和反序列化。我们可以使用示例 3-4 中提出的特质描述模型工厂。

##### 示例 3-4。模型工厂表示

```
trait ModelFactory {
 def create(input : ModelDescriptor) : Model
 def restore(bytes : Array[Byte]) : Model
}
```

这个特质的基本方法如下：

`create`

基于模型描述符创建模型的方法。

`restore`

一个从模型的`toByte`方法发出的字节数组中恢复模型的方法。这两种方法需要合作以确保`ModelSerializer`/`ModelDeserializer`的正确功能。

# 测试工具

我还创建了一个小型测试工具，用于验证实现。它包括两个简单的 Kafka 客户端：一个用于模型，一个用于数据。两者都基于一个通用的`KafkaMessageSender`类（[完整代码在此处可用](http://bit.ly/kafka-ms)），如示例 3-5 所示。

##### 示例 3-5。KafkaMessageSender 类

```
class KafkaMessageSender (brokers: String, zookeeper : String){

 // Configure
 ...
 // Create producer
 val producer = new KafkaProducer[Array[Byte], Array[Byte]](props)
 val zkUtils = ZkUtils.apply(zookeeper, KafkaMessageSender
   .sessionTimeout, KafkaMessageSender.connectionTimeout, false)

 // Write value to the queue
 def writeValue(topic:String, value:Array[Byte]): RecordMetadata = {
   val result = producer.send(
     new ProducerRecord[Array[Byte],
       Array[Byte]](topic, null, value)).get
       producer.flush()
   result
 }

 // Close producer
 def close(): Unit = {
   producer.close
 }

 def createTopic(topic : String, numPartitions: Int = 1,
   replicationFactor : Int = 1): Unit = {
   if (!AdminUtils.topicExists(zkUtils, topic)){
     try {
       AdminUtils.createTopic(...
     }catch {
       ...
     }
   }
   else
     println(s"Topic $topic already exists")
 }
}

object KafkaMessageSender{
 ...
 private val senders : Map[String, KafkaMessageSender] = Map()

 def apply(brokers:String, zookeeper :String): KafkaMessageSender ={
   senders.get(brokers) match {
     case Some(sender) => sender
     case _ => {
       val sender = new KafkaMessageSender(brokers, zookeeper)
       senders.put(brokers, sender)
       sender
     }
   }
 }
}
```

这个类使用 Kafka API 创建一个 Kafka 生产者并发送消息。`DataProvider`类使用`KafkaMessageSender`类发送数据消息（[完整代码在此处可用](http://bit.ly/kafka-dataprovider)，如示例 3-6 所示）。

##### 示例 3-6。DataProvider 类

```
DataProvider {

 ...

 def main(args: Array[String]) {
   val sender = KafkaMessageSender(
     ApplicationKafkaParameters.LOCAL_KAFKA_BROKER,
     ApplicationKafkaParameters.LOCAL_ZOOKEEPER_HOST)
   sender.createTopic(ApplicationKafkaParameters.DATA_TOPIC)
   val bos = new ByteArrayOutputStream()
   val records  = getListOfRecords(file)
   while (true) {
     var lineCounter = 0
     records.foreach(r => {
       bos.reset()
       r.writeTo(bos)
       sender.writeValue(ApplicationKafkaParameters.DATA_TOPIC,
         bos.toByteArray)
       pause()
     })
     pause()
   }
 }
 ...
 def getListOfRecords(file: String): Seq[WineRecord] = {

   var result = Seq.empty[WineRecord]
   val bufferedSource = Source.fromFile(file)
   for (line <- bufferedSource.getLines) {
     val cols = line.split(";").map(_.trim)
     val record = new WineRecord(
       fixedAcidity = cols(0).toDouble,
       volatileAcidity = cols(1).toDouble,
       citricAcid = cols(2).toDouble,
       residualSugar = cols(3).toDouble,
       chlorides = cols(4).toDouble,
       freeSulfurDioxide = cols(5).toDouble,
       totalSulfurDioxide = cols(6).toDouble,
       density = cols(7).toDouble,
       pH = cols(8).toDouble,
       sulphates = cols(9).toDouble,
       alcohol = cols(10).toDouble,
       dataType = "wine"
     )
     result = record +: result
   }
   bufferedSource.close
   result
 }
}
```

实际数据与用于训练[葡萄酒质量数据集](https://archive.ics.uci.edu/ml/datasets/wine+quality)的数据相同，该数据以 CSV 文件的形式存储在本地。文件被读入内存，然后记录从文本记录转换为 protobuf 记录，这些记录通过一个预定义的发送间隔的无限循环发布到 Kafka 主题。

一个类似的[实现](http://bit.ly/kafka-modelprovider)用于生成用于提供服务的模型。对于一组模型，我使用了在 TensorFlow 中使用不同训练算法的结果（导出为执行图）和 PMML 格式，这些结果通过一个预定义的发送间隔的无限循环发布到 Kafka 主题。

现在我们已经概述了必要的组件，第四章到第八章展示了如何使用特定技术实现这个解决方案。
