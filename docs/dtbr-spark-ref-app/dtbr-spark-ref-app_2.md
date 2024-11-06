# Twitter 实时语言分类器

# Twitter 实时语言分类器

在这个参考应用程序中，我们展示了如何使用 Apache Spark 训练语言分类器 - 取代您可能当前正在使用的整套工具。

此参考应用程序在一次见面会上进行了演示，演示内容可以在这里录制 - 此链接直接跳转到演示时间，但之前的讲话也很有用：

![Aaron Davidson doing his magic](https://www.youtube.com/watch?v=FjhRkfAuU7I#t=2035)

创建一个生产就绪的分类器通常需要经历 5 个典型阶段。通常，每个阶段都是由不同的工具集甚至不同的工程团队完成的：

1.  抓取/收集数据集。

1.  清理和探索数据，进行特征提取。

1.  在数据上构建模型并迭代/改进它。

1.  使用更多数据来改进模型，可能需要升级基础设施以支持构建更大的模型。（例如迁移到 Hadoop。）

1.  实时应用模型。

Spark 可用于上述所有目的，并且对于所有这些目的来说都非常简单易用。我们选择将语言分类器分解为 3 部分，每部分使用一个简单的 Spark 程序来完成：

1.  收集推文数据集 - 使用 Spark Streaming 来收集推文数据集并将其写入文件。

1.  检查推文并训练模型 - 使用 Spark SQL 来检查推文数据集。然后使用 Spark MLLib 应用 K-Means 算法对数据进行模型训练。

1.  实时应用模型 - 使用 Spark Streaming 和 Spark MLLib 来过滤与指定聚类相匹配的推文的实时流。

# 收集推文数据集

# 第一部分：收集推文数据集

使用 Spark Streaming 来收集推文作为数据集。推文以 JSON 格式写出，每行一个推文。每隔一段时间写出一个推文文件，直到收集到所需数量的推文为止。

查看 Collect.scala 获取完整代码。我们现在将浏览其中一些有趣的部分。

Collect.scala 接受以下参数列表：

1.  *outputDirectory* - 用于写入推文的输出目录。文件将以 'part-%05d' 命名

1.  *numTweetsToCollect* - 在程序退出之前收集的最小推文数量。

1.  *intervalInSeconds* - 每个间隔写出一组新的推文。

1.  *partitionsEachInterval* - 用于控制每个间隔写入的输出文件数

Collect.scala 还需要[Twitter API 凭证](https://apps.twitter.com/)。如果您从未注册过 Twitter Api 凭证，请按照此处的步骤进行操作[这里](https://databricks-training.s3.amazonaws.com/realtime-processing-with-spark-streaming.html#twitter-credential-setup)。Twitter 凭证通过命令行标志传递。

下面是 Collect.scala 中实际代码的片段。 该代码调用 Spark Streaming Twitter 库中的 TwitterUtils 来获取推文的 DStream。 然后，调用 map 将推文转换为 JSON 格式。 最后，在 DStream 上调用 for each RDD。 此示例重新分区 RDD 以便写出，以便您可以控制输出文件的数量。

```
 val tweetStream = TwitterUtils.createStream(ssc, Utils.getAuth)
  .map(gson.toJson(_))

tweetStream.foreachRDD((rdd, time) => {
  val count = rdd.count()
  if (count > 0) {
    val outputRDD = rdd.repartition(partitionsEachInterval)
    outputRDD.saveAsTextFile(
      outputDirectory + "/tweets_" + time.milliseconds.toString)
    numTweetsCollected += count
    if (numTweetsCollected > numTweetsToCollect) {
      System.exit(0)
    }
  }
}) 
```

运行 Collect.scala 以自行收集推文数据集：

```
 %  ${YOUR_SPARK_HOME}/bin/spark-submit \
     --class "com.databricks.apps.twitter_classifier.Collect" \
     --master ${YOUR_SPARK_MASTER:-local[4]} \
     target/scala-2.10/spark-twitter-lang-classifier-assembly-1.0.jar \
     ${YOUR_OUTPUT_DIR:-/tmp/tweets} \
     ${NUM_TWEETS_TO_COLLECT:-10000} \
     ${OUTPUT_FILE_INTERVAL_IN_SECS:-10} \
     ${OUTPUT_FILE_PARTITIONS_EACH_INTERVAL:-1} \
     --consumerKey ${YOUR_TWITTER_CONSUMER_KEY} \
     --consumerSecret ${YOUR_TWITTER_CONSUMER_SECRET} \
     --accessToken ${YOUR_TWITTER_ACCESS_TOKEN}  \
     --accessTokenSecret ${YOUR_TWITTER_ACCESS_SECRET} 
```

# 检查推文并训练模型

# 第 2 部分：检查推文并训练模型

第二个程序检查推文中发现的数据，并使用推文进行 K-Means 聚类来训练语言分类器：

+   检查 - 使用 Spark SQL 收集有关推文的数据--查看其中的一些推文，并计算用户最常用语言的推文总数。

+   训练 - 使用 Spark MLLib 应用 K-Means 算法对推文进行聚类。 聚类的数量和算法的迭代次数是可配置的。 在训练模型之后，会显示来自不同聚类的一些样本推文。

请参见此处以获取运行第 2 部分的命令。

# 使用 Spark SQL 检查

# 使用 Spark SQL 进行检查

可以使用 Spark SQL 根据推文检查数据。 以下是来自 ExamineAndTrain.scala 的一些相关代码片段。

首先，以下是一段代码，可以漂亮地打印出 5 个样本推文，使它们更易读。

```
val tweets = sc.textFile(tweetInput)
for (tweet <- tweets.take(5)) {
  println(gson.toJson(jsonParser.parse(tweet)))
} 
```

Spark SQL 可以加载 JSON 文件并根据该数据推断模式。 以下是加载 json 文件、在名为 "tweetTable" 的临时表中注册数据并根据该数据打印模式的代码。

```
val tweetTable = sqlContext.jsonFile(tweetInput)
tweetTable.registerTempTable("tweetTable")
tweetTable.printSchema() 
```

现在，查看 10 个样本推文的文本。

```
sqlContext.sql(
    "SELECT text FROM tweetTable LIMIT 10")
    .collect().foreach(println) 
```

查看 10 个样本推文的用户语言、用户名和文本。

```
sqlContext.sql(
    "SELECT user.lang, user.name, text FROM tweetTable LIMIT 10")
    .collect().foreach(println) 
```

最后，显示用户语言的推文计数。 这可以帮助确定此推文数据集的理想聚类数量。

```
sqlContext.sql(
    "SELECT user.lang, COUNT(*) as cnt FROM tweetTable " +
    "GROUP BY user.lang ORDER BY cnt DESC limit 1000")
    .collect.foreach(println) 
```

# 使用 Spark MLLib 进行训练

# 使用 Spark MLLib 进行训练

本节涵盖如何使用推文中的文本训练语言分类器。

首先，我们需要对推文文本进行特征化。 MLLib 有一个名为 HashingTF 的类可以做到这一点：

```
object Utils {
  ...

  val numFeatures = 1000
  val tf = new HashingTF(numFeatures)

  /**
   * Create feature vectors by turning each tweet into bigrams of
   * characters (an n-gram model) and then hashing those to a
   * length-1000 feature vector that we can pass to MLlib.
   * This is a common way to decrease the number of features in a
   * model while still getting excellent accuracy. (Otherwise every
   * pair of Unicode characters would potentially be a feature.)
   */
  def featurize(s: String): Vector = {
    tf.transform(s.sliding(2).toSeq)
  }

  ...
} 
```

这是实际从 tweetTable 中获取推文文本并对其进行特征化的代码。 调用 K-Means 创建聚类数量，并且该算法针对指定的迭代次数运行。 最后，将训练好的模型持久化，以便稍后加载。

```
val texts = sqlContext.sql("SELECT text from tweetTable").map(_.head.toString)
// Caches the vectors since it will be used many times by KMeans.
val vectors = texts.map(Utils.featurize).cache()
vectors.count()  // Calls an action to create the cache.
val model = KMeans.train(vectors, numClusters, numIterations)
sc.makeRDD(model.clusterCenters, numClusters).saveAsObjectFile(outputModelDir) 
```

最后，以下是一些代码，用于获取一组样本推文并按聚类打印出它们，以便我们可以看到我们的模型包含哪些语言聚类。 选择您喜欢的语言用于第 3 部分。

```
val some_tweets = texts.take(100)
for (i <- 0 until numClusters) {
  println(s"\nCLUSTER $i:")
  some_tweets.foreach { t =>
    if (model.predict(Utils.featurize(t)) == i) {
      println(t)
    }
  }
} 
```

# 运行检查和训练

# 运行检查和训练

要运行此程序，需要以下参数列表：

1.  YOUR_TWEET_INPUT - 这是输入推文的文件模式。

1.  OUTPUT_MODEL_DIR - 这是持久化模型的目录。

1.  NUM_CLUSTERS - 算法应创建的聚类数量。

1.  NUM_ITERATIONS - 算法应运行的迭代次数。

以下是运行 ExamineAndTrain.scala 的示例命令：

```
%  ${YOUR_SPARK_HOME}/bin/spark-submit \
     --class "com.databricks.apps.twitter_classifier.ExamineAndTrain" \
     --master ${YOUR_SPARK_MASTER:-local[4]} \
     target/scala-2.10/spark-twitter-lang-classifier-assembly-1.0.jar \
     "${YOUR_TWEET_INPUT:-/tmp/tweets/tweets*/part-*}" \
     ${OUTPUT_MODEL_DIR:-/tmp/tweets/model} \
     ${NUM_CLUSTERS:-10} \
     ${NUM_ITERATIONS:-20} 
```

# 实时应用模型

## 第 3 部分：实时应用模型

Spark Streaming 用于过滤传入的实时推文，仅接受被分类为指定群（类型）的推文。它接受以下参数：

1.  modelDirectory - 这是在第 2 部分训练的模型持久化的目录。

1.  clusterNumber - 这是您要从第 2 部分选择的群。只有匹配此语言群的推文将被打印出来。

此程序非常简单 - 下面是代码的主体部分。首先，加载 Spark Streaming 上下文。其次，创建一个 Twitter DStream 并映射它以获取文本。第三，加载在第 2 步中训练的 K-Means 模型。最后，在推文上应用模型，仅过滤出与指定群匹配的推文，并打印匹配的推文。

```
println("Initializing Streaming Spark Context...")
val conf = new SparkConf().setAppName(this.getClass.getSimpleName)
val ssc = new StreamingContext(conf, Seconds(5))

println("Initializing Twitter stream...")
val tweets = TwitterUtils.createStream(ssc, Utils.getAuth)
val statuses = tweets.map(_.getText)

println("Initializing the KMeans model...")
val model = new KMeansModel(ssc.sparkContext.objectFileVector.collect())

val filteredTweets = statuses
  .filter(t => model.predict(Utils.featurize(t)) == clusterNumber)
filteredTweets.print() 
```

现在，运行 Predict.scala：

```
 %  ${YOUR_SPARK_HOME}/bin/spark-submit \
     --class "com.databricks.apps.twitter_classifier.Predict" \
     --master ${YOUR_SPARK_MASTER:-local[4]} \
     target/scala-2.10/spark-twitter-lang-classifier-assembly-1.0.jar \
     ${YOUR_MODEL_DIR:-/tmp/tweets/model} \
     ${CLUSTER_TO_FILTER:-7} \
     --consumerKey ${YOUR_TWITTER_CONSUMER_KEY} \
     --consumerSecret ${YOUR_TWITTER_CONSUMER_SECRET} \
     --accessToken ${YOUR_TWITTER_ACCESS_TOKEN}  \
     --accessTokenSecret ${YOUR_TWITTER_ACCESS_SECRET} 
```
