# 第二章\. 导出模型

在深入讨论模型服务之前，有必要讨论导出模型的主题。正如之前讨论的，数据科学家定义模型，工程师实现模型服务。因此，从数据科学工具导出模型的能力现在很重要。

对于本书，我将使用两个不同的示例：预测模型标记语言（PMML）和 TensorFlow。让我们看看如何使用这些工具导出模型。

# TensorFlow

为了更容易实现模型评分，TensorFlow 支持导出经过训练的模型，Java API 可以使用这些模型来实现评分。TensorFlow Java API 并不执行实际处理；它们只是实际 TensorFlow C++代码的薄[Java 本机接口（JNI）](https://en.wikipedia.org/wiki/Java_Native_Interface)包装器。因此，它们的使用需要将 TensorFlow C++可执行文件“链接”到您的 Java 应用程序。

TensorFlow 目前支持两种模型导出类型：[执行图的导出](https://www.tensorflow.org/api_docs/python/tf/train/Saver)，可用于推理优化，以及今年推出的新的[SavedModel](http://bit.ly/tensorflow-savedmodel-github)格式。

## 导出执行图

导出执行图是保存模型的“标准”TensorFlow 方法。让我们看一个示例，如何将执行图导出到应用于开源[葡萄酒质量数据集](https://archive.ics.uci.edu/ml/datasets/wine+quality)的[Keras](http://bit.ly/keras-tutorial)与 TensorFlow 后端应用的多类分类问题实现中（[完整代码](http://bit.ly/keras-complete)）。

##### 示例 2-1\. 从 Keras 模型导出执行图

```
...
# Create TF session and set it in Keras
sess = tf.Session()
K.set_session(sess)
...
# Saver op to save and restore all the variables
saver = tf.train.Saver()
# Save produced model
model_path = "path"
model_name = "WineQuality"
save_path = saver.save(sess, model_path+model_name+".ckpt")
print "Saved model at ", save_path
# Now freeze the graph (put variables into graph)
input_saver_def_path = ""
input_binary = False
output_node_names = "dense_3/Sigmoid"
restore_op_name = "save/restore_all"
filename_tensor_name = "save/Const:0"
output_frozen_graph_name = model_path + 'frozen_' + model_name
  + '.pb'
clear_devices = True
freeze_graph.freeze_graph(graph_path, input_saver_def_path,
input_binary, save_path,Output_node_names,
restore_op_name, filename_tensor_name,
output_frozen_graph_name, clear_devices, "")
# Optimizing graph
input_graph_def = tf.GraphDef()
with tf.gfile.Open(output_frozen_graph_name, "r") as f:
   data = f.read()
   input_graph_def.ParseFromString(data)
output_graph_def =
  optimize_for_inference_lib.optimize_for_inference(
   input_graph_def,
   ["dense_1_input"],
   ["dense_3/Sigmoid"],
   tf.float32.as_datatype_enum)
# Save the optimized graph
tf.train.write_graph(output_graph_def, model_path,
  "optimized_" + model_name + ".pb", as_text=False)
```

示例 2-1 改编自[Keras 机器学习示例](http://bit.ly/keras-tutorial)，演示如何导出 TensorFlow 图。为此，需要明确设置 Keras 执行的 TensorFlow 会话。TensorFlow 执行图与执行会话绑定，因此需要会话才能访问图形。

实际图形导出实现涉及以下步骤：

1.  保存初始图形。

1.  冻结图形（这意味着将图形定义与参数合并）。

1.  优化图形以进行服务（删除不影响服务的元素）。

1.  保存优化后的图形。

保存的图形是使用二进制 Google 协议缓冲区（protobuf）格式存储的优化图形，其中仅包含对模型服务相关的部分图形和数据（实现学习和中间计算的部分图形被删除）。

导出模型后，您可以用它进行评分。示例 2-2 使用 TensorFlow Java API 加载和评分模型（[完整代码在此处可用](http://bit.ly/winemodelserving-scala)）。

##### 示例 2-2\. 为从 Keras 模型的执行图创建的模型提供服务

```
class WineModelServing(path : String) {
 import WineModelServing._
 // Constructor
 val lg = readGraph(Paths.get (path))
 val ls = new Session (lg)

 def score(record : Array[Float]) : Double = {
   val input = Tensor.create(Array(record))
   val result = ls.runner.feed("dense_1_input",input).
     fetch("dense_3/Sigmoid").run().get(0)
   // Extract result value
   val rshape = result.shape
   var rMatrix =
     Array.ofDimFloat.asInstanceOf[Int],rshape(1).
       asInstanceOf[Int])result.copyTo(rMatrix)
   var value = (0, rMatrix(0)(0))
   1 to (rshape(1).asInstanceOf[Int] -1) foreach{i => {
      if(rMatrix(0)(i) > value._2)
        value = (i, rMatrix(0)(i))
    }}
    value._1.toDouble
 }
 def cleanup() : Unit = {
   ls.close
 }
}
object WineModelServing{
 def main(args: Array[String]): Unit = {
   val model_path = "/optimized_WineQuality.pb"   // model
   val data_path = "/winequality_red.csv" // data
   val lmodel = new WineModelServing(model_path)
   val inputs = getListOfRecords(data_path)
   inputs.foreach(record =>
     println(s"result ${lmodel.score(record._1)}"))
   lmodel.cleanup()
 }
 private def readGraph(path: Path) : Graph = {
   try {
     val graphData = Files.readAllBytes(path)
     val g = new Graph
     g.importGraphDef(graphData)
     g
   } ...
 }
...
}
```

在这个简单的代码中，构造函数使用`readGraph`方法读取执行图，并创建一个附加了该图的 TensorFlow 会话。

score 方法接受包含葡萄酒质量观察结果的输入记录，并将其转换为张量格式，该格式用作运行图的输入。由于导出的图不提供有关输入或输出的名称和形状（执行签名）的任何信息，因此在使用此方法时，必须知道您的流接受（提供）哪些变量（即输入参数）以及要获取的哪些张量（及其形状）作为结果。在接收到结果（以张量形式）后，提取其值。

执行由`WineModelServing`对象中的主方法编排。该方法首先创建`WineModelServing`类的一个实例，然后读取输入记录列表，并对每个记录在`WineModelServing`类实例上调用`serve`方法。

要运行这段代码，除了需要 TensorFlow Java 库外，还必须在运行代码的机器上安装 TensorFlow C++ 实现库（*.dll* 或 *.so*）。

执行图导出的优点包括以下内容：

+   由于优化，导出的图具有相对较小的大小。

+   该模型是自包含的单个文件，这使得将其作为二进制 blob 进行传输变得容易，例如，使用 Kafka 主题。

缺点是模型的用户必须明确知道模型的输入和输出（以及它们的形状和类型）才能正确使用图；然而，这通常不是一个严重的问题。

## 导出 Saved Model

TensorFlow *SavedModel* 是一种新的导出格式，于 2017 年推出，其中模型被导出为具有以下结构的目录：

```
assets/
assets.extra/
variables/
    variables.data-?????-of-?????
    variables.index
Saved_model.pb
```

其中：

+   `assets` 是一个包含辅助文件（如词汇表等）的子文件夹。

+   `assets.extra` 是一个子文件夹，高级库和用户可以在其中添加自己的资产，这些资产与模型共存但不会被图加载。它不受 SavedModel 库管理。

+   `variables` 是一个包含来自[TensorFlow Saver](http://bit.ly/tensorflow-saver)的输出的子文件夹：变量索引和数据。

+   `saved_model.pb` 以二进制协议缓冲区格式包含图和 MetaGraph 定义。

[SavedModel](https://www.tensorflow.org/api_docs/python/tf/saved_model) 格式的优点包括：

+   您可以将多个共享单一变量和资产的图添加到单个 SavedModel 中。每个图都与一组特定的标签相关联，以允许在加载或恢复操作期间进行识别。

+   支持 SignatureDefs。图输入和输出的定义（包括每个输入和输出的形状和类型）称为 Signature。SavedModel 使用 [SignatureDefs](http://bit.ly/tensorflow-signature-defs) 允许通用支持可能需要与图一起保存的签名。

+   支持资产。在某些情况下，TensorFlow 操作依赖于外部文件进行初始化，例如，词汇表。SavedModel 将这些附加文件导出到资产目录中。

这是一个 Python 代码片段（[完整代码在此处可用](http://bit.ly/tensorflow-winequalityclass-savedmodel)），展示了如何以保存的模型格式保存训练好的模型：

##### 示例 2-3\. 从 Keras 模型中导出保存的模型

```
#export_version =...  # version number (integer)
export_dir = "savedmodels/WineQuality/"
builder = saved_model_builder.SavedModelBuilder(export_dir)
signature = predict_signature_def(inputs={'winedata': model.input},
  outputs={'quality': model.output})
builder.add_meta_graph_and_variables(sess=sess,
  tags=[tag_constants.SERVING],
  signature_def_map={'predict': signature})
builder.save()
```

通过用这段代码替换 示例 2-1 中的导出执行图，可以从你的多分类问题中获得一个保存的模型。

将模型导出到目录后，可以用于提供服务。示例 2-4（[完整代码在此处可用](http://bit.ly/lightbend-ts-wine)）利用 TensorFlow Java API 加载并对模型进行评分。

##### 示例 2-4\. 基于从 Keras 模型中保存的模型提供模型

```
object WineModelServingBundle {
 def apply(path: String, label: String): WineModelServingBundle =
new WineModelServingBundle(path, label)
 def main(args: Array[String]): Unit = {
   val data_path = "/winequality_red.csv"
   val saved_model_path = "/savedmodels/WineQuality"
   val label = "serve"
   val model = WineModelServingBundle(saved_model_path, label)
   val inputs = getListOfRecords(data_path)
   inputs.foreach(record =>
     println(s"result ${model.score(record._1)}
       expected ${record._2}"))
   model.cleanup()
 }
...
class WineModelServingBundle(path : String, label : String){
 val bundle = SavedModelBundle.load(path, label)
 val ls: Session = bundle.session
 val metaGraphDef = MetaGraphDef.parseFrom(bundle.metaGraphDef())
 val signatures = parseSignature(
   metaGraphDef.getSignatureDefMap.asScala)
 def score(record : Array[Float]) : Double = {
   val input = Tensor.create(Array(record))
   val result = ls.runner.feed(signatures(0).inputs(0).name, input)
 .fetch(signatures(0).outputs(0).name).run().get(0)
   ...
 }
...
 def convertParameters(tensorInfo: Map[String,TensorInfo]) :
   Seq[Parameter] = {
   var parameters = Seq.empty[Parameter]
   tensorInfo.foreach(input => {
     ...
     fields.foreach(descriptor => {
       descriptor._2.asInstanceOf[TensorShapeProto].getDimList
      .toArray.map(d => d.asInstanceOf[
        TensorShapeProto.Dim].getSize)
      .toSeq.foreach(v => shape = shape :+ v.toInt)
      .foreach(v => shape = shape :+ v.toInt)
       }
       if(descriptor._1.getName.contains("name") ) {
         name = descriptor._2.toString.split(":")(0)
       }
       if(descriptor._1.getName.contains("dtype") ) {
         dtype = descriptor._2.toString
       }
     })
     parameters = Parameter(name, dtype, shape) +: parameters
   })
   parameters
 }
 def parseSignature(signatureMap : Map[String, SignatureDef])
   : Seq[Signature] = {

   var signatures = Seq.empty[Signature]
   signatureMap.foreach(definition => {
     val inputDefs = definition._2.getInputsMap.asScala
     val outputDefs = definition._2.getOutputsMap.asScala
     val inputs = convertParameters(inputDefs)
     val outputs = convertParameters(outputDefs)
     signatures = Signature(definition._1, inputs, outputs)
       +: signatures
   })
   signatures
 }
}
...
```

将此代码与 示例 2-2 中的代码进行比较。虽然主要结构相同，但有两个重要的区别：

+   读取图表更加复杂。保存的模型不仅包含图表本身，还包含整个捆绑包（目录），然后从捆绑包中获取图表。此外，还可以提取方法签名（作为 protobuf 定义）并解析它以获取执行方法的输入和输出。请记住，通常情况下，从捆绑包中读取的图表可以包含多个签名，因此需要按名称选择适当的签名。这个名称在模型保存时定义（*winedata*，在 示例 2-3 中定义）。在代码中，因为我知道只有一个签名，所以我只取了数组的第一个元素。

+   在实现方法中，我不是硬编码输入和输出的名称，而是依赖于签名定义。

###### 警告

在保存参数名称时，TensorFlow 使用 *name:column* 的约定。例如，在我们的情况下，输入名称 *dense_1_input*，带有单列（0），表示为 *dense_1_input:0*。Java API 不支持此表示法，因此代码在“:”处拆分名称并仅返回第一个子字符串。

另外，目前正在进行 [工作](https://github.com/jpmml/jpmml-tensorflow) 将 TensorFlow 导出的模型（以保存模型格式）转换为 PMML。完成这项工作后，开发人员将有额外的选择来构建从 TensorFlow 导出的模型的评分解决方案。

# PMML

在我们的下一个示例中，使用与 TensorFlow 示例中的多类别分类相同的葡萄酒质量数据集，我们展示了如何使用[JPMML/SparkML](https://github.com/jpmml/jpmml-sparkml)导出 SparkML 机器学习模型的[随机森林分类器](https://en.wikipedia.org/wiki/Random_forest)。代码如示例 2-5 所示（[完整代码在此处可用](http://bit.ly/wine-quality-random-forest)）。

##### 示例 2-5. 使用带有 PMML 导出的 SparkML 的随机森林分类器

```
object WineQualityRandomForestClassifierPMML {
 def main(args: Array[String]): Unit = {
   ...
   // Load and parse the data file
   ...
   // Decision Tree operates on feature vectors
   val assembler = new VectorAssembler().
     setInputCols(inputFields.toArray).setOutputCol("features")
   // Fit on whole dataset to include all labels in index.
   val labelIndexer = new StringIndexer()
     .setInputCol("quality").setOutputCol("indexedLabel").fit(dff)
   // Create classifier
   val dt = new RandomForestClassifier().setLabelCol("indexedLabel")
      .setFeaturesCol("features").setNumTrees(10)
   // Convert indexed labels back to original labels.
   val labelConverter= new IndexToString().setInputCol("prediction")
    .setOutputCol("predictedLabel").setLabels(labelIndexer.labels)
   // Create pileline
   val pipeline = new Pipeline()
     .setStages(Array(assembler, labelIndexer, dt, labelConverter))
   // Train model
   val model = pipeline.fit(dff)
   // PMML
   val schema = dff.schema
   val pmml = ConverterUtil.toPMML(schema, model)
   MetroJAXBUtil.marshalPMML(pmml, System.out)
   spark.stop()
 }
}
```

代码的大部分定义了机器学习管道，其中包含以下组件：

[向量装配器](http://bit.ly/2gcnBQq)

将给定列的列表组合成单个向量列的转换器。

[标签索引器](http://bit.ly/2yFAxpr)

这将字符串标签列编码为标签索引列。

[分类器](http://bit.ly/2zgdGh2)

这里使用了随机森林分类器，它属于流行的分类和回归方法家族。

[标签转换器](http://bit.ly/2xzgkl6)

将标签索引列映射回包含原始标签的字符串列。

构建管道后，对其进行训练，然后 PMML 导出器使用数据帧模式和管道定义将完整管道及其参数以 PMML 格式导出。

导出模型后，您可以用于评分。示例 2-6 使用[JPMML 评估器库](https://github.com/jpmml/jpmml-evaluator)加载和评分模型（[完整代码在此处可用](http://bit.ly/randomforest-wine-complete-example)）。

##### 示例 2-6. 服务 PMML 模型

```
class WineQualityRandomForestClassifier(path : String) {
 import WineQualityRandomForestClassifier._
 var arguments = mutable.Map[FieldName, FieldValue]()
 // constructor
 val pmml: PMML = readPMML(path)
 optimize(pmml)
 // Create and verify evaluator
 val evaluator = ModelEvaluatorFactory.newInstance()
   .newModelEvaluator(pmml)
 evaluator.verify()
 // Get input/target fields
 val inputFields = evaluator.getInputFields
 val target: TargetField = evaluator.getTargetFields.get(0)
 val tname = target.getName

 def score(record : Array[Float]) : Double = {
   arguments.clear()
   inputFields.foreach(field => {
     arguments.put(field.getName, field
       .prepare(getValueByName(record, field.getName.getValue)))
   })
   // Calculate output
   val result = evaluator.evaluate(arguments)
   // Convert output
   result.get(tname) match {
      case c : Computable => c.getResult.toString.toDouble
      case v : Any => v.asInstanceOf[Double]
   }
 }
...
object WineQualityRandomForestClassifier {
 def main(args: Array[String]): Unit = {
   val model_path = "data/
     winequalityRandonForrestClassification.pmml"
   val data_path = "data/winequality_red.csv"
   val lmodel = new WineQualityRandomForestClassifier(model_path)
   val inputs = getListOfRecords(data_path)
   inputs.foreach(record =>
     println(s"result ${lmodel.score(record._1)}"))
 }
 def readPMML(file: String): PMML = {
   var is = null.asInstanceOf[InputStream]
   try {
     is = new FileInputStream(file)
     PMMLUtil.unmarshal(is)
   }
   finally if (is != null) is.close()
 }
 private val optimizers = ...
 def optimize(pmml : PMML) = this.synchronized {
   ...
 }
...
}
```

在这个简单的示例中，构造函数调用`readPMML`方法读取 PMML 模型，然后调用 optimize 方法。我们使用优化的 PMML（[优化器](http://bit.ly/optimizers-gl-topic)更改默认生成以实现更高效的执行）表示，该表示用于创建评估器。

score 方法接受包含质量观察结果的输入记录，并将它们转换为评估器可接受的格式。然后，将数据传递给评估器以生成评分。最后，从结果中提取实际值。

执行由`WineQualityRandomForestClassifier`对象中的主方法编排。该方法首先创建`WineQualityRandomForestClassifier`类的一个实例，然后读取输入记录列表，并在每条记录上调用`WineQualityRandomForestClassifier`类实例中的 serve 方法。

现在我们知道如何导出模型了，让我们讨论如何将这些模型用于实际模型评分。
