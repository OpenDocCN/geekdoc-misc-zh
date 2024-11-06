# 浅拷贝对象

> 原文：[`typescriptbook.jp/tips/shallow-copy-object`](https://typescriptbook.jp/tips/shallow-copy-object)

对象可以将各种键和属性的组合视为一个单独的实体。

在处理对象时，对于实例的比较和赋值与其他语言一样是引用的比较和赋值。如果其他地方持有该引用，则可能会被修改。

## 容易导致覆盖实例的弊端​

假设我们要创建一个关于生活习惯疾病的服务。该服务允许用户输入一天的饮食，计算热量，并且可以判断未来是否会患上生活习惯疾病（稍有不同，但我们将其称为代谢综合征）。

假设我们定义了一个表示一天饮食的对象类型为`MealsPerDay`，并定义了一个函数`willBeMetabo()`，用于根据一天摄入的食物热量判断是否会患上生活习惯疾病，则代码如下。

```
ts`type  <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp>  = { <data-lsp lsp="(property) breakfast: string">breakfast</data-lsp>:  string; <data-lsp lsp="(property) lunch: string">lunch</data-lsp>:  string; <data-lsp lsp="(property) dinner: string">dinner</data-lsp>:  string;};function  <data-lsp lsp="function willBeMetabo(meals: MealsPerDay): boolean">willBeMetabo</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>:  <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp>):  boolean {  // ...}`
```

```
ts`type <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp> = { <data-lsp lsp="(property) breakfast: string">breakfast</data-lsp>:  string; <data-lsp lsp="(property) lunch: string">lunch</data-lsp>:  string; <data-lsp lsp="(property) dinner: string">dinner</data-lsp>:  string;};function <data-lsp lsp="function willBeMetabo(meals: MealsPerDay): boolean">willBeMetabo</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>: <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp>):  boolean {  // ...}`
```

使用方法如下：

```
ts`// 439.2 kcalconst  <data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>:  <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp>  = { <data-lsp lsp="(property) breakfast: string">breakfast</data-lsp>:  "a vegetable salad", <data-lsp lsp="(property) lunch: string">lunch</data-lsp>:  "a cod's meuniere", <data-lsp lsp="(property) dinner: string">dinner</data-lsp>:  "a half bottle of wine (white)",};<data-lsp lsp="function willBeMetabo(meals: MealsPerDay): boolean">willBeMetabo</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);false`
```

```
ts`// 439.2 kcalconst  <data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>: <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp> = { <data-lsp lsp="(property) breakfast: string">breakfast</data-lsp>:  "a vegetable salad", <data-lsp lsp="(property) lunch: string">lunch</data-lsp>:  "a cod's meuniere", <data-lsp lsp="(property) dinner: string">dinner</data-lsp>:  "a half bottle of wine (white)",};<data-lsp lsp="function willBeMetabo(meals: MealsPerDay): boolean">willBeMetabo</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);false`
```

但是，仅仅这样做可能会导致服务对于非食物类输入（例如螺丝）做出意料之外的反应。因此，我们定义一个验证函数`isMeals()`，用于验证输入是否真的是食物。当输入非食物时，该函数会抛出异常。

`isMeals()`的结构很简单。它只是判断早餐、午餐和晚餐是否是食物。如果有一个判断食物的函数`isMeal()`，那么它只需在内部调用它。由于本次讨论重点不在`isMeal()`的实现上，因此省略了。

```
ts`function  <data-lsp lsp="function isMeals(meals: MealsPerDay): void">isMeals</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>:  <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp>):  void {  if (!<data-lsp lsp="function isMeal(something: string): boolean">isMeal</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) breakfast: string">breakfast</data-lsp>)) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("BREAKFAST IS NOT A MEAL!"); }  if (!<data-lsp lsp="function isMeal(something: string): boolean">isMeal</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) lunch: string">lunch</data-lsp>)) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("LUNCH IS NOT A MEAL!!!"); }  if (!<data-lsp lsp="function isMeal(something: string): boolean">isMeal</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) dinner: string">dinner</data-lsp>)) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("DINNER IS NOT A MEAL!!!"); }}`
```

```
ts`function <data-lsp lsp="function isMeals(meals: MealsPerDay): void">isMeals</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>: <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp>):  void {  if (!<data-lsp lsp="function isMeal(something: string): boolean">isMeal</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) breakfast: string">breakfast</data-lsp>)) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("BREAKFAST IS NOT A MEAL!"); }  if (!<data-lsp lsp="function isMeal(something: string): boolean">isMeal</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) lunch: string">lunch</data-lsp>)) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("LUNCH IS NOT A MEAL!!!"); }  if (!<data-lsp lsp="function isMeal(something: string): boolean">isMeal</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) dinner: string">dinner</data-lsp>)) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("DINNER IS NOT A MEAL!!!"); }}`
```

在本用例中，我们首先通过`isMeals()`进行验证，然后通过`willBeMetabo()`进行判断。如果输入了无法食用的物品，只要能捕获异常并处理即可，大致上会是这种形式。

```
ts`function  <data-lsp lsp="function shouldBeCareful(meals: MealsPerDay): boolean">shouldBeCareful</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>:  <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp>):  boolean {  try {  // ...  <data-lsp lsp="function isMeals(meals: MealsPerDay): void">isMeals</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>);  return  <data-lsp lsp="function willBeMetabo(meals: MealsPerDay): boolean">willBeMetabo</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>); } catch (<data-lsp lsp="(local var) err: unknown">err</data-lsp>:  unknown) {  // ... }}`
```

```
ts`function <data-lsp lsp="function shouldBeCareful(meals: MealsPerDay): boolean">shouldBeCareful</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>: <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp>):  boolean {  try {  // ... <data-lsp lsp="function isMeals(meals: MealsPerDay): void">isMeals</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>);  return <data-lsp lsp="function willBeMetabo(meals: MealsPerDay): boolean">willBeMetabo</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>); } catch (<data-lsp lsp="(local var) err: unknown">err</data-lsp>:  unknown) {  // ... }}`
```

假设`isMeals()`的作者或维护者在`isMeals()`中写了一段代码，将自己喜欢的高热量食物覆盖了原始实例。由于这个更改，原本应该摄入非常健康且不到 500 卡路里的食物的用户，现在却摄入了 19,800 卡路里的热量炸弹。

```
ts`function  <data-lsp lsp="function isMeals(meals: MealsPerDay): void">isMeals</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>:  <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp>):  void {  <data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) breakfast: string">breakfast</data-lsp> =  "a beef steak";  // beef steak will be 1200 kcal  <data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) lunch: string">lunch</data-lsp> =  "a bucket of ice cream";  // a bucket of ice cream will be 7200 kcal  <data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) dinner: string">dinner</data-lsp> =  "3 pizzas";  // 3 pizzas will be 11400 kcal  if (!<data-lsp lsp="function isMeal(meal: string): boolean">isMeal</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) breakfast: string">breakfast</data-lsp>)) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("BREAKFAST IS NOT MEAL!"); }  if (!<data-lsp lsp="function isMeal(meal: string): boolean">isMeal</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) lunch: string">lunch</data-lsp>)) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("LUNCH IS NOT MEAL!!!"); }  if (!<data-lsp lsp="function isMeal(meal: string): boolean">isMeal</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) dinner: string">dinner</data-lsp>)) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("DINNER IS NOT MEAL!!!"); }}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);439.2 kcal<data-lsp lsp="function isMeals(meals: MealsPerDay): void">isMeals</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);19,800 kcal!!!<data-lsp lsp="function willBeMetabo(meals: MealsPerDay): boolean">willBeMetabo</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);true`
```

```
ts`function <data-lsp lsp="function isMeals(meals: MealsPerDay): void">isMeals</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>: <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp>):  void {  <data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) breakfast: string">breakfast</data-lsp> =  "a beef steak";  // beef steak will be 1200 kcal  <data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) lunch: string">lunch</data-lsp> =  "a bucket of ice cream";  // a bucket of ice cream will be 7200 kcal  <data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) dinner: string">dinner</data-lsp> =  "3 pizzas";  // 3 pizzas will be 11400 kcal  if (!<data-lsp lsp="function isMeal(meal: string): boolean">isMeal</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) breakfast: string">breakfast</data-lsp>)) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("BREAKFAST IS NOT MEAL!"); }  if (!<data-lsp lsp="function isMeal(meal: string): boolean">isMeal</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) lunch: string">lunch</data-lsp>)) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("LUNCH IS NOT MEAL!!!"); }  if (!<data-lsp lsp="function isMeal(meal: string): boolean">isMeal</data-lsp>(<data-lsp lsp="(parameter) meals: MealsPerDay">meals</data-lsp>.<data-lsp lsp="(property) dinner: string">dinner</data-lsp>)) {  throw  new  <data-lsp lsp="var Error: ErrorConstructor
new (message?: string | undefined) => Error">Error</data-lsp>("DINNER IS NOT MEAL!!!"); }}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);439.2 kcal<data-lsp lsp="function isMeals(meals: MealsPerDay): void">isMeals</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);19,800 kcal!!!<data-lsp lsp="function willBeMetabo(meals: MealsPerDay): boolean">willBeMetabo</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);true`
```

如果调用`isMeals()`，那么无论输入什么食物，`willBeMetabo()`都会判断所有人都会患上生活习惯疾病。`meals`的更改不仅限于`isMeals()`内部，还会影响外部。

### 这个问题​

这个例子中，`isMeals()`出了问题。如果这个函数是由我们自己编写的，我们可能会很快找到问题的原因。避免编写这种有问题的函数当然很重要，但更重要的是设计不会犯错的系统，而不是假设人类不会犯错。

如果`isMeals()`是外部引入的包，那就有问题了。由于我们无法轻易修改这个包（虽然不是不可能），因此向制作者提交错误修复的请求并等待开发停止是不现实的。

### 该怎么做才是正确的​

通常情况下，要么禁止修改实例，要么为了避免原始实例被破坏而准备一个替罪羊实例是常见做法。前者代表了所谓的值对象。这里介绍的是后者的替罪羊，即准备拷贝的方法。

## 浅拷贝（shallow copy）是什么​

正如标题所示，**浅拷贝**指的是什么？这意味着在拷贝对象时，无论对象有多深的结构（即嵌套），只会拷贝第一层。显然，其反义词是深拷贝（deep copy）。

### 浅拷贝的对象是不相等的​

将浅拷贝函数命名为`shallowCopy()`。实现并不复杂，但由于这里只想讨论行为，所以具体实现将在后面提到。浅拷贝的对象和原始对象使用`===`进行比较时会返回`false`。这是符合拷贝的原始含义的行为，如果返回`true`，则表示拷贝失败。

```
ts`const  <data-lsp lsp="const object1: object">object1</data-lsp>:  object  = {};const  <data-lsp lsp="const object2: object">object2</data-lsp>:  object  =  <data-lsp lsp="function shallowCopy(obj: object): object">shallowCopy</data-lsp>(<data-lsp lsp="const object1: object">object1</data-lsp>);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const object1: object">object1</data-lsp> === <data-lsp lsp="const object2: object">object2</data-lsp>);false`
```

```
ts`const  <data-lsp lsp="const object1: object">object1</data-lsp>:  object  = {};const  <data-lsp lsp="const object2: object">object2</data-lsp>:  object  = <data-lsp lsp="function shallowCopy(obj: object): object">shallowCopy</data-lsp>(<data-lsp lsp="const object1: object">object1</data-lsp>);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const object1: object">object1</data-lsp> === <data-lsp lsp="const object2: object">object2</data-lsp>);false`
```

以下示例展示了通过浅拷贝来避免覆盖先前实例的示例。`meals`实例保持不变，只有作为参数传递给`isMeals()`的`scapegoat`发生了变化。

```
ts`const  <data-lsp lsp="const scapegoat: MealsPerDay">scapegoat</data-lsp>:  <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp>  =  <data-lsp lsp="function shallowCopy(meals: MealsPerDay): MealsPerDay">shallowCopy</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);{ breakfast: "a vegetable salad", lunch: "a cod's meuniere", dinner: "a half bottle of wine (white)" }<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const scapegoat: MealsPerDay">scapegoat</data-lsp>);{ breakfast: "a vegetable salad", lunch: "a cod's meuniere", dinner: "a half bottle of wine (white)" }<data-lsp lsp="function isMeals(meals: MealsPerDay): void">isMeals</data-lsp>(<data-lsp lsp="const scapegoat: MealsPerDay">scapegoat</data-lsp>);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);{ breakfast: "a vegetable salad", lunch: "a cod's meuniere", dinner: "a half bottle of wine (white)" }<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const scapegoat: MealsPerDay">scapegoat</data-lsp>);{ breakfast: "a beef steak", lunch: "a bucket of ice cream", dinner: "3 pizzas" }`
```

```
ts`const  <data-lsp lsp="const scapegoat: MealsPerDay">scapegoat</data-lsp>: <data-lsp lsp="type MealsPerDay = {
    breakfast: string;
    lunch: string;
    dinner: string;
}">MealsPerDay</data-lsp> = <data-lsp lsp="function shallowCopy(meals: MealsPerDay): MealsPerDay">shallowCopy</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);{ breakfast: "a vegetable salad", lunch: "a cod's meuniere", dinner: "a half bottle of wine (white)" }<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const scapegoat: MealsPerDay">scapegoat</data-lsp>);{ breakfast: "a vegetable salad", lunch: "a cod's meuniere", dinner: "a half bottle of wine (white)" }<data-lsp lsp="function isMeals(meals: MealsPerDay): void">isMeals</data-lsp>(<data-lsp lsp="const scapegoat: MealsPerDay">scapegoat</data-lsp>);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const meals: MealsPerDay">meals</data-lsp>);{ breakfast: "a vegetable salad", lunch: "a cod's meuniere", dinner: "a half bottle of wine (white)" }<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const scapegoat: MealsPerDay">scapegoat</data-lsp>);{ breakfast: "a beef steak", lunch: "a bucket of ice cream", dinner: "3 pizzas" }`
```

### 如果无法通过浅拷贝来避免​

正如前面所述，浅拷贝只会拷贝对象的第一层。因此，如果对象具有深层次、复杂的结构，那么除了第二层以外的部分都将变成简单的引用。下面的示例展示了当浅拷贝的属性中包含对象时，这些对象不是被复制而是被引用的情况。

```
ts`type  <data-lsp lsp="type NestObject = {
    nest: object;
}">NestObject</data-lsp>  = { <data-lsp lsp="(property) nest: object">nest</data-lsp>:  object;};const  <data-lsp lsp="const object1: NestObject">object1</data-lsp>:  <data-lsp lsp="type NestObject = {
    nest: object;
}">NestObject</data-lsp>  = { <data-lsp lsp="(property) nest: object">nest</data-lsp>: {},};const  <data-lsp lsp="const object2: NestObject">object2</data-lsp>:  <data-lsp lsp="type NestObject = {
    nest: object;
}">NestObject</data-lsp>  =  <data-lsp lsp="function shallowCopy(meals: NestObject): NestObject">shallowCopy</data-lsp>(<data-lsp lsp="const object1: NestObject">object1</data-lsp>);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const object1: NestObject">object1</data-lsp> === <data-lsp lsp="const object2: NestObject">object2</data-lsp>);false<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const object1: NestObject">object1</data-lsp>.<data-lsp lsp="(property) nest: object">nest</data-lsp> ===  <data-lsp lsp="const object2: NestObject">object2</data-lsp>.<data-lsp lsp="(property) nest: object">nest</data-lsp>);true`
```

```
ts`type <data-lsp lsp="type NestObject = {
    nest: object;
}">NestObject</data-lsp> = { <data-lsp lsp="(property) nest: object">nest</data-lsp>:  object;};const  <data-lsp lsp="const object1: NestObject">object1</data-lsp>: <data-lsp lsp="type NestObject = {
    nest: object;
}">NestObject</data-lsp> = { <data-lsp lsp="(property) nest: object">nest</data-lsp>: {},};const  <data-lsp lsp="const object2: NestObject">object2</data-lsp>: <data-lsp lsp="type NestObject = {
    nest: object;
}">NestObject</data-lsp> = <data-lsp lsp="function shallowCopy(meals: NestObject): NestObject">shallowCopy</data-lsp>(<data-lsp lsp="const object1: NestObject">object1</data-lsp>);<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const object1: NestObject">object1</data-lsp> === <data-lsp lsp="const object2: NestObject">object2</data-lsp>);false<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const object1: NestObject">object1</data-lsp>.<data-lsp lsp="(property) nest: object">nest</data-lsp> ===  <data-lsp lsp="const object2: NestObject">object2</data-lsp>.<data-lsp lsp="(property) nest: object">nest</data-lsp>);true`
```

如果想要创建完全的拷贝，可以使用深拷贝，与浅拷贝一起使用。

关于深拷贝，本次不会深入讨论。与浅拷贝相比，深拷贝需要更多时间，并且需要复制实体而不是引用，因此需要分配相同数量的存储空间。如果无脑使用深拷贝，很快就会浪费时间和空间。如果浅拷贝足够，那么最好使用浅拷贝。

### 实现浅拷贝​

在当今的 JS 中，浅拷贝的实现变得非常简单，下面的代码就可以完成。

```
ts`const  <data-lsp lsp="const shallowCopied: object">shallowCopied</data-lsp>:  object  = { ...<data-lsp lsp="const sample: object">sample</data-lsp> };`
```

```
ts`const  <data-lsp lsp="const shallowCopied: object">shallowCopied</data-lsp>:  object  = { ...<data-lsp lsp="const sample: object">sample</data-lsp> };`
```

当然变量`sample`必须是一个对象。这里的`...`是展开语法。有关展开语法，请参考函数章节。

从 ES2018 开始，可以使用展开语法来复制对象。例如，以下是浅复制的一个例子

```
ts`const  <data-lsp lsp="const sample: object">sample</data-lsp>:  object  = { <data-lsp lsp="(property) year: number">year</data-lsp>:  1999, <data-lsp lsp="(property) month: number">month</data-lsp>:  7,};const  <data-lsp lsp="const shallowCopied: object">shallowCopied</data-lsp>:  object  = { ...<data-lsp lsp="const sample: object">sample</data-lsp> };`
```

```
ts`const  <data-lsp lsp="const sample: object">sample</data-lsp>:  object  = { <data-lsp lsp="(property) year: number">year</data-lsp>:  1999, <data-lsp lsp="(property) month: number">month</data-lsp>:  7,};const  <data-lsp lsp="const shallowCopied: object">shallowCopied</data-lsp>:  object  = { ...<data-lsp lsp="const sample: object">sample</data-lsp> };`
```

编译为 ES2018 时会变成以下形式。

```
ts`const  <data-lsp lsp="const sample: {
    year: number;
    month: number;
}">sample</data-lsp>  = { <data-lsp lsp="(property) year: number">year</data-lsp>:  1999, <data-lsp lsp="(property) month: number">month</data-lsp>:  7,};const  <data-lsp lsp="const shallowCopied: {
    year: number;
    month: number;
}">shallowCopied</data-lsp>  = { ...<data-lsp lsp="const sample: {
    year: number;
    month: number;
}">sample</data-lsp> };`
```

```
ts`const  <data-lsp lsp="const sample: {
    year: number;
    month: number;
}">sample</data-lsp>  = { <data-lsp lsp="(property) year: number">year</data-lsp>:  1999, <data-lsp lsp="(property) month: number">month</data-lsp>:  7,};const  <data-lsp lsp="const shallowCopied: {
    year: number;
    month: number;
}">shallowCopied</data-lsp>  = { ...<data-lsp lsp="const sample: {
    year: number;
    month: number;
}">sample</data-lsp> };`
```

几乎相同，但是编译为 ES2017 时会变成以下形式。

```
ts`const  <data-lsp lsp="const sample: {
    year: number;
    month: number;
}">sample</data-lsp>  = { <data-lsp lsp="(property) year: number">year</data-lsp>:  1999, <data-lsp lsp="(property) month: number">month</data-lsp>:  7,};const  <data-lsp lsp="const shallowCopied: {
    year: number;
    month: number;
}">shallowCopied</data-lsp>  =  <data-lsp lsp="var Object: ObjectConstructor">Object</data-lsp>.<data-lsp lsp="(method) ObjectConstructor.assign<{}, {
    year: number;
    month: number;
}>(target: {}, source: {
    year: number;
    month: number;
}): {
    year: number;
    month: number;
} (+3 overloads)">assign</data-lsp>({}, <data-lsp lsp="const sample: {
    year: number;
    month: number;
}">sample</data-lsp>);`
```

```
ts`const  <data-lsp lsp="const sample: {
    year: number;
    month: number;
}">sample</data-lsp>  = { <data-lsp lsp="(property) year: number">year</data-lsp>:  1999, <data-lsp lsp="(property) month: number">month</data-lsp>:  7,};const  <data-lsp lsp="const shallowCopied: {
    year: number;
    month: number;
}">shallowCopied</data-lsp>  =  <data-lsp lsp="var Object: ObjectConstructor">Object</data-lsp>.<data-lsp lsp="(method) ObjectConstructor.assign<{}, {
    year: number;
    month: number;
}>(target: {}, source: {
    year: number;
    month: number;
}): {
    year: number;
    month: number;
} (+3 overloads)">assign</data-lsp>({}, <data-lsp lsp="const sample: {
    year: number;
    month: number;
}">sample</data-lsp>);`
```

并且。在实现展开语法之前，我们使用`Object.assign()`。虽然这两者并不完全相同，但可以将`Object.assign({}, obj)`用作`{...obj}`的替代品。

## 使用复制的 API​

在 JavaScript 中，有一些对象提供了用于简洁编写浅复制的 API。`Map`和`Set`就是其中之一。

### `Map<K, V>`的复制​

要复制`Map`，只需将要复制的`Map`对象传递给`Map`构造函数。

```
ts`const  <data-lsp lsp="const map1: Map<string, string>">map1</data-lsp>  =  new  <data-lsp lsp="var Map: MapConstructor
new <string, string>(iterable?: Iterable<readonly [string, string]> | null | undefined) => Map<string, string> (+3 overloads)">Map</data-lsp>([ [".js",  "JS"], [".ts",  "TS"],]);const  <data-lsp lsp="const map2: Map<string, string>">map2</data-lsp>  =  new  <data-lsp lsp="var Map: MapConstructor
new <string, string>(iterable?: Iterable<readonly [string, string]> | null | undefined) => Map<string, string> (+3 overloads)">Map</data-lsp>(<data-lsp lsp="const map1: Map<string, string>">map1</data-lsp>);// 要素は同一だが、Mapインスタンスは異なる<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const map2: Map<string, string>">map2</data-lsp>);Map (2) {".js" => "JS", ".ts" => "TS"}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const map1: Map<string, string>">map1</data-lsp> !== <data-lsp lsp="const map2: Map<string, string>">map2</data-lsp>);true`
```

```
ts`const  <data-lsp lsp="const map1: Map<string, string>">map1</data-lsp>  =  new  <data-lsp lsp="var Map: MapConstructor
new <string, string>(iterable?: Iterable<readonly [string, string]> | null | undefined) => Map<string, string> (+3 overloads)">Map</data-lsp>([ [".js",  "JS"], [".ts",  "TS"],]);const  <data-lsp lsp="const map2: Map<string, string>">map2</data-lsp>  =  new  <data-lsp lsp="var Map: MapConstructor
new <string, string>(iterable?: Iterable<readonly [string, string]> | null | undefined) => Map<string, string> (+3 overloads)">Map</data-lsp>(<data-lsp lsp="const map1: Map<string, string>">map1</data-lsp>);// 要素は同一だが、Mapインスタンスは異なる<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const map2: Map<string, string>">map2</data-lsp>);Map (2) {".js" => "JS", ".ts" => "TS"}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const map1: Map<string, string>">map1</data-lsp> !== <data-lsp lsp="const map2: Map<string, string>">map2</data-lsp>);true`
```

## 📄️ Map<K, V>

Map 是 JavaScript 的内置 API 之一，用于处理键值对的对象。Map 对于每个键只能存储一个值。

### `Set<T>`的复制[​

要复制`Set`，只需将要复制的`Set`对象传递给`Set`构造函数。

```
ts`const  <data-lsp lsp="const set1: Set<number>">set1</data-lsp>  =  new  <data-lsp lsp="var Set: SetConstructor
new <number>(iterable?: Iterable<number> | null | undefined) => Set<number> (+1 overload)">Set</data-lsp>([1,  2,  3]);const  <data-lsp lsp="const set2: Set<number>">set2</data-lsp>  =  new  <data-lsp lsp="var Set: SetConstructor
new <number>(iterable?: Iterable<number> | null | undefined) => Set<number> (+1 overload)">Set</data-lsp>(<data-lsp lsp="const set1: Set<number>">set1</data-lsp>);// 要素は同一だが、Setのインスタンスは異なる<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const set2: Set<number>">set2</data-lsp>);Set (3) {1, 2, 3}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const set1: Set<number>">set1</data-lsp> !== <data-lsp lsp="const set2: Set<number>">set2</data-lsp>);true`
```

```
ts`const  <data-lsp lsp="const set1: Set<number>">set1</data-lsp>  =  new  <data-lsp lsp="var Set: SetConstructor
new <number>(iterable?: Iterable<number> | null | undefined) => Set<number> (+1 overload)">Set</data-lsp>([1,  2,  3]);const  <data-lsp lsp="const set2: Set<number>">set2</data-lsp>  =  new  <data-lsp lsp="var Set: SetConstructor
new <number>(iterable?: Iterable<number> | null | undefined) => Set<number> (+1 overload)">Set</data-lsp>(<data-lsp lsp="const set1: Set<number>">set1</data-lsp>);// 要素は同一だが、Setのインスタンスは異なる<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const set2: Set<number>">set2</data-lsp>);Set (3) {1, 2, 3}<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const set1: Set<number>">set1</data-lsp> !== <data-lsp lsp="const set2: Set<number>">set2</data-lsp>);true`
```

## 📄️ Set<T>

Set 是 JavaScript 的内置 API 之一，用于处理值的集合对象。Set 不能存储重复的值。存储在 Set 中的值是唯一的。

### `Array<T>`的复制[​

有多种方法可以复制数组，但最简单的方法是使用数组的展开语法。

```
ts`const  <data-lsp lsp="const array1: number[]">array1</data-lsp>  = [1,  2,  3];const  <data-lsp lsp="const array2: number[]">array2</data-lsp>  = [...<data-lsp lsp="const array1: number[]">array1</data-lsp>];`
```

```
ts`const  <data-lsp lsp="const array1: number[]">array1</data-lsp>  = [1,  2,  3];const  <data-lsp lsp="const array2: number[]">array2</data-lsp>  = [...<data-lsp lsp="const array1: number[]">array1</data-lsp>];`
```

在这种情况下，如果忘记写展开语法`...`，将会得到数组的数组`T[][]`类型，所以请注意。

## 相关信息​

## 📄️ 数组的展开语法「...」

在 JavaScript 的数组中，可以使用展开语法「...」来展开元素。
