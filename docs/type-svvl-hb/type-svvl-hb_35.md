# 合并对象

> 原文：[`typescriptbook.jp/tips/merge-objects`](https://typescriptbook.jp/tips/merge-objects)

在前一页我们讨论了对象的浅拷贝。

在那里，通过之前提到的扩展语法 (`...`)，我们发现可以轻松地进行浅拷贝。

这次我们考虑合并两个以上的对象。由于要利用前一页关于对象浅拷贝的知识，如果您还没有阅读，请先阅读，然后再查看这里。

## 📄️ 浅拷贝对象

对象可以将各种键和属性组合为一个单独的实体。

## 这次要进行的合并请参考​

我们经常在 Git 等 VCS（版本控制系统）中听到合并这个词。一般来说，合并涉及到合并方和被合并方，合并方会将被合并方的所有内容（有时可以选择）移动或复制过来。

在 JavaScript、TypeScript 中，代码基础上的合并与 VCS 中的略有不同，主流做法是从两个对象中生成一个新的合并对象。

### 要进行合并，请参考​

使用对象浅拷贝的知识。作为复习，浅拷贝只需使用扩展语法即可写成如下形式。

```
ts`const  <data-lsp lsp="const copied: {}">copied</data-lsp>  = { ...<data-lsp lsp="const obj: object">obj</data-lsp> };`
```

```
ts`const  <data-lsp lsp="const copied: {}">copied</data-lsp>  = { ...<data-lsp lsp="const obj: object">obj</data-lsp> };`
```

对象的合并只需将要合并的对象像参数一样用扩展语法排列即可完成拷贝

```
ts`const  <data-lsp lsp="const merged: {}">merged</data-lsp>  = { ...<data-lsp lsp="const obj1: object">obj1</data-lsp>,  ...<data-lsp lsp="const obj2: object">obj2</data-lsp> };`
```

```
ts`const  <data-lsp lsp="const merged: {}">merged</data-lsp>  = { ...<data-lsp lsp="const obj1: object">obj1</data-lsp>,  ...<data-lsp lsp="const obj2: object">obj2</data-lsp> };`
```

### 写成愉快的事情​

オブジェクト的合并不仅限于两个，可以合并任意数量的对象。

```
ts`const  <data-lsp lsp="const merged: {}">merged</data-lsp>  = {  ...<data-lsp lsp="const obj1: object">obj1</data-lsp>,  ...<data-lsp lsp="const obj2: object">obj2</data-lsp>,  ...<data-lsp lsp="const obj3: object">obj3</data-lsp>,  // ...};`
```

```
ts`const  <data-lsp lsp="const merged: {}">merged</data-lsp>  = {  ...<data-lsp lsp="const obj1: object">obj1</data-lsp>,  ...<data-lsp lsp="const obj2: object">obj2</data-lsp>,  ...<data-lsp lsp="const obj3: object">obj3</data-lsp>,  // ...};`
```

由于已经在 ES2017 中输出了浅拷贝，因此这里也一并输出。

```
ts`const  <data-lsp lsp="const merged: object">merged</data-lsp>  =  <data-lsp lsp="var Object: ObjectConstructor">Object</data-lsp>.<data-lsp lsp="(method) ObjectConstructor.assign<object, object>(target: object, source: object): object (+3 overloads)">assign</data-lsp>(<data-lsp lsp="var Object: ObjectConstructor">Object</data-lsp>.<data-lsp lsp="(method) ObjectConstructor.assign<object, object>(target: object, source: object): object (+3 overloads)">assign</data-lsp>(<data-lsp lsp="var Object: ObjectConstructor">Object</data-lsp>.<data-lsp lsp="(method) ObjectConstructor.assign<{}, object>(target: {}, source: object): object (+3 overloads)">assign</data-lsp>({}, <data-lsp lsp="const obj1: object">obj1</data-lsp>), <data-lsp lsp="const obj2: object">obj2</data-lsp>), <data-lsp lsp="const obj3: object">obj3</data-lsp>);`
```

```
ts`const  <data-lsp lsp="const merged: object">merged</data-lsp>  =  <data-lsp lsp="var Object: ObjectConstructor">Object</data-lsp>.<data-lsp lsp="(method) ObjectConstructor.assign<object, object>(target: object, source: object): object (+3 overloads)">assign</data-lsp>(<data-lsp lsp="var Object: ObjectConstructor">Object</data-lsp>.<data-lsp lsp="(method) ObjectConstructor.assign<object, object>(target: object, source: object): object (+3 overloads)">assign</data-lsp>(<data-lsp lsp="var Object: ObjectConstructor">Object</data-lsp>.<data-lsp lsp="(method) ObjectConstructor.assign<{}, object>(target: {}, source: object): object (+3 overloads)">assign</data-lsp>({}, <data-lsp lsp="const obj1: object">obj1</data-lsp>), <data-lsp lsp="const obj2: object">obj2</data-lsp>), <data-lsp lsp="const obj3: object">obj3</data-lsp>);`
```

编译为。顺便说一句，这有点冗长

```
ts`const  <data-lsp lsp="const merged: object">merged</data-lsp>  =  <data-lsp lsp="var Object: ObjectConstructor">Object</data-lsp>.<data-lsp lsp="(method) ObjectConstructor.assign<{}, object, object, object>(target: {}, source1: object, source2: object, source3: object): object (+3 overloads)">assign</data-lsp>({}, <data-lsp lsp="const obj1: object">obj1</data-lsp>, <data-lsp lsp="const obj2: object">obj2</data-lsp>, <data-lsp lsp="const obj3: object">obj3</data-lsp>);`
```

```
ts`const  <data-lsp lsp="const merged: object">merged</data-lsp>  =  <data-lsp lsp="var Object: ObjectConstructor">Object</data-lsp>.<data-lsp lsp="(method) ObjectConstructor.assign<{}, object, object, object>(target: {}, source1: object, source2: object, source3: object): object (+3 overloads)">assign</data-lsp>({}, <data-lsp lsp="const obj1: object">obj1</data-lsp>, <data-lsp lsp="const obj2: object">obj2</data-lsp>, <data-lsp lsp="const obj3: object">obj3</data-lsp>);`
```

也会得到相同的结果。

### 注意事项​

如果存在相同的键，请务必优先考虑最后写入的内容。请注意不要覆盖值。

```
ts`const  <data-lsp lsp="const obj1: object">obj1</data-lsp>:  object  = { <data-lsp lsp="(property) firstName: string">firstName</data-lsp>:  "Otto", <data-lsp lsp="(property) middleName: string">middleName</data-lsp>:  "von", <data-lsp lsp="(property) lastName: string">lastName</data-lsp>:  "Bismarck",};const  <data-lsp lsp="const obj2: object">obj2</data-lsp>:  object  = { <data-lsp lsp="(property) firstName: string">firstName</data-lsp>:  "Yuko", <data-lsp lsp="(property) lastName: string">lastName</data-lsp>:  "Sato",};const  <data-lsp lsp="const merged: object">merged</data-lsp>:  object  = { ...<data-lsp lsp="const obj1: object">obj1</data-lsp>,  ...<data-lsp lsp="const obj2: object">obj2</data-lsp> };<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const merged: object">merged</data-lsp>);{ firstName: "Yuko", middleName: "von" lastName: "Sato" }`
```

```
ts`const  <data-lsp lsp="const obj1: object">obj1</data-lsp>:  object  = { <data-lsp lsp="(property) firstName: string">firstName</data-lsp>:  "Otto", <data-lsp lsp="(property) middleName: string">middleName</data-lsp>:  "von", <data-lsp lsp="(property) lastName: string">lastName</data-lsp>:  "Bismarck",};const  <data-lsp lsp="const obj2: object">obj2</data-lsp>:  object  = { <data-lsp lsp="(property) firstName: string">firstName</data-lsp>:  "Yuko", <data-lsp lsp="(property) lastName: string">lastName</data-lsp>:  "Sato",};const  <data-lsp lsp="const merged: object">merged</data-lsp>:  object  = { ...<data-lsp lsp="const obj1: object">obj1</data-lsp>,  ...<data-lsp lsp="const obj2: object">obj2</data-lsp> };<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const merged: object">merged</data-lsp>);{ firstName: "Yuko", middleName: "von" lastName: "Sato" }`
```
