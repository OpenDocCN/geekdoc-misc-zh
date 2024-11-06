# TypeScript 的特点

> 原文：[`typescriptbook.jp/overview/features`](https://typescriptbook.jp/overview/features)

TypeScript 是由微软于 2012 年 10 月 1 日首次宣布的，可扩展的 JavaScript 的超集语言。可扩展的语言是指在项目规模或开发团队规模增加时仍然能够正常工作的语言，而 TypeScript 由于其特性而适用于大型项目。

TypeScript 是 JavaScript 的超集，为 JavaScript 添加了静态类型。TypeScript 编写的代码可以编译为纯粹的 JavaScript，在浏览器、服务器等所有支持 JavaScript 的执行环境中运行。此外，它是一个开源项目，使用 Apache License 2.0 提供。

## JavaScript 的超集​

TypeScript 在添加类型的同时保留了与 JavaScript 的基本兼容性。因此，熟悉 JavaScript 的人可以很快学会它。

## 编译​

TypeScript 代码可以转译为各种 JavaScript 版本（例如：ES5、ES6）。这样一来，就可以避免浏览器和执行环境的兼容性问题。

## 静态类型检查​

TypeScript 是一种具有静态类型检查的语言，通过为变量和函数参数指定类型，可以提高代码的安全性并更容易地发现错误。

```
typescript`function  sum(a:  number, b:  number):  number {  return a + b;}`
```

```
typescript`function sum(a:  number, b:  number):  number {  return a + b;}`
```

## 类型推断​

TypeScript 会根据上下文自动推断未带类型注解的变量的类型。这样一来，即使开发者没有显式指定类型，代码的安全性也会得到提升。

## 结构化部分类型系统​

TypeScript 采用结构化部分类型系统，根据对象的形状（即对象具有哪些属性和方法）来推断类型。因此，它基于结构部分类型而不是名义类型。

## 泛型​

TypeScript 支持泛型，可以编写通用且可重用的代码。

```
typescript`function  <data-lsp lsp="function identity<T>(arg: T): T">identity</data-lsp><<data-lsp lsp="(type parameter) T in identity<T>(arg: T): T">T</data-lsp>>(<data-lsp lsp="(parameter) arg: T">arg</data-lsp>:  <data-lsp lsp="(type parameter) T in identity<T>(arg: T): T">T</data-lsp>):  <data-lsp lsp="(type parameter) T in identity<T>(arg: T): T">T</data-lsp> {  return <data-lsp lsp="(parameter) arg: T">arg</data-lsp>;}`
```

```
typescript`function <data-lsp lsp="function identity<T>(arg: T): T">identity</data-lsp><<data-lsp lsp="(type parameter) T in identity<T>(arg: T): T">T</data-lsp>>(<data-lsp lsp="(parameter) arg: T">arg</data-lsp>: <data-lsp lsp="(type parameter) T in identity<T>(arg: T): T">T</data-lsp>): <data-lsp lsp="(type parameter) T in identity<T>(arg: T): T">T</data-lsp> {  return <data-lsp lsp="(parameter) arg: T">arg</data-lsp>;}`
```

## 高级类型表示​

TypeScript 使用高级类型系统来表示复杂的类型。这使得可以以更强大和丰富的方式开发应用程序逻辑。以下是 TypeScript 中可用的一些高级类型表示的示例。

1.  **联合类型**：可以表示多种类型中的任何一种。例如，处理初始值为`null`的变量时，可以使用联合类型。

    ```
    typescript`type  NullableString  =  string  |  null;`
    ```

    ```
    typescript`type NullableString =  string  |  null;`
    ```

1.  **元组类型**：可以指定数组的每个元素的不同类型。这样一来，可以简洁地表示不同类型的组合。

    ```
    typescript`type  Point2D  = [number,  number];`
    ```

    ```
    typescript`type Point2D = [number,  number];`
    ```

## 支持多种语言范式​

TypeScript 支持面向对象编程（OOP）和函数式编程（FP）的两种范式。这使得开发者可以构建灵活且强大的程序。

## 类与接口​

TypeScript 支持基于类的面向对象编程和接口。这使得代码重用和继承变得更加容易，有助于管理大型项目。

```
typescript`interface  <data-lsp lsp="interface Person">Person</data-lsp> { <data-lsp lsp="(property) Person.firstName: string">firstName</data-lsp>:  string; <data-lsp lsp="(property) Person.lastName: string">lastName</data-lsp>:  string;}class  <data-lsp lsp="class Employee">Employee</data-lsp>  implements  <data-lsp lsp="interface Person">Person</data-lsp> { <data-lsp lsp="(property) Employee.firstName: string">firstName</data-lsp>:  string; <data-lsp lsp="(property) Employee.lastName: string">lastName</data-lsp>:  string;  constructor(<data-lsp lsp="(parameter) firstName: string">firstName</data-lsp>:  string, <data-lsp lsp="(parameter) lastName: string">lastName</data-lsp>:  string) {  this.<data-lsp lsp="(property) Employee.firstName: string">firstName</data-lsp> = <data-lsp lsp="(parameter) firstName: string">firstName</data-lsp>;  this.<data-lsp lsp="(property) Employee.lastName: string">lastName</data-lsp> = <data-lsp lsp="(parameter) lastName: string">lastName</data-lsp>; }}`
```

```
typescript`interface <data-lsp lsp="interface Person">Person</data-lsp> { <data-lsp lsp="(property) Person.firstName: string">firstName</data-lsp>:  string; <data-lsp lsp="(property) Person.lastName: string">lastName</data-lsp>:  string;}class <data-lsp lsp="class Employee">Employee</data-lsp> implements <data-lsp lsp="interface Person">Person</data-lsp> { <data-lsp lsp="(property) Employee.firstName: string">firstName</data-lsp>:  string; <data-lsp lsp="(property) Employee.lastName: string">lastName</data-lsp>:  string;  constructor(<data-lsp lsp="(parameter) firstName: string">firstName</data-lsp>:  string, <data-lsp lsp="(parameter) lastName: string">lastName</data-lsp>:  string) {  this.<data-lsp lsp="(property) Employee.firstName: string">firstName</data-lsp> = <data-lsp lsp="(parameter) firstName: string">firstName</data-lsp>;  this.<data-lsp lsp="(property) Employee.lastName: string">lastName</data-lsp> = <data-lsp lsp="(parameter) lastName: string">lastName</data-lsp>; }}`
```

## 内存管理​

TypeScript 基本上执行与 JavaScript 相同的内存管理。JavaScript 引擎使用垃圾收集来自动释放内存。

## 异步处理​

TypeScript 与 JavaScript 一样支持基于事件的异步编程模型。通过 Promise 和 async/await，可以简洁高效地实现异步处理。

```
typescript`async  function  <data-lsp lsp="function fetchData(): Promise<void>">fetchData</data-lsp>():  <data-lsp lsp="interface Promise<T>">Promise</data-lsp><void> {  try {  const  <data-lsp lsp="const response: Response">response</data-lsp>  =  await  <data-lsp lsp="function fetch(input: RequestInfo | URL, init?: RequestInit | undefined): Promise<Response>">fetch</data-lsp>("https://api.example.com/data");  const  <data-lsp lsp="const data: any">data</data-lsp>  =  await  <data-lsp lsp="const response: Response">response</data-lsp>.<data-lsp lsp="(method) Body.json(): Promise<any>">json</data-lsp>();  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const data: any">data</data-lsp>); } catch (<data-lsp lsp="(local var) error: unknown">error</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.error(message?: any, ...optionalParams: any[]): void (+1 overload)">error</data-lsp>("Error fetching data:", <data-lsp lsp="(local var) error: unknown">error</data-lsp>); }}`
```

```
typescript`async  function <data-lsp lsp="function fetchData(): Promise<void>">fetchData</data-lsp>(): <data-lsp lsp="interface Promise<T>">Promise</data-lsp><void> {  try {  const  <data-lsp lsp="const response: Response">response</data-lsp>  =  await <data-lsp lsp="function fetch(input: RequestInfo | URL, init?: RequestInit | undefined): Promise<Response>">fetch</data-lsp>("https://api.example.com/data");  const  <data-lsp lsp="const data: any">data</data-lsp>  =  await  <data-lsp lsp="const response: Response">response</data-lsp>.<data-lsp lsp="(method) Body.json(): Promise<any>">json</data-lsp>();  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>(<data-lsp lsp="const data: any">data</data-lsp>); } catch (<data-lsp lsp="(local var) error: unknown">error</data-lsp>) {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.error(message?: any, ...optionalParams: any[]): void (+1 overload)">error</data-lsp>("Error fetching data:", <data-lsp lsp="(local var) error: unknown">error</data-lsp>); }}`
```

## 单线程模型​

TypeScript（以及 JavaScript）采用单线程模型。单线程模型实现了简单易懂的代码，并通过事件循环和异步处理支持高效的任务处理。另一方面，还可以利用 Web Workers 创建在后台运行的线程，实现多任务处理。

## 强大的开发环境​

TypeScript 提供了强大的开发环境。开发者可以在编辑器中获得智能感知和实时错误显示功能，以享受优质的开发体验。这使得开发过程更加顺畅，可以在早期发现类型错误和不一致，编写出更可靠的代码。

## 开源​

TypeScript 是一个开源项目，可以在[TypeScript GitHub 存储库](https://github.com/microsoft/TypeScript)上找到其源代码和文档。开发者可以通过 GitHub 存储库为 TypeScript 项目做出贡献。

## 总结​

由于这些特点，TypeScript 在现代 Web 开发中成为了非常有吸引力的选择。通过引入静态类型和高级类型系统，它可以适用于大型项目，面向对象编程和函数式编程等多种开发风格，实现了健壮且灵活的代码。此外，作为开源项目，又得到了微软强大的支持，这也是其魅力之一。
