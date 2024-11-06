# 接收对象并返回对象（RORO）

> 原文：[`typescriptbook.jp/tips/receive-an-object-return-an-object`](https://typescriptbook.jp/tips/receive-an-object-return-an-object)

有一种思想叫做 RORO，即在函数或方法中接收一个对象作为参数，并返回一个对象。RORO 是 **Receive an Object, Return an Object** 的缩写。这种思想在 JavaScript 和 TypeScript 中都有很大的好处。

## 以前的函数​

不仅仅是 JavaScript，初学者时期的函数通常具有这种形式。

```
ts`function  <data-lsp lsp="function findUser(name?: string, age?: number, country?: string, isVip?: boolean): User">findUser</data-lsp>( <data-lsp lsp="(parameter) name: string | undefined">name</data-lsp>?:  string, <data-lsp lsp="(parameter) age: number | undefined">age</data-lsp>?:  number, <data-lsp lsp="(parameter) country: string | undefined">country</data-lsp>?:  string, <data-lsp lsp="(parameter) isVip: boolean | undefined">isVip</data-lsp>?:  boolean):  <data-lsp lsp="type User = {
    id: string;
    name: string;
    age: number;
    country: string;
    password: string;
    vip: boolean;
}">User</data-lsp> {  // ...}`
```

```
ts`function <data-lsp lsp="function findUser(name?: string, age?: number, country?: string, isVip?: boolean): User">findUser</data-lsp>( <data-lsp lsp="(parameter) name: string | undefined">name</data-lsp>?:  string, <data-lsp lsp="(parameter) age: number | undefined">age</data-lsp>?:  number, <data-lsp lsp="(parameter) country: string | undefined">country</data-lsp>?:  string, <data-lsp lsp="(parameter) isVip: boolean | undefined">isVip</data-lsp>?:  boolean): <data-lsp lsp="type User = {
    id: string;
    name: string;
    age: number;
    country: string;
    password: string;
    vip: boolean;
}">User</data-lsp> {  // ...}`
```

为了能���搜索喜欢的参数��我们使参数本身也是可选的。然而，接下来会遇到一个问题。

### 当参数被添加时​

假设居住地和国籍不同！并且作为参数添加了国籍(`nationality`)。在这种情况下，国籍应该添加在哪里？在`isVip`之后是安全的，但有些人可能不喜欢这个位置。

此外，虽然我们只讨论了`findUser()`函数，但如果存在类似参数的`~~~User()`方法，那么可能需要同时修改多个地方。这很麻烦。

### 对于其他函数存在不可省略参数的情况​

可选参数必须放在右侧（后面）。在这种情况下，我们使所有参数都是可选的，但有些情况下，如果要创建一个只有国家 (`country`) 是必填的函数，那么它必须成为函数的第一个参数。这种情况会导致与添加参数时相同的混乱。

作为解决这个问题的方法，有一个叫做 RORO 的概念，它将对象中必要的信息打包到一个参数中传递。

## RORO (Receive an Object, Return an Object)​ への直接リンク")

对于上述用户，如果创建一个类似数据类（只包含公共数据的类）就可以避免这个问题。在 TypeScript 中将其类型命名为`UserInfo`，`UserInfo`将如下所示。

```
ts`type  <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    isVip?: boolean | undefined;
}">UserInfo</data-lsp>  = { <data-lsp lsp="(property) name?: string | undefined">name</data-lsp>?:  string; <data-lsp lsp="(property) age?: number | undefined">age</data-lsp>?:  number; <data-lsp lsp="(property) country?: string | undefined">country</data-lsp>?:  string; <data-lsp lsp="(property) isVip?: boolean | undefined">isVip</data-lsp>?:  boolean;};`
```

```
ts`type <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    isVip?: boolean | undefined;
}">UserInfo</data-lsp> = { <data-lsp lsp="(property) name?: string | undefined">name</data-lsp>?:  string; <data-lsp lsp="(property) age?: number | undefined">age</data-lsp>?:  number; <data-lsp lsp="(property) country?: string | undefined">country</data-lsp>?:  string; <data-lsp lsp="(property) isVip?: boolean | undefined">isVip</data-lsp>?:  boolean;};`
```

在这种情况下，`Optional`的`?`是很正式的，但也可以使用`Partial<T>`来代替。

这样，您可以将此类型的对象作为参数类型接收一个。

```
ts`function  <data-lsp lsp="function findUser(info: UserInfo): User">findUser</data-lsp>(<data-lsp lsp="(parameter) info: UserInfo">info</data-lsp>:  <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    isVip?: boolean | undefined;
}">UserInfo</data-lsp>):  <data-lsp lsp="type User = {
    id: string;
    name: string;
    age: number;
    country: string;
    password: string;
    vip: boolean;
}">User</data-lsp> {  if (<data-lsp lsp="(parameter) info: UserInfo">info</data-lsp>.<data-lsp lsp="(property) age?: number | undefined">age</data-lsp> >=  20) {  // ... }  // ...}`
```

```
ts`function <data-lsp lsp="function findUser(info: UserInfo): User">findUser</data-lsp>(<data-lsp lsp="(parameter) info: UserInfo">info</data-lsp>: <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    isVip?: boolean | undefined;
}">UserInfo</data-lsp>): <data-lsp lsp="type User = {
    id: string;
    name: string;
    age: number;
    country: string;
    password: string;
    vip: boolean;
}">User</data-lsp> {  if (<data-lsp lsp="(parameter) info: UserInfo">info</data-lsp>.<data-lsp lsp="(property) age?: number | undefined">age</data-lsp> >=  20) {  // ... }  // ...}`
```

这不仅仅是 JavaScript 和 TypeScript 中有用的技巧，而是一个简单的技巧。为什么这在 JavaScript 和 TypeScript 中如此重要呢？这与解构赋值有关。

使用解构赋值，函数只需指定对象的键作为参数即可访问其值。例如，在只需要名称 (`name`) 的函数`findUserByName()`中，而不是接收整个`UserInfo`，使用解构赋值如下所示。

```
ts`function  <data-lsp lsp="function findUserByName({ name }: UserInfo): User">findUserByName</data-lsp>({ <data-lsp lsp="(parameter) name: string | undefined">name</data-lsp> }:  <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    isVip?: boolean | undefined;
}">UserInfo</data-lsp>):  <data-lsp lsp="type User = {
    id: string;
    name: string;
    age: number;
    country: string;
    password: string;
    vip: boolean;
}">User</data-lsp> {  // ...}`
```

```
ts`function <data-lsp lsp="function findUserByName({ name }: UserInfo): User">findUserByName</data-lsp>({ <data-lsp lsp="(parameter) name: string | undefined">name</data-lsp> }: <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    isVip?: boolean | undefined;
}">UserInfo</data-lsp>): <data-lsp lsp="type User = {
    id: string;
    name: string;
    age: number;
    country: string;
    password: string;
    vip: boolean;
}">User</data-lsp> {  // ...}`
```

如果您需要再次了解有关解构赋值的知识，请参考下一页。

## 📄️ 对象的解构赋值

JavaScript 中有一种方便的语法叫做对象解构赋值。解构赋值是从对象中提取属性的功能。  ## 📄️ 解构赋值参数

在 JavaScript 中，解构赋值语法也可以用于函数参数。当参数是对象或数组时，如果只想在函数中使用部分对象或数组，解构赋值参数就很方便。

解构赋值不仅使得调用函数的一方不必担心参数的顺序，而且如果`UserInfo`在未来发生变化，也不需要每次都添加参数，只需在希望使用的函数中访问该键即可。如果像上面的例子中增加了国籍 (`nationality`)，只需将其添加到任意位置即可。顺序不会影响调用。

```
ts`type  <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    nationality?: string | undefined;
    isVip?: boolean | undefined;
}">UserInfo</data-lsp>  = { <data-lsp lsp="(property) name?: string | undefined">name</data-lsp>?:  string; <data-lsp lsp="(property) age?: number | undefined">age</data-lsp>?:  number; <data-lsp lsp="(property) country?: string | undefined">country</data-lsp>?:  string; <data-lsp lsp="(property) nationality?: string | undefined">nationality</data-lsp>?:  string; <data-lsp lsp="(property) isVip?: boolean | undefined">isVip</data-lsp>?:  boolean;};`
```

```
ts`type <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    nationality?: string | undefined;
    isVip?: boolean | undefined;
}">UserInfo</data-lsp> = { <data-lsp lsp="(property) name?: string | undefined">name</data-lsp>?:  string; <data-lsp lsp="(property) age?: number | undefined">age</data-lsp>?:  number; <data-lsp lsp="(property) country?: string | undefined">country</data-lsp>?:  string; <data-lsp lsp="(property) nationality?: string | undefined">nationality</data-lsp>?:  string; <data-lsp lsp="(property) isVip?: boolean | undefined">isVip</data-lsp>?:  boolean;};`
```

これだけで`nationality`を (`byName`で国籍を使っている問題は置いておくとして) 簡単に呼び出せます。

```
ts`function  <data-lsp lsp="function findUserByName({ name, nationality }: UserInfo): User">findUserByName</data-lsp>({ <data-lsp lsp="(parameter) name: string | undefined">name</data-lsp>, <data-lsp lsp="(parameter) nationality: string | undefined">nationality</data-lsp> }:  <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    nationality?: string | undefined;
    isVip?: boolean | undefined;
}">UserInfo</data-lsp>):  <data-lsp lsp="type User = {
    id: string;
    name: string;
    age: number;
    country: string;
    password: string;
    vip: boolean;
}">User</data-lsp> {  // ...}`
```

```
ts`function <data-lsp lsp="function findUserByName({ name, nationality }: UserInfo): User">findUserByName</data-lsp>({ <data-lsp lsp="(parameter) name: string | undefined">name</data-lsp>, <data-lsp lsp="(parameter) nationality: string | undefined">nationality</data-lsp> }: <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    nationality?: string | undefined;
    isVip?: boolean | undefined;
}">UserInfo</data-lsp>): <data-lsp lsp="type User = {
    id: string;
    name: string;
    age: number;
    country: string;
    password: string;
    vip: boolean;
}">User</data-lsp> {  // ...}`
```

正如在函数说明中所述，您也可以在解构赋值中使用默认值。例如，如果在`findUser()`中不搜索已退休用户，则只需将`UserInfo`和函数更改为以下内容。

```
ts`type  <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    nationality?: string | undefined;
    isVip?: boolean | undefined;
    isRetired?: boolean | undefined;
}">UserInfo</data-lsp>  = { <data-lsp lsp="(property) name?: string | undefined">name</data-lsp>?:  string; <data-lsp lsp="(property) age?: number | undefined">age</data-lsp>?:  number; <data-lsp lsp="(property) country?: string | undefined">country</data-lsp>?:  string; <data-lsp lsp="(property) nationality?: string | undefined">nationality</data-lsp>?:  string; <data-lsp lsp="(property) isVip?: boolean | undefined">isVip</data-lsp>?:  boolean; <data-lsp lsp="(property) isRetired?: boolean | undefined">isRetired</data-lsp>?:  boolean;};`
```

```
ts`type <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    nationality?: string | undefined;
    isVip?: boolean | undefined;
    isRetired?: boolean | undefined;
}">UserInfo</data-lsp> = { <data-lsp lsp="(property) name?: string | undefined">name</data-lsp>?:  string; <data-lsp lsp="(property) age?: number | undefined">age</data-lsp>?:  number; <data-lsp lsp="(property) country?: string | undefined">country</data-lsp>?:  string; <data-lsp lsp="(property) nationality?: string | undefined">nationality</data-lsp>?:  string; <data-lsp lsp="(property) isVip?: boolean | undefined">isVip</data-lsp>?:  boolean; <data-lsp lsp="(property) isRetired?: boolean | undefined">isRetired</data-lsp>?:  boolean;};`
```

```
ts`function  <data-lsp lsp="function findUser({ name, age, country, isRetired }: UserInfo): User">findUser</data-lsp>({ <data-lsp lsp="(parameter) name: string | undefined">name</data-lsp>, <data-lsp lsp="(parameter) age: number | undefined">age</data-lsp>, <data-lsp lsp="(parameter) country: string | undefined">country</data-lsp>, <data-lsp lsp="(parameter) isRetired: boolean">isRetired</data-lsp> =  false }:  <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    nationality?: string | undefined;
    isVip?: boolean | undefined;
    isRetired?: boolean | undefined;
}">UserInfo</data-lsp>):  <data-lsp lsp="type User = {
    id: string;
    name: string;
    age: number;
    country: string;
    password: string;
    vip: boolean;
}">User</data-lsp> {  // ...}`
```

```
ts`function <data-lsp lsp="function findUser({ name, age, country, isRetired }: UserInfo): User">findUser</data-lsp>({ <data-lsp lsp="(parameter) name: string | undefined">name</data-lsp>, <data-lsp lsp="(parameter) age: number | undefined">age</data-lsp>, <data-lsp lsp="(parameter) country: string | undefined">country</data-lsp>, <data-lsp lsp="(parameter) isRetired: boolean">isRetired</data-lsp> =  false }: <data-lsp lsp="type UserInfo = {
    name?: string | undefined;
    age?: number | undefined;
    country?: string | undefined;
    nationality?: string | undefined;
    isVip?: boolean | undefined;
    isRetired?: boolean | undefined;
}">UserInfo</data-lsp>): <data-lsp lsp="type User = {
    id: string;
    name: string;
    age: number;
    country: string;
    password: string;
    vip: boolean;
}">User</data-lsp> {  // ...}`
```
