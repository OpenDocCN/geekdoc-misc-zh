# [使用 Prettier 自动格式化代码](https://prettier.io/docs/en/options.html) 

> 原文：[`typescriptbook.jp/tutorials/prettier`](https://typescriptbook.jp/tutorials/prettier)

本教程将使用代码格式化工具“Prettier”自动格式化 TypeScript 代码。

## 可以在本章学到以下内容：

本章目标是引入 Prettier 并自动格式化代码。

+   安装 Prettier 的方法

+   Prettier 的执行方法

+   设置格式规则的方法

## 了解 Prettier​

Prettier 是一款自动格式化代码的工具。Prettier 支持的格式广泛，包括但不限于以下格式。

此外，您也可以使用插件来格式化其他语言，如 PHP 等。

+   JavaScript

+   TypeScript

+   JSX

+   Flow

+   JSON

+   HTML

+   Vue

+   Angular

+   Ember

+   Css

+   Less

+   SCSS

+   styled-components

+   styled-jsx

+   GraphQL

+   Markdown

+   MDX

+   YAML

+   Svelte

## 为什么要引入 Prettier​

在团队开发中，不同的开发者会产生缩进不一致、对象末尾是否加逗号等代码风格的差异。

```
ts`// オブジェクトの最後にカンマが付いている// 文字列はダブルクォート// 行末にセミコロンが付いているconst  user1  = { name:  "太郎", age:  20,};``// オブジェクトの最後にカンマが付かない// 文字列はシングルクォート// 行末にセミコロンが付かないconst  user2  = { name:  'まさる', age:  30}`

```

ts`// 末尾带逗号的对象// 字符串使用双引号// 行尾没有分号 const  user1  = { name:  "太郎", age:  20,};``// 末尾不带逗号的对象// 字符串使用单引号// 行尾没有分号 const  user2  = { name:  'まさる', age:  30}`

要手动统一这些代码风格，您需要创建指导方针，并在团队内共享，并在代码审查中仔细检查。另外，当新成员加入团队时，还需要共享规则。

引入 Prettier 并自动格式化代码后，您可以轻松统一代码风格。开发人员无需关注细节的代码样式，可以更专注于开发，从而提高开发效率。

## 本教程所需内容​

本教程所需内容如下：

+   需要 Node.js v16 或更高版本

+   使用 Yarn v1.x（本教程在 v1.22.19 上测试通过）

有关如何安装 Node.js，请参阅准备开发环境。

使用 Yarn 作为包管理工具。首先进行安装。如果您已经安装过，请跳过此步骤。

```
shell`npm install -g yarn`
```

```
shell`npm install -g yarn`
```

## 创建项目​

创建用于本教程的项目。

```
shell`mkdir prettier-tutorialcd prettier-tutorial`
```

```
shell`mkdir prettier-tutorialcd prettier-tutorial`
```

在项目根目录下创建`package.json`文件，内容如下：

```
package.jsonjson`{  "name":  "prettier-tutorial",  "license":  "UNLICENSED"}`
```

```
package.jsonjson`{  "name":  "prettier-tutorial",  "license":  "UNLICENSED"}`
```

## 安装 Prettier​

Prettier 仅在开发时使用，因此请使用`-D`选项进行安装。

```
shell`yarn add -D 'prettier@²'`
```

```
shell`yarn add -D 'prettier@²'`
```

检查版本并确认安装。

```
shell`yarn prettier -v2.8.1`
```

```
shell`yarn prettier -v2.8.1`
```

## 自动格式化 TypeScript​

使用`prettier`命令，自动格式化 TypeScript 文件。

首先创建`src`目录，并创建`src/helloWorld.ts`。

```
shell`mkdir srctouch src/helloWorld.ts`
```

```
shell`mkdir srctouch src/helloWorld.ts`
```

将`helloWorld.ts`的内容更改为以下内容。

此代码被故意编写得难以阅读，以便进行自动格式化的确认。

```
src/helloWorld.tsts`const  <data-lsp lsp="const hello: (name: string) => void">hello</data-lsp>  = ( <data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) => {<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Hello,World "+ <data-lsp lsp="(parameter) name: string">name</data-lsp>)}`
```

```
src/helloWorld.tsts`const <data-lsp lsp="const hello: (name: string) => void">hello</data-lsp> = ( <data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) => {<data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Hello,World "+ <data-lsp lsp="(parameter) name: string">name</data-lsp>)}`
```

尝试运行`prettier`命令。

命令格式为`prettier [options] [file/directory]`。

以下示例将自动格式化`src`目录下的所有文件。

```
shell`yarn prettier src`
```

```
shell`yarn prettier src`
```

虽然显示了格式化结果，但是您会注意到`helloWorld.ts`未更改。如果在不带选项的情况下运行`prettier`命令，则仅会显示格式化结果，不会进行文件重写。

如果要同时执行文件重写，请使用`--write`选项。

```
shell`yarn prettier --write src`
```

```
shell`yarn prettier --write src`
```

执行后，您可以检查`helloWorld.ts`，您会发现代码已经被格式化了。

```
src/helloWorld.tsts`const  <data-lsp lsp="const hello: (name: string) => void">hello</data-lsp>  = (<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Hello,World "  + <data-lsp lsp="(parameter) name: string">name</data-lsp>);};`
```

```
src/helloWorld.tsts`const <data-lsp lsp="const hello: (name: string) => void">hello</data-lsp> = (<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Hello,World "  + <data-lsp lsp="(parameter) name: string">name</data-lsp>);};`
```

## Prettier 的默认格式规则​

Prettier 有默认的格式规则。从上述执行结果中可以看出，缩进是两个空格。

一些典型项目的默认值如下：

若要查看所有项目的默认值，请参阅[Prettier 官方文档](https://prettier.io/docs/en/options.html)。

| 项目 | 默认值 |
| --- | --- |
| 单行最大字符数 | 80 |
| 缩进宽度 | 2 |
| 缩进 | 空格 |
| 分号 | 添加 |
| 引号 | 双引号 |

## 设置 Prettier 的格式规则​

### 使用 CLI 选项进行设置​

格式规则可以在执行`prettier`命令时作为选项指定。

使用另一组格式规则对之前格式化的`helloWorld.ts`进行格式化。

```
shell`yarn prettier --no-semi --tab-width 4 --write src`
```

```
shell`yarn prettier --no-semi --tab-width 4 --write src`
```

检查格式化后的代码，您会发现分号消失了，缩进从 2 改为 4。

```
src/helloWorld.tsts`const  <data-lsp lsp="const hello: (name: string) => void">hello</data-lsp>  = (<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Hello,World "  + <data-lsp lsp="(parameter) name: string">name</data-lsp>)}`
```

```
src/helloWorld.tsts`const <data-lsp lsp="const hello: (name: string) => void">hello</data-lsp> = (<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>("Hello,World "  + <data-lsp lsp="(parameter) name: string">name</data-lsp>)}`
```

### 创建配置文件​

Prettier 也可以将格式化规则写入配置文件中。

在项目根目录下创建`.prettierrc`。

```
shell`touch .prettierrc`
```

```
shell`touch .prettierrc`
```

接下来，将`.prettierrc`修改如下。

```
.prettierrcjson`{  "tabWidth":  2,  "semi":  true,  "singleQuote":  true}`
```

```
.prettierrcjson`{  "tabWidth":  2,  "semi":  true,  "singleQuote":  true}`
```

创建配置文件后，尝试运行`prettier`命令。

如果项目根目录中存在`.prettierrc`，Prettier 会自动加载配置文件并设置格式化规则。

```
shell`yarn prettier --write src`
```

```
shell`yarn prettier --write src`
```

您可以通过配置文件中描述的格式化规则，查看`helloWorld.ts`的变化。

```
src/helloWorld.tsts`const  <data-lsp lsp="const hello: (name: string) => void">hello</data-lsp>  = (<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>('Hello,World '  + <data-lsp lsp="(parameter) name: string">name</data-lsp>);};`
```

```
src/helloWorld.tsts`const <data-lsp lsp="const hello: (name: string) => void">hello</data-lsp> = (<data-lsp lsp="(parameter) name: string">name</data-lsp>:  string) => {  <data-lsp lsp="namespace console
var console: Console">console</data-lsp>.<data-lsp lsp="(method) Console.log(message?: any, ...optionalParams: any[]): void (+1 overload)">log</data-lsp>('Hello,World '  + <data-lsp lsp="(parameter) name: string">name</data-lsp>);};`
```

在上述示例中，我们使用 JSON 格式创建了配置文件，但是 Prettier 还支持 JS、YAML、TOML 等格式。

```
prettier.config.jsjs`<data-lsp lsp="module export=
(property) export=: {
    tabWidth: number;
    semi: boolean;
    singleQuote: boolean;
}">module</data-lsp>.<data-lsp lsp="module export=
(property) export=: {
    tabWidth: number;
    semi: boolean;
    singleQuote: boolean;
}">exports</data-lsp>  = { <data-lsp lsp="(property) tabWidth: number">tabWidth</data-lsp>:  2, <data-lsp lsp="(property) semi: boolean">semi</data-lsp>:  true, <data-lsp lsp="(property) singleQuote: boolean">singleQuote</data-lsp>:  true,};`
```

```
prettier.config.jsjs`<data-lsp lsp="module export=
(property) export=: {
    tabWidth: number;
    semi: boolean;
    singleQuote: boolean;
}">module</data-lsp>.<data-lsp lsp="module export=
(property) export=: {
    tabWidth: number;
    semi: boolean;
    singleQuote: boolean;
}">exports</data-lsp>  = { <data-lsp lsp="(property) tabWidth: number">tabWidth</data-lsp>:  2, <data-lsp lsp="(property) semi: boolean">semi</data-lsp>:  true, <data-lsp lsp="(property) singleQuote: boolean">singleQuote</data-lsp>:  true,};`
```

```
.prettierrc.ymlyaml`tabWidth:  2semi:  truesingleQuote:  true`
```

```
.prettierrc.ymlyaml`tabWidth:  2semi:  truesingleQuote:  true`
```

```
.prettierrc.tomltoml`tabWidth =  2semi =  truesingleQuote =  true`
```

```
.prettierrc.tomltoml`tabWidth =  2semi =  truesingleQuote =  true`
```

除了`.prettierrc`，还有一些其他文件名也可以被自动识别为配置文件。

格式和文件名的组合如下：

| 格式 | 文件名 |
| :-- | :-- |
| json | `.prettierrc`, `.prettierrc.json`, `.prettierrc.json5` |
| js | `.prettierrc.js`, `.prettierrc.cjs`, `prettier.config.js`,   `prettier.config.cjs` |
| yaml | `.prettierrc`, `.prettierrc.yml`, `.prettierrc.yaml` |
| toml | `.prettierrc.toml` |

### 查看其他格式化规则​

除了这里介绍的，还有一些其他的格式化规则。

如果您想要查看其他格式化规则、CLI 命令选项名称、配置文件键名等，请参考[Prettier 的官方文档](https://prettier.io/docs/en/options.html)。

### 什么样的格式化规则是最好的？​

当您将 Prettier 引入项目时，可能会对格式化规则感到困惑。

由于格式化规则很大程度上取决于个人喜好，建议项目开发者们进行讨论并做出决定。如果想要更改格式化规则，只需运行`prettier`命令即可，因此事后更改也很容易。

如果没有特别偏好，建议直接使用 Prettier 的默认格式化规则。

## 禁用 Prettier 的自动格式化​

通过在代码中添加`prettier-ignore`注释，可以排除部分代码不受 Prettier 的自动格式化影响。

```
src/helloWorld.tsts`const  <data-lsp lsp="const board1: number[]">board1</data-lsp>  = [1,  0,  0,  1];//  prettier-ignoreconst  <data-lsp lsp="const board2: number[]">board2</data-lsp>  = [  1,  0,  0,  1];`
```

```
src/helloWorld.tsts`const  <data-lsp lsp="const board1: number[]">board1</data-lsp>  = [1,  0,  0,  1];//  prettier-ignoreconst  <data-lsp lsp="const board2: number[]">board2</data-lsp>  = [  1,  0,  0,  1];`
```

```

```
