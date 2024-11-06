# 生成对象属性的类型

> 原文：[`typescriptbook.jp/tips/generates-type-from-object-property`](https://typescriptbook.jp/tips/generates-type-from-object-property)

## 从对象中只想要属性](/tips/generates-type-from-object-property)

## 📄️ 生成对象键的类型

从对象中只想要键

与前一页相反，这次的目标是从对象中获取属性而不是键的联合类型。假设这次也定义了以下消息。

```
ts`const  <data-lsp lsp="const conf: {
    en: string;
    fr: string;
    es: string;
    ja: string;
    zh: string;
}">conf</data-lsp>  = { <data-lsp lsp="(property) en: string">en</data-lsp>:  "Are you sure?", <data-lsp lsp="(property) fr: string">fr</data-lsp>:  "Êtes-vous sûr?", <data-lsp lsp="(property) es: string">es</data-lsp>:  "Está seguro?", <data-lsp lsp="(property) ja: string">ja</data-lsp>:  "よろしいですか？", <data-lsp lsp="(property) zh: string">zh</data-lsp>:  "您确定吗？",};`
```

```
ts`const  <data-lsp lsp="const conf: {
    en: string;
    fr: string;
    es: string;
    ja: string;
    zh: string;
}">conf</data-lsp>  = { <data-lsp lsp="(property) en: string">en</data-lsp>:  "Are you sure?", <data-lsp lsp="(property) fr: string">fr</data-lsp>:  "Êtes-vous sûr?", <data-lsp lsp="(property) es: string">es</data-lsp>:  "Está seguro?", <data-lsp lsp="(property) ja: string">ja</data-lsp>:  "よろしいですか？", <data-lsp lsp="(property) zh: string">zh</data-lsp>:  "您确定吗？",};`
```

最终目标是获得以下联合类型。

```
ts`type  <data-lsp lsp="type ConfirmationMessage = &quot;Are you sure?&quot; | &quot;Êtes-vous sûr?&quot; | &quot;Está seguro?&quot; | &quot;よろしいですか？&quot; | &quot;您确定吗？&quot;">ConfirmationMessage</data-lsp>  =  |  "Are you sure?"  |  "Êtes-vous sûr?"  |  "Está seguro?"  |  "よろしいですか？"  |  "您确定吗？";`
```

```
ts`type <data-lsp lsp="type ConfirmationMessage = &quot;Are you sure?&quot; | &quot;Êtes-vous sûr?&quot; | &quot;Está seguro?&quot; | &quot;よろしいですか？&quot; | &quot;您确定吗？&quot;">ConfirmationMessage</data-lsp> =  |  "Are you sure?"  |  "Êtes-vous sûr?"  |  "Está seguro?"  |  "よろしいですか？"  |  "您确定吗？";`
```

## 解决这个问题​

这次我们将结合前面介绍的从对象中生成类型的方法和映射类型，来实现这个目标。

## 📄️ 生成对象的类型

在许多语言中，定义结构体和对象后才开始编码，但在 JavaScript 的基础上构建的 TypeScript 中，往往没有这样的规定。  ## 📄️ 生成对象键的类型

从对象中只想要键

作为方法的方法，首先生成对象的键类型，然后使用映射类型引用对象的属性类型，并以文字类型获取它们。

### 生成键的类型​

生成键的类型与前一页相同。通过以下方式，您可以获得语言键的联合类型。有关详细信息，请参阅生成对象键值的页面。

## 📄️ 生成对象键的类型

从对象中只想要键

```
ts`type  <data-lsp lsp="type Language = &quot;en&quot; | &quot;fr&quot; | &quot;es&quot; | &quot;ja&quot; | &quot;zh&quot;" style="border-bottom:solid 2px lightgrey">Language</data-lsp>  =  keyof  typeof <data-lsp lsp="const conf: {
    en: string;
    fr: string;
    es: string;
    ja: string;
    zh: string;
}">conf</data-lsp>;` `type Language = "en" | "fr" | "es" | "ja" | "zh"`

```

ts`type <data-lsp lsp="type Language = &quot;en&quot; | &quot;fr&quot; | &quot;es&quot; | &quot;ja&quot; | &quot;zh&quot;" style="border-bottom:solid 2px lightgrey">Language</data-lsp> =  keyof  typeof <data-lsp lsp="const conf: {

    en: string;

    fr: string;

    es: string;

    ja: string;

    zh: string;

}">conf</data-lsp>;` `type Language = "en" | "fr" | "es" | "ja" | "zh"`

### 映射类型​

使用映射类型来引用对象的属性类型。为了从原始对象生成类型，我们使用`typeof`。

```
ts`type  <data-lsp lsp="type ConfirmationMessage = string" style="border-bottom:solid 2px lightgrey">ConfirmationMessage</data-lsp>  = (typeof <data-lsp lsp="const conf: {
    en: string;
    fr: string;
    es: string;
    ja: string;
    zh: string;
}">conf</data-lsp>)[<data-lsp lsp="type Language = &quot;en&quot; | &quot;fr&quot; | &quot;es&quot; | &quot;ja&quot; | &quot;zh&quot;">Language</data-lsp>];` `type ConfirmationMessage = string`

```

ts`type <data-lsp lsp="type ConfirmationMessage = string" style="border-bottom:solid 2px lightgrey">ConfirmationMessage</data-lsp> = (typeof <data-lsp lsp="const conf: {

    en: string;

    fr: string;

    es: string;

    ja: string;

    zh: string;

}">conf</data-lsp>)[<data-lsp lsp="type Language = &quot;en&quot; | &quot;fr&quot; | &quot;es&quot; | &quot;ja&quot; | &quot;zh&quot;">Language</data-lsp>];` `type ConfirmationMessage = string`

### 允许获取文字类型​

如果保持原样生成对象的类型，那么类型不是文字类型。换句话说，它只是一个`string`类型的联合类型，即`string`类型。因此，我们在原始对象`conf`上添加`as const`。

```
ts`const  <data-lsp lsp="const conf: {
    readonly en: &quot;Are you sure?&quot;;
    readonly fr: &quot;Êtes-vous sûr?&quot;;
    readonly es: &quot;Está seguro?&quot;;
    readonly ja: &quot;よろしいですか？&quot;;
    readonly zh: &quot;您确定吗？&quot;;
}">conf</data-lsp>  = { <data-lsp lsp="(property) en: &quot;Are you sure?&quot;">en</data-lsp>:  "Are you sure?", <data-lsp lsp="(property) fr: &quot;Êtes-vous sûr?&quot;">fr</data-lsp>:  "Êtes-vous sûr?", <data-lsp lsp="(property) es: &quot;Está seguro?&quot;">es</data-lsp>:  "Está seguro?", <data-lsp lsp="(property) ja: &quot;よろしいですか？&quot;">ja</data-lsp>:  "よろしいですか？", <data-lsp lsp="(property) zh: &quot;您确定吗？&quot;">zh</data-lsp>:  "您确定吗？",} as  <data-lsp lsp="type const = {
    readonly en: &quot;Are you sure?&quot;;
    readonly fr: &quot;Êtes-vous sûr?&quot;;
    readonly es: &quot;Está seguro?&quot;;
    readonly ja: &quot;よろしいですか？&quot;;
    readonly zh: &quot;您确定吗？&quot;;
}">const</data-lsp>;`
```

```
ts`const  <data-lsp lsp="const conf: {
    readonly en: &quot;Are you sure?&quot;;
    readonly fr: &quot;Êtes-vous sûr?&quot;;
    readonly es: &quot;Está seguro?&quot;;
    readonly ja: &quot;よろしいですか？&quot;;
    readonly zh: &quot;您确定吗？&quot;;
}">conf</data-lsp>  = { <data-lsp lsp="(property) en: &quot;Are you sure?&quot;">en</data-lsp>:  "Are you sure?", <data-lsp lsp="(property) fr: &quot;Êtes-vous sûr?&quot;">fr</data-lsp>:  "Êtes-vous sûr?", <data-lsp lsp="(property) es: &quot;Está seguro?&quot;">es</data-lsp>:  "Está seguro?", <data-lsp lsp="(property) ja: &quot;よろしいですか？&quot;">ja</data-lsp>:  "よろしいですか？", <data-lsp lsp="(property) zh: &quot;您确定吗？&quot;">zh</data-lsp>:  "您确定吗？",} as  <data-lsp lsp="type const = {
    readonly en: &quot;Are you sure?&quot;;
    readonly fr: &quot;Êtes-vous sûr?&quot;;
    readonly es: &quot;Está seguro?&quot;;
    readonly ja: &quot;よろしいですか？&quot;;
    readonly zh: &quot;您确定吗？&quot;;
}">const</data-lsp>;`
```

## 总结​

将您自定义的键类型`Language`分配给映射类型的键部分。最终形式如下所示。

```
ts`const  <data-lsp lsp="const conf: {
    readonly en: &quot;Are you sure?&quot;;
    readonly fr: &quot;Êtes-vous sûr?&quot;;
    readonly es: &quot;está seguro?&quot;;
    readonly ja: &quot;よろしいですか？&quot;;
    readonly zh: &quot;您确定吗？&quot;;
}">conf</data-lsp>  = { <data-lsp lsp="(property) en: &quot;Are you sure?&quot;">en</data-lsp>:  "Are you sure?", <data-lsp lsp="(property) fr: &quot;Êtes-vous sûr?&quot;">fr</data-lsp>:  "Êtes-vous sûr?", <data-lsp lsp="(property) es: &quot;está seguro?&quot;">es</data-lsp>:  "está seguro?", <data-lsp lsp="(property) ja: &quot;よろしいですか？&quot;">ja</data-lsp>:  "よろしいですか？", <data-lsp lsp="(property) zh: &quot;您确定吗？&quot;">zh</data-lsp>:  "您确定吗？",} as  <data-lsp lsp="type const = {
    readonly en: &quot;Are you sure?&quot;;
    readonly fr: &quot;Êtes-vous sûr?&quot;;
    readonly es: &quot;está seguro?&quot;;
    readonly ja: &quot;よろしいですか？&quot;;
    readonly zh: &quot;您确定吗？&quot;;
}">const</data-lsp>;type  <data-lsp lsp="type ConfirmationMessage = &quot;Are you sure?&quot; | &quot;Êtes-vous sûr?&quot; | &quot;está seguro?&quot; | &quot;よろしいですか？&quot; | &quot;您确定吗？&quot;" style="border-bottom:solid 2px lightgrey">ConfirmationMessage</data-lsp>  = (typeof <data-lsp lsp="const conf: {
    readonly en: &quot;Are you sure?&quot;;
    readonly fr: &quot;Êtes-vous sûr?&quot;;
    readonly es: &quot;está seguro?&quot;;
    readonly ja: &quot;よろしいですか？&quot;;
    readonly zh: &quot;您确定吗？&quot;;
}">conf</data-lsp>)[keyof  typeof <data-lsp lsp="const conf: {
    readonly en: &quot;Are you sure?&quot;;
    readonly fr: &quot;Êtes-vous sûr?&quot;;
    readonly es: &quot;está seguro?&quot;;
    readonly ja: &quot;よろしいですか？&quot;;
    readonly zh: &quot;您确定吗？&quot;;
}">conf</data-lsp>];` `type ConfirmationMessage = "Are you sure?" | "Êtes-vous sûr?" | "está seguro?" | "よろしいですか？" | "您确定吗？"`

```

ts`const  <data-lsp lsp="const conf: {

    readonly en: &quot;Are you sure?&quot;;

    readonly fr: &quot;Êtes-vous sûr?&quot;;

    readonly es: &quot;está seguro?&quot;;

    readonly ja: &quot;よろしいですか？&quot;;

    readonly zh: &quot;您确定吗？&quot;;

}">conf</data-lsp>  = { <data-lsp lsp="(property) en: &quot;Are you sure?&quot;">en</data-lsp>:  "Are you sure?", <data-lsp lsp="(property) fr: &quot;Êtes-vous sûr?&quot;">fr</data-lsp>:  "Êtes-vous sûr?", <data-lsp lsp="(property) es: &quot;está seguro?&quot;">es</data-lsp>:  "está seguro?", <data-lsp lsp="(property) ja: &quot;よろしいですか？&quot;">ja</data-lsp>:  "よろしいですか？", <data-lsp lsp="(property) zh: &quot;您确定吗？&quot;">zh</data-lsp>:  "您确定吗？",} as  <data-lsp lsp="type const = {

    readonly en: &quot;Are you sure?&quot;;

    readonly fr: &quot;Êtes-vous sûr?&quot;;

    readonly es: &quot;está seguro?&quot;;

    readonly ja: &quot;よろしいですか？&quot;;

    readonly zh: &quot;您确定吗？&quot;;

}">const</data-lsp>;type <data-lsp lsp="type ConfirmationMessage = &quot;Are you sure?&quot; | &quot;Êtes-vous sûr?&quot; | &quot;está seguro?&quot; | &quot;よろしいですか？&quot; | &quot;您确定吗？&quot;" style="border-bottom:solid 2px lightgrey">ConfirmationMessage</data-lsp> = (typeof <data-lsp lsp="const conf: {

    readonly en: &quot;Are you sure?&quot;;

    readonly fr: &quot;Êtes-vous sûr?&quot;;

    readonly es: &quot;está seguro?&quot;;

    readonly ja: &quot;よろしいですか？&quot;;

    readonly zh: &quot;您确定吗？&quot;;

}">conf</data-lsp>)[keyof  typeof <data-lsp lsp="const conf: {

    readonly en: &quot;Are you sure?&quot;;

    readonly fr: &quot;Êtes-vous sûr?&quot;;

    readonly es: &quot;está seguro?&quot;;

    readonly ja: &quot;よろしいですか？&quot;;

    readonly zh: &quot;您确定吗？&quot;;

}">conf</data-lsp>];` `type ConfirmationMessage = "Are you sure?" | "Êtes-vous sûr?" | "está seguro?" | "よろしいですか？" | "您确定吗？"`

`as const`を忘れないようにしてください。

```

```

```

```

```

```
