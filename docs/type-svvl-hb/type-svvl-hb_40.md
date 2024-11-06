# オブジェクトからキーの型を生成する

> 原文：[`typescriptbook.jp/tips/generates-type-from-object-key`](https://typescriptbook.jp/tips/generates-type-from-object-key)

## オブジェクトからキーだけ欲しい​

あるメッセージが言語ごとに定義されているとします。

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

内容は確認を促す変哲もないシステムのメッセージです。このオブジェクトを使ってシステムがサポートしている言語の一覧を作ります。次のようなユニオン型が今回の目的です。

```
ts`type  <data-lsp lsp="type Language = &quot;en&quot; | &quot;fr&quot; | &quot;es&quot; | &quot;ja&quot; | &quot;zh&quot;">Language</data-lsp>  =  "en"  |  "fr"  |  "es"  |  "ja"  |  "zh";`
```

```
ts`type <data-lsp lsp="type Language = &quot;en&quot; | &quot;fr&quot; | &quot;es&quot; | &quot;ja&quot; | &quot;zh&quot;">Language</data-lsp> =  "en"  |  "fr"  |  "es"  |  "ja"  |  "zh";`
```

### `typeof`​

頻出するこの`typeof`はJavaScriptのものではなく、TypeScriptの`typeof`です。これをオブジェクトに対して使用している例は前のページにあるとおりです。

## 📄️ オブジェクトから型を生成する

多くの言語では型による構造体、オブジェクトの定義をしてからコーディングが始まりますが、元がJavaScriptであるTypeScriptにはそのような決まりがないことも多々あります。

この例で実行すれば次のような型`TypeOfLanguage`が生成されるでしょう (型名は便宜的なものです) 。

```
ts`type  <data-lsp lsp="type TypeOfLanguage = {
    en: string;
    fr: string;
    es: string;
    ja: string;
    zh: string;
}" style="border-bottom:solid 2px lightgrey">TypeOfLanguage</data-lsp>  =  typeof <data-lsp lsp="const conf: {
    en: string;
    fr: string;
    es: string;
    ja: string;
    zh: string;
}">conf</data-lsp>;` `type TypeOfLanguage = {
    en: string;
    fr: string;
    es: string;
    ja: string;
    zh: string;
}`

```

ts`type <data-lsp lsp="type TypeOfLanguage = {

    en: string;

    fr: string;

    es: string;

    ja: string;

    zh: string;

}" style="border-bottom:solid 2px lightgrey">TypeOfLanguage</data-lsp> =  typeof <data-lsp lsp="const conf: {

    en: string;

    fr: string;

    es: string;

    ja: string;

    zh: string;

}">conf</data-lsp>;` `type TypeOfLanguage = {

    en: string;

    fr: string;

    es: string;

    ja: string;

    zh: string;

}`

ここまでくればあとは少しです。`TypeOfLanguage`型のキーだけを型にしてしまいます。

### `keyof`​

`keyof`はオブジェクトの型に使うとそのオブジェクトのキーをユニオン型にして返します。上記の`TypeOfLanguage`型があれば

```
ts`type  <data-lsp lsp="type Language = &quot;en&quot; | &quot;fr&quot; | &quot;es&quot; | &quot;ja&quot; | &quot;zh&quot;" style="border-bottom:solid 2px lightgrey">Language</data-lsp>  =  keyof  <data-lsp lsp="type TypeOfLanguage = {
    en: string;
    fr: string;
    es: string;
    ja: string;
    zh: string;
}">TypeOfLanguage</data-lsp>;` `type Language = "en" | "fr" | "es" | "ja" | "zh"`

```

ts`type <data-lsp lsp="type Language = &quot;en&quot; | &quot;fr&quot; | &quot;es&quot; | &quot;ja&quot; | &quot;zh&quot;" style="border-bottom:solid 2px lightgrey">Language</data-lsp> =  keyof <data-lsp lsp="type TypeOfLanguage = {

    en: string;

    fr: string;

    es: string;

    ja: string;

    zh: string;

}">TypeOfLanguage</data-lsp>;` `type Language = "en" | "fr" | "es" | "ja" | "zh"`

となります。

## 📄️ keyof 型演算子

keyofはオブジェクトの型からプロパティ名を型として返す型演算子です。たとえば、nameプロパティを持つ型に対して、keyofを使うと文字列リテラル型の"name"が得られます。

## まとめ​

見た目が少々いびつですが、次でオブジェクトから希望するキーのユニオン型を生成できます。

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

### 疑問: `keyof conf`じゃダメなんですか？​

動作しません。なぜなら`keyof`は値ではなく (オブジェクトの) 型に対して使用できるからです。一方`typeof`は値から型を生成するのでこの順番で使用する必要があります。

```

```

```

```

```

```
