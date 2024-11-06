# 配列から全要素の型を生成する

> 原文：[`typescriptbook.jp/tips/generates-type-of-element-from-array`](https://typescriptbook.jp/tips/generates-type-of-element-from-array)

前ページでは、配列から全要素の型を生成する方法が登場しました。

```
ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type  <data-lsp lsp="type Currency = &quot;CNY&quot; | &quot;EUR&quot; | &quot;GBP&quot; | &quot;JPY&quot; | &quot;KRW&quot; | &quot;USD&quot;" style="border-bottom:solid 2px lightgrey">Currency</data-lsp>  = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>)[number];` `type Currency = "CNY" | "EUR" | "GBP" | "JPY" | "KRW" | "USD"`

```

ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type <data-lsp lsp="type Currency = &quot;CNY&quot; | &quot;EUR&quot; | &quot;GBP&quot; | &quot;JPY&quot; | &quot;KRW&quot; | &quot;USD&quot;" style="border-bottom:solid 2px lightgrey">Currency</data-lsp> = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>)[number];` `type Currency = "CNY" | "EUR" | "GBP" | "JPY" | "KRW" | "USD"`

`typeof currencies[number]`という書き方は、初めて見ると理解に苦しむコードかもしれません。そのためより詳しく説明します。

## 前ページのコードを観察する​

配列からある要素の型を生成するコードについて、前ページに続き通貨の配列でもう一度確認します。

```
ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type  <data-lsp lsp="type Currency = &quot;GBP&quot;" style="border-bottom:solid 2px lightgrey">Currency</data-lsp>  = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>)[2];` `type Currency = "GBP"`

```

ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type <data-lsp lsp="type Currency = &quot;GBP&quot;" style="border-bottom:solid 2px lightgrey">Currency</data-lsp> = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>)[2];` `type Currency = "GBP"`

ここで、`typeof currencies[2]`の`2`は、前ページでリテラル型と説明していますが本当でしょうか？次のコードで確認してみます。

```
ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;const  <data-lsp lsp="const index: 2">index</data-lsp>  =  2  as  <data-lsp lsp="type const = 2">const</data-lsp>;type  <data-lsp lsp="type Currency = &quot;CNY&quot; | &quot;EUR&quot; | &quot;GBP&quot; | &quot;JPY&quot; | &quot;KRW&quot; | &quot;USD&quot;">Currency</data-lsp>  = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>)[<data-err><data-lsp lsp="type index = /*unresolved*/ any">index</data-lsp></data-err>];'index' refers to a value, but is being used as a type here. Did you mean 'typeof index'?2749'index' refers to a value, but is being used as a type here. Did you mean 'typeof index'?`
```

```
ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;const  <data-lsp lsp="const index: 2">index</data-lsp>  =  2  as  <data-lsp lsp="type const = 2">const</data-lsp>;type <data-lsp lsp="type Currency = &quot;CNY&quot; | &quot;EUR&quot; | &quot;GBP&quot; | &quot;JPY&quot; | &quot;KRW&quot; | &quot;USD&quot;">Currency</data-lsp> = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>)[<data-err><data-lsp lsp="type index = /*unresolved*/ any">index</data-lsp></data-err>];'index' refers to a value, but is being used as a type here. Did you mean 'typeof index'?2749'index' refers to a value, but is being used as a type here. Did you mean 'typeof index'?`
```

`2`が値として解釈されるコードではエラーになってしまいました。

では明確にリテラル型だとわかるコードも試してみましょう。

```
ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type  <data-lsp lsp="type Index = 2">Index</data-lsp>  =  2;type  <data-lsp lsp="type Currency = &quot;GBP&quot;" style="border-bottom:solid 2px lightgrey">Currency</data-lsp>  = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>)[<data-lsp lsp="type Index = 2">Index</data-lsp>];` `type Currency = "GBP"`

```

ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type <data-lsp lsp="type Index = 2">Index</data-lsp> =  2;type <data-lsp lsp="type Currency = &quot;GBP&quot;" style="border-bottom:solid 2px lightgrey">Currency</data-lsp> = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>)[<data-lsp lsp="type Index = 2">Index</data-lsp>];` `type Currency = "GBP"`

これで`typeof currencies[2]`の`2`はリテラル型であることがはっきりしました。

## 数値のリテラル型と`number`型​

`2`のリテラル型と`number`型の関係を集合で表現すると、`2`⊂`number`と書くことができます。他の表現をすると、`0`、`1`、`2`..など数値のリテラル型のいずれかの型として振る舞うのが`number`型です。

「いずれかの型」といえばユニオン型の出番です。

[## 📄️ ユニオン型

TypeScriptのユニオン型(union type)は「いずれかの型」を表現するものです。

`number`型の代わりにリテラルのユニオン型を使ってみましょう。

```
ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type  <data-lsp lsp="type Currency = &quot;CNY&quot; | &quot;EUR&quot; | &quot;GBP&quot; | &quot;JPY&quot; | &quot;KRW&quot; | &quot;USD&quot;" style="border-bottom:solid 2px lightgrey">Currency</data-lsp>  = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>)[0  |  1  |  2  |  3  |  4  |  5];` `type Currency = "CNY" | "EUR" | "GBP" | "JPY" | "KRW" | "USD"`

```

ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type <data-lsp lsp="type Currency = &quot;CNY&quot; | &quot;EUR&quot; | &quot;GBP&quot; | &quot;JPY&quot; | &quot;KRW&quot; | &quot;USD&quot;" style="border-bottom:solid 2px lightgrey">Currency</data-lsp> = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>)[0  |  1  |  2  |  3  |  4  |  5];` `type Currency = "CNY" | "EUR" | "GBP" | "JPY" | "KRW" | "USD"`

`0 | 1 | 2 | 3 | 4 | 5`型でも`currencies`配列から全要素の型を生成することができました。このように`number`型は数値のリテラル型のワイルドカードとして振る舞うことがわかります。

## 一般化する​

このページの締めくくりに一般化したコードを示します。

```
ts`type  <data-lsp lsp="type List = (string | number | boolean)[]">List</data-lsp>  = (string  |  number  |  boolean)[];type  <data-lsp lsp="type Elem = string | number | boolean" style="border-bottom:solid 2px lightgrey">Elem</data-lsp>  =  <data-lsp lsp="type List = (string | number | boolean)[]">List</data-lsp>[number];` `type Elem = string | number | boolean`

```

ts`type <data-lsp lsp="type List = (string | number | boolean)[]">List</data-lsp> = (string  |  number  |  boolean)[];type <data-lsp lsp="type Elem = string | number | boolean" style="border-bottom:solid 2px lightgrey">Elem</data-lsp> = <data-lsp lsp="type List = (string | number | boolean)[]">List</data-lsp>[number];` `type Elem = string | number | boolean`

`List`型から`List[number]`という書き方ですべての要素の型である`string | number | boolean`が生成できました。

### アンチパターンの紹介​

次のように具体的なインデックスで同じ型を生成することは可能ですが、アンチパターンなので注意してください。

```
ts`type  <data-lsp lsp="type List = (string | number | boolean)[]">List</data-lsp>  = (string  |  number  |  boolean)[];type  <data-lsp lsp="type Elem = string | number | boolean" style="border-bottom:solid 2px lightgrey">Elem</data-lsp>  =  <data-lsp lsp="type List = (string | number | boolean)[]">List</data-lsp>[0]; // 避けるべき書き方` `type Elem = string | number | boolean`

```

ts`type <data-lsp lsp="type List = (string | number | boolean)[]">List</data-lsp> = (string  |  number  |  boolean)[];type <data-lsp lsp="type Elem = string | number | boolean" style="border-bottom:solid 2px lightgrey">Elem</data-lsp> = <data-lsp lsp="type List = (string | number | boolean)[]">List</data-lsp>[0]; // 避けるべき書き方` `type Elem = string | number | boolean`

この書き方がアンチパターンである理由は`List`型をタプル型だと混乱させてしまう可能性があるためです。`List[0]`は特定の要素から型を生成しているため、各要素の型が同じ型ではない、つまり`List`が配列型ではなくタプル型だからこの書き方をしていると誤解させる可能性があります。配列型はどの要素の型も同じものとして扱うので、`List[number]`の書き方が適切です。

```

```

```

```

```

```

```

```

```

```

```

```
