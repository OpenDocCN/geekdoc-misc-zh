# 配列から型を生成する

> 原文：[`typescriptbook.jp/tips/generates-type-from-array`](https://typescriptbook.jp/tips/generates-type-from-array)

単位のように振る舞うことを期待されて定義されたコレクションは少なくないでしょう。今回はコレクションでも主に配列に焦点を当てそれらから型を生成する方法の紹介です。

## 通貨の配列から通貨の型を作りたい​

国際的な外貨を使うことができるサービスを開発していたとします。サポートしている通貨を配列で保持しているとし次のようになっているとします。

```
ts`const  <data-lsp lsp="const currencies: string[]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"];`
```

```
ts`const  <data-lsp lsp="const currencies: string[]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"];`
```

このようなとき、このJavaScriptの資産をできるだけ変更せずに貨幣の

```
ts`type  <data-lsp lsp="type Currency = &quot;CNY&quot; | &quot;EUR&quot; | &quot;GBP&quot; | &quot;JPY&quot; | &quot;KRW&quot; | &quot;USD&quot;">Currency</data-lsp>  =  "CNY"  |  "EUR"  |  "GBP"  |  "JPY"  |  "KRW"  |  "USD";`
```

```
ts`type <data-lsp lsp="type Currency = &quot;CNY&quot; | &quot;EUR&quot; | &quot;GBP&quot; | &quot;JPY&quot; | &quot;KRW&quot; | &quot;USD&quot;">Currency</data-lsp> =  "CNY"  |  "EUR"  |  "GBP"  |  "JPY"  |  "KRW"  |  "USD";`
```

### `typeof`​

これはJavaScriptの`typeof`ではなくTypeScriptの`typeof`です。`typeof`はTypeScriptがその変数をどのような型であるかと認識しているかかを教えてくれます。

```
ts`const  <data-lsp lsp="const currencies: string[]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"];type  <data-lsp lsp="type Currency = string[]" style="border-bottom:solid 2px lightgrey">Currency</data-lsp>  =  typeof <data-lsp lsp="const currencies: string[]">currencies</data-lsp>;` `type Currency = string[]`

```

ts`const  <data-lsp lsp="const currencies: string[]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"];type <data-lsp lsp="type Currency = string[]" style="border-bottom:solid 2px lightgrey">Currency</data-lsp> =  typeof <data-lsp lsp="const currencies: string[]">currencies</data-lsp>;` `type Currency = string[]`

予想されている方が多かったかもしれませんが`string[]`型と出てしまいました。ではこれをどうすれば`string`ではなく定数値で取得できるでしょうか。それは定数値で取得したいオブジェクトに`as const`をつけると取得できます。

```
ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type  <data-lsp lsp="type Currency = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]" style="border-bottom:solid 2px lightgrey">Currency</data-lsp>  =  typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>;` `type Currency = readonly ["CNY", "EUR", "GBP", "JPY", "KRW", "USD"]`

```

ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type <data-lsp lsp="type Currency = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]" style="border-bottom:solid 2px lightgrey">Currency</data-lsp> =  typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>;` `type Currency = readonly ["CNY", "EUR", "GBP", "JPY", "KRW", "USD"]`

定数 (リテラル型) は取れましたが依然配列のままです。これをユニオン型で取るためには考え方を逆転させる必要があります。

#### 何番目のリテラル型が欲しいか​

たとえば`'GBP'`が欲しいとします。`'GBP'`は2 番目なので`currencies`の2 番目の型を取れば希望のリテラル型が取れます。

```
ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type  <data-lsp lsp="type Currency = &quot;GBP&quot;" style="border-bottom:solid 2px lightgrey">Currency</data-lsp>  = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>)[2];` `type Currency = "GBP"`

```

ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type <data-lsp lsp="type Currency = &quot;GBP&quot;" style="border-bottom:solid 2px lightgrey">Currency</data-lsp> = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>)[2];` `type Currency = "GBP"`

`'GBP'`を取ることができました。

### すべてのリテラル型が欲しい​

本題です。まさか次のようにするわけには行かないのでもっと賢い方法を考える必要があります。

```
ts`type  Currency  =  typeof currencies[0] |  typeof currencies[1] |  typeof currencies[2] | ....`
```

```
ts`type Currency =  typeof currencies[0] |  typeof currencies[1] |  typeof currencies[2] | ....`
```

そこで思いつくのは`typeof`をしているときのインデックスです。実はこれもリテラル型であり`currencies`の`2`のリテラル型を取ることを意味しています。

配列はnumber 型のインデックスに要素を代入しているオブジェクトなのでこのリテラル型のインデックスの代わりに`number`を使うことによって

```
ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type  <data-lsp lsp="type Currency = &quot;CNY&quot; | &quot;EUR&quot; | &quot;GBP&quot; | &quot;JPY&quot; | &quot;KRW&quot; | &quot;USD&quot;" style="border-bottom:solid 2px lightgrey">Currency</data-lsp>  = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">currencies</data-lsp>)[number];` `type Currency = "CNY" | "EUR" | "GBP" | "JPY" | "KRW" | "USD"`

```

ts`const  <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">货币</data-lsp>  = ["CNY",  "EUR",  "GBP",  "JPY",  "KRW",  "USD"] as  <data-lsp lsp="type const = readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot;]">const</data-lsp>;type <data-lsp lsp="type Currency = &quot;CNY&quot; | &quot;EUR&quot; | &quot;GBP&quot; | &quot;JPY&quot; | &quot;KRW&quot; | &quot;USD&quot;" style="border-bottom:solid 2px lightgrey">货币类型</data-lsp> = (typeof <data-lsp lsp="const currencies: readonly [&quot;CNY&quot;, &quot;EUR&quot;, &quot;GBP&quot;, &quot;JPY&quot;, &quot;KRW&quot;, &quot;USD&quot]">货币</data-lsp>)[number];` `type 货币类型 = "CNY" | "EUR" | "GBP" | "JPY" | "KRW" | "USD"`

と希望のユニオン型を取得できます。

```

```

```

```

```

```

```

```
