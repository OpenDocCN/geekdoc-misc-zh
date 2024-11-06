# オブジェクトのサブセットを得る

> 原文：[`typescriptbook.jp/tips/get-a-subset-of-an-object`](https://typescriptbook.jp/tips/get-a-subset-of-an-object)

オブジェクトのサブセットを得る方法です。サブセットとは、あるオブジェクトのいち部分を切り取ったもので、ここで紹介する方法は、プロパティ名を指定してオブジェクトの一部分を切り出すものです。たとえば、次のような数多くのプロパティを持つオブジェクトがあるとき、ここから数個のプロパティだけを持つオブジェクトを作る方法です。

```
ts`const  <data-lsp lsp="const profile: {
    name: string;
    twitter: string;
    github: string;
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">profile</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "suin", <data-lsp lsp="(property) twitter: string">twitter</data-lsp>:  "suin", <data-lsp lsp="(property) github: string">github</data-lsp>:  "suin", <data-lsp lsp="(property) country: string">country</data-lsp>:  "JP", <data-lsp lsp="(property) prefecture: string">prefecture</data-lsp>:  "東京都", <data-lsp lsp="(property) city: string">city</data-lsp>:  "千代田区", <data-lsp lsp="(property) address: string">address</data-lsp>:  "丸の内 2-4-1", <data-lsp lsp="(property) building: string">building</data-lsp>:  "丸ビル", <data-lsp lsp="(property) zipcode: string">zipcode</data-lsp>:  "100-6390",};// 上の9つプロパティを持つオブジェクトから、下の6つのプロパティだけを抽出したオブジェクトを得たいconst  <data-lsp lsp="const address: {
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">address</data-lsp>  = { <data-lsp lsp="(property) country: string">country</data-lsp>:  "JP", <data-lsp lsp="(property) prefecture: string">prefecture</data-lsp>:  "東京都", <data-lsp lsp="(property) city: string">city</data-lsp>:  "千代田区", <data-lsp lsp="(property) address: string">address</data-lsp>:  "丸の内 2-4-1", <data-lsp lsp="(property) building: string">building</data-lsp>:  "丸ビル", <data-lsp lsp="(property) zipcode: string">zipcode</data-lsp>:  "100-6390",};`
```

```
ts`const  <data-lsp lsp="const profile: {
    name: string;
    twitter: string;
    github: string;
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">profile</data-lsp>  = { <data-lsp lsp="(property) name: string">name</data-lsp>:  "suin", <data-lsp lsp="(property) twitter: string">twitter</data-lsp>:  "suin", <data-lsp lsp="(property) github: string">github</data-lsp>:  "suin", <data-lsp lsp="(property) country: string">country</data-lsp>:  "JP", <data-lsp lsp="(property) prefecture: string">prefecture</data-lsp>:  "東京都", <data-lsp lsp="(property) city: string">city</data-lsp>:  "千代田区", <data-lsp lsp="(property) address: string">address</data-lsp>:  "丸の内 2-4-1", <data-lsp lsp="(property) building: string">building</data-lsp>:  "丸ビル", <data-lsp lsp="(property) zipcode: string">zipcode</data-lsp>:  "100-6390",};// 上の9つプロパティを持つオブジェクトから、下の6つのプロパティだけを抽出したオブジェクトを得たいconst  <data-lsp lsp="const address: {
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">address</data-lsp>  = { <data-lsp lsp="(property) country: string">country</data-lsp>:  "JP", <data-lsp lsp="(property) prefecture: string">prefecture</data-lsp>:  "東京都", <data-lsp lsp="(property) city: string">city</data-lsp>:  "千代田区", <data-lsp lsp="(property) address: string">address</data-lsp>:  "丸の内 2-4-1", <data-lsp lsp="(property) building: string">building</data-lsp>:  "丸ビル", <data-lsp lsp="(property) zipcode: string">zipcode</data-lsp>:  "100-6390",};`
```

## 方法 1: 即時関数・分割代入・shorthand property nameの合わせ技​

オブジェクトのサブセットを得る1つ目の方法は、即時関数と分割代入、そして、shorthand property nameを組み合わせる方法です。

```
ts`const  <data-lsp lsp="const sns: {
    twitter: string;
    github: string;
}">sns</data-lsp>  = (({ <data-lsp lsp="(parameter) twitter: string">twitter</data-lsp>, <data-lsp lsp="(parameter) github: string">github</data-lsp> }) => ({ <data-lsp lsp="(property) twitter: string">twitter</data-lsp>, <data-lsp lsp="(property) github: string">github</data-lsp> }))(<data-lsp lsp="const profile: {
    name: string;
    twitter: string;
    github: string;
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">profile</data-lsp>);//=> {//   "twitter": "suin",//   "github": "suin"// }`
```

```
ts`const  <data-lsp lsp="const sns: {
    twitter: string;
    github: string;
}">sns</data-lsp>  = (({ <data-lsp lsp="(parameter) twitter: string">twitter</data-lsp>, <data-lsp lsp="(parameter) github: string">github</data-lsp> }) => ({ <data-lsp lsp="(property) twitter: string">twitter</data-lsp>, <data-lsp lsp="(property) github: string">github</data-lsp> }))(<data-lsp lsp="const profile: {
    name: string;
    twitter: string;
    github: string;
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">profile</data-lsp>);//=> {//   "twitter": "suin",//   "github": "suin"// }`
```

この方法のメリットとデメリットは次のとおりです。

+   メリット

    +   外部ライブラリを必要としない。

+   デメリット

    +   初見の読み手には意外性のあるコードに見える場合がある。

    +   即時関数の引数部分とshorthand property nameの2 箇所に同じプロパティ名を書く必要があり冗長。

この書き方は、数個の少ないプロパティを抽出したいときは便利ですが、たくさんのプロパティを抽出しようとすると記述量が増え、徐々に大変さが出てきます。

抽出したいプロパティよりも、除きたいプロパティのほうが少ない場合は、次のような書き方で除きたいプロパティを指定するほうが簡単です。

```
ts`const  <data-lsp lsp="const address: {
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}" style="border-bottom:solid 2px lightgrey">address</data-lsp>  = (({ <data-lsp lsp="(parameter) name: string">name</data-lsp>, <data-lsp lsp="(parameter) twitter: string">twitter</data-lsp>, <data-lsp lsp="(parameter) github: string">github</data-lsp>,  ...<data-lsp lsp="(parameter) rest: {
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">rest</data-lsp> }) => <data-lsp lsp="(parameter) rest: {
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">rest</data-lsp>)(<data-lsp lsp="const profile: {
    name: string;
    twitter: string;
    github: string;
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">profile</data-lsp>);` `const address: {
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}//=> {//   "country": "JP",//   "prefecture": "東京都",//   "city": "千代田区",//   "address": "丸の内 2-4-1",//   "building": "丸ビル",//   "zipcode": "100-6390"// }`

```

ts`const  <data-lsp lsp="const address: {

    country: string;

    prefecture: string;

    city: string;

    address: string;

    building: string;

    zipcode: string;

}" style="border-bottom:solid 2px lightgrey">address</data-lsp>  = (({ <data-lsp lsp="(parameter) name: string">name</data-lsp>, <data-lsp lsp="(parameter) twitter: string">twitter</data-lsp>, <data-lsp lsp="(parameter) github: string">github</data-lsp>,  ...<data-lsp lsp="(parameter) rest: {

    country: string;

    prefecture: string;

    city: string;

    address: string;

    building: string;

    zipcode: string;

}">rest</data-lsp> }) => <data-lsp lsp="(parameter) rest: {

    country: string;

    prefecture: string;

    city: string;

    address: string;

    building: string;

    zipcode: string;

}">rest</data-lsp>)(<data-lsp lsp="const profile: {

    name: string;

    twitter: string;

    github: string;

    country: string;

    prefecture: string;

    city: string;

    address: string;

    building: string;

    zipcode: string;

}">profile</data-lsp>);` `const address: {

    country: string;

    prefecture: string;

    city: string;

    address: string;

    building: string;

    zipcode: string;

}//=> {//   "country": "JP",//   "prefecture": "東京都",//   "city": "千代田区",//   "address": "丸の内 2-4-1",//   "building": "丸ビル",//   "zipcode": "100-6390"// }`

JavaScriptでは、`delete`を使うとオブジェクトからプロパティを取り除けるので、上の書き方はまどろっこしいと思われるかもしれません。この書き方をするには理由があって、TypeScriptでは`delete`の使い勝手が良くないからです。あるオブジェクトから`delete`を使ってプロパティを取り除きたい場合、TypeScriptではそのプロパティがオプショナルでなければなりません。

```
ts`const  <data-lsp lsp="const address: {
    name: string;
    twitter: string;
    github: string;
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">address</data-lsp>  = { ...<data-lsp lsp="const profile: {
    name: string;
    twitter: string;
    github: string;
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">profile</data-lsp> };delete  <data-lsp lsp="const address: {
    name: string;
    twitter: string;
    github: string;
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">address</data-lsp>.<data-lsp lsp="(property) name: string">name</data-lsp>;The operand of a 'delete' operator must be optional.2790The operand of a 'delete' operator must be optional.`
```

```
ts`const  <data-lsp lsp="const address: {
    name: string;
    twitter: string;
    github: string;
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">address</data-lsp>  = { ...<data-lsp lsp="const profile: {
    name: string;
    twitter: string;
    github: string;
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">profile</data-lsp> };delete  <data-lsp lsp="const address: {
    name: string;
    twitter: string;
    github: string;
    country: string;
    prefecture: string;
    city: string;
    address: string;
    building: string;
    zipcode: string;
}">address</data-lsp>.<data-lsp lsp="(property) name: string">name</data-lsp>;The operand of a 'delete' operator must be optional.2790The operand of a 'delete' operator must be optional.`
```

## 方法 2: lodash.pick / lodash.omit​

2つ目の方法は[lodash](https://lodash.com/)を用いるものです。lodashはさまざまな便利関数を提供するライブラリで、その中のひとつに`pick`というオブジェクトのサブセットを得るための関数があります。

```
ts`import _ from  "lodash";const  sns  =  _.pick(profile, ["twitter",  "github"]);//=> {//   "twitter": "suin",//   "github": "suin"// }`
```

```
ts`import _ from  "lodash";const  sns  =  _.pick(profile, ["twitter",  "github"]);//=> {//   "twitter": "suin",//   "github": "suin"// }`
```

lodash 全体ではなく、`pick`関数だけが必要な場合は、パッケージ[lodash.pick](https://www.npmjs.com/package/lodash.pick)を使うこともできます。この場合、次のようにして`pick`関数を使います。

```
ts`import pick from  "lodash.pick";const  sns  =  pick(profile, ["twitter",  "github"]);`
```

```
ts`import pick from  "lodash.pick";const  sns  = pick(profile, ["twitter",  "github"]);`
```

lodash.pickのメリットとデメリットは次のとおりです。

+   メリット

    +   宣言的で読みやすい。

    +   記述量が少ない。

+   デメリット

    +   ライブラリを導入する必要がある。

lodash.pickは抽出したいプロパティ名を指定する関数ですが、抽出したいプロパティより除外したいプロパティが少ない場合は、[lodash.omit](https://www.npmjs.com/package/lodash.omit)を使ったほうが便利です。

```
ts`import _ from  "lodash";const  address  =  _.omit(profile, ["name",  "twitter",  "github"]);//=> {//   "country": "JP",//   "prefecture": "東京都",//   "city": "千代田区",//   "address": "丸の内 2-4-1",//   "building": "丸ビル",//   "zipcode": "100-6390"// }`
```

```
ts`import _ from  "lodash";const  address  =  _.omit(profile, ["name",  "twitter",  "github"]);//=> {//   "country": "JP",//   "prefecture": "東京都",//   "city": "千代田区",//   "address": "丸の内 2-4-1",//   "building": "丸ビル",//   "zipcode": "100-6390"// }`
```

lodash、lodash.pickとlodash.omitのインストールは次のコマンドで行なえます。

```
bash`# lodashのインストールnpm install lodashnpm install -D @types/lodash``# lodash.pickとlodash.omitのインストールnpm install lodash.pick lodash.omitnpm install -D @types/lodash.pick @types/lodash.omit`

```

bash`# 安装 lodashnpm install lodashnpm install -D @types/lodash``# 安装 lodash.pick 和 lodash.omitnpm install lodash.pick lodash.omitnpm install -D @types/lodash.pick @types/lodash.omit`

```

```

```

```
