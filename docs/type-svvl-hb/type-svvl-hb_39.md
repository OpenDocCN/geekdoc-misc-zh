# オブジェクトから型を生成する

> 原文：[`typescriptbook.jp/tips/generates-type-from-object`](https://typescriptbook.jp/tips/generates-type-from-object)

多くの言語では型による構造体、オブジェクト��定義をしてからコーディングが始まりますが、元がJavaScriptであるTypeScriptにはそのような決まりがないことも多々あります。

## 一般的な型を先に決めるプログラミング​

多くの言語ではその型が何かを決めてから、その型に属するオブジェクトを決めます。次の例はTypeScriptの例ですが、他の言語に当てはめても問題なく受け入れられると思います。

```
ts`type  <data-lsp lsp="type Account = {
    accountName: string;
    password: string;
    age: number;
    plan: &quot;Free&quot; | &quot;Standard&quot; | &quot;Premium&quot;;
}">Account</data-lsp>  = { <data-lsp lsp="(property) accountName: string">accountName</data-lsp>:  string; <data-lsp lsp="(property) password: string">password</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number; <data-lsp lsp="(property) plan: &quot;Free&quot; | &quot;Standard&quot; | &quot;Premium&quot;">plan</data-lsp>:  "Free"  |  "Standard"  |  "Premium";};const  <data-lsp lsp="const account: Account">account</data-lsp>:  <data-lsp lsp="type Account = {
    accountName: string;
    password: string;
    age: number;
    plan: &quot;Free&quot; | &quot;Standard&quot; | &quot;Premium&quot;;
}">Account</data-lsp>  = { <data-lsp lsp="(property) accountName: string">accountName</data-lsp>:  "yyts", <data-lsp lsp="(property) password: string">password</data-lsp>:  "ccbyncsa30", <data-lsp lsp="(property) age: number">age</data-lsp>:  80, <data-lsp lsp="(property) plan: &quot;Free&quot; | &quot;Standard&quot; | &quot;Premium&quot;">plan</data-lsp>:  "Standard",};`
```

```
ts`type <data-lsp lsp="type Account = {
    accountName: string;
    password: string;
    age: number;
    plan: &quot;Free&quot; | &quot;Standard&quot; | &quot;Premium&quot;;
}">Account</data-lsp> = { <data-lsp lsp="(property) accountName: string">accountName</data-lsp>:  string; <data-lsp lsp="(property) password: string">password</data-lsp>:  string; <data-lsp lsp="(property) age: number">age</data-lsp>:  number; <data-lsp lsp="(property) plan: &quot;Free&quot; | &quot;Standard&quot; | &quot;Premium&quot;">plan</data-lsp>:  "Free"  |  "Standard"  |  "Premium";};const  <data-lsp lsp="const account: Account">account</data-lsp>: <data-lsp lsp="type Account = {
    accountName: string;
    password: string;
    age: number;
    plan: &quot;Free&quot; | &quot;Standard&quot; | &quot;Premium&quot;;
}">Account</data-lsp> = { <data-lsp lsp="(property) accountName: string">accountName</data-lsp>:  "yyts", <data-lsp lsp="(property) password: string">password</data-lsp>:  "ccbyncsa30", <data-lsp lsp="(property) age: number">age</data-lsp>:  80, <data-lsp lsp="(property) plan: &quot;Free&quot; | &quot;Standard&quot; | &quot;Premium&quot;">plan</data-lsp>:  "Standard",};`
```

すでにJavaScriptの資産があるプロジェクトにおいては表立って型などなく、そのため`Account`といった型は存在せず代入式の`const account`のみが存在していることでしょう。そんなときはこの`const account`をTypeScriptに変換してできるだけ近い形で型を作ることができます。

### `typeof`​

この`typeof`はJavaScriptのものではなく、TypeScriptの`typeof`です。これを実際に動作している変数に使ってみるとその変数をTypeScriptはどのような型と認識しているのかがわかります。

```
ts`const  <data-lsp lsp="const account: {
    accountName: string;
    password: string;
    age: number;
    plan: string;
}">account</data-lsp>  = { <data-lsp lsp="(property) accountName: string">accountName</data-lsp>:  "yyts", <data-lsp lsp="(property) password: string">password</data-lsp>:  "ccbyncsa30", <data-lsp lsp="(property) age: number">age</data-lsp>:  80, <data-lsp lsp="(property) plan: string">plan</data-lsp>:  "Standard",};type  <data-lsp lsp="type Account = {
    accountName: string;
    password: string;
    age: number;
    plan: string;
}" style="border-bottom:solid 2px lightgrey">Account</data-lsp>  =  typeof <data-lsp lsp="const account: {
    accountName: string;
    password: string;
    age: number;
    plan: string;
}">account</data-lsp>;` `type Account = {
    accountName: string;
    password: string;
    age: number;
    plan: string;
}`

```

ts`const  <data-lsp lsp="const account: {

    accountName: string;

    password: string;

    age: number;

    plan: string;

}">account</data-lsp>  = { <data-lsp lsp="(property) accountName: string">accountName</data-lsp>:  "yyts", <data-lsp lsp="(property) password: string">password</data-lsp>:  "ccbyncsa30", <data-lsp lsp="(property) age: number">age</data-lsp>:  80, <data-lsp lsp="(property) plan: string">plan</data-lsp>:  "Standard",};type <data-lsp lsp="type Account = {

    accountName: string;

    password: string;

    age: number;

    plan: string;

}" style="border-bottom:solid 2px lightgrey">Account</data-lsp> =  typeof <data-lsp lsp="const account: {

    accountName: string;

    password: string;

    age: number;

    plan: string;

}">account</data-lsp>;` `type Account = {

    accountName: string;

    password: string;

    age: number;

    plan: string;

}`

`plan`が意図するユニオン型にはなりませんが、それなりに近い型を得ることができました。

### プロパティを定数値で取得したい場合​

プロパティを定数値で取得したい場合はオブジェクトに`as const`をつけます。

```
ts`const  <data-lsp lsp="const account: {
    readonly accountName: &quot;yyts&quot;;
    readonly password: &quot;ccbyncsa30&quot;;
    readonly age: 80;
    readonly plan: &quot;Standard&quot;;
}">account</data-lsp>  = { <data-lsp lsp="(property) accountName: &quot;yyts&quot;">accountName</data-lsp>:  "yyts", <data-lsp lsp="(property) password: &quot;ccbyncsa30&quot;">password</data-lsp>:  "ccbyncsa30", <data-lsp lsp="(property) age: 80">age</data-lsp>:  80, <data-lsp lsp="(property) plan: &quot;Standard&quot;">plan</data-lsp>:  "Standard",} as  <data-lsp lsp="type const = {
    readonly accountName: &quot;yyts&quot;;
    readonly password: &quot;ccbyncsa30&quot;;
    readonly age: 80;
    readonly plan: &quot;Standard&quot;;
}">const</data-lsp>;type  <data-lsp lsp="type Account = {
    readonly accountName: &quot;yyts&quot;;
    readonly password: &quot;ccbyncsa30&quot;;
    readonly age: 80;
    readonly plan: &quot;Standard&quot;;
}" style="border-bottom:solid 2px lightgrey">Account</data-lsp>  =  typeof <data-lsp lsp="const account: {
    readonly accountName: &quot;yyts&quot;;
    readonly password: &quot;ccbyncsa30&quot;;
    readonly age: 80;
    readonly plan: &quot;Standard&quot;;
}">account</data-lsp>;` `type Account = {
    readonly accountName: "yyts";
    readonly password: "ccbyncsa30";
    readonly age: 80;
    readonly plan: "Standard";
}`

```

ts`const  <data-lsp lsp="const account: {

    readonly accountName: &quot;yyts&quot;;

    readonly password: &quot;ccbyncsa30&quot;;

    readonly age: 80;

    readonly plan: &quot;Standard&quot;;

}">account</data-lsp>  = { <data-lsp lsp="(property) accountName: &quot;yyts&quot;">accountName</data-lsp>:  "yyts", <data-lsp lsp="(property) password: &quot;ccbyncsa30&quot;">password</data-lsp>:  "ccbyncsa30", <data-lsp lsp="(property) age: 80">age</data-lsp>:  80, <data-lsp lsp="(property) plan: &quot;Standard&quot;">plan</data-lsp>:  "Standard",} as  <data-lsp lsp="type const = {

    readonly accountName: &quot;yyts&quot;;

    readonly password: &quot;ccbyncsa30&quot;;

    readonly age: 80;

    readonly plan: &quot;Standard&quot;;

}">const</data-lsp>;type <data-lsp lsp="type Account = {

    readonly accountName: &quot;yyts&quot;;

    readonly password: &quot;ccbyncsa30&quot;;

    readonly age: 80;

    readonly plan: &quot;Standard&quot;;

}" style="border-bottom:solid 2px lightgrey">Account</data-lsp> =  typeof <data-lsp lsp="const account: {

    readonly accountName: &quot;yyts&quot;;

    readonly password: &quot;ccbyncsa30&quot;;

    readonly age: 80;

    readonly plan: &quot;Standard&quot;;

}">account</data-lsp>;` `type Account = {

    readonly accountName: "yyts";

    readonly password: "ccbyncsa30";

    readonly age: 80;

    readonly plan: "Standard";

}`

### 特定のプロパティだけを定数値で取得したい場合​

これでは型の制約が強力すぎて他の値が代入できないので、もう少し柔軟にします。たとえば`plan`だけがユニオン型になるようにしたければ`plan`の右に希望の型を書いてあげればそれでその型になります。

```
ts`const  <data-lsp lsp="const account: {
    accountName: string;
    password: string;
    age: number;
    plan: &quot;Standard&quot; | &quot;Free&quot; | &quot;Premium&quot;;
}">account</data-lsp>  = { <data-lsp lsp="(property) accountName: string">accountName</data-lsp>:  "yyts", <data-lsp lsp="(property) password: string">password</data-lsp>:  "ccbyncsa30", <data-lsp lsp="(property) age: number">age</data-lsp>:  80, <data-lsp lsp="(property) plan: &quot;Standard&quot; | &quot;Free&quot; | &quot;Premium&quot;">plan</data-lsp>:  "Standard"  as  "Free"  |  "Standard"  |  "Premium",};type  <data-lsp lsp="type Account = {
    accountName: string;
    password: string;
    age: number;
    plan: &quot;Standard&quot; | &quot;Free&quot; | &quot;Premium&quot;;
}" style="border-bottom:solid 2px lightgrey">Account</data-lsp>  =  typeof <data-lsp lsp="const account: {
    accountName: string;
    password: string;
    age: number;
    plan: &quot;Standard&quot; | &quot;Free&quot; | &quot;Premium&quot;;
}">account</data-lsp>;` `type Account = {
    accountName: string;
    password: string;
    age: number;
    plan: "Standard" | "Free" | "Premium";
}`

```

ts`const  <data-lsp lsp="const account: {

    accountName: string;

    password: string;

    age: number;

    plan: &quot;Standard&quot; | &quot;Free&quot; | &quot;Premium&quot;;

}">account</data-lsp>  = { <data-lsp lsp="(property) accountName: string">accountName</data-lsp>:  "yyts", <data-lsp lsp="(property) password: string">password</data-lsp>:  "ccbyncsa30", <data-lsp lsp="(property) age: number">age</data-lsp>:  80, <data-lsp lsp="(property) plan: &quot;Standard&quot; | &quot;Free&quot; | &quot;Premium&quot;">plan</data-lsp>:  "Standard"  as  "Free"  |  "Standard"  |  "Premium",};type <data-lsp lsp="type Account = {

    accountName: string;

    password: string;

    age: number;

    plan: &quot;Standard&quot; | &quot;Free&quot; | &quot;Premium&quot;;

}" style="border-bottom:solid 2px lightgrey">Account</data-lsp> =  typeof <data-lsp lsp="const account: {

    accountName: string;

    password: string;

    age: number;

    plan: &quot;Standard&quot; | &quot;Free&quot; | &quot;Premium&quot;;

}">account</data-lsp>;` `type Account = {

    accountName: string;

    password: string;

    age: number;

    plan: "Standard" | "Free" | "Premium";

}`

```

```

```

```

```

```
