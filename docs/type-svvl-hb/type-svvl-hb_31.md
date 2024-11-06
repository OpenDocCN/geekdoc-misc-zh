# 型の再利用

> 原文：[`typescriptbook.jp/reference/type-reuse`](https://typescriptbook.jp/reference/type-reuse)

TypeScriptでは型から別の型を導き出す機能があります。既存の型を再度利用して、新たな型を生み出すことを本書では「型の再利用」と呼ぶことにします。

## 型の再利用のメタファー​

多くのプログラミング言語では、変数を処理して別の変数を導き出せます。たとえば、あるオブジェクトのキーの配列が欲しいとき、キーの配列を別途宣言してもよいです。しかし、オブジェクトからキーを導きだしたほうが変更に強いコードになります。

```
ts`const  <data-lsp lsp="const obj: {
    a: number;
    b: number;
    c: number;
}">obj</data-lsp>  = { <data-lsp lsp="(property) a: number">a</data-lsp>:  1, <data-lsp lsp="(property) b: number">b</data-lsp>:  2, <data-lsp lsp="(property) c: number">c</data-lsp>:  3 };const  <data-lsp lsp="const keys1: string[]">keys1</data-lsp>  = ["a",  "b",  "c"];const  <data-lsp lsp="const keys2: string[]">keys2</data-lsp>  =  <data-lsp lsp="var Object: ObjectConstructor">Object</data-lsp>.<data-lsp lsp="(method) ObjectConstructor.keys(o: {}): string[] (+1 overload)">keys</data-lsp>(<data-lsp lsp="const obj: {
    a: number;
    b: number;
    c: number;
}">obj</data-lsp>); // keys1より保守性が高い`
```

```
ts`const  <data-lsp lsp="const obj: {
    a: number;
    b: number;
    c: number;
}">obj</data-lsp>  = { <data-lsp lsp="(property) a: number">a</data-lsp>:  1, <data-lsp lsp="(property) b: number">b</data-lsp>:  2, <data-lsp lsp="(property) c: number">c</data-lsp>:  3 };const  <data-lsp lsp="const keys1: string[]">keys1</data-lsp>  = ["a",  "b",  "c"];const  <data-lsp lsp="const keys2: string[]">keys2</data-lsp>  =  <data-lsp lsp="var Object: ObjectConstructor">Object</data-lsp>.<data-lsp lsp="(method) ObjectConstructor.keys(o: {}): string[] (+1 overload)">keys</data-lsp>(<data-lsp lsp="const obj: {
    a: number;
    b: number;
    c: number;
}">obj</data-lsp>); // keys1より保守性が高い`
```

上は変数の再利用の例です。TypeScriptには変数の再利用の型バージョンがあります。それが型の再利用です。たとえば、あるオブジェクトの型からキーの型を導き出すことができます。

```
ts`type  <data-lsp lsp="type Obj = {
    a: string;
    b: string;
    c: string;
}">Obj</data-lsp>  = { <data-lsp lsp="(property) a: string">a</data-lsp>:  string; <data-lsp lsp="(property) b: string">b</data-lsp>:  string; <data-lsp lsp="(property) c: string">c</data-lsp>:  string };type  <data-lsp lsp="type Keys = keyof Obj">Keys</data-lsp>  =  keyof  <data-lsp lsp="type Obj = {
    a: string;
    b: string;
    c: string;
}">Obj</data-lsp>;//=> "a" | "b" | "c"`
```

```
ts`type <data-lsp lsp="type Obj = {
    a: string;
    b: string;
    c: string;
}">Obj</data-lsp> = { <data-lsp lsp="(property) a: string">a</data-lsp>:  string; <data-lsp lsp="(property) b: string">b</data-lsp>:  string; <data-lsp lsp="(property) c: string">c</data-lsp>:  string };type <data-lsp lsp="type Keys = keyof Obj">Keys</data-lsp> =  keyof <data-lsp lsp="type Obj = {
    a: string;
    b: string;
    c: string;
}">Obj</data-lsp>;//=> "a" | "b" | "c"`
```

型の再利用とは、変数の再利用のメタファーなのです。
