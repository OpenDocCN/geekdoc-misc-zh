# 5  抽象域库

抽象解释中的抽象域概念（参见**Sec. 3.1**）独立于特定应用，并且可以在许多不同的静态分析的部分中实现，并且甚至可以相互替换。这样的库实现了抽象属性的表示和对这些属性的操作的算法，例如逻辑操作、属性变换器、加宽等。

### 5.1  [NewPolka](http://pop-art.inrialpes.fr/people/bjeannet/newpolka/index.html)多面体库

[NewPolka](http://pop-art.inrialpes.fr/people/bjeannet/newpolka/index.html)库处理具有有理系数约束和生成器的凸多面体（具有 C 和 OCaml 接口）。

### 5.2  [Parma Polyhedra Library (PPL)](http://www.cs.unipr.it/ppl/)

[Parma Polyhedra Library (PPL)](http://www.cs.unipr.it/ppl/)是一个用户友好的、完全动态的、可移植的、异常安全的、高效的 C++库，用于处理凸多面体，它可以被定义为有理系数（严格或非严格）的有限数量的（开放或闭合）超空间的交集，每个超空间由一个等式或不等式描述。

### 5.3  [八边形抽象域库](http://www.di.ens.fr/~mine/oct/)

[八边形抽象域库](http://www.di.ens.fr/~mine/oct/)是一个用于操作特殊类型的多面体的库，这些多面体称为八边形，对应于形式为 +/-*x* +/-*y* ≤ *c* 的约束集（其中 *x* 和 *y* 是变量， *c* 是有理常数，因此，在二维情况下，这些多面体最多有八个面）[85]。
