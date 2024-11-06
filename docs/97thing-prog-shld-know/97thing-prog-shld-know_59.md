# 未利用多态性的机会

# 未利用多态性的机会

多态性是面向对象编程中基本的伟大思想之一。这个词源于希腊语，意思是多 (*poly*) 种形式 (*morph*)。在编程的语境中，多态性指的是特定类的对象或方法的多种形式。但多态性不仅仅是关于替代实现。谨慎使用多态性可以创建微小的局部执行环境，让我们能够在不需要冗长的 *if-then-else* 块的情况下工作。处于上下文中使我们能够直接做正确的事情，而处于上下文之外则迫使我们重新构造上下文，以便我们随后能够做正确的事情。通过谨慎使用替代实现，我们可以捕获可以帮助我们生成更少但更可读的代码的上下文。这最好通过一些代码来演示，比如下面（不现实地）简单的购物车：

```
public class ShoppingCart {
    private ArrayList<Item> cart = new ArrayList<Item>();
    public void add(Item item) { cart.add(item); }
    public Item takeNext() { return cart.remove(0);  }
    public boolean isEmpty() { return cart.isEmpty(); }
} 
```

假设我们的网店提供可以下载的物品和需要邮寄的物品。让我们构建另一个支持这些操作的对象：

```
public class Shipping {
    public boolean ship(Item item, SurfaceAddress address) { ... }
    public boolean ship(Item item, EMailAddress address { ... }
} 
```

当客户完成结账时，我们需要发货：

```
while (!cart.isEmpty()) {
    shipping.ship(cart.takeNext(), ???);
} 
```

*???*参数不是某种新的花哨的 Elvis 操作符，而是在询问我应该通过电子邮件还是普通邮件发送物品？回答这个问题所需的上下文已经不存在。我们本可以在布尔值或枚举中捕获运输方式，然后使用 *if-then-else* 填充缺少的参数。另一种解决方案是创建两个都扩展自 Item 的类。我们将它们称为 DownloadableItem 和 SurfaceItem。现在让我们写一些代码。我将提升 Item 为支持单个方法 ship 的接口。为了发送购物车的内容，我们将调用`item.ship(shipper)`。类`DownloadableItem`和`SurfaceItem`都将实现 ship。

```
public class DownloadableItem implements Item {
    public boolean ship(Shipping shipper) {
        shipper.ship(this, customer.getEmailAddress());
    }
}

public class SurfaceItem implements Item {
    public boolean ship(Shipping shipper) {
        shipper.ship(this, customer.getSurfaceAddress());
    }
} 
```

在这个例子中，我们已经委托每个物品处理`Shipping`的责任。由于每个物品都知道如何最好地发货，这种安排使我们能够继续进行而无需 *if-then-else*。该代码还演示了两种经常一起使用的模式：命令和双重分派。对这些模式的有效使用依赖于对多态性的谨慎使用。当这种情况发生时，我们的代码中将减少 *if-then-else* 块的数量。

虽然有些情况下使用 *if-then-else* 比使用多态性更实际，但更多情况下，更多态的编码风格将产生一个更小、更可读且更不脆弱的代码库。错过的机会数量是我们代码中 *if-then-else* 语句的简单计数。

作者为[Kirk Pepperdine](http://programmer.97things.oreilly.com/wiki/index.php/Kirk_Pepperdine)。
