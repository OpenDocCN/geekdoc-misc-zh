# 单一责任原则

# 单一责任原则

良好设计的最基本原则之一是：

> 将因相同原因而改变的事物聚集在一起，并将因不同原因而改变的事物分开。

这个原则通常被称为*单一责任原则*或 SRP。简而言之，它指出一个子系统、模块、类，甚至一个函数，不应该有多个改变的理由。一个经典的例子是一个具有处理业务规则、报告和数据库的方法的类：

```
public class Employee {
  public Money calculatePay() ...
  public String reportHours() ...
  public void save() ...
} 
```

一些程序员可能认为将这三个函数放在同一个类中是完全合适的。毕竟，类应该是对共同变量进行操作的函数集合。然而，问题在于这三个函数因完全不同的原因而改变。`calculatePay` 函数会在计算支付的业务规则更改时更改。`reportHours` 函数会在有人想要报告的不同格式时更改。保存函数会在数据库管理员更改数据库架构时更改。这三个改变的原因结合在一起使 `Employee` 非常不稳定。它会因为任何这些原因而改变。更重要的是，任何依赖于 `Employee` 的类都会受到这些更改的影响。

良好的系统设计意味着我们将系统分成可以独立部署的组件。独立部署意味着如果我们改变一个组件，我们不必重新部署其他组件。然而，如果 `Employee` 被其他组件中的许多其他类频繁使用，那么对 Employee 的每一次更改很可能导致其他组件被重新部署；从而抵消了组件设计（或者如果您更喜欢更时尚的名称，可以说是 SOA）的一个主要优点。

```
public class Employee {
  public Money calculatePay() ...
}

public class EmployeeReporter {
  public String reportHours(Employee e) ...
}

public class EmployeeRepository {
  public void save(Employee e) ...
} 
```

上面显示的简单分区解决了这些问题。这些类中的每一个都可以放在自己的组件中。或者，所有报告类都可以放在报告组件中。所有与数据库相关的类都可以放在存储库组件中。所有业务规则可以放在业务规则组件中。

敏锐的读者会发现上面的解决方案仍然存在依赖关系。`Employee` 仍然被其他类依赖。因此，如果修改 `Employee`，其他类很可能需要重新编译和部署。因此，`Employee` 无法进行修改然后独立部署。然而，其他类可以进行修改并独立部署。对其中任何一个进行修改都不会强制其他类重新编译或重新部署。甚至通过谨慎使用*依赖反转原则*（DIP），甚至可以独立部署 `Employee`，但这是另一本[不同的书](http://www.amazon.com/dp/0135974445/)的话题。

仔细应用 SRP，将因不同原因而改变的事物分开，是创建具有独立可部署组件结构的设计的关键之一。

由[Bob 大叔](http://programmer.97things.oreilly.com/wiki/index.php/Uncle_Bob)
