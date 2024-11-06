# WET 会削弱性能瓶颈

# WET 会削弱性能瓶颈

DRY 原则（Don't Repeat Yourself）的重要性在于它规范了一个系统中的每一条知识都应该有一个单一的表现形式的思想。换句话说，知识应该包含在单一的实现中。DRY 的反义词是 WET（Write Every Time）。当知识被编码在几个不同的实现中时，我们的代码就是 WET 的。考虑到 DRY 与 WET 在性能配置文件上的众多影响，DRY 与 WET 的性能影响变得非常明显。

让我们首先考虑我们系统的一个特性，比如*X*，它是一个 CPU 瓶颈。假设特性*X*占用了 CPU 的 30%。现在假设特性*X*有十种不同的实现。平均而言，每个实现将占用 CPU 的 3%。如果我们想要快速取得成功，那么这个 CPU 利用率水平是不值得担心的，很可能我们会忽视这个特性是我们的瓶颈。然而，假设我们以某种方式识别出特性*X*是一个瓶颈。现在我们面临的问题是找到并修复每一个实现。在 WET 中，我们有十个不同的实现需要找到并修复。而在 DRY 中，我们会清楚地看到 30%的 CPU 利用率，而且我们只需要修复十分之一的代码。我提到了我们不必花时间去寻找每一个实现吗？

有一个使用案例，我们经常违反 DRY 的：我们对集合的使用。一个常见的实现查询的技巧是迭代集合，然后依次对每个元素应用查询：

```
public class UsageExample {
    private ArrayList<Customer> allCustomers = new ArrayList<Customer>();
    // ...
    public ArrayList<Customer> findCustomersThatSpendAtLeast(Money amount) {
        ArrayList<Customer> customersOfInterest = new ArrayList<Customer>();
        for (Customer customer: allCustomers) {
            if (customer.spendsAtLeast(amount))
               customersOfInterest.add(customer);
        }
        return customersOfInterest;
    }
} 
```

通过向客户暴露这个原始集合，我们违反了封装。这不仅限制了我们重构的能力，还迫使我们代码的用户违反 DRY 原则，因为他们每个人都要重新实现可能相同的查询。通过将暴露的原始集合从 API 中移除，我们可以轻松避免这种情况。在这个例子中，我们可以引入一个新的、与我们的领域语义更加一致的集合类型，称为`CustomerList`。这个新类更符合我们领域的语义。它将成为我们所有查询的自然容器。

有了这种新的集合类型，我们还可以轻松地查看这些查询是否是性能瓶颈。通过将查询合并到类中，我们消除了向客户暴露表示选择（如`ArrayList`）的需要。这使我们可以自由地更改这些实现，而不必担心违反客户合同：

```
public class CustomerList {
    private ArrayList<Customer> customers = new ArrayList<Customer>();
    private SortedList<Customer> customersSortedBySpendingLevel = new SortedList<Customer>();
    // ...
    public CustomerList findCustomersThatSpendAtLeast(Money amount) {
        return new CustomerList(customersSortedBySpendingLevel.elementsLargerThan(amount));
    }
}

public class UsageExample {
    public static void main(String[] args) {
        CustomerList customers = new CustomerList();
        // ...
        CustomerList customersOfInterest = customers.findCustomersThatSpendAtLeast(someMinimalAmount);
        // ...
    }
} 
```

在这个例子中，遵循 DRY 原则使我们能够引入一个基于客户消费水平的 SortedList 的替代索引方案。比这个特定例子的具体细节更重要的是，遵循 DRY 原则帮助我们找到并修复了一个性能瓶颈，如果代码是 WET 的话，那么要找到这个瓶颈将更加困难。

作者：[柯克·佩珀丁](http://programmer.97things.oreilly.com/wiki/index.php/Kirk_Pepperdine)
