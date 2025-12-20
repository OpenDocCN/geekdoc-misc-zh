# 变体可以持有数据

> 原文：[`rust-exercises.com/100-exercises/05_ticket_v2/03_variants_with_data.html`](https://rust-exercises.com/100-exercises/05_ticket_v2/03_variants_with_data.html)

```rs
enum Status {
    ToDo,
    InProgress,
    Done,
}
```

我们的 `Status` 枚举通常被称为 **C 风格枚举**。

每个变体都是一个简单的标签，有点像命名常量。你可以在许多编程语言中找到这种类型的枚举，如 C、C++、Java、C#、Python 等。

Rust 枚举可以更进一步。我们可以 **将数据附加到每个变体**。

## 变体

假设我们想要存储目前正在处理票据的人的名字。

我们只有当票据处于进行中时才会有这些信息。对于待办票据或已完成票据，它不会在那里。我们可以通过将一个 `String` 字段附加到 `InProgress` 变体上来模拟这一点：

```rs
enum Status {
    ToDo,
    InProgress {
        assigned_to: String,
    },
    Done,
}
```

`InProgress` 现在是一个 **类似结构的变体**。

事实上，语法与我们在定义结构体时使用的语法相同——它只是作为变体“内联”在枚举中。

## 访问变体数据

如果我们尝试在一个 `Status` 实例上访问 `assigned_to`，

```rs
let status: Status = /* */;

// This won't compile
println!("Assigned to: {}", status.assigned_to);
```

编译器会阻止我们：

```rs
error[E0609]: no field `assigned_to` on type `Status`
 --> src/main.rs:5:40
  |
5 |     println!("Assigned to: {}", status.assigned_to);
  |                                        ^^^^^^^^^^^ unknown field 
```

`assigned_to` 是 **变体特定的**，它不是所有 `Status` 实例都可用。

要访问 `assigned_to`，我们需要使用 **模式匹配**：

```rs
match status {
    Status::InProgress { assigned_to } => {
        println!("Assigned to: {}", assigned_to);
    },
    Status::ToDo | Status::Done => {
        println!("ToDo or Done");
    }
}
```

## 绑定

在匹配模式 `Status::InProgress { assigned_to }` 中，`assigned_to` 是一个 **绑定**。

我们正在 **解构** `Status::InProgress` 变体并将 `assigned_to` 字段绑定到一个新变量，也命名为 `assigned_to`。

如果我们愿意，我们可以将字段绑定到不同的变量名：

```rs
match status {
    Status::InProgress { assigned_to: person } => {
        println!("Assigned to: {}", person);
    },
    Status::ToDo | Status::Done => {
        println!("ToDo or Done");
    }
}
```

## 练习

本节练习位于 `[05_ticket_v2/03_variants_with_data](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/05_ticket_v2/03_variants_with_data)`
