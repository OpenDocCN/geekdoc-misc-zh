# 总结

> 原文：[`rust-exercises.com/100-exercises/04_traits/14_outro.html`](https://rust-exercises.com/100-exercises/04_traits/14_outro.html)

在本章中，我们介绍了相当多的不同特性——我们只是触及了表面！可能感觉你需要记住很多东西，但不用担心：当你编写 Rust 代码时，你经常会遇到这些特性，它们很快就会变得自然而然。

## 结束语

特性功能强大，但不要过度使用它们。

一些需要记住的指南：

+   如果一个函数总是用单一类型调用，不要使其泛化。这会在你的代码库中引入间接性，使其更难理解和维护。

+   如果你只有一个实现，不要创建一个特性。这是特性不需要的标志。

+   当有道理时，为你的类型实现标准特性（`Debug`、`PartialEq`等）。这将使你的类型更符合惯例，更容易处理，并解锁标准库和生态系统 crate 提供的大量功能。

+   如果你需要第三方 crate 中它们生态系统中解锁的功能，请实现这些特性。

+   小心仅为了在测试中使用模拟而使代码泛化。这种方法的维护成本可能很高，通常更好的做法是使用不同的测试策略。有关高保真测试的详细信息，请查看[测试大师班](https://github.com/mainmatter/rust-advanced-testing-workshop)。

## 测试你的知识

在继续之前，让我们再进行一次练习，以巩固我们所学的知识。这次你将得到最少的指导——只有练习描述和测试来引导你。

## 练习

本节练习位于[`04_traits/14_outro`](https://github.com/mainmatter/100-exercises-to-learn-rust/tree/main/exercises/04_traits/14_outro)
