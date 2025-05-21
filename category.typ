#import "common.typ": *
= 模型与范畴论 <ch:category>

为什么依值类型论模型的研究需要范畴论? 从模型的定义中可以看到，许多构造中需要反复验证有关代换的等式，例如 $(a, b)sigma = (a sigma, b sigma)$ 等等。在构造某个具体的模型时，往往需要验证数十条等式。这种情况称作#translate[自然性雪崩][naturality avalanche]，其中 “自然性” 是因为许多等式类似范畴论中自然变换满足的等式。

模型定义中的许多结构可以打包为范畴论中已有的事物，这样可以批量处理，简化证明。同时，范畴论也可以为类型论的模型提供一些直观，许多时候可以自动得到正确的构造。
由于代换本质是对类型论中变量的处理，可以说范畴论的语言是对变量结构的天然抽象。有些时候，甚至可以用范畴论的工具完全消除处理变量的部分。

== 模型的等价定义

=== 具族范畴

=== 自然模型

== 展映射与概括范畴

(... discrete fibrations, equivalent to natural models)

#define[展映射][display map]
#define[概括范畴][comprehension category]

LCCC and topos

== 融贯问题

#define[融贯问题][coherence problem]

(also mention universes in sheaf topos)

== 语法的泛性质

mention sconing and gluing

== 模型的函子观点

- diagram as functor from small categories
- algebraic structure as product preserving functor
- essentially algebraic structure as left exact functor
- model as functor preserving representable maps into presheaf categories
  - Compare with direct encoding, left exact functor into Set

上村太一 (罗马字：Taichi Uemura)

== 变量的结构

substructural models
