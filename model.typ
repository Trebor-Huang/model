#import "common.typ": *
= 模型与同伦论 <ch:homotopy-theory>


在 #[@sec:groupoid]的群胚模型中，我们提到应当有办法将类型解释为同伦意义下的空间。本章就来处理此事。

将类型解释为空间，最重要的意义是支撑#translate[泛等公理][univalence]。大致来说，两个类型的名字之间相等 $"Id"(cal(U), A, B)$，就能给出类型之间的等价 $"El"(A) tilde.eq "El"(B)$。泛等公理声称这反过来也成立：任何类型之间的等价都来自于它们名字之间的相等关系。这意味着在宇宙 $cal(U)$ 里，任何类型都_至多有一个名字_。由于 Russell 悖论等问题，不能要求任何类型都_恰好_有一个名字，因此泛等公理退而求其次。

从同伦论的视角，泛等公理使得类型论可以作为研究空间的#translate[综合][synthetic] 语言。即无需从 ZFC 集合开始构造出空间的概念，而是直接将其嵌入形式系统中，作为语言的一部分。这样可以给出同伦论中许多命题的优雅证明。平面几何的公理系统也是一种综合语言，直接在形式系统中描述点与线的关系，与解析几何利用实数表达几何概念相对.#footnote[不过，平面几何属于公理语言，即以一般的逻辑为基础，加入若干公理刻画数学对象的性质。综合语言不全是公理语言，例如同伦类型论或综合微分几何就不是公理语言。]

从数学基础的视角，泛等公理能够推出许多优良的性质。例如函数外延性、命题外延性等 Martin-Löf 类型论中独立的命题都是泛等公理的推论。另外还有#define[结构同一原理][structure identity principle]，大致说的是各种数学结构的 “同构” “同胚” 等同一性的定义，在泛等公理下都直接等价于道路类型。例如群同构的集合 $"Iso"(G, H)$ 与 $"Id"("Group", G, H)$ 有双射，等等。

接下来假设读者已经了解泛等公理以及同伦类型论的基础概念。@sec:univalence-equivalences 中也记录了泛等公理的一些零散知识。

== 相等类型与模型范畴

identity type and lifting

model structure and spaces (mention directed graph / groupoid model)

Sattler's model structure criteria?

== 单纯集模型

Воеводский (Voevodsky), paper by Chris Kapulkin and Peter LeFanu Lumsdaine @simplicial-model

Introduce fibrant types

== 立方模型

Explain why simplicial model is not constructive

BCH model

Internal language and cartesian models

Internal universes

(homotopy canonicity??)

problems with cubical models: they don't represent space
$==>$ equivariant cubical model etc

== 同伦类型论的内模型

idea of using HoTT/2LTT to synthetically define infinity-models

mention that Set model doesn't work inside HoTT because Set is not a hSet
