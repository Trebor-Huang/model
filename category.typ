#import "common.typ": *
= 模型与范畴论 <ch:category>

为什么依值类型论模型的研究需要范畴论? 从模型的定义中可以看到，许多构造中需要反复验证有关代换的等式，例如 $(a, b)sigma = (a sigma, b sigma)$ 等等。在构造某个具体的模型时，往往需要验证数十条等式。这种情况称作#translate[自然性雪崩][naturality avalanche]，其中 “自然性” 是因为许多等式类似范畴论中自然变换满足的等式。

模型定义中的许多结构可以打包为范畴论中已有的事物，这样可以批量处理，简化证明。同时，范畴论也可以为类型论的模型提供一些直观，许多时候可以自动得到正确的构造。
由于代换本质是对类型论中变量的处理，可以说范畴论的语言是对变量结构的天然抽象。有些时候，甚至可以用范畴论的工具完全消除处理变量的部分。

另一方面，自 Lawvere 始有利用范畴结构研究逻辑的办法，称作范畴逻辑学。例如一阶逻辑中的量词 $exists$ 和 $forall$ 与伴随函子有密切的联系。这发展出了一套将各类范畴与逻辑相对应的理论。范畴的性质越好，能支撑的逻辑原理就越多。其中#translate[初等意象][elementary topos] 是性质优良的范畴，可以支撑构造主义高阶逻辑。既然类型论也可以充当逻辑的功能，自然能提问研究这两者之间的关系。

== 模型的等价定义

=== 具族范畴与自然模型

#let Fam = math.sans("Fam")

比较范畴的定义 (@def:category) 与模型的定义 (@def:model) 中代换的部分，呼之欲出的是语义语境与语义代换构成范畴 $cal(C)$。语义类型 $"Tp"(Gamma)$ 则为每个语义语境赋予一个集合，这看上去与函子的定义 (@def:functor) 非常接近。不过需要注意的是，这里箭头的方向是相反的，即 $sigma : Delta -> Gamma$ 将 $Gamma$ 语境下的类型映射到 $Delta$ 下的类型。因此，$"Tp"$ 构成函子 $cal(C)^"op" -> Set$，也就是一个预层。

元素 $"Tm"(Gamma, A)$ 也有类似的代换操作，但是它还取决于类型 $A$，因此不能直接写作预层。这有多种解决办法。
- 可以将同一个语境下的所有元素合并在一起，得到 #eq($ "Tm"(Gamma) = product.co_(A in"Tp"(Gamma)) "Tm"(Gamma, A). $) 这在代换下就构成预层。有自然变换 $typeof : "Tm" -> "Tp"$ 取出元素的类型。这样三个对象 $("Tp", "Tm", typeof)$ 就完全记录了所需的信息。
- 可以将元素与类型合在一起，得到集合族。每个类型 $A in "Tp"(Gamma)$ 都附带一个集合 $"Tm"(Gamma, A)$，这就构成 $"Tp"(Gamma)$ 上的集合族。准确来说，定义范畴 $Fam$ 的对象是集合族，而 $A_(x in X)$ 到 $B_(y in Y)$ 的箭头由函数 $f : X -> Y$ 与 $F_x : A_x -> B_(f(x))$ 组成。这样，$"Tm"$ 与 $"Tp"$ 的数据就能组合为一个函子 $cal(C)^"op" -> Fam$。
- 可以让语境与类型合起来构成新的范畴。具体来说，定义范畴 $integral_cal(C)"Tp"$ 的对象为有序对 $(Gamma; A)$，临时用分号与语境扩展 $(Gamma, A)$ 示区分。从 $(Gamma; A)$ 到 $(Delta; B)$ 的箭头是代换 $sigma : Gamma -> Delta$，满足 $B sigma = A$。这样 $"Tm"$ 就可以视作 $\(integral_cal(C)"Tp"\)^"op" -> Set$ 的预层。
  注意有序对之间的箭头 $(Gamma; A) -> (Delta; B)$ 与语境扩展之间的代换 $(Gamma, A) -> (Delta, B)$ 不同，因为后者还包含一个元素 $Gamma, A tack B sigma$，但是我们还没定义元素 $"Tm"$，所以不能这么办。

第一种方案最简洁，只需要两个预层与它们之间的映射，不需要额外引入新的范畴，因此以下我们采用第一种方案。不过其余两个办法也大同小异。

对于语境扩展，按照前文将元素 $a in "Tm"(Gamma, A)$ 改写成满足 $typeof(a) = A$ 的元素 $a in "Tm"(Gamma)$。语境扩展需要有对象 $(Gamma, A)$，映射 $frak(p) : (Gamma, A) -> Gamma$ 与元素 $frak(q) in "Tm"((Gamma, A))$，满足 $typeof(frak(q)) = A frak(p)$。对于任何代换 $sigma : Delta -> Gamma$ 与元素 $t in "Tm"(Delta)$，满足 $typeof(t) = A sigma$，都有唯一的代换 $[sigma, t] : Delta -> (Gamma, A)$ 满足 $frak(p) compose [sigma, t] = sigma$ 与 $frak(q)[sigma, t] = t$。

读者或许可以发现此时定义与范畴论中的拉回非常相似。我们写出来以供参考：
#definition[
  在范畴 $cal(C)$ 中，给定映射 $f : X -> Z$ 与 $g : Y -> Z$，其*拉回*为对象 $P$ 配备映射 $p : P -> X$ 与 $q : P -> Y$，满足 $g compose p = f compose q$。假如有对象 $Q$ 与映射 $s ： Q -> X$ 和 $t : Q -> Y$ 满足 $g compose s = f compose t$，那么有唯一的映射 $[s, t] : Q -> P$ 满足 $p compose [s, t] = s$ 与 $q compose [s, t] = t$。
]
拉回的定义见左侧的交换图。如果我们做一些小小的修改，就可以套到语境扩展里。
#eq[
  #diagram($
    Q edge(->, "rrd", bend: #25deg, t) edge(->, "rdd", bend: #(-20deg), s) edgeM("-->", "rd", [s, t]) \
    & P edge(->, q) edgeL(->, "d", p) & Y edgeL(->, "d", f) \
    & X edgeR(->, g) & Z
  $)
  #h(2em) // TODO better alignment?
  #diagram($
    Delta edge("-O", "rrd", bend: #25deg, t) edge(->, "rdd", bend: #(-20deg), sigma) edgeM("-->", "rd", [sigma, t]) \
    & (Gamma, A) edge("-O", frak(q)) edgeL(->, "d", frak(p)) & "Tm" edgeL(->, "d", typeof) \
    & Gamma edgeR("-O", A) & "Tp"
  $)
]
这里，临时采用形如 $multimap$ 的箭头表示它是预层的元素，例如 $Gamma multimap "Tp"$ 表示 $"Tp"(Gamma)$ 的元素。与这样的元素 “复合” 可以用预层的函子性定义。我们不禁要问，是否有办法让这些箭头真正成为箭头? 答案是肯定的。

米田引理 (@lemma:yoneda) 告诉我们，元素 $Gamma multimap "Tp"$ 与箭头 $yo(Gamma) -> "Tp"$ 一一对应。换句话说，如果我们将所有语境都套上 $yo$，这张图表就变成预层范畴中的拉回图表。这样看来，语境扩展的定义就可以打包成拉回。具体来说，对于任何自然变换 $A : yo(Gamma) -> "Tp"$，它与 $typeof : "Tm" -> "Tp"$ 的拉回预层需要可表，也就是需要自然同构于某个对象 $(Gamma, A)$ 的米田嵌入 $yo(Gamma, A)$。
#definition[
  给定范畴 $cal(C)$ 上的预层 $X$ 与 $Y$，假如自然变换 $f : X -> Y$ 满足对于任何映射 $x : yo(A) -> X$，它与 $f$ 的拉回 $P$ 都可表，就说 $f$ 是预层之间的*可表映射*。
]
按照这个定义，语境扩展就可以表达成要求 $"Tm" -> "Tp"$ 是可表映射。这里有一些细节需要说明。
- 预层范畴中需要保证拉回的存在性。这不难。回忆预层是到集合范畴的函子，而它们的拉回就是逐点按照集合的拉回计算的。集合间两个函数 $f$ 与 $g$ 的拉回可以由公式 ${(x, y) mid(|) f(x) = g(y)}$ 定义。
- 语境扩展的泛性质中，图表左上角的 $Delta$ 只能取语境，而不能取任意预层，因此定义成预层范畴中的拉回就是更强的要求。不过，从米田引理可以推出这两个条件实际上是等价的。
- 我们还需要保证 $frak(p)$ 是个代换，但是米田引理保证两个可表预层之间的自然变换 $yo(Gamma, A) -> yo(Gamma)$ 与原范畴中的箭头 $(Gamma, A) -> Gamma$ 一一对应，因此不成问题。
- 严格来说，我们不应该要求拉回可表，而是要具体选出表示对象 $(Gamma, A)$ 与自然同构。以后的讨论有时为了方便会混淆这两者。

我们总结以上的讨论，可以将模型的概念用范畴语言重新表述。模型的这种形式称作#translate[自然模型][natural model]。这个定义由 Steve Awodey~@natural-model 提出，不过 Marcelo Fiore 也独立观察到此事。
#definition[
  依值类型论的*自然模型*包含一个范畴 $cal(C)$，其上两个预层 $"Tm"$ 与 $"Tp"$，还有二者之间的可表映射 $typeof : "Tm" -> "Tp"$。
]


Presheaf as discrete fibrations, formulation of representability

== 展映射与概括范畴

#define[展映射][display map]
#define[概括范畴][comprehension category]

LCCC and topos

== 融贯问题

#define[融贯问题][coherence problem]

- Natural solution using coproducts of display maps
- Hofmann's solution
- Can be avoided using dedicated dependent structures

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
