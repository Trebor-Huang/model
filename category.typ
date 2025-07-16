#import "common.typ": *
= 模型与范畴论 <ch:category>

为什么依值类型论模型的研究需要范畴论? 从模型的定义中可以看到，许多构造中需要反复验证有关代换的等式，例如 $(a, b)sigma = (a sigma, b sigma)$ 等等。在构造某个具体的模型时，往往需要验证数十条等式。这种情况称作#translate[自然性雪崩][naturality avalanche]，其中 “自然性” 是因为许多等式类似范畴论中自然变换满足的等式。

模型定义中的许多结构可以打包为范畴论中已有的事物，这样可以批量处理，简化证明。同时，范畴论也可以为类型论的模型提供一些直观，许多时候可以自动得到正确的构造。
由于代换本质是对类型论中变量的处理，可以说范畴论的语言是对变量结构的天然抽象。有些时候，甚至可以用范畴论的工具完全消除处理变量的部分。

另一方面，自 Lawvere 始有利用范畴结构研究逻辑的办法，称作范畴逻辑学。例如一阶逻辑中的量词 $exists$ 和 $forall$ 与伴随函子有密切的联系。这发展出了一套将各类范畴与逻辑相对应的理论。范畴的性质越好，能支撑的逻辑原理就越多。其中#translate[初等意象][elementary topos] 是性质优良的范畴，可以支撑构造主义高阶逻辑。既然类型论也有充当逻辑的功能，一个自然的问题就是这两者之间有什么关系。

== 模型的定义

=== 具族范畴与自然模型

#let Fam = math.sans("Fam")

比较范畴 (@def:category) 与模型 (@def:model) 的定义中代换的部分，呼之欲出的是语义语境与语义代换构成范畴 $cal(C)$。语义类型 $"Tp"(Gamma)$ 则为每个语义语境赋予一个集合，这看上去与函子 (@def:functor) 非常接近。不过需要注意的是，这里箭头的方向是相反的，即 $sigma : Delta -> Gamma$ 将 $Gamma$ 语境下的类型映射到 $Delta$ 下的类型。因此，$"Tp"$ 构成函子 $cal(C)^"op" -> Set$。我们将这种函子称作 $cal(C)$ 上的*预层*。

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
]<def:natural-model>
这个定义与@def:model 相比，简洁性不言而喻。不过，范畴语言的功力还不止于此。

考虑模型中单元素类型结构的定义。它要求在每个 $"Tp"(Gamma)$ 中选出元素 $Unit_Gamma$。类似地，空类型结构也要求选出元素 $Empty_Gamma$。从某个集合 $X$ 中选出元素，用范畴语言表述就是选定映射 $1 -> X$，其中 $1$ 是单元素集合，即集合范畴的终对象。

我们考虑预层 $1$ 使得 $1(Gamma)$ 均为单元素集合。这是预层范畴中的终对象。这样，预层间的映射 $1 -> "Tp"$ 就在每个 $"Tp"(Gamma)$ 中选出了元素。因此，我们应当要求有两个映射 $Unit, Empty : 1 -> "Tp"$，满足某些条件。此时，注意预层映射的自然性正好是代换需要满足的等式 $Unit_Gamma sigma = Unit_Delta$ 与 $Empty_Gamma sigma = Empty_Delta$。因此使用范畴语言时，代换等式往往会自然地打包进各种构造中。

单元素类型还需要满足每个 $"Tm"(Gamma, Unit_Gamma)$ 恰有一个元素。在自然模型中，$"Tm"$ 被改为合并了各种类型的元素集的预层。因此要表述这个条件，应该考虑
#eq($ U(Gamma) = {u mid(|) u in "Tm"(Gamma), typeof(u) = Unit_Gamma}. $)
这构成一个预层。用范畴语言的说法，就是拉回
#eq(diagram($
  U edge(->) edge("d", ->) & "Tm" edgeL("d", ->, typeof)\
  1 edgeR(->, Unit) & "Tp"
$))
我们要求 $U$ 是单元素预层，即 $U -> 1$ 是预层同构.（不过注意 $Empty$ 不能要求拉回是空预层，因为某些语境下空类型是有元素的，例如 $x : Empty tack x : Empty$.）在 #[@sec:natural-type-structure]中还会进一步介绍如何用范畴语言处理其他类型结构。

/*
在预层范畴中的一切范畴构造都会附带代换操作。这样，范畴论的语言可以自动处理例如 $(A times B) sigma = A sigma times B sigma$ 的等式。我们完整叙述自然模型中乘积类型的定义为例。
#definition[
  给定范畴 $cal(C)$ 上的自然模型，考虑预层
  #eq($ F(Gamma) = {(A, B, a, b) mid(|) vec(A in "Tp"(Gamma)\, B in "Tp"(Gamma),
  a in "Tm"(Gamma, A)\, b in "Tm"(Gamma, B),
  delim: #none)}. $)
  则 $F -> "Tp" times "Tp"$ 有显然的投影映射。假如有自然变换 $G : "Tp" times "Tp" -> "Tp"$，使得它与 $typeof$ 的拉回恰好是 $F$，那么就称其为此模型中的*乘积类型结构*。
]

(... we really need to introduce internal language first, or don't boast about substitutions yet)

(maybe we can wait until after LCCC, emphasize dialectics)

- start with binary product type
  - Note that substitution equations are absorbed naturally
- non-dependent function type
  - discuss relation to HOAS
- dependent sigma and pi type
- internal language of presheaves
- justify logical framework
*/

// Presheaf as discrete fibrations, formulation of representability (maybe we don't need this, or put in the appendix)

=== 展映射与概括范畴

在模型的定义中，不难看出形如 $(Gamma, A) -> Gamma$ 的代换是有特殊地位的。在范畴语义中，这些态射也有许多优秀的性质。我们将其称作#define[展映射][display map]。这个概念在类型论以外也有重要应用。

在集合模型中，任何映射都同构于某个 $(Gamma, A) -> Gamma$。给定映射 $f : Y -> X$，可以定义集合族 $A_x = f^(-1) {x}$，也就是 $A_x = {y mid(|) f(y) = x}$。这样，不交并 $product.co_(x in X) A_x$ 与 $Y$ 就有双射。因此，集合族与映射两个概念可以相互转换。在别的数学概念中，则不是所有映射都能与依值对象进行对应。例如对角映射 $X -> X^2$ 一般找不到对应的依值对象，除非这个模型中的相等类型满足外延性。因此，异常模型 (@sec:exception)、容器模型 (@sec:polynomial)、群胚模型 (@sec:groupoid) 等等都包含不是展映射的映射。从这个角度说，展映射可以理解为性质较好的投影映射。

研究展映射的一大动机是许多时候依值对象不好直接描述。例如光滑流形 $M$ 上的向量丛可以看作是 $M$ 上的 “依值向量空间”，为每个点 $x in M$ 赋予向量空间 $V_x$，使得 $x$ 在流形上运动时 $V_x$ 的变化是光滑的。但一个向量空间族何时光滑难以定义，因此在数学中往往转而考虑全空间 $E = product.co_(x in M) V_x$ 上的光滑结构与光滑映射 $E -> M$.
//#footnote[另一种办法是通过定义 “$Pi$ 类型”，即从 $x in M$ 到 $V_x$ 的光滑函数，间接描述向量族的光滑结构。]
同理，在数学中研究对象 $B$ 上的依值对象 $A_x$ 时，往往转而考虑全空间 $E$ 与映射 $p : E -> B$，间接研究依值对象。这种技术在代数几何中达到巅峰，以 Grothendieck 的#translate[相对视角][relative point of view] 为典型。例如希望表达每个 $A_x$ 都是紧空间，则说 $p$ 是紧合映射; 希望表达每个 $A_x$ 都是仿射空间，则说 $p$ 是仿射映射，等等。

另一方面，展映射仍然是范畴中的箭头，因此如果通过刻画展映射间接描述依值类型，就可以用上范畴论中的许多工具。这又与 Bénabou 发展的纤维化范畴论不谋而合。这一节，我们来考察另一种定义依值类型的模型的办法，称作概括范畴。

如果要以展映射为基础定义类型论的模型，就要考虑态射范畴 $cal(C)^->$，即对象是 $cal(C)$ 中的态射，态射是 $cal(C)$ 中的交换方的范畴。我们的第一个想法是选择其子范畴 $cal(E) arrow.hook cal(C)^->$。不过我们暂且先取任意的函子 $F : cal(E) -> cal(C)^->$，稍后再讨论将此函子限定为子范畴含入映射的情况。这样，$cal(E)$ 就是全体语义类型的范畴，而 $cal(C)$ 是全体语义语境的范畴。我们有函子 $cal(E) -> cal(C)^(->)$ 将 $Gamma$ 上的依值类型 $A$ 映射到对应的展映射 $(Gamma, A) -> Gamma$。可以发现，$F$ 复合上函子 $cod : cal(C)^(->) -> cal(C)$ 得到的 $cal(E) -> cal(C)$ 就应该将每个类型映射到它所处的语境。

接下来，我们需要将代换操作翻译到展映射的语言中。考虑集合族 $A_x$ 与对应的展映射 $p : (Gamma, A) -> Gamma$。假如有映射 $sigma : Delta -> Gamma$，那么 $Delta$ 上对应的集合族是 $(A sigma)_x = A_(sigma(x))$，因此有
#eq($ (Delta, A sigma) &= {(x, a) mid(|) x in Delta, a in A_(sigma(x))} \ &tilde.equiv {(x, y) mid(|) x in Delta, y in (Gamma, A), p(y) = sigma(x)} $)
其中最后一步是将集合族语言的 $A_(sigma(x))$ 转而利用展映射 $(Gamma, A) -> Gamma$ 表达得到的。最后这个集合在范畴论的语言中就是#translate[拉回][pullback]。换句话说，我们有拉回方
#eq(diagram($
  (Delta, A sigma) edge(->) edge("d", ->)
  & (Gamma, A) edge("d", ->) \
  Delta edge(->, sigma) & Gamma
$))
那么，我们大致上就要要求展映射 $(Gamma, A) -> Gamma$ 可以沿着任何代换 $Delta -> Gamma$ 作拉回，并且得到的新映射 $(Delta, A sigma) -> Delta$ 仍然是展映射。

范畴语言中，展映射是某个对象 $A in cal(E)$，有函子将其映射到 $(Gamma, A) -> Gamma$。因此我们的实际情况是
#eq(diagram($
  A sigma edge(->) edge("d", |->)
  & A edge("d", |->) \
  Delta edge(->, sigma) & Gamma
$))
其中上半部分在 $cal(E)$ 中，由上至下的映射是 $p = cod compose F : cal(E) -> cal(C)$。那么，我们只需先定义这种图表上的广义 “拉回”，再要求 $F$ 将每个这样的广义拉回映射到 $cal(C)^->$ 中真正的拉回方。

#definition[
考虑函子 $p : cal(E) -> cal(C)$。给定 $cal(E)$ 中的箭头 $f : B -> A$ 与其在 $p$ 下的像 $sigma = p(f) : Delta -> Gamma$。考虑任意如下图中的情况：
#eq(diagram({
  node((0,0), $B$, name: <B>)
  node((1,0), $A$, name: <A>)
  edgeR(<B>, "->", <A>, $f$)

  node((0,1), $Delta$, name: <Delta>)
  node((1,1), $Gamma$, name: <Gamma>)
  edgeR(<Delta>, "->", <Gamma>, $sigma$)

  edge(<B>, "|->", <Delta>)
  edge(<A>, "|->", <Gamma>)

  node((-1, -0.5), $X$, name: <X>)
  node((-1, 0.5), $p(X)$, name: <pX>)
  edge(<X>, "|->", <pX>)

  edgeR(<pX>, "->", <Delta>, $delta$)
  edge(<X>, "->", <A>, bend: 15deg, $h$)
  edge(<X>, "-->", <B>)
}))
其中 $p(h) = sigma compose delta$。如果存在唯一的箭头 $g : X -> B$，使得 $h = f compose g$，并且 $p(g) = delta$，就称 $f$ 与 $sigma$ 构成的方形是 *$p$-拉回方*，或称 $f$ 是#define[拉回态射][cartesian morphism]。假如对任意 $sigma : Delta -> Gamma$ 与 $A$ 满足 $p(A) = Gamma$，总存在 $p$-拉回方，就说函子 $p$ 是#define[纤维化][Grothendieck fibration]函子。
]
我们也说 $p$ 定义了 $cal(C)$ 上的#define[纤维范畴][fibered category]，并且有时单用 $cal(E)$ 指代这个纤维范畴。

#lemma[
  $cod : cal(C)^-> -> cal(C)$ 是纤维化函子当且仅当 $cal(C)$ 有全部拉回。
]
#proof[
代入纤维化的定义得到 $cod$-拉回方的图表是
#eq(diagram({
  node((0,0), $B$, name: <B>)
  node((1,0), $A$, name: <A>)
  edgeR(<B>, "->", <A>, $f$)

  node((0,1), $Delta$, name: <Delta>)
  node((1,1), $Gamma$, name: <Gamma>)
  edgeR(<Delta>, "->", <Gamma>, $sigma$)

  edge(<B>, "->", <Delta>)
  edge(<A>, "->", <Gamma>)

  node((-1, -0.5), $X$, name: <X>)
  node((-1, 0.5), $Xi$, name: <pX>)
  edge(<X>, "->", <pX>)

  edgeR(<pX>, "->", <Delta>, $delta$)
  edge(<X>, "->", <A>, bend: 15deg, $h$)
  edge(<X>, "-->", <B>)
}))
可以发现正好是拉回的图表，不过将 $X -> Delta$ 拆分为两步。不难看出 $cod$-拉回方与范畴 $cal(C)$ 的拉回方是等价的。
]

#definition[
  #define[概括范畴][comprehension category] 包含一个范畴 $cal(C)$ 表示语境，一个范畴 $cal(E)$ 表示类型，有函子 $F : cal(E) -> cal(C)^->$，使得与 $cod : cal(C)^-> -> cal(C)$ 复合之后可以得到纤维范畴 $cal(E) -> cal(C)$，并且 $F$ 将拉回态射映到拉回态射.#footnote[我们无需要求 $cal(C)$ 有全部拉回，即 $cod : cal(C)^-> -> cal(C)$ 不一定是纤维范畴。不过如果加上这个条件，$F$ 就是纤维化范畴之间的保持结构的映射。] 同时，$cal(C)$ 有终对象表示空语境。
]

- Discuss possible morphisms between types
  - Motivate equivalence between fibered categories and pseudofunctors
  - Making $cal(E) -> cal(C)$ discrete or making $F$ full both eliminates this extra information
    - Discrete fibrations behave much better
  - Possible use case as modeling subtypes or other kinds of coercions

=== 范畴的依值类型语言

(special type of comprehension categories: every arrow is a display map)

- $Sigma, Pi$ and extensional equality type structures on comprehension categories

- Examples of comprehension categories with Pi and Sigma types
  - LCCC
    - Note that it's very hard to define a CwF with an LCCC! More on this later
    - Application of type theoretic language (exponentiable arrows closed under pullback)
  - elementary toposes
    - presheaf categories
    - sheaves? maybe just over cantor space

#definition[
  假如有集合 $X$，配有两个集合 $X_0$、$X_1$ 与双射 $X tilde.equiv X_0 times X_1$，再配有集合 $X_00$、$X_01$、$X_10$、$X_11$ 与双射 $X_0 tilde.equiv X_00 times X_01$ 和 $X_1 tilde.equiv X_10 times X_11$，以此类推，就称此结构为 *Cantor 层*。Cantor 层之间的态射由一族映射 $f_b : X_b -> Y_b$ 组成，使得与配备的双射都交换。
]

(optional: sheafification universe)

=== 自然模型的类型结构 <sec:natural-type-structure>

Use internal language of presheaves to describe type structures

== 融贯问题

#define[融贯问题][coherence problem]

- Natural solution using coproducts of display maps
- Hofmann's solution
- Can be avoided using dedicated dependent structures

(also mention universes in sheaf topos)

== 语法的泛性质

What are morphisms between models?

mention sconing and gluing (dependent elimination)

will use to prove canonicity etc later down the line

== 模型的函子观点

(a category of algebras, model is a map from an algebra to a specified subcategory)

- diagram as functor from small categories
- algebraic structure as product preserving functor
- essentially algebraic structure as left exact functor
- model as functor preserving representable maps into presheaf categories
  - Compare with direct encoding, left exact functor into Set

上村太一 (罗马字：Taichi Uemura)

== 变量的结构

substructural models
