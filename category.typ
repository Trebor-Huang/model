#import "common.typ": *
= 模型与范畴论 <ch:category>

为什么依值类型论模型的研究需要范畴论? 从模型的定义中可以看到，许多构造中需要反复验证有关代换的等式，例如 $(a, b)sigma = (a sigma, b sigma)$ 等等。在构造某个具体的模型时，往往需要验证数十条等式。这种情况称作#translate[自然性雪崩][naturality avalanche]，其中 “自然性” 是因为许多等式类似范畴论中自然变换满足的等式。

模型定义中的许多结构可以打包为范畴论中已有的事物，这样可以批量处理，简化证明。同时，范畴论也可以为类型论的模型提供一些直观，许多时候可以自动得到正确的构造。
由于代换本质是对类型论中变量的处理，可以说范畴论的语言是对变量结构的天然抽象。有些时候，甚至可以用范畴论的工具完全消除处理变量的部分。

另一方面，自 Lawvere 始有利用范畴结构研究逻辑的办法，称作范畴逻辑学。例如一阶逻辑中的量词 $exists$ 和 $forall$ 与伴随函子有密切的联系。这发展出了一套将各类范畴与逻辑相对应的理论。范畴的性质越好，能支撑的逻辑原理就越多。其中#translate[初等意象][elementary topos] 是性质优良的范畴，可以支撑构造主义高阶逻辑。既然类型论也有充当逻辑的功能，一个自然的问题就是这两者之间有什么关系。

== 具族范畴与自然模型

#let Fam = math.sans("Fam")

比较范畴 (@def:category) 与模型 (@def:model) 的定义中代换的部分，呼之欲出的是语义语境与语义代换构成范畴 $cal(C)$。语义类型 $"Tp"(Gamma)$ 则为每个语义语境赋予一个集合，这看上去与函子 (@def:functor) 非常接近。不过需要注意的是，这里箭头的方向是相反的，即 $sigma : Delta -> Gamma$ 将 $Gamma$ 语境下的类型映射到 $Delta$ 下的类型。因此，$"Tp"$ 构成函子 $cal(C)^"op" -> Set$。我们将这种函子称作 $cal(C)$ 上的*预层*。

元素 $"Tm"(Gamma, A)$ 也有类似的代换操作，但是它还取决于类型 $A$，因此不能直接写作预层。这有多种解决办法。
- 可以将同一个语境下的所有元素合并在一起，得到 #eq($ "Tm"(Gamma) = product.co_(A in"Tp"(Gamma)) "Tm"(Gamma, A). $) 这在代换下就构成预层。有自然变换 $typeof : "Tm" -> "Tp"$ 取出元素的类型。这样三个对象 $("Tp", "Tm", typeof)$ 就完全记录了所需的信息。
- 可以将元素与类型合在一起，得到集合族。每个类型 $A in "Tp"(Gamma)$ 都附带一个集合 $"Tm"(Gamma, A)$，这就构成 $"Tp"(Gamma)$ 上的集合族。准确来说，定义范畴 $Fam$ 的对象是集合族，而 $A_(x in X)$ 到 $B_(y in Y)$ 的箭头由函数 $f : X -> Y$ 与 $F_x : A_x -> B_(f(x))$ 组成。这样，$"Tm"$ 与 $"Tp"$ 的数据就能组合为一个函子 $cal(C)^"op" -> Fam$。
- 可以让语境与类型合起来构成新的范畴。具体来说，定义范畴 $integral_cal(C)"Tp"$ 的对象为有序对 $(Gamma; A)$，临时用分号以示区分。从 $(Gamma; A)$ 到 $(Delta; B)$ 的箭头是代换 $sigma : Gamma -> Delta$，满足 $B sigma = A$。这样 $"Tm"$ 就可以视作 $\(integral_cal(C)"Tp"\)^"op" -> Set$ 的预层。
  注意有序对之间的箭头 $(Gamma; A) -> (Delta; B)$ 与语境扩展之间的代换 $(Gamma dot A) -> (Delta dot B)$ 不同，因为后者还包含一个元素 $Gamma, A tack B sigma$，但是我们还没定义元素 $"Tm"$，所以不能这么办。

第一种方案最简洁，只需要两个预层与它们之间的映射，不需要额外引入新的范畴，因此以下我们采用第一种方案。不过其余两个办法也大同小异。

对于语境扩展，按照前文将元素 $a in "Tm"(Gamma, A)$ 改写成满足 $typeof(a) = A$ 的元素 $a in "Tm"(Gamma)$。语境扩展需要有对象 $Gamma dot A$，映射 $frak(p) : Gamma dot A -> Gamma$ 与元素 $frak(q) in "Tm"(Gamma dot A)$，满足 $typeof(frak(q)) = A frak(p)$。对于任何代换 $sigma : Delta -> Gamma$ 与元素 $t in "Tm"(Delta)$，满足 $typeof(t) = A sigma$，都有唯一的代换 $[sigma, t] : Delta -> (Gamma dot A)$ 满足 $frak(p) compose [sigma, t] = sigma$ 与 $frak(q)[sigma, t] = t$。

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
    & Gamma dot A edge("-O", frak(q)) edgeL(->, "d", frak(p)) & "Tm" edgeL(->, "d", typeof) \
    & Gamma edgeR("-O", A) & "Tp"
  $)
]
这里，临时采用形如 $multimap$ 的箭头表示它是预层的元素，例如 $Gamma multimap "Tp"$ 表示 $"Tp"(Gamma)$ 的元素。与这样的元素 “复合” 可以用预层的函子性定义。我们不禁要问，是否有办法让这些箭头真正成为箭头? 答案是肯定的。

米田引理 (@lemma:yoneda) 告诉我们，元素 $Gamma multimap "Tp"$ 与箭头 $yo(Gamma) -> "Tp"$ 一一对应。换句话说，如果我们将所有语境都套上 $yo$，这张图表就变成预层范畴中的拉回图表。这样看来，语境扩展的定义就可以打包成拉回。具体来说，对于任何自然变换 $A : yo(Gamma) -> "Tp"$，它与 $typeof : "Tm" -> "Tp"$ 的拉回预层需要可表，也就是需要自然同构于某个对象 $(Gamma dot A)$ 的米田嵌入 $yo(Gamma dot A)$。
#definition[
  给定范畴 $cal(C)$ 上的预层 $X$ 与 $Y$，假如自然变换 $f : X -> Y$ 满足对于任何映射 $x : yo(A) -> Y$，它与 $f$ 的拉回 $P$ 都可表，就说 $f$ 是预层之间的*可表映射*。
]
按照这个定义，语境扩展就可以表达成要求 $"Tm" -> "Tp"$ 是可表映射。这里有一些细节需要说明。
- 预层范畴中需要保证拉回的存在性。这不难。回忆预层是到集合范畴的函子，而它们的拉回就是逐点按照集合的拉回计算的。集合间两个函数 $f$ 与 $g$ 的拉回可以由公式 ${(x, y) mid(|) f(x) = g(y)}$ 定义。
- 语境扩展的泛性质中，图表左上角的 $Delta$ 只能取语境，而不能取任意预层，因此定义成预层范畴中的拉回就是更强的要求。不过，从米田引理可以推出这两个条件实际上是等价的。
- 我们还需要保证 $frak(p)$ 是个代换，但是米田引理保证两个可表预层之间的自然变换 $yo(Gamma dot A) -> yo(Gamma)$ 与原范畴中的箭头 $(Gamma dot A) -> Gamma$ 一一对应，因此不成问题。
- 严格来说，我们不应该要求拉回可表，而是要具体选出表示对象 $Gamma dot A$ 与自然同构。以后的讨论有时为了方便会混淆这两者。

我们总结以上的讨论，可以将模型的概念用范畴语言重新表述。模型的这种形式称作#translate[自然模型][natural model]。这个定义由 Steve Awodey~@natural-model 提出，不过 Marcelo Fiore 也独立观察到此事。
#definition[
  依值类型论的*自然模型*包含一个范畴 $cal(C)$，其上两个预层 $"Tm"$ 与 $"Tp"$，还有二者之间的可表映射 $typeof : "Tm" -> "Tp"$。
]<def:natural-model>
这个定义与@def:model 相比，简洁性不言而喻。不过，范畴语言的功力还不止于此。例如对于每个类型构造子，都有相对的代换规则。无参数类型构造子有 $Bool sigma = Bool$ 与 $Unit sigma = Unit$，而如不交并类型则有 $(A + B) sigma = A sigma + B sigma$ 等。在范畴论的语言中，可以把类型构造子的参数打包为预层。如二元类型构造子的参数预层是 $X(Gamma) = {(A, B) mid(|) A, B in "Tp"(Gamma)}$，零元的参数预层则是 $X(Gamma) = 1$，均为单元素集。这也可以处理依值类型构造子，如 $Pi$ 类型的参数是 $X(Gamma) = {(A, B) mid(|) A in "Tp"(Gamma), B in "Tp"(Gamma, A)}$。此时，如果要求模型中给出预层之间的自然变换 $X -> "Tp"$，就相当于给出类型构造子，而其自然性就对应这些代换的等式。

有了类型构造子，元素的构造子也可同样操作，将参数写成预层 $Y$。例如对于二元乘积类型，$X(Gamma) = {(A, B) mid(|) A, B in "Tp"(Gamma)}$，而 $Y(Gamma) = {(A,B,a,b) mid(|) a in "Tm"(Gamma, A), b in "Tm"(Gamma, B)}$ (注意这里一并写出了它的类型参数)。这样类型构造子是自然变换 $X -> "Ty"$，而元素构造子是自然变换 $Y -> "Tm"$。同时还有以下交换方
#eq(diagram($
  Y edge(->) edge("d", ->) & "Tm" edgeL("d", ->, typeof)\
  X edgeR(->) & "Tp"
$))
它要求每个构造子都有正确的类型。对于不交并类型，则有 $Y(Gamma) = {(A, B, a) mid(|) a in "Tm"(Gamma, A)} union {(A, B, b) mid(|) b in "Tm"(Gamma, B)}$。这样我们就将类型构造子、元素构造子以及其在代换下的等式全部打包为范畴语言中的一个交换方。

对于乘积类型而言，其消去子与 $beta$、$eta$ 规则还可以更进一步地用范畴语言叙述：只需要求这个交换方为拉回即可。这是因为类型构造子 $X -> "Tp"$ 与 $typeof : "Tm" -> "Tp"$ 的拉回预层是 $Y'(Gamma) = {(A, B, p) mid(|) p in "Tm"(Gamma, A times B)}$，恰好编码了这个类型的全体元素。乘积类型的消去子与 $beta$、$eta$ 等式说的是一切元素 $p$ 都可以唯一地表示为有序对 $p = (a, b)$。因此在范畴语言下说的就是 $Y$ 与 $Y'$ 同构，即 $Y$ 本身是拉回。

更一般而言，对于带 $eta$ 规则的#translate[负极类型][negative type] 而言，我们可以完全描述每个类型的全体元素集合，如函数类型对应 $Y(Gamma) = {(A, B, f) mid(|) f in "Tm"(Gamma dot A, B)}$，等等。因此构造子、消去子、$beta$ 与 $eta$ 等式就可以直接表述为有对应的拉回方。

不过，以上说法还有两个不完美之处。一是 $X$ 与 $Y$ 两个预层还需要手工定义，因此还需要确认它们的确构成预层。二是没有介绍#translate[正极类型][positive type] 对应的消去子如何表述。这一点暂时留给读者思考。在 #[@sec:natural-type-structure]中还会进一步介绍如何用范畴语言处理类型结构。

== 基于展映射的模型的定义

在模型的定义中，不难看出形如 $(Gamma dot A) -> Gamma$ 的代换是有特殊地位的。在范畴语义中，这些态射也有许多优秀的性质。我们将其称作#define[展映射][display map]。这个概念在类型论以外也有重要应用。

在集合模型中，任何映射都同构于某个 $(Gamma dot A) -> Gamma$。给定映射 $f : Y -> X$，可以定义集合族 $A_x = f^(-1) {x}$，也就是 $A_x = {y mid(|) f(y) = x}$。这样，不交并 $product.co_(x in X) A_x$ 与 $Y$ 就有双射。因此，集合族与映射两个概念可以相互转换。在别的数学概念中，则不是所有映射都能与依值对象进行对应。例如对角映射 $X -> X^2$ 一般找不到对应的依值对象，除非这个模型中的相等类型满足外延性。因此，异常模型 (@sec:exception)、容器模型 (@sec:polynomial)、群胚模型 (@sec:groupoid) 等等都包含不是展映射的映射。从这个角度说，展映射可以理解为性质较好的投影映射。

研究展映射的一大动机是许多时候依值对象不好直接描述。例如光滑流形 $M$ 上的向量丛可以看作是 $M$ 上的 “依值向量空间”，为每个点 $x in M$ 赋予向量空间 $V_x$，使得 $x$ 在流形上运动时 $V_x$ 的变化是光滑的。但一个向量空间族何时光滑难以定义，因此在数学中往往转而考虑全空间 $E = product.co_(x in M) V_x$ 上的光滑结构与光滑映射 $E -> M$.
//#footnote[另一种办法是通过定义 “$Pi$ 类型”，即从 $x in M$ 到 $V_x$ 的光滑函数，间接描述向量族的光滑结构。]
同理，在数学中研究对象 $B$ 上的依值对象 $A_x$ 时，往往转而考虑全空间 $E$ 与映射 $p : E -> B$，间接研究依值对象。这种技术在代数几何中达到巅峰，以 Grothendieck 的#translate[相对视角][relative point of view] 为典型。例如希望表达每个 $A_x$ 都是紧空间，则说 $p$ 是紧合映射; 希望表达每个 $A_x$ 都是仿射空间，则说 $p$ 是仿射映射，等等。
另一方面，展映射仍然是范畴中的箭头，因此如果通过刻画展映射间接描述依值类型，就可以用上范畴论中的许多工具。这又与 Bénabou 发展的纤维化范畴论不谋而合。

本节中我们介绍从展映射视角定义的几种类型论模型的概念，并讨论它们之间的联系。从这个视角定义的模型与类型论的关联没有那么直接，但是能更好地与范畴论和同伦论中的概念联系起来。在 #[@sec:coherence-problem]中我们会讨论这些模型与具族范畴的转化关系。

=== 局部积闭范畴的语言

考虑集合族 $A_x$ 与对应的展映射 $p : (Gamma dot A) -> Gamma$。假如有映射 $sigma : Delta -> Gamma$，那么 $Delta$ 上对应的集合族是 $(A sigma)_x = A_(sigma(x))$，因此有
#eq($ Delta dot A sigma &= {(x, a) mid(|) x in Delta, a in A_(sigma(x))} \ &tilde.equiv {(x, y) mid(|) x in Delta, y in Gamma dot A, p(y) = sigma(x)} $)
其中最后一步是将集合族语言的 $A_(sigma(x))$ 转而利用展映射 $p : (Gamma dot A) -> Gamma$ 表达得到的。最后这个集合在范畴论的语言中就是#translate[拉回][pullback]。换句话说，我们有拉回方
#eq(diagram($
  Delta dot A sigma edge(->) edge("d", ->)
  pullback("dr")
  & Gamma dot A edge("d", ->) \
  Delta edge(->, sigma) & Gamma
$))
那么，我们大致上就要要求展映射 $(Gamma dot A) -> Gamma$ 可以沿着任何代换 $Delta -> Gamma$ 作拉回，并且得到的新映射 $(Delta dot A sigma) -> Delta$ 仍然是展映射。

对于 $Sigma$ 类型，我们同样先考虑集合范畴中的直观。假如有展映射 $Gamma dot A -> Gamma$ 与 $(Gamma dot A) dot B -> Gamma dot A$，分别表示两个集合族 $A_(x in Gamma)$ 与 $B_(x in Gamma dot A)$，那么如果想取 $Sigma$ 类型 $Sigma A B$，那么对应的映射应当恰好是复合映射 $(Gamma dot A) dot B -> Gamma$，如@fig:sigma-compcat 所示。这样看，$Sigma$ 类型在展映射的语言中就对应映射的复合.#footnote[
读者或许注意到，按照这个论证，$Sigma$ 类型应该只要求某个同构于复合映射的映射是展映射，而不要求复合映射本身就是展映射。我们暂时遵循范畴论的观点，不区分同构的事物，即认为同构于展映射的映射也必须是展映射。
]
#numbered-figure(caption: [$Sigma$ 类型示意], canvas({
  import draw: *
  rect((-1,0), (1,1), stroke: 0.5pt)
  content((1.5,0.5), $Gamma$)
  content((-0.5,0.4), $attach(bullet, bl:x)$)
  content((0.5,0.5), $bullet_y$)
  rect((-2,1.7), (0,2.7), stroke: 0.5pt)
  line((-1,1.7), (-0.5,0.6), stroke:0.5pt)
  content((-1.4,2.3), $bullet$)
  content((-0.6,2.2), $bullet$)
  content((0.45,2.25), $bullet$)
  content((1,2.1), $bullet$)
  content((1.6,2.3), $bullet$)
  rect((0,1.7), (2,2.7), stroke: 0.5pt)
  line((1,1.7), (0.5,0.7), stroke:0.5pt)
  content((2.5,2.2), $A_y$)
  content((-2.5,2.2), $A_x$)
  rect((-2.5,3.5), (2.5, 4.7), stroke: 0.5pt)
  line((-1.5, 3.5), (-1.5, 4.7), stroke: 0.5pt)
  line((0.5, 3.5), (0.5, 4.7), stroke: 0.5pt)
  line((1.5, 3.5), (1.5, 4.7), stroke: 0.5pt)

  line((-1.4,2.3), (-2,3.5), stroke:0.5pt)
  line((-0.6,2.2), (-1,3.5), stroke:0.5pt)
  line((0.45,2.25), (0,3.5), stroke:0.5pt)
  line((1,2.1), (1,3.5), stroke:0.5pt)
  line((1.6,2.3), (2,3.5), stroke:0.5pt)
  for i in range(5) {
    content((i - 2,4.1), $B_#(i+1)$)
  }

  rect((-2.5,3.5), (-0.5, 4.7), stroke: red+2pt)
  content((-1.5, 5.1), text(fill: red.darken(50%), $(Sigma A B)_x$))
})) <fig:sigma-compcat>

接下来，我们考察外延类型论中的相等类型。假设有语境 $Gamma$ 中的类型 $A$，对应展映射 $frak(p) : (Gamma dot A) -> Gamma$。相等类型依赖于两个变量 $(Gamma, x : A, y : A)$，因此这里第二个变量的类型实际上需要经过代换 $A frak(p)$ 表示它不使用第一个变量 $x : A$。前面提到代换在展映射的语言下是拉回，因此有
#eq(diagram($
  Gamma dot A dot A frak(p) edge(->) edge("d", ->)
  pullback("dr")
  & Gamma dot A edge("d", ->) \
  Gamma dot A edge(->, frak(p)) & Gamma
$))
在集合语言中，这对应集合 ${(x, a_1, a_2) mid(|) a_1, a_2 in A_x}$。

在集合模型中，外延相等类型 $"Id"(x, y)$ 对应集合族
#eq($
  {star mid(|) x = y} =
  cases(
    {star} quad & x = y,
    varnothing & x != y
  )
$)
其中等号均为集合论意义的等号。换成展映射的语言，就是从 ${(x, a_1, a_2) mid(|) a_1 = a_2 in A_x}$ 到 ${(x, a_1, a_2) mid(|) a_1, a_2 in A_x}$ 的含入映射。注意到前者实际上就同构于 $Gamma dot A$。因此，外延相等类型对应要求 $Gamma dot A -> (Gamma dot A) dot A frak(p)$ 这个对角映射是展映射。

将 $(Gamma dot A)$ 记作 $Delta$，则 $(Gamma dot A) dot A frak(p)$ 是拉回 $Delta times_Gamma Delta$。在代数几何中，有许多条件是关于对角映射 $Delta -> Delta times_Gamma Delta$ 的，例如某映射拟分离当且仅当其对角映射拟紧，某映射分离当且仅当对角映射是闭嵌入，等等。这些条件可以看作是对某类型的相等类型作限制。

从纯语法的视角，我们已经知道类型论中添加了外延相等类型会对理论的性质产生极大影响。从语义的视角也不例外。以下我们假设范畴中每个对象 $Gamma$ 到终对象的映射都是展映射 —— 这是比较合理的要求，因为每个对象应当表示某个语境 $(x_1 : A_1, dots, x_n : A_n)$，因此是从空语境 $1$ 开始逐步搭建的。如果取一个大 $Sigma$ 类型，就能将 $Gamma$ 表示为空语境中的类型，即展映射 $Gamma -> 1$。
在这个假设下，一旦有了外延相等类型，可以证明_所有的映射_都必须成为展映射。具体如图所示：
#eq(diagram({
  node((1, 0), [$Delta$])
  node((1, -1), [$Delta times Gamma$])
  node((1, -2), [$Gamma$])
  pullback("dr")
  node((2, -1), [$Delta^3$])
  node((2, -2), [$Delta^2$])
  edge((1, -1), (1, 0), "->")
  edge((1, -2), (1, -1), "->")
  edgeL((2, -2), (2, -1), [$[id, delta]$], "->")
  edgeR((1, -1), (2, -1), [$[delta, f]$], "->")
  edge((1, -2), (2, -2), "->")
}))
假设有映射 $f : Gamma -> Delta$。图中 $Delta times Gamma -> Delta$ 的投影映射是展映射，因为它是 $Gamma -> 1$ 沿着 $Delta -> 1$ 的拉回。其次，对角映射 $delta : Delta -> Delta^2$ 也是展映射，因为它代表了展映射 $Delta -> 1$ 上的相等类型。因此，图中 $Delta^2 -> Delta^3$ 也是展映射，从而沿着 $[delta, f]$ 拉回得到的也是展映射。最后左侧两个展映射复合也是展映射。通过追图可以得知这个复合恰好是 $f$，换句话说 $f$ 必须是展映射。

从语法的视角，这是因为某个映射 $f : A -> B$ 可以利用 $Sigma$ 类型与外延相等写成 $B$ 上的依值类型 $P(x) = (a : A) times (f(a) = x)$。而此依值类型对应的展映射 $(x : B, y : P(x)) -> B$ 与 $A -> B$ 是同构的。注意到这里的同构是范畴意义上的同构，因此用到的相等关系是判值相等。如果将 $P$ 中的相等类型改为一般的内涵相等类型，则同构不成立。

以上讨论可以用范畴论的观点进一步阐述。我们先考虑简单情况，假设所有映射都是展映射。某个语境 $Gamma$ 下的所有类型就是陪域为 $Gamma$ 的映射。用范畴论的语言，这就是#translate[俯范畴][overcategory] $cal(C)\/Gamma$。在俯范畴中的操作与原范畴中几乎相同，唯一的区别是一切都可以依赖 $Gamma$ 中的变量。这个范畴中从 $(Gamma dot A) -> Gamma$ 到 $(Gamma dot B) -> Gamma$ 的映射对应一个表达式 $Gamma, x:A tack t : B$，直观上也可以视作在 $Gamma$ 中的函数 $A -> B$。

给定代换 $sigma : Delta -> Gamma$，我们可以对所有类型 $(Gamma dot B) -> Gamma$ 作拉回。这构成函子
#eq($ sigma^* : cal(C)\/Gamma -> cal(C)\/Delta. $)
代换可以将依赖 $Gamma$ 的一切构造转化为依赖 $Delta$ 的构造，符合我们的期望。另一方面，如果将 $sigma$ 视作一个依值类型 $(Gamma dot A) -> Gamma$，则 $Sigma$ 类型是一个反方向的函子
#eq($ sigma_! : cal(C)\/(Gamma dot A) -> cal(C)\/Gamma. $)
也就是消耗语境中的一个变量的操作。

在范畴论中，一旦遇到两个相反方向的函子，就应当立刻观察它们是否伴随。根据 $Sigma$ 类型的性质，在语境 $Gamma$ 下从 $Sigma A B$ 到 $X$ 的映射应当等同于语境 $(Gamma, x : A)$ 下从 $B(x)$ 到 $X$ 的映射，这里 $X$ 不依赖变量 $x : A$，因此需要经过弱化代换 $X sigma$。换句话说，存在双射
#eq($ hom_(cal(C)\/Gamma) (sigma_! B, X) tilde.equiv hom_(cal(C)\/(Gamma dot A)) (B, sigma^* X). $)
其中 $sigma_! B$ 如上所述就是 $Sigma A B$ 的另一种写法。可以验证这个双射也是自然的，因此有伴随函子 $sigma_! tack.l sigma^*$。

令人惊讶的是，$Pi$ 类型在这个框架下也有非常优雅的表述。注意 $Pi$ 类型和 $Sigma$ 类型一样，都应当是消除一个变量的函子 $cal(C)\/(Gamma dot A) -> cal(C)\/Gamma$。而在语境 $Gamma$ 中要构造一族函数，即构造从 $X$ 到 $Pi A B$ 的映射，只需要在语境 $(Gamma, x:A)$ 中给出从 $X$ 到 $B(x)$ 的映射，即依赖于 $x$ 的一族表达式。我们在 #[@sec:model-definition]中已经看到类似的说法，即 $"Tm"(Gamma, Pi A B) tilde.equiv "Tm"(Gamma dot A, B)$。这里我们有
#eq($ hom_(cal(C)\/Gamma) (X, sigma_* B) tilde.equiv hom_(cal(C)\/(Gamma dot A)) (sigma^* X, B). $)
其中 $sigma_*$ 是 $Pi$ 类型对应的函子。因此有伴随函子 $sigma^* tack.l sigma_*$。这就说明 $Sigma$、代换、$Pi$ 三者构成伴随三函子
#eq($ sigma_! tack.l sigma^* tack.l sigma_*. $)
这就是 Seely~@seely-lccc 的观察：如果某个范畴具有这样三个伴随函子，则它可以作为带有 $Pi$ 与 $Sigma$ 类型的外延类型论的模型。事实上这个结论是有问题的，我们会在 #[@sec:coherence-problem]进一步讨论。在此之前，我们用图表的语言具体写出 $Pi$ 类型对应的泛性质。

#definition[
给定映射 $f : Y -> X$ 与 $g : Z -> Y$，其#define[前推][pushforward] 是对象 $Pi_f Z$ 与箭头 $f_* g : Pi_f Z -> X$，满足以下性质：
#eq(diagram(spacing: (1em, 3em), {
  node((1, -1), [$W$])
  node((2, 0), [$Pi_f Z$])
  node((1, 1), [$X$])
  node((0, 1), [$Y$])
  node((0, -1), [$Y times_X W$])
  pullback("dr")
  node((0, 0), [$Z$])
  edge((1, -1), (2, 0), "-->")
  edgeL((2, 0), (1, 1), "->", $f_* g$)
  edgeR((1, -1), (1, 1), "->", $h$)
  edge((0, 1), (1, 1), "->", $f$)
  edge((0, -1), (1, -1), "->")
  edge((0, 0), (0, 1), "->", $g$)
  edge((0, -1), (0, 0), "->", $u$)
}))
对于任何箭头 $h : W -> X$ 与 $u : Y times_X W -> Z$，若 $u$ 与 $g$ 的复合等于投影映射 $Y times_X W -> Y$，则存在唯一的箭头 $W -> Pi_f Z$，使得其与 $f_* g$ 复合等于 $h : W -> X$。
]
改写为类型论的记号如下：
#eq(diagram(spacing: (1em, 3em), {
  node((1, -1), [$Delta$])
  node((2, 0), [$Gamma dot Pi A B$])
  node((1, 1), [$Gamma$])
  node((0, 1), [$Gamma dot A$])
  node((0, -1), [$Delta dot A sigma$])
  pullback("dr")
  node((0, 0), [$Gamma dot A dot B$])
  edge((1, -1), (2, 0), "-->")
  edge((2, 0), (1, 1), "->")
  edgeL((1, -1), (1, 1), "->", $tau$)
  edge((0, 1), (1, 1), "->", $sigma$)
  edge((0, -1), (1, -1), "->")
  edge((0, 0), (0, 1), "->")
  edge((0, -1), (0, 0), "->", $u$)
}))
换句话说，要给出代换 $Delta -> (Gamma dot Pi A B)$，只需要给出 $tau : Delta -> Gamma$ 与一个依赖于 $A$ 的表达式 $u$。读者可以尝试证明前推与拉回的确构成伴随函子 $sigma^* tack.l sigma_*$。此事大体就是展开定义。

#definition[
  某个范畴是#define[局部积闭范畴][locally cartesian closed category]，当且仅当对任何映射 $sigma : Gamma -> Delta$，复合函子 $sigma_! : cal(C)\/Gamma -> cal(C)\/Delta$ 都处在三伴随 $sigma_! tack.l sigma^* tack.l sigma_*$ 中。
]

这样的三伴随在一阶逻辑中也有类似的表述。一阶逻辑中我们不讨论依值类型，而考虑谓词 $P(x,y,z)$，对应子集 $U arrow.hook X times Y times Z$。这里的 $(x,y,z)$ 类似类型论中的语境。这样，每个语境 $Gamma$ 中的谓词就对应其子集的偏序 $"Sub"(Gamma)$。每个代换对应映射 $sigma^* : "Sub"(Delta) -> "Sub"(Gamma)$。如果考虑投影映射 $sigma : Gamma times X -> Gamma$，则有三伴随 #eq($ exists tack.l sigma^* tack.l forall $)
其中 $exists U = {a in Gamma mid(|) exists x in X bind (a,x) in U}$，类似地 $forall U = {a in Gamma mid(|) forall x in X bind (a,x) in U}$。这种情形抽象得来的结构称作一阶逻辑的#translate[超理论][hyperdoctrine]。

常见的局部积闭范畴的例子有集合范畴 $Set$。#[@ch:examples]中提到的不少支持外延相等类型的例子也都是局部积闭范畴。所有的#translate[意象][topos] 都是局部积闭范畴，而范畴论的研究中已经发展出一套丰富的描述和构造意象的理论。因此借助局部积闭范畴就可以得到许多类型论的模型。

#definition[
  假如有集合 $X$，配有两个集合 $X_0$、$X_1$ 与双射 $X tilde.equiv X_0 times X_1$，再配有集合 $X_00$、$X_01$、$X_10$、$X_11$ 与双射 $X_0 tilde.equiv X_00 times X_01$ 和 $X_1 tilde.equiv X_10 times X_11$，以此类推，就称此结构为 *Cantor 层*。Cantor 层之间的态射由一族映射 $f_b : X_b -> Y_b$ 组成，使得与配备的双射都交换。
]

这个范畴其实是 Cantor 空间#footnote[实数中考虑三进制展开只有 0 与 2 的小数，其构成 $[0,1]$ 的子空间称作 *Cantor 空间*。]上的层范畴 $sans("Sh")("Cantor")$，是意象。因此我们立刻得到这是局部积闭范畴。事实上它可以作为 #[@sec:markov-principle]提到的 Марков 原理的反模型。



(...) @clans-and-tribes

=== 概括范畴

这一节，我们来考察并非所有映射都是展映射的情况。

如果要以展映射为基础定义类型论的模型，就要考虑态射范畴 $cal(C)^->$，即对象是 $cal(C)$ 中的态射，态射是 $cal(C)$ 中的交换方的范畴。我们的第一个想法是选择其子范畴 $cal(E) arrow.hook cal(C)^->$。不过我们可暂且先取任意的函子 $F : cal(E) -> cal(C)^->$，有需要时再讨论将此函子限定为子范畴含入映射的情况。这样，$cal(E)$ 就是全体语义类型的范畴，而 $cal(C)$ 是全体语义语境的范畴。我们有函子 $cal(E) -> cal(C)^(->)$ 将 $Gamma$ 上的依值类型 $A$ 映射到对应的展映射 $(Gamma dot A) -> Gamma$。可以发现，$F$ 复合上函子 $cod : cal(C)^(->) -> cal(C)$ 得到的 $cal(E) -> cal(C)$ 就应该将每个类型映射到它所处的语境。

前面我们大致提到，代换在展映射的语言中应当解释为拉回。
范畴语言中是某个对象 $A in cal(E)$，用函子 $F$ 将其映射到 “真正的展映射” $(Gamma dot A) -> Gamma$。因此我们的实际情况是
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

注意我们尚未说明概括范畴是合理的类型论模型。探究此事，只需要将概括范畴与自然模型相比。但这就可以发现实际上概括范畴比自然模型多出了额外的信息。概括范畴中 $cal(E)$ 的对象直观上是类型 $Gamma tack A istype$ 的语义解释，而这个范畴中的态射则是类型之间的某种态射。假设 $Gamma tack A istype$，$Delta tack B istype$。$F : cal(E) -> cal(C)^->$ 将态射 $A -> B$ 映射到某个代换 $(Gamma dot A) -> (Delta dot B)$。但是并非所有这样的代换都一定在 $F$ 的像里，并且 $cal(E)$ 中的多个态射可能映射到同一个代换。而自然模型中没有额外规定类型之间的态射。我们有三种办法解决此问题。

其一是令 $cal(E)$ 是 $cal(C)^->$ 的满子范畴，这样相当于要求 $A -> B$ 的映射与代换 $(Gamma dot A) -> (Delta dot B)$ 一一对应，使得这些额外的自由度被 $cal(C)$ 完全决定。这是让 $cal(E)$ 海纳百川，兼收并蓄。这样得到的数学对象称作#define[展映射范畴][display map category].

其二是令 $cal(E)$ 只包含纤维化要求必须存在的映射。换句话说， $cal(E)$ 中的任何态射都出现在某个 $p$-拉回方中。这有更简洁的描述。
#definition[
考虑函子 $p : cal(E) -> cal(C)$。给定 $cal(C)$ 中的态射 $sigma : Delta -> Gamma$ 与 $A in cal(E)$，使得 $p(A) = Gamma$，如果总是存在唯一的 $f : B -> A$ 使得 $p(f) = sigma$，就说 $p$ 是#define[离散纤维化][discrete fibration]。
#eq(diagram({
  node((0,0), $B$, name: <B>)
  node((1,0), $A$, name: <A>)
  edge(<B>, "-->", <A>, $f$)

  node((0,1), $Delta$, name: <Delta>)
  node((1,1), $Gamma$, name: <Gamma>)
  edgeR(<Delta>, "->", <Gamma>, $sigma$)

  edge(<B>, "|->", <Delta>)
  edge(<A>, "|->", <Gamma>)
}))
此时，此图一定是 $p$-拉回方。因此离散纤维化都是纤维化。
]
假如在概括范畴中令 $p : cal(E) -> cal(C)$ 是离散纤维化，就使得 $cal(E)$ 中只包含必须的态射，从而也消除了多余的自由度。这样得到的数学对象称作#translate[具集范畴][category with attributes]. 直观来说，这两种概括范畴应该都与自然模型等价。我们会在 #[@sec:coherence-problem]讨论此事。

第三种办法则是反其道而行之，不去修改概括范畴使得语义匹配语法，而是修改语法使得它匹配概括范畴。这就需要添加一类新的语法，描述类型之间的映射。它可以用于包含子类型的系统，是前沿研究的课题 @comprehension-type-theory。

(...) simplified and expanded definition of DMC and CwA

=== 乱花渐欲迷人眼

以上介绍了许多不同的概念，似乎都可以作为类型论的模型。为何要有如此繁杂的概念? 实际应用时又应该选择什么?

当代的研究中，大部分情况使用的都是具族范畴或者与之等价的概念，包括具集范畴与自然模型 (见 @sec:coherence-problem)。有时候会添加语境性的要求，即范畴中所有对象都可以唯一分解为从空语境出发的有限个语境扩展。某种意义下，这是从类型论语法的视角出发唯一 “正确” 的定义。

少数偏向范畴论视角的研究或者较老的文章会采用别的定义。这是因为局部积闭范畴与概括范畴等等比较适合直接套用范畴论的已有构造。对于同伦类型论而言，同伦论中的模型范畴非常适合与概括范畴或者具集范畴结合。不过反过来，例如多项式模型 (@sec:polynomial) 就更适合用具族范畴。#[@sec:coherence-problem]会考察如何将这些不同的定义互相转换。

初次阅读时，读者不必纠缠不同定义之间的细节，笼统认为它们都大致等价即可。

== 融贯问题 <sec:coherence-problem>

#define[融贯问题][coherence problem]

- display map categories: full subcategory $cal(E) -> cal(C)^->$
- category with attributes: discrete fibration $cal(E) -> cal(C)$, equivalent to split full compcat
- CwA (compcat) = CwF (families) = NatModel (typeof)

...

- Natural solution using coproducts of display maps
- Hofmann's solution
- Lumsdaine local universes and Bocquet's generalization @bocquet-strictification
- Can be avoided using dedicated dependent structures

(also mention universes in sheaf topos)

=== 自然模型的类型结构 <sec:natural-type-structure>

// 介绍局部积闭范畴与概括范畴，除了展示自然模型之外的另一种定义类型论模型的思路之外，另一个重要目的是为接下来的范畴论操作提供一种语言。

// 换句话说，我们在自然模型的研究中需要用到一些范畴论构造。这些构造用范畴论表述比较复杂，但是我们往往可以在类型论（具体来说是带有 $Sigma$、$Pi$ 与外延相等的类型论）中写下一些表达式，再用 #[@sec:lccc-language]的办法解释为范畴中的构造，并且这正是我们想要表达的构造。

(...) reexpress constructs in natural models using the LCCC language, because these constructions are more categorical, but we still want to retain the type theoretic syntax

== 语法与自由模型

语法构成的模型， (...) 用于表述语法的性质 (举例)


(...) #define[表达式模型][term model]，总是模型的范畴中的始对象，因此也称作#define[始模型][initial model] 或者#define[自由模型][free model]。

=== 语法不等同于表达式模型

- We can form the term model, but it cannot be syntax itself, because this needs a definition of model to make sense, which does not exist before models.
  - Syntax _is_ the specification of models
- Statements about syntax can be interpreted as statements about free models
  - For most type theories, initial models usually suffice
  - Counterexample: simply typed lambda calculus with no base types. The models can have non-trivial structure, but the term model is empty.
  - Usual solution: add enough base type to prevent degeneration.

=== 自由模型

What are morphisms between models?

mention sconing and gluing (dependent elimination)

will use to prove canonicity etc later down the line

/*
类型论模型定义的重要特性是其中只要求等式。并非所有数学结构都可以这样定义。例如域是拥有四则运算的集合，其中除法的除数必须非零。因此在域的定义中就必须用到_不等式_。相对地，环则只拥有加法、减法与乘法，其中的结合律、分配律等等都是纯等式。这种数学结构称作#define[代数结构][algebraic structure]。群、环、向量空间都是代数结构，而域、全序、拓扑空间不是.#footnote[代数结构可以包含多个集合，而不一定只在一个集合上配备运算。这称作#define[多类][multi-sorted] 代数结构。类型论模型的另一个特别之处在于涉及的集合以元素为指标，例如 $"Tp"(Gamma)$ 对每个元素 $Gamma in "Ctx"$ 都有一个集合。这样的代数理论称作#define[广义代数理论][generalized algebraic theory]，或者 Cartmell 理论。]

代数结构的一大特征是可以自由生成。换言之，给定一些元素，可以构造出_仅仅_满足代数结构本身要求的等式的结构。例如，一个元素 $x$ 在环的加法、减法、乘法下可以生成表达式 $x^2 + x - 2x$。这些表达式构成的环称作多项式环 $ZZ[x]$。具体来说，我们将给定的元素利用代数结构中的运算自由组合，将构造出的所有表达式商去需要满足的等式关系，得到的就是自由代数结构。

当然，假如这个代数结构中有指定元素 (也就是零元运算，例如环公理要求乘法单位元 $1$)，那么不用给定元素，也能生成非平凡的代数结构。 (expand on this, syntax of groups vs free groups)
*/

== 模型的函子观点

(a category of algebras, model is a map from an algebra to a specified subcategory)

- diagram as functor from small categories
- algebraic structure as product preserving functor
- essentially algebraic structure as left exact functor
- model as functor preserving representable maps into presheaf categories
  - Compare with direct encoding, left exact functor into Set

上村太一 (罗马字：Taichi Uemura)

== 变量的结构

models for substructural type theory and modal type theory, i.e. theory that messes with contexts, see Gratzer @mtt-thesis.
