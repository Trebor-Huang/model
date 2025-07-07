#import "common.typ": *
= 例海拾珠 <ch:examples>

构造模型的具体例子的思路实则非常简洁。我们先确定模型的核心对象，例如集合模型的核心自然是集合。然后，为了解释依值现象，我们提出某种 “依值对象”。对于集合而言，依值集合就是集合族。为了阐释这种思路，我们先来观察有向图构成的模型。这一例子没有什么实际应用，但是其中依值对象的构造应能启发读者。

观览有向图的例子后，我们再探究各类在数学与计算机科学中有用的模型。这些模型中用到的核心对象，不同背景的读者可能各自只熟悉一部分。为此，文章中会略作介绍，但是读者先跳过也无妨。

== 有向图

=== 模型定义

#definition[
  *有向图* $Gamma$ 包含如下资料：顶点集合 $V$ 与边的集合 $E$，配有两个函数 $s, t : E -> V$，分别给出一条边的两个顶点。如果 $x$ 是 $Gamma$ 的顶点，我们直接写作 $x in Gamma$。如果 $e$ 是 $Gamma$ 的边，满足 $s(e) = x$，$t(e) = y$，我们将其写作 $e : x -> y$。
]
这里有向图允许有自环和重边，在范畴论中也称作#define[箭图][quiver]。
#definition[
  给定两个有向图，其间的*同态*给出顶点到顶点、边到边之间的映射，保持边与顶点之间的连接关系。换言之，图同态 $sigma : Gamma -> Delta$ 对于所有边 $e : x -> y$，都满足 $sigma(e) : sigma(x) -> sigma(y)$.
]
#let terminal-graph = box(diagram({
  node((0,0), fill: black, radius: 0.2em, outset: 0.3em, name: <n0>)
  edge(<n0>, "->", <n0>, bend: 130deg, loop-angle: 180deg)
}), height: 0em, inset: (top: -0.88em))

我们将语境解释为有向图，而代换解释为同态。有些反直觉的是，空语境是有一个点与一个自环的图 #terminal-graph，
而不是单点图 $bullet$。这是因为空语境需要满足 $Gamma -> ()$ 恰好有一个代换，所以需要一个自环，否则 $Gamma$ 中的边无法映射到 $()$ 中。

若要用有向图构建模型，就需要定义依值有向图的概念。
#definition[
  给定有向图 $Gamma$，*依值有向图*包含如下资料：对于每个顶点 $x in Gamma$，有一族集合 $V_x$ 表示依值顶点，对于每条边 $e : x -> y$，有一族集合 $E_e$ 表示依值边，配有两个函数 $s : E_e -> V_x$ 与 $t : E_e -> V_y$。其中的元素写作 $epsilon : alpha xarrow(e) beta$.
] <def:dependent-graph>
不难看出，依值有向图就是依值集合 —— 即集合族 —— 的简单推广。给定有向图 $Gamma$ 与依值有向图 $A$，可以将 $A$ 中的所有顶点与边合在一起构成新的有向图 $integral A$，称作*全图*。其顶点形如 $(x, y)$，其中 $x$ 是 $Gamma$ 的顶点，而 $y$ 是关于 $x$ 的依值顶点。类似地，其边形如 $(e, epsilon)$。这条边的起点和终点分别是 $(s(e), s(epsilon))$ 与 $(t(e), t(epsilon))$。这构成语境扩展 $(Gamma, A)$ 的解释。请读者构造图同态 $frak(p) : integral A -> Gamma$。

#numbered-figure(caption: [依值有向图], placement: auto)[
  #let bull = node.with(fill: black, radius: 0.2em, outset: 0.5em)
  #let chosen = color.oklch(50%, 70%, 70deg)
  #diagram(
    spacing: (5em, 3em),
    bull((0, 0), name: <n1>),
    bull((1, 0.5), name: <n2>),
    bull((2, 0), name: <n3>),
    edge(<n1>, "->", <n2>, bend: 25deg),
    edge(<n1>, "~>", <n2>, bend: -25deg),
    edge(<n2>, "->", <n3>),
    edge(<n3>, "->", <n3>, loop-angle: 0deg, bend: 130deg),
    node((-0.5, 0), $Gamma$),

    bull((0, -2), name: <n1-1>),
    bull((-0.1, -1.5), name: <n1-2>, radius: 0.25em, fill: chosen),
    bull((1, -1.7), name: <n2-1>),
    bull((1, -1.35), name: <n2-2>),
    bull((1, -1), name: <n2-3>, radius: 0.25em, fill: chosen),
    bull((2, -1.7), name: <n3-1>, radius: 0.25em, fill: chosen),
    edge(<n1-1>, "->", <n2-1>, bend: 30deg),
    edge(<n1-1>, "->", <n2-1>),
    edge(<n1-1>, "~>", <n2-2>, bend: -10deg),
    edge(<n1-2>, "->", <n2-1>, bend: -5deg),
    edge(<n1-2>, "->", <n2-3>, bend: 5deg, stroke: chosen + 1.5pt, mark-scale: 40%),
    edge(<n1-2>, "~>", <n2-3>, bend: -30deg, stroke: chosen + 1.5pt, mark-scale: 40%),
    edge(<n2-1>, "->", <n3-1>, bend: 15deg),
    edge(<n2-3>, "->", <n3-1>, bend: -20deg),
    edge(<n2-3>, "->", <n3-1>, bend: 10deg, stroke: chosen + 1.5pt, mark-scale: 40%),
    edge(<n3-1>, "->", <n3-1>, loop-angle: 0deg, bend: 130deg, stroke: chosen + 1.5pt, mark-scale: 40%),

    node((-0.5, -1.7), $A$),
    node((2.5, -1.7), text(fill: chosen, $a$)),
  )
] <fig:dependent-graph>

有了语境和类型的解释，下一步是定义元素的解释。在集合模型中，集合族 $A_x$ 的元素 $a_x$ 对于每个 $x in Gamma$ 都选择了元素 $a_x in A_x$。对于依值有向图而言，就是对每个顶点 $x in Gamma$ 都选择 $x$ 上的依值顶点 $a_x$，对每条边 $e : x -> y$ 都选择依值边 $epsilon : a_x xarrow(e) a_y$。

#[@fig:dependent-graph] 中画出了一个依值有向图。 $Gamma$ 有三个顶点，而 $A$ 中对应的依值顶点分别有两个、三个、一个。 $Gamma$ 的每条边上方都有 (零个或多个) 对应的依值边。其中 $Gamma$ 左侧两个顶点之间有两条边，用不同的画法加以区分。如果将 $A$ 视作单独的有向图，忘记与 $Gamma$ 的对应关系，得到的就是 $integral A$。标红的部分则选出了 $A$ 的一个元素 $a$。

依值有向图的代换与集合族的代换也类似。假如有同态 $sigma : Delta -> Gamma$ 与 $Gamma$ 上的依值有向图 $A$，那么可以把 $A sigma$ 在顶点 $x in Delta$ 上的依值顶点定义为 $A$ 在 $sigma(x)$ 上的依值顶点，边 $e$ 上的依值边定义为 $A$ 在 $sigma(e)$ 上的依值边。请读者验证这的确构成 $Delta$ 上的依值有向图，并且满足代换的相关等式。

以上结构组成类型论模型的基本框架，道理与集合模型类似。难点在于构造各种类型的结构。我们先给出一些定义与引理，供读者小试牛刀。稍后也会用到这些工具。

#lemma[
  空语境下的依值有向图与有向图一一对应。
] <lemma:empty-dependent-graph>
#proof[
  回忆空语境是有一个顶点和一个自环的有向图 #terminal-graph。它的依值有向图需要选择唯一的顶点上的依值顶点集 $V$ 与唯一一条边上的依值边集 $E$，配上映射 $s, t : V -> E$。这与有向图的定义完全相同。
]

#definition[
  给定两个有向图 $Gamma$ 与 $A$，可以将 $A$ 视作 $Gamma$ 上的*常依值有向图*。具体来说，每个顶点 $x in Gamma$ 上的依值顶点集都是 $A$ 的顶点集，而每条边上的依值边集都是 $A$ 的边集。
] <def:const-dependent-graph>

#lemma[
  给定有向图 $Gamma$ 与 $A$，将 $A$ 视作常依值有向图时，它的元素与 $Gamma -> A$ 的图同态一一对应。
]
#proof[
  依值有向图的元素 $a$ 需要为每个顶点 $x in Gamma$ 选择它的依值顶点，在这里就是选择 $A$ 的顶点。而 $a$ 还需要为每条边选择依值边，也就是选择 $A$ 的边。$a$ 还需要保持顶点与边的连接关系，这恰好对应图同态保持顶点与边的连接关系的要求。
]

关于有向图的定义，读者或许已经发现它是一种代数结构。其特殊之处在于所有的运算都恰好是一元运算.#footnote[有向图的另一个特点是它的运算 $s, t$ 之间没有任何等式，不过这一点似乎没法做文章。] 这种代数结构称作#define[预层][presheaf]。正因所有运算都是一元的，有许多构造在预层中可以大大简化。一下给出的类型结构的构造都可以推广到一般的预层上，从而构成集合论的预层模型。例如，考虑一列集合 $X_n$ 与函数 $f_n : X_(n+1) -> X_(n)$，其中 $n in NN$。它们构成的代数结构也是预层。这种结构构成的模型在#translate[卫递归][guarded recursion] 的研究中有所应用。

=== 类型结构

==== $Sigma$ 类型
给定有向图 $Gamma$，依值有向图 $A$ 与 $integral A$ 上的依值有向图 $B$，$Sigma A B$ 在 $x in Gamma$ 上的依值顶点形如 $(a, b)$，其中 $a$ 是 $A$ 在 $x$ 上的依值顶点，而 $b$ 是 $B$ 在 $(x, a)$ 上的依值顶点。依值边则同理。配对、投影运算都很容易构造。需要读者注意的是，代换等式 $(Sigma A B)sigma = Sigma (A sigma) (B sigma')$ 是严格成立的。换句话说，这两个依值有向图是_同一个_依值有向图，而不仅仅是同构的有向图。

==== 空类型
空类型不难看出应该解释成空的依值有向图。这样，$"Tm"(Gamma, Empty)$ 在 $Gamma$ 非空时是空集，而在 $Gamma$ 是空图时恰有一个元素。注意从空集出发的函数总是恰有一个，因此无论是哪种情况，都不难定义出所需的消去子 $"abort"_A : "Tm"(Gamma, Empty) -> "Tm"(Gamma, A)$，满足所需的代换等式。与集合模型类似，#[@sec:empty-type]中提到的空类型 $eta$ 等式也成立。

==== 不交并
不交并则应该解释成依值有向图的不交并。具体来说，$A + B$ 在 $x in Gamma$ 上的依值顶点，要么是 $A$ 在 $x$ 上的依值顶点，要么是 $B$ 在 $x$ 上的依值顶点。对依值边也同理。我们同样需要验证 $(A + B)sigma = A sigma + B sigma$，即两侧是同一个依值有向图。

不交并的构造子的构造是显然的。消去子则开始有些难度，不过仅仅是略微繁琐一些。类型 $Gamma, x : A + B tack P istype$ 对应 $integral (A + B)$ 上的依值有向图。根据构造，不难看出 $integral (A + B)$ 与有向图的不交并 $integral A + integral B$ 是同构的。因此 $P$ 也可以分解为两部分，分别在 $integral A$ 与 $integral B$ 上。这样，如果这两部分分别给出元素，那么就能组合出整体的元素。

==== 相等类型
相等类型的构造与集合模型中的类似。给定 $Gamma$ 上的依值有向图 $A$ 与两个元素 $s, t$，如果对于顶点 $x in Gamma$ 有 $s_x = t_x$，就定义依值顶点集 $"Id"(A, s, t)_x$ 为单元素集合，否则是空集。对于边也是类似的。因为 $s$ 与 $t$ 在某条边 $e in Gamma$ 上相等的前提是它们在这条边的两个顶点上也分别相等，所以 $"Id"(A, s, t)$ 是良定义的。与集合模型类似，在有向图模型中相等类型满足外延性，因此我们不用验证 $"J"$ 消去子。

==== 宇宙类型
先忽略集合大小问题。假设 $bullet$ 代表只有一个顶点的有向图，而 $bullet -> bullet$ 代表恰好有一条边的有向图。可以将宇宙有向图 $U$ 的顶点集定义为 $bullet$ 上的全体依值有向图的集合，而边集定义为 $bullet -> bullet$ 上的全体依值有向图的集合。换句话说， $U$ 的顶点集是全体集合的集合，而一条边则是三个集合 $X$、$Y$ 与 $E$，配上两个函数 $E -> X$ 和 $E -> Y$。显然，这条边的两个端点分别是 $X$ 和 $Y$。读者可以验证，图同态 $Gamma -> U$ 与 $Gamma$ 上的依值有向图一一对应。因此，我们可以将宇宙类型 $cal(U) in "Tp"(Gamma)$ 解释为 $U$ 的常依值有向图 (见@def:const-dependent-graph)。这样 $"Tm"(Gamma, cal(U))$ 就与 $"Tp"(Gamma)$ 一一对应，可以用来构造 $"El"$ 了。这里读者还需要验证常依值有向图在代换下稳定，即 $cal(U)sigma = cal(U)$，其中两个 $cal(U)$ 是关于不同有向图的依值有向图。

接下来与集合模型类似处理集合大小问题。前面提到将语境解释为有向图，实则是解释为 $H_kappa$ 中的有向图，而后我们再取强不可达基数 $lambda < kappa$ 构造宇宙的解释。
我们定义宇宙有向图 $U_lambda$ 的顶点集是 $H_lambda$，而两个顶点 $X$ 和 $Y$ 之间的边则是 $H_lambda$ 中的集合 $E$，配备两个函数 $s : E -> X$ 与 $t : E -> Y$。对于多个宇宙的情况，或者 Coquand 层级，相信读者不难类推。

=== 函数类型 <sec:graph-exponential>

$Pi$ 类型需要单开一节讨论。这是因为它的构造乍看比较天马行空。不过，这个构造实际上可以机械地推算出来，无需灵感。我们也会考察不依值的普通函数类型的构造。

假设有有向图 $Gamma$，其上的依值有向图 $A$ 与 $integral A$ 上的依值有向图 $B$，我们需要构造依值有向图 $Pi A B$，也就需要知道顶点集和边集分别是什么。为此，我们考虑 $Pi$ 类型的规则。
#eq($
  rule(
    Gamma tack lambda x bind t : Pi A B,
    Gamma\, x : A tack t : B
  ) quad
  rule(
    Gamma tack f(t) : B[id, t],
    Gamma tack f : Pi A B,
    Gamma tack t : A
  )
$)
我们需要给出映射 $"lam" : "Tm"((Gamma, A), B) -> "Tm"(Gamma, Pi A B)$，而 $beta$ 与 $eta$ 规则说明这个映射是双射。

考虑 $Gamma$ 的一个顶点 $x$。这等价于考虑一个图同态 $sigma : bullet -> Gamma$，其中 $bullet$ 是单点图。如果我们做代换 $(Pi A B) sigma$，就可以得到 $bullet$ 上的依值有向图。此时注意到 $(Pi A B) sigma$ 的元素集 $"Tm"(bullet, (Pi A B) sigma)$ 与 $(Pi A B) sigma$ 在唯一一个顶点上的依值顶点集有双射，而这又和 $Pi A B$ 在 $x in Gamma$ 上的依值顶点集相同。这意味着要构造后者，只需要计算前者。进一步，
#eq($
  & quad "Tm"(bullet, (Pi A B) sigma) \
  &= "Tm"(bullet, Pi (A sigma) (B sigma')) \
  &tilde.equiv "Tm"((bullet, A sigma), B sigma').
$)
其中 $sigma'$ 表示 $B$ 的最后一个变量不动，而其他变量按照 $sigma$ 代换。这样，我们就知道 $Pi A B$ 在 $x$ 上的依值顶点集必须与 $"Tm"((bullet, A sigma), B sigma')$ 有双射，这就完全确定了这个集合。类似地，对于 $Gamma$ 的一条边 $e$，只需要考虑图同态 $sigma : II -> Gamma$，其中 $II = (bullet -> bullet)$ 恰好有一条边。同样的推理可以得到 $Pi A B$ 在 $e$ 上的依值边集必须是 $"Tm"((II, A sigma), B sigma')$。

将计算结果再展开化简，就可以得到如下定义。
#definition[
  给定 $Gamma$、$A$、$B$ 如上，定义 $Pi A B$ 为 $Gamma$ 上的依值有向图，其中 $x in Gamma$ 上的依值顶点集为 $product_(a in A_x) B_((x,a))$，其中 $A_x$ 是 $A$ 在 $x$ 上的依值顶点集。给定 $Gamma$ 的边 $e$ 以及 $Pi A B$ 中合适的顶点 $f_1$ 与 $f_2$，以这两者为端点，在 $e$ 上的依值边集合为
#eq($ E_e^(f_1, f_2) = { F in product_(alpha in A_e) B_((e, alpha)) mid(|) vec(delim: #none,
  s(F(alpha)) = f_1(s(alpha)),
  t(F(alpha)) = f_2(t(alpha))
) }. $)
其中 $A_e$ 表示 $A$ 在 $e$ 上的依值边集，并且 $s$ 与 $t$ 给出一条边的起点与终点。$Pi A B$ 在 $e$ 上的全体依值边的集合就是不交并 $product.co_(f_1, f_2) E_e^(f_1, f_2)$。
]
由此，我们仅靠计算就直接推断出了 $Pi$ 类型的构造。同时，代换等式 $(Pi A B)sigma = Pi (A sigma) (B sigma')$ 也是严格成立的。请读者思考 $"lam"$ 与 $"app"$ 如何定义。

假设在空语境下，并且 $B$ 不依赖于 $A$，这等于说有两个有向图 $A$ 与 $B$。此时 $Pi A B$ 退化为普通的函数 $A -> B$。这就导出了有向图之间的 “映射图” 的概念。在范畴论中，这是有向图范畴的指数对象。给定有向图 $Gamma$ 与 $Delta$，我们定义 $Gamma -> Delta$ 的顶点集为 $Gamma$ 的顶点到 $Delta$ 的顶点之间的映射构成的集合。给定两个这样的映射 $f$ 与 $g$，它们之间的边则需要为 $Gamma$ 的每条边 $x xarrow(e) y$ 选择一条边 $f(x) --> g(y)$。


=== 排中律的反模型

尽管有向图模型只是为了演示模型构造的办法，但是它也有一定用处。有向图模型构成排中律的反模型，我们借此机会演示反模型的具体构造。如果采用 “类型就是命题” 的理解办法，那么排中律是
#eq($
  (A :cal(U)) -> "El"(A) + ("El"(A) -> Empty).
$)
不过，在同伦类型论等现代观点中，只有一部分类型应该看作命题。命题的所有元素都应该相等，即 $(x, y : "El"(A)) -> x = y$，我们简写成 $"isProp"(A)$。因此，同伦类型论语境下的排中律一般仅限于命题排中律，写作
#eq($
  (A :cal(U)) (p :"isProp"(A)) -> "El"(A) + ("El"(A) -> Empty).
$)
因为后者更弱，所以后者的反模型一定都是前者的反模型。

我们需要说明有向图模型中排中律类型没有元素。不过，排中律的 $Pi$ 类型使得验证此事有些繁琐。这里有巧法可以减少工作量。想要证明排中律不成立，只需要具体构造一个不满足排中律的类型即可。用严谨的语言来说，假如我们要证明 $Pi A B$ 在空语境下没有语义元素，并且有 $a in "Tm"((), A)$ 是 $A$ 的语义元素，那么只需要说明 $B[a]$ 没有语义元素。

先忽略大小问题，根据宇宙类型的构造，$"Tm"((), cal(U))$ 的元素应当与有向图一一对应。我们考虑单点有向图 $A = bullet$， $"El"(A)$ 则是对应的空语境中的依值有向图。这在直观上应该的确满足 $"isProp"(A)$。事实上依值有向图满足 $"isProp"(A)$ 当且仅当语境 $Gamma$ 的每个顶点上至多有一个依值顶点，每条边上至多有一条依值边。感兴趣的读者可以自己验证。

接下来需要计算 $"El"(A) -> Empty$。根据 #[@sec:graph-exponential]的讨论，我们需要计算单点图到空图之间的映射图。展开定义可以立刻得到这个图也是空的。因此 $"El"(A) + ("El"(A) -> Empty)$ 同构于 $"El"(A)$。但是，$"El"(A)$ 没有元素! 这是因为 $A$ 只有顶点而没有边，而空语境对应有向图 #terminal-graph，有一个自环。因此 $"El"(A)$ 的元素需要选出自环上的依值边，而这是不可能的。这样就说明了有向图模型中排中律不成立，进而说明 Martin-Löf 类型论中无法证明排中律。

前面提到有向图模型是预层模型的特殊情况。一个经典的结论是，预层模型满足排中律当且仅当这个代数结构中所有操作都有逆。例如一个集合 $X$ 配上运算 $iota : X -> X$ 满足 $iota(iota(x)) = x$，这样 $iota$ 的逆运算是它自己。

== 恒等模型与宇宙

在 Peano 公理系统中，除了归纳法，还需要一系列公理，例如 $0 != "suc"(n)$。在依值类型论中，则可以直接用归纳子证明 $0 != "suc"(n)$。具体办法是先定义 $"Code" : NN -> cal(U)$ 为
#eq($
  "Code"(m) = cases(
    Unit quad & (m = 0),
    Empty quad & (m = "suc"(n))
  )
$)
再定义 $"encode" : (m : NN) -> 0 = m -> "Code"(m)$。由 J 原理，只需考虑 $m$ 是 $0$ 的情况，此时 $"Code"(m)$ 是 $Unit$，因此选择 $star : "Code"(0)$ 即可。此时 $"encode"("suc"(n))$ 的类型是 $0 = "suc"(n) -> Empty$，恰好是不等式 $0 != "suc"(n)$ 的定义。

注意到以上证明中用到了类型的类型 $cal(U)$。这是依值类型论中归纳子额外强度的来源。事实上，如果类型论中没有任何宇宙，是无法证明 $0 != 1$ 的。要说明这一点，只需要找到某个模型使得 $0 = 1$ 成立。

(...) 平凡模型

(...) 尽管没有写出 $NN$ 模型结构

== 异常

在计算机程序中，#translate[异常][exception] 表示程序出现了特殊情况。异常模型给出了考虑这种情况的类型论语义，其中每个类型都包含一些异常值。显然，如果某个类型论中包含异常处理机制，那么就需要这种模型。但是异常模型对一般的依值类型论也有别的用途：它构成了函数外延性的反模型。

函数外延性在 Martin-Löf 类型论中是无法证明的。换句话说，给定命题 $forall x bind f(x) = g(x)$，无法说明 $f = g$。直观上，这可以依靠在函数上打标签来说明。在集合模型中，将函数类型的解释改成 ${"true", "false"} times (text("原解释"))$。函数应用时会抛弃前面的标签信息，因此函数逐点相等不能推出函数本身相等。

这个思路几乎可以构成模型，但它唯一不能满足的是函数的 $eta$ 等式：
#eq($
  rule(
    Gamma tack f = lambda x bind f(x) : A -> B,
    Gamma tack f : A -> B
  ).
$)
因为右侧抛弃了函数的标签，无法将函数原样重组回去。当然，对于无 $eta$ 等价的类型论，这就的确构成反模型，证明了函数外延性是独立的。

对于含 $eta$ 规则的类型论而言，据我所知最简洁的函数外延性反模型正是异常模型。 这种模型的一个版本可以参考 Pédrot 与 Tabareau 的工作 @exception-model。András Kovács 形式化了另一个版本 @exception-agda，并且有简明扼要的解释。另一个反模型是 #[@sec:polynomial]介绍的多项式模型。

=== 模型定义

由于类型论中本身没有抛出异常的办法，我们限制代换和语义元素不能抛出任何新异常。这也保证了并非所有类型都有语义元素，不然就无法达成构造反模型的目的了。另一方面，常函数 $lambda x. c$ 在输入异常时输出也应当是 $c$，而非异常值。因此不必将异常值映射到异常值。

#definition[
  *带异常集合*由集合 $Gamma$ 与子集 $overline(Gamma) subset.eq Gamma$ 组成。子集中的元素称作*正常值*，子集外的元素称作*异常值*.#footnote[在证明助理中形式化此构造时，不必将其表达为子集，可以直接写作类型族 $"isNormal" : Gamma -> "Type"$。] *正常映射*是不抛出新异常的函数 $sigma : Gamma -> Delta$，即需要将 $overline(Gamma)$ 映射到 $overline(Delta)$ 中。
]

#definition[
  给定带异常集合 $overline(Gamma) subset.eq Gamma$，*依值带异常集合*由集合族 $A_x$，子集族 $overline(A)_x subset.eq A_x$ 与元素族 $"error"(A)_x in A_x$ 组成，其中 $x in Gamma$。同时，只有 $x in overline(Gamma)$ 时 $overline(A)_x$ 才可以有元素。依值异常集合的*正常元素族*需要在每个 $A_x$ 中选出元素 $a_x$，使得 $x in overline(Gamma)$ 时 $a_x in overline(A)_x$.
]
这里， $"error"(A)_x$ 为每个类型选出了一个*错误*值。注意与异常值相区分：前者是单个元素，而后者可以有多个。直观上，应该要求错误值属于异常值，即 $"error"(A)_x in.not overline(A)_x$。不做此要求的理由在之后会解释。

我们将语义语境定义为带异常集合，语义代换定义为带异常集合之间的正常映射。语义类型 $A in "Tp"(Gamma)$ 是依值带异常集合，而语义元素 $a in "Tm"(Gamma, A)$ 是它的_正常_元素族。这意味着 $"error"(A)$ 不一定属于 $"Tm"(Gamma, A)$。

由于代换需要将正常值映射为正常值，可以将代换在语义类型与语义元素上的操作分别定义为 $(A sigma)_x = A_(sigma(x))$ 与 $(a sigma)_x = a_(sigma(x))$，这样得到的仍然是依值带异常集合与其正常元素族。
将语境扩展 $(Gamma, A)$ 解释为不交并 $product.co_(x in Gamma) A_x$，其中正常值形如 $(x, y)$，满足 $x in overline(Gamma)$ 与 $y in overline(A)_x$。这样投影映射 $frak(p) : (Gamma, A) -> A$ 与语义元素 $frak(q) : "Tm"((Gamma, A), A frak(p))$ 都不难构造。

=== 类型结构

类型构造的思路是，对于不含 $eta$ 等式的类型 $A$，我们与集合模型的构造相比额外添加一个值作为 $"error"(A)$ 的定义。对于含有 $eta$ 等式的类型，比如 $A times B$，则不作添加，直接定义 $"error"(A times B)_x = ("error"(A)_x, "error"(B)_x)$。这是因为如果额外添加错误值，那么这个新的元素就无法满足 $eta$ 等式。

==== 单元素类型
对于最简单的单元素类型，我们定义 $Unit_x = {star}$ 为单元素集合，$overline(Unit)_x = {star}$ 为全体元素。根据之前的讨论，单元素类型选定的错误值按 $eta$ 等式必须等于 $star$。这意味着 $"error"(A)_x$ 有可能在 $overline(A)_x$ 中，即属于正常值。另一方面，我们也不能将 $star$ 改为异常值，即将 $overline(Unit)_x$ 定义为空集。因为这样 $"Tm"(Gamma, Unit)$ 也是空集，不合要求。

假如执意添加新的错误值会如何呢? 定义另一个类型 $P$，满足 $P_x = {star, epsilon}$ 为二元素集合，$overline(P)_x = {star}$，而 $"error"(P)_x = epsilon$。由于 $"Tm"(Gamma, P)$ 只包含正常元素族，所以在空语境中 $P$ 只有一个语义元素 $star$。但是，假如 $Gamma = {g}$ 恰有一个元素，并且 $g$ 是异常值，那么 $"Tm"(Gamma, P)$ 就有两个不相等的元素，不满足 $eta$ 规则。

这个类型 $P$ 可以看作利用归纳类型定义的单元素类型，因为归纳类型没有 $eta$ 规则。需要注意的是，有些证明助理为了方便，将恰有一个构造子的归纳类型视作带有 $eta$ 的#translate[记录类型][record type]。但这两者在理论上是满足不同规则的。

==== Boole 类型
构造 $Bool$ 的解释时，我们额外添加错误值 $epsilon$。当消去子 $ite(b, t, f)$ 遇到这个错误值时，就返回 $"error"(A)$，其中 $A$ 是消去子的返回类型。因为 $Bool$ 没有 $eta$ 等式，所以这样定义不会破坏需要的性质。

==== $Sigma$ 类型
集合 $(Sigma A B)_x = product.co_(a in A_x) B_((x, a))$，其中正常元素是两个分量都正常的有序对，而错误值 $"error"(Sigma A B)_x = ("error"(A)_x, "error"(B)_((x, "error"(A)_x)))$.

==== $Pi$ 类型
$Pi$ 类型也具有 $eta$ 规则，因此不额外添加错误值。$Pi A B$ 的定义与集合模型中的定义一样，是集合 #eq($ (Pi A B)_x = product_(a in A_x) B_((x, a)). $) 其中正常元素 $f in \(overline(Pi A B)\)_x$ 是那些将正常元素 $a in overline(A)_x$ 映射到正常元素 $f(a) in overline(B)_((x, a))$ 的函数。将错误值 $"error"(Pi A B)_x$ 定义为函数 $a |-> "error"(B)_((x, a))$，也就是将所有 $A$ 中的元素都映射到 $B$ 的错误值。读者熟悉构造时，可以试着考虑 $B$ 不依赖 $A$ 时，即普通函数类型的特殊情形是怎么样的。

==== 相等类型
因为相等类型没有 $eta$ 规则，我们额外添加一个错误值。具体来说，
#eq($ "Id"(A, s, t)_x = cases(
  {star, epsilon} quad & s_x = t_x,
  {epsilon} & s_x != t_x
) $)
并且 $"error"("Id"(A, s, t))_x = epsilon$。显然，$overline("Id"(A,s,t))_x$ 应只包含 $star$。

在有向图模型中，我们通过相等类型的外延性避免了验证 J 原理。异常模型中的相等类型不满足外延性，不过还有其他办法减少工作量。根据@sec:J-equivalences，我们只需构造 $contr$ 与 $transp$ 两条规则的解释即可。

$contr$ 说的是在 $Sigma$ 类型 $(x : A) times (s = x)$ 中的所有元素都等于 $(s, refl(s))$。给定带异常集合 $Gamma$ 与依值带异常集合 $A$，对正常元素族 $s in "Tm"(Gamma, A)$，类型 $T = sum_(a : A) (s = a)$ 满足 $T_x = {(a, epsilon) mid(|) a in A_x} union {(s_x, star)}$，其中只有 $(s_x, star)$ 是正常值。我们需要构造语义元素 $Gamma, u : T tack c : u = (s, refl(s))$。为此，我们在 $u = (s_x, star)$ 时定义 $c_((x, u)) = star$，否则定义 $c_((x, u)) = epsilon$。不难看出这满足 $contr$ 的等式要求，并且有代换等式 $contr_A (s, t, p) sigma = contr_A (s sigma, t sigma, p sigma)$。

$transp$ 说的则是对于两个元素 $s, t$ 与依值类型 $P(x)$，如果有 $p : s = t$，那么就有函数 $P(s) -> P(t)$。我们也可以类似地构造，即当 $s_x = t_x$ 的确成立时取恒等函数，否则输出类型 $P(t)$ 的错误值 $"error"(P(t))_x$。


最后，对于其他类型，特别是宇宙类型的处理，留给读者作为练习，亦可参阅 Kovács 的形式化 @exception-agda。

=== 函数外延性的反模型

万事俱备，可以验证异常模型是函数外延性的反模型。这会用到前面所讲不满足 $eta$ 的单元素类型 $P$。有两个函数 $f, g : P -> P$。前者是常函数，将 $star$ 与 $epsilon$ 都映射到 $star$。后者是恒等函数 $x |-> x$。这两者都构成函数类型的元素。

我们先证明它们逐点相等，即类型 #eq($ (x : P) -> f(x) = g(x) $) 有元素。这只需要说明 $"Tm"((x : P), f(x) = g(x))$ 有元素即可。根据正常元素族的定义，我们需要当 $x = star$ 时选择 $f(x) = g(x)$ 的正常元素，并且 $x = epsilon$ 时选择 $f(x) = g(x)$ 的任意元素。前者可以选择自反性 $refl$，而后者则可以直接选择 $star$。

最后，相等类型 $f = g$ 没有元素。这是因为在空语境中，正常元素族必须选择类型的一个正常元素，但是由于 $f$ 和 $g$ 不相等，相等类型里没有正常元素。

读者可以试着将上面的论证补完，从而证明 Martin-Löf 类型论中，对于任何类型 $X$ 与 $Y$，类型
#eq($ (f, g : X -> Y) -> [(x : X) -> f(x) = g(x)] -> (f = g) $)
都没有元素。进一步，还可以令 $X, Y : cal(U)$ 为类型变量，在前面加上 $product_(X, Y:cal(U))$ 全称量词。这些不过是繁琐的细节处理。

== 容器与多项式 <sec:polynomial>

此节选读。#translate[容器][container] 模型，或称多项式模型，是函数外延性的另一个反模型。在编程中，容器是能装载一系列元素的数据结构。例如列表 $"List"(X)$ 可以装载零个或多个元素，有序对 $X times X$ 恰好可以装载两个，等等。

例子：并非所有映射都是展映射

== 群胚 <sec:groupoid>

相等类型的消去子大致说的是 “相等类型元素的唯一构造办法是 $refl$”。但这种直觉下，除了写出 J 原理之外，还可以写出 K 原理。
#eq($
  rule(
    Gamma tack "J"_A (p, P, r) : P(s, t, p);
    Gamma tack p : "Id"(A, s, t),
    Gamma\, x : A\, y : A\, q : "Id"(A, x, y) tack P(x,y,q) istype;
    Gamma\, z : A tack r : P(z, z, refl_A (z))
  )\ #v(0.35em) \
  rule(
    Gamma tack "K"_A (p, P, r) : P(s, p);
    Gamma tack p : "Id"(A, s, s),
    Gamma\, x : A\, q : "Id"(A, x, x) tack P(x,q) istype;
    Gamma\, z : A tack r : P(z, refl_A (z))
  )
$)
乍看之下，K 原理似乎是 J 原理的特例，适用于 $s$ 与 $t$ 是语法上完全相同的表达式的情况。然而稍微摆弄一番即可发现，找不到简单的办法用 J 原理表达出 K 原理。

如果证明助理有#translate[模式匹配][pattern matching] 的功能，那么也有类似的情况。例如证明 $"Id"(A, x, y) -> P(x) -> P(y)$ 时，我们对变量 $p : "Id"(A, x, y)$ 匹配得到 $p = refl(x)$。这样，证明助理应当将语境中的变量 $y$ 替换为变量 $x$，得到目标类型 $P(x) -> P(x)$，此时填入恒等函数即可。那么，如果 $y$ 与 $x$ 是同一个变量，就应该是上述规则的特例。然而，在将模式匹配翻译为消去子的过程中，这一步必须用到 K 原理~@elim-pattern-matching。如果希望模式匹配与仅使用消去子等价，需要作出一些语法限制~@elim-pattern-matching-without-K。

在有 J 原理的前提下，K 原理等价于一个更简单的叙述，即相等证明的唯一性
#eq($
  rule(
    Gamma tack "UIP"(p, q) : p = q,
    Gamma tack s\, t : A,
    Gamma tack p\, q : s = t
  ).
$)
证明见@sec:K-equivalences。我们在 #[@sec:set-model]的集合模型中已经说明了这与 Martin-Löf 类型论是相容的，因此不可能证伪该原理。它究竟可证还是独立，很长一段时间里都是未解之谜。

1996 年，Hofmann 与 Streicher @groupoid-interpretation 提出了群胚模型，作为 K 原理的反模型。这不仅回答了这个问题，还为其独立性提供了清晰的解释。Martin-Löf 类型论中的类型不仅可以理解为集合，还可以视作_空间_。相等类型的元素则可以视作空间中两个点之间的全体道路构成的空间。这样，人们首次建立了类型论与同伦论之间的联系。为此，在与同伦相关的语境下，我们也将相等类型称作*道路类型*。

在类型论的语法中，类型的定义表面上只会描述其元素的构成，而其中的道路则是 “自动生成” 的。例如给出一条 $A times B$ 中的道路就等价于同时给出 $A$ 中的道路与 $B$ 中的道路。再如函数 $(a, b : X) -> (a = b) -> (f(a) = f(b))$ 是靠 J 消去子定义的，无法在定义函数 $f$ 时控制此函数的表现。如果以空间作为模型，就可以精确控制道路的去处，进而给出各种命题的反模型。

=== 群胚与道路

同伦意义下的空间结构十分丰富，因此要直接以空间构造出类型论的模型有些难度。我们将其推迟到#[@ch:homotopy-theory]。Hofmann 与 Streicher 则采用了只能记录一部分同伦信息的数学结构，对空间做粗略的近似。这个数学结构就是#translate[群胚][groupoid]。

#definition[
  *群胚* $G$ 包含一些点 $x, y in G$ 的集合，两点之间有道路集 $hom_G (x, y)$，
  - 道路有拼接操作，将 $p in hom_G (x, y)$ 与 $q in hom_G (y, z)$ 拼接为 $q * p in hom_G (x, z)$。
  - 有平凡道路 $refl(x) in hom_G (x, x)$。
  - 拼接操作满足结合律 $(p * q) * r = p * (q * r)$ 与单位律 $refl(y) * p = p = p * refl(x)$。
  - 道路有逆转操作，将 $p in hom_G (x, y)$ 变为 $p^(-1) in hom_G (y, x)$，满足 $p^(-1) * p = refl(x)$ 与 $p * p^(-1) = refl(y)$。
] <def:groupoid>
群胚的定义刻画了空间中的点与它们之间的道路，不过没有记录二维乃至更高维的结构信息。最常见的构造群胚的办法是给定一个空间，而后忘记二维以上的信息。这个构造称作基本群胚。
#definition[
  给定拓扑空间 $X$，可以定义*基本群胚* $pi_(<= 1) (X)$ 的点集为 $X$ 的点集，而 $hom_(pi_(<=1) (X)) (x, y)$ 为 $x$ 到 $y$ 的道路集合，商去同伦关系。 // 换句话说，其中的元素形如连续函数 $p : [0, 1] -> X$，使得 $p(0) = x$，$p(1) = y$。如果有两条道路 $p$ 与 $q$，使得存在连续函数 $H : [0, 1] times [0, 1] -> X$
]
如果不熟悉拓扑的基本概念也不要紧。两点之间的道路就是以它们为起点和终点的连续曲线。而如果两条连续曲线能在端点不移动的情况下连续地从一条变为另一条，就说它们同伦。不过，群胚的优点在于它将拓扑概念完全_代数化_了，因此可以简单地按照代数思维，或者离散的组合视角处理群胚，无需担心点集拓扑的技术细节。

群胚的代数性在名字上就初见端倪。如果群胚只有一个点 $star$，那么 $star$ 到自己的道路集合构成一个群.#footnote[许多文献会因此称群是群胚的特殊情况，不过这并不好。群胚的 “元素” 集是它的点集，但群的元素在这个对应下却变成了道路 —— 由于是一个点到自己的道路，所以也叫做*环路* —— 的集合。这么看，这两个概念某种意义上相差了一个维度。因此，我们称一个群 $G$ 对应的群胚为#define[解环群胚][delooping groupoid]，写作 $"B"G$。] 其中群运算是道路拼接。
例如，一般的魔方上的公式变换就构成一个群。群运算是将两个公式并排放置，而单位元是空公式。考虑一种常见的魔方变体，将某些块粘在一起，禁止相对滑动，称作*捆绑魔方*。此时，由于某个状态下并不是所有转动都可以进行，有一些会被捆绑限制，因此它对应的代数结构就从群变成群胚。其中，每一个状态对应一个点，该状态下能执行的公式 (注意可以包括多步转动) 对应道路。由于所有公式都有逆公式，这的确构成群胚。

另一个组合性质的例子是图上的道路。给定无向图 $G$，其中的道路是有限条首尾相连的边组成的列表，而平凡道路就是长度为零的列表。如果道路沿着同一条边折返，就等价于消去折返的部分。这与一般的群胚相比，区别在于道路之间没有非平凡的等式，也就是道路之间没有多余的同伦关系。

#definition[
  给定群胚 $G$ 与 $H$，其间的*同态* $f$ 包括点集之间的映射与道路集 $hom_G (x, y) -> hom_H (f(x), f(y))$ 的映射，满足 $f(refl(x)) = refl(f(x))$、$f(p*q) = f(p)*f(q)$ 与 $f(p^(-1)) = f(p)^(-1)$。
]

#definition[
  给定集合 $X$，定义*离散群胚*的点集是 $X$，只有平凡道路 $refl(x)$。集合 $X$ 对应的离散群胚也写作 $X$。
]
离散群胚之间的同态 $X -> Y$ 恰好是集合之间的映射 $X -> Y$。因此，群胚模型会完整包含一份集合模型。读者可以验证，以下群胚模型中的所有类型构造，限制在离散群胚中就恰好与集合模型中的构造相同。

群胚可以刻画空间的零维与一维同伦信息。一个自然的想法是能否同理给出刻画更高维信息的纯代数结构，乃至完全包含所有同伦信息。花些功夫可以定义出 2-群胚与 3-群胚等，但是定义的组合复杂度增长迅速，很难推广到无穷群胚的情况。对此的研究是高阶代数的来由。

1991 年，Воеводский (Voevodsky) 与 Михаил Капранов (Mikhail Kapranov) 给出了一种无穷群胚的定义，并证明了这种无穷群胚能在同伦意义下表示所有的空间 @inf-groupoid-homotopy-type。但是 1998 年，由 Carlos Simpson~@homotopy-type-3-groupoid 给出了反例，因此证明有误。事实上球面 $SS^2$ 就不在其表达能力范围内。然而，很长一段时间内，人们都没有明白错误在哪里，因此不清楚究竟是证明有误还是反例不成立。这件事是 Воеводский 转而追求形式化证明、发展同伦类型论的动机之一。

有了群胚，依值类型应该仿照集合族定义为群胚族。其中，有道路 $p : "Id"(A, x, y)$ 时，依值类型 $B(x)$ 到 $B(y)$ 有转移映射 $transp(p)$。正如群胚使我们能精确控制道路的表现，群胚族也需要让我们精确控制转移映射的表现。
#definition[
  给定群胚 $Gamma$，*群胚族* $A$ 为每个点 $x in Gamma$ 赋予群胚 $A_x$，为每条道路 $p in hom_Gamma (x, y)$ 赋予同态 $A_p : A_x -> A_y$，使得 $A_refl(x)$ 是恒等映射，并且 $A_p compose A_q = A_(p * q)$。这自动保证 $A_p$ 都可逆，并且 $A_(p^(-1)) = A_p^(-1)$。
]
这样不难看出如何对群胚族进行代换，即 $(A sigma)_x = A_(sigma x)$，满足 $A (sigma compose delta) = (A sigma) delta$。

=== 依值群胚与纤维化

本节讨论群胚模型中依值类型的另一种解释，与后文无关，可以跳过。

阅读了有向图模型之后，读者可能期望依值群胚的定义如下：

#definition[
  给定群胚 $Gamma$，定义*依值群胚* $A$ 包含如下资料：对于每个点 $x in Gamma$ 配备集合 $A_x$，对于每条道路 $p in hom_Gamma (x, y)$ 与 $alpha in A_x$ 和 $beta in A_y$ 配备道路集 $hom_A^p (alpha, beta)$。有平凡道路 $refl(alpha) in hom_A^(refl(x)) (alpha, alpha)$、道路逆转 $(-)^(-1) : hom_A^p (alpha, beta) -> hom_A^(p^(-1)) (beta, alpha)$ 与道路拼接操作
  #eq($ hom_A^p (y, z) times hom_A^q (x, y) -> hom_A^(p * q) (x, z), $)
  满足单位律、结合律，并且道路逆转满足 $xi * xi^(-1) = refl(alpha)$ 与 $xi^(-1) * xi = refl(beta)$。
]
此定义与依值有向图 (@def:dependent-graph) 类似，只不过这里还为群胚中的每个运算规定了对应的依值运算。这个定义不能直接作为类型的解释。这是因为我们希望相等类型的元素由群胚中的道路给出，因此还需要保证依值群胚的道路满足相等类型的性质。

根据@sec:J-equivalences 的结论， $contr$, $transp$

  (...)

#definition[
  给定群胚 $Gamma$ 与依值群胚 $A$，如果对于每条道路 $p in hom_Gamma (x, y)$ 与 $A$ 中的依值点 $alpha in A_x$，都有一条 $p$ 上的依值道路 $xi in hom_A^p (alpha, beta)$ 以 $alpha$ 为起点，就称 $A$ 是#define[纤维化][fibration]。
]
定义中的道路 $xi$ 称作 $p$ 的#define[抬升][lift]。注意在抬升的定义中只能限制 $xi$ 的一个端点。(...)

(...) action under substitution

(...) a glimpse of models for homotopy type theory

=== 模型定义

在群胚模型中，语境的解释是群胚，类型的解释则是群胚族。空语境 $()$ 则对应只有一个点 $star$ 与一条平凡道路 $refl(star)$ 的群胚。不难看出，空语境上的群胚族恰好与普通的群胚是等价的。
#definition[
  给定群胚 $Gamma$ 上的群胚族 $A$，定义*全群胚* $integral A$ 的点是有序对 ${(x, a) mid(|) x in Gamma, a in Gamma_x}$，而从 $(x, a)$ 到 $(y, b)$ 的道路集是有序对 $(p, theta)$，其中 $p in hom_Gamma (x, y)$，并且 $theta$ 是群胚 $A_b$ 中从 $A_p (a)$ 到 $b$ 的道路#footnote[这里，$theta$ 也可取为从 $a$ 到 $A_(p^(-1)) (b)$ 的道路，因为有双射 $hom_A_x (a, A_(p^(-1)) (b)) tilde.equiv hom_A_y (A_p (a), b)$。我们可以认为这两个等价的集合中的元素描述了 $p$ 上的 “依值道路”，见 HoTT 书~@hott-book[式 6.2.2]。]。道路拼接是 $(p, theta) * (q, psi) = (p * q, theta * A_p (psi))$。
]

#definition[
  给定群胚 $Gamma$ 上的群胚族 $A$，定义 $A$ 的元素族 $a in "Tm"(Gamma, A)$ 为每个点 $x in Gamma$ 选择元素 $a_x in A_x$，为每条道路 $p in hom_Gamma (x, y)$ 选择道路 $a_p in hom_A_b (A_p (a), b)$，使得 $a_refl = refl$ 与 $a_(p*q) = a_p * A_p (a_q)$ 成立。这些等式无非是让 $a$ 保持群胚运算，不过因为依值类型的原因需要插入映射 $A_p$ 进行转换。
]

对于群胚模型中类型结构，建议读者先试着自己构造，再对照下文。

==== $Sigma$ 与 $Pi$ 类型
设有群胚 $Gamma$、群胚族 $A$ 与 $integral A$ 上的群胚族 $B$，我们需要定义 $Gamma$ 上的群胚族 $Sigma A B$ 与 $Pi A B$。
前者非常直观，群胚 $(Sigma A B)_x$ 的顶点集是 ${(a, b) mid(|) a in A_x, b in B_((x, a))}$，而从 $(a, b)$ 到 $(a', b')$ 的道路集则是
#eq($ {(alpha, beta) mid(|) alpha in hom_A_x (a, a'), beta in hom_B_(\(x, a'\)) (B_((refl(x), alpha)) (b), b')} $)
这来自于 Martin-Löf 类型论中的定理：
#lemma[
  给定类型 $A$ 与依值类型 $B(a)$，$Sigma A B$ 上从 $(a, b)$ 到 $(a', b')$ 的道路由一条从 $a$ 到 $a'$ 的道路 $p$ 与一条从 $transp(p, b)$ 到 $b'$ 的道路唯一决定。
]
#proof[
  见 HoTT 书~@hott-book[定理 2.7.2]。
]

而对于 $Gamma$ 中的道路，$(Sigma A B)_p$ 对应的群胚同态则将 $(a, b)$ 映射到 $\(A_p (a), B_((p,refl)) (b)\)$。这个定义则同样来自 Martin-Löf 类型论中的定理，见 HoTT 书~@hott-book[定理 2.7.4]。请读者验证以上定义正确，并且 $(Sigma A B) sigma = Sigma (A sigma) (B sigma')$。

$Pi$ 类型则有些许复杂，不过也可以按照 #[@sec:graph-exponential]的办法求解，或者参考 HoTT 书~@hott-book[2.9 节] 中对 $Pi$ 类型上的道路的刻画。
- 群胚 $(Pi A B)_x$ 的点 $f$ 由两个映射组成，一个将 $a in A_x$ 映射到 $f(a) in B_((x, a))$，另一个将 $p in hom_A_x (a, a')$ 映射到 $f(p) in hom_B_(\(x, a'\)) (B_((refl, p)) (f(a)), f(a'))$，使得 $f$ 保持群胚运算，即 $f(refl) = refl$ 与 $f(p * q) = f(p) * B_((refl, p))(f(q))$ 成立。
- 群胚 $(Pi A B)_x$ 中，$f$ 到 $g$ 的道路 $xi$ 则由 $B$ 中的一族道路 $xi_a in hom_B_((x, a)) (f(a), g(a))$ 给出，其中 $a in A_x$。对于每条道路 $p in hom_A_x (a, a')$，道路 $xi$ 需要满足正方形
  #eq(diagram($
    f(a) edge(xi_a) edgeR("d", f(p)) & g(a) edgeL("d", g(p)) \
    f(a') edgeR(xi_a') & g(a')
  $))
  交换，即 $g(p) * xi_a = xi_a' * f(p)$ 成立。
- 最后，对于 $Gamma$ 中的道路 $p in hom_Gamma (x, y)$，对应的同态则将 $f$ 映射到 $g = (Pi A B)_p (f)$，满足在顶点上
  #eq($ g(a) = B_((p,refl)) f(A_(p^(-1)) (a)). $)
  即先反向将 $a in A_y$ 拉回 $A_x$，应用 $f$ 之后再移动至 $B_((x, a))$~@hott-book[式 2.9.4--5]。$g$ 在道路上的表现过于冗杂，从略。

==== 相等类型
对于 $"Id"(A, a_1, a_2)$ 而言，我们先思考 $A$ 是不依值的普通群胚的简单情况。此时我们希望相等类型的元素就是 $A$ 中的道路。至于道路之间的道路，我们则按离散群胚的办法补上。这样，$"Id"(A, a_1, a_2)$ 的解释就是离散群胚 $hom_A (a_1, a_2)$。

对于一般情形，即当 $A$ 是群胚族时，我们定义群胚族 $"Id"(A, a_1, a_2)$ (...)

最后，我们还需要验证 J 原理。根据@sec:J-equivalences 的结论，我们只需构造 $contr$ 与 $transp$ 两个运算，并且验证它们与代换交换。

对于 $contr$ 而言，我们需要计算 $Sigma$ 类型 $(y : A) times (x = y)$ 在群胚模型中的解释。先就 $A$ 不依值的情况建立直觉。此时群胚 $(y : A) times (x = y)$ 的点是有序对 $(y, p)$，其中 $y in A$，$p in hom_A (x, y)$。从 $(y, p)$ 到 $(y', p')$ 的道路集同构于 ${q in hom_A (y, y') mid(|) q * p = p'}$。$contr$ 说明该类型中的所有元素都等于 $(x, refl)$，在群胚语义中就是为每个点 $(y, p)$ 选择一条到 $(x, refl)$ 的道路，满足一些条件。显然应当选择道路 $p^(-1)$，此时需要满足的条件是对于任何道路 $q in hom_A (y, y')$，如果 $q * p = p'$，那么 $(p')^(-1) * q = p^(-1)$。不难看出这总是成立。同时，如果 $q = refl$，那么 $q^(-1)$ 自然也是 $refl$，因此这满足所需的判值相等关系。

依值情况类似，只需再验证 $contr_A (s, t, p) sigma = contr_(A sigma) (s sigma, t sigma, p sigma)$ 即可，繁而不难。

对于 $transp$ 而言，我们同样先考虑 $x : A tack P(x) istype$，即 $A$ 本身不依值的简单情况。 (...)

=== K 原理的反模型

有了群胚模型，不难想到如何违反 K 原理，或者与其等价的相等证明唯一性原理。考虑群胚 $H = "B"ZZ\/2ZZ$，视作空语境下的群胚族。更具体来说，$H$ 有一个点 $star$，有两条道路 $refl(star)$ 与 $eta$，满足 $eta * eta = refl(star)$。这样，相等类型 $"Id"(H, star, star)$ 就有两个不相等的元素，违反了相等证明的唯一性。论证的细节与之前的几个反模型论证完全一致，读者可以自行补充。

当然，由于群胚只记录了一维信息，它是满足更高维的相等证明唯一性的。具体而言，命题
#eq($
  product_(x, y : A) product_(p, q : x = y) product_(alpha, beta : p = q) alpha = beta
$)
仍然是成立的。这是因为相等类型本身的道路是按离散群胚的办法补全的，因此它们之间再取道路就与集合模型中的表现一致。如果构造 2-群胚模型，就能给出这个二维 K 原理的反模型，以此类推。

== 可计算性与模型 <sec:realizability-model>

构造主义往往与可计算的事物联系在一起，因为构造主义中的原理都可以找到程序对应。这就是 Brouwer–Heyting–Колмогоров 解释。相反，排中律就难以找到类似的程序.#footnote[如果拓展我们对程序的定义，那么仍然可以找到#translate[计算续体][continuation] 等解释。但是 “一个程序要么停机要么不停机” 无论如何也不可能解释出可以判定停机性的程序，因此这样的拓展是有限度的。] 不过，BHK 解释并不是声称_所有_能找到程序对应的逻辑原理_都属于_构造主义。事实上，有一些逻辑原理虽然有程序对应，但我们一般不认为是纯粹构造的。

为了消除歧义，往往将完全构造性的原理称作#translate[中性数学][neutral mathematics]。例如可以认为 Martin-Löf 类型论属于中性数学。构造主义逻辑则可以视流派添加额外的公理。例如#translate[直觉主义][intuitionism] 是一种流派，承认可数选择公理等等。俄罗斯流派则致力研究所有能实现为程序的逻辑原理。

=== 计算模型

在计算机科学入门课中，一般会学到 Turing 机、$lambda$ 演算与递归函数等计算模型。它们的重要共同点是这些模型下可计算的函数 $NN -> NN$ 都是相同的。这种现象启发了 *Church–Turing 论题*：一切合理的可计算性概念都会给出同样一个子集 $F subset.eq (NN -> NN)$，因此我们可以直接选择任意一个作为可计算函数的定义。

但是，这并不代表这些计算模型就没有区别，或者对可计算性的定义就盖棺定论了。Church–Turing 论题仅仅针对的是一阶函数 $NN -> NN$，对高阶函数如 $(NN -> NN) -> NN$ 则没有效力。当代的程序设计中的高阶函数层出不穷。倘若没有理论定义哪些高阶函数可计算，显然荒谬。另一方面，我们也可以想象计算能力超出 Turing 机的计算模型，例如可以瞬间判断两个无限精度的实数是否相等。尽管物理上无望造出这种机器，但是不影响我们展开数学研究。这些机器意义下的可计算函数，以及它们之间的强度比较等等，也妙趣横生。

#let defined = math.class("binary", sym.arrow.b)
#let diverge = math.class("binary", sym.arrow.t)
为此，我们先来抽象定义计算模型的概念。由于计算模型中往往会出现不停机、出错等情况，因此会涉及#translate[偏函数][partial function]，即只在定义域的某个子集上有值的函数。如果如果某个表达式 $f(x)$ 有定义，就写 $f(x) defined$，否则写 $f(x) diverge$。规定如果有表达式之间的等式 $f(x) = g(y)$，就表示二者要么同时无定义，要么同时有定义并且相等。举个例子，按照这样的惯例不能写 $x\/x = 1$，因为 $x = 0$ 时左边无定义但右边有定义。
#definition[
  #define[偏组合代数][partial combinatory algebra] 由一个集合 $AA$ 与偏二元运算 $AA times AA harpoon AA$ 组成，直接写作左结合的并列或者点乘符号，即 $x y z = x dot y dot z = (x y) z$。
  
  二元运算需要满足#define[组合完备性][combinatorial completeness]：对于任何 $n$ 个变量的组合，如 $x y y (z y)$ 或者 $z (w (x y)) z$ 等等，都存在某个元素 $a in AA$，使得 $a x_1 ... x_n$ 等于这个组合。
]
这里，$AA$ 的元素既是程序又是数据，$f x$ 表示将程序 $f$ 输入数据 $x$ 运行.#footnote[也有具备类型系统的偏组合代数，可以将程序与数据分开，读者可自行了解。] 组合完备性保证了存在足够多的程序，供我们对数据做基本的操作。例如存在 $i in AA$ 使得 $i x = x$ 构成恒等函数的程序; 存在 $k in AA$ 使得 $k x y = x$，因此 $k x$ 可以作为常函数。

作为例子，有限长的 01 字符串构成偏组合代数。其中 $f x$ 表示将字符串 $f$ 看作某个图灵机 $M$ 的描述，而 $x$ 看作一条纸带，运行 $M$ 的最终结果。如果 $M$ 不停机，就表示 $f x$ 无定义。通用图灵机保证了这个二元运算的组合完备性。在逻辑学中，习惯将 01 字符串改编成自然数。这样就定义了 $NN$ 上的某个偏组合代数。

编程视角下往往直接考虑源码构成的偏组合代数比较方便。即 $f x$ 表示以 $f$ 为源码的程序，输入字符串 $x$ 得到的结果。这与前一个例子基本是相同的。

#let LLambda = h(0pt) + box(rotate(180deg)[$VV$]) + h(0pt)

另一个例子是 $lambda$ 演算。考虑 $beta$ 等价意义下的表达式集合 $LLambda$，二元运算就是函数应用。这样组合完备性显然成立，例如 $k x y = x$ 可以直接由 $lambda x y bind x$ 表达。值得注意的是，这个二元运算是全运算，因为不停机的表达式也是集合 $LLambda$ 中的元素。如果我们只考虑#define[既约][reduced] 表达式 $LLambda'$，即无法 $beta$ 归约的表达式，那么二元运算就会变成偏运算。

有了计算模型的定义，就可以着手定义哪些数学对象是可计算的。以下我们固定一个具体的偏组合代数 $AA$。
#let realizes = math.scripts(sym.forces)
#definition[
  如果有集合 $X$ 与二元关系 $r realizes x$，表示 “程序 $r in AA$ 实现了元素 $x in X$”，使得每个元素都至少有一个程序实现，就称它为#define[汇编][assembly]。如果一个程序至多实现一个元素，就称之为#define[谦][modest] 集合。
]
在常见的计算模型中，都会有自然数的某种实现。例如 $lambda$ 演算中的 Church 自然数，在图灵机中用二进制纸带表达自然数，等等。这样就可以定义 $NN$ 上的汇编关系 $realizes_NN$。

汇编的定义中不要求一个元素只对应一个程序，是因为有许多程序可能表达相同的元素。例如自然数上的函数 $f(x) = x$ 与 $f(x) = "round"(sqrt(x^2 + 0.1))$ 作为程序显然是不同的，但是实现了同一个数学意义上的函数。另一边，不要求一个程序只对应一个元素则有妙用。例如定义 $nabla NN$ 的底集合仍是 $NN$，但是所有程序都实现了所有自然数，即 $r realizes n$ 恒为真。这个汇编描述了 “无计算内涵”，或者 “被擦除” 的信息，且听后文分解。

#definition[
  给定两个汇编 $X$ 与 $Y$，函数 $f : X -> Y$ *可计算*当且仅当存在程序 $r in AA$ 使得 $a realizes_X x$ 时总有 $r a defined$，并且 $r a realizes_Y f(x)$。
]

假如偏组合代数 $AA$ 是 Turing 机或者 $lambda$ 演算，那么函数 $f : NN -> NN$ 在此意义下可计算，当且仅当它在通常的定义下可计算。因此这个定义是合理的推广。另一方面，$nabla NN -> nabla NN$ 的可计算函数就是集合间的任意函数 $f : NN -> NN$，因为任意一个 $r in AA$ 都可以实现 $f$。这解释了为何 $nabla$ 表示无计算内涵。另一个例子是编程语言中的类型信息。编译中往往会擦去代码中的类型，因此多态函数 $forall x bind F(x)$ 可以将 $x$ 解释为 $nabla"Type"$ 的元素，其中 $nabla"Type"$ 中所有程序都实现了所有类型。这在模型的构造中会多次用到。

#theorem[
  恒等函数 $id : X -> X$ 总是可计算。可计算函数的复合也可计算。
]
#proof[
  恒等函数由程序 $i$ 实现，满足 $i x = x$。这是由组合完备性保证的。假如有程序 $p$ 与 $q$ 分别实现了两个函数，那么函数的复合由 $b p q$ 实现，其中 $b$ 是满足 $b x y z = x (y z)$ 的程序，也由组合完备性保证。
]
注意同一个可计算函数可以有多个不同的程序实现。因此我们说可计算函数是_存在_程序实现，而不是_配备_了程序。

//这可以用来表达一些比较微妙的情况。例如对于任何实数 $x$，考虑语言 #eq($ L_x = {11 dots 1 mid(|) #[该字符串在 $x$ 的十进制展开中出现]}. $) 一道经典的谜题是判断 $L_sqrt(2)$ 是否能用 Turing 机判定。答案是肯定的，因为如果十进制展开中连续出现了 $n$ 个 $1$，那么显然也一定连续出现了 $m$ 个 $1$，其中 $m <= n$。因此 $L_sqrt(2)$ 要么只有有限个元素，要么等于 $1^* = {1, 11, 111,...}$。无论是哪种情况，这语言都是可判定的，甚至是正则语言! 这里反直觉的地方在于，尽管 $L_x$ 对每个具体的实数 $x$ 都可判定，但是不存在一个办法能输入实数 $x$，输出判定程序。

// 这些定义非常朴素，但是点出了可计算性的讨论中编码的重要性。我们在讨论可计算性时提到的自然数实际上是带有 $realizes_NN$ 结构的，只不过隐去不谈。在讨论更复杂的对象的可计算性时，编码就尤为重要。例如数值计算多项式的零点时，输入的是多项式的系数，还是一个黑盒程序 (保证这个程序正确实现了某个多项式)，所需要的技术完全不同。

=== 具现模型

以上形式化可计算性的技术称作#define[具现][realizability]。我们据此给出类型论的模型。
将语境解释为汇编，将代换解释为可计算函数。空语境则是单元素集合 ${star}$，满足 $r realizes star$ 对所有 $r$ 都成立。
#lemma[
  给定 $AA$ 的非空子集 $U$，定义汇编 $1_U$ 只有一个元素，并且 $r realizes star$ 当且仅当 $r in U$。则所有 $1_U$ 都互相同构，并且任何汇编 $Gamma$ 到 $1_U$ 都恰有一个可计算函数。
]
#proof[
  给定非空子集 $U$ 与 $V$。因为它们非空，可以任取元素 $u in U$ 与 $v in V$。定义映射 $1_U -> 1_V$，在集合元素上为恒等函数，由程序 $k v$ 实现。其中 $k$ 是上文提到的满足 $k x y = x$ 的元素，由组合完备性保证存在。反过来，$k u$ 可以实现反方向的映射。这构成了 $1_U$ 与 $1_V$ 之间的同构。

  对于任何汇编 $Gamma$，在集合元素上只有一个函数 $Gamma -> 1_U$。这个函数是可计算的，因为 $k u$ 可以作为这个函数的实现。这就说明了恰好有一个可计算函数 $Gamma -> 1_U$。
]
这说明实际上怎么选择空语境的程序实现都可以。我们选择全体程序比较方便。

#definition[
  给定汇编 $Gamma$，定义 $Gamma$ 上的*汇编族*为一族汇编 $A_x$，其中 $x in Gamma$。
]
这个定义简单得令人惊讶。读者或许期望另有条件，要求存在某个程序 $r in AA$ 实现了这个汇编族。究其本质，是因为类型信息在程序中是完全擦除的，因此不需要也不能有额外的要求来定义某种 “可计算汇编族” 的概念。

与集合模型类似，我们将语境扩展定义为汇编族的不交并 $product.co_(x in Gamma) A_x$。它的实现需要用到有序对的程序编码。
#definition[
  如果偏组合代数 $AA$ 上有配对程序 $P$ 与投影程序 $R_1$ 和 $R_2$，满足 $R_1 (P x y) = x$ 与 $R_2 (P x y) = y$，就说这三个程序构成有序对的实现。
]
如果 $AA$ 中有天然的有序对结构，自然可以直接取用。也可以通过组合完备性构造：令 $P$ 满足 $P x y z = z x y$。构造 $Q_1 x y = x$，$Q_2 x y = y$。这样就有投影程序 $R_i (p) = p Q_i$。请读者验证这个定义构成有序对的实现。
#definition[
  给定 $Gamma$ 上的汇编族 $A_x$，它的*不交并* $integral A$ 是汇编。其底集合为 $product.co_(x in Gamma) A_x$，而 $r realizes (x, a)$ 当且仅当 $r = P r_1 r_2$，其中 $r_1 realizes x$，并且在汇编 $A_x$ 中 $r_2 realizes a$。
]
#lemma[
  $integral A$ 的定义中，无论使用哪种有序对的实现，得到的汇编都是同构的.#footnote[尽管同构，它们不一定相等。因此在构造依值类型的时候需要注意类型之间满足的判值等式。]
]
读者照定义应当不难给出语境扩展等运算的构造。对于各种类型而言，汇编族的定义则是将各种表达式编译为 $AA$ 中的程序。例如 $Sigma$ 类型编译为有序对，而 $Pi$ 类型则编译为函数。

假设有汇编 $Gamma$ 与其上的汇编族 $A_x$，还有 $integral A$ 上的汇编族 $B_((x, a))$。定义 $Sigma$ 类型对应的汇编族 $(Sigma A B)_x$ 为不交并 $product.co_(a in A_x) B_((x, a))$，使得 $r realizes_((Sigma A B)_x) (a, b)$ 当且仅当 $r$ 是有序对程序 $P r_1 r_2$，满足 $r_1 realizes_A_x a$，并且 $r_2 realizes_B_((x, a)) b$。

$Pi$ 类型的底集合则不是全体函数 $product_(a in A_x) B_((x, a))$，而只包含可计算的依值函数。某个依值函数 $f$ 可计算，无非就是存在程序 $r$ 能实现它。这里，$r realizes_((Pi A B)_x) f$ 当且仅当 $s realizes_A_x a$ 时 $r s defined$，并且 $r s realizes_B_((x,a)) f(a)$。这样得到的汇编就仍然满足每个元素都至少有一个程序实现的要求。

对于自然数 $NN$ 或者 $Empty$ 与 $Unit$ 等类型，对应的汇编族直接不依赖 $x in Gamma$ 即可。这样，不难算出空语境中 $NN -> NN$ 的元素的确就与可计算函数一一对应。


Extensional equality

=== 命题、命题截断

- Homotopy Propositions, impredicative propositions, strict propositions (coincides with homotopy propositions in extensional type theory)
- Homotopy proposition truncation, impredicative inhabited type, irrelevant squash type
- Will deal with impredicative universe in @sec:impredicative-universe, the homotopy propositions are included in that universe in this model

=== 可计算的逻辑原理

==== 可数选择

- Discuss various notions of choice
- Existence quantifier in extensional type theory

$ forall x : NN bind exists y : A bind P(x, y) ==> exists f : NN -> A bind forall x : NN bind P(x, f(x)) $
$ product_(x : NN) norm(P(x)) --> norm(product_(x : NN) P(x)) $

#let markov = "Марков"
==== #markov 原理

$ (not forall (x : NN) bind f(n) != "true") --> exists (x : NN) bind f(n) = "true" $

You can improve to $Sigma$ type by searching the minimal one

==== Church 原理

=== 非直谓宇宙 <sec:impredicative-universe>

阅读本节需要对非直谓宇宙的定义有所了解。由于通行的术语稍显混乱，建议读者先通读#[@appendix:impredicative] 中对非直谓宇宙的介绍。

- Mention proof irrelevant model of Prop (but the main treatment is in the appendix), it's tricky.
  - Realizability model has that too

- Proof relevant model of Prop, allowing large elimination
  - Mention $Lambda$-sets here or below?
  - Note that squash-type inductives still can't have large induction, otherwise there's Russell's paradox (mention in appendix? probably no need)

- Alternative model proves independence of strong Sigma types within Prop @independence-results-coc
  - $A = NN$ (general recursive functions) for simplicity, maybe rephrase?
  - Let $X$ be *extra modest* if there exists a subset $A' subset.eq A$ such that programs represent an element iff they are defined on $A'$, and they represent the same element iff the actions on $A'$ are equal. $"Prop"$ can be defined as the universe of extra modest sets. Closed under impredicative Pi types.
  - Let $T$ be the extra modest set of total recursive functions
  - Let $X_t$ be a family with underlying set $NN$, $r realizes n$ iff $r(2k) = t(k)$ and [($r(1) = n$ and $t$ is not all zero) OR ($t$ is constant zero and $r(3) = n$)]. $r(k)$ be undefined for other $k$.
  - $Sigma T X$ is not extra modest over the empty context, so the universe doesn't contain a code for it, if we fix the construction of $Sigma$ and the definition of El.
  - However, we just want an _encoding_, i.e. a type that satisfies the universal property of it. This specifies $Sigma$ up to isomorphism, therefore we should find isomorphism invariant properties
  - Assembly $Y$ is *separable* if for unequal elements $y_1, y_2 in Y$, there exists a computable $phi : Y -> Bool$ such that $phi(y_1) = "false"$ and $phi(y_2) = "true"$. (Separable assemblies are modest.)


// == 操作语义与模型 ???

// - Define operational semantics on raw terms first, then fit a type system on it
// - Relation to $Lambda$-realizability

== 语法翻译

- syntactic version of the exception model/labelled function model
- validate injectivity of type constructors via labels
  - trivial countermodel in set model, since $A times Empty = Empty$ strictly holds

