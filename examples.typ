#import "common.typ": *
= 例海拾珠 <ch:examples>

构造模型的具体例子的思路实则非常简洁。我们先确定模型的核心对象，例如集合模型的核心自然是集合。然后，为了解释依值现象，我们提出某种 “依值对象”。对于集合而言，依值集合就是集合族。为了阐释这种思路，我们先来观察有向图构成的模型。这一例子没有什么实际应用，但是其中依值对象的构造应能启发读者。

观览有向图的例子后，我们再探究各类在数学与计算机科学中有用的模型。这些模型中用到的核心对象，不同背景的读者可能各自只熟悉一部分。为此，文章中会略作介绍，但是读者先跳过也无妨。

== 有向图

=== 模型定义

#let xarrow(arrow: sym.arrow, ..args, sup: none, sub: none) = {
  if args.pos().len() >= 1 {
    sup = args.pos().at(0)
  }
  if args.pos().len() >= 2 {
    sub = args.pos().at(1)
  }
  context {
    let lsup = measure($script(sup)$)
    let lsub = measure($script(sub)$)
    math.attach(math.stretch(arrow, size: calc.max(lsup.width, lsub.width) + 0.75em), t: box($script(sup)$, inset: (bottom: -0.3em)), b: box($script(sub)$, inset: (top: -1.1em), baseline: 100%))
  }
}

#definition[
  *有向图* $Gamma$ 包含如下资料：顶点集合 $V$ 与边的集合 $E$，配有两个函数 $s, t : E -> V$，分别给出一条边的两个顶点。如果 $x$ 是 $Gamma$ 的顶点，我们直接写作 $x in Gamma$。如果 $e$ 是 $Gamma$ 的边，满足 $s(e) = x$，$t(e) = y$，我们将其写作 $e : x -> y$。
]
这里有向图允许有自环和重边，在范畴论中也称作#define[箭图][quiver]。
#definition[
  给定两个有向图，其间的*同态*给出顶点到顶点、边到边之间的映射，保持边与顶点之间的连接关系。换言之，图同态 $sigma : Gamma -> Delta$ 对于所有边 $e : x -> y$，都满足 $sigma(e) : sigma(x) -> sigma(y)$.
]
若要用有向图构建模型，就需要定义依值有向图的概念。
#definition[
  给定有向图 $Gamma$，*依值有向图*包含如下资料：对于每个顶点 $x in Gamma$，有一族集合 $V_x$ 表示依值顶点，对于每条边 $e : x -> y$，有一族集合 $E_e$ 表示依值边，配有两个函数 $s : E_e -> V_x$ 与 $t : E_e -> V_y$。其中的元素写作 $epsilon : alpha xarrow(e) beta$.
]
不难看出，依值有向图就是依值集合 (即集合族) 的简单推广。给定有向图 $Gamma$ 与依值有向图 $A$，可以将 $A$ 中的所有顶点与边合在一起构成新的有向图 $integral A$，称作*全图*。其顶点形如 $(x, y)$，其中 $x$ 是 $Gamma$ 的顶点，而 $y$ 是关于 $x$ 的依值顶点。类似地，其边形如 $(e, epsilon)$。这条边的起点和终点分别是 $(s(e), s(epsilon))$ 与 $(t(e), t(epsilon))$。这构成语境扩展 $(Gamma, A)$ 的解释。请读者构造图同态 $frak(p) : integral A -> Gamma$。

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

以上结构组成类型论模型的基本框架，道理与集合模型类似。难点在于构造各种类型的结构。

=== 类型结构

$Sigma$ 类型比较简单。给定有向图 $Gamma$，依值有向图 $A$ 与 $integral A$ 上的依值有向图 $B$，$Sigma A B$ 在 $x in Gamma$ 上的依值顶点形如 $(a, b)$，其中 $a$ 是 $A$ 在 $x$ 上的依值顶点，而 $b$ 是 $B$ 在 $(x, a)$ 上的依值顶点。依值边则同理。配对、投影运算都很容易构造。需要读者注意的是，代换等式 $(Sigma A B)sigma = Sigma (A sigma) (B sigma')$ 是严格成立的。换句话说，这两个依值有向图是_同一个_依值有向图，而不仅仅是同构的有向图。

空类型不难看出应该解释成空的依值有向图。这样，$"Tm"(Gamma, "Empty")$ 在 $Gamma$ 非空时是空集，而在 $Gamma$ 是空图时恰有一个元素。注意从空集出发的函数总是恰有一个，因此无论是哪种情况，都不难定义出所需的消去子 $"abort"_A : "Tm"(Gamma, "Empty") -> "Tm"(Gamma, A)$，满足所需的代换等式。与集合模型类似，#[@sec:empty-type]中提到的空类型 $eta$ 等式也成立。

不交并则应该解释成依值有向图的不交并。具体来说，$A + B$ 在 $x in Gamma$ 上的依值顶点，要么是 $A$ 在 $x$ 上的依值顶点，要么是 $B$ 在 $x$ 上的依值顶点。对依值边也同理。我们同样需要验证 $(A + B)sigma = A sigma + B sigma$，即两侧是同一个依值有向图。 (..constructor)

不交并的消去子则开始有些难度，不过仅仅是略微繁琐一些。

(... eliminator)


- Extensional equality
- Plain function type
- Pi
- Universe!!

关于有向图的定义，读者或许已经发现它是一种代数结构。其特殊之处在于所有的运算都恰好是一元运算.#footnote[有向图的另一个特点是它的运算 $s, t$ 之间没有任何等式，不过这一点似乎没法做文章。] 这种代数结构称作#define[预层][presheaf]。正因所有运算都是一元的，有许多构造在预层中可以大大简化。以上提到的类型结构的构造都可以推广到一般的预层上，从而构成集合论的预层模型。例如，考虑一列集合 $X_n$ 与函数 $f_n : X_(n+1) -> X_(n)$，其中 $n in NN$。它们构成的代数结构也是预层。这种结构构成的模型在 #translate[？？？][guarded recursion] 的研究中有所应用。

=== 排中律的反模型

尽管有向图模型只是为了演示模型构造的办法，但是它也有一定用处。有向图模型构成排中律的反模型，我们借此机会演示反模型的具体构造。如果采用 “类型就是命题” 的理解办法，那么排中律是
#eq($
  product_(A :cal(U)) "El"(A) + ("El"(A) -> "Empty").
$)
不过，在同伦类型论等现代观点中，只有一部分类型应该看作命题。命题的所有元素都应该相等，即 $product_(x,y : "El"(A)) x = y$，我们简写成 $"isProp"(A)$。因此，同伦类型论语境下的排中律一般仅限于命题排中律，写作
#eq($
  product_(A :cal(U)) product_(p :"isProp"(A)) "El"(A) + ("El"(A) -> "Empty").
$)
因为后者更弱，所以后者的反模型一定都是前者的反模型。

我们需要说明有向图模型中排中律类型没有元素。不过，排中律的 $Pi$ 类型使得验证此事有些繁琐。这里有巧法可以减少工作量。假如空语境下 $product_(x : A) P(x)$ 有元素，那么语境 $x : A$ 下类型 $P(x)$ 就一定会有元素，反之亦然。因此我们只需要验证集合
#eq($
  "Tm"((A : cal(U), p : "isProp"(A)), "El"(A) + ("El"(A) -> "Empty"))
$)
没有元素即可。回忆在有向图模型中，类型是依值有向图，而构造一个元素需要在语境有向图的每个顶点上选择依值顶点，在每条边上选择依值边。那么，假如我们证明语境 $Gamma = (A : cal(U), p : "isProp"(A))$ 的某个顶点上没有任何依值顶点，就可以证明这个类型没有元素。

(...)

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
这里， $"error"(A)_x$ 为每个类型赋予异常。直观上，应该要求它们的确是异常值，即 $"error"(A)_x in.not overline(A)_x$。不做此要求的理由在之后会解释。

我们将语义语境定义为带异常集合，语义代换定义为带异常集合之间的正常映射。语义类型 $A in "Tp"(Gamma)$ 是依值带异常集合，而语义元素 $a in "Tm"(Gamma, A)$ 是它的_正常_元素族。这意味着 $"error"(A)$ 不一定属于 $"Tm"(Gamma, A)$。

由于代换需要将正常值映射为正常值，可以将代换在语义类型与语义元素上的操作分别定义为 $(A sigma)_x = A_(sigma(x))$ 与 $(a sigma)_x = a_(sigma(x))$，这样得到的仍然是依值带异常集合与其正常元素族。
将语境扩展 $(Gamma, A)$ 解释为不交并 $product.co_(x in Gamma) A_x$，其中正常值形如 $(x, y)$，满足 $x in overline(Gamma)$ 与 $y in overline(A)_x$。这样投影映射 $frak(p) : (Gamma, A) -> A$ 与语义元素 $frak(q) : "Tm"((Gamma, A), A frak(p))$ 都不难构造。

=== 类型结构

类型构造的思路是，对于不含 $eta$ 等式的类型 $A$，我们与集合模型的构造相比额外添加一个值作为 $"error"(A)$ 的定义。对于含有 $eta$ 等式的类型，比如 $A times B$，则不作添加，直接定义 $"error"(A times B)_x = ("error"(A)_x, "error"(B)_x)$。这是因为如果额外添加异常元素，那么这个新的元素就无法满足 $eta$ 等式。

对于最简单的单元素类型，我们定义 $"Unit"_x = {star}$ 为单元素集合，$overline("Unit")_x = {star}$ 为全体元素。根据之前的讨论，单元素类型选定的异常元素按 $eta$ 等式必须是 $star$。这意味着 $"error"(A)_x$ 有可能在 $overline(A)_x$ 中，是正常值.#footnote[我们也不能将 $star$ 改为异常值，即将 $overline("Unit")_x$ 定义为空集。因为这样 $"Tm"(Gamma, "Unit")$ 也是空集，不合要求。]

假如执意添加新的异常元素会如何呢? 定义 $P_x = {star, epsilon}$ 为二元素集合，$overline(P)_x = {star}$，而 $"error"(P)_x = epsilon$。由于 $"Tm"(Gamma, P)$ 只包含正常元素族，所以在空语境中 $P$ 只有一个语义元素 $star$。但是，假如 $Gamma = {g}$ 恰有一个元素，并且 $g$ 是异常值，那么 $"Tm"(Gamma, P)$ 就有两个不相等的元素，不满足 $eta$ 规则。

这个类型 $P$ 可以看作利用归纳类型定义的单元素类型，因为归纳类型没有 $eta$ 规则。需要注意的是，有些证明助理为了方便，将恰有一个构造子的归纳类型视作带有 $eta$ 的#translate[记录类型][record type]。但这两者在理论上是满足不同规则的。

Pi type

identity type

对于其他类型，特别是宇宙类型的处理，留给读者作为练习，亦可参阅 Kovács @exception-agda。

=== 函数外延性的反模型

(...)

== 容器与多项式 <sec:polynomial>

可以跳过

- 更传统的 funext 反例

例子：并非所有映射都是展映射

== 群胚

== 可计算性与模型

== 操作语义与模型

== 语法翻译

syntactic version of the exception model

== 语法性质的证明

(promote to own chapter?)
