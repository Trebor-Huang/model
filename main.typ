#set text(font: ("New Computer Modern", "Source Han Serif SC"), weight: 450, size: 12pt, lang: "zh")
#show math.equation: set text(font: ("New Computer Modern Math", "Source Han Serif SC"))
#let par-indent = 2em
#set par(leading: 0.85em, spacing: 1em, first-line-indent: (amount: par-indent, all: true), justify: true)
#show math.equation.where(block: true): set par(leading: 0.5em)
#set list(indent: 0.7em)
#set enum(indent: 0.7em)

// CJK punctuation
#show "。": "." + h(0.5em, weak: true)
#show "：": ":" + h(0.4em, weak: true)
#show "，": "," + h(0.35em, weak: true)
#show "（": " ("
#show "）": ") "

#let underdot = {
  let radius = 0.08em
  sym.zwj + box(place(dx: -0.5em - radius, dy: 0.2em, circle(radius: radius, fill: black, stroke: none)))
}
#show emph: it => {
  show regex("\p{sc=Han}"): it => it + underdot
  it
}

// Translation (used for indexing)
#let translation-table = state("translations", ())
#let add-entry(zh, en) = translation-table.update(it => {
  it.push((zh, en))
  it
})
#let translate(zh, en) = [#zh #text(fill: luma(40%))[(#en)]#add-entry(zh,en)]
#let define(zh, en) = [*#zh* #text(fill: luma(40%))[(#en)]#add-entry(zh,en)]

// Defintions
#import "@preview/ctheorems:1.1.3": *
#show: thmrules.with(qed-symbol: [#sym.square#parbreak()])
#let thmstyle = thmplain.with(
  separator: [. ],
  titlefmt: strong,
  bodyfmt: content => content + parbreak(),
  inset: (left: 0em, right: 0em),
  base_level: 2
)

#let theorem = thmstyle("theorem", "定理")
#let lemma = thmstyle("theorem", "引理")
#let definition = thmstyle("theorem", "定义")
#let proof = thmproof(
  "proof", "证明",
  separator: [. ],
  titlefmt: text.with(font: ("Latin Modern Roman", "Kaiti SC")),
  inset: (left: 0em, right: 0em),
)

// Equations
#let eq(content) = [\
  #box(align(center, content), width: 1fr)\
]
#set figure.caption(separator: [. ])
#let numbered-figure = figure.with(kind: "numbered-figure", supplement: "图表", numbering: "1", gap: 1em)
#let varnothing = sym.diameter
#let cal = text.with(font: "KaTeX_Caligraphic")

// Inference rules
#let rule(concl, ..prem) = math.frac(prem.pos().intersperse(math.quad).join(),concl)
#let partir(..rules) = for rule in rules.pos() {
  box(math.equation(rule, block: true), inset: (left: 1em, right: 1em))
  // TODO box inherit baseline
}
// Other type theoretic stuff
#let istype = math.op(math.sans("type"))
#let isnf = math.op(text(fill: color.oklch(50%, 80%, 200deg), math.sans("nf")))
#let isne = math.op(text(fill: color.oklch(50%, 80%, 80deg), math.sans("ne")))
#let isvar = math.op(text(fill: color.oklch(50%, 0%, 0deg), math.sans("var")))
#let interpret(x) = math.lr(math.class("opening",sym.bracket.double) + x + math.class("closing",sym.bracket.double.r))
#let bind = math.class("punctuation", ".")
#let ite(b,t,f) = $"if" #b "then" #t "else" #f$

// Front page
#[
#set align(center)
#v(1fr)
#set text(size: 36pt)
*依值类型论的模型*\
#set text(size: 20pt)
Trebor\ #v(1em)
#set text(size: 14pt)
#datetime.today().display("[year]年[month padding:none]月[day padding:none]日")
#v(1.2fr)
]

#set page(numbering: "i")
#counter(page).update(1)

// Headings and outline
#show heading: set block(above: 1.25em, below: 0.9em)
#show heading.where(level: 1): it => [
  #pagebreak(weak: true)
  #set align(center)
  #set text(size: 20pt)
  #it
]
#show heading.where(level: 2): set text(size: 16pt)
#show heading.where(level: 3): set text(size: 14pt)
#show heading.where(level: 4): set text(size: 12pt)
#show heading.where(level: 4): box.with(inset: (left: -par-indent, right: 0.75em))

#outline(depth: 2, indent: 1.5em)

// Redact the chapter number
#set heading(numbering: (a, ..b) => numbering("1.", ..b))
#show heading.where(level: 1): set heading(numbering: (k) => [第#numbering("一", k)章])
#show heading.where(level: 4): set heading(numbering: none)
#show ref: it => {
  let el = it.element
  if el != none and el.func() == heading {
    context {
      if el.level == 1 {
        link(it.target)[第#numbering("一", ..counter(heading).at(it.target))章]
      } else {
        link(it.target)[#numbering("1.1", ..counter(heading).at(it.target))节]
      }
    }
  } else {
    it
  }
}

#set page(numbering: "1")
#counter(page).update(1)

#heading(numbering: none)[前言]

= 前置知识

== 类型论拾遗

阅读本文，读者自然需要对依值类型论有基础的了解。例如 $Sigma$ 与 $Pi$ 类型的规则，读者应当胸有成竹。同样，如果读者希望阅读同伦类型论相关的章节，就需要对同伦类型论有了解，反之则跳过也不影响阅读。

本文不会花费过多笔墨讨论变量的处理。我们在公式中一般直接使用具名变量，但是 $lambda x. x$ 与 $lambda y. y$ 直接视作等同，不加额外说明。对于#translate[语境][context] 而言，如果希望强调其不依赖变量名的属性，可能将 $(Gamma, x:A)$ 写作 $(Gamma, A)$。为了方便书写，我们也将 $Sigma$ 类型写成 $(x : A) times B(x)$，与非依值的 $A times B$ 对应。$Pi$ 类型写成 $(x : A) -> B(x)$。不依赖变量名时，则直接写作 $Sigma A B$ 与 $Pi A B$。

依值类型论的定义中，往往先定义不考虑类型的表达式集合，称作#translate[原始表达式][raw term]，再定义类型规则剔除类型不合的表达式，以及#translate[判值相等][judgmental equality] 关系。这样可以得到一系列集合
#eq($"Ctx" quad "Tp"(Gamma) quad "Tm"(Gamma, A)$)
分别代表类型正确的语境、类型与元素表达式，商去判值相等后构成的集合。其中 $Gamma in "Ctx"$, $A in "Tp"(Gamma)$。不过，如果可以从一开始就确保类型的正确性，在数学处理上会更加优雅。这可以由归纳定义的办法构造。

自然数的归纳构造办法是定义 $NN$ 为满足 $0 in NN$ 与 $n in NN ==> "suc"(n) in NN$ 的最小集合。在集合论中，可以将这里的 “最小” 严格定义成所有满足条件的集合的交。在类型论#sym.zwj#footnote[自然，这里的类型论是#translate[元理论][metatheory]，与我们正在定义的类型论不相同。]中，这可以实现为归纳类型。对于表达式而言，归纳构造办法稍微复杂一些，例如有
#eq($
  A,B in "Tp"(Gamma) &==> (A times B) in "Tp"(Gamma)\
  a in "Tm"(Gamma, A), quad b in "Tm"(Gamma,B) &==> (a, b) in "Tm"(Gamma, A times B) \
  a in "Tm"(Gamma, A), quad b in "Tm"(Gamma,B) &==> pi_1 (a, b) = a.
$)
这些规则生成的最小结构就是类型论的语法。本文不会用到这些构造的细节，因此不再赘述。

如果将上文中的 $A in "Tp"(Gamma)$ 改写为 $Gamma tack A istype$，$a in "Tm"(Gamma, A)$ 改写为 $Gamma tack a : A$，并且将蕴涵关系 $==>$ 写作长横线，那么这些规则就化作逻辑学中熟悉的形式：
#eq(partir(
  $rule(Gamma tack A times B istype, Gamma tack A istype, Gamma tack B istype)$,
  $rule(Gamma tack (a,b) : A times B, Gamma tack a : A, Gamma tack b : B)$,
  $rule(Gamma tack pi_1 (a,b) = a : A, Gamma tack a : A, Gamma tack b : B)$
))
本文中所有这样的写法都应当视作与类似 $a in "Tm"(Gamma, A)$ 的写法等同。这种写法仅仅是为了遵循传统，并且或许更加易读，而没有额外的特殊含义。需要警示读者的是，并不是所有这样的长横线都可以做此解读，不同的范式中有不同的理解办法。

本文不在记号上区分判值相等与相等类型，只靠文字说明和上下文辨义。

=== 语境与代换 <sec:explicit-substitution>

代换的方向对初学者或许有些反直觉。例如假设 $Delta = (x : NN, y : NN)$ 与 $Gamma = (z : NN)$，那么 $sigma = [x \/ 3, y \/ f(z)]$ 乍看应当是从 $Delta$ 到 $Gamma$ 的代换。不过，如果 $Delta = (x : A)$ 与 $Gamma = (y : B)$ 都只有一个类型，那么代换 $sigma = [x \/ t]$ 就与从 $B$ 到 $A$ 的函数一一对应。因此我们将代换的方向写作 $Gamma -> Delta$，或者仿照元素的写法 $Gamma tack sigma : Delta$。

我们把空语境和空代换都写作 $()$，而给定 $Gamma -> Delta$ 的代换 $sigma$，我们可以在 $Delta$ 中添加一个变量 $(Delta, x : A)$，那么代换也需要增加对新变量的代换结果，我们写作 $(sigma, x\/t)$。在不使用变量名的写法中，则写作 $(sigma, t) : Gamma -> (Delta, A)$。

在类型论的规则中，语境和代换有两种解释方式。通常的介绍中，会认为代换是从当前变量集到表达式的映射。
代换在表达式上的操作是在表达式上递归定义的，例如
#eq($ (A + B)[x \/ M] = (A[x \/ M] + B[x \/ M]) $)
等等。这种定义要求所有的语境都有明确的层次结构：如果 $Gamma = Delta$，那么这两个语境长度必须相同。如果 $(Gamma, x : A) = (Gamma', x' : A')$，那么除了变量名可以修改之外，必须满足 $Gamma = Gamma'$ 与 $A = A'$。这样，我们可以认为某条规则
#eq($
  rule(Gamma tack F(A) istype, Gamma tack A istype)
$)
实际上是一连串规则
#eq($
  #for Gamma in ($$, $x : X$, $x : X, y : Y$) {
    $rule(Gamma tack F(A) istype, Gamma tack A istype) quad$
  }
  dots.c
$)
的缩写。这实质上就消除了规则中的所有语境元变量，只使用类型元变量表达。

另一种解释办法是认为语境没有天然的层次。这就需要将代换作为额外的语法元素，包含在类型论的规则当中。例如我们需要额外的判定 $Gamma tack sigma : Delta$, 表达 $sigma$ 是两个语境之间的代换。 需要添加新的语法 $"subst"(t, sigma)$ 表示将 $t$ 做代换 $sigma$ 得到的新表达式，这里写作 $t sigma$。$(A + B)sigma = (A sigma + B sigma)$ 这条等式则是额外添加的判值相等，而不需要做递归定义。熟悉证明助理中的复杂归纳类型的读者可以发现，原本类型论的语法需要定义成#translate[归纳递归类型族][indexed inductive-recursive type]，而这种解释方法则可以将其简化为#translate[归纳类型族][indexed inductive type].

这两种解释办法定义得到语法本质上是等价的，并且都自然地对应一种模型的定义。前者为每一种长度的语境都各自赋予一类对象，而后者将所有的语境放在一起。但是，数学实际中遇到的对象往往不会具有这样明确的长度结构。例如在集合中，$A times varnothing = varnothing$，因此没有办法区分一个空集究竟是几个集合的乘积。我们故而采用第二种观点，而将第一种观点下的相关定义称作#define[语境性][contextual] 的。不过，这两者实际上大同小异，只是细节处理上后者会更加优雅。

为供读者参考，在@fig:substitution 中列出了第二种观点下需要添加的相关规则，粗读时可以跳过。其中， $frak(p)$ 是从语境扩展 $(Gamma, A)$ 到 $Gamma$ 的代换，抛弃最后一个分量。同时应当有变量表达式 #eq($ Gamma, x : A tack x : A. $)但是 $A$ 是在语境 $Gamma$ 中的类型，所以严格来说需要经过 $frak(p)$ 代换之后才能在 $(Gamma, x : A)$ 语境下使用。在不使用变量名时，将元素表达式 $Gamma, x : A tack x : A$ 写作 $frak(q) in "Tm"((Gamma, A), A frak(p))$。这样，语境中从右向左的第 $n$ 个变量就应该写作 $frak(q) frak(p)^(n-1)$，与 de Bruijn 指标的写法类似。

#numbered-figure(
  placement: auto,
  caption: [代换的规则],
  partir(
    // Category of substitutions
    $rule(
      Gamma tack id : Gamma
    )$,
    $rule(
      Gamma tack tau compose sigma : Xi,
      Gamma tack sigma : Delta,
      Delta tack tau : Xi
    )$,
    $rule(
      Gamma tack id compose sigma = sigma : Delta,
      Gamma tack sigma : Delta
    )$,
    $rule(
      Gamma tack sigma compose id = sigma : Delta,
      Gamma tack sigma : Delta
    )$,
    $rule(
      Gamma tack delta compose (tau compose sigma) = (delta compose tau) compose sigma : Theta,
      Gamma tack sigma : Delta,
      Delta tack tau : Xi,
      Xi tack delta : Theta,
    )$,
    // Functorial actions
    $rule(
      Gamma tack A sigma istype,
      Gamma tack sigma : Delta,
      Delta tack A istype
    )$,
    $rule(
      Gamma tack t sigma : A sigma,
      Gamma tack sigma : Delta,
      Delta tack t : A
    )$,
    $rule(
      Gamma tack A (tau compose sigma) = (A tau) sigma istype,
      Gamma tack sigma : Delta,
      Delta tack tau : Xi,
      Xi tack A istype
    )$,
    $rule(
      Gamma tack t (tau compose sigma) = (t tau) sigma : A tau sigma,
      Gamma tack sigma : Delta,
      Delta tack tau : Xi,
      Xi tack t : A
    )$,
    // Empty context
    $rule(
      Gamma tack () : ()
    )$,
    $rule(
      Gamma tack sigma = () : (),
      Gamma tack sigma : ()
    )$,
    // Context extension
    $rule(
      Gamma tack (sigma, t) : (Delta, A), 
      Gamma tack sigma : Delta,
      Delta tack A istype,
      Gamma tack t : A sigma
    )$,
    $rule(
      Gamma\, A tack frak(p) : Gamma,
      Gamma tack A istype
    )$,
    $rule(
      Gamma\, A tack frak(q) : A frak(p),
      Gamma tack A istype
    )$,
    // beta
    $rule(
      Gamma tack frak(p) compose (sigma, t) = sigma : Delta,
      Gamma tack sigma : Delta,
      Delta tack A istype,
      Gamma tack t : A sigma
    )$,
    $rule(
      Gamma tack frak(q) (sigma, t) = t : A sigma,
      Gamma tack sigma : Delta,
      Delta tack A istype,
      Gamma tack t : A sigma
    )$,
    // eta
    $rule(
      Gamma tack sigma = (frak(p) compose sigma, frak(q) sigma) : (Delta, A),
      Delta tack A istype,
      Gamma tack sigma : (Delta, A),
    )$
  )
)<fig:substitution>

=== 类型与宇宙

依值类型论的核心在于冒号左侧的表达式可以出现在冒号的右侧。这个特性使得在依值类型论的实现中往往在语法上对冒号左右两侧（元素与类型）不做区分，即二者都属于表达式。不过在理论上，将两者的语法类别分开可以让各种概念更加干净清晰。例如在语法上，如果 $M, N$ 是元素表达式，$A$ 是类型表达式，那么 $"Id"(A,x,y)$ 就是类型表达式。在 $Gamma tack M : A$ 中，$M$ 必须是元素表达式，而 $A$ 必须是类型表达式。

粗略地说，#define[宇宙][universe] 是类型的类型。不过这个说法有两个不准确之处。第一，宇宙一般只是一些类型的类型，不会覆盖全部的类型。第二，宇宙的元素实际上是类型的_名字_，而非类型本身。类型的名字属于元素表达式，而不属于类型表达式。在语法上额外有一个构造 $"El"$，将类型的名字 $A : cal(U)$ 转化为类型表达式 $"El"(A) istype$。这种处理宇宙的办法名字是 *Tarski 宇宙*。不区分类型的名字与类型的做法称作 *Russell 宇宙*。可以认为 Russell 宇宙只是在工程上较为方便，在理论上应该作为 Tarski 宇宙的简写法理解。

#let convert = math.class("unary", sym.arrow.t)
依值类型论中往往有多重宇宙，它们主要的功能之一是控制类型的大小。这里需要区分的是宇宙之间的#define[累积][cumulation] 关系与元素关系。在 Tarski 宇宙下，累积性是指有算符 $convert$ 将低层宇宙的元素变为高层宇宙的元素，使得#footnote[不同的宇宙理论上应当使用不同的 $"El"$ 算符，例如写作 $"El"_(cal(U)_1)$ 与 $"El"_(cal(U)_2)$。这里略去。]
#eq($ "El"(convert A) = "El"(A) istype $)
成立，即这两个名字指代的是同一个类型。Russell宇宙下可以将 $"El"$ 与 $convert$ 都作为隐式转换处理。元素关系则是说存在大宇宙的一个元素 $U_1 : cal(U)_2$，使得 $"El"(U_1) = cal(U)_1$ 是小宇宙。 Russell 宇宙下可以写作 $cal(U)_1 : cal(U)_2$. 这两个性质是互相独立的，即两两组合一共有四种可能性。

控制大小也可以无需宇宙。可以依靠多个类型判断 $Gamma tack A istype_kappa$ 表示类型的不同大小，其中 $kappa$ 是控制大小的层级参数。换句话说，我们选择多个集合 $"Tp"_kappa (Gamma)$ 与对应的元素 $"Tm"_kappa (Gamma, A)$。类型论的各种规则都可以添加层级标记，例如
#eq($
  rule(Gamma tack A -> B istype_max{kappa, lambda}, Gamma tack A istype_kappa, Gamma tack B istype_lambda) quad
  rule(Gamma tack cal(U)_kappa istype_(kappa^+)).
$)
这样，控制大小的功能就与宇宙为类型提供名字的功能独立了。这种办法称作 *Coquand 层级*。另外一个好处是，在这种情况下可以引入 $"El"$ 的逆运算，给定 $A istype_kappa$，给出它的一个名字 $ceil(A) : cal(U)_kappa$。Tarski 宇宙因为同时承担了控制大小与提供名字的功能，因此不能引入这种算符：$A istype$ 无法确定应该让 $ceil(A)$ 处在哪个宇宙中。

=== 正规形式与典范形式

为了实现依值类型论的类型检查，我们需要能够判定表达式之间是否有判值相等。 这可以依靠#translate[正规形式][normal form] 实现。如果每个表达式都等于唯一一个正规形式，那么只要计算出正规形式并比较即可。传统中，往往可以在表达式上定义一系列重写关系，例如 $1 + 1 ~> 2$ 或者 $pi_1 (a, b) ~> a$，使得正规形式是不能通过重写化简的表达式，不过这不是必须的。对于常见的依值类型论而言，可以直接定义出所有的正规形式，而不需要依赖重写关系。同时，重写关系的技术难以处理 $eta$ 等价关系，以及许多更加复杂的判值相等。

正规形式是与#translate[中性形式][neutral form] 互相归纳定义的。直观而言，正规形式是一系列#footnote[可以是零个、一个或多个，下同。]构造子的嵌套，嵌套的最底层是中性形式。中性形式则是一系列消去子卡在某个变量上。例如，$lambda n bind "suc"(n)$ 是正规形式，从外向内分别是函数类型的构造子与自然数类型的构造子。再者，$lambda b bind ite(b, 1, 2)$ 也是正规形式，最外侧是函数类型构造子，而内部是 Boole 类型的消去子卡在 $b$ 上。

为了迫使 $eta$ 展开，规定正规形式最底层的中性形式必须是不可 $eta$ 展开的类型。例如假设 $f : (NN -> NN) -> NN$，则变量 $f$ 本身是中性形式，但不是正规形式，因为它可以展开为 $lambda g bind f(lambda n bind g(n))$。这里，外部是函数类型的构造子 $lambda g$，而内部是类型为 $NN$ 的中性形式 $f(lambda n bind g(n))$，函数类型的消去子 (即函数应用) 卡在了变量 $f$ 上。

给定语境 $Gamma$ 与类型 $Gamma tack A istype$，我们定义集合 $"Nf"(Gamma, A) -> "Tm"(Gamma, A)$。为了与表达式集合相呼应，我们将 $M in "Nf"(Gamma, A)$ 写作 $Gamma tack M : A isnf$，并且将含入函数写为隐式转换。类似地，也有正规表达式 $"Ne"(Gamma, A)$，写作 $Gamma tack M : A isne$。同时也有正规与中性的类型，写作 $Gamma tack A isnf istype$ 与 $Gamma tack A isne istype$. 注意正规表达式 $"Nf"(Gamma, A)$ 中 $Gamma$ 与 $A$ 没有任何正规性要求，是 (判值相等意义下) 任意的语境与类型表达式。

#numbered-figure(
  placement: auto,
  caption: [正规形式与中性形式],
  partir(
    // Function
    $rule(
      Gamma tack product_(x : A) B isnf istype,
      Gamma tack A isnf istype,
      Gamma\, x : A tack B isnf istype
    )$,
    $rule(
      Gamma tack lambda x bind t : product_(x : A) B isnf,
      Gamma\, x : A tack t : B isnf
    )$,
    $rule(
      Gamma tack f(t) : B[x\/t] isne,
      Gamma tack f : product_(x : A) B isne,
      Gamma tack t : B isnf
    )$,
    // Pair
    $rule(
      Gamma tack sum_(x : A) B isnf istype,
      Gamma tack A isnf istype,
      Gamma\, x : A tack B isnf istype
    )$,
    $rule(
      Gamma tack (a, b) : sum_(x : A) B isnf,
      Gamma tack a : A isnf,
      Gamma tack b : B[x\/a] isnf
    )$,
    $rule(
      Gamma tack pi_1 p : A isne,
      Gamma tack p : sum_(x : A) B isne
    )$,
    $rule(
      Gamma tack pi_2 p : B[x\/pi_1 p] isne,
      Gamma tack p : sum_(x : A) B isne
    )$,
    // Boolean
    $rule(
      Gamma tack "Bool" isnf istype
    )$,
    $rule(
      Gamma tack "true" : "Bool" isnf
    )$,
    $rule(
      Gamma tack "false" : "Bool" isnf
    )$,
    $rule(
      Gamma tack ite(b, s, t) : A[x\/b] isne,
      Gamma\, x : "Bool" tack A istype,
      Gamma tack b : "Bool" isne,
      Gamma tack s : A[x\/"true"] isnf,
      Gamma tack t : A[x\/"false"] isnf,
    )$,
    // Variable
    $rule(
      Gamma tack t : "Bool" isnf,
      Gamma tack t : "Bool" isne
    )$,
    $rule(
      Gamma tack x : A isne,
      Gamma tack x : A isvar
    )$,
    // TODO
  )
)<fig:normal-form>

注意@fig:normal-form 中，一条规则是 Boole 类型的中性形式都是正规形式。严格来说，这在正规形式的递归定义中应该写成构造子 $iota : "Ne"(Gamma, "Bool") -> "Nf"(Gamma, "Bool")$，但是我们写作隐式转换。另外，因为没有写出宇宙的规则，所以无法构造类型变量，故暂时不存在任何中性类型。宇宙满足大体规则格式如下，其中宇宙 $cal(U)$ 只包含乘积类型为例。
#eq($
  rule(
    Gamma tack cal(U) istype
  ) quad
  rule(
    Gamma tack "El"(A) istype,
    Gamma tack A : cal(U)
  ) quad
  rule(
    Gamma tack A dot(times) B : cal(U),
    Gamma tack A : cal(U),
    Gamma tack B : cal(U)
  )\
  rule(
    Gamma tack "El"(A dot(times) B) = "El"(A) times "El"(B) istype,
    Gamma tack A : cal(U),
    Gamma tack B : cal(U)
  )
$)
对应的正规形式规则如下。
#eq($
  rule(
    Gamma tack cal(U) isnf istype
  ) quad
  rule(
    Gamma tack "El"(A) isne istype,
    Gamma tack A : cal(U) isne
  ) quad
  rule(
    Gamma tack A dot(times) B : cal(U) isnf,
    Gamma tack A : cal(U) isnf,
    Gamma tack B : cal(U) isnf
  )
$)
(...What happens for Coquand universes?)

代换 $Gamma tack sigma : Delta$ 也可以规定正规形式，直观上说 $sigma = [x_1 \/ t_1, x_2 \/ t_2, ...]$ 是正规形式当且仅当每个 $t_i$ 都是正规形式。严格来说可以写成如下规则：
#eq($
  rule(Gamma tack () : () isnf) quad
  rule(
    Gamma tack (sigma, t) : (Delta, A) isnf,
    Gamma tack sigma : Delta isnf,
    Gamma tack t : A sigma isnf
  ).
$)
也可以同理定义 $Gamma tack sigma : Delta isne$。这些规则中还用到了 $Gamma tack x : A isvar$ 的写法，其意义自明。而若有代换 $Gamma tack sigma : Delta isvar$，即每一项都是变量，我们就称 $sigma$ 是#define[更名][renaming] 代换。

程序员一般不太关心正规形式，因为程序的运行求值不会在有变量的环境下进行。例如 $lambda x bind x + (1 + 1)$ 在运行时不会计算为 $lambda x bind x + 2$，而是等到有参数输入后再进行计算。更狭义而言，只有一小部分 “基础” 类型能在运行时提供信息，例如 $"Bool"$ 类型或者自然数类型 $NN$。在无变量的情况下，这些类型的正规形式非常简单。例如 $"Bool"$ 类型只有 $"true"$ 与 $"false"$ 两个元素。这类表达式称作#define[典范形式][canonical form]。

== 范畴论筑基

本文采用的思路是尽可能晚引入范畴语言。不熟悉范畴的读者也可以跳过此节继续阅读。这一节对范畴论基础蜻蜓点水，同时也确定一些有歧义的记号的写法。

- Diagrammatic reasoning

- Natural isomorphism chains

== 集合论撷英

- Set theory for category theory



= 模型的定义

模型，语义与解释的区别

- Start from examples, then extract definition
- Later package definition more elegantly

== 集合模型

直观上说，对于大多数类型论而言，每个类型可以理解为集合，函数类型对应集合之间的函数构成的集合，乘积类型对应集合的 Descartes 乘积，等等。(同伦类型论不在此列.) 因此，我们理应能够构造出类型论的集合模型。
依值类型论中，依值类型 $x : A tack B(x) istype$ 可以解释为集合族 ${B(x)}_(x in A)$，即为每个元素 $x in A$ 赋予一个集合 $B(x)$。 $Sigma$ 类型对应不交并
#eq($ product.co_(x in A) B(x) = {(x, y) mid(|) x in A, y in B(x) }. $)
相应地，$Pi$ 类型对应乘积 $product_(x in A) B(x)$。

不过，上面的说法并不完整。在依值类型论中，_所有_的类型 $Gamma tack A istype$ 都是依值的，即依赖于 $Gamma$ 中的变量。这样看来，语境的解释才应该是集合，而类型解释为集合族。例如，空语境对应单元素类型，而语境扩展 $(Gamma, A)$ 可以解释为不交并 $product.co_(x in Gamma) A(x)$。另一方面，我们还需要区分语法与它们对应的解释。例如可以将 $Gamma$ 的解释记作 $interpret(Gamma)$。这样就能给出完整的集合模型：
- 语境 $Gamma$ 解释为集合，记作 $interpret(Gamma)$。
- 类型 $Gamma tack A istype$ 解释为集合族，记作 $interpret(A)_x$，其中 $x in interpret(Gamma)$。
- 空语境解释为单元素集合，即 $interpret(()) = {star}$。
- 语境扩展解释为不交并 $interpret((Gamma, A)) = product.co_(x in interpret(Gamma)) interpret(A)_x$。
- $Gamma tack t : A$ 解释为集合族 $interpret(A)$ 的元素族 $interpret(t)$。即对于每个 $x in interpret(Gamma)$ 都有 $interpret(t)_x in interpret(A)_x$。
- 变量代换 $Gamma tack sigma : Delta$ 解释为集合之间的函数 $interpret(Gamma) -> interpret(Delta)$。
- 从 $(Gamma, A)$ 到 $Gamma$ 的投影代换 $frak(p)$ 定义为 $(x, y) |-> x$，而变量 $Gamma, a:A tack a : A$ 解释为元素族 $interpret(a)_((x, y)) = y$。

我们可以按照直观写出各种类型在集合模型中的解释。读者只需熟记任何类型都是依值于语境的，即可轻松得到正确的写法。这样，对于任何表达式，例如 $lambda (x : NN) bind x + 1$，都能在集合里找到对应的元素解释。
- 单元素类型的解释为 $interpret(1)_x = {star}$，Boole类型的解释为 $interpret("Bool")_x = {"true", "false"}$。这两者都不依赖参数 $x in interpret(Gamma)$。
- 给定 $Gamma tack A istype$ 与 $Gamma, A tack B istype$，$Sigma$ 类型的解释为
  #eq($ interpret(Sigma A B)_x = product.co_(a in interpret(A)_x) interpret(B)_((x, a)) $)
  而 $Pi$ 类型则是将 $product.co$ 换为 $product$。
- 给定 $Gamma tack A istype$ 与两个元素 $Gamma tack s, t : A$，相等类型解释为
  #eq($ interpret("Id"(A, s, t))_x = cases(
    {star} quad & interpret(s)_x = interpret(t)_x \
    varnothing  & interpret(s)_x != interpret(t)_x
  ) $)
- 这些类型对应的元素，例如 $lambda$ 函数抽象、函数应用、有序对的配对与投影映射等等，读者可先行思考，稍后给出模型的定义后会再讨论。

== 语法模型

模型将语法解释为各种数学对象。但是语法本身也是一种数学对象，因此应当有一个平凡的模型，将每个表达式都解释为自身。换言之，我们需要确保模型的定义能让语法本身构成模型。

(nothing more to say here, demote to section 0)

== 依值类型论的自然模型

=== 定义

我们从上文讨论的直观里抽取出模型的一套定义。为了区分某个语法概念与它对应的语义解释，我们将语境的解释称作*语义语境*，类型的解释称为*语义类型*，以此类推。例如在集合模型中，语义语境的意思就是集合。不过，我们仍然会采用同样的字母指代这些对象，例如语法语境与语义语境都用 $Gamma, Delta, Theta$ 等字母表示，否则排版容易叠床架屋。

在 #[@sec:explicit-substitution]中，我们提到不应该将语境的长度视为本质属性，因此变量代换需要视作新的语法构造，而非在语法上递归定义的函数。在模型的定义中这样的好处是明显的：我们将表达式解释为数学对象之后，递归定义的代换就行不通了。因为两个语法上不同的表达式在模型中可能对应相同的数学对象，因此在这个模型中就不能靠递归定义这两个表达式的代换。但是，因为类型论的规则中用到了不少代换，所以我们需要在模型里额外添加代换的资料。

模型的定义大致与类型论的规则一一对应，其中关于代换的部分可以参考@fig:substitution。

#definition[
  依值类型论的#define[自然模型][natural model] 包含以下资料。
  - 有一类数学对象 $"Ctx"$，作为语境的解释，称作语义语境。
  - 给定两个语义语境 $Gamma, Delta$，有集合 $hom(Gamma, Delta)$ 作为代换的解释。其中的元素写作 $sigma : Gamma -> Delta$，称作语义代换。
  - 有恒等代换 $id : Gamma -> Gamma$ 与代换复合操作，给定 $sigma : Gamma -> Delta$ 与 $tau : Delta -> Xi$，给出 $tau compose sigma : Gamma -> Xi$。它们满足单位律与结合律。
  - 对于每个语义语境 $Gamma$，有集合 $"Tp"(Gamma)$ 作为类型的解释，其中的元素称作语义类型。
  - 对于每个语义语境 $Gamma$ 与语义类型 $A in "Tp"(Gamma)$，有集合 $"Tm"(Gamma, A)$，作为类型元素的解释，其中的元素称作语义元素。也可以不限定类型，给出所有元素的集合 $"Tm"(Gamma)$。
  - 对于语义类型 $A in "Tp"(Gamma)$ 与代换 $sigma : Delta -> Gamma$，有语义代换运算 $A sigma in "Tp"(Delta)$ —— 注意代换的方向 —— 满足 $A id = A$ 与 $A (sigma compose tau) = (A sigma) tau$。 因此我们将连续代换不加括号地写作 $A sigma tau$。
  - 对语义元素 $a in "Tm"(Gamma, A)$ 与代换 $sigma : Delta -> Gamma$，有语义代换运算 $a sigma in "Tm"(Delta, A sigma)$，满足 $a id = a$ 与 $a (sigma compose tau) = (a sigma) tau$。
  - 给定语义语境 $Gamma$ 与类型 $A in "Tp"(Gamma)$，有语境延拓运算 $(Gamma, A) in "Ctx"$，投影代换 $frak(p) : (Gamma, A) -> Gamma$ 与变量 $frak(q) in "Tm"((Gamma, A), A)$。
  - 给定语义代换 $sigma : Gamma -> Delta$、语义类型 $A in "Tp"(Delta)$ 与语义元素 $a in "Tm"(Gamma, A sigma)$，有代换延拓运算 $(sigma, a) : Gamma -> (Delta, A)$，并且它是唯一满足 $frak(p) compose (sigma, a) = sigma$ 与 $frak(q) (sigma, a) = a$ 的代换。
]
乍看之下模型的定义让人眼花缭乱，但读者浏览#[@ch:examples]中的例子后就会发现定义中大部分内容都会化作简单的概念，或者能显然给出，一般无需多虑。在#[@ch:category]中我们还会引入更多打包简化定义的办法。

Algebraic nature of models, generalized algebraic theories

=== 类型结构

不同的类型论会在以上的基础上添加各自的类型，因此在模型中也会相应的按照这些类型的规则定义类型结构。我们以几个常见的类型为例，展示这些类型结构的一般定义办法。

==== $Sigma$ 类型

==== $Pi$ 类型

==== 不交并

==== 自然数类型

==== 相等类型

=== 相容性与独立性

Consistency, consistency/independence of funext, UIP etc.

#translate[自洽][consistent], #translate[相容][consistent], #translate[独立][independent]，#translate[反模型][contermodel]

= 例海拾珠 <ch:examples>

构造模型的具体例子的思路实则非常简洁。我们先确定模型的核心对象，例如集合模型的核心自然是集合。然后，为了解释依值现象，我们提出某种 “依值对象”。对于集合而言，依值集合就是集合族。为了阐释这种思路，我们先来观察有向图构成的模型。这一例子没有什么实际应用，但是其中依值对象的构造应能启发读者。

观览有向图的例子后，我们再探究各类在数学与计算机科学中有用的模型。这些模型中用到的核心对象，不同背景的读者可能各自只熟悉一部分。为此，文章中会略作介绍，但是读者先跳过也无妨。

== 有向图

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

有向图的结构非常简单。
#definition[
  *有向图* $Gamma$ 包含如下资料：顶点集合 $V$ 与边的集合 $E$，配有两个函数 $s, t : E -> V$，分别给出一条边的两个顶点。如果 $x$ 是 $Gamma$ 的顶点，我们直接写作 $x in Gamma$。如果 $e$ 是 $Gamma$ 的边，满足 $s(e) = x$，$t(e) = y$，我们将其写作 $e : x -> y$。
]
这里有向图允许有自环和重边，在范畴论中也称作#define[箭图][quiver]。
#definition[
  给定两个有向图，其间的*同态*给出顶点到顶点、边到边之间的映射，保持边与顶点之间的连接关系。换言之，图同态 $sigma : Gamma -> Delta$ 对于所有边 $e : x -> y$，都满足 $sigma(e) : sigma(x) -> sigma(y)$.
]
若要用有向图构建模型，就需要定义依值有向图的概念。
#definition[
  给定有向图 $Gamma$，*依值有向图*包含如下资料：对于每个顶点 $x in Gamma$，有一族集合 $V_x$，对于每条边 $e : x -> y$，有一族集合 $E_e$，配有两个函数 $s : E_e -> V_x$ 与 $t : E_e -> V_y$。其中的元素写作 $epsilon : alpha xarrow(e) beta$.
]
不难看出，依值有向图就是依值集合 (即集合族) 的简单推广。

(...)

countermodel of excluded middle

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

(...)

== 容器与多项式 <sec:polynomial>

== 群胚

== 可计算性与模型

== 操作语义与模型

== 语法翻译

syntactic version of the exception model

== 语法性质的证明

(promote to own chapter?)

= 模型与范畴论 <ch:category>

- Necessity for naturality avalanche
- Beautiful handling of variable binding

== 自然模型的等价形式

CwF, natural model, discrete fibrations

== 展映射与概括范畴

== 融贯问题

(also mention universes in sheaf topos)

== 语法的泛性质

mention sconing and gluing

== 模型的函子观点

上村太一 (罗马字：Taichi Uemura)

== 变量的结构

= 模型与同伦论

== 相等类型与模型范畴

== Voevodsky 单纯集模型

== 立方模型

== 模型的同伦论

#show heading.where(level: 1): set heading(numbering: none)

= 术语翻译表
#columns(2)[
#set par(justify: false)
// #set text(size: 0.9em)
#context {
  let final = translation-table.final()
  let final = final.sorted(key : ((zh, en)) => en.text)
  for (zh, en) in final [
    / #zh: #en

  ]
}
]

// Bibliography
#[
#set text(lang: "en")
// #set par(justify: false)
#show link: set text(font: ("CMU Typewriter Text"), size: 0.9em)
#bibliography("references.yaml", title: "参考文献", style: "ieee-alt.csl") // TODO style
]
