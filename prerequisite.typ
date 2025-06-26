#import "common.typ": *
= 前置知识

== 类型论拾遗 <sec:prelim-type-theory>

阅读本文，读者自然需要对依值类型论有基础的了解。例如 $Sigma$ 与 $Pi$ 类型的规则，读者应当胸有成竹。同样，如果读者希望阅读同伦类型论相关的章节，就需要对同伦类型论有了解，反之则跳过也不影响阅读。

本文不会花费过多笔墨讨论变量的处理。我们在公式中一般直接使用具名变量，但是 $lambda x. x$ 与 $lambda y. y$ 直接视作等同，不加额外说明。对于#translate[语境][context] 而言，如果希望强调其不依赖变量名的属性，可能将 $(Gamma, x:A)$ 写作 $(Gamma, A)$。为了方便书写，我们也将 $Sigma$ 类型写成 $(x : A) times B(x)$，与非依值的 $A times B$ 对应。同理 $Pi$ 类型写成 $(x : A) -> B(x)$。在无变量名的写法中则作 $Sigma A B$ 与 $Pi A B$。

依值类型论的定义中，往往先定义不考虑类型的表达式集合，称作#translate[原始表达式][raw term]，再定义类型规则剔除类型不合的表达式，并给出#translate[判值相等][judgmental equality] 关系。这样可以得到一系列集合
#eq($"Ctx" quad "Tp"(Gamma) quad "Tm"(Gamma, A)$)
分别代表类型正确的语境、类型与元素表达式，_商去判值相等后_构成的集合。其中 $Gamma in "Ctx"$, $A in "Tp"(Gamma)$。我们几乎永远不会考虑不商去判值相等的表达式。不过，如果可以从一开始就确保类型的正确性，在数学处理上会更加优雅。这可以由归纳定义的办法构造。

自然数的归纳构造办法是定义 $NN$ 为满足 $0 in NN$ 与 $n in NN ==> "suc"(n) in NN$ 的最小集合。在集合论中，可以将这里的 “最小” 严格定义成所有满足条件的集合的交。在类型论#sym.zwj#footnote[自然，这里的类型论是#translate[元理论][metatheory]，与我们正在定义的类型论不相同。]中，这可以实现为归纳类型。对于表达式而言，归纳构造办法稍微复杂一些，例如有
#eq($
  A,B in "Tp"(Gamma) &==> (A times B) in "Tp"(Gamma)\
  a in "Tm"(Gamma, A), quad b in "Tm"(Gamma,B) &==> (a, b) in "Tm"(Gamma, A times B) \
  a in "Tm"(Gamma, A), quad b in "Tm"(Gamma,B) &==> pi_1 (a, b) = a.
$)
这些规则生成的最简结构就是类型论的语法。本文不会用到这些构造的细节，因此不再赘述。

如果将上文中的 $A in "Tp"(Gamma)$ 改写为 $Gamma tack A istype$，$a in "Tm"(Gamma, A)$ 改写为 $Gamma tack a : A$，并且将蕴涵关系 $==>$ 写作长横线，那么这些规则就化作逻辑学中熟悉的形式：
#eq(partir(
  $rule(Gamma tack A times B istype, Gamma tack A istype, Gamma tack B istype)$,
  $rule(Gamma tack (a,b) : A times B, Gamma tack a : A, Gamma tack b : B)$,
  $rule(Gamma tack pi_1 (a,b) = a : A, Gamma tack a : A, Gamma tack b : B)$
))
本文中所有这样的写法都应当视作与类似 $a in "Tm"(Gamma, A)$ 的写法等同。这种写法仅仅是为了遵循传统，并且或许更加易读，而没有额外的特殊含义。需要警示读者的是，并不是所有这样的长横线都可以做此解读，不同的范式中有不同的理解办法。

本文不在记号上区分判值相等与相等类型，只靠文字说明和上下文辨义。偶尔会将相等类型写作 $"Id"(A, x, y)$，含义相同。@appendix:identity 中收集了相等类型的一些性质。

=== 语境与代换 <sec:explicit-substitution>

代换的方向对初学者或许有些反直觉。例如假设 $Delta = (x : NN, y : NN)$ 与 $Gamma = (z : NN)$，那么 $sigma = [x \/ 3, y \/ f(z)]$ 乍看应当是从 $Delta$ 到 $Gamma$ 的代换。不过，如果 $Delta = (x : A)$ 与 $Gamma = (y : B)$ 都只有一个类型，那么代换 $sigma = [x \/ t]$ 就与从 $B$ 到 $A$ 的函数一一对应。因此我们将代换的方向写作 $Gamma -> Delta$，或者仿照元素的写法 $Gamma tack sigma : Delta$。

给定 $Gamma -> Delta$ 的代换 $sigma$，我们可以在 $Delta$ 中添加一个变量 $(Delta, x : A)$，那么代换也需要增加对新变量的代换结果，我们写作 $[sigma, x\/t]$。在不使用变量名的写法中，则写作 $[sigma, t] : Gamma -> (Delta, A)$。我们把空语境写作 $()$，空代换写作 $[]$。

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
      Gamma tack [] : ()
    )$,
    $rule(
      Gamma tack sigma = [] : (),
      Gamma tack sigma : ()
    )$,
    // Context extension
    $rule(
      Gamma tack [sigma, t] : (Delta, A), 
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
      Gamma tack frak(p) compose [sigma, t] = sigma : Delta,
      Gamma tack sigma : Delta,
      Delta tack A istype,
      Gamma tack t : A sigma
    )$,
    $rule(
      Gamma tack frak(q) [sigma, t] = t : A sigma,
      Gamma tack sigma : Delta,
      Delta tack A istype,
      Gamma tack t : A sigma
    )$,
    // eta
    $rule(
      Gamma tack sigma = [frak(p) compose sigma, frak(q) sigma] : (Delta, A),
      Delta tack A istype,
      Gamma tack sigma : (Delta, A),
    )$
  )
)<fig:substitution>

=== 类型与宇宙 <sec:universe-hierarchy>

依值类型论的核心在于冒号左侧的表达式可以出现在冒号的右侧。这个特性使得在依值类型论的实现中往往在语法上对冒号左右两侧（元素与类型）不做区分，即二者都属于表达式。不过在理论上，将两者的语法类别分开可以让各种概念更加干净清晰。例如在语法上，如果 $M, N$ 是元素表达式，$A$ 是类型表达式，那么 $"Id"(A,x,y)$ 就是类型表达式。在 $Gamma tack M : A$ 中，$M$ 必须是元素表达式，而 $A$ 必须是类型表达式。

粗略地说，#define[宇宙][universe] 是类型的类型。不过这个说法有两个不准确之处。第一，宇宙一般只是一些类型的类型，不会覆盖全部的类型。第二，宇宙的元素实际上是类型的_名字_，而非类型本身。类型的名字属于元素表达式，而不属于类型表达式。在语法上额外有一个构造 $"El"$，将类型的名字 $A : cal(U)$ 转化为类型表达式 $"El"(A) istype$。除了类型构造子
#eq($ rule(Gamma tack A times B istype, Gamma tack A istype, Gamma tack B istype) $)
之外，为了表达宇宙在这些类型构造子下封闭，还会引入宇宙内的版本
#eq($ rule(Gamma tack A dot(times) B : cal(U), Gamma tack A : cal(U), Gamma tack B : cal(U)) $)
满足 $"El"(A dot(times) B) = "El"(A) times "El"(B) istype$。这种处理宇宙的办法名字是 *Tarski 宇宙*。不区分类型的名字与类型的做法称作 *Russell 宇宙*。可以认为 Russell 宇宙只是在工程上较为方便，在理论上应该作为 Tarski 宇宙的简写法理解。

我们也可以干脆不使用类型构造子 $times$，只引入宇宙中的 $dot(times)$。这样做的好处是可以让类型构造子不覆盖所有宇宙。例如可以引入两个宇宙，其中只有一个包含函数类型。

#let convert = math.class("unary", sym.arrow.t)
依值类型论中往往有多重宇宙，它们主要的功能之一是控制类型的大小。这里需要区分的是宇宙之间的#translate[累积][cumulation] 关系与元素关系。*元素关系*是说存在大宇宙的一个元素 $U_1 : cal(U)_2$，使得 $"El"(U_1) = cal(U)_1$ 是小宇宙。 Russell 宇宙下可以写作 $cal(U)_1 : cal(U)_2$。*累积关系*在 Russell 宇宙下是说低层级的类型可以直接当作高层级的类型使用。这看似只是一种语法糖，但是它实际上蕴涵了非平凡的判值相等关系。在 Tarski 宇宙下，累积性是指有算符 $convert$ 将低层宇宙的元素变为高层宇宙的元素，使得#footnote[不同的宇宙理论上应当使用不同的 $"El"$ 算符，例如写作 $"El"_(cal(U)_1)$ 与 $"El"_(cal(U)_2)$。这里略去。] $"El"(convert A) = "El"(A) istype$
成立，即这两个名字指代的是同一个类型。它还需要满足 #eq($ Gamma tack convert(A dot(times) B) = (convert A)dot(times) (convert B) : cal(U)_2 $) 等等式。换句话说，不同宇宙之间的类型构造子选取需要互相兼容。

元素关系与累积关系是互相独立的，即两两组合一共有四种可能性。

控制大小也可以无需宇宙。可以依靠多个类型判断 $Gamma tack A istype_kappa$ 表示类型的不同大小，其中 $kappa$ 是控制大小的层级参数。换句话说，我们选择多个集合 $"Tp"_kappa (Gamma)$ 与对应的元素 $"Tm"_kappa (Gamma, A)$。类型论的各种规则都可以添加层级标记，例如
#eq($
  rule(Gamma tack A -> B istype_max{kappa, lambda}, Gamma tack A istype_kappa, Gamma tack B istype_lambda) quad
  rule(Gamma tack cal(U)_kappa istype_(kappa^+)).
$)
这样，控制大小的功能就与宇宙为类型提供名字的功能独立了。这种办法称作 *Coquand 层级*。另外一个好处是，在这种情况下可以引入 $"El"$ 的逆运算#footnote[这里只有 $"El"(ceil(A)) = A istype_kappa$ 是要紧的，$ceil("El"(A)) = A : cal(U)_kappa$ 可不加。]，给定 $A istype_kappa$，给出它的一个名字 $ceil(A) : cal(U)_kappa$。Tarski 宇宙因为同时承担了控制大小与提供名字的功能，因此不能引入这种算符：$A istype$ 无法确定应该让 $ceil(A)$ 处在哪个宇宙中。这样还可以避免 Tarski 宇宙中分别引入类型构造子与 $cal(U)$ 元素的构造子的重复劳作。例如只需将 $A, B : cal(U)$ 的乘积定义为 $A dot(times) B = ceil("El"(A) times "El"(B))$ 即可。

宇宙的另一大问题是#translate[非直谓][impredicative] 宇宙，见#[@appendix:impredicative]的讨论。

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
      Gamma tack Bool isnf istype
    )$,
    $rule(
      Gamma tack "true" : Bool isnf
    )$,
    $rule(
      Gamma tack "false" : Bool isnf
    )$,
    $rule(
      Gamma tack ite(b, s, t) : A[x\/b] isne,
      Gamma\, x : Bool tack A istype,
      Gamma tack b : Bool isne,
      Gamma tack s : A[x\/"true"] isnf,
      Gamma tack t : A[x\/"false"] isnf,
    )$,
    // Variable
    $rule(
      Gamma tack t : Bool isnf,
      Gamma tack t : Bool isne
    )$,
    $rule(
      Gamma tack x : A isne,
      Gamma tack x : A isvar
    )$,
    // TODO
  )
)<fig:normal-form>

注意@fig:normal-form 中，一条规则是 Boole 类型的中性形式都是正规形式。严格来说，这在正规形式的递归定义中应该写成构造子 $iota : "Ne"(Gamma, Bool) -> "Nf"(Gamma, Bool)$，但是我们写作隐式转换。另外，因为没有写出宇宙的规则，所以无法构造类型变量，故暂时不存在任何中性类型。宇宙满足大体规则格式如下，其中宇宙 $cal(U)$ 只包含乘积类型为例。
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
在 Coquand 宇宙中，则不需要为类型名字的运算各自添加规则，只需以下三条。
#eq($
  rule(
    Gamma tack cal(U) isnf istype
  ) quad
  rule(
    Gamma tack "El"(A) isne istype,
    Gamma tack A : cal(U) isne
  ) quad
  rule(
    Gamma tack ceil(X) : cal(U) isnf,
    Gamma tack X isnf istype
  )
$)

代换 $Gamma tack sigma : Delta$ 也可以规定正规形式，直观上说 $sigma = [x_1 \/ t_1, x_2 \/ t_2, ...]$ 是正规形式当且仅当每个 $t_i$ 都是正规形式。严格来说可以写成如下规则：
#eq($
  rule(Gamma tack [] : () isnf) quad
  rule(
    Gamma tack [sigma, t] : (Delta, A) isnf,
    Gamma tack sigma : Delta isnf,
    Gamma tack t : A sigma isnf
  ).
$)
也可以同理定义 $Gamma tack sigma : Delta isne$。这些规则中还用到了 $Gamma tack x : A isvar$ 的写法，其意义自明。而若有代换 $Gamma tack sigma : Delta isvar$，即每一项都是变量，我们就称 $sigma$ 是#define[更名][renaming] 代换。

程序员一般不太关心正规形式，因为程序的运行求值不会在有变量的环境下进行。例如 $lambda x bind x + (1 + 1)$ 在运行时不会计算为 $lambda x bind x + 2$，而是等到有参数输入后再进行计算。更狭义而言，只有一小部分 “基础” 类型能在运行时提供信息，例如 $Bool$ 类型或者自然数类型 $NN$。在无变量的情况下，这些类型的正规形式非常简单。例如 $Bool$ 类型只有 $"true"$ 与 $"false"$ 两个元素。这类表达式称作#define[典范形式][canonical form]。

== 范畴论筑基

本书采用的思路是尽可能晚引入范畴语言，因此推荐不熟悉范畴的读者跳过此节继续阅读。这一节对范畴论基础蜻蜓点水，同时也确定一些有歧义的记号的写法。

#definition[
  一个*范畴* $cal(C)$ 包含一些对象 $X, Y, Z, dots in "Obj"(cal(C))$，并且每个对象之间有集合 $hom(X, Y)$，其元素称作*态射*或者*箭头*，写作 $f : X -> Y$。态射之间有复合操作，将 $f : X -> Y$ 与 $g : Y -> Z$ 复合为 $g compose f : X -> Z$。这里复合的顺序与函数复合保持一致。复合满足结合律 $(h compose g) compose f = h compose (g compose f)$，并且每个对象都配有单位箭头 $id_X$，满足 $f compose id_X = f = id_Y compose f$。
] <def:category>

例如，集合与集合之间的函数构成范畴 $Set$。各种数学对象都可以类似地构成范畴。
在数学中有许多只用态射之间的复合关系就能表达的事物。它们都可以直接表述为范畴论中的一般概念。例如集合的双射、代数结构的同构、拓扑空间的同胚，都可以用范畴语言表达：
#definition[
  假如有箭头 $f : X -> Y$ 与 $g : Y -> X$ 满足 $f compose g = id_Y$ 与 $g compose f = id_X$，那么就说 $f$ 是*同构*，而 $g$ 是其*逆态射*。
]

范畴中论证的一大组成就是#translate[追图][diagram chasing]。这类似初等平面几何学中的#translate[倒角][angle chasing]，即在复杂的图形中利用一系列性质给出角度的连等式。例如，同构的逆态射总是唯一的，或者以下定理，都是利用追图证明的。证明留给读者。
#theorem[
  给定三个映射
  #eq($ X xarrow(f) Y xarrow(g) Z xarrow(h) W, $)
  如果 $g compose f$ 与 $h compose g$ 都是同构，那么图中所有的映射都是同构。
]

范畴中大部分概念都以#translate[泛性质][universal property] 的形态出现。对于范畴论初学者来说，泛性质的格式是要求某个图表中存在唯一一个态射满足某些等式。以乘积为例。

#definition[
  给定范畴 $cal(C)$ 中的两个对象 $X$、$Y$，假设有对象 $Z$ 与态射 $pi_1 : Z -> X$、$pi_2 : Z -> Y$ 使得对于任何别的对象 $Z'$ 与态射 $f : Z' -> X$ 和 $g : Z' -> Y$，都有唯一的箭头 $(f, g) : Z' -> Z$ 使得 $pi_1 compose (f, g) = f$，$pi_2 compose (f, g) = g$。此时称 $(Z, pi_1, pi_2)$ 构成 $X$ 与 $Y$ 的*乘积*。
]
例如，集合之间的 Descartes 乘积 $X times Y = {(x, y) mid(|) x in X, y in Y}$ 构成范畴论意义的乘积。
泛性质的重要特征是保证了定义的唯一性。
#theorem[
  给定两个对象 $X$ 与 $Y$ 之间的两个乘积 $(Z, pi_1, pi_2)$ 与 $(Z', pi'_1, pi'_2)$，存在唯一的同构 $f : Z -> Z'$ 满足 $pi'_i compose f = pi_i$。
]
#proof[
  利用 $(Z, pi_1, pi_2)$ 的泛性质，可以得到箭头 $g : Z' -> Z$ 满足 $pi_i compose g = pi'_i$。同理利用 $(Z', pi'_1, pi'_2)$ 的泛性质也可以得到箭头 $f : Z -> Z'$ 满足 $pi'_i compose f = pi_i$。两者复合得到箭头 $f compose g$ 满足 #eq($ pi'_i compose f compose g = pi_i compose g = pi'_i. $) 另一方面，恒等映射 $id : Z' -> Z'$ 也满足 $pi'_i compose id = pi'_i$，但是泛性质保证了这样的映射的唯一性，所以 $f compose g = id$。同理 $g compose f = id$，所以 $f$ 构成同构。
]
初学者务必注意此唯一性定理的具体叙述。有了唯一性，我们可以记 $X$ 与 $Y$ 的乘积为 $X times Y$。它满足定理如 $(X times Y) times Z$ 同构于 $X times (Y times Z)$ 等等，都可以依靠泛性质追图证明。

范畴之间的映射关系是函子。

#definition[
  给定范畴 $cal(C)$ 与 $cal(D)$，*函子* $F$ 包括对象之间的映射 $"Obj"(cal(C)) -> "Obj"(cal(D))$ 与箭头之间的映射 $hom(X, Y) -> hom(F(X), F(Y))$，满足 $F(id_X) = id_(F(X))$ 与 $F(f compose g) = F(f) compose F(g)$。
] <def:functor>

粗略来说，利用某个数学对象构造新的数学对象，往往都构成合适范畴之间的函子。有时候，我们希望构造箭头方向相反的函子，即将 $X -> Y$ 的箭头映射到 $F(Y) -> F(X)$ 的箭头。这称作#define[反变][contravariant] 函子。不过，我们可以避免额外做此定义。只需要考虑范畴 $cal(C)^"op"$，即将 $cal(C)$ 中的箭头方向反转得到的心范畴，即可将反变函子定义为 $cal(C)^"op" -> cal(D)$ 的普通函子。

函子之间还有更高一级的映射关系。

#definition[
  给定函子 $F, G : cal(C) -> cal(D)$，*自然变换* $alpha$ 为每个对象 $X in "Obj"(cal(C))$ 赋予箭头 $alpha_X : F(X) -> G(X)$，使任何 $cal(C)$ 中的箭头 $f : X -> Y$ 都有等式 $G(f) compose alpha_X = alpha_Y compose F(f)$。换言之，以下方形交换。
  #eq(diagram($
    F(X) edge(->, F(f)) edge(->, "d", alpha_X) & F(Y) edgeL(->, "d", alpha_Y) \
    G(X) edgeR(->, G(f)) & G(Y)
  $))
] <def:natural-transform>

不难看出有恒等自然变换 $id : F -> F$，并且两个自然变换 $F -> G$ 与 $G -> H$ 可以复合。这意味着固定两个范畴 $cal(C)$ 与 $cal(D)$，它们之间的函子构成另一个范畴，写作 $[cal(C), cal(D)]$。如果自然变换的每个箭头都是同构，那么每个箭头分别取逆可以得到另一个自然变换。此时称其为*自然同构*。换句话说，这是函子范畴中的同构。

本书不是范畴论教材，因此不详细讨论这些概念的直观。但是值得一提的是，自然同构可以给出泛性质的另一种理解方式，在实践中非常方便。
#theorem[
  两个对象的乘积与以下定义等价：$X$ 与 $Y$ 的乘积是一个对象 $Z$ 配备自然同构 $hom(-, Z) tilde.equiv hom(-, X) times hom(-, Y)$。
]
这里，$hom(-, X)$ 表示函子 $F(W) = hom(W, X)$，是从 $cal(C)^"op"$ 到 $Set$ 的函子。本质上说，泛性质描述的是某些箭头之间有双射关系，因为泛性质定义中的 “唯一” 与 “存在” 分别对应单射与满射。自然性则保证了这样的双射与箭头之间的复合操作兼容。我们趁机定义指数对象的概念。指数对象是对函数集合的范畴论抽象。它也可以用图表风格的语言定义，但是比较繁琐。
#definition[
  给定对象 $X$ 与 $Y$，*指数对象* $X^Y$ 是配备了自然同构 $hom(-, X^Y) tilde.equiv hom(- times Y, X)$ 的对象.
]

一般而言，泛性质有一半可以写成某个对象 $X$ 配备自然同构 $hom(-, X) tilde.equiv F(-)$，其中 $F$ 是从 $cal(C)^"op"$ 到 $Set$ 的函子。另一半则是对偶地描述 $hom(X, -) tilde.equiv F(-)$，这里 $F : cal(C) -> Set$。换言之，我们描述指向 $X$ 的箭头或者从 $X$ 出发的箭头，从而定义对象 $X$。这种定义的合理性是由以下引理保证的。

#lemma[米田#footnote[罗马字为 Yoneda。]][
  给定对象 $X in "Obj"(cal(C))$ 与函子 $F : cal(C)^"op" -> Set$，定义 $yo(X)$ 为函子 $hom(-, X)$，则集合 $F(X)$ 与自然变换 $yo(X) -> F$ 的集合构成双射。特别地，$yo(X) -> yo(Y)$ 的自然变换与箭头 $X -> Y$ 的集合构成双射。
] <lemma:yoneda>

米田引理保证了，只要描述指向 $X$ 的箭头，就能完全确定 $X$ 本身。具体来说，一套这样的描述就是一个函子 $F : cal(C)^"op" -> Set$。因此我们可以认为这样的函子是某种虚构的 “广义对象”。它描述了某个对象如果存在的话会有哪些箭头指向它。我们将这种函子称作 $cal(C)$ 上的*预层*，其构成的函子范畴称作预层范畴 $Psh(cal(C))$。$yo$ 则构成了 $cal(C) -> Psh(cal(C))$ 的含入函子，将原范畴嵌入到广义对象的范畴中。如果预层 $F$ 自然同构于某个 $yo(X)$，就说 $F$ 是#define[可表][representable] 预层。

这样的视角可以将许多追图证明变为颇具代数风格的连等式计算。要证明两个对象 $X$ 与 $Y$ 同构，只需要说明 $yo(X)$ 与 $yo(Y)$ 自然同构，而它们的泛性质又可以允许我们将它们展开成别的预层进行计算。

== 集合论撷英 <sec:set-theory>

// 假设读者了解基数的基本定义。基数是度量集合元素个数的数学对象。例如每个自然数都是有限基数，而 $aleph_0$ 描述了全体自然数的数量，$frak(c)$ 表示全体实数的数量，等等。以下谈到的基数都指无限基数。

=== 基数

bijections and cardinals

cardinal arithmetic

=== 序数

well-founded orders

well orders

(the aleph series = well-founded cardinals)

=== 大基数理论

依值类型论的模型不可避免涉及集合论与大基数的理论。例如直观上类型可以解释为集合，函数类型对应函数的集合，宇宙类型则是一定大小以内全体集合的集合。然而这是行不通的。例如在 ZFC 集合论中，就算限定集合只能包含一个元素，全体一元集也无法构成集合 #eq($ V_1 = {y mid(|) exists x bind y = {x}}. $) 假设不然，那么并集 $union.big V_1$ 按照公理也应该构成集合，但这恰好是全体集合的集合，在 ZFC 中是不能存在的。因此，我们需要发展一套理论，描述 “包含了足够多集合” 的集合。

倘若我们的元理论也是类型论，并且本身包含宇宙的概念，那么可以利用元理论中的宇宙解释宇宙。但是这样做往往不很方便，并且需要元理论的规则高度匹配。有轶事一则： Martin-Löf~@mltt-1971 曾提出一套类型论，其中有 $cal(U) : cal(U)$，是不自洽的，但是论文中却给出了自洽性的证明。其罪魁祸首在于元理论中也有 $cal(U) : cal(U)$ 的宇宙规则，本身就是不自洽的!

在 ZFC 集合论中，给定基数 $kappa$，前面提到我们无法将全体元素个数少于 $kappa$ 的集合构成集合，这是因为尽管这些集合本身的大小有限制，但是它们的元素可以是任何别的集合，因此在数量上没有限制。假如我们要求不仅这些集合的元素个数少于 $kappa$，并且它们元素的元素个数也少于 $kappa$，元素的元素的元素等等都做如此要求，得到的东西称作#define(key: "hereditarily kappa-small set")[继承 $kappa$ 小集][hereditarily $kappa$-small set] $H_kappa$。例如，${varnothing, {varnothing}}$ 是继承有限集。可以证明 $H_kappa$ 构成集合。

在集合模型中，为了让宇宙在 $Sigma$ 类型、$Pi$ 类型等等构造下封闭，我们需要 $H_kappa$ 对一系列集合上的操作封闭。这对 $kappa$ 的大小提出了要求。例如，$Sigma$ 类型直观上要求如果 $A in H_kappa$，并且 $B : A -> H_kappa$ 是一族集合，那么 $product.co_(x in A) B(x)$ 也属于 $H_kappa$。转换为基数的语言，这意味着如果有少于 $kappa$ 个小于 $kappa$ 的基数，它们的和也小于 $kappa$。这种基数在集合论中称作*正则基数*。类似地，对于 $Pi$ 类型，则是将 $product.co$ 替换为 $product$。这样得到的基数称作*强不可达基数*。请读者证明 $aleph_0$ 是强不可达基数。

假如存在强不可达基数 $kappa$，那么 $H_kappa$ 就能构成 ZFC 的模型，故而意味着 ZFC 是自洽的。由 Gödel 不完备性定理，这意味着 ZFC 不可能证明强不可达基数的存在性.#footnote[除非 ZFC 本身有矛盾，不过那样天就塌了。] 这是合理的。例如 Lean 定理证明助手中可以形式化 ZFC 的模型 @lean-con-ch，因此某种意义上说 Lean 的类型论比 ZFC 要强。然而，依值类型论的模型的研究重点并不是讨论各种理论的证明论强度，而在于可计算性、同伦论、程序语义等等。因此，我们不会取 ZFC 为元理论，而是添加足够强的大基数假设，使得我们能专注于对模型其他性质的研究。

在类型论中，往往需要一系列宇宙 $cal(U)_0, cal(U)_1, cal(U)_2, dots$，因此仅仅假设一个强不可达基数是不够的。为此，我们采用以下公理，为我们提供足够多的强不可达基数。
#thmstyle("theorem", "公理")("Tarski–Grothendieck")[
  对于任何基数 $lambda$，都存在强不可达基数 $kappa > lambda$。
] <ax:tarski-grothendieck>
这样，任何集合都包含在某个 $H_kappa$ 中。我们可以从 $aleph_0$ 出发，反复用@ax:tarski-grothendieck 取出更大的强不可达基数，构成一列 $kappa_0 < kappa_1 < dots.c$ 用来给类型论中的宇宙提供模型。
