#import "common.typ": *
= 前置知识

== 类型论拾遗 <sec:prelim-type-theory>

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
这些规则生成的最简结构就是类型论的语法。本文不会用到这些构造的细节，因此不再赘述。

如果将上文中的 $A in "Tp"(Gamma)$ 改写为 $Gamma tack A istype$，$a in "Tm"(Gamma, A)$ 改写为 $Gamma tack a : A$，并且将蕴涵关系 $==>$ 写作长横线，那么这些规则就化作逻辑学中熟悉的形式：
#eq(partir(
  $rule(Gamma tack A times B istype, Gamma tack A istype, Gamma tack B istype)$,
  $rule(Gamma tack (a,b) : A times B, Gamma tack a : A, Gamma tack b : B)$,
  $rule(Gamma tack pi_1 (a,b) = a : A, Gamma tack a : A, Gamma tack b : B)$
))
本文中所有这样的写法都应当视作与类似 $a in "Tm"(Gamma, A)$ 的写法等同。这种写法仅仅是为了遵循传统，并且或许更加易读，而没有额外的特殊含义。需要警示读者的是，并不是所有这样的长横线都可以做此解读，不同的范式中有不同的理解办法。

本文不在记号上区分判值相等与相等类型，只靠文字说明和上下文辨义。偶尔会将相等类型写作 $"Id"(A, x, y)$，含义相同。

=== 语境与代换 <sec:explicit-substitution>

代换的方向对初学者或许有些反直觉。例如假设 $Delta = (x : NN, y : NN)$ 与 $Gamma = (z : NN)$，那么 $sigma = [x \/ 3, y \/ f(z)]$ 乍看应当是从 $Delta$ 到 $Gamma$ 的代换。不过，如果 $Delta = (x : A)$ 与 $Gamma = (y : B)$ 都只有一个类型，那么代换 $sigma = [x \/ t]$ 就与从 $B$ 到 $A$ 的函数一一对应。因此我们将代换的方向写作 $Gamma -> Delta$，或者仿照元素的写法 $Gamma tack sigma : Delta$。

我们把空语境写作 $()$，空代换写作 $[]$。给定 $Gamma -> Delta$ 的代换 $sigma$，我们可以在 $Delta$ 中添加一个变量 $(Delta, x : A)$，那么代换也需要增加对新变量的代换结果，我们写作 $[sigma, x\/t]$。在不使用变量名的写法中，则写作 $[sigma, t] : Gamma -> (Delta, A)$。

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
这样，控制大小的功能就与宇宙为类型提供名字的功能独立了。这种办法称作 *Coquand 层级*。另外一个好处是，在这种情况下可以引入 $"El"$ 的逆运算，给定 $A istype_kappa$，给出它的一个名字 $ceil(A) : cal(U)_kappa$。Tarski 宇宙因为同时承担了控制大小与提供名字的功能，因此不能引入这种算符：$A istype$ 无法确定应该让 $ceil(A)$ 处在哪个宇宙中。这样还可以避免 Tarski 宇宙中分别引入类型构造子与 $cal(U)$ 元素的构造子的重复劳作。例如只需将 $A, B : cal(U)$ 的乘积定义为 $A dot(times) B = ceil("El"(A) times "El"(B))$ 即可。

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
  ) quad dots.c
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

程序员一般不太关心正规形式，因为程序的运行求值不会在有变量的环境下进行。例如 $lambda x bind x + (1 + 1)$ 在运行时不会计算为 $lambda x bind x + 2$，而是等到有参数输入后再进行计算。更狭义而言，只有一小部分 “基础” 类型能在运行时提供信息，例如 $"Bool"$ 类型或者自然数类型 $NN$。在无变量的情况下，这些类型的正规形式非常简单。例如 $"Bool"$ 类型只有 $"true"$ 与 $"false"$ 两个元素。这类表达式称作#define[典范形式][canonical form]。

== 范畴论筑基

本文采用的思路是尽可能晚引入范畴语言。不熟悉范畴的读者也可以跳过此节继续阅读。这一节对范畴论基础蜻蜓点水，同时也确定一些有歧义的记号的写法。

#definition[
  一个*范畴* $cal(C)$ 包含一些对象 $X, Y, Z, dots in "Obj"(cal(C))$，并且每个对象之间有集合 $hom(X, Y)$，其元素称作*态射*或者*箭头*，写作 $f : X -> Y$。态射之间有复合操作，将 $f : X -> Y$ 与 $g : Y -> Z$ 复合为 $g compose f : X -> Z$。这里复合的顺序与函数复合保持一致。复合满足结合律 $(h compose g) compose f = h compose (g compose f)$，并且每个对象都配有单位箭头 $id_X$，满足 $f compose id_X = f = id_Y compose f$。
]

- Diagrammatic reasoning

- Natural isomorphism chains

== 集合论撷英 <sec:set-theory>

// Doesn't work, try looking at wwli

依值类型论的模型不可避免涉及集合论与大基数的理论。例如直观上类型可以解释为集合，函数类型对应函数的集合，宇宙类型则是一定大小以内全体集合的集合。然而这是行不通的。例如在 ZFC 集合论中，就算限定集合只能包含一个元素，全体一元集也无法构成集合 #eq($ V_1 = {y mid(|) exists x bind y = {x}}. $) 假设不然，那么并集 $union.big V_1$ 按照公理也应该构成集合，但这恰好是全体集合的集合，在 ZFC 中是不能存在的。因此，我们需要发展一套理论，描述 “包含了足够多集合” 的集合。

倘若我们的元理论也是类型论，并且本身包含宇宙的概念，那么可以利用元理论中的宇宙解释宇宙。但是这样做往往不很方便，并且需要元理论的规则高度匹配。有轶事一则： Martin–Löf~@mltt-1971 曾提出一套类型论，其中有 $cal(U) : cal(U)$，是不自洽的。但是论文中给出了自洽性的证明，其中元理论中也有 $cal(U) : cal(U)$ 的宇宙规则!

在 ZFC 集合论中，给定基数 $kappa$，前面提到我们无法将全体元素个数少于 $kappa$ 的集合构成集合，这是因为尽管这些集合本身的大小有限制，但是它们的元素可以是任何别的集合，因此在数量上没有限制。假如我们要求不仅这些集合的元素个数少于 $kappa$，并且它们元素的元素个数也少于 $kappa$，元素的元素的元素等等都做如此要求，得到的东西称作#define(key: "hereditarily kappa-small set")[继承 $kappa$ 小集][hereditarily $kappa$-small set] $H_kappa$。例如，${varnothing, {varnothing}}$ 是继承有限集。可以证明 $H_kappa$ 构成集合。


- Strongly inaccessible cardinals and Grothendieck universes

- Set theory for category theory
