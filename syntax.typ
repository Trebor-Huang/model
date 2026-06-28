#import "common.typ": *
= 语法性质的证明 <ch:syntax>

本章我们运用模型证明语法的性质。

有一些关于语法的性质可以直接用语法本身证明。例如 $1 + 1 = 2 : NN$ 这个判值相等可以靠类型论的规则推导出来。另一方面，$"true" = "false" : Bool$ 判值相等则不能推导出来。这靠直接分析语法很难说明。此时就需要运用模型 (主要是@thm:soundness)。

#theorem[
  Martin-Löf 类型论无法推出 $tack "true" = "false" : Bool$。
]
#proof[
  考虑 #[@sec:set-model]中的集合模型。若可以推出 $tack "true" = "false" : Bool$，则由可靠性定理，集合模型中 $"true" = "false"$，矛盾。
]
读者须注意区分以下三者：
+ 无法推出 $tack "true" = "false" : Bool$，或写作 $cancel(tack) "true" = "false" : Bool$。
+ 相等类型 $"true" = "false"$ 没有元素，即 $"Tm"(1, "true" = "false") = nothing$。
+ 可以证明 $"true" != "false"$，即 $("true" = "false") -> Empty$ 有元素。
要证明第一个，需要构造模型使得 $"true"$ 与 $"false"$ 不相等; 要证明第二个，需要构造模型使得相等类型的解释中没有语义元素; 要证明第三个，只需要在类型论的语法中写出这样的元素。

== 典范性

典范性大致指的是空语境中某个类型的所有元素均可在判值相等意义下化为指定形式。例如 Boole 类型的典范形式是 $"true"$ 与 $"false"$。

#theorem[
  Martin-Löf 类型论中，任何表达式 $tack t : Bool$ 都要么满足 $tack t = "true" : Bool$，要么满足 $tack t = "false" : Bool$。
]

在集合模型中，的确有 $"Tm"(1, Bool) = {"true", "false"}$。这是否足以说明典范性呢? 直观来说，可靠性定理告诉我们语法中成立的事情在任何模型中也成立。取逆否命题就得到模型中不成立的事情在语法中不能成立。但这里我们希望证明语法中的判值相等_成立_，因此我们惯用的方法不管用了。可靠性定理的确为每个表达式 $tack t : Bool$ 选定了 $"true"$ 或 $"false"$，但是这并没有说明 $t$ 与所选的元素之间的判值相等关系。有可能存在两个表达式判值不相等，但均被解释为 $"true"$。

这样来看，我们需要在模型的构造中安装一些 “追踪器”，记录每个语义元素原本对应哪个语法元素。这种技巧就是#define[逻辑关系][logical relation]，也作 #translate[Tait 计算谓词][Tait computability predicate]。

=== 核算模型

#let sem(X) = $X^bullet$
#let syn(X) = $X^circle.small$
#let con(X) = $X^arrow.b$
先考虑无变量的情况：假如有类型 $A$，集合模型中解释为集合 $X$。我们只需添加函数 $p$，将 $X$ 的元素映射到 $A$ 的语法元素，得到三元组 $(X, A, p)$。这样，每个元素 $x in X$ 都携带了自己对应的语法元素 $tack p(x) : A$。我们将这三个组件分别称作*语义部分*、*语法部分*与*链接映射*。

不难得到依值类型的版本。定义*核算结构*为三元组 $(X, Gamma, sigma)$，其中 $X$ 是任意集合，$Gamma$ 是语法语境，$sigma : X -> hom(1, Gamma)$ 是一族代换。其上的依值核算结构为三元组 $(Y, A, p)$，其中 $Y$ 是 $X$ 上的集合族，$A$ 是 $Gamma$ 中的类型，而 $p_x : Y_x -> "Tm"(1, A sigma_x)$ 是一族函数，将集合的元素映射到语法元素。

我们构造新的模型，其中语境解释为核算结构，语义代换 $(X, Gamma, sigma) -> (X', Gamma', sigma')$ 是二元组 $(f : X -> X', phi : Gamma -> Gamma')$，构成交换方
  #eq(diagram($
    X edge("->", f) edge("d", "->", sigma) & X' edge("d", "->", sigma') \
    hom(1, Gamma) edgeR("->", delta |-> phi compose delta) & hom(1, Gamma')
  $))
语义类型是依值核算结构。而某个依值核算结构 $(Y, A, p)$ 的语义元素形如有序对 $(y, t)$，其中 $y$ 是语义部分的元素族，即 $y_x in Y_x$，$t$ 是语法部分的元素 $Gamma tack t : A$，满足判值相等 $p_x (y_x) = t sigma_x$ 表示链接映射下语义部分正确对应了语法部分。
语境扩展的语法、语义部分分别使用了语法与集合模型的语境扩展定义：
#eq($ (X, Gamma, sigma) dot (Y, A, p) = (product.co_(x in X) Y_x, thick Gamma dot A, thick (x, y) |-> [sigma_x, p_x]). $)

==== $Bool$ 类型
我们需要在核算结构 $(X, Gamma, sigma)$ 上定义 $Bool$ 类型结构。其语义部分为常集合族 ${"true", "false"}$，与集合语义相同。语法部分自然是 $Bool$，而链接映射 ${"true", "false"} -> "Tm"(1, Bool)$ 将集合的元素 $"true"$ 映射到表达式 $"true"$，将 $"false"$ 映射到 $"false"$。

==== $Sigma$ 类型
给定核算结构 $(X, Gamma, sigma)$，依值结构 $(Y, A, p)$ 与其语境扩展下的依值核算结构 $(Z, B, q)$，定义其 $Sigma$ 类型结构 $(W, C, r)$ 满足
#eq($
  W_x &= product.co_(y in Y_x) Z_((x, y)) \
  C &= Sigma A B \
  r_x (y, z) &= (p_x (y_x), q_((x, y_x)) (z_((x, y_x))))
$)
不难发现语义部分 $W$ 与集合语义中的定义也相同，并且链接映射对两个分量分别作用。

==== $Pi$ 类型
与 $Sigma$ 类型类似，其中语法部分显然应该改为 $Pi A B$，但语义部分则略微复杂。$W_x$ 定义为有序对 $(F, f)$ 的集合，其中 $F in product_(y in Y_x) Z_((x, y))$，而 $f in "Tm"(Gamma dot A, B)$ 是语法元素，使得 $F$ 与 $f$ 有对应关系。具体来说，当 $p_x (y) = t$ 时，有 $q_((x, y))(F(y)) = f[sigma_x, t]$。

不能直接将 $W_x$ 定义为集合中的函数集，是因为有许多函数不能被语法表达 (语法只有可数多元素，而如 $NN -> NN$ 的函数集不可数)，并且那些可以被表达的函数往往有多种表达 (如 $ite(b, "true", "false")$ 与恒等函数在集合语义中相等，但是没有判值相等)。因此，为了保证每个函数都对应一个语法上的函数，需要将 $W_x$ 定义为集合函数与语法函数的有序对。此时链接映射 $r_x (F, f)$ 显然定义为 $f$ 即可。

==== 宇宙类型
有了上述例子，读者应当不难类似构造别的类型结构。唯一较困难的是宇宙类型。暂时忽略集合大小问题，核算结构 $(X, Gamma, sigma)$ 下的宇宙类型，语法部分显然是语法的宇宙 $cal(U)$。而语义部分的集合族为 #eq($ V_x = {(Y, A, p) mid(|) #[$Y$ 是集合，$Gamma tack A : cal(U)$，$p : Y -> "Tm"(1, "El"(A) sigma_x)$]}. $) 链接映射将 $(Y, A, p)$ 映射到 $A$。这样，宇宙类型的（语义）元素能给出一个语义类型。读者可尝试证明宇宙类型对各种类型构造子封闭。

对于集合大小的问题，只需要在集合模型中引入 $H_kappa$ 宇宙，然后将 $V_x$ 定义中的集合 $Y$ 修改为 $H_kappa$ 的元素即可。

=== 典范性的证明

#proof[
  根据可靠性定理，可以得到从语法到核算模型的解释。观察核算模型的定义，用归纳法可以证明，将某个语法对象解释为语义对象，再取回语法部分，与最初的语法对象相同。

  给定表达式 $tack t : Bool$，其解释为 $(y, t')$。由前文讨论得 $t' = t$，而按照定义有 $y in {"true", "false"}$，并且当 $y = "true"$ 时 $t' = "false"$，当 $y = "false"$ 时 $t' = "true"$。无论哪种情况，都有 $t$ 与 $"true"$ 或 $"false"$ 判值相等。
]

=== 依值模型

- dependent elimination, displayed models and gluing

== 正规性

- direct construction of the mode
  - Tracking elements are equipped with renaming action
  - Presheaf of normal and neutral forms
- algorithmic content and decidability of judgmental equality (of well-typed terms)
  - This gives decidability of typechecking, but is tricky
- judgmental injectivity of type constructors

== 参数性
- Discuss models of system F?
- distinguish syntactic and set-semantic parametricity
