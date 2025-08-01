#import "common.typ": *
= 非直谓宇宙 <appendix:impredicative>

非直谓性在逻辑学和哲学中概念比较模糊，没有统一的定义。在类型论的语境中，非直谓性则具体指代函数类型 (或者 $Pi$ 类型) 所处的宇宙满足的规则。就一般直觉而言，假如类型 $A$ 在宇宙层级 $kappa$ 中，而 $B$ 在层级 $lambda$ 中，那么函数类型 $A -> B$ 应该取其大者，即 $max{kappa, lambda}$。但是，如果某个宇宙层级是*非直谓*的，那么只要陪域 $B$ 在此层级中，任何函数类型 $A -> B$ 就也处在此层级中。

具体来说，用 Tarski 宇宙描述的规则是
#eq($
  "直谓："
  rule(
    Gamma tack A dot(->) B : cal(U)_max{kappa, lambda},
    Gamma tack A : cal(U)_kappa,
    Gamma tack B : cal(U)_lambda
  )"，非直谓："
  rule(
    Gamma tack A dot(->) B : cal(U)_lambda,
    Gamma tack A : cal(U)_kappa,
    Gamma tack B : cal(U)_lambda
  ),
$)
其中 $dot(->)$ 是函数类型在宇宙中的名字。也可以用 Coquand 层级，避免涉及类型名字的问题，即
#eq($
  "直谓："
  rule(
    Gamma tack A -> B istype_max{kappa, lambda},
    Gamma tack A istype_kappa,
    Gamma tack B istype_lambda
  )"，非直谓："
  rule(
    Gamma tack A -> B istype_lambda,
    Gamma tack A istype_kappa,
    Gamma tack B istype_lambda
  ).
$)
假如宇宙的层级结构比较复杂，比如有互相不能比较大小的层级，那么非直谓性需要根据具体情况定义。

从数学家的视角来看，非直谓宇宙乍看是完全荒谬的，或者仅存在于奇异的逻辑系统中。但是，一般的数学中也有这样的现象。假如 $cal(U)_lambda$ 只包含*命题*，即 $Empty$ 与 $Unit$ 这些所有元素都相等的类型，那么这就显得合理了。$1$ 的多少次方都等于 $1$，同理无论类型 $A$ 有多大，$A -> Unit$ 都只有一个元素。这一点在集合论中也有体现：无论多少个集合相交，得到的仍然是集合而不是真类，其中交集的定义是
#eq($
  inter.big X = { y mid(|) forall (x in X) bind y in x},
$)
这里的 $forall$ 就对应类型论中的 $Pi$ 类型，而 $X$ 可以是真类。某种意义上，这是主流数学中能见到的非直谓宇宙的唯一例子。

编程中，非直谓性就有更多用途。例如 F 系统中可以用非直谓类型定义自然数
#eq($
  NN = forall X bind (X -> X) -> (X -> X).
$)
这样自然数 $n$ 可以编码为输入 $f : X -> X$，输出将 $f$ 复合 $n$ 次得到 $f^(compose n)$ 的函数。这种技巧可以将复杂的抽象 —— 例如函数式编程的透镜 —— 转化为函数上的操作，进而允许编译器做更好的优化。但是这样的类型在数学上看意义就不太显然，我们在 #[@sec:impredicative-universe]会详细讨论其中一个解释办法。

另外需要提及的是，有一些类型系统，如 F 系统等，习惯包含一种可以取遍全体类型的 “大 $Pi$ 类型”，可以写作 $product_(A istype) P(A)$.#footnote[也可以按照 F 系统的习惯写作 $forall$，但是这与逻辑中的 $forall$ 并不相同。后者等同于满足 $P(x)$ 都是命题的 $Pi$ 类型 $Pi x bind P(x)$，与定义域无关。] 这意味着需要有另一种语境扩展 $(Gamma, A istype)$，能引入类型变量。为了与一般的类型论相比较，我们可以利用宇宙将这种系统等价改写成不含类型变量的类型论。只需要引入宇宙 $cal(U)$ 包含原系统的所有类型，并将原先的 $A istype$ 改做 $A : cal(U)$ 即可。注意类型构造子的改写，例如乘积类型
#eq($
  rule(
    Gamma tack A dot(times) B : cal(U),
    Gamma tack A : cal(U),
    Gamma tack B : cal(U)
  ),
$)
由于 $cal(U) : cal(U)$ 不成立，因此 $A$ 和 $B$ 都不能取值为 $cal(U)$ (或者用 Tarski 宇宙的说法，$cal(U)$ 中不存在元素构成 $cal(U)$ 自身的名字)。这样 $cal(U)$ 就只能单独构成一个类型，不能组合成更复杂的类型表达式，保证了与原系统的等价性。改写之后容易看出，这种 $Pi$ 类型也是非直谓性的一种体现，因为 $product_(A:cal(U)) P(A)$ 的定义域是 $cal(U)$ —— 注意不是定义域为 $A : cal(U)$，而是定义域就是 $cal(U)$ 本身，也就是宇宙层级比原系统中的所有类型都高 —— 但所处的宇宙仍然是 $cal(U)$，比直谓性要求的要低一层。

== 构造演算与其变体 <sec:calculus-of-constructions>

=== 定义

#translate[构造演算][calculus of constructions] 是一种只有 $Pi$ 类型与宇宙的类型论。在文献中常被缩写为 CoC，早期文献也作 CC。读者或许知道这类类型系统被 Barendregt 称作#define[纯类型系统][pure type system]，并且构造演算的子系统构成一个立方体，称作 $lambda$ 立方。我们_不认为_这是合适的分类。其中的宇宙有一些表现得比较反直觉，只是为了凑齐规律而添加的。它在某些方面分类过于细致，而在另一些方面则不够精细。特别是希望以此为基础添加 $Sigma$ 类型或者更复杂的结构时，无法用纯类型系统的框架描述各种变体。读者可以参阅 Bart Jacobs~@on-cubism 对纯类型系统的批评。

利用 Coquand 层级，可以定义*构造演算*为含有 $istype$ 与 $istype_*$ 两个层级的类型论，使得 $istype_*$ 与宇宙 $*$ 有 $"El"$ 和 $ceil(-)$ 的转换操作，而 $istype$ 没有对应的宇宙。同时，构造演算对 $Pi$ 封闭，并且 $istype_*$ 非直谓。@fig:coc-rules 中有部分规则。

如果认为构造演算是编程语言的类型系统，那么一般称 $*$ 为 $"Set"$，因为程序所操作的类型直观上是集合。不在 $*$ 中的类型则称作#translate[种类][kind]，属于编程语言中#translate[类型体操][type gymnastics] 所操作的事物。但如果认为构造演算是逻辑系统，就称 $*$ 为 $"Prop"$，认为其元素是命题。这是因为上文所讲的，在主流数学中唯一存在的非直谓宇宙就是命题构成的宇宙。

#numbered-figure(caption: [构造演算的规则])[
  #partir(
    $$,
    $rule(
      Gamma tack "El"(A) istype_*,
      Gamma tack A : *
    )$,
    $rule(
      Gamma tack ceil(A) : *,
      Gamma tack A istype_*
    )$,
    $rule(
      Gamma tack "El"(ceil(A)) = A istype_*,
      Gamma tack A istype_*
    )$,
    $$,
    $rule(
      Gamma tack Pi A B istype_j,
      Gamma tack A istype_i,
      Gamma\, A tack B istype_j
    ) quad (i,j in {*, diameter})$,
  )
] <fig:coc-rules>

一般认为构造演算的 $istype_*$ 与 $istype$ 之间没有累积性，但是添加累积性似乎对表达能力没有什么影响。

=== 构造演算用例 <sec:coc-usage-examples>

本节省略宇宙的 $"El"$ 与 $ceil(-)$ 记号。

构造演算的重要性质是可以用非直谓性编码各种数据类型与逻辑谓词。例如与 F 系统中一样可以定义自然数
#eq($
  NN = (X : *) -> (X -> X) -> (X -> X).
$)
这样，自然数 $n$ 可以编码成 $lambda X f x bind f(f( dots f (x)))$，其中 $f$ 应用 $n$ 次。自然数的加法就是 $n + m = lambda X f x bind n X f (m X f x)$，先应用 $n$ 次，再应用 $m$ 次。这样可以写出许多自然数上的程序。

至于逻辑，可以定义真命题为 $top = (X : *) -> X -> X$，它有唯一的元素 $lambda X x bind x$，假命题则是 $bot = (X : *) -> X$，没有元素。命题的合取与析取分别是
#eq($
  p and q &= (X : *) -> (p -> q -> X) -> X \
  p or q &= (X : *) -> (p -> X) -> (q -> X) -> X.
$)
还能利用 Leibniz 原理定义元素的相等命题。给定 $x, y : A$，有
#eq($
  "Id"(A, x, y) = (P : A -> *) -> P(x) -> P(y).
$)
这说的是任何对 $x$ 成立的命题，对 $y$ 也成立。尽管看似不对称，但它的确构成等价关系。

依值类型论中除了 $Pi$ 类型外，另一个重要类型就是 $Sigma$ 类型。不过，非直谓编码无法构造出完整的 $Sigma$ 类型，区别在于消去子。为此我们先作术语辨析。弱消去子为
#eq($
  rule(
    Gamma tack "elim"(p, Q) : C,
    Gamma tack p : (a : A) times B(a),
    Gamma tack C istype,
    Gamma \, a : A \, b : B tack Q : C
  ).
$)
注意 $C$ 不能依赖于 $p$。这意味着无法靠弱消去子取出 $Sigma$ 类型的第二分量，因为其类型不能匹配。强消去子则允许 $C$ 依赖于 $p$，即
#eq($
  rule(
    Gamma tack "elim"(p, Q) : C(p),
    Gamma tack p : Sigma A B,
    Gamma\, p : Sigma A B tack C(p) istype,
    Gamma \, a : A \, b : B tack Q : C(a, b)
  ).
$)
极强消去子则由两个投影函数 $pi_1$ 与 $pi_2$ 构成，也就是通常所说的 $Sigma$ 类型。我们往往还会限制弱消去子与强消去子中类型 $C$ 所处的宇宙层级。如果 $C$ 可以处于任何层级，那么极强消去子与强消去子可以互相推导。另一方面，如果同时存在两个 $Sigma$ 类型，一强一弱，那么二者同构。但是只有弱 $Sigma$ 类型时无法构造出强 $Sigma$ 类型。

利用非直谓宇宙，可以编码弱 $Sigma$ 类型，即
#eq($
  (x : A) times P(x) = (C : *) -> ((x : A) -> P(x) -> C) -> C.
$)
注意这里限制了 $C$ 只能处于非直谓宇宙 $*$ 中，并且 $Sigma$ 类型也在 $*$ 里。如果 $A = *$，那么与 F 系统中的 $forall$ 类推，也将这种弱 $Sigma$ 类型称作 $exists$ 类型。事实上，如果加入非直谓强 $exists$ 类型 $(exists X bind P(X)) : *$，并且具备投影函数 $(exists X bind P(X)) -> *$，那么系统就有矛盾 @impredicative-sigma。这说明非直谓宇宙是无法编码这种类型的。但是，这并不排除可以编码 $A$ 与 $B$ 都在 $*$ 宇宙中的 $Sigma$ 类型 $(x : A) times B(x)$。我们将在 #[@sec:impredicative-universe]证明也这是不可能的。

与 $Sigma$ 类型类似，归纳类型的非直谓编码也只能构造弱版本。这对一般编程而言足矣，但要作为逻辑系统，就必须要有完整的归纳法。假设读者已熟悉归纳类型的大致原理，下文只将探讨这些类型与非直谓宇宙的交互。

=== 宇宙层级

构造演算只有一个宇宙，有时显得有些捉襟见肘。一个自然的想法是添加无限多个层级 $istype_i$ 与对应的宇宙 $*_i$，使得 $tack *_i istype_(i+1)$。这样，所有的类型都在某个宇宙之中有名字。

对于 $Pi$ 类型，由于构造演算中的规则是
#eq($
  rule(
    Gamma tack Pi A B istype_j,
    Gamma tack A istype_i,
    Gamma\, A tack B istype_j
  ),
$)
最直观的想法是直接将其套用在新增的层级上。这样，就有无限多层非直谓宇宙。不过，这样得到的类型论是有矛盾的。Girard 发现，只要两个非直谓宇宙之间有元素关系，类型论就有矛盾。这就是 Girard 悖论，在@sec:girard-paradox 有详细讲述。

#let imax = math.op("imax")
既然更高的宇宙不能是非直谓的，我们只好将其定为直谓宇宙。回忆对于直谓宇宙层级而言有规则
#eq($
  rule(
    Gamma tack Pi A B istype_max{i, j},
    Gamma tack A istype_i,
    Gamma\, A tack B istype_j
  ).
$)
这样，如果要将最底层宇宙（即 $i = 0$，有些文献也定作 $i = -1$）改为非直谓的，就只需要将 $max{i,j}$ 改为 $imax(i, j)$，定义为
#eq($
  imax(i, j) &= cases(
    0 & (j = 0),
    max{i, j} quad & (j != 0)
  ).
$)
此类型论在文献中记作 $"CC"_omega$，没有固定名称。这些直谓宇宙一般写作 $"Type"_i$。

这么修改之后，还有没有矛盾呢? 我们只需找到一个模型。根据前文的讨论，我们可以在集合模型中试将最底层的类型解释为至多有一个元素的集合。这样，无论多少个这样的集合取 $Pi$ 类型，得到的结果都还是只有一个元素，不会导致悖论。

不过，这么做有一些困难。理论上宇宙 $*$ 应该只有两个元素，空集和单元素集，但是单元素集不只一个。事实上，根据 #[@sec:set-theory]的讨论， $V_1 = {x mid(|) exists y bind x = {y}}$ 是真类。一个想法是强行选定一个单元素集 $1 = {varnothing}$，但是这样与 $Pi$ 类型的构造不兼容。

集合模型中将 $Pi$ 类型解释为集合乘积 $product_(x in A) B(x)$。具体展开定义后，这种集合的元素 $f$ 形如 $f = {(a_1, b_1), (a_2, b_2), ...}$，是有序对的集合，记录了每个 $a in A$ 应当映射到什么元素。如果 $B(x)$ 都只有一个元素，那么 $product_(x in A) B(x)$ 也只有一个元素，但是这个元素本身内部还有许多元素，结构非常复杂。因此如果将宇宙 $*$ 定为只有两个元素，那么它就不能对 $Pi$ 类型封闭。
#let coerce = math.class("unary", sym.arrow.t)
为此，我们可以再修改 $Pi$ 类型的定义。如果陪域满足 $tack B istype_*$，那么 $Pi A B$ 就根据 $B$ 是否总有元素定义为空集 $varnothing$ 或者某个固定的单元素集 (例如${varnothing}$)。如果 $tack B istype_i$ $(i > 1)$，那么就按照一般的办法解释为集合的乘积。这样的确可以构造出 $"CC"_omega$（包括构造演算）的模型。

不过，此时累积性就不成立：临时用 $coerce A$ 显式写出从 $istype_*$ 到 $istype_1$ 的转换，那么这个集合模型中 $coerce(Pi A B) istype_1$ 与 $Pi (coerce A) (coerce B) istype_1$ 就不相等。前者是 ${varnothing}$，而后者是 ${{(x, varnothing) mid(|) x in A}}$，虽然都有一个元素，但是后者有很多元素的元素。

一方面，我们可以接受此事。从 Curry–Howard 对应的角度来看，这就相当于认为非直谓宇宙 $"Prop"$ 的 $forall$ 命题与直谓宇宙的 $Pi$ 类型并不完全是同一种东西，而是只有同构关系。另一方面，我们也可以修改集合模型中函数的编码。不将 $f$ 编码为 ${(x, f(x)) mid(|) x in A}$，而是编码为 ${(x, u) mid(|) x in A, u in f(x)}$。注意由于 ZF 集合论中一切对象都是集合，$f(x)$ 也可以看作集合，因此 $u in f(x)$ 是合法的。

再者，#[@sec:realizability-model]中介绍的模型也满足累积性。不过与集合模型不同，它不满足排中律。

由于我们有时候将最底层的非直谓宇宙看作 $"Prop"$，而有时看作 $"Set"$，出于实用考虑我们也可以将其一分为二。换句话说，可以考虑两个非直谓宇宙，都在最底层且没有元素关系，一个称为 $"Prop"$，一个称为 $"Set"$。这不会导致矛盾，因为对于该类型论的任何表达式，将 $"Prop"$ 与 $"Set"$ 均替换为 $*$ 之后，得到的就是 $"CC"_omega$ 中的合法表达式，所以如果一者有矛盾，另一者就一定有矛盾。

在现代视角下，Curry–Howard对应应当将命题解释为至多有一个元素的类型，而非全体类型。这样，每个宇宙 $cal(U)$ 都能导出一个子类型
#eq($ "hProp"_cal(U) = (A : cal(U)) times (forall x, y : "El"(A) bind x = y) $)
表示其中的命题，我们临时记作 $"hProp"$ 以示区分。另一方面，在构造演算的集合模型中，$"Prop"$ 宇宙下的类型的确至多有一个元素，但这并不能在构造演算或者 $"CC"_omega$ 中得证.（事实上， #[@sec:realizability-model]给出的模型就是反模型.）因此，二者有许多相似之处，但不完全相同。

我们自然可以向 $"Prop"$ 添加公理，要求该宇宙中的所有类型都至多有一个元素。这称作#define[证明无关性][proof irrelevance]。也可以向 $"hProp"_cal(U)$ 添加公理增加非直谓性，例如要求 $"hProp"_cal(U) tilde.eq "hProp"_(cal(U)')$ 对任何两个宇宙 $cal(U)$ 与 $cal(U)'$ 都成立。这样取直谓 $Pi$ 类型抬升了宇宙层级之后总可以通过此等价降回来。有若干定理给出 $"Prop"$ 与 $"hProp"$ 分别添加对应的公理之后是等价的。

=== 归纳类型

前面已经提到，自然数类型可以靠非直谓宇宙编码为
#eq($ NN = (X : *) -> (X -> X) -> (X -> X). $)
这个编码已经足够定义常见的递归函数。列表与二叉树类型也有对应的非直谓编码。
#eq($
  "List"(A) &= (X : *) -> (A -> X -> X) -> (X -> X) \
  "Tree" &= (X : *) -> X -> (X -> X -> X) -> X \
  A + B &= (X : *) -> (A -> X) -> (B -> X) -> X.
$)
因此，构造演算可以满足纯函数式编程的大部分需求。

然而从编程的视角看，非直谓编码有两个重要的缺陷。第一是递归函数的值域必须在同一个非直谓宇宙中。第二是没有依值递归，也即归纳法。前面提到非直谓编码 $Sigma$ 类型的问题也是其体现。因此我们考虑在 $"CC"_omega$ 中额外添加归纳类型作为#translate[原语][primitive]。例如自然数类型 $NN : *$ 有两个构造子 $"zero" : NN$ 与 $n : NN tack "suc"(n) : NN$，还有消去子
#eq($
  rule(
    Gamma tack "elim"_P (k, z, s) : P(k);
    Gamma tack k : NN,
    Gamma\, n : NN tack P(n) istype,
    Gamma tack z : P("zero");
    Gamma\, n : NN\, p : P(n) tack s : P("suc"(n))
  )
$)
注意这里完全不限制 $P$ 所处的宇宙，也没有任何对非直谓宇宙的特殊处理。

从逻辑的视角看，认为 $*$ 是命题宇宙，第一个缺陷则不成立。假设 $p != q$ 是直谓宇宙中类型的元素，对 $x : A + B$ 分类讨论，如果 $A$ 成立输出 $p$，$B$ 成立则输出 $q$。$A$ 与 $B$ 同时成立就导致 $p = q$，矛盾。从这个角度看，对于命题宇宙的归纳类型，其消去子的值域本身就应该限制在命题宇宙中。不过第二个缺陷，即依值递归的问题仍然存在。因此将 $"CC"_omega$ 作为逻辑系统时，添加归纳类型需要作出限制：如果归纳类型在 $*$ 中，那么消去子的值域类型也需要在 $*$ 中。

当然，如果某个归纳类型显然只有至多一个元素，那么不限制消去子也不会导致上述问题。这些归纳类型包括空类型 (假命题)、单位类型 (真命题)、乘积类型 (且命题)、相等类型、#translate[可达谓词][accessibility predicate] 等。

最后，归纳类型的宇宙大小一般由其包含的其它类型所处的宇宙决定。例如 $"List"(A)$ 与 $A$ 处于同一宇宙。但是，非直谓编码下可以将任何类型压缩到非直谓宇宙中去。考虑
#eq($ norm(A) = (X : *) -> (A -> X) -> X. $)
那么 $norm(A) : *$，相当于逻辑命题 “$A$ 有元素”。这类似于命题截断类型，但是将同伦类型论中的命题修改为命题宇宙中的类型。这种归纳类型无论从编程视角还是逻辑视角都应该限制其消去子的值域，否则会导致悖论。

以上提到的各种归纳类型可以总结如下：
- 非直谓编码的类型，在构造演算或者 $"CC"_omega$ 中就已存在，无需额外规则。
- 在直谓宇宙中添加归纳类型，直接按照正常的规则添加即可。
- 在非直谓宇宙中也按照正常的规则添加，没有额外限制的归纳类型，临时称作大归纳类型 (这不是标准术语)。
- 如果在非直谓宇宙中添加的归纳类型，限制消去子也只能在同一个宇宙中，临时称作小归纳类型。
- 大归纳类型有一部分从语法上可以显然判定至多有一个元素，称作亚单元素类型。
- 以上类型所处的宇宙都是按照自然的规则计算的，如果强行要求某个本该处于更高宇宙的归纳类型加入非直谓宇宙，称作压缩类型。其消去子限制在同一个宇宙中。
如果将类型论视作编程语言，那么可以添加直谓归纳类型、大归纳类型与压缩类型。如果将类型论视作逻辑系统，那么可以添加直谓归纳类型、小归纳类型、亚单元素的大归纳类型，以及压缩类型。

== 寓言一则

起初，构造演算的村子里有一个非直谓宇宙。人们用它可以构造各种各样的类型。有些人编写程序，有些人构造证明，生活十分幸福。

后来，人们觉得一个宇宙不够用，想要造更多的宇宙。但是，Girard 告诉他们，这些新的宇宙不能是非直谓的，不然就会倒塌。于是人们搭了一座塔，只有最底层的宇宙是非直谓的，其余的宇宙是直谓宇宙。这样，村子改名叫做 $"CC"_omega$。

再后来，大家发现用非直谓宇宙构造的 $NN$ 类型定义的递归函数 $NN -> A$ 必须满足 $A$ 在最底层的宇宙中。编写程序的人们对此很不满意，于是商量着建起了归纳类型。这样，非直谓宇宙里的归纳类型 $NN$ 也可以消去至任何宇宙中的类型。村子也改名叫做构造归纳演算。

另一边，构造证明的人们想要使用经典逻辑，于是引入了排中律与选择公理。但是，这引来了灾难。地底沉睡的怪物苏醒了，呼啦一下摧毁了村子。这只怪物叫做 Berardi 悖论。在有排中律与选择公理时，$A : "Prop"$ 的所有元素都必须相等。这就让 $NN$ 这样的类型无处藏身。

为了击败怪物，人们决定将编写程序与构造证明分开。他们将原本的非直谓宇宙分成两个，一个叫做 $"Prop"$，另一个叫做 $"Set"$。人们把 $"Prop"$ 宇宙中的归纳类型消去子限制到 $"Prop"$ 宇宙中，而将 $"Set"$ 宇宙的非直谓性移除。这样就将怪物的力量封印了。//不过，在 $"Prop"$ 宇宙中的归纳类型也有一些例外。例如单元素类型、空类型等等，它们所有的元素原本就相等，因此不需要限制它们的消去子。

大家把重建的村子称作直谓构造归纳演算，这就是 Coq/Rocq 定理证明器的由来。

== 悖论三则

=== 朴素集合论的悖论 <sec:paradoxes-naive>

Russell 悖论是集合论中最广为人知的悖论。它说明了并不是所有属性 $P$ 都能用于构成集合 ${x mid(|) P(x)}$。只消考察集合 $R = {x mid(|) x in.not x}$。

先来说明 $R in.not R$：要证明某个命题的否定，只需要假设此命题并推出矛盾.#footnote[这是命题否定的基本性质，不属于反证法，因此没有用到排中律。] 假设 $R in R$，那么因为 $R$ 的元素都不属于自身，那么要使 $R$ 是 $R$ 的元素，就必须满足 $R in.not R$，矛盾。以上证明了 $R in.not R$，但这又意味着 $R$ 是 ${x mid(|) x in.not x}$ 的元素，而后者恰好就是 $R$ 的定义。因此 $R in R$ 也成立。

上面的论证说明了，假如能构造集合 ${x mid(|) x in.not x}$，那么它就既是自己的元素，又不是自己的元素。要解决这个悖论，只需要修改集合论，将论证中的某一步消除即可。注意这不能靠_添加_公理解决，因为添加公理不会使原先成立的证明变得不成立，因此越添加公理，矛盾的可能性只会越大。ZFC 集合论就将构造任意集合 ${x mid(|) P(x)}$ 的办法删去，替换成数条更弱的构造集合的办法。

如果类型论中有宇宙满足 $cal(U) : cal(U)$，那么也可以照搬 Russell 悖论。不过其中的构造比较精巧，因为需要定义递归类型，使得集合的元素是别的集合，即构成树状结构。具体来说，考虑
#eq($
  VV = product_(X:cal(U)) [product_(A:cal(U)) (A -> X) -> X] -> X.
$)
这是 #[@sec:coc-usage-examples]中提到的非直谓编码的例子。只要给定一族集合 $f : A -> VV$，就能构造新的集合 ${f(a) mid(|) a : A} : VV$，定义为
#eq($
  lambda X bind lambda F bind F A (lambda a bind f a X F).
$)
其中，对集合 $R$ 的定义必须要用到 $Sigma$ 类型，即先定义 $Delta = sum_(x : VV) x in.not x$，再定义 $R = {pi_1 (r) mid(|) r : Delta}$。
读者可以在证明助理中开启 $cal(U) : cal(U)$ 的功能 (例如在 Agda 中是 `--type-in-type`)，形式化该证明。

Martin-Löf 在 1971 年提出了最早的 Martin-Löf 类型论，其中有 $cal(U) : cal(U)$ 的规则，看上去可以照搬 Russell 悖论导出矛盾。但是这个类型论不含 $Sigma$ 类型。论文中写作 $Sigma$ 的类型是用 $Pi$ 作非直谓编码的弱 $Sigma$ 类型。因此 Russell 悖论并不能直接套用。1972 年，Girard 才发现这个系统不自洽，见@sec:girard-paradox.//事实上，Martin-Löf在论文中证明了它是自洽的，但是由于证明的元理论本身满足 $VV in VV$，所以实际上元理论也有矛盾。

在 Russell 悖论之前，在朴素集合论中就发现了一系列类似的矛盾，Russell 悖论只是其中最简洁的一个。例如 Cantor 最著名的定理说的是任何集合 $X$ 的元素个数都要严格比幂集 $cal(P)(X)$ 少。但是，如果有全体集合的集合 $VV$，它理应是元素数量最大的集合，因此 $abs(VV) < abs(cal(P)(VV))$ 不应该成立。这是 *Cantor 悖论*。事实上，将 Cantor 定理的证明展开化简之后，这条悖论就会化作 Russell 悖论。

除了基数以外，对序数的研究中也产生了类似的悖论。Cantor 证明了任意序数之间都可相互比较，即 $alpha < beta$、$alpha = beta$ 与 $alpha > beta$ 三者必居其一。但数学家 Burali-Forti 在 1897 年又证明了存在不可比较的序数! 他的论证是如果所有序数都可比较，那么全体序数的集合也是良序集 $"No"$，就应该构成最大的序数 $Omega$。但这是不可能的，因为 $Omega + 1 > Omega$。这就是 *Burali-Forti 悖论*。

这则悖论可以做一些简化，避免用到序数的全套理论。例如可以只用良基关系 (@def:well-founded)。假如良基集合 $A$ 与 $B$ 的某个真子集同构，就说 $A < B$。这样全体良基集合的集合 $"WF"$ 也是良基的。进一步分析可以得到 $"WF" < "WF"$，矛盾。这是 *Мириманов 悖论*。还可以定义无挠序的概念：
#definition-appendix[
  如果全序集 $A$ 满足任何子集 ${x in A mid(|) x < a_0}$ 与 $A$ 本身没有保序同构，就说 $A$ 是*无挠*的。这种子集称作 $A$ 的#define[前段][initial segment]。
]
全体无挠序的集合构成全序集 $"TF"$，任何无挠序都同构于 $"TF"$ 的某个前段。但 $"TF"$ 本身又是无挠的，因此它同构于自己的某个前段，故不是无挠的，矛盾。

=== Girard 悖论 <sec:girard-paradox>
#let Uminus = $"U"^-$

1972年，逻辑学家 Jean-Yves Girard (注意不是哲学家 René Girard) 在博士论文~@girard-paradox 中研究了一类用于表达高阶逻辑的类型论，其中只包含 $Pi$ 类型与不同的宇宙层级。在附录中，他提出了这些类型论的一种自然推广，起名为 U 系统，并且证明了这个系统是不自洽的。

如果将这个系统中的所有宇宙层级视作相同，那么 U 系统就化作前文提到 Martin-Löf 的 $cal(U) : cal(U)$ 系统，因此前者的所有证明都可以直接照搬到后者。这就说明了该类型论不自洽。有些材料将类型论中的 Russell 悖论也混同于 Girard 悖论，但二者实则不尽相同。前者因为能够使用 $Sigma$ 类型，逻辑更加简单。

粗略而言， U 系统就是对 $Pi$ 类型封闭，并且有两个非直谓宇宙的类型论，使得两个宇宙 $*$ 与 $square$ 有元素关系。也可以认为有三个层级 $istype_*$、$istype_square$ 与 $istype$。由于 Girard 悖论中并不会用到所有宇宙层级之间的 $Pi$ 类型，所以实际的 U 系统还删去了一部分不需要的 $Pi$ 类型规则。

Girard 在 U 系统中将 Burali-Forti 悖论的简化版本 (即利用无挠序的版本) 形式化，证明了 U 系统中类型 $bot = (X : *) -> X$ 有元素。它自然不可能有正规形式，因为 $bot$ 没有正规元素。因此这也说明 U 系统不满足正规化。Coquand 在 1986 年另给出一版本，利用了良基关系的悖论。这一悖论用到的 $Pi$ 类型种类更少，因此删去不需要的规则之后得到 #Uminus 系统也是不自洽的。

1995 年，Hurkens 再进一步给出了简化。由于这一版本已经非常不同，而且极其简短，有时改称其为 *Hurkens 悖论*。这利用了非直谓性编码一个集合 $X$，满足 $X$ 与其双重幂集 $(X -> *) -> *$ 有双射。Hurkens 的论文~@hurkens-paradox 中讨论了这一系列悖论的演化。

尽管 U 系统不自洽，无法作为逻辑系统使用，但它的所有类型都可正规化，因此类型检查仍然是可判定的。与之相反，$cal(U) : cal(U)$ 的系统中类型检查不可判定。另外，所有这些系统都仍是#define[等式自洽][equationally consistent] 的，即并非所有表达式都判值相等。

=== Berardi 悖论 <sec:berardi-paradox>

在构造演算中，如果将 $"Prop"$ 中的类型视作命题，那么形式化经典逻辑时不免需要假定排中律与选择公理。Berardi 悖论说的是这些假设可以推出证明无关性，即 $p : "Prop"$ 总是满足 $(x, y : p) -> x = y$。这意味着不能将最底层宇宙的类型同时视作命题和集合，因为集合应当可以有多个不同的元素。

回忆我们可以用非直谓宇宙编码逻辑连词，如
#eq($
  top &= (X : "Prop") -> X -> X \
  bot &= (X : "Prop") -> X \
  not p &= p -> bot \
  p and q &= (X : "Prop") -> (p -> q -> X) -> X \
  p or q &= (X : "Prop") -> (p -> X) -> (q -> X) -> X \
  (forall x : A bind p(x)) &= (x : A) -> p(x) \
  (exists x : A bind p(x)) &= (X : "Prop") -> ((x : A) -> p(x) -> X) -> X \
  "Id"(A, x, y) &= (P : A -> "Prop") -> P(x) -> P(y) \
  // norm(A) &= (X : "Prop") -> (A -> X) -> X
$)
这里 $A$ 可以是任意类型，而 $p$ 与 $q$ 需要在 $"Prop"$ 宇宙中。这样，排中律就是
#eq($ "EM" : (p : "Prop") -> (p or not p). $)
选择公理则有多种说法。

一般的选择公理说的是，给定类型族 $B(x) istype$ 与谓词 $P : (x : A) -> B(x) -> "Prop"$，如果命题 $forall (x : A) bind exists (y : B(x)) bind P(x, y)$ 成立，那么就存在函数在每个 $B(x)$ 中选出一个元素，即
#eq($ exists (f : (x : A) -> B(x)) bind forall (x : A) bind P(x, f(x)). $)
如果类型论中有 $Sigma$ 类型，可以将 $B$ 与 $P$ 合并成类型族 $C(x) = sum_(y : B(x)) P(x, y)$。这样选择公理化为非常对称的形式
#eq($ ((x : A) -> norm(C(x))) -> norm((x : A) -> C(x)). $)
在同伦类型论中，这个形式更为常见。不过 $"CC"_omega$ 没有 $Sigma$ 类型，因此需要用上面的复杂形式。

在（有 $Sigma$ 类型的）类型论中，全局选择#footnote[这与集合论的全局选择只有形似，因为 ZF 等集合论的真类与类型论中的性质差异很大。]则说的是将选择公理结论中的 $exists$ 换做 $Sigma$，或者 $norm(A)$ 换做 $A$。这样不仅存在选择函数，还能给出固定的一个选择函数。例如从 $forall (x : A) bind exists (y : B(x)) bind P(x, y)$ 可以推出
#eq($ sum_(f : (x : A) -> B(x)) forall (x : A) bind P(x, f(x)). $)
这等价于说
#eq($ ((x : A) -> norm(C(x))) -> (x : A) -> C(x). $)
它实际上等价于更简洁的公理：$norm(A) -> A$。

不过，在无 $Sigma$ 类型的类型论中无法作出这样的化简，因此需要拆分成两步。有算符 $epsilon$，给定谓词 $P$ 满足 $forall (x : A) bind exists (y : B(x)) bind P(x, y)$，给出函数 $f : (x : A) -> B(x)$。再有公理说明 $f$ 满足 $P(x, f(x))$ 总是成立。

#theorem-appendix[Barbanera–Berardi][
  在构造演算中假定排中律与全局选择公理，则任何命题 $p : "Prop"$ 的所有元素相等，即 $"Id"(p, x, y)$ 有元素。
]
#proof[
可以用非直谓宇宙编码 $Bool$ 类型为 $(X : "Prop") -> X -> X -> X$。其中 $"true"$ 和 $"false"$ 分别返回第一个与第二个参数。分类讨论算符 $ite(b, x, y)$ 在非直谓编码下就是 $b p x y$。注意这里 $x$ 与 $y$ 的类型必须一致。

要找到两个元素不相等的类型，最显然的办法就是考虑 $Bool$。事实上，假如 $"true"$ 与 $"false"$ 相等，那么任何 $p : "Prop"$ 的元素 $x, y : p$ 都两两相等，这意味着只需要考虑 $Bool$ 即可。具体证明是注意到 $ite("true", x, y) = x$ 而 $ite("false", x, y) = y$，因此如果有 $omega : "Id"(Bool, "true", "false")$，则 $omega(lambda b bind "Id"(p, x, ite(b, x, y)))("refl"(x))$ 就证明了 $"Id"(p, x, y)$.#footnote[这个证明无法说明更高宇宙中的类型元素都相等，例如对 $X : "Type"_2$ 的元素就不适用。这是因为 $Bool$ 的非直谓编码中 $X$ 只能取值于 $"Prop"$ 宇宙，因此 $ite(b, x, y)$ 只能是命题宇宙中的类型的元素。]

将函数类型 $X -> Bool$ 也记作 $Bool^X$，类比（经典逻辑）集合论中的幂集。设 $UU = (X : "Prop") -> Bool^X$。那么显然有映射 $pi : UU -> Bool^UU$，定义是 $pi = lambda u bind u UU$。反过来，可以利用排中律定义映射 $iota : Bool^UU -> UU$，即
#eq($
  iota alpha X = cases(
    alpha & (X = UU),
    (dots.c) quad & (X != UU)
  )
$)
其中对命题 $X = UU$ 是否成立利用排中律分类讨论，而省略号可以任填 $Bool^X$ 的元素，例如输出 $"false"$ 的常函数即可。这样，函数复合 $pi compose iota$ 就是恒等函数。

不过，这个分类讨论其实不能成立，因为两个分支中的表达式类型不相同。换句话说，单纯的分类讨论 $ite(b, x, y)$ 不能满足要求，而需要_依值分类讨论_。用非直谓编码的 $Bool$ 是无法定义依值分类讨论的，这与上文提到的强 $Sigma$ 类型情况类似。利用选择公理，我们可以绕开依值分类讨论。

#let retract = sym.lt.tri
令 $A retract B$ 为命题 $exists f : A -> B bind exists g : B -> A bind g compose f = id_A$ 的缩写。那么显然有
#eq($ (cal(P)(X) retract cal(P)(UU)) -> exists f : cal(P)(X) -> cal(P)(UU) bind exists g : cal(P)(UU) -> cal(P)(X) bind g compose f = id, $)
再由排中律，可以将两个存在量词移到前面来。换句话说，由 $p -> exists x bind q(x)$ 可以对 $p$ 分类讨论推出 $exists x bind p -> q(x)$。这样，就可以用全局选择取出具体的 $f_X$ 与 $g_X$，使得当 $cal(P)(X) retract cal(P)(UU)$ 成立时，$g_X compose f_X = id$。注意 $X = UU$ 时 $cal(P)(X) retract cal(P)(UU)$ 显然成立，因此定义
#eq($ iota alpha X = g_X (f_X (alpha)) $)
即可。

以上我们构造了 $pi : UU -> Bool^UU$ 与 $iota : Bool^UU -> UU$，满足 $pi compose iota = id_(Bool^UU)$。这其实足够导出 Russell 悖论，不过由于我们使用的是 $Bool$ 而不是 $"Prop"$，其最终结论是 $Bool$ 中的 $"true"$ 与 $"false"$ 相等，而非 $top <-> bot$。后者会使得一切命题都有证明，而前者仅仅使一切命题的证明都相等。
]

// (mention Diaconescu's theorem)
