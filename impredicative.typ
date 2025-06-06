#import "common.typ": *
= 非直谓宇宙 <appendix:impredicative>

非直谓性在逻辑学和哲学中概念比较模糊，没有统一的定义。在类型论的语境中，非直谓性则具体指代函数类型 (或者 $Pi$ 类型) 所处的宇宙满足的规则。就一般直觉而言，假如类型 $A$ 在宇宙层级 $kappa$ 中，而 $B$ 在层级 $lambda$ 中，那么函数类型 $A -> B$ 应该取二者大者，即 $max{kappa, lambda}$。但是，如果某个宇宙层级是*非直谓*的，那么只要陪域 $B$ 在此层级中，任何函数类型 $A -> B$ 就也处在此层级中。

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
由于 $cal(U) : cal(U)$ 不成立，因此 $A$ 和 $B$ 都不能取值为 $cal(U)$ (或者用 Tarski 宇宙的说法，$cal(U)$ 中不存在元素构成 $cal(U)$ 自身的名字)。这样 $cal(U)$ 就只能单独构成一个类型，不能组合成更复杂的类型表达式，保证了与原系统的等价性。改写之后容易看出，这种 $Pi$ 类型也是非直谓性的一种体现，因为 $product_(A:cal(U)) P(A)$ 的定义域是 $cal(U)$ —— 注意不是定义域为 $A : cal(U)$，而是定义域就是 $cal(U)$ 本身，也就是宇宙层级比原系统中的所有类型都高 —— 的 $Pi$ 类型，所处的宇宙仍然是 $cal(U)$，比直谓性要求的要低一层。

== 构造演算与其变体 <sec:calculus-of-constructions>

=== 定义

#translate[构造演算][calculus of constructions]，或缩写为 CoC，是一种只有 $Pi$ 类型与宇宙的类型论。
读者或许知道这类类型系统被 Barendregt 称作#define[纯类型系统][pure type system]，并且 CoC 的子系统构成一个立方体，称作 $lambda$ 立方。我们_不认为_这是合适的分类。其中的宇宙有一些表现得比较反直觉，只是为了凑齐规律而添加的。它在某些方面分类过于细致，而在另一些方面则不够精细。特别是希望以此为基础添加 $Sigma$ 类型或者更复杂的结构时，无法用纯类型系统的框架描述各种变体。读者可以参阅 Bart Jacobs~@on-cubism 对纯类型系统的批评。

定义*构造演算*为对 $Pi$ 类型封闭，并且包含一个非直谓宇宙 $*$ 的类型论。换句话说，宇宙中有名字
#eq($
  rule(
    Gamma tack dot(Pi)(A, B) : *,
    Gamma tack A istype,
    Gamma\, A tack B : *
  ) quad
  rule(
    Gamma tack "El"\(dot(Pi)(A, B)\) = Pi A("El"(B)) istype,
    Gamma tack A istype,
    Gamma\, A tack B : *
  ).
$)
注意其中 $A$ 是任意类型。也可以用 Coquand 宇宙，设 $A istype_*$ 与 $A istype$ 两个层级，但只有 $istype_*$ 与宇宙 $*$ 之间有 $"El"$ 和 $ceil(-)$ 的转换操作，而 $istype$ 层级没有宇宙。这样非直谓宇宙的规则就是
#eq($
  rule(
    Gamma tack Pi A B istype_j,
    Gamma tack A istype_i,
    Gamma\, A tack B istype_j
  ) quad (i,j in {*, diameter}).
$)
如果认为构造演算是编程语言的类型系统，那么一般称 $*$ 为 $"Set"$，因为程序所操作的类型直观上是集合。不在 $*$ 中的类型则称作#translate[种类][kind]。但如果认为构造演算是逻辑系统，就称 $*$ 为 $"Prop"$，认为其元素是命题。这是因为上文所讲的，在主流数学中唯一存在的非直谓宇宙就是命题构成的宇宙。

#numbered-figure(caption: [构造演算的规则])[
  (...)
]

=== 构造演算用例 <sec:coc-usage-examples>

Some examples of its abilities and limitations

encoding inductive types (system F)

Sigma types, strong and weak

=== 宇宙层级

Talk about adding more universes, reveal Girard paradox

Resort to adding predicative universe hierarchy (adding two for both Set and Prop)

- Proposition as elements of `Prop`, compare with HoTT
- Choice and Diaconescu's theorem(?)
- Proof irrelevant model of Prop using ZFC sets
  - Tricky a priori, if $"Prop" : "Set"$ ($V_1$ is not small)
  - Easy in Coquand hierarchies, mark variables by sort, but cumulativity won't hold, i.e. $(Pi_"Prop" A B)' != Pi_"Set" A' B'$
  - Easy if Prop is not a universe, Pi and Forall separated


== 寓言一则

- The universe structure of CoC, CIC and pCIC (in story)
- talk about inductive types, large elimination, and squash types

== 悖论三则

=== 朴素集合论的悖论

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

Martin-Löf 在 1971 年提出了最早的 Martin-Löf 类型论，但是其中没有 $Sigma$ 类型。论文中写作 $Sigma$ 的类型是用 $Pi$ 作非直谓编码的 (...) refer to previous section。因此 Russell 悖论并不能直接套用。1972 年，Girard 发现这个系统不自洽，见 @sec:girard-paradox.//事实上，Martin-Löf在论文中证明了它是自洽的，但是由于证明的元理论本身满足 $VV in VV$，所以实际上元理论也有矛盾。

在 Russell 悖论之前，在朴素集合论中就发现了一系列类似的矛盾，Russell 悖论只是其中最简洁的一个。例如 Cantor 最著名的定理说的是任何集合 $X$ 的元素个数都要严格比幂集 $cal(P)(X)$ 少。但是，如果有全体集合的集合 $VV$，它理应是元素数量最大的集合，因此 $abs(VV) < abs(cal(P)(VV))$ 不应该成立。这是 *Cantor 悖论*。事实上，将 Cantor 定理的证明展开化简之后，这条悖论就会化作 Russell 悖论。

除了基数以外，对序数的研究中也产生了类似的悖论。Cantor 证明了任意序数之间都可相互比较，即 $alpha < beta$、$alpha = beta$ 与 $alpha > beta$ 三者必居其一。但数学家 Burali-Forti 在 1897 年又证明了存在不可比较的序数! 这是因为如果所有序数都可比较，那么全体序数的集合也是良序集 $"No"$，就应该构成最大的序数 $Omega$。但这是不可能的，因为 $Omega + 1 > Omega$。这就是 *Burali-Forti 悖论*。

这则悖论可以做一些简化，避免用到序数的全套理论。例如可以只用良基关系 (...) 假如良基集合 $A$ 与 $B$ 的某个真子集同构，就说 $A < B$。这样全体良基集合的集合 $"WF"$ 也是良基的。进一步分析可以得到 $"WF" < "WF"$，矛盾。这是 *Mirimanoff 悖论*。还可以定义无挠序的概念：
#definition[
  如果全序集 $A$ 满足任何子集 ${x in A mid(|) x < a_0}$ 与 $A$ 本身没有保序同构，就说 $A$ 是*无挠*的。这种子集称作 $A$ 的#define[前段][initial segment]。
]
全体无挠序的集合构成全序集 $"TF"$，任何无挠序都同构于它的某个前段。但 $"TF"$ 本身又是无挠的，因此它同构于自己的某个前段，故不是无挠的，矛盾。

=== Girard 悖论 <sec:girard-paradox>
#let Uminus = $"U"^-$

// TODO reread and streamline

由于相关术语的使用比较混乱，这里稍作正名。

1972年，逻辑学家 Jean-Yves Girard (注意不是哲学家 René Girard) 在博士论文~@girard-paradox 中研究了一类用于表达高阶逻辑的类型论，其中只包含 $Pi$ 类型与不同的宇宙层级。在附录中，他提出了这些类型论的一种自然推广，起名为 U 系统，并且证明了这个系统是不自洽的。如果将这个系统中的所有宇宙层级视作相同，那么 U 系统就化作前文提到的 $cal(U) : cal(U)$ 系统，因此前者的所有证明都可以直接照搬到后者。这就说明了 Martin-Löf 的 (...) 不自洽。

U 系统可以视作有两个宇宙 $cal(U)_*$ 与 $cal(U)_square$，其中前者是后者的元素 (或者严格来说，存在 $dot(cal(U))_* : cal(U)_square$ 满足 $"El"\(dot(cal(U))_*\) = cal(U)_*$)，可以构成以下的 $Pi$ 类型：
#eq($
  rule(
    Gamma tack dot(Pi)(A, B) : cal(U)_j,
    Gamma tack A : cal(U)_i,
    Gamma\, "El"(A) tack B : cal(U)_j
  ) quad (i, j) = {(*, *), (square, *), (square, square)},
$) (...)

当然，读者不必详细记忆哪些宇宙之间有 $Pi$ 类型，只需要粗略记得有两个非直谓宇宙有元素关系即可。


Russell 悖论不能直接套，因为 U 系统中所有类型都可正规化。同时 U 系统的类型检查可判定，并且等式理论自洽

- Girard (1972), simplification of the Burali-Forti paradox, order without torsion
- Coquand's formulation (1986), well-founded relation
- Hurkens paradox, double powerset

=== Berardi 悖论

Inductive types and large elimination (where to put it?)

(mention Diaconescu's theorem)
