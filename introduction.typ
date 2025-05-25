#import "common.typ": *
= 概论

我们希望为类型论的语法赋予 “含义”。这些含义可以是任何数学对象，我们称作#define[语义][semantics]，而从语法到语义的映射称作#define[解释][interpretation]。不过，有用的语义应当满足一些要求，使得语义对象的性质可以与语法相对应。一套满足要求的语义就是#define[模型][model]。

我们先从具体的例子出发，思考模型的定义应该满足什么条件。最直观的模型是集合模型，在 #[@sec:set-model]会讲解。因此，我们需要保证模型的定义能让集合构成模型。
另外，既然语义可以是任何数学对象，而语法本身也是一种数学对象，那么应当有一个平凡的模型，将每个表达式都解释为自身。所以我们也需要确保语法也可构成模型。

== 集合模型 <sec:set-model>

直观上说，对于大多数类型论而言，每个类型可以理解为集合，函数类型对应集合之间的函数构成的集合，乘积类型对应集合的 Descartes 乘积，等等。(同伦类型论不在此列.) 因此，我们理应能够构造出类型论的集合模型。
依值类型论中，依值类型 $x : A tack B(x) istype$ 可以解释为集合族 ${B(x)}_(x in A)$，即为每个元素 $x in A$ 赋予一个集合 $B(x)$。 $Sigma$ 类型对应不交并
#eq($ product.co_(x in A) B(x) = {(x, y) mid(|) x in A, y in B(x) }. $)
相应地，$Pi$ 类型对应乘积 $product_(x in A) B(x)$。

不过，上面的说法并不完整。在依值类型论中，_所有_的类型 $Gamma tack A istype$ 都是依值的，即依赖于 $Gamma$ 中的变量。这样看来，语境的解释才应该是集合，而类型解释为集合族。例如，空语境对应单元素类型，而语境扩展 $(Gamma, A)$ 可以解释为不交并 $product.co_(x in Gamma) A(x)$。另一方面，我们还需要区分语法与它们对应的解释。例如可以将 $Gamma$ 的解释记作 $interpret(Gamma)$。这样就能给出完整的集合模型：
- 语境 $Gamma$ 解释为集合，记作 $interpret(Gamma)$。
- 类型 $Gamma tack A istype$ 解释为集合族，记作 $interpret(A)_x$，其中 $x in interpret(Gamma)$。
- 空语境解释为单元素集合，即 $interpret(()) = {star}$。需要注意的是，空语境不是空集。因为空语境的 “空” 表示没有变量，因此变量的取值就只有一种情况。这与零个集合的乘积是单元素集，或者幂 $n^0 = 1$ 的道理是一样的。
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

为了避免讨论全体集合的集合的困难，我们一般不认为语境可以取任意集合，而是如 #[@sec:set-theory]介绍的选定强不可达基数 $kappa$ 并将语境解释为 $H_kappa$ 中的元素。

== 模型的定义

我们从上文讨论的直观里抽取出模型的一套定义。为了区分某个语法概念与它对应的语义解释，我们将语境的解释称作*语义语境*，类型的解释称为*语义类型*，以此类推。例如在集合模型中，语义语境的意思就是集合。不过，我们仍然会采用同样的字母指代这些对象，例如语法语境与语义语境都用 $Gamma, Delta, Theta$ 等字母表示，否则排版容易叠床架屋。

在 #[@sec:explicit-substitution]中，我们提到不应该将语境的长度视为本质属性，因此变量代换需要视作新的语法构造，而非在语法上递归定义的函数。在模型的定义中这样的好处是明显的：我们将表达式解释为数学对象之后，递归定义的代换就行不通了。因为两个语法上不同的表达式在模型中可能对应相同的数学对象，因此在这个模型中就不能靠递归定义这两个表达式的代换.#footnote[那么，干脆去掉代换的概念，能否行得通呢? 类型论里有许多规则需要用代换来表达，例如 $beta$ 判值相等 $(lambda x. t) s = t[x\/s]$。倘若能不用代换表达此类规则，那么在模型中也能免去讨论代换结构。留给读者思考。]

=== 基本框架

模型的定义大致与类型论的规则一一对应，其中关于代换的部分可以参考@fig:substitution。读者不必死记，粗读之后即可向后阅读例子。

#definition[
  依值类型论的*模型*包含以下资料。
  - 有一类数学对象 $"Ctx"$，作为语境的解释，称作语义语境。
  - 给定两个语义语境 $Gamma, Delta$，有集合 $hom(Gamma, Delta)$ 作为代换的解释。其中的元素写作 $sigma : Gamma -> Delta$，称作语义代换。
  - 有恒等代换 $id : Gamma -> Gamma$ 与代换复合操作，给定 $sigma : Gamma -> Delta$ 与 $tau : Delta -> Xi$，给出 $tau compose sigma : Gamma -> Xi$。它们满足单位律与结合律。
  - 对于每个语义语境 $Gamma$，有集合 $"Tp"(Gamma)$ 作为类型的解释，其中的元素称作语义类型。
  - 对于每个语义语境 $Gamma$ 与语义类型 $A in "Tp"(Gamma)$，有集合 $"Tm"(Gamma, A)$，作为类型元素的解释，其中的元素称作语义元素。
  - 对于语义类型 $A in "Tp"(Gamma)$ 与代换 $sigma : Delta -> Gamma$，有语义代换运算 $A sigma in "Tp"(Delta)$ —— 注意代换的方向 —— 满足 $A id = A$ 与 $A (sigma compose tau) = (A sigma) tau$。 因此我们将连续代换不加括号地写作 $A sigma tau$。
  - 对语义元素 $a in "Tm"(Gamma, A)$ 与代换 $sigma : Delta -> Gamma$，有语义代换运算 $a sigma in "Tm"(Delta, A sigma)$，满足 $a id = a$ 与 $a (sigma compose tau) = (a sigma) tau$。
  - 有空语境 $()$，或者写作 $1$，使得任何语义语境 $Gamma$ 到 $1$ 都只有一个代换。
  - 给定语义语境 $Gamma$ 与类型 $A in "Tp"(Gamma)$，有语境扩展运算 $(Gamma, A) in "Ctx"$，投影代换 $frak(p) : (Gamma, A) -> Gamma$ 与变量 $frak(q) in "Tm"((Gamma, A), A frak(p))$。
  - 给定语义代换 $sigma : Gamma -> Delta$、语义类型 $A in "Tp"(Delta)$ 与语义元素 $a in "Tm"(Gamma, A sigma)$，有代换延拓运算 $[sigma, a] : Gamma -> (Delta, A)$，并且它是唯一满足 $frak(p) compose [sigma, a] = sigma$ 与 $frak(q) [sigma, a] = a$ 的代换。
] <def:model>
乍看之下模型的定义让人眼花缭乱，但读者浏览#[@ch:examples]中的例子后就会发现定义中大部分内容都会化作简单的概念，或者能显然给出，一般无需多虑。在#[@ch:category]中我们还会引入更多打包简化定义的办法。

要理解代换满足的等式，集合模型有一定启发性。对于集合 $Gamma$ 上的集合族 $A_x$，如果有代换 $sigma : Delta -> Gamma$，即两个集合之间的函数，那么集合族可以作代换得到 $B_y = A_(sigma(y))$，是 $Delta$ 上的集合族。

类型论模型定义的重要特性是其中只要求等式。并非所有数学结构都可以这样定义。例如域是拥有四则运算的集合，其中除法的除数必须非零。因此在域的定义中就必须用到_不等式_。相对地，环则只拥有加法、减法与乘法，其中的结合律、分配律等等都是纯等式。这种数学结构称作#define[代数结构][algebraic structure]。群、环、向量空间都是代数结构，而域、全序、拓扑空间不是.#footnote[代数结构可以包含多个集合，而不一定只在一个集合上配备运算。这称作#define[多类][multi-sorted] 代数结构。类型论模型的另一个特别之处在于涉及的集合以元素为指标，例如 $"Tp"(Gamma)$ 对每个元素 $Gamma in "Ctx"$ 都有一个集合。这样的代数理论称作#define[广义代数理论][generalized algebraic theory]，或者 Cartmell 理论。]

代数结构的一大特征是可以自由生成。换言之，给定一些元素，可以构造出_仅仅_满足代数结构本身要求的等式的结构。例如，一个元素 $x$ 在环的加法、减法、乘法下可以生成表达式 $x^2 + x - 2x$。这些表达式构成的环称作多项式环 $ZZ[x]$。具体来说，我们将给定的元素利用代数结构中的运算自由组合，将构造出的所有表达式商去需要满足的等式关系，得到的就是自由代数结构。当然，假如这个代数结构中有指定元素 (也就是零元运算，例如环公理要求乘法单位元 $1$)，那么不用给定元素，也能生成非平凡的代数结构。

这样的描述看上去与 #[@sec:prelim-type-theory]对语法的描述不谋而合。事实上，语法正是自由生成的模型，记作 $cal(T)$。换句话说，语法是依靠模型中的运算自由组合生成的结构，并且除了模型要求的等式之外不满足任何额外的等式。这就是为何我们对语法和语义使用同样的记号：语法是特殊的语义。如果有多个模型 $cal(M), cal(N)$，我们用 $"Tp"_cal(M)$ 等记号区分语义对象来自哪个模型。这样，如果要强调某个对象是语法对象，也可以直接写 $"Tp"_cal(T)$。

=== 类型结构

不同的类型论会在以上的基础上添加各自的类型，因此在模型中也会相应的按照这些类型的规则定义类型结构。我们以几个常见的类型为例，展示这些类型结构的一般定义办法。这些定义只消对类型论规则作机械地改写即可得到，读者观察出规律即可跳过。读者也可以试着用定理证明助手形式化集合模型的构造，有助于消化其中微妙之处。

==== 单元素类型
对于每个语义语境 $Gamma$，选择语义类型 $"Unit" in "Tp"(Gamma)$。严格来说，应该写作 $"Unit"_Gamma$，因为每个语境的类型是不同的。单元素类型的规则如下：
#let star = math.class("normal", sym.star)
#eq($
  rule(
    Gamma tack star : "Unit"
  ) quad
  rule(
    Gamma tack t = star : "Unit",
    Gamma tack t : "Unit"
  )
$)
这可以直接翻译到模型的语言中，即为每个 $"Unit"_Gamma$ 选择元素 $star_Gamma : "Tm"(Gamma, "Unit"_Gamma)$，使得 $"Tm"(Gamma, "Unit"_Gamma)$ 中的所有元素都与之相等。

不过，#[@sec:explicit-substitution]的讨论中，我们提到需要将代换在表达式上的行为作为判值相等加入规则中。这里，因为没有变量，代换的行为非常简单。
#eq($
  rule(
    Gamma tack "Unit" sigma = "Unit" istype,
    Gamma tack sigma : Delta
  ) quad
  rule(
    Gamma tack star sigma = star : "Unit",
    Gamma tack sigma : Delta
  )
$)
因此模型的定义中需要添加等式要求 $"Unit"_Delta sigma = "Unit"_Gamma$ 以及 $star_Delta sigma = star_Gamma$。之后的规则中我们会省略下标，写作 $star sigma = star$.#footnote[由于 $"Tm"(Gamma, "Unit")$ 都只有一个元素，因此等式 $star sigma = star$ 是自动满足的。别的类型则不然。]

在集合模型中，我们已经构造了集合族 $"Unit"_Gamma$，它为元素 $x in Gamma$ 赋予的集合是 ${star}$。其中 $star$ 是集合论中任意一个对象。而 $star_Gamma$ 对应显然的平凡元素族。

==== $Sigma$ 类型
给定语义语境 $Gamma$，类型 $A in "Tp"(Gamma)$ 与 $B in "Tp"((Gamma, A))$，$Sigma$ 类型结构需要选定类型 $Sigma A B in "Tp"(Gamma)$。$Sigma$ 类型的构造子如下：
#eq($
  rule(
    Gamma tack (a, b) : Sigma A B,
    Gamma tack a : A,
    Gamma tack b : B[id, a]
  )
$)
注意使用了代换 $[id, a] : Gamma -> (Gamma, A)$ 使得类型正确，表示语境中的其他变量不改变，而将最后一个变量换为 $a$。用具名变量的语言，就是 $B[x\/a]$。在模型中，这就对应一个二元运算 $"pair"(a,b)$，将 $a in "Tm"(Gamma, A)$ 与 $b in "Tm"(Gamma, B[id, a])$ 映射到 $"Tm"(Gamma, Sigma A B)$。

$Sigma$ 类型的消去子是投影操作：
#eq($
  rule(
    Gamma tack pi_1 (p) : A,
    Gamma tack p : Sigma A B
  ) quad
  rule(
    Gamma tack pi_2 (p) : B[id, pi_1 (p)],
    Gamma tack p : Sigma A B
  )
$)
注意我们不认为 $pi_1$ 是能单独出现的函数，而必须形如 $pi_1 (p)$ 才符合语法。要构造函数 $Sigma A B -> A$，需要写成 $lambda p bind pi_1 (p)$。否则，函数类型和 $Sigma$ 类型就相耦合，破坏了各个功能之间的独立性。投影在模型中的对应就是两个映射 $"proj"_1$ 与 $"proj"_2$，分别把语义元素 $p in "Tm"(Gamma, Sigma A B)$ 映射到 $"Tm"(Gamma, A)$ 与 $"Tm"(Gamma, B[id, "proj"_1 (p)])$。

在集合模型中，给定集合族 $B : "Tp"((Gamma, A))$ 与元素族 $a in "Tm"(Gamma, A)$，$B'=B[id, a]$ 是 $Gamma$ 上的集合族，定义为 $B'_x = B_((x, a_x))$。请读者构造集合模型中的 $"pair"$ 与 $"proj"_i$ 函数。

$Sigma$ 类型的 $beta$ 与 $eta$ 相等，分别对应等式
#eq($
  "proj"_1 (a, b) &= a\
  "proj"_2 (a, b) &= b\
  ("proj"_1 (a), "proj"_2 (a)) &= p.
$)
同样，除了这些等式还有代换需要满足的等式。对于类型本身有
#eq($
  (Sigma A B)sigma = Sigma (A sigma) (B sigma')
$)
其中 $sigma' = [sigma compose frak(p), frak(q)]$ 表示除了最后一个变量不变以外，对其他所有变量用 $sigma$ 代换。同样，对表达式也有等式
#eq($
  "pair"(a, b) sigma &= "pair"(a sigma, b sigma) \
  "proj"_1 (p) sigma &= "proj"_1 (p sigma) \
  "proj"_2 (p) sigma &= "proj"_2 (p sigma).
$)

==== $Pi$ 类型
与 $Sigma$ 类型大体相同，只不过将构造子和消去子分别替换为函数构造与函数应用。
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
这两条规则分别对应一元运算 $"lam" : "Tm"((Gamma, A), B) -> "Tm"(Gamma, Pi A B)$ 与二元运算 $"app"$，将 $f in "Tm"(Gamma, Pi A B)$ 与 $t : "Tm"(Gamma, A)$ 映射到 $"app"(f, t) in "Tm"(Gamma, B[id, t])$。 代换需要满足 $"lam"(t) sigma = "lam"(t sigma')$ 与 $"app"(f, t) sigma = "app"(f sigma, t sigma)$。同样， $sigma' = [sigma compose frak(p), frak(q)]$ 表示最后一个变量不变，而其他变量按 $sigma$ 代换。
$beta$ 与 $eta$ 等式分别是
#eq($
  "app"("lam"(t), s) &= t[id, s] \
  "lam"("app"(t frak(p), frak(q))) &= t.
$)
这实际上给出了 $"lam"$ 的反函数 $"lam"^(-1) (t) = "app"(t frak(p), frak(q))$。换句话说是将语境 $Gamma$ 中的函数 $t$ 映射到语境 $(Gamma, x : A)$ 中的表达式 $t(x)$，其中 $x$ 是新变量。 $beta$ 与 $eta$ 等式保证了这两个映射互逆。

==== 空类型 <sec:empty-type>
类似单元素类型，我们要求每个语境下选出类型 $"Empty"_Gamma in "Tp"(Gamma)$，并且在代换下 $"Empty"_Delta sigma = "Empty"_Gamma$。空类型没有构造子，只有消去子：
#eq($
  rule(
    Gamma tack "abort"_A (p) : A,
    Gamma tack p : "Empty",
    Gamma tack A istype
  )
$)
严格来说，应该允许 $A$ 依赖于一个空类型的变量，才是完整的依值消去子。不过由于空类型可以推出一切，这并没有太大区别。在语义中，我们需要为每个 $A$ 配备运算 #eq($ "abort"_A : "Tm"(Gamma, "Empty") -> "Tm"(Gamma, A), $) 满足 $"abort"_A (p) sigma = "abort"_(A sigma) (p sigma)$。
由于没有构造子，空类型没有 $beta$ 等式。

在集合模型中，空类型的解释是空集合族。 如果 $Gamma$ 非空，那么 $"Tm"(Gamma, "Empty")$ 就是空集，否则它恰好有一个元素。这是因为定义域为空的函数集 $varnothing -> X$，或者零个集合的乘积 $product_(p in varnothing) X_p$，都恰好有一个元素。无论是哪种情况，都不难看出 $"abort"_A$ 只有唯一一种构造方式，因此也总是满足代换的等式。

空类型一般也没有 $eta$ 等式。假如有的话，它应该形如这样：
#eq($
  rule(
    Gamma tack "abort"_A (p) = t : A,
    Gamma tack p : "Empty",
    Gamma tack A istype,
    Gamma tack t : A
  ).
$)
换句话说，如果集合 $"Tm"(Gamma, "Empty")$ 有元素，那么所有集合 $"Tm"(Gamma, A)$ 都必须有唯一的元素。在集合模型中这是成立的。但是在语法中，这意味着如果 $Gamma$ 可以推出矛盾，则 $Gamma$ 下任意类型的所有元素都相等，那么类型检查就需要能判定任意语境是否能推出矛盾，这是不现实的。

==== 不交并
不交并是类型上的二元运算 $"Tp"(Gamma) times "Tp"(Gamma) -> "Tp"(Gamma)$，满足 $(A + B)sigma = A sigma + B sigma$。有两个函数
#eq($
  "inj"_1 &: "Tm"(Gamma, A) -> "Tm"(Gamma, A + B), \
  "inj"_2 &: "Tm"(Gamma, B) -> "Tm"(Gamma, A + B).
$)
分类讨论运算的规则如下：
#eq($
  rule(
    Gamma tack "case"_P (p, l, r) : P[id, p];
    Gamma tack p : A + B,
    Gamma\, x : A + B tack P istype;
    Gamma\, a : A tack l : P[id, "inj"_1 (a)],
    Gamma\, b : B tack r : P[id, "inj"_2 (b)],
  )
$)
读者应该可以写出它对应的运算。对应的代换等式是
#eq($
  "case"_P (p, l, r) sigma = "case"_(P sigma') (p sigma, l sigma', r sigma').
$)
同样， $sigma' = [sigma compose frak(p), frak(q)]$。与空类型类似，不交并一般有 $beta$ 等式而无 $eta$ 等式。$beta$ 等式形如
#eq($
  "case"_P ("inj"_1 (a), l, r) &= l[id, a], \
  "case"_P ("inj"_2 (b), l, r) &= r[id, b].
$)
$eta$ 等式虽然困难不及空类型的情形，但是仍可产生神奇的推论。注意到 Boole 类型与 $"Unit" + "Unit"$ 基本相同，考虑 $f : "Bool" -> "Bool"$，则有判值相等 $f(f(f(x))) = f(x)$。读者可以观察 Gabriel Scherer~@stlc-sum-eta 的工作。

在集合模型中，不交并的解释就是集合族的不交并，即 $(A + B)_x = A_x + B_x$，其中后者的 $+$ 是集合的不交并。$"case"$ 的定义略显繁琐，不过也是十分自然的。

// ==== 自然数类型

==== 相等类型
给定语义类型 $A in "Tp"(Gamma)$ 与两个元素 $s, t in "Tm"(Gamma, A)$，需要给出相等类型 $"Id"(A, s, t) in "Tm"(Gamma, A)$，满足 $"Id"(A, s, t) sigma = "Id"(A sigma, s sigma, t sigma)$。相等类型的构造子是 $"refl"_A (t)$，将 $t in "Tm"(Gamma, A)$ 映射到 $"Tm"(Gamma, "Id"(A, t, t))$，满足 $"refl"_A (t) sigma = "refl"_(A sigma) (t sigma)$。

相等类型的消去子有些复杂。用具名变量的写法，规则是
#eq($
  rule(
    Gamma tack "J"_A (p, P, r) : P(s, t, p);
    Gamma tack p : "Id"(A, s, t),
    Gamma\, x : A\, y : A\, q : "Id"(A, x, y) tack P(x,y,q) istype;
    Gamma\, z : A tack r : P(z, z, "refl"_A (z))
  )
$)
这里，$y : A$ 严格来说应该写为 $y : A frak(p)$，因为此处有新变量 $x$。同样， $q : "Id"(A, x, y)$ 应当用 $A frak(p) frak(p)$。读者可以类似地写出其他需要改动的位置。$"J"$ 在代换下的表现与前文类似，不过其中 $P$ 用到的代换应该是 $sigma'''$，即最后三个变量不动，而其余变量按 $sigma$ 代换。

相等类型同样一般只有 $beta$ 等式：$"J"_A ("refl"_A (t), P, r) = r[z\/t]$。$eta$ 等式的形式比较复杂，读者可以试着写一写。不过，我们可以考虑另两条条比较简单的规则：
#eq($
  rule(
    Gamma tack s = t : A,
    Gamma tack p : "Id"(A, s, t)
  ) quad
  rule(
    Gamma tack p = "refl"_A (t),
    Gamma tack p : "Id"(A, t, t)
  )
$)
其中前者称作#define[等式反映][equality reflection]。换句话说，如果相等类型有元素，那么就有判值相等。有 $"J"$ 消去子的情况下，$eta$ 等式等价于等式反映，并且它可以推出之前所有提到的一般不加入的 $eta$ 规则。另外，如果不加入 $"J"$ 消去子，那么这两条规则合起来可以推出 $"J"$。Martin-Löf 类型论加上这些规则称作#define[外延类型论][extensional type theory]。

集合模型中，相等类型集合族的定义按照元素 $s_x, t_x$ 是否相等分类讨论。如果 $s_x = t_x$，那么 $"Id"(A,s,t)_x$ 就是单元素集合，反之则是空集。这样，等式反映的确是成立的，并且相等类型的所有元素都形如 $"refl"_A (t)$。这样的好处是我们不用验证复杂的 $"J"$ 消去子，不过读者可以自己尝试。

==== 层级与宇宙
在 #[@sec:universe-hierarchy]中提到的各种处理宇宙的方案，各自对应模型中不同的结构。对于最简单的单个 Tarski 宇宙而言，与单位类型一样，需要在每个语境中选出 $cal(U)_Gamma in "Tp"(Gamma)$，满足 $cal(U)_Delta sigma = cal(U)_Gamma$。将宇宙的元素转换为类型的 $"El"$ 算符对应 #eq($ "El"_(cal(U)) : "Tm"(Gamma, cal(U)) -> "Tp"(Gamma). $) 满足 $"El"_cal(U) (A) sigma = "El"_cal(U) (A sigma)$。读者应该不难看出 Tarski 宇宙对各种类型构造子封闭的规则应该如何表达。

集合模型中，根据 #[@sec:set-theory]中的讨论，我们利用强不可达基数的理论。具体来说，我们之前将 $"Tp"(Gamma)$ 定义为 $Gamma -> H_kappa$ 的集合族，其中 $kappa$ 是某个强不可达基数。如果要在此构造宇宙，则需要找到另一个强不可达基数 $lambda < kappa$，此时有 $H_lambda in H_kappa$，因此可以定义 $Gamma$ 下的集合族 $cal(U)_x = H_lambda$，不依赖 $x$。运算 $"El"_cal(U)$ 的定义域是 $H_lambda$ 的元素族，也就是为每个 $x in  Gamma$ 选择 $A_x in H_lambda$。它的值域则是 $H_kappa$ 的元素族，所以可以直接定义 $"El"_cal(U) (A) = A$。

对于 Coquand 层级， $Gamma tack A istype$ 被拆分成多个版本 $Gamma tack A istype_kappa$，其中 $kappa$ 取遍所有层级。对应地，具有 Coquand 层级的类型论的模型就应该将 $"Tp"(Gamma)$ 改为 $"Tp"_kappa (Gamma)$，$"Tm"(Gamma, A)$ 改为 $"Tm"_kappa (Gamma, A)$.#footnote[如果每个 $"Tp"_kappa (Gamma)$ 没有交集，那么元素集合不需要标注 $kappa$ 也可以，标注出来更加清晰。]//$kappa <= lambda$ 的层级累积性可以表述为函数 $iota : "Tp"_kappa (Gamma) -> "Tp"_lambda (Gamma)$，使得等式 $"Tm"_kappa (Gamma, A) = "Tm"_lambda (Gamma, iota(A))$ 与 $iota(A)sigma = iota(A sigma)$ 成立。注意前者是两个集合之间的等式。
有了 Coquand 层级，Coquand 宇宙则非常简单，有
#eq($
  "El"_kappa &: "Tm"_kappa (Gamma, cal(U)_kappa) -> "Tp"_kappa (Gamma) \
  ceil(-)_kappa &: "Tp"_kappa (Gamma) -> "Tm"_kappa (Gamma, cal(U)_kappa)
$)
并且两者互为逆映射，满足 $"El"_kappa (A)sigma = "El"_kappa (A sigma)$ 与 $ceil(A)_kappa sigma = ceil(A sigma)_kappa$。
在集合模型中，可以取强不可达基数 $kappa$，并令 $"Tp"_kappa (Gamma)$ 为取值在 $H_kappa$ 中的集合族。这样， $"El"_kappa (A) = A$ 就是双射。

== 相容性与独立性

在数理逻辑中，模型的一大用途是说明某个命题无法在公理系统中证明或者证伪。如果类型论 $TT$ 中，某个类型 $A$ (视作命题) 没有元素，就说此命题#define[不可证][unprovable]。特别地，如果空类型没有元素，就说这个类型论是#define[自洽][consistent] 的。倘若类型论 $TT$ 添加了公理 $A$ 后仍然自洽，就说它们是#define[相容][consistent] 的。

不难看出，某个命题的否定不可证，等价于这个命题本身与类型论相容。不过在没有排中律的情况下，某个命题不可证要弱于这个命题的否定与类型论相容。如果这两者都和类型论相容，我们就说这个命题是#define[独立][independent] 于该类型论的。不熟悉逻辑学的读者对这些术语之间的联系感到困惑十分正常，多做辨析，熟练即可。

证明这些性质的办法是构造模型。具体来说，假如类型 $A$ 有元素 $tack t : A$，那么任何模型中都会有其解释 $interpret(t) in "Tm"(1, interpret(A))$。那么，如果能构造某个模型，使得 $"Tm"(1, interpret(A))$ 是空集，就可以说明不存在这样的语法表达式 $t$。我们称之为 $A$ 的#define[反模型][counter-model]。读者可以类推写出相容性、独立性等等的证明办法，以此熟悉定义。

在 #[@sec:set-model]中，我们已经定义了集合模型。不难在集合模型中给出空类型的语义 —— 就是空集。因此，这就证明了类型论的自洽性。具体是哪个类型论的自洽性，取决于我们为集合模型构造了哪些类型结构。例如，上文中已经讨论了 Martin-Löf 类型论中所有的类型结构，所以这就说明了 Martin-Löf 类型论是自洽的。更具体来说，由于我们使用了 ZFC 集合论加上 Tarski–Grothendieck @ax:tarski-grothendieck，所以以上的讨论证明了 Tarski–Grothendieck 集合论可以推出 Martin-Löf 类型论是自洽的。

集合模型还可以给出许多公理的相容性。例如#define[函数外延性][function extensionality] 是类型
#eq($
  product_(f, g : A -> B) [product_(x : A) f(x) = g(x)] -> f = g.
$)
在集合模型中这是显然成立的。因此函数外延性与 Martin-Löf 类型论相容。类似地，读者也可以验证 Martin-Löf 类型论与 *K 原理*#footnote[也称为#define[相等证明的唯一性][uniqueness of identity proofs]，缩写为 UIP。K 原理的名字来自 Thomas Streicher，顺承 J 原理的名字选择了下一个字母。]
#eq($ product_(x,y : A) product_(p,q : x = y) p = q $)
相容。之后我们会介绍这两条公理各自的反模型，也就能分别说明它们与 Martin-Löf 类型论独立。
