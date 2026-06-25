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

这样来看，我们需要在模型的构造中安装一些 “追踪器”，记录每个语义元素原本对应哪个语法元素。这种技巧就是#define[逻辑关系][logical relation]，也作 #translate[Tait 计算谓词][Tait computability predicate]。先考虑无变量的情况：假如有类型 $A$，集合模型中解释为集合 $X$。我们只需添加函数 $p$，将 $X$ 的元素映射到 $A$ 的语法元素，得到三元组 $(X, A, p)$。这样，每个元素 $x in X$ 都携带了自己对应的语法元素 $tack p(x) : A$。不难得到依值类型的版本。
#proof[
  定义*核算结构*#footnote[翻译未定。]为三元组 $(X, Gamma, sigma)$，其中 $X$ 是任意集合，$Gamma$ 是语法语境，$sigma : X -> hom(1, Gamma)$ 是一族代换。其上的依值核算结构为三元组 $(Y, A, p)$，其中 $Y$ 是 $X$ 上的集合族，$A$ 是 $Gamma$ 中的类型，而 $p_x : Y_x -> "Tm"(1, A sigma_x)$ 是一族函数。

  我们构造新的模型，其中语境解释为核算结构，代换 $(X, Gamma, sigma) -> (X', Gamma', sigma')$ 解释为二元组 $(f : X -> X', phi : Gamma -> Gamma')$，构成交换方
  #eq(diagram($
    X edge("->", f) edge("d", "->", sigma) & X' edge("d", "->", sigma') \
    hom(1, Gamma) edge("->", delta |-> phi compose delta) & hom(1, Gamma')
  $))
  将类型解释为依值核算结构，而 $(Y, A, p)$ 的语义元素集是 $Y$。

  (...)
]

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
