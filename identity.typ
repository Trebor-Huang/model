#import "common.typ": *
= 相等类型的性质 <appendix:identity>

== J 原理的等价表述 <sec:J-equivalences>
相等类型的消去子是
#eq($
  rule(
    Gamma tack "J"_A (p, P, r) : P(s, t, p);
    Gamma tack p : "Id"(A, s, t),
    Gamma\, x : A\, y : A\, q : "Id"(A, x, y) tack P(x,y,q) istype;
    Gamma\, z : A tack r : P(z, z, refl_A (z))
  )
$)
满足 $"J"_A (refl_A (t), P, r) = r(t)$。由于它涉及的依值类型比较复杂，我们可以将其拆分为两条更简单的规则。

假设有 $Gamma tack s,t : A$ 与 $Gamma tack p : s = t$。那么有序对类型 $(x : A) times (s = x)$ 中有两个元素，$(s, refl(s))$ 与 $(t, p)$。记 $contr_A (s, t, p) : (s, refl(s)) = (t, p)$ 是二者之间的道路，使得平凡情况下 $contr_A (s, s, refl(s)) : (s, refl(s)) = (s, refl(s))$ 本身是平凡道路 $refl$。

如果还有依值类型 $Gamma, x : A tack P istype$，那么有函数 $transp_A (p, P, u)$ 将元素 $u : P(s)$ 转移到 $P(t)$ 中。它满足判值相等 $transp_A (refl, P, u) = u$，即沿着平凡道路转移是恒等函数。

用 J 原理不难表达出 $contr_A$ 与 $transp_A$，并且满足对应的判值相等。反过来，如果将这两者作为类型论中的规则，也可以表达出 J 原理。给定 J 原理的参数 $p$、$P$、$r$，可以先用 $contr$ 构造等式 $(s, refl(s)) = (t, p)$，再对此式用 $transp$ 得到 $transp(contr(s, t, p), Q, r)$。其中类型 $Q$ 依赖于变量 $d : (x : A) times (s = x)$，定义为 $Q(d) = P(s, pi_1 (d), pi_2 (d))$。这样得到的表达式也满足 J 原理所需的判值相等关系。

== K 原理的等价表述 <sec:K-equivalences>
K 原理说的是
#eq($
  rule(
    Gamma tack "K"_A (p, P, r) : P(s, p);
    Gamma tack p : "Id"(A, s, s),
    Gamma\, x : A\, q : "Id"(A, x, x) tack P(x,q) istype;
    Gamma\, z : A tack r : P(z, refl_A (z))
  )
$)
而相等证明的唯一性是公理
#eq($ "UIP"_A : product_(x : A) product_(p : x = x) p = refl(x), $)
另可以表述成
#eq($ "UIP"'_A = product_(x, y : A) product_(p, q : x = y) p = q. $)
在有 J 原理的前提下，这三者互相等价。

由 K 原理推出 $"UIP"_A$，只需令 $P(x, q)$ 为相等类型 $q = refl(x)$，$r = refl(refl(z))$ 即可。反过来，在 $"UIP"_A$ 给出的等式 $p = refl(x)$ 上再运用 J 原理，即可推出 K 原理。其次，由 $"UIP"'_A$ 推出 $"UIP"_A$ 是显然的。由 $"UIP"_A$ 推出 $"UIP"'_A$ 则是先对 $p : x = y$ 用 J 原理，再直接应用 $"UIP"_A$。

== 等式反映 <sec:reflection-consequences>
等式反映说的是
#eq($
  rule(
    Gamma tack s = t : A,
    Gamma tack p : "Id"(A, s, t)
  ).
$)
换言之，如果可以证明两个表达式相等，那么它们就判值相等。这对类型论的语法性质有极大影响，因为这相当于可以在语境中假设任意表达式的判值相等。例如有
#eq($ p : "Id"(cal(U), NN, NN -> NN) tack 3(4) : NN. $)
其中 $3(4)$ 是函数应用。因此，正规形式的定义就不再适用。

事实上，在等式反映下，类型检查与判值相等都不可判定。在可计算性理论中的一个重要结论是，给定一些生成元以及它们之间的等式关系，判定由它们生成的群中两个元素是否相等是不可能的，因为可以在其中编码停机问题。而这个判定问题可以直接写进含有等式反映的类型论的类型检查中。直接在语境中假设有一个群 $G$，将每个生成元翻译为类型论中的变量 $x_i : G$，并且将等式关系直接写进语境中，如 $p : x_1 x_2 = x_3^2$ 即可。此时如果要检查 $refl(M) : M = N$ 是否类型正确，就需要判定是否能从这些等式关系中推导出 $M$ 与 $N$ 相等。

在等式反映与 J 原理下，可以推出相等证明的唯一性。由于有等式反映，这等价于推出以下判值相等版本的相等证明唯一性：
#eq($
  rule(
    Gamma tack p = refl_A (t),
    Gamma tack p : "Id"(A, t, t)
  ).
$)
具体来说，由@sec:J-equivalences 中的结论可知有序对类型 $(x : A) times (t = x)$ 中等式
#eq($ (t, p) = (t, refl(t)) $)
成立。用等式反映可以将其化为判值相等。此时应用 $pi_2$ 就得到判值相等 $p = refl(t)$ 成立。

进一步，等式反映还可以推出函数外延性。如果 $p : forall x bind f(x) = g(x)$，那么就有判值相等 $x : A tack f(x) = g(x)$，从而判值相等 $(lambda x bind f(x)) = (lambda x bind g(x))$ 也成立，再由 $eta$ 等式得 $f = g$。

另一方面，如果有等式反映与判值相等版本的相等证明唯一性，那么就能推导出 J 原理。这也非常直观。给定 $p : "Id"(A, s, t)$，则类型论中任何 $s$ 都能直接替换成 $t$，并且 $p$ 能直接替换成 $refl(s)$。因此如果有 $z : A tack r : P(z, z, refl(z))$，就能直接推出 $r[z\/s] : P(s, s, refl(s))$ 成立，故 $r[z\/s] : P(s, t, p)$ 也成立。


== 泛等公理 <sec:univalence-equivalences>
- equivalent forms of univalence
