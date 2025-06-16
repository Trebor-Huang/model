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
- equivalent forms of UIP and K

== 等式反映 <sec:reflection-consequences>
- reflection and another rule implies J
- reflection and J implies UIP and funext


== 泛等公理 <sec:univalence-equivalences>
- equivalent forms of univalence
