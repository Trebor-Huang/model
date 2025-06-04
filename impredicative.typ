#import "common.typ": *
= 非直谓宇宙 <appendix:impredicative>

- Basic rules
- General theory of impredicative universes
  - Proposition as elements of `Prop`, compare with HoTT
  - Choice and Diaconescu's theorem (Appendix?)
- The universe structure of CoC, CIC and pCIC
- Girard's paradox
- Inductive types, large elimination
  - Berardi's paradox

Figure out where to put these:
- Proof irrelevant model of Prop using ZFC sets
  - Tricky a priori, if $"Prop" : "Set"$ ($V_1$ is not small)
  - Easy in Coquand hierarchies, mark variables by sort, but cumulativity won't hold, i.e. $(Pi_"Prop" A B)' != Pi_"Set" A' B'$
  - Easy if Prop is not a universe, Pi and Forall separated


== 寓言一则

== 宇宙层级的历史

== 非直谓宇宙的悖论

=== Russell 悖论

- Version in type theory (need Sigma type, or impredicative encoding of it?? which means $* : *$)

=== Girard 悖论
#let Uminus = $"U"^-$

Russell 悖论不能直接套，因为 U 系统中所有类型都可正规化。同时 U 系统的类型检查可判定，并且等式理论自洽

- Girard (1972), simplification of the Burali–Forti paradox, order without torsion
- Coquand's formulation (1986), well-founded relation
- Hurkens paradox, double powerset

=== Berardi 悖论

(mention Diaconescu's theorem)
