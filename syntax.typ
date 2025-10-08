#import "common.typ": *
= 语法性质的证明 <ch:syntax>

- warm up: true is not equal to false using Set models

== 典范性
- direct construction of the model
  - "tracking elements", pretending simple types
  - contexts are $(X, Gamma, sigma : X -> hom(1, Gamma))$, types are $(Y_(x in X), A, Y_x -> A sigma_x)$, elements are a tracking element together with a corresponding real element

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
