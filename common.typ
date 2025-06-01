#import "@preview/cetz:0.3.4": canvas, draw
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge
#let diagram = diagram.with(label-size: 0.85em, label-sep: 0.15em)
#let edgeL = edge.with(label-side: left)
#let edgeR = edge.with(label-side: right)
#let edgeM = edge.with(label-side: center)

#let hyperlink(dest, body) = link(dest, underline(text(fill: color.oklch(45%, 55%, 250deg), body), offset: 0.2em))

// Translation (used for indexing)
#let translation-table = state("translations", ())
#let add-entry(zh, en, key) = translation-table.update(it => {
  let actual = key
  if actual == none {
    actual = en.at("text", default: "")
  }
  it.push((zh, en, actual))
  it
})
#let translate(zh, en, key:none) = [#zh #text(fill: luma(40%))[(#en)]#add-entry(zh,en,key)]
#let define(zh, en, key:none) = [*#zh* #text(fill: luma(40%))[(#en)]#add-entry(zh,en,key)]

// Defintions
#import "@preview/ctheorems:1.1.3": *
#let thmstyle = thmplain.with(
  separator: [*.* ],
  titlefmt: strong,
  namefmt: x => [(#x)],
  bodyfmt: content => content + parbreak(),
  inset: (left: 0em, right: 0em),
  base_level: 2
)

#let theorem = thmstyle("theorem", "定理")
#let lemma = thmstyle("theorem", "引理")
#let definition = thmstyle("theorem", "定义")
#let proof = thmproof(
  "proof", "证明",
  separator: h(0em),
  titlefmt: box.with(stroke: 0.5pt, outset: (top: 0.25em, bottom: 0.25em, left: 0.1em, right: 0.1em)),
  inset: (left: 0em, right: 0em),
)

// Figure
#let numbered-figure = figure.with(kind: "numbered-figure", supplement: "图表", numbering: "1", gap: 1em)

// Equations
#let eq(content) = [\
  #box(align(center, content), width: 1fr)\
]
#let varnothing = sym.diameter
#let cal(it) = text(font: "KaTeX_Caligraphic", it) // TODO spacing difference?

// Inference rules
#let rule(concl, ..prem) = if type(prem.at(0, default: none)) == array {
    math.frac(box(
      prem.pos()
      .map(it => math.equation(it.intersperse(math.quad).join()))
      .intersperse("\n").join()
    ),
      concl.intersperse(math.quad).join())
  } else {
    math.frac(prem.pos().intersperse(math.quad).join(),concl)
  }
#let partir(..rules) = for rule in rules.pos() {
  box(math.equation(rule, block: true), inset: (left: 1em, right: 1em))
  // TODO box inherit baseline
}
// Other type theoretic stuff
#let istype = math.op(math.sans("type"))
#let isnf = math.op(text(fill: color.oklch(50%, 80%, 200deg), math.sans("nf")))
#let isne = math.op(text(fill: color.oklch(50%, 80%, 80deg), math.sans("ne")))
#let isvar = math.op(text(fill: color.oklch(50%, 0%, 0deg), math.sans("var")))
#let typeof = math.op("typeof")
#let interpret(x) = math.lr(math.class("opening",sym.bracket.double) + x + math.class("closing",sym.bracket.double.r))
#let bind = math.class("punctuation", ".")
#let Unit = math.bb("1")
#let Bool = math.bb("2")
#let ite(b,t,f) = $"if" #b "then" #t "else" #f$
#let Set = math.sans("Set")
#let Psh = math.sans("Psh")
#let yo = math.class("unary", "よ")

#let xarrow(arrow: sym.arrow, ..args, sup: none, sub: none) = {
  if args.pos().len() >= 1 {
    sup = args.pos().at(0)
  }
  if args.pos().len() >= 2 {
    sub = args.pos().at(1)
  }
  context {
    let lsup = measure($script(sup)$)
    let lsub = measure($script(sub)$)
    math.attach(math.stretch(arrow, size: calc.max(lsup.width, lsub.width) + 0.75em), t: box($script(sup)$, inset: (bottom: -0.3em)), b: box($script(sub)$, inset: (top: -1.1em), baseline: 100%))
  }
}
