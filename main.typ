#import "common.typ": *
#set text(font: ("New Computer Modern", "Source Han Serif SC"), weight: 450, size: 12pt, lang: "zh")
#show math.equation: set text(font: ("New Computer Modern Math", "Source Han Serif SC"))

#let par-indent = 2em
#set par(leading: 0.85em, spacing: 1em, first-line-indent: (amount: par-indent, all: true), justify: true)
#show math.equation.where(block: true): set par(leading: 0.5em)
#set list(indent: 0.7em)
#set enum(indent: 0.7em)

// Theorems
#show: thmrules.with(qed-symbol: [#sym.square#parbreak()])

// CJK punctuation
#show "。": ". " + h(0.15em, weak: true) // + h(0.5em, weak: true)
#show "：": ": " + h(0.1em, weak: true) // + h(0.4em, weak: true)
#show "，": ", " // + h(0.35em, weak: true)
#show "（": " ("
#show "）": ") "
#show "、": "、" + h(-0.2em)
#show "……": set text(font: "Source Han Serif SC")

#let underdot = {
  let radius = 0.08em
  sym.zwj + box(place(dx: -0.5em - radius, dy: 0.2em, circle(radius: radius, fill: black, stroke: none)))
}
#show emph: it => {
  show regex("\p{sc=Han}"): it => it + underdot
  it
}

#set footnote(numbering: it => text(numbering("①", it), font: "Source Han Serif SC", weight: 600))
#show footnote: set super(baseline: -0.5em, size: 0.65em)
#show footnote.entry: set super(baseline: 0pt, size: 1em)

// Figure
#set figure.caption(separator: [. ])

// Front page
#[
#set align(center)
#v(1fr)
#set text(size: 36pt)
*依值类型论的模型*\
#set text(size: 20pt)
Trebor\ #v(1em)
#set text(size: 14pt)
#datetime.today().display("[year]年[month padding:none]月[day padding:none]日")
#v(1.5fr)

#let realignment = place(
  bottom+center
)[
#set text(size: 1.5em)
#diagram(node-outset: 0.2em, {
  let scale = 80%
  node((1,1.5), $"Tp"$, name: <Tp>)
  node((1,0), $"Tm"$, name: <Tm>)
  edgeL(<Tm>, "->", <Tp>, $pi$, mark-scale: scale)

  node((0,2), $Gamma$, name: <Gamma>)
  node((0,0.5), $Delta$, name: <Delta>)
  edgeM(<Delta>, "->", <Gamma>, box($f$, inset: 0.2em), label-pos: 40%, mark-scale: scale)

  node((-1,1.5), $tilde(Gamma)$, name: <Gamma1>)
  node((-1,0), $tilde(Delta)$, name: <Delta1>)
  edgeR(<Delta1>, "->", <Gamma1>, $i^* f$, mark-scale: scale)

  edgeR(<Gamma1>, ">->", <Gamma>, $i$, mark-scale: scale)
  edge(<Gamma>, "-->", <Tp>, mark-scale: scale)
  edge(<Gamma1>, "->", <Tp>, mark-scale: scale)

  edge(<Delta1>, ">->", <Delta>, mark-scale: scale)
  edge(<Delta>, "-->", <Tm>, mark-scale: scale)
  edge(<Delta1>, "->", <Tm>, mark-scale: scale)
})
]

#let magic = place(
  bottom + center,
canvas({
  import draw: *
  set-style(stroke: (thickness: 2mm, cap: "round", join: "round", paint: luma(50%)))

  circle((0,0), radius: 2.75)
  let top-height = 1.6
  let bottom-height = -top-height - 0.1
  let stem-pos = -0.73
  let bowl-width = 1.05
  let bowl-depth = 1.45
  let descend-height = 1.25
  let descend-width = bowl-width * 0.9
  bezier(
    (stem-pos, bottom-height),
    (stem-pos - descend-width, bottom-height + descend-height),
    (stem-pos, bottom-height + descend-height)
  )
  line((stem-pos, bottom-height), (stem-pos, top-height))
  for _ in (1,2) {
    arc(
      (rel: (0, bowl-width - bowl-depth)),
      radius: bowl-width/2,
      start: -180deg,
      stop: 0deg,
    )
    line((), (rel: (0, bowl-depth - bowl-width)))
  }

  circle((0,0), radius: 4)
  let N = 32
  for i in range(N) {
    content(
      (angle: i * 360deg/N, radius: 3.1),
      text(
        size: 24pt, fill: luma(40%),
        ($Sigma$, $tilde.equiv$, $Pi$, $cal(U)$).at(calc.rem(i, 4))
      ),
      angle: - 90deg + i * 360deg/N,
      anchor: "south"
    )
  }
}))

#magic
]


#set page(numbering: "i")
#counter(page).update(1)

// Headings and outline
#show heading: set block(above: 1.25em, below: 0.9em)
#show heading.where(level: 1): it => [
  #pagebreak(weak: true)
  #counter(footnote).update(0)
  #set align(center)
  #set text(size: 20pt)
  #if it.numbering == none {
    it
  } else {
    block[
      #counter(heading).display()#h(1em)#it.body
    ]
  }
]
#let section-fill = color.oklch(90%, 50%, -80deg)
#show heading.where(level: 2): it => [
  #set text(size: 16pt)
  #block(sticky: true)[
    #box(place(
      bottom+right,
      dx: -0.5em,
      align(right, box(
        counter(heading).display(),
        inset: (right: 0.45em),
        outset: 0.3em,
        width: 2.5cm,
        // fill: section-fill,
        stroke: 0.5pt,
        radius: 0.2em,
      ))
    ))#it.body
  ]
]
#show heading.where(level: 3): set text(size: 14pt)
#show heading.where(level: 4): set text(size: 12pt)
#show heading.where(level: 4): box.with(inset: (right: 0.75em))

#set outline.entry(fill: repeat(gap: 0.2em)[·])
#outline(depth: 3, indent: 1.5em)

// Redact the chapter number
#set heading(numbering: (a, ..b) => numbering("1.", ..b))
#show heading.where(level: 1): set heading(numbering: (k) => [第#numbering("一", k)章])
#show heading.where(level: 4): set heading(numbering: none)

#let is-appendix = state("is-appendix", false)
#show ref: it => {
  let el = it.element
  if el != none and el.func() == heading {
    context {
      if el.level == 1 {
        link(it.target)[#numbering(el.numbering, ..counter(heading).at(it.target))]
      } else if not is-appendix.at(it.target) {
        // Re-display the chapter number
        link(it.target)[#numbering("1.1", ..counter(heading).at(it.target)) 节]
      } else {
        link(it.target)[附录 #numbering("A.1", ..counter(heading).at(it.target))]
      }
    }
  } else {
    it
  }
}

#set page(numbering: "1")
#counter(page).update(1)

#include "preface.typ"

#include "prerequisite.typ"

#include "introduction.typ"

#include "examples.typ"

#include "category.typ"

#include "syntax.typ"

#include "model.typ"

// Appendix numbering
#counter(heading).update(0)
#is-appendix.update(true)
#show heading.where(level: 1): set heading(numbering: (k) => [附录 #numbering("A", k)])

#include "impredicative.typ"

#include "identity.typ"

#is-appendix.update(false)
#show heading.where(level: 1): set heading(numbering: none)

= 术语翻译表
#columns(2)[
#set par(justify: false)
#context {
  let final = translation-table.final().sorted(key : ((zh, en, key)) => lower(key))
  for (zh, en, _) in final [
    / #zh: #en

  ]
}
]

// Bibliography
#[
#set text(lang: "en")
#show regex("[A-Z]\. "): it => it.text.slice(0,2) + sym.space.thin
#show link: set text(font: "DejaVu Sans Mono", size: 0.8em, fill: blue.darken(10%))
#show regex("(10\.|http).+"): it => text(
  for i in it.text {
    i + sym.zws
  }
)
#show "arithmétique": [arith-?mé-?tique]
#bibliography("references.yaml", title: "参考文献", style: "ieee-alt.csl") // TODO style
]
