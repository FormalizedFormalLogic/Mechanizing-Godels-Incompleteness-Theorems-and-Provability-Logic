#import "@preview/ctheorems:1.1.3": *
#import "@preview/curryst:0.5.0": prooftree, rule

#let auxColor = color.hsl(205deg, 55%, 40%)

#let base-text-size = 11pt
#let font-base = "libertinus serif"
#let font-alter = font-base
#let font-math = ("New Computer Modern Math", "libertinus serif")
#let font-code = "JuliaMono"

#let SOURCE = "https://github.com/FormalizedFormalLogic/Foundation/blob/master"

#let init(body) = {
  set page(
    "a4",
    numbering: "1",
    number-align: center,
  )

  set heading(numbering: "1.1")

  set text(size: base-text-size, font: font-base)

  show math.equation: set text(font: font-math)

  // show raw: set text(size: 7pt, font: font-code)
  show raw: set text(font: font-code)

  show raw.where(block: false): box.with(
    inset: (x: 4pt, y: 0pt),
    outset: (y: 3pt),
    radius: 4pt,
  )

  show raw.where(block: true): block.with(
    inset: 10pt,
    radius: 4pt,
  )

  show link: set text(fill: auxColor)

  show: thmrules.with(qed-symbol: [#text[❏]])

  set document()

  set par(
    justify: true,
    first-line-indent: (
      all: true,
      amount: 1em,
    ),
  )

  body

  pagebreak(weak: true)

  bibliography("references.bib", style: "association-for-computing-machinery")
}

#let abst(
  title: "",
  subtitle: "",
  author: "",
  date: (datetime.today().year(), datetime.today().month(), datetime.today().day()),
  body,
) = {
  set page(numbering: "1", number-align: center)

  set heading(numbering: "1.1")

  set text(size: base-text-size, font: font-base)

  show math.equation: set text(font: font-math)

  show raw: set text(size: 7pt, font: font-code)

  show raw: set text(font: font-code)

  show raw.where(block: false): box.with(
    inset: (x: 4pt, y: 0pt),
    outset: (y: 3pt),
    radius: 4pt,
  )

  show raw.where(block: true): block.with(
    inset: 10pt,
    radius: 4pt,
  )

  show link: set text(fill: auxColor)

  set par(justify: true)

  show: thmrules.with(qed-symbol: [#text  [❏]])

  set document(title: title)

  grid(
    columns: 1fr,
    align: (center + horizon),
    rect(stroke: none)[
      #block(text(weight: 700, 1.75em, title))
    ],
    v(.5cm),
    rect(stroke: none)[
      #pad(
        top: 1em,
        x: 1em,
        author,
      )
    ],
    v(1cm),
  )
  body
}

#let leancode(code, links: (), note: none) = {
  let code-text = if code.func() == raw {
    code.text
  } else {
    let raw-elem = code.children.find(it => it.func() == raw)
    if raw-elem != none { raw-elem.text } else { "" }
  }

  block(
    width: 100%,
    stroke: (left: 1pt + luma(0)),
    inset: 0pt,
    breakable: true,
  )[
    #block(
      width: 100%,
      fill: luma(250),
      inset: (x: 4pt, y: 8pt),
      spacing: 0pt,
    )[
      #set par(justify: false, first-line-indent: 0pt)
      #set text(fill: rgb("#000000"), size: 10pt, font: font-code)
      #show raw: set text(font: font-code)
      #raw(code-text, lang: "lean", block: true, syntaxes: "assets/syntaxes/Lean.sublime-syntax")
    ]


    #block(width: 100%, inset: (x: 12pt, y: 4pt), spacing: 0pt)[
      #set par(first-line-indent: 0pt)
      #grid(
        columns: (auto, 1fr),
        align: (left + horizon, right + horizon),
        if links.len() > 0 {
          text[
            #strong[#if links.len() > 1 { "Related Sources" } else { "Related Source" }:]
            #text(size: 8pt)[#enum(..links.map(l => link(SOURCE + "/" + l)[#text(font: font-code)[#l]]))]
          ]
        },
      )
      #if note != none {
        text[*Note:* #note]
      }
    ]
  ]
}

#let sqthmbox(
  title,
  dash: "solid",
  base: "heading",
) = thmbox(
  "theorem",
  title,
  base: base,
  inset: (left: 0pt, top: 0pt, bottom: 0pt),
  titlefmt: body => [
    #text(font: font-alter, size: base-text-size)[*#body*]
  ],
  namefmt: name => [
    #text(font: font-alter, size: base-text-size)[*(#name)*]
  ],
  separator: [
    #h(.4em)
  ],
  base_level: 1,
  breakable: true,
)

#let barthmbox(
  title,
  dash: "solid",
) = thmbox(
  "theorem",
  title,
  radius: 0pt,
  inset: (left: 0pt, top: 0pt, bottom: 0pt),
  titlefmt: body => [
    #text(font: font-alter, size: base-text-size)[*#body*]
  ],
  namefmt: name => [
    #text(font: font-alter, size: base-text-size)[*(#name)*]
  ],
  separator: [
    #h(.4em)
  ],
  base_level: 1,
  breakable: true,
)

#let lemma = sqthmbox("Lemma")

#let theorem = sqthmbox("Theorem")

#let proposition = sqthmbox("Proposition")


#let fact = sqthmbox("Fact")

#let corollary = sqthmbox("Corollary", base: "theorem")

#let definition = barthmbox("Definition")

#let notation = barthmbox("Notation", dash: "dotted")

#let remark = barthmbox("Remark", dash: "dotted")

#let example = barthmbox("Example")

#let problem = barthmbox("Problem")

#let conjecture = barthmbox("Conjecture")

#let proof = thmproof(
  "proof",
  [_Proof._],
  titlefmt: body => [
    #text(font: font-alter, size: base-text-size)[#body]
  ],
  separator: [
    #h(.4em)
  ],
)

