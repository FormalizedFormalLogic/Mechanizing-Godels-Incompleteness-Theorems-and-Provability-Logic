#import "@preview/ctheorems:1.1.3": *
#import "@preview/curryst:0.5.0": prooftree, rule

#let auxColor = rgb("#00f")

#let base-text-size = 11pt
#let font-base = ("libertinus serif", "Shippori Mincho B1")
#let font-alter = font-base
#let font-math = ("New Computer Modern Math", "New Computer Modern Sans Math", "libertinus serif")
#let font-code = "JuliaMono"

#let init(body) = {
  set page(
    "a4",
    numbering: "1",
    number-align: center,
    margin: (left: 40mm, right: 40mm),
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

  pagebreak()

  bibliography("references.bib")
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

#let _lean-border = luma(210)

#let leancode(code, links: (), note: none) = {
  let code-text = if code.func() == raw {
    code.text
  } else {
    let raw-elem = code.children.find(it => it.func() == raw)
    if raw-elem != none { raw-elem.text } else { "" }
  }

  block(
    width: 100%,
    stroke: (0.5pt + _lean-border),
    inset: 0pt,
    breakable: true,
    clip: true,
  )[
    #block(width: 100%, fill: luma(220), inset: (x: 12pt, y: 4pt))[
      #grid(
        columns: (auto, 1fr),
        align: (left + horizon, right + horizon),
        if links.len() > 0 {
          text(size: 8pt, fill: auxColor)[
            #links.map(l => link(l)[#l.split("/").last().split("#").first()]).join(h(8pt))
          ]
        },
      )
    ]

    #block(
      width: 100%,
      fill: luma(250),
      inset: (x: 8pt, y: 12pt),
      text(fill: rgb("#000000"), 9pt, font: font-code, raw(code-text, lang: "lean")),
    )

    #if note != none {
      line(length: 100%, stroke: 0.5pt + _lean-border)
      block(width: 100%, inset: (x: 12pt, y: 8pt))[
        #text(size: 9pt)[
          #show raw: set text(1em)
          *Mechanization Note:* #note
        ]
      ]
    }
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

