#import "@preview/ctheorems:1.1.3": *
#import "@preview/curryst:0.5.0": prooftree, rule
#import "@preview/itemize:0.2.0" as el

#let auxColor = color.hsl(205deg, 55%, 40%)

#let base-text-size = 11pt
#let font-base = ("libertinus serif", "Shippori Mincho B1")
#let font-alter = font-base
#let font-math = ("New Computer Modern Math", "New Computer Modern Sans Math", "libertinus serif")
#let font-code = "JuliaMono"

#let SOURCE = "https://github.com/FormalizedFormalLogic/Foundation/blob/master"

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
  show raw: set text(font: font-code, size: 8pt)

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

  show: el.default-enum-list.with(
    fill: black,
    font: font-base,
    size: base-text-size,
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

  show raw: set text(size: 6pt, font: font-code)

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
  set raw(lang: "lean")

  block(
    width: 100%,
    breakable: true,
    inset: (y: 16pt),
    clip: true,
  )[
      #grid(
        gutter: 8pt,
        block(
          width: 100%,
        )[
          #set par(justify: false, first-line-indent: 10pt)
          #set text(fill: rgb("#040404"), size: 9pt, font: font-code)
          #show raw: set text(font: font-code)
          #align(left, code)
        ],
        if links.len() > 0 {
          grid(
            columns: (1fr, 1fr),
            gutter: 6pt,
            align: (right, left),
            text(10pt, smallcaps[Source:]),
            text(8pt, enum(..links.map(l => link(SOURCE + "/" + l)[#text(font: font-code)[#l]])))
          )
        },
        if note != none {
          grid(
            columns: (1fr, 1fr),
            gutter: 6pt,
            align: (right, left),
            text(10pt, smallcaps[Note:]),
            text(10pt, note)
          )
        }
      )
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

