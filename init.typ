#import "@preview/ctheorems:1.1.3": *

#let lightlightgray = luma(0)
#let lightgray = luma(0)
#let auxColor = rgb("#00f")

#let base-text-size = 11pt
#let font-base = ("libertinus serif", "Shippori Mincho B1")
#let font-alter = font-base
#let font-math = ("New Computer Modern Math", "New Computer Modern Sans Math", "libertinus serif")
#let font-code = ("JuliaMono")

#let init(body) = {
  set page("a4", numbering: "1", number-align: center)

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

  show: thmrules.with(qed-symbol: [#text(fill: lightgray)[❏]])

  set document()
  
  body

  pagebreak()
  
  bibliography("references.bib")
}

#let abst(
    title: "",
    subtitle: "",
    author: "",
    date: (datetime.today().year(), datetime.today().month(), datetime.today().day()),
    body
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

  show: thmrules.with(qed-symbol: [#text(fill: lightgray)[❏]])

  set document(title: title)

  grid(
    columns: (1fr),
    align: (center + horizon),
    rect(stroke: none)[
      #block(text(weight: 700, 1.75em, title))
    ],
    v(.5cm),
    rect(stroke: none)[
      #pad(
        top: 1em,
        x: 1em,
        author
      )
    ],
    v(1cm),
  )
  body
}

= theorems

#let sqthmbox(
    title,
    color: lightlightgray,
    color2: lightgray,
    dash: "solid",
    base: "heading") = thmbox(
  "theorem",
  title,
  base: base,
  inset: (left: 0pt, top: 0pt, bottom: 0pt),
  titlefmt: body => [
    #text(font: font-alter, size: base-text-size, fill: color2)[*#body*]
  ],
  namefmt: name => [
    #text(font: font-alter, size: base-text-size, fill: color2)[*(#name)*]
  ],
  separator: [
    #h(.4em) 
  ],
  base_level: 1,
  breakable: true,
)

#let barthmbox(
    title,
    color: lightlightgray,
    color2: lightgray,
    dash: "solid") = thmbox(
  "theorem",
  title,
  radius: 0pt,
  inset: (left: 0pt, top: 0pt, bottom: 0pt),
  titlefmt: body => [
    #text(font: font-alter, size: base-text-size, fill: color2)[*#body*] 
  ],
  namefmt: name => [
    #text(font: font-alter, size: base-text-size, fill: color2)[*(#name)*]
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

#let corollary = sqthmbox("Corollary", base: "theorem", )

#let definition = barthmbox("Definition")

#let notation = barthmbox("Notation", color: auxColor, color2: auxColor, dash: "dotted")

#let remark = barthmbox("Remark", color: auxColor, color2: auxColor, dash: "dotted")

#let example = barthmbox("Example")

#let problem = barthmbox("Problem")

#let conjecture = barthmbox("Conjecture")

#let proof = thmproof(
  "proof",
  [_Proof._],
  titlefmt: body => [
    #text(font: font-alter, size: base-text-size, fill: lightgray)[#body]
  ],
  separator: [
    #h(.4em)
  ],
)

#let struct(body) = {
  block(
    width: 100%,
    stroke: (left: (thickness: 1pt, paint: luma(230))),
    inset: (left: 12pt, top: 5pt, bottom: 8pt))[#body]
}