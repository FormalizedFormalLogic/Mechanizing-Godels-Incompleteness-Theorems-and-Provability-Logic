#import "@preview/fine-lncs:0.6.5": author, institute, lncs, proof, theorem
#import "@preview/fine-lncs:0.6.5": author, institute, lncs, theorem, proof
#import "@preview/ctheorems:1.1.3": *
#import "@preview/curryst:0.5.0": prooftree, rule

#let auxColor = color.hsl(205deg, 55%, 40%)

#let base-text-size = 10pt
#let font-math = ("New Computer Modern Math", "libertinus serif")
#let font-code = "JuliaMono"


// リンクのパスの先頭ディレクトリ（リポジトリ名）から宛先リポジトリを解決する
#let REPO_SOURCES = (
  "Foundation": "https://github.com/FormalizedFormalLogic/Foundation/blob/master",
  "ProvabilityLogic": "https://github.com/FormalizedFormalLogic/ProvabilityLogic/blob/main",
)
// リンクはタプル ("Foundation", "Foundation/FirstOrder/...") で指定する:
// 第1要素がリポジトリ名（REPO_SOURCES のキー），第2要素がリポジトリ内のパス
#let lean-link(index, l) = {
  let (repo, path) = l
  link(REPO_SOURCES.at(repo) + "/" + path)[
    #(index + 1)
  ]
}

#let init(
  title: "",
  authors: (),
  date: (datetime.today().year(), datetime.today().month(), datetime.today().day()),
  abstract: "",
  keywords: (),
  body,
) = {
  // fine-lncs は著者が2人以上だと一律 "A et al." にするので，
  // LNCS の慣例に従い2人なら "A and B" とする（3人以上は et al.）
  let abbrev(name) = {
    let ns = name.split(" ")
    [#ns.at(0).split("-").map(w => w.at(0) + ".").join("-") #ns.last()]
  }
  let running-author = {
    let an = authors.map(a => abbrev(a.name))
    if an.len() == 2 [#an.at(0) and #an.at(1)] else { none }
  }

  show: lncs.with(
    title: title,
    authors: authors,
    running-author: running-author,
    abstract: abstract,
    keywords: keywords,
    bibliography: bibliography("references.bib", style: "assets/springer-lecture-notes-in-computer-science.csl"),
  )

  set heading(numbering: "1.1")

  set text(size: base-text-size)

  show math.equation: set text(font: font-math)

  // show raw: set text(size: 7pt, font: font-code)
  show raw: set text(font: font-code)

  show raw.where(block: false): box.with(
    inset: (x: 4pt, y: 0pt),
    outset: (y: 3pt),
    radius: 4pt,
  )

  show link: set text(fill: auxColor)

  show: thmrules.with(qed-symbol: [#text[❏]])

  // For theorem environment
  show figure.where(kind: "thmenv"): set par(first-line-indent: (all: false, amount: 1em))

  set par(
    justify: true,
    first-line-indent: (
      all: true,
      amount: 1em,
    ),
  )

  body

  pagebreak(weak: true)
}

#let leancode(code, links: (), note: none) = {
  let code-text = if code.func() == raw {
    code.text
  } else {
    let raw-elem = code.children.find(it => it.func() == raw)
    if raw-elem != none { raw-elem.text } else { "" }
  }
  block(inset: 0.5em)
  align(center, block(
    width: 120%,
    // fill: rgb("#eee"),
    stroke: 0.5pt + black,
    inset: (x: 1em),
    breakable: true,
    clip: true,
    align(left, grid(
      block(
        inset: 1em,
        text(
          size: 8pt,
          font: font-code,
          raw(
            lang: "lean",
            block: true,
            syntaxes: "assets/Lean.sublime-syntax",
            code-text,
          ),
        ),
      ),
      if note != none {
        block(
          inset: 1em,
          text(8pt)[#smallcaps[Note:] #note],
        )
      },
    )),
  ))
  align(center, block(
    width: 120%,
    if links.len() > 0 {
      grid(
        columns: (1fr, auto),
        gutter: 6pt,
        align: (right, left),
        smallcaps[Source:],
        for (index, li) in links.enumerate() {
          lean-link(index, li)
        },
      )
    },
  ))
  block(inset: 0.5em)
}


#let sqthmbox(
  title,
  dash: "solid",
  base: "heading",
) = thmbox(
  "theorem",
  title,
  base: base,
  //stroke: (left: 2pt + luma(200)),
  inset: (top: 8pt, bottom: 8pt),
  radius: 0pt,
  titlefmt: body => [
    #text[*#body*]
  ],
  namefmt: name => [
    #text[*(#name)*]
  ],
  separator: [
    #h(.4em)
  ],
  base_level: 1,
  breakable: true,
)


#let definition = sqthmbox("Definition")
#let notation = sqthmbox("Notation", dash: "dotted")
#let lemma = sqthmbox("Lemma")
#let theorem = sqthmbox("Theorem")
#let proposition = sqthmbox("Proposition")
#let fact = sqthmbox("Fact")
#let corollary = sqthmbox("Corollary", base: "theorem")
#let remark = sqthmbox("Remark", dash: "dotted")
#let example = sqthmbox("Example")
#let problem = sqthmbox("Problem")
#let conjecture = sqthmbox("Conjecture")

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

