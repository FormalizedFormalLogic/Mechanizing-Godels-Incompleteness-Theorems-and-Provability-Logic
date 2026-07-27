#import "@preview/ctheorems:1.1.3": *
#import "@preview/curryst:0.5.0": prooftree, rule

#let auxColor = color.hsl(205deg, 55%, 40%)

#let base-text-size = 11pt
#let font-base = "Nimbus Roman"
#let font-alter = "Nimbus Sans"
#let font-math = ("New Computer Modern Math", "libertinus serif")
#let font-code = "JuliaMono"

#let SOURCE = "https://github.com/FormalizedFormalLogic/Foundation/blob/master"

// リンクのパスの先頭ディレクトリ（リポジトリ名）から宛先リポジトリを解決する
#let REPO_SOURCES = (
  "Foundation": "https://github.com/FormalizedFormalLogic/Foundation/blob/master",
  "ProvabilityLogic": "https://github.com/FormalizedFormalLogic/ProvabilityLogic/blob/main",
)
// リンクはタプル ("Foundation", "Foundation/FirstOrder/...") で指定する:
// 第1要素がリポジトリ名（REPO_SOURCES のキー），第2要素がリポジトリ内のパス
#let lean-link(l) = {
  let (repo, path) = l
  let base = REPO_SOURCES.at(repo, default: SOURCE)
  link(base + "/" + path)[#path]
}

// notations.typ の LARGE/Large/normalsize 相当．
// notations.typ が init.typ を import するため，循環を避けてここで定義する．
#let sized(size, it) = rect(stroke: none, text(size: size)[#it])

#let init(
  title: "",
  authors: (),
  date: (datetime.today().year(), datetime.today().month(), datetime.today().day()),
  abstract: "",
  body,
) = {
  set page(
    "a4",
    numbering: "1",
    number-align: center,
  )
  set document(
    title: title,
    author: authors.map(a => a.name),
    date: datetime(year: date.at(0), month: date.at(1), day: date.at(2)),
  )

  set heading(numbering: "1.1")
  show heading: set text(font: font-alter)

  set text(size: base-text-size, font: font-base)

  show strong: set text(font: font-alter)
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

  align(
    center,
    stack(
      text(size: 17.28pt, font: font-alter, weight: "bold", title),
      v(10mm),
      grid(
        columns: authors.map(_ => 1fr),
        ..authors.map(a => stack(
          sized(14.4pt, a.name),
          sized(10.95pt, a.affiliation),
          sized(10.95pt, raw(a.email)),
          // orcid が与えられた著者にのみ ORCID iD を添える
          ..if "orcid" in a {
            (
              sized(
                10.95pt,
                link(
                  "https://orcid.org/" + a.orcid,
                  box(baseline: 0.15em, image("assets/ORCID.svg", height: 0.9em)) + raw(a.orcid),
                ),
              ),
            )
          } else { () },
        )),
      ),
      v(4mm),
      sized(
        12pt,
        datetime(year: date.at(0), month: date.at(1), day: date.at(2)).display(
          "[month repr:long] [day padding:none], [year]",
        ),
      ),
      v(4mm),
    ),
  )

  align(
    center,
    stack(
      [*Abstract*],
      v(4mm),
      box(width: 80%, align(left, abstract)),
      v(8mm),
    ),
  )

  body

  pagebreak(weak: true)

  bibliography("references.bib", style: "association-for-computing-machinery")
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
    inset: 0pt,
    breakable: true,
  )[
    #block(
      width: 100%,
      inset: (x: 12pt, y: 8pt),
      stroke: (left: 2pt + auxColor),
      spacing: 0pt,
    )[
      // #set par(justify: false, first-line-indent: 0pt)
      // #show raw: set text(font: font-code)
      #text(size: 1em, font: font-code)[
        #raw(lang: "lean", block: true, syntaxes: "assets/syntaxes/Lean.sublime-syntax", code-text)
      ]
    ]

    #block(
      width: 100%,
      inset: (x: 12pt, y: 8pt),
      spacing: 0pt,
      stroke: (left: 2pt + luma(220)),
    )[
      #set par(first-line-indent: 0pt)
      #grid(
        columns: (auto, 1fr),
        align: (left + horizon, right + horizon),
        if links.len() > 0 {
          text(size: 0.9em)[
            #strong[#if links.len() > 1 { "Related Sources" } else { "Related Source" }:]
            #enum(..links.map(lean-link))
          ]
        },
      )
      #if note != none {
        text(size: 0.9em)[*Note:* #note]
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
  stroke: (left: 2pt + luma(0)),
  inset: (left: 12pt, top: 8pt, bottom: 8pt),
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

