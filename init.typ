#import "@preview/ctheorems:1.1.3": *
#import "@preview/curryst:0.5.0": prooftree, rule

#let auxColor = color.hsl(205deg, 55%, 40%)
#let codeBgColor = luma(245)

#let base-text-size = 10pt
#let small-text-size = 9pt
#let title-text-size = 14pt
#let font-text = ("New Computer Modern", "Libertinus Serif")
#let font-math = ("New Computer Modern Math", "Libertinus Serif")
#let font-code = "JuliaMono"

#let paper-size = "a4"
#let page-margin = (left: 18mm, right: 18mm, top: 26mm, bottom: 26mm)
#let par-spacing = 0.75em


// リンクのパスの先頭ディレクトリ（リポジトリ名）から宛先リポジトリを解決する
#let REPO_SOURCES = (
  "Foundation": "https://github.com/FormalizedFormalLogic/Foundation/blob/master",
  "ProvabilityLogic": "https://github.com/FormalizedFormalLogic/ProvabilityLogic/blob/main",
)
// リンクは (リポジトリ名, リポジトリ内パス) のタプルで指定する
#let lean-link(index, l) = {
  let (repo, path) = l
  link(REPO_SOURCES.at(repo) + "/" + path)[
    #(index + 1)
  ]
}


// ---- 著者・所属 ----

#let author(name, orcid: none, insts: ()) = {
  if type(insts) != array { insts = (insts,) }
  (name: name, orcid: orcid, insts: insts)
}

#let institute(name, addr: none, email: none, url: none) = (
  name: name,
  addr: addr,
  email: email,
  url: url,
)

#let abbrev-name(name) = {
  let parts = name.split(" ")
  let given = parts.slice(0, -1).map(w => w.split("-").map(p => p.first() + ".").join("-"))
  (..given, parts.last()).join(" ")
}

#let running-author-of(authors) = {
  let ns = authors.map(a => abbrev-name(a.name))
  if ns.len() == 0 { none } else if ns.len() == 1 {
    ns.first()
  } else if ns.len() == 2 {
    ns.join(" and ")
  } else {
    [#ns.first() et al.]
  }
}

#let join-authors(items) = {
  if items.len() == 0 { [No Author Given] } else if items.len() == 1 {
    items.first()
  } else if items.len() == 2 {
    items.join([ and ])
  } else {
    items.slice(0, -1).join([, ]) + [, and ] + items.last()
  }
}


// ctheorems の ref ルールは `numbering: none` の環境を参照すると落ちるので，そこだけ先に処理する
#let thmref-fallback(it) = {
  let el = it.element
  if el != none and el.func() == figure and el.kind == "thmenv" and el.numbering == none {
    link(it.target, el.supplement)
  } else { it }
}

#let thmnumber(target) = context {
  let el = query(target).first()
  let meta = query(selector(<meta:thmenvcounter>).after(el.location())).first()
  numbering(el.numbering, ..thmcounters.at(meta.location()).at("latest"))
}


// ---- 本体 ----

#let init(
  title: [],
  running-title: none,
  running-author: auto,
  thanks: none,
  authors: (),
  abstract: none,
  keywords: (),
  acknowledgements: none,
  interests: none,
  lang: "en",
  body,
) = {
  // 脚注の中の `@thm:...` にも効かせるため，文書の最も外側で適用する
  show: thmrules.with(qed-symbol: [❏])
  show ref: thmref-fallback

  set document(author: authors.map(a => a.name), title: title)
  set text(font: font-text, lang: lang, size: base-text-size)
  set par(leading: 0.5em, spacing: par-spacing)

  set page(
    paper: paper-size,
    margin: page-margin,
    header-ascent: 1.6em,
    footer-descent: 2em,
  )

  let header-author = if running-author == auto {
    running-author-of(authors)
  } else { running-author }
  let header-title = if running-title == none { title } else { running-title }

  set page(header: context {
    let n = counter(page).get().first()
    if n == 1 { return none }
    if calc.odd(n) {
      align(right)[#header-title #h(1cm) #n]
    } else {
      align(left)[#n #h(1cm) #header-author]
    }
  })

  set heading(numbering: "1.1")
  show heading: it => {
    // 見出し番号と本文の間隔は Typst 既定より広く取る
    let head = if it.numbering == none { it.body } else {
      counter(heading).display(it.numbering) + h(4.5mm) + it.body
    }
    if it.level == 1 {
      set text(12pt, weight: "bold")
      block(above: 18pt, below: 16pt, head)
    } else if it.level == 2 {
      set text(10pt, weight: "bold")
      block(above: 18pt, below: 8pt, head)
    } else if it.level == 3 {
      set text(10pt, weight: "bold")
      // run-in 見出し
      block(below: 0em, height: 2em + par-spacing, spacing: 0em) + head
    } else {
      set text(10pt, weight: "regular", style: "italic")
      block(below: 0em, height: 1.3em + par-spacing, spacing: 0em) + head
    }
  }

  set super(size: 8pt)
  show footnote.entry: set text(small-text-size)
  set footnote.entry(
    separator: line(start: (0pt, 0pt), length: 57pt, stroke: 0.5pt),
    indent: 1mm,
  )

  set figure(gap: 4.5mm, placement: none)
  set figure(supplement: it => if it.func() == image { [Fig.] } else if it.func() == table {
    [Table]
  } else { [Figure] })
  set figure.caption(separator: [. ])
  show figure.caption: it => align(center)[
    *#it.supplement #context it.counter.display()#it.separator*#it.body
  ]
  show figure.where(kind: table): set figure.caption(position: top)
  show figure.where(kind: image): set image(width: 100%)
  show figure: it => {
    // 定理環境も figure なので除く
    if it.kind == "thmenv" { return it }
    set text(small-text-size)
    set align(left)
    it
  }

  let table-stroke = 0.5pt
  set table(stroke: (_, _) => (left: table-stroke, right: table-stroke))
  set table(inset: (x: 0.7mm, y: 0.74mm))
  set table.hline(stroke: table-stroke)

  set math.equation(numbering: none)
  show math.equation.where(block: true): set block(above: 1em, below: 1em)
  show math.equation: set text(font: font-math)

  show raw: set text(font: font-code)
  show raw.where(block: false): box.with(
    fill: codeBgColor,
    inset: (x: 4pt, y: 0pt),
    outset: (y: 3pt),
    radius: 4pt,
  )

  show link: set text(fill: auxColor)

  set terms(indent: 1em, hanging-indent: 1.5em)

  // 中央寄せの表・証明図と説明リストは上下に余白を取る
  show align: set block(spacing: 1.2em)
  show terms: it => block(above: 1.2em, below: 1.2em, it)

  align(center, {
    block(
      text(weight: "bold", size: title-text-size, title)
        + if thanks != none {
          set super(size: 10pt)
          footnote(numbering: _ => [⋆#h(2pt)], thanks)
        },
    )

    v(11mm)

    let insts = authors.map(a => a.insts).flatten().dedup()

    join-authors(authors.map(a => {
      let refs = a.insts.map(i => str(insts.position(x => x == i) + 1)).join(",")
      let orcid = if a.orcid != none { [\[#a.orcid\]] } else { none }
      [#a.name#super[#refs#orcid]]
    }))

    v(6mm)

    {
      set text(small-text-size)
      set par(leading: 0.65em, spacing: 0.65em)
      if insts.len() == 0 { [No Institute Given] } else {
        insts
          .enumerate()
          .map(((i, inst)) => {
            let lines = (
              {
                super[#(i + 1)]
                h(0.2em)
                inst.name
                if inst.addr != none [, #inst.addr]
              },
            )
            if inst.email != none {
              lines.push(link("mailto:" + inst.email, inst.email))
            }
            if inst.url != none { lines.push(link(inst.url)) }
            lines.join(linebreak())
          })
          .join(parbreak())
      }
    }

    let has-abstract = abstract not in (none, [])
    let has-keywords = keywords.len() > 0
    if has-abstract or has-keywords {
      v(11mm)
      block(width: 85%, {
        set align(left)
        set par(justify: true)
        set text(size: small-text-size)
        if has-abstract [*Abstract.* #abstract]
        if has-keywords {
          if has-abstract { v(4.5mm) }
          let display = if type(keywords) == str { keywords } else {
            keywords.join([ $dot$ ])
          }
          [*Keywords:* #display]
        }
      })
    }
  })

  v(18pt)

  show figure.where(kind: "thmenv"): set par(first-line-indent: (all: false, amount: 1em))

  set par(justify: true, first-line-indent: (all: true, amount: 1em))

  body

  pagebreak(weak: true)

  set text(size: small-text-size)
  if acknowledgements != none {
    block(above: 1.5em)[*Acknowledgements.* #acknowledgements]
  }
  if interests != none {
    block(above: 1.5em)[*Disclosure of Interests.* #interests]
  }

  show std.bibliography: set text(small-text-size)
  bibliography("references.bib", style: "assets/springer-lecture-notes-in-computer-science.csl")
}


// ---- Lean のコード ----

// 本文の版面より少しはみ出させる
#let leancode-width = 100%
#let leancode(code, links: (), note: none) = {
  let code-text = if code.func() == raw {
    code.text
  } else {
    let raw-elem = code.children.find(it => it.func() == raw)
    if raw-elem != none { raw-elem.text } else { "" }
  }
  align(center, block(
    width: leancode-width,
    above: 1.6em,
    below: 0.5em,
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
    width: leancode-width,
    above: 0.5em,
    below: 1.6em,
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
}


// ---- 定理環境 ----
// 識別子を "theorem" で揃えているので，全環境が節ごとの通し番号を共有する

#let sqthmbox(title) = thmbox(
  "theorem",
  title,
  base: "heading",
  base_level: 1,
  inset: (top: 8pt, bottom: 8pt),
  radius: 0pt,
  titlefmt: strong,
  namefmt: name => strong[(#name)],
  separator: h(.4em),
  breakable: true,
)

#let definition = sqthmbox("Definition")
#let notation = sqthmbox("Notation")
#let lemma = sqthmbox("Lemma")
#let theorem = sqthmbox("Theorem")
#let proposition = sqthmbox("Proposition")
#let fact = sqthmbox("Fact")
#let corollary = sqthmbox("Corollary")
#let remark = sqthmbox("Remark")
#let example = sqthmbox("Example")
#let problem = sqthmbox("Problem")
#let conjecture = sqthmbox("Conjecture")

#let proof = thmproof(
  "proof",
  [_Proof._],
  titlefmt: it => text(size: base-text-size, it),
  separator: h(.4em),
)


// ================= Notations =================

// --- General math symbols ---

#let Nat = $bb(N)$

#let PowerSet = $cal(upright("P"))$

#let proves = $class("relation", tack.r)$
#let nproves = $class("relation", tack.r.not)$

#let models = $class("relation", tack.rr)$

#let Box = $class("unary", square)$
#let Boxdot = $class("unary", ⊡)$
#let Dia = $class("unary", diamond)$
#let interpret = $class("binary", triangle.r.small)$
#let land = $and$
#let limp = $->$
#let liff = $<->$
#let lor = $or$
#let lnot = $not$

#let PropVar = $upright("Var")$

#let Logic(L) = $sans(upright(#L))$
#let sumQuasiNormal(L1, L2) = $#L1 + #L2$
#let LogicD = Logic("D")
#let LogicA = Logic("A")
#let LogicGLPoint3 = Logic("GL.3")
#let LogicGLAlpha(a) = $Logic("GL")_(#a)$
#let LogicGLBetaMinus(b) = $Logic("GL")_(#b)^-$
#let trace(x) = $upright("tr")(#x)$
#let subfml(A) = $upright("Sub")(#A)$
#let prebox(X) = $Box^(-1) #X$

#let LogicS4 = Logic("S4")
#let LogicGL = Logic("GL")
#let LogicGLPlusBoxBot(n) = $LogicGL + Box^#n bot$
#let LogicS = Logic("S")
#let LogicGrz = Logic("Grz")

#let LogicIQL = Logic("IQL")

// Intuitionistic modal logics
#let LogiciK = Logic("iK")
#let LogiciGL = Logic("iGL")
#let LogiciSL = Logic("iSL")

// Polymodal provability logic and its strictly positive fragments
#let LogicGLP = Logic("GLP")
#let LogicRC = Logic("RC")
#let LogicWC = Logic("WC")
#let LogicQRC1 = $Logic("QRC"_1)$

#let Gentzen(L) = $cal("G")_(#L)$
#let GentzenGL = Gentzen(LogicGL)
#let GentzenGLPoint3 = Gentzen(LogicGLPoint3)
#let GentzenGrz = Gentzen(LogicGrz)

#let GentzenS = Gentzen(LogicS)
#let GentzenD = Gentzen(LogicD)

#let GentzenWithCutGL = $Gentzen(LogicGL) + ("Cut")$
#let GentzenWithCutGrz = $Gentzen(LogicGrz) + ("Cut")$
#let GentzenWithCutS = $Gentzen(LogicS) + ("Cut")$
#let GentzenWithCutD = $Gentzen(LogicD) + ("Cut")$

// Levelled sequent arrows of the sequent calculi for S and D
#let seq(l) = $attach(tr: #l, =>)$
#let seq1 = seq("1")
#let seq2 = seq("2")
#let seq3 = seq("3")

#let Hilbert(L) = $cal("H")_(#L)$
#let HilbertGL = Hilbert(LogicGL)
#let HilbertGrz = Hilbert(LogicGrz)

// Use for *standard* provability predicate
#let Pr(T) = $attach(br: #T, sans("Pr"))$
#let RPr(T, f, e) = $attach(tr: chevron.l #f\, #e chevron.r, br: #T, sans("Pr"))$
#let RGodel(T, f, e) = $attach(tr: (#f\, #e), br: #T, sans("G"))$
#let supexp = $sans("supexp")$
#let iterexp(x, y) = $attach(tr: #y, br: #x, 2)$

#let height(T) = $upright("hgt")(#T)$
#let rank(x) = $upright("rank")(#x)$

#let True(x) = $sans("True")(#x)$
#let TruePartial(Gamma, x) = $sans("True")_(#Gamma) (#x)$
#let ProvLogic(T, U) = $upright("PL")_(#T) (#U)$
#let Thm(T) = $upright("Thm")(#T)$
#let Rfn(G, T) = $upright("Rfn")_(#G) (#T)$
#let Rep(S) = $sans("Rep")_(#S)$
#let ArithSent = $upright("Sent")_upright("A")$
#let StrongInterpret(f, B) = $#f^(upright("s"))_(#B)$

// Craig companion: Craig's trick で r.e. 理論から得られる同等な原始再帰的理論
#let Craig(T) = $#T^upright("C")$

#let Theory(T) = $sans(upright(#T))$
#let PA = Theory("PA")
#let PAMinus = $PA^-$
#let TA = Theory("TA")
#let HA = Theory("HA")
#let CH = Theory("CH")
#let ZF = Theory("ZF")
#let ZFC = Theory("ZFC")
#let TC = Theory("TC")

#let Axiom(A) = $upright(#A)$
#let AxiomK = $Axiom("K")$
#let AxiomL = $Axiom("Löb")$
#let AxiomT = $Axiom("T")$
#let AxiomGrz = $Axiom("Grz")$

#let Cond(C) = $bold(#C)$
#let D1 = $Cond("D1")$
#let D2 = $Cond("D2")$
#let D3 = $Cond("D3")$
#let Kre = $Cond("Kre")$
#let Ros = $Cond("Ros")$

#let System(X) = $bold(#X)$

#let LK = System("LK")
#let LJ = System("LJ")
#let wforces = $attach(forces, br: "w")$

#let Lang(T) = $cal(L)_(#T)$
#let LOR = Lang("OR")
#let Ind(x) = $sans("I")#x$
#let ISigma1 = $Ind(Sigma_1)$
#let Robinson = $sans("Q")$
#let R0 = $sans("R"_0)$
#let BussS12 = $sans("S")^1_2$
#let Con(T) = $sans("Con")_(#T)$

#let Universe = $bold(upright(V))$
#let Bit = $"Bit"$
#let Fix = $bold("Fix")$

#let Bew = $class("unary", frak("B"))$
#let Wid = $class("unary", frak("W"))$

#let Godel(B) = $sans("G")_#B$
#let fixpoint(x) = $sans("fixedpoint")_#x$
#let Rosser = $frak(R)$

#let Jeroslow(W) = $sans("J")_#W$
#let Safe(B, W) = $sans("Safe")_(#B,#W)$
#let FLoN(B, W) = $sans("FLoN")_(#B,#W)$

#let sepWithCommaMath(..args) = args.pos().join($,$)

#let brak(..args) = $lr(chevron.l sepWithCommaMath(..args) chevron.r)$
#let quant(Q, ..args) = $#Q sepWithCommaMath(..args) space.narrow$
#let fal(..args) = $quant(forall, ..args)$
#let exs(..args) = $quant(exists, ..args)$
#let nexs(..args) = $quant(exists.not, ..args)$
#let exsUniq(..args) = $quant(exists!, ..args)$

#let godelize(x) = $lr(⌜ #x ⌝)$
#let num(x) = $overline(#x)$
