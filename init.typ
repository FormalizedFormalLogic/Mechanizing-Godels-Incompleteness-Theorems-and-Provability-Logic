#import "@preview/fine-lncs:0.6.5": author, institute, lncs
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

  set math.equation(numbering: none)

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

#let thmnumber(target) = context {
  let el = query(target).first()
  let meta = query(selector(<meta:thmenvcounter>).after(el.location())).first()
  numbering(el.numbering, ..thmcounters.at(meta.location()).at("latest"))
}

#let proof = thmproof(
  "proof",
  [_Proof._],
  titlefmt: body => [
    #text(size: base-text-size)[#body]
  ],
  separator: [
    #h(.4em)
  ],
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

// 命題変数の集合（Lean の `Prop` と衝突するので Var と書く）
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

#let True(x) = $sans("True")(#x)$
#let TruePartial(Gamma, x) = $sans("True")_(#Gamma) (#x)$
#let ProvLogic(T, U) = $upright("PL")_(#T) (#U)$

#let Theory(T) = $sans(upright(#T))$
#let Peano = Theory("PA")
#let PAMinus = $Peano^-$
#let TrueArithmetic = Theory("TA")
#let HeytingArithmetic = Theory("HA")

#let Axiom(A) = $upright(#A)$
#let AxiomK = $Axiom("K")$
#let AxiomL = $Axiom("Löb")$
#let AxiomT = $Axiom("T")$
#let AxiomGrz = $Axiom("Grz")$

#let LOR = $cal(L)_"OR"$
#let Ind(x) = $sans("I")#x$
#let ISigma1 = $Ind(Sigma_1)$
#let Robinson = $sans("Q")$
#let R0 = $sans("R"_0)$
#let Con(T) = $sans("Con")_(#T)$

// 内部算術（G2 の証明で固定する IΣ₁ のモデルとその上の構成）
#let Universe = $bold(upright(V))$
#let Bit = $"Bit"$
// 類上の関数 Φ の不動点（Knaster--Tarski）
#let Fix = $bold("Fix")$

#let Bew = $class("unary", frak("B"))$
#let Wid = $class("unary", frak("W"))$

// 証明可能性の抽象化
#let Godel(B) = $sans("G")_#B$
#let fixpoint(x) = $sans("fixedpoint")_#x$
// Ros を満たす証明可能性述語
#let Rosser = $frak(R)$

// 反証可能性の抽象化
#let Jeroslow(W) = $sans("J")_#W$
#let Safe(B, W) = $sans("Safe")_(#B,#W)$
// 形式化された無矛盾律
#let FLoN(B, W) = $sans("FLoN")_(#B,#W)$

#let sepWithCommaMath(..args) = args.pos().join[,]

#let quant(Q, ..args) = $#Q sepWithCommaMath(..args) space.narrow$
#let fal(..args) = $quant(forall, ..args)$
#let exs(..args) = $quant(exists, ..args)$

#let godel(x) = $lr(⌜ #x ⌝)$
#let num(x) = $overline(#x)$
