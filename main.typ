#import "init.typ": *
#import "notations.typ": *

#show: thmrules
#show: init

#set page(footer: none)

#align(
  center,
  stack(
    LARGE[Mechanizing Gödel's Incompleteness Theorems \ and Provability Logic],
    v(10mm),
    grid(
      columns: (1fr, 1fr),
      stack(
        Large[Shogo Saito],
        normalsize[Tohoku University \ Mathematical Institute],
        normalsize[`saito.shogo.q8@dc.tohoku.ac.jp`],
      ),
      stack(
        Large[Mashu Noguchi],
        normalsize[Kobe Unversity \ Graduate School of System Informatics],
        normalsize[`251x054x@stu.kobe-u.ac.jp`],
      ),
    ),
    v(4mm),
    large[June 4, 2026],
    v(4mm),
  ),
)

#align(
  center,
  stack(
    [*Abstract*],
    v(4mm),
    box(width: 80%, align(left)[
      We formalized proofs of Gödel's first and second incompleteness theorems and
      Solovay's arithmetical completeness of $LogicGL$ and related results in Lean4 theorem prover.
    ]),
    v(8mm),
  ),
)

= Introduction

_Gödel's incompleteness theorems_ are among the most significant results in mathematical logic.
In his seminal paper @godel1931, he proved what is now known as the first incompleteness theorem (G1), and in a footnote, he outlined the second incompleteness theorem (G2).
G2 was later proved rigorously by Hilbert and Bernays @hilbertGrundlagenMathematikBd1939.
We state the theorems in modern terms:
G1, with Rosser's improvement @Rosser1936, states that for any consistent axiomatic system with sufficient expressive power to execute arithmetic, there exists a proposition that can neither be proved nor disproved within the system.
G2 states that, for any consistent _nice_ axiomatic system as in G1, the proposition formally representing the system's own consistency cannot be proved within the system itself.

Gödel also made another important observation: that provability can be regarded as a modality.
In his early work @godelInterpretationIntuitionischenAussagenkalkuls1933, he observed that the provability of intuitionistic logic can be treated similarly to the modal operator $Box$ in the modal logic now called #LogicS4.
However, it follows from G2, that abstracting the behavior of the provability predicate, the most central notion of the incompleteness theorems, does not yield #LogicS4.
Solovay @solovay1976 showed that the modal logic called #LogicGL precisely captures the behavior of the standard provability predicate.
This fact, known as _Solovay's arithmetical completeness theorem_, was a significant result that opened up the subfield of modal logic called _provability logic_.

On the other hand, recently, there have been much active works on mechanizing mathematics using interactive theorem provers, guaranteeing the validity of existing and new results, and providing AI/LLM-assisted or automated proving.
There are many well-known interactive theorem provers such as Rocq @RocqProver, Isabelle @Isabelle, HOL Light @HOLLight @HOLLightTutorial, Agda @Agda, and Lean @moura2021lean, and mathematics has been mechanized in each of them, including in the field of mathematical logic (some of these mechanizations are summarized in @AwesomeLogicFormalization).
In particular, for mechanizing Gödel's incompleteness theorems, this line of work began with Shankar in 1986 @Shankar1986 @Shankar1997, and continues with O'Connor @OConnor2005 @OConnor2009, Harrison @Harrison2006, Paulson @Paulson2015, and Popescu and Traytel @PopescuTraytel2019 @PopescuTraytel2021, Kirst and Peters @KirstPeters2023.
As for provability logic, modal-logical properties of #LogicGL, such as its semantical completeness and automated solvers, have been mechanized by Maggesi and Perini Brogi @maggesiMechanisingGodelLob2023, Gignoux @Gignoux2026.
However, these are either abstract or not full mechanizations within arithmetic.
For instance, O'Connor's implementation assumes several facts needed for the proof of G2 as axioms, and Paulson's mechanization of G2 uses hereditarily finite sets, not arithmetic.
To the best of our knowledge, no full formalization of the incompleteness theorems entirely within arithmetic is known, and consequently, no mechanization about provability logic has been reported.

In this paper, we present machine-assisted formalizations of Gödel's 1st and 2nd incompleteness theorems and Solovay's arithmetical completeness theorem.
Our work is carried out in Lean 4, an interactive theorem prover, together with mathlib4 @mathlib2020, its community-developed mathematics library.
Lean 4 is based on the Calculus of Inductive Constructions (CIC) @moura2021lean,
and features dependent types, quotient types, and support for noncomputable definitions, making it highly expressive.
In addition, its powerful metaprogramming infrastructure like aesop @inproceedings enables efficient proof automation and extensibility.

Our mechanization is currently hosted as a repository on GitHub, and the version we refer to is #link(SOURCE).
In this report, we will briefly and informally introduce the mathematical facts without omitting the essentials, and show the code of our mechanization corresponding to those facts.
However, for the sake of readability, note that in some places we have modified the hosted code.
Moreover, owing to motivations other than the incompleteness theorems and provability logic that this report focuses on, some implementations are stated as more general definitions.
We add comments where we deem it necessary, but for the actual working (verified) code, refer to the repository.


= 証明可能性論理

この節では，様相論理，特に証明可能性論理の形式化について述べる．
我々は，証明可能性論理という分野の中でも基本的かつ最重要の事実として，我々はSolovayの算術的完全性定理 @solovay1976 の形式化に成功した．
前節と同様に，定義や事実の導入は最小限に留める．
様相論理および証明可能性論理の詳細については，標準的な教科書 @chagrovModalLogic2001 @boolosLogicProvability1994 あるいは，サーベイ @japaridzeLogicProvability1998 @artemovProvabilityLogic2005 を参照されたい．

== 様相論理の基本的な性質など

まず，様相論理の基本的な枠組みを準備しよう．
Formulas of modal logic are defined from propositional variables (denotes #Prop), the primitive logical connectives $bot$ and $limp$, and the modal operator $Box$.
The remaining operators $top, lnot, land, lor, Dia$ are introduced as the usual abbreviations.
We write $[p := B]$ for substitution, and write $A[p := B]$ for the result of substituting $B$ for all occurrences of $p$ in $A$.

#leancode(
  links: (
    "Foundation/Modal/Formula/Basic.lean",
  ),
)[
  ```
  inductive Formula (α : Type*) where
    | atom   : α → Formula α
    | falsum : Formula α
    | imp    : Formula α → Formula α → Formula α
    | box    : Formula α → Formula α

  abbrev top : Formula α := imp falsum falsum
  abbrev neg (φ : Formula α) : Formula α := imp φ falsum
  abbrev or (φ ψ : Formula α) : Formula α := imp (neg φ) ψ
  abbrev and (φ ψ : Formula α) : Formula α := neg (imp φ (neg ψ))
  abbrev dia (φ : Formula α) : Formula α := neg (box (neg φ))

  abbrev Substitution (α) := α → (Formula α)

  def Formula.subst (s : Substitution α) : Formula α → Formula α
    | atom a  => (s a)
    | ⊥       => ⊥
    | □φ      => □(φ.subst s)
    | φ 🡒 ψ   => φ.subst s 🡒 ψ.subst s

  notation:80 φ "⟦" s "⟧" => Modal.Formula.subst s φ
  ```
]

論理とは論理式の集合としよう．
我々は論理 $LogicGL$ を定義するが，その方法はまずGentzen流のシークエント計算によって定める．
#LogicGL は一般にはHilbert流で定義するが，Kripke意味論に対する完全性を示す場合や，あるいはその他の重要な性質を示す際において，シークエント計算を導入したほうがいくらか証明が簡単であり，かつ，形式化の難易度も低くなる．
ここでの #LogicGL のGentzen流シークエント計算は，SambinとValentini @SV82 によるものである．
最終的には，以下の同値性を示すことができる．

最後に，証明可能性論理で重要な非正規な様相論理 $Logic("S")$ と $Logic("D")$ を導入する．
前者は Solovay @solovay1976 に，後者はJaparidze (Dzhaparidze) に由来する．
これらに純粋にはKripke意味論は適用できないが，適当に拡張したKripeモデルのクラスに対して健全かつ完全であることが知られている．ただしその説明は省略する．

#proposition[cf. @Vis84][
  以下同値．

  1. $Logic("S") proves A$
]

#proposition[cf. @Bek90][
  以下は同値．

  1. $Logic("D") proves A$
]

これらの意味論を用いて，以下の包含関係が成り立つ．

=== シークエント計算の応用について <sect:application-of-sequent-calculus>

SambinとValentini @SV82 ではさらに$LogicGL$ のシークエント計算に対してのいくつかの応用が示されている．
まず，純粋なシークエント計算であるため，Maeharaの手法を用いて，Craig補間定理(CIP)を示すことができる．

さらに，Boolos および Smorynskiは，$LogicGL$ のCIPから，#LogicGL の不動点定理を示すことができることを示している．この証明もシークエント計算を用いて形式化することができている．

#LogicGL の不動点定理は，例えば のでもLeanで形式化されている．
ここでは，その証明の形式化から，補間および不動点は，シークエント計算の導出木から構成的にLean上で計算することが可能であることを注意しておこう．

ただし，現状ではシークエント計算の導出木を自動で証明探索などによって構成することは出来ないので，単に具体的に導出木をこちらで別途手入力で計算する必要がある．また，例えばKripke意味論を用いて $LogicGL proves A$ を非構成的に証明している場合は当然その補間や不動点は計算可能ではない．

最後に $LogicS$ と $Logic("D")$ のCIPに関しての事実も形式化しているので，軽く述べおこう．

#proposition[@Bek87][
  $Logic("S")$ はCIPを持つ．
]

#proposition[@Bek89][
  $Logic("D")$ はCIPを持たない．
  特に，次の $A$ と $B$ に対しての補間が存在しない．
]

=== ラベル付きシークエント計算について

我々は，#LogicGL のラベル付きシークエント計算 @Neg14 についても形式化しているが，これは先行研究として MaggesiとPerini Brogi @maggesiMechanisingGodelLob2023 によるHOL Lightでの #LogicGL のラベル付きシークエント計算の形式化とほとんど方法としては同じであり，その意味では新規性はあまりない．
ただしいくつかの実装上の相違点については触れておこう．

MaggesiとPerini Brogiのシークエント計算の*実装の*停止性はメタの数学的事実として保証されている．
一方で，我々は実際にproof-searchを定義する際に，Leanの制約上としてそれがwell-foundedになるということによって，停止性を定理証明支援系の中で保証していると言える．
この点では我々のほうがより強い保証を与えていると言える．
しかし，MaggesiとPerini Brogiの形式化は実用上の有用性があり，停止性の保証は無いものの実際に計算を行わせてタクティク的に使うことが出来て，形式化上に現れる #LogicGL の簡単な証明を自動化することが出来ている．
他方我々の実装では，そのwell-foundednessの証明の実装上の制約上，我々のラベル付きシークエント計算を例えばLeanのタクティクとして使うことが出来ず，純粋に数学的事実としてラベル付きシークエント計算の諸性質が形式化されているに留まっている．
故に実用性上の優位性に関してはMaggesiとPerini Brogiの形式化のほうに軍配が上がっている．

また，ラベル付きシークエント計算で @sect:application-of-sequent-calculus で述べたようなCIPを示すことができるかは未解決であるため，現状では，#LogicGL の論理としての特徴を形式化する点においては，あまり有効ではないことは指摘しておく．

== 算術的完全性定理

== 証明可能性定理の分類定理

=== いくつかの `sorry` に関して

分類定理を形式化すること自体とは直接関係が無いものの，しかし証明可能性論理上のいくつかの事実は `sorry` のままで残されている．
