#import "init.typ": *
#import "notations.typ": *

#show: thmrules
#show: init

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
我々は，証明可能性論理という分野の中でも基本的かつ最重要の事実として，我々はSolovayの算術的完全性定理 @solovay1976 の形式化に成功している．
前節と同様に，定義や事実の導入は最小限に留める．
様相論理および証明可能性論理の詳細については，標準的な教科書 @chagrovModalLogic2001 @boolosLogicProvability1994 @smorynskiSelfReferenceModalLogic1985 あるいは，サーベイ @japaridzeLogicProvability1998 @artemovProvabilityLogic2005 を参照されたい．

== 様相論理の基本的な性質など

まず，様相論理の基本的な枠組みを準備しよう．
様相論理の論理式は，命題変数（その全体を #Prop と書く），原始的な論理結合子 $bot$ と $limp$，および様相演算子 $Box$ から構成される．
残りの演算子 $top, lnot, land, lor, Dia$ は通常の略記として導入する．
_代入_とは各命題変数に論理式を割り当てる写像 $s$ のことであり，$A[s]$ で $A$ に現れる各命題変数 $p$ を $s(p)$ で置き換えて得られる論理式を表す．
形式化においては，命題変数全体は任意の型 `α` としてパラメータ化されている．
例えば，`α` として `Empty` を選択することにより，命題変数を含まない論理式(closedとかletterlessと呼ぶ)を表現することが出来る．
論理式の有限集合 $Gamma$ に対して，$Box Gamma = { Box B | B in Gamma }$ と書く．

#leancode[
  ```
  inductive Formula (α : Type*)
  | atom : α → Formula α
  | bot  : Formula α
  | imp  : Formula α → Formula α → Formula α
  | box  : Formula α → Formula α

  abbrev neg (A : Formula α) : Formula α := A 🡒 ⊥
  abbrev top : Formula α := ∼⊥
  abbrev or (A B : Formula α) : Formula α := ∼A 🡒 B
  abbrev and (A B : Formula α) : Formula α := ∼(A 🡒 ∼B)
  abbrev dia (A : Formula α) : Formula α := ∼□(∼A)

  abbrev Substitution (α β) := α → Formula β

  def subst (s : Substitution α β) : Formula α → Formula β
    | atom a  => (s a)
    | ⊥       => ⊥
    | □A      => □(A.subst s)
    | A 🡒 B   => A.subst s 🡒 B.subst s
  notation:95 A "⟦" s "⟧" => Formula.subst s A
  ```
]

論理とは論理式の集合としよう．

#leancode[
  ```
  abbrev Logic (α) := Set (Formula α)
  ```
]

#LogicGL で重要なのはGentzen流のシークエント計算，Kripke意味論，そしてHilbert流の証明体系による3種類の特徴づけである．
#LogicGL は一般にはHilbert流で定義するが，Kripke意味論に対する完全性を示す場合や，あるいはその他の重要な性質を示す際において，シークエント計算を導入したほうがいくらか証明が数学的に簡単であり，かつ，形式化の難易度も低くなる．
更に，応用として補間定理や不動点補題も容易に導出できる (@sect:application-of-sequent-calculus で議論する)．
そこで我々の形式化ではまずGentzen流のシークエント計算を定め，最終的にこれらすべての特徴づけの同値性 (@thm:GL_TFAE) を示す．それぞれ見ていこう．

まずはGentzen流のシークエント計算を導入する．
ここでの #LogicGL のGentzen流シークエント計算は，SambinとValentini @SV82 によるものである．

#definition[
  _シークエント_ $Gamma => Delta$ とは，論理式の有限集合の対である．
  #LogicGL のシークエント計算は，以下の規則からなる．
  ただし，弱化規則 $(upright("wk")_(upright("L")))$，$(upright("wk")_(upright("R")))$ においてはそれぞれ $Gamma subset.eq Gamma'$，$Delta subset.eq Delta'$ とする．

  #align(center, grid(
    columns: 2,
    column-gutter: 4em,
    row-gutter: 2em,
    prooftree(rule(name: $(upright("axm"))$, $A => A$)),
    prooftree(rule(name: $(bot_(upright("L")))$, $bot =>$)),
    prooftree(rule(name: $(upright("wk")_(upright("L")))$, $Gamma' => Delta$, $Gamma => Delta$)),
    prooftree(rule(name: $(upright("wk")_(upright("R")))$, $Gamma => Delta'$, $Gamma => Delta$)),
    prooftree(rule(
      name: $(limp_(upright("L")))$,
      $A limp B, Gamma => Delta$,
      $Gamma => A, Delta$,
      $B, Gamma => Delta$,
    )),
    prooftree(rule(name: $(limp_(upright("R")))$, $Gamma => A limp B, Delta$, $A, Gamma => B, Delta$)),
    grid.cell(colspan: 2, prooftree(rule(
      name: $(upright("GL"))$,
      $Box Gamma => Box A$,
      $Box A, Gamma, Box Gamma => A$,
    ))),
  ))
]
#leancode[
  ```
  structure Sequent (α : Type u) where
    ant : FormulaFinset α
    suc : FormulaFinset α
  infix:50 " ⟹ " => Sequent.mk

  inductive ProofGentzen : Sequent α → Type u
  | axm (A) : ProofGentzen ({A} ⟹ {A})
  | botL : ProofGentzen ({⊥} ⟹ ∅)
  | wkL  {Γ Γ' Δ}  : ProofGentzen (Γ ⟹ Δ) → Γ ⊆ Γ' → ProofGentzen (Γ' ⟹ Δ)
  | wkR  {Γ Δ Δ'}  : ProofGentzen (Γ ⟹ Δ) → Δ ⊆ Δ' → ProofGentzen (Γ ⟹ Δ')
  | impL {Γ Δ A B} : ProofGentzen (Γ ⟹ (insert A Δ)) → ProofGentzen (insert B Γ ⟹ Δ) →
                     ProofGentzen ((insert (A 🡒 B) Γ) ⟹ Δ)
  | impR {Γ Δ A B} : ProofGentzen ((insert A Γ) ⟹ (insert B Δ)) →
                     ProofGentzen (Γ ⟹ (insert (A 🡒 B) Δ))
  | boxGL {Γ A} : ProofGentzen ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A}) → ProofGentzen (Γ.box ⟹ {□A})
  prefix:120 "⊢ᵍ! " => ProofGentzen
  ```
]

この体系にカット規則が含まれないことに注意しておく．
カット規則を加えた体系（形式化では `⊢ᵍᶜ`）も別途定義しており，SambinとValentini @SV82 によるカット除去定理に相当する同値性も @thm:GL_TFAE の一部として形式化されている．

次に，Kripke意味論を導入する．
我々は様相論理一般の議論をしたいわけではないので，ここではフレームの概念は省略し，すべてモデルのみで議論する．

#definition[
  $W$ を空でない集合とし，その要素を_点_と呼ぶ．
  $W$ 上の _Kripkeモデル_とは，対 $M = chevron.l R, V chevron.r$ であって，$R subset.eq W times W$（_到達可能性関係_）および $V colon W -> Prop -> 2$（_付値_）からなるものである．
  モデルに関して以下の用語を定める．
  - モデルが_有限_であるとは，$W$ が有限集合であることをいう．
  - モデルが_推移的_（_非反射的_）であるとは，$R$ が推移的（非反射的）であることをいう．
  - 点 $r in W$ が_根_であるとは，$x != r$ なる任意の $x in W$ に対して $r R x$ となることをいう．根を1つ指定したモデルを_根付きモデル_と呼ぶ．
  - モデルが _$LogicGL$モデル_であるとは，$R$ が推移的かつ逆整礎的であることをいう．特に，有限かつ推移的かつ非反射的なモデルを_有限$LogicGL$モデル_と呼び，これは$LogicGL$モデルである．

  モデル $M$，その点 $x$，論理式 $A$ に対して，_充足関係_ $M, x forces A$ を次のように定める．
  - $M, x forces p$ とは，$V(x, p) = 1$ となることである．
  - $M, x forces.not bot$．
  - $M, x forces A limp B$ とは，$M, x forces A$ ならば $M, x forces B$ となることである．
  - $M, x forces Box A$ とは，$x R y$ なる任意の $y in W$ について $M, y forces A$ となることである．
]
#leancode(
  note: [
    点の全体 $W$ は空でない任意の型 `κ` として与え，モデルは関係と付値の対として実装する．
    充足関係 `Forces` には `⊩` の記法を与えている．
  ],
)[
  ```
  structure Model (κ : Type u) [Nonempty κ] (α : Type v) where
    Rel' : κ → κ → Prop
    Val' : κ → α → Prop

  def Forces (x : M.World) : Formula α → Prop
  | #a    => M x a
  | ⊥     => False
  | A 🡒 B => Forces x A → Forces x B
  | □A    => ∀ y, x ≺ y → Forces y A
  infix:55 " ⊩ " => Forces

  class IsGL (M : Model κ α) extends IsTrans _ M.Rel, IsConverseWellFounded _ M.Rel

  class IsFiniteGL (M : Model κ α) extends IsTrans _ M.Rel, Std.Irrefl M.Rel where
    [finite : Finite M.World]

  abbrev Model.Root (M : Model κ α) := { r : M.World // ∀ x, x ≠ r → r ≺ x }

  structure RootedModel (κ) [Nonempty κ] (α) extends Model κ α where
    root : toModel.Root
  ```
]

最後に，Hilbert流の証明体系を導入する．

#definition[
  #LogicGL のHilbert流の証明体系は，以下の公理と推論規則からなる．

  1. 古典命題論理のトートロジー (cf: @chagrovModalLogic2001)
  2. 公理 $AxiomK$: $Box(A limp B) limp (Box A limp Box B)$
  3. 公理 $Axiom("4")$: $Box A limp Box Box A$
  4. 公理 $AxiomL$: $Box(Box A limp A) limp Box A$
  5. 推論規則: モーダス・ポネンス (MP) および必然化規則 (Nec)．
]
#leancode(
  note: [
    Łukasiewicz の3公理さえあれば古典命題論理のトートロジーをすべて証明できるが，代わりにここで述べている公理をシンタクティカルに証明する必要があり，それは極めて面倒なので今回はすべて導入している．
    公理 $Axiom("4")$ は $AxiomK$ と $AxiomL$ から構文論的に導出可能であるが (cf. @Boo94) ，その証明はパズル的に面倒なので，形式化では公理として採用している．
  ],
)[
  ```
  inductive ProofHilbert : Formula α → Type u
  | implyK   {A B}   : ProofHilbert $ A 🡒 B 🡒 A
  | implyS   {A B C} : ProofHilbert $ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)
  | dne      {A}     : ProofHilbert $ ∼∼A 🡒 A
  | andElimL {A B}   : ProofHilbert $ (A ⋏ B) 🡒 A
  | andElimR {A B}   : ProofHilbert $ (A ⋏ B) 🡒 B
  | andIntro {A B}   : ProofHilbert $ A 🡒 B 🡒 (A ⋏ B)
  | orIntroL {A B}   : ProofHilbert $ A 🡒 (A ⋎ B)
  | orIntroR {A B}   : ProofHilbert $ B 🡒 (A ⋎ B)
  | orElim   {A B C} : ProofHilbert $ (A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C)
  | modalK   {A B}   : ProofHilbert $ □(A 🡒 B) 🡒 (□A 🡒 □B)
  | modal4   {A}     : ProofHilbert $ □A 🡒 □□A
  | modalL   {A}     : ProofHilbert $ □(□A 🡒 A) 🡒 □A
  | mdp      {A B}   : ProofHilbert (A 🡒 B) → ProofHilbert A → ProofHilbert B
  | nec      {A}     : ProofHilbert A → ProofHilbert (□A)
  prefix:50 "⊢ʰ! " => ProofHilbert

  abbrev LogicGL {α} : Logic α := { A | ⊢ʰ A }
  ```
]

これらの特徴づけの同値性として，次を形式化した．

#theorem[Characterization of #LogicGL][
  以下は同値である．

  1. $LogicGL proves A$，すなわちHilbert流の証明体系で $A$ が証明可能．
  2. シークエント計算で $=> A$ が証明可能．
  3. カット規則を加えたシークエント計算で $=> A$ が証明可能．
  4. ラベル付きシークエント計算で $A$ が証明可能．
  5. 任意の有限$LogicGL$モデルの任意の点で $A$ が真．
  6. 任意の根付き有限$LogicGL$モデルの根で $A$ が真．
  7. 木であるような任意の根付き有限$LogicGL$モデルの根で $A$ が真．
] <thm:GL_TFAE>
#leancode[
  ```
  theorem provability_TFAE [DecidableEq α] {A : Formula α} : [
    A ∈ LogicGL,
    ⊢ʰ A,
    ⊢ᵍ (∅ ⟹ {A}),
    ⊢ᵍᶜ (∅ ⟹ {A}),
    ⊢ˡ (∅ ⸴ ∅ ⟹ˡ {(0 : LabelledGentzen.Label) ∶ A}),
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGL] → M.root.1 ⊩ A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLTree] → M.root.1 ⊩ A
  ].TFAE
  ```
]

いくつか注意しておく．
$LogicGL$ のKripke完全性(1と5の同値性)は Segerberg @Segerberg1971 に帰する．
このことは有限$LogicGL$モデルのクラスに対する通常のKripke完全性であり，MaggesiとPelini-Brogi @maggesiMechanisingGodelLob2023 によってHOL Light上で既に形式化されている．
しかし，後述する算術的完全性定理の証明には，単なるKripke完全性ではなく，根付きモデルに対する完全性（6，さらには7）が必要となる．
根付きモデルから木モデルへの変形は，tree unraveling と呼ばれる手法による (cf. @chagrovModalLogic2001[Theorem 3.18])．
また，2と3の同値性はカット除去定理に相当する．

続いて，証明可能性論理で重要な様相論理 $Logic("S")$ と $Logic("D")$ を導入する．
これらは非正規な様相論理であり，前者は Solovay @solovay1976 に，後者はJaparidze (Dzhaparidze) @Jap86 に由来する．

#definition[
  論理 $L_1, L_2$ に対して，$L_1$ と $L_2$ の union に対してMPと代入による閉包として得られる論理を $sumQuasiNormal(L_1, L_2)$ と書くことにする．

  - Solovayの証明可能性論理 $LogicS$ とは，$sumQuasiNormal(LogicGL, { Box A limp A | A })$ のことである．
  - Japaridzeの証明可能性論理 $Logic("D")$ とは，$sumQuasiNormal(LogicGL, ({ lnot Box bot } union { Box(Box A lor Box B) limp Box A lor Box B | A, B }))$ のことである．
]
#leancode[
  ```
  inductive Logic.sumQuasiNormal (L₁ L₂ : Logic α) : Logic α
    | mem₁ {A}    : L₁ A → sumQuasiNormal L₁ L₂ A
    | mem₂ {A}    : L₂ A → sumQuasiNormal L₁ L₂ A
    | mdp  {A B}  : sumQuasiNormal L₁ L₂ (A 🡒 B) → sumQuasiNormal L₁ L₂ A → sumQuasiNormal L₁ L₂ B
    | subst {A s} : sumQuasiNormal L₁ L₂ A → sumQuasiNormal L₁ L₂ (A⟦s⟧)
  infix:50 " +ᴸ " => Logic.sumQuasiNormal

  abbrev LogicS {α} : Logic α := LogicGL +ᴸ ({ □A 🡒 A | A })

  abbrev LogicD {α} : Logic α := LogicGL +ᴸ (insert (∼□⊥) { □(□A ⋎ □B) 🡒 (□A ⋎ □B) | (A) (B) })
  ```
]

これらの論理は非正規，すなわち必然化規則で閉じていないため，純粋にはKripke意味論を適用できない．
しかし，有限$LogicGL$モデルを適当に拡張して得られる無限モデルのクラスに対しては健全かつ完全であることが知られている．
$LogicS$ に対するそのようなモデルは tail モデル @Vis84 と呼ばれ，$Logic("D")$ に対しては擬 tail モデル (cf. @Bek90) と呼ばれるものを用いる．
これらの構成の詳細は省略するが，我々はこれらの意味論的な特徴づけを経由して，次の2つの命題を形式化した．
ここで $"Sub"(A)$ は $A$ の部分論理式全体の集合を表す．

#proposition[cf. @Vis84][
  以下は同値．

  1. $LogicS proves A$
  2. 任意の有限$LogicGL$モデルとその点 $t$ から構成される tail モデルの鎖上において，$A$ が最終的に常に真．
  3. 任意の根付き有限$LogicGL$モデルの根において $and.big_(Box B in "Sub"(A)) (Box B limp B) limp A$ が真．
  4. $LogicGL proves and.big_(Box B in "Sub"(A)) (Box B limp B) limp A$
] <prop:S_characterization>
#leancode(
  note: [
    形式化した定理の主張では，さらにKashimaとKato @KK23 によるカットフリーなシークエント計算による特徴づけとの同値性も含まれている．
  ],
)[
  ```
  theorem provability_TFAE [DecidableEq α] : [
    A ∈ LogicS,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (tail : M.World),
      ∃ k : ℕ, ∀ n : ℕ, k ≤ n → Forces (M := (M.toTail tail).toModel) (toTail.chainPoint n) A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      M.root.1 ⊩ (⋀A.subfmlsS 🡒 A),
    (⋀A.subfmlsS 🡒 A) ∈ LogicGL,
    ⊢ᴳ (∅ ⟹[1] {A})
  ].TFAE
  ```
]

#proposition[cf. @Bek90][
  以下は同値．ここで $"Sub"_Box (A) = {B | Box B in "Sub"(A)}$ とする．

  1. $Logic("D") proves A$
  2. 任意の有限$LogicGL$モデルから構成される擬 tail モデルの根において $A$ が真．
  3. 任意の根付き有限$LogicGL$モデルの根において $and.big_(Gamma subset.eq "Sub"_Box (A)) (Box(or.big Box Gamma) limp or.big Box Gamma) limp A$ が真．
  4. $LogicGL proves and.big_(Gamma subset.eq "Sub"_Box (A)) (Box(or.big Box Gamma) limp or.big Box Gamma) limp A$
] <prop:D_characterization>
#leancode[
  ```
  theorem provability_TFAE [DecidableEq α] : [
    A ∈ LogicD,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ r o,
      (M.toPseudoTail r o).root.1 ⊩ A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      M.root.1 ⊩ (⋀A.subfmlsD 🡒 A),
    (⋀A.subfmlsD 🡒 A) ∈ LogicGL
  ].TFAE
  ```
]

これらの論理の単なる包含関係は自明に成立する．
意味論を用いて反例モデルを構成することにより，以下の真の包含関係が成り立つ．

#proposition[
  $LogicGL subset.neq Logic("D") subset.neq LogicS$
]

=== シークエント計算の応用について <sect:application-of-sequent-calculus>

SambinとValentini @SV82 ではさらに$LogicGL$ のシークエント計算に対してのいくつかの応用が示されている．
まず，純粋なシークエント計算であるから素直にMaeharaの手法 (cf: @Takeuti2013) を用いて，Craig補間性 (CIP) を示すことができる．

#theorem[Craig Interpolation Property for #LogicGL][
  $LogicGL proves A limp B$ ならば，ある論理式 $C$ が存在して，$LogicGL proves A limp C$ かつ $LogicGL proves C limp B$ であり，$C$ の命題変数はすべて $A$ と $B$ の両方に現れる．
] <thm:GL_CIP>
#leancode[
  ```
  theorem CIP (h : (A 🡒 B) ∈ LogicGL) :
    ∃ C : Formula α, (A 🡒 C) ∈ LogicGL ∧ (C 🡒 B) ∈ LogicGL ∧ C.atoms ⊆ A.atoms ∩ B.atoms
  ```
]

特に $LogicGL$ のCIPは #LogicGL の不動点定理を導く @Smorynski1978 @Boo79 という点で重要である．
我々は $LogicGL$ の不動点定理もシークエント計算を用いて形式化することができている．

#theorem[#LogicGL の不動点定理 @SV82][


  $p$ が $A$ において様相化されているとする．
  このとき，$p$ を含まず $A$ の命題変数のみからなる論理式 $D$ が存在して，
  $ LogicGL proves A[p := D] <-> D $
  が成り立つ．
  さらにこの不動点は同値を除いて一意である．

  ここで，命題変数 $p$ が論理式 $A$ において_様相化されている_ (modalized) とは，$A$ における $p$ のすべての出現が $Box$ のスコープ内にあることをいう．
] <thm:GL_fixpoint>
#leancode(
  note: [
    ここで `q` は不動点の構成に用いる $A$ に現れない新しい命題変数である．
    なお `⊡A` は $A land Box A$ の略記である．
  ],
)[
  ```
  theorem fixpointTheorem {A : Formula α} {p q : α}
    (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    ∃ D : Formula α, D.atoms ⊆ A.atoms \ {p} ∧ ((A⟦p ↦ D⟧) 🡘 D) ∈ LogicGL

  theorem fixpoint_uniqueness (hA : A.ModalizedIn p) :
    ⊢ᵍ ({⊡(A 🡘 #p), ⊡((A⟦p ↦ #q⟧) 🡘 #q)} ⟹ {(#p : Formula α) 🡘 #q})
  ```
]

#LogicGL の不動点定理は，例えば Gignoux @Gignoux2026 でもLeanで形式化されている．
ここでは，Gignoux の形式化が意味論的な方法による証明であるのに対し，我々の形式下では，その証明の形式化から，補間および不動点は，シークエント計算の導出木から構成的にLean上で計算することが可能であることを注意しておこう．
ただし，現状ではシークエント計算の導出木を自動で証明探索などによって構成することは出来ないので，単に具体的に導出木をこちらで別途手入力で計算する必要がある．また，例えばKripke意味論を用いて $LogicGL proves A$ を非構成的に証明している場合は当然その補間や不動点はLean上で計算可能ではない．

最後に $LogicS$ と $Logic("D")$ のCIPに関しての事実も形式化しているので，軽く述べおこう．

#theorem[@Bek87][
  $Logic("S")$ はCIPを持つ．
]
#leancode[
  ```
  theorem CIP (h : (A 🡒 B) ∈ LogicS) :
    ∃ C : Formula α, (A 🡒 C) ∈ LogicS ∧ (C 🡒 B) ∈ LogicS ∧ C.atoms ⊆ A.atoms ∩ B.atoms
  ```
]

#theorem[@Bek89][
  $Logic("D")$ はCIPを持たない．
  特に，次の $A$ と $B$ に対して，$Logic("D") proves not A -> B$ だがその補間は存在しない．
  ここで $a,b,c$ は相異なる命題変数とする．
  $
    A & equiv Box (Box b or a) -> Box b \
    B & equiv Box (a -> Box c) -> Box c
  $
] <thm:D_no_CIP>
#leancode[
  ```
  theorem notCIP {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ A B : Formula α, (A 🡒 B) ∈ LogicD ∧
      ¬ ∃ C : Formula α, (A 🡒 C) ∈ LogicD ∧ (C 🡒 B) ∈ LogicD ∧
        C.atoms ⊆ A.atoms ∩ B.atoms
  ```
]

=== ラベル付きシークエント計算について

我々は，#LogicGL のラベル付きシークエント計算 @Neg14 についても形式化しているが，これは先行研究として MaggesiとPerini Brogi @maggesiMechanisingGodelLob2023 によるHOL Lightでの #LogicGL のラベル付きシークエント計算の形式化とほとんど方法としては同じであり，その意味では新規性はあまりない．
ただしいくつかの実装上の相違点については触れておこう．

MaggesiとPerini Brogiのシークエント計算の*実装の*停止性はメタの数学的事実として保証されている．
つまり，Negri @Neg14 が示した数学的事実によって，彼らが正しく実装しているならばという仮定付きによって，計算が停止することが保証されている．
一方で，我々は実際にproof-searchを定義する際に，Leanの制約上としてそれがwell-foundedになるということによって，停止性を定理証明支援系の中で保証している．
この点では我々のほうがより強い保証を与えていると言える．
しかし，MaggesiとPerini Brogiの形式化は実用上の有用性があり，停止性の保証は無いものの実際に計算を行わせてタクティク的に使うことが出来て，形式化上に現れる #LogicGL の簡単な証明を自動化することが出来ている．
他方我々の実装では，そのwell-foundednessの証明の実装上の制約上，我々のラベル付きシークエント計算を例えばLeanのタクティクとして使うことが出来ず，純粋に数学的事実としてラベル付きシークエント計算の諸性質が形式化されているに留まっている．
故に実用性上の優位性に関してはMaggesiとPerini Brogiの形式化のほうに軍配が上がっている．

また，ラベル付きシークエント計算で @sect:application-of-sequent-calculus で述べたようなCIPを形式化の証明に書き起こすことは難しい #footnote[
  ラベル付きシークエント計算一般のInterpolantに関しては例えば @GiessenJalaliKuznets2026a[Section 5] に記載されているが，#LogicGL のラベル付きシークエント計算に関してそれが可能かは現状では未解決だと思われる．
]．
現状では，#LogicGL の論理としての特徴を形式化する点においては，あまり有効ではないことは指摘しておく．

== 算術的完全性定理

この節では，我々の証明可能性論理の形式化の主結果である，Solovayの算術的完全性定理 @solovay1976 とその一般化の形式化について述べる．

まず，様相論理式を算術の文へと翻訳する算術的解釈を定義する．
以下，$T$ は $Delta_1$-定義可能な公理系を持ち $Theory("I")Sigma_1$ を含む算術の理論とし，$T$ の標準的な証明可能性述語 $Pr(T)$ のみを考える．

#definition[
  写像 $f colon Prop -> upright("Sent")_upright("A")$ を _算術的実現_（または単に_実現_）と呼ぶ．
  実現 $f$ が与えられたとき，_（標準的）算術的解釈_とは，様相論理式 $A$ を次のように算術の文 $f_(Pr(T))(A)$ へと翻訳する $f$ の拡張のことである．
  $
           f_(Pr(T)) (p) & = f(p) \
         f_(Pr(T)) (bot) & = bot \
    f_(Pr(T)) (A limp B) & = f_(Pr(T)) (A) limp f_(Pr(T)) (B) \
       f_(Pr(T)) (Box A) & = Pr(T) (GoedelNum(f_(Pr(T))(A)))
  $
]
#leancode(
  note: [
    技術的な理由により，実現の実装は任意の証明可能性述語 `𝔅` に対して定義されている．
    ただし本稿では標準的な証明可能性述語のみを考えるので，`𝔅` としては常に `T.standardProvability` を取った `StandardRealization` を用いる．
  ],
)[
  ```
  structure Realization (α : Type*) (𝔅 : Provability T₀ T) where
    val : α → FirstOrder.Sentence L

  abbrev StandardRealization (α : Type*) (T : FirstOrder.ArithmeticTheory) [T.Δ₁] :=
    Realization α T.standardProvability

  def interpret (f : Realization α 𝔅) : Formula α → FirstOrder.Sentence L
    | #a    => f.val a
    | ⊥     => ⊥
    | A 🡒 B => (A.interpret f) 🡒 (B.interpret f)
    | □A    => 𝔅 (A.interpret f)
  ```
]

#definition[
  _$U$ に相対的な $T$ の（標準的）証明可能性論理_ $ProvLogic(T, U)$ を次で定める．
  $
    ProvLogic(T, U) = { A | #text[任意の実現 $f$ に対して $U proves f_(Pr(T)) (A)$] }
  $
]
#leancode[
  ```
  def provabilityLogicRelativeTo (T U : ArithmeticTheory) [T.Δ₁] : Logic α :=
    {A | ∀ f : StandardRealization α T, U ⊢ f A}

  abbrev provabilityLogic (T : ArithmeticTheory) [T.Δ₁] : Logic α := T.provabilityLogicRelativeTo T
  ```
]

Solovayの算術的完全性定理とは，標準的な証明可能性述語を様相演算子と見なしたときの挙動が，ちょうど様相論理 #LogicGL によって捉えられるという定理である．
すなわち，適切な $T$ と $U$ の選び方のもとで，証明可能性論理 $ProvLogic(T, U)$ は #LogicGL と一致する．
ここでは，Visser @Visser1981 による理論の_高さ_の概念を用いた一般化されたバージョン (@thm:arithmetical_completeness) を示す．

#definition[理論の高さ][
  $n >= 0$ に対して，$Pr(T)^n$ で証明可能性述語 $Pr(T)$ の $n$ 回の反復を表す（ただし $n = 0$ のとき $Pr(T)^0(x) equiv x$）．
  理論 $T$ の_高さ_ $height(T) <= omega$ とは，$T proves Pr(T)^n (GoedelNum(bot))$ となる最小の $n in omega$ のことである．そのような $n$ が存在しないとき $height(T) = omega$ とする．
]
#leancode(
  note: [
    実現と同様，任意の証明可能性述語 `𝔅` に対して定義されるが，本稿では標準的な証明可能性述語のみを考える．
  ],
)[
  ```
  noncomputable def Provability.height (𝔅 : Provability T₀ T) : ENat := ENat.find (T ⊢ 𝔅^[·] ⊥)

  noncomputable abbrev ArithmeticTheory.height (T : ArithmeticTheory) [T.Δ₁] : ℕ∞ :=
    T.standardProvability.height
  ```
]

なお，$T$ が $Sigma_1$-健全ならば，任意の $n in omega$ に対して $T nproves Pr(T)^n (GoedelNum(bot))$ であるから，$height(T) = omega$ である．

#definition[
  $n <= omega$ に対して，論理 #LogicGLPlusBoxBot($n$) を次で定める．
  $n < omega$ のときは，#LogicGL に論理式 $Box^n bot$ を加えて得られる非正規様相論理 $sumQuasiNormal(LogicGL, {Box^n bot})$ とし，$n = omega$ のときは #LogicGL そのものとする．
]
#leancode[
  ```
  def LogicGLPlusBoxBot {α} : ℕ∞ → Logic α
    | .some n => LogicGL +ᴸ □^[n]⊥
    | .none   => LogicGL
  ```
]

我々の証明可能性論理の形式化における主結果は以下である．

#theorem[@Visser1981][
  $ProvLogic(T, T) = LogicGLPlusBoxBot(height(T))$
] <thm:arithmetical_completeness>
#leancode[
  ```
  lemma eq_provabilityLogic : LogicGLPlusBoxBot (α := α) T.height = T.provabilityLogic
  ```
]

@thm:arithmetical_completeness は，$LogicGLPlusBoxBot(height(T)) nproves A$ のときに反例モデルとして得られる，適切な高さを持つ根付き有限$LogicGL$モデルを算術に埋め込むことによって証明される（Solovay文の構成）．
ここで @thm:GL_TFAE で述べた根付きモデルに対する完全性が必要となる．
系として，Solovayによる元々の主張が得られる．

#corollary[Solovayの（第1）算術的完全性定理 @solovay1976][
  $T$ が $Sigma_1$-健全ならば，$ProvLogic(T, T) = LogicGL$．
  特に $ProvLogic(PeanoArithmetic, PeanoArithmetic) = LogicGL$．
]
#leancode[
  ```
  theorem eq_provabilityLogic_sigma1_sound [T.SoundOnHierarchy 𝚺 1] :
    @LogicGL α = T.provabilityLogic

  theorem eq_provabilityLogic_peano_arithmetic : @LogicGL α = (𝗣𝗔.provabilityLogic)
  ```
]

さらに，Solovayは #LogicS が真の算術 #TrueArithmetic に関して算術的完全であることも証明している．
この証明には @prop:S_characterization で述べた $LogicS$ の $LogicGL$ への還元が本質的に用いられる．

#theorem[Solovayの（第2）算術的完全性定理 @solovay1976][
  $T$ を健全な理論とする．
  任意の論理式 $A$ に対して，$LogicS proves A$ であることと，任意の実現 $f$ に対して $NN models f_(Pr(T)) (A)$ となることは同値である．
  すなわち，$ProvLogic(T, TrueArithmetic) = LogicS$．
]
#leancode[
  ```
  theorem arithmetical_completeness_iff [DecidableEq α] :
    A ∈ LogicS ↔ (∀ f : StandardRealization α T, ℕ↓[ℒₒᵣ] ⊧ f A)

  theorem eq_provabilityLogicRelativeTo_TA [DecidableEq α] :
    @LogicS α = T.provabilityLogicRelativeTo 𝗧𝗔
  ```
]

== 証明可能性定理の分類定理

== いくつかの `sorry` に関して

分類定理を形式化すること自体には直接依存していないものの，しかし証明可能性論理上のいくつかの事実は現状 `sorry` のままで残されている．
ここでは，そのことについて注意しておこう．

$Logic("D")$ が証明可能性論理であるという事実 @Jap86 @AB05[Example 60] は，現状では `sorry`-freeではない．
#theorem[
  $Logic("D") = ProvLogic(T, T + upright("Rfn")_(Sigma_1)(T))$．
  ここで $upright("Rfn")_(Sigma_1)(T)$ は $T$ の $Sigma_1$ 論理式に対する反映原理．
] <thm:D_is_provability_logic>

この事実は，以下の事実が我々の形式化で出来ていない事による．
この事実を証明するためには真理の部分定義述語などに関する議論が必要であり，それは我々はまだ完成できていない．

#theorem[Unboundness @KreiselLevy1968 @AB05[Theorem 23]][
  $upright("Rfn")_(Sigma_n)(T)$ はいかなる $T$ の $Pi_n$ 文による無矛盾なr.e.拡大理論でも証明可能ではない．
]

もう一つはuniform arithmetical completeness theoremである．

#theorem[Uniform Arithmetical Completeness Theorem][
  任意の $Sigma_1$-健全な理論 $T$ に対して uniformな算術的解釈 $f$ が構成できる．
  つまり，任意の論理式 $A$ に対して，$LogicGL proves A$ であることと，$T proves f_(Pr(T)) (A)$ となることが同値になる．
]

== その他の細々

$Logic("GL.3")$ のシークエント計算がValentini @VS83 @Val86 によって形式化されている．
特に，@VS83 により，$Logic("GL.3")$

== 今後の進展

論理 $Logic("D")$ のカットフリーなシークエント計算はKashimaら @KKIM25 によって検討されている．
