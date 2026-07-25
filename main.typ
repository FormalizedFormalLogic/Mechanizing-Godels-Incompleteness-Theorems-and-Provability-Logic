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
        normalsize[`me@sno2wman.net`],
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
In his seminal paper @God31, he proved what is now known as the first incompleteness theorem (G1), and in a footnote, he outlined the second incompleteness theorem (G2).
G2 was later proved rigorously by Hilbert and Bernays @HB39.
We state the theorems in modern terms:
G1, with Rosser's improvement @Ros36, states that for any consistent axiomatic system with sufficient expressive power to execute arithmetic, there exists a proposition that can neither be proved nor disproved within the system.
G2 states that, for any consistent _nice_ axiomatic system as in G1, the proposition formally representing the system's own consistency cannot be proved within the system itself.

Gödel also made another important observation: that provability can be regarded as a modality.
In his early work @God33, he observed that the provability of intuitionistic logic can be treated similarly to the modal operator $Box$ in the modal logic now called #LogicS4.
However, it follows from G2, that abstracting the behavior of the provability predicate, the most central notion of the incompleteness theorems, does not yield #LogicS4.
Solovay @Sol76 showed that the modal logic called #LogicGL precisely captures the behavior of the standard provability predicate.
This fact, known as _Solovay's arithmetical completeness theorem_, was a significant result that opened up the subfield of modal logic called _provability logic_.

On the other hand, recently, there have been much active works on mechanizing mathematics using interactive theorem provers, guaranteeing the validity of existing and new results, and providing AI/LLM-assisted or automated proving.
There are many well-known interactive theorem provers such as Rocq @RocqProver, Isabelle @Isabelle, HOL Light @HOLLight @HOLLightTutorial, Agda @Agda, and Lean @dMU21, and mathematics has been mechanized in each of them, including in the field of mathematical logic (some of these mechanizations are summarized in @AwesomeLogicFormalization).
In particular, for mechanizing Gödel's incompleteness theorems, this line of work began with Shankar in 1986 @Sha86 @Sha97, and continues with O'Connor @OCo05 @OCo09, Harrison @Har06, Paulson @Pau15, and Popescu and Traytel @PT19 @PT21, Kirst and Peters @KP23.
As for provability logic, modal-logical properties of #LogicGL, such as its semantical completeness and automated solvers, have been mechanized by Maggesi and Perini Brogi @MPB23, Gignoux @Gig26.
However, these are either abstract or not full mechanizations within arithmetic.
For instance, O'Connor's implementation assumes several facts needed for the proof of G2 as axioms, and Paulson's mechanization of G2 uses hereditarily finite sets, not arithmetic.
To the best of our knowledge, no full formalization of the incompleteness theorems entirely within arithmetic is known, and consequently, no mechanization about provability logic has been reported.

In this paper, we present machine-assisted formalizations of Gödel's 1st and 2nd incompleteness theorems and Solovay's arithmetical completeness theorem.
Our work is carried out in Lean 4, an interactive theorem prover, together with mathlib4 @mathlib2020, its community-developed mathematics library.
Lean 4 is based on the Calculus of Inductive Constructions (CIC) @dMU21,
and features dependent types, quotient types, and support for noncomputable definitions, making it highly expressive.
In addition, its powerful metaprogramming infrastructure like aesop @LF23 enables efficient proof automation and extensibility.

Our mechanization is currently hosted as a repository on GitHub, and the version we refer to is #link(SOURCE).
In this report, we will briefly and informally introduce the mathematical facts without omitting the essentials, and show the code of our mechanization corresponding to those facts.
However, for the sake of readability, note that in some places we have modified the hosted code.
Moreover, owing to motivations other than the incompleteness theorems and provability logic that this report focuses on, some implementations are stated as more general definitions.
We add comments where we deem it necessary, but for the actual working (verified) code, refer to the repository.


= 証明可能性論理

この節では，様相論理，特に証明可能性論理の形式化について述べる．
我々は，証明可能性論理という分野の中でも基本的かつ最重要の事実として，Solovayの算術的完全性定理 @Sol76 の形式化に成功している．
また，Beklemishev @Bek90 による証明可能性論理の分類定理の結果も形式化している．
前節と同様に，定義や事実の導入は最小限に留める．
様相論理および証明可能性論理の詳細については，標準的な教科書 @CZ97 @Boo94 @Smo85 あるいは，サーベイ @JdJ98 @AB05 を参照されたい．

== 様相論理の基本的な性質など

まず，様相論理の基本的な枠組みを準備しよう．

#definition[
  様相論理の論理式は，命題変数（その全体を #Prop と書く），原始的な論理結合子 $bot$ と $limp$，および様相演算子 $Box$ から構成される．
  残りの演算子 $top, lnot, land, lor, Dia$ は通常の略記として導入する．
  また，$Boxdot A equiv A land Box A$ と略記する．

  _代入_とは各命題変数に論理式を割り当てる写像 $s$ のことであり，$A[s]$ で $A$ に現れる各命題変数 $p$ を $s(p)$ で置き換えて得られる論理式を表す．

  論理式の有限集合 $Gamma$ に対して，$Box Gamma = { Box B | B in Gamma }$ と書く．
  特に強調したいとき，論理式の集合を論理という．
]

#leancode(
  note: [
    形式化においては，命題変数全体は任意の型 `α` としてパラメータ化されている．
    例えば，`α` として `Empty` を選択することにより，命題変数を含まない論理式（closed あるいは letterless と呼ばれる）を表現することが出来る．
  ],
  links: (
    "ProvabilityLogic/Formula/Basic.lean",
    "ProvabilityLogic/Formula/Substitution.lean",
    "ProvabilityLogic/Logic/Basic.lean",
  ),
)[
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
  abbrev boxdot (A : Formula α) : Formula α := A ⋏ □A

  abbrev Substitution (α β) := α → Formula β

  def subst (s : Substitution α β) : Formula α → Formula β
    | atom a  => (s a)
    | ⊥       => ⊥
    | □A      => □(A.subst s)
    | A 🡒 B   => A.subst s 🡒 B.subst s
  notation:95 A "⟦" s "⟧" => Formula.subst s A

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
  ただし，弱化規則 (wkL)，(wkR) においてはそれぞれ $Gamma subset.eq Gamma'$，$Delta subset.eq Delta'$ とする．

  #align(center, grid(
    columns: 2,
    column-gutter: 4em,
    row-gutter: 2em,
    prooftree(rule(name: [(axm)], $A => A$)),
    prooftree(rule(name: [($bot$L)], $bot =>$)),
    prooftree(rule(name: [(wkL)], $Gamma' => Delta$, $Gamma => Delta$)),
    prooftree(rule(name: [(wkR)], $Gamma => Delta'$, $Gamma => Delta$)),
    prooftree(rule(
      name: [($limp$L)],
      $A limp B, Gamma => Delta$,
      $Gamma => A, Delta$,
      $B, Gamma => Delta$,
    )),
    prooftree(rule(name: [($limp$R)], $Gamma => A limp B, Delta$, $A, Gamma => B, Delta$)),
    grid.cell(colspan: 2, prooftree(rule(
      name: [($Box$GL)],
      $Box Gamma => Box A$,
      $Box A, Gamma, Box Gamma => A$,
    ))),
  ))
]
#leancode(links: ("ProvabilityLogic/Gentzen/Basic.lean",))[
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
  links: ("ProvabilityLogic/Kripke/Basic.lean", "ProvabilityLogic/Kripke/RootedModel.lean"),
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

後の議論のために，有限$LogicGL$モデルの点の_ランク_とモデルの_高さ_の概念も導入しておく．

#definition[
  $M$ を有限$LogicGL$モデルとする．
  - 点 $x$ の_ランク_ $upright("rank")(x)$ とは，$x$ から伸びる $R$-鎖 $x R y_1 R dots.c R y_n$ の長さ $n$ の最大値である．
  - 根付き有限$LogicGL$モデル $M$ の_高さ_とは，その根のランクである．
]
#leancode(links: ("ProvabilityLogic/Kripke/Rank.lean",))[
  ```
  noncomputable def World.rank {M : Model κ α} [Fintype M.World] [M.IsGL] (x : M.World) : ℕ :=
    cwfHeight (· ≺ ·) x

  noncomputable def height (M : RootedModel κ α) [Fintype M.World] [M.IsGL] : ℕ := M.root.1.rank
  ```
]

最後に，Hilbert流の証明体系を導入する．

#definition[
  #LogicGL のHilbert流の証明体系は，以下の公理と推論規則からなる．

  1. 古典命題論理のトートロジー (cf. @CZ97)
  2. 公理 $AxiomK$: $Box(A limp B) limp (Box A limp Box B)$
  3. 公理 $Axiom("4")$: $Box A limp Box Box A$
  4. 公理 $AxiomL$: $Box(Box A limp A) limp Box A$
  5. 推論規則: モーダス・ポネンス (MP) および必然化規則 (Nec)．
]
#leancode(
  links: ("ProvabilityLogic/Hilbert/Basic.lean", "ProvabilityLogic/Logic/GL/Basic.lean"),
  note: [
    Łukasiewicz の3つの公理さえあれば古典命題論理のトートロジーをすべて証明できるが，代わりにここで述べている公理をシンタクティカルに証明する必要があり，それは極めて面倒なので今回はすべて導入している．
    公理 $Axiom("4")$ は無くても構文論的に導出可能であるが (cf. @Boo94[Chapter 1, Theorem 18]) ，その証明はパズル的に面倒なので，今回の形式化では公理として採用している．
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
#leancode(links: ("ProvabilityLogic/Logic/GL/Basic.lean",))[
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
$LogicGL$ のKripke完全性(1と5の同値性)は Segerberg @Seg71 に帰する．
このことは有限$LogicGL$モデルのクラスに対する通常のKripke完全性であり，MaggesiとPerini Brogi @MPB23 によってHOL Light上で既に形式化されている．
しかし，後述する算術的完全性定理の証明には，単なるKripke完全性ではなく，根付きモデルに対する完全性（6，さらには7）が必要となる．
根付きモデルから木モデルへの変形は，tree unraveling と呼ばれる手法による (cf. @CZ97[Theorem 3.18])．
また，2と3の同値性はカット除去定理に相当する．

続いて，証明可能性論理で重要な様相論理 $Logic("S")$ と $LogicD$ を導入する．
これらは非正規な様相論理であり，前者は Solovay @Sol76 に，後者はJaparidze (Dzhaparidze) @Jap86 に由来する．

#definition[
  論理 $L_1, L_2$ に対して，$L_1$ と $L_2$ の和集合をMPと代入で閉じて得られる論理を $sumQuasiNormal(L_1, L_2)$ と書くことにする．

  そのうえで，Solovayの証明可能性論理とJaparidzeの証明可能性論理を以下で定める．
  - $LogicS := sumQuasiNormal(LogicGL, { Box A limp A | A })$．
  - $LogicD := sumQuasiNormal(LogicGL, ({ lnot Box bot } union { Box(Box A lor Box B) limp Box A lor Box B | A, B }))$．
]
#leancode(links: (
  "ProvabilityLogic/Logic/SumQuasiNormal.lean",
  "ProvabilityLogic/Logic/S/Basic.lean",
  "ProvabilityLogic/Logic/D/Basic.lean",
))[
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
$LogicS$ に対するそのようなモデルは tail モデル @Vis84 と呼ばれ，$LogicD$ に対しては擬 tail モデル (cf. @Bek90) と呼ばれるものを用いる．
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
  links: ("ProvabilityLogic/Logic/S/Basic.lean",),
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

  1. $LogicD proves A$
  2. 任意の有限$LogicGL$モデルから構成される擬 tail モデルの根において $A$ が真．
  3. 任意の根付き有限$LogicGL$モデルの根において $and.big_(Gamma subset.eq "Sub"_Box (A)) (Box(or.big Box Gamma) limp or.big Box Gamma) limp A$ が真．
  4. $LogicGL proves and.big_(Gamma subset.eq "Sub"_Box (A)) (Box(or.big Box Gamma) limp or.big Box Gamma) limp A$
] <prop:D_characterization>
#leancode(links: ("ProvabilityLogic/Logic/D/Basic.lean",))[
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

これらの論理の単なる包含関係は定義より自明に成立する．
更に，意味論を用いて反例モデルを構成することにより，以下の真の包含関係が成り立つ．

#proposition[
  $LogicGL subset.neq LogicD subset.neq LogicS$
]
#leancode(
  links: ("ProvabilityLogic/Logic/D/Basic.lean",),
)[
  ```
  lemma LogicD_ssubset_LogicS [Inhabited α] [DecidableEq α] : (LogicD : Logic α) ⊂ LogicS
  ```
]

=== シークエント計算の応用について <sect:application-of-sequent-calculus>

SambinとValentini @SV82 ではさらに$LogicGL$ のシークエント計算に対してのいくつかの応用が示されている．
まず，純粋なシークエント計算であるから素直にMaeharaの手法 (cf. @Tak87) を用いて，Craig補間性 (CIP) を示すことができる．

#theorem[Craig Interpolation Property for #LogicGL][
  $LogicGL proves A limp B$ ならば，ある論理式 $C$ が存在して，$LogicGL proves A limp C$ かつ $LogicGL proves C limp B$ であり，$C$ の命題変数はすべて $A$ と $B$ の両方に現れる．
] <thm:GL_CIP>
#leancode(links: ("ProvabilityLogic/Logic/GL/CIP.lean", "ProvabilityLogic/Gentzen/Maehara.lean"))[
  ```
  theorem CIP (h : (A 🡒 B) ∈ LogicGL) :
    ∃ C : Formula α, (A 🡒 C) ∈ LogicGL ∧ (C 🡒 B) ∈ LogicGL ∧ C.atoms ⊆ A.atoms ∩ B.atoms
  ```
]

特に $LogicGL$ のCIPは #LogicGL の不動点定理を導く @Smo78 @Boo79 という点で重要である．
我々は $LogicGL$ の不動点定理もシークエント計算を用いて形式化することができている．

#definition[
  命題変数 $p$ が論理式 $A$ において_様相化されている_ (modalized) とは，$A$ における $p$ のすべての出現が $Box$ のスコープ内にあることをいう．
]
#leancode(links: ("ProvabilityLogic/Formula/Modalized.lean",))[
  ```
  def ModalizedIn (p : α) : Formula α → Prop
    | #a    => a ≠ p
    | ⊥     => True
    | A 🡒 B => A.ModalizedIn p ∧ B.ModalizedIn p
    | □_    => True
  ```
]

#theorem[#LogicGL の不動点定理 @SV82][
  $p$ が $A$ において様相化されているとする．
  このとき，$p$ を含まず $A$ の命題変数のみからなる論理式 $D$ が存在して，
  $ LogicGL proves A[p := D] <-> D $
  が成り立つ．
  さらにこの不動点は同値を除いて一意である．
] <thm:GL_fixpoint>
#leancode(
  links: ("ProvabilityLogic/Logic/GL/Fixedpoint.lean",),
  note: [
    ここで `q` は不動点の構成に用いる $A$ に現れない新しい命題変数である．
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

#LogicGL の不動点定理は，例えば Gignoux @Gig26 でもLeanで形式化されている．
ここでは，Gignoux の形式化が意味論的な方法による証明であるのに対し，我々の形式化では，その証明の形式化から，補間および不動点は，シークエント計算の導出木から構成的にLean上で計算することが可能であることを注意しておこう．
ただし，現状ではシークエント計算の導出木を自動で証明探索などによって構成することは出来ないので，単に具体的に導出木をこちらで別途手入力で計算する必要がある．また，例えばKripke意味論を用いて $LogicGL proves A$ を非構成的に証明している場合は当然その補間や不動点はLean上で計算可能ではない．

最後に $LogicS$ と $LogicD$ のCIPに関しての事実も形式化しているので，軽く述べておこう．

#theorem[@Bek87][
  $Logic("S")$ はCIPを持つ．
]
#leancode(links: ("ProvabilityLogic/Logic/S/CIP.lean",))[
  ```
  theorem CIP (h : (A 🡒 B) ∈ LogicS) :
    ∃ C : Formula α, (A 🡒 C) ∈ LogicS ∧ (C 🡒 B) ∈ LogicS ∧ C.atoms ⊆ A.atoms ∩ B.atoms
  ```
]

#theorem[@Bek89][
  $LogicD$ はCIPを持たない．
  特に，次の $A$ と $B$ に対して，$LogicD proves not A -> B$ だがその補間は存在しない．
  ここで $a,b,c$ は相異なる命題変数とする．
  $
    A & equiv Box (Box b or a) -> Box b \
    B & equiv Box (a -> Box c) -> Box c
  $
] <thm:D_no_CIP>
#leancode(links: ("ProvabilityLogic/Logic/D/NotCIP.lean",))[
  ```
  theorem notCIP {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ A B : Formula α, (A 🡒 B) ∈ LogicD ∧
      ¬ ∃ C : Formula α, (A 🡒 C) ∈ LogicD ∧ (C 🡒 B) ∈ LogicD ∧
        C.atoms ⊆ A.atoms ∩ B.atoms
  ```
]

=== ラベル付きシークエント計算について

我々は，#LogicGL のラベル付きシークエント計算 @Neg14 についても形式化しているが，これは先行研究として MaggesiとPerini Brogi @MPB23 によるHOL Lightでの #LogicGL のラベル付きシークエント計算の形式化とほとんど方法としては同じであり，その意味では新規性はあまりない．
ただしいくつかの実装上の相違点については触れておこう．

MaggesiとPerini Brogiのシークエント計算の*実装の*停止性はメタの数学的事実として保証されている．
つまり，@Neg14 が示した数学的事実によって，彼らが正しく実装しているならばという仮定付きによって，計算が停止することが保証されている．
一方で，我々は実際にproof-searchを定義する際に，Leanの制約上としてそれがwell-foundedになるということによって，停止性を定理証明支援系の中で保証している．
この点では我々のほうがより強い保証を与えていると言える．
しかし，MaggesiとPerini Brogiの形式化は実用上の有用性があり，停止性の保証は無いものの実際に計算を行わせてタクティク的に使うことが出来て，形式化上に現れる #LogicGL の簡単な証明を自動化することが出来ている．
他方我々の実装では，そのwell-foundednessの証明の実装上の制約上，我々のラベル付きシークエント計算を例えばLeanのタクティクとして使うことが出来ず，純粋に数学的事実としてラベル付きシークエント計算の諸性質が形式化されているに留まっている．
故に実用性上の優位性に関してはMaggesiとPerini Brogiの形式化のほうに軍配が上がっている．

また，ラベル付きシークエント計算で @sect:application-of-sequent-calculus で述べたようなCIPを形式化の証明に書き起こすことは難しい #footnote[
  ラベル付きシークエント計算一般のInterpolantに関しては例えば @vdGJK26[Section 5] に記載されているが，#LogicGL のラベル付きシークエント計算に関してそれが可能かは現状では未解決だと思われる．
]．
現状では，#LogicGL の論理としての特徴を形式化する点においては，あまり有効ではないことは指摘しておく．

== 算術的完全性定理

この節では，我々の証明可能性論理の形式化の主結果である，Solovayの算術的完全性定理 @Sol76 とその一般化の形式化について述べる．

まず，様相論理式を算術の文へと翻訳する算術的解釈を定義する．
以下，$T$ は $Delta_1$-定義可能な公理系を持ち $Theory("I")Sigma_1$ を含む算術の理論とし，$T$ の標準的な証明可能性述語 $Pr(T)$ のみを考える．

#definition[
  写像 $f colon Prop -> upright("Sent")_upright("A")$ を _算術的実現_（または単に_実現_）と呼ぶ．
  実現 $f$ が与えられたとき，_（標準的）算術的解釈_とは，様相論理式 $A$ を次のように算術の文 $f_(Pr(T))(A)$ へと翻訳する $f$ の拡張のことである．
  - $f_(Pr(T)) (p) & = f(p)$
  - $f_(Pr(T)) (bot) & = bot$
  - $f_(Pr(T)) (A limp B) & = f_(Pr(T)) (A) limp f_(Pr(T)) (B)$
  - $f_(Pr(T)) (Box A) & = Pr(T) (GoedelNum(f_(Pr(T))(A)))$

]
#leancode(
  links: ("ProvabilityLogic/ProvabilityLogic/Interpret.lean",),
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
#leancode(links: ("ProvabilityLogic/ProvabilityLogic/Interpret.lean",))[
  ```
  def provabilityLogicRelativeTo (T U : ArithmeticTheory) [T.Δ₁] : Logic α :=
    {A | ∀ f : StandardRealization α T, U ⊢ f A}

  abbrev provabilityLogic (T : ArithmeticTheory) [T.Δ₁] : Logic α := T.provabilityLogicRelativeTo T
  ```
]

Solovayの算術的完全性定理とは，ラフな言い方では標準的な証明可能性述語を様相演算子と見なしたときの挙動が，ちょうど様相論理 #LogicGL によって捉えられるという定理である．
すなわち，適切な $T$ と $U$ の選び方のもとで，証明可能性論理 $ProvLogic(T, U)$ は #LogicGL と一致する．
ここでは，Visser @Vis81 による理論の_高さ_の概念を用いた一般化されたバージョン (@thm:arithmetical_completeness) を示す．

#definition[理論の高さ][
  $n >= 0$ に対して，$Pr(T)^n$ で証明可能性述語 $Pr(T)$ の $n$ 回の反復を表す（ただし $n = 0$ のとき $Pr(T)^0(x) equiv x$）．
  理論 $T$ の_高さ_ $height(T) <= omega$ とは，$T proves Pr(T)^n (GoedelNum(bot))$ となる最小の $n in omega$ のことである．そのような $n$ が存在しないとき $height(T) = omega$ とする．
]
#leancode(
  links: ("Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Height.lean",),
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
  $n <= omega$ に対して，論理 #LogicGLPlusBoxBot($n$) を記号を濫用して以下のように定める．
  $n < omega$ のときは，$sumQuasiNormal(LogicGL, {Box^n bot})$ とし，$n = omega$ のときは #LogicGL そのものとする．
]
#leancode(links: ("ProvabilityLogic/Logic/GLPlusBoxBot/Basic.lean",))[
  ```
  def LogicGLPlusBoxBot {α} : ℕ∞ → Logic α
    | .some n => LogicGL +ᴸ □^[n]⊥
    | .none   => LogicGL
  ```
]

我々の証明可能性論理の形式化における主結果は以下である．

#theorem[@Vis81][
  $ProvLogic(T, T) = LogicGLPlusBoxBot(height(T))$
] <thm:arithmetical_completeness>
#leancode(links: ("ProvabilityLogic/ProvabilityLogic/GLPlusBoxBot/Basic.lean",))[
  ```
  lemma eq_provabilityLogic : LogicGLPlusBoxBot (α := α) T.height = T.provabilityLogic
  ```
]

@thm:arithmetical_completeness は，$LogicGLPlusBoxBot(height(T)) nproves A$ のときに反例モデルとして得られる，適切な高さを持つ根付き有限$LogicGL$モデルを算術に埋め込むことによって証明される（Solovay文の構成）．
ここで @thm:GL_TFAE で述べた根付きモデルに対する完全性が必要となる．
系として，Solovayによる元々の主張が得られる．

#corollary[Solovayの（第1）算術的完全性定理 @Sol76][
  $T$ が $Sigma_1$-健全ならば，$ProvLogic(T, T) = LogicGL$．
  特に $ProvLogic(PeanoArithmetic, PeanoArithmetic) = LogicGL$．
]
#leancode(links: ("ProvabilityLogic/ProvabilityLogic/GL/Basic.lean",))[
  ```
  theorem eq_provabilityLogic_sigma1_sound [T.SoundOnHierarchy 𝚺 1] :
    @LogicGL α = T.provabilityLogic

  theorem eq_provabilityLogic_peano_arithmetic : @LogicGL α = (𝗣𝗔.provabilityLogic)
  ```
]

さらに，Solovayは #LogicS が真の算術 #TrueArithmetic に関して算術的完全であることも証明している．
この証明には @prop:S_characterization で述べた $LogicS$ の $LogicGL$ への還元が本質的に用いられる．

#theorem[Solovayの（第2）算術的完全性定理 @Sol76][
  $T$ を健全な理論とする．
  任意の論理式 $A$ に対して，$LogicS proves A$ であることと，任意の実現 $f$ に対して $NN models f_(Pr(T)) (A)$ となることは同値である．
  すなわち，$ProvLogic(T, TrueArithmetic) = LogicS$．
]
#leancode(links: ("ProvabilityLogic/ProvabilityLogic/S/Basic.lean",))[
  ```
  theorem arithmetical_completeness_iff [DecidableEq α] :
    A ∈ LogicS ↔ (∀ f : StandardRealization α T, ℕ↓[ℒₒᵣ] ⊧ f A)

  theorem eq_provabilityLogicRelativeTo_TA [DecidableEq α] :
    @LogicS α = T.provabilityLogicRelativeTo 𝗧𝗔
  ```
]

== 証明可能性定理の分類定理

Artemov, Beklemishev, Visser, Japaridze などらによって，$ProvLogic(T, U)$ の $T, U$ を動かすことによって得られる証明可能性論理たちがどのようになるかを分類し，それは Beklemishev @Bek90 によって完全になされた．
我々はこの分類定理も形式化した．
ただしその証明は算術とKripke意味論の複雑な議論によるものであるから，やはり証明の詳細は省略し，主要な結果を列挙する．
詳細は @Bek90 @AB05 を参照されたい．

#definition[
  $n in omega$ に対して，$F_n := Box^(n+1) bot limp Box^n bot$ と定める．
]
#leancode(
  links: ("ProvabilityLogic/Formula/Basic.lean",),
  note: [
    $F_n$ では名前として使いづらいので，形式化では $F_n$ を `TBB` (axiom $Axiom("T")$ for Box Bot)と名付けている．
  ],
)[
  ```
  def TBB (n : ℕ) : Formula α := (□^[(n + 1)]⊥) 🡒 (□^[n]⊥)
  ```
]

#definition[
  論理式 $A$ の_トレース_ $trace(A) subset.eq omega$ とは，高さが $n$ の根付き有限$LogicGL$モデルであって根で $A$ が偽となるものが存在するような $n$ 全体の集合である．
  論理 $L$ の_トレース_は $trace(L) := union.big_(A in L) trace(A)$ と定める．
]
#leancode(links: ("ProvabilityLogic/ProvabilityLogic/Classification/GeneralTrace.lean",))[
  ```
  def trace (A : Formula α) : Set ℕ := { n |
    ∃ κ : Type u, ∃ _ : Nonempty κ, ∃ M : RootedModel κ α, ∃ _ : Fintype M.World, ∃ _ : M.IsGL,
    (M.height = n ∧ M.root.1 ⊮ A) }

  abbrev Logic.trace (L : Logic α) : Set ℕ := ⋃ A ∈ L, A.trace
  ```
]

#definition[
  $alpha subset.eq omega$ および補有限な $beta subset.eq omega$ に対して，以下の非正規様相論理を定める．
  - $LogicGLAlpha(alpha) := sumQuasiNormal(LogicGL, { F_n : n in alpha })$
  - $LogicGLBetaMinus(beta) := sumQuasiNormal(LogicGL, { lnot and.big_(n in omega without beta) F_n })$

  とくに，$LogicGLAlpha(omega)$ を $LogicA$ と命名する #footnote[Artemovに由来するはず？]．
]
#leancode(links: ("ProvabilityLogic/ProvabilityLogic/Classification/LetterlessTrace.lean",))[
  ```
  abbrev LogicGLAlpha {α} (Alpha : Set ℕ) : Logic α := (@LogicGL α) +ᴸ ↑(Alpha.image $ TBB (α := Empty))

  abbrev LogicA {α} : Logic α := LogicGLAlpha Set.univ

  noncomputable abbrev TBBMinus [DecidableEq α] (X : Set ℕ) (X_finite : X.Finite) : Formula α :=
    ∼⋀(X_finite.toFinset.image TBB)

  abbrev LogicGLBetaMinus {α} [DecidableEq α] (Beta : Set ℕ) (Beta_cofinite : Betaᶜ.Finite) : Logic α :=
    (@LogicGL α) +ᴸ (LetterlessFormulaSet.lift { TBBMinus _ Beta_cofinite })
  ```
]

分類定理の証明の過程で最も本質的な補題が次の2つの事実である．

#lemma[@AB05[Corollary 55, Corollary 58]][
  $L$ を $trace(L) = omega$ なる証明可能性論理とする．
  1. $LogicA subset.neq L subset.neq LogicD$ となることはない．
  2. $LogicD subset.neq L subset.neq LogicS$ となることはない．
]
#leancode(links: (
  "ProvabilityLogic/ProvabilityLogic/Classification/A_D.lean",
  "ProvabilityLogic/ProvabilityLogic/Classification/D_S.lean",
))[
  ```
  theorem no_logic_between_LogicA_LogicD :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → ¬((LogicA ⊂ L) ∧ (L ⊂ LogicD))

  theorem no_logic_between_LogicD_LogicS :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → ¬((LogicD ⊂ L) ∧ (L ⊂ LogicS))
  ```
]

分類定理は次のように述べられる．

#theorem[証明可能性論理の分類定理 @Bek90 @AB05[Theorem 40]][
  $L = ProvLogic(T, U)$ とする．
  1. $trace(L)$ が補無限ならば，$L = LogicGLAlpha(trace(L))$．
  2. $trace(L)$ が補有限で $L subset.eq.not LogicS$ ならば，$L = LogicGLBetaMinus(trace(L))$．
  3. $trace(L)$ が補有限で $L subset.eq LogicS$ ならば，$L$ は $LogicGLAlpha(trace(L))$，$LogicD inter LogicGLBetaMinus(trace(L))$，$LogicS inter LogicGLBetaMinus(trace(L))$ のいずれかである．
]
#leancode(links: ("ProvabilityLogic/ProvabilityLogic/Classification/Result.lean",))[
  ```
  theorem classification_provability_logics [DecidableEq α] :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    if h_coinfinite : L.traceᶜ.Infinite then
      L = LogicGLAlpha L.trace
    else
      haveI h_cofinite : L.traceᶜ.Finite := Set.not_infinite.mp h_coinfinite;
      if ¬(L ⊆ LogicS) then
        L = LogicGLBetaMinus L.trace h_cofinite
      else
        L = LogicGLAlpha L.trace ∨
        L = LogicD ∩ LogicGLBetaMinus L.trace h_cofinite ∨
        L = LogicS ∩ LogicGLBetaMinus L.trace h_cofinite
  ```
]

さらに，@Bek90 では_真の証明可能性論理_，すなわち $ProvLogic(T, TrueArithmetic)$ の形の論理についての分類定理も示した．
この事実も形式化している．ただしこの事実は

#theorem[真の証明可能性論理の分類定理 @Bek90 @AB05[Corollary 41]][
  $L = ProvLogic(T, TrueArithmetic)$ は次のいずれかであり，それぞれの場合は $T$ の性質によって特徴づけられる．
  1. $L = LogicS$ ⟺ $T$ が健全．
  2. $L = LogicD$ ⟺ $T$ が $Sigma_1$-健全だが健全ではない．
  3. $L = LogicA$ ⟺ $T$ が $Sigma_1$-健全でなく $height(T) = omega$．
  4. $L = LogicGLBetaMinus(omega without {n})$ ⟺ $height(T) = n < omega$．
]
#leancode(links: ("ProvabilityLogic/ProvabilityLogic/Classification/Result.lean",))[
  ```
  theorem classification_provabilityLogic_TA [DecidableEq α] [Nonempty α] :
    letI L : Logic α := T.provabilityLogicRelativeTo 𝗧𝗔;
    (ℕ↓[ℒₒᵣ] ⊧* T ∧ L = LogicS) ∨
    (T.SoundOnHierarchy 𝚺 1 ∧ ¬(ℕ↓[ℒₒᵣ] ⊧* T) ∧ L = LogicD) ∨
    (¬(T.SoundOnHierarchy 𝚺 1) ∧ T.height = (⊤ : ℕ∞) ∧ L = LogicA) ∨
    ∃ n : ℕ, T.height = n ∧ L = LogicGLBetaMinus {n}ᶜ (by simp)
  ```
]

== いくつかの `sorry` に関して

分類定理を形式化すること自体には直接依存していないものの，しかし証明可能性論理上のいくつかの事実は現状 `sorry` のままで残されている．
ここでは，そのことについて注意しておこう．

1つ目は，実際に，$LogicD$ が証明可能性論理であるという事実は，現状では `sorry`-freeではない．
#theorem[@Jap86 @AB05[Example 60]][
  $LogicD = ProvLogic(T, T + upright("Rfn")_(Sigma_1)(T))$．
  ここで $upright("Rfn")_(Sigma_1)(T)$ は $T$ の $Sigma_1$ 論理式に対する反映原理．
] <thm:D_is_provability_logic>

この事実は，以下の事実が我々の形式化で出来ていない事による．
この事実を証明するためには真理の部分定義述語などに関する議論が必要であり，それは我々はまだ完成できていない．

#theorem[Unboundness @KL68 @AB05[Theorem 23]][
  $upright("Rfn")_(Sigma_n)(T)$ はいかなる $T$ の $Pi_n$ 文による無矛盾なr.e.拡大理論でも証明可能ではない．
]

もう一つはuniform arithmetical completeness theoremである．

#theorem[Uniform Arithmetical Completeness Theorem][
  任意の $Sigma_1$-健全な理論 $T$ に対して uniformな算術的解釈 $f$ が構成できる．
  つまり，任意の論理式 $A$ に対して，$LogicGL proves A$ であることと，$T proves f_(Pr(T)) (A)$ となることが同値になる．
]

== $LogicGLPoint3$ について

$LogicGLPoint3$ のシークエント計算はValentini @VS83 @Val86 によって与えられている．
特に，@VS83 では consistency assertion と呼ばれる算術の文のクラスに関して $LogicGLPoint3$ がある種の算術的完全性を持つことを示している．
この周辺のことについて簡単に述べておく．

#definition[
  $LogicGLPoint3$ とは，#LogicGL に弱い線形性の公理 $Box(Boxdot A limp B) lor Box(Boxdot B limp A)$ を加えて得られる正規様相論理である#footnote[古い文献では $Logic("GLLin")$ @VS83 @Val86 や $Logic("K4.3W")$ @Seg71 などと書かれていた．]．
]

#leancode(links: ("ProvabilityLogic/Logic/SumNormal.lean", "ProvabilityLogic/Logic/GLPoint3/Basic.lean"))[
  ```
  inductive Logic.sumNormal (L₁ L₂ : Logic α) : Logic α
    | mem₁ {A}    : L₁ A → sumNormal L₁ L₂ A
    | mem₂ {A}    : L₂ A → sumNormal L₁ L₂ A
    | mdp  {A B}  : sumNormal L₁ L₂ (A 🡒 B) → sumNormal L₁ L₂ A → sumNormal L₁ L₂ B
    | subst {A s} : sumNormal L₁ L₂ A → sumNormal L₁ L₂ (A⟦s⟧)
    | nec  {A}    : sumNormal L₁ L₂ A → sumNormal L₁ L₂ (□A)
  infix:50 " ⊕ᴸ " => Logic.sumNormal

  abbrev LogicGLPoint3 {α} : Logic α := LogicGL ⊕ᴸ { (□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A)) | (A) (B) }
  ```
]

#definition[
  有限$LogicGL$モデルでかつ線形なもの，すなわち $x prec y$ かつ $x prec z$ ならば $y prec z$ または $y = z$ または $z prec y$ であるものを有限$LogicGLPoint3$モデルと呼ぶ．
]

#leancode(links: ("ProvabilityLogic/Kripke/Linearity.lean",))[
  ```
  class IsFiniteGLPoint3 (M : Model κ α) extends Model.IsFiniteGL M where
    linear : ∀ {x y z : M.World}, x ≺ y → x ≺ z → y ≺ z ∨ y = z ∨ z ≺ y
  ```
]

#definition[
  $LogicGLPoint3$ のシークエント計算とは，#LogicGL のシークエント計算の $Box upright("GL")$ 規則を次の規則に置き換えたものである．
  ここで $Delta != emptyset$ とし，${S_1, dots, S_m} = PowerSet(Delta) without {emptyset}$（したがって $m = 2^(|Delta|) - 1$）とする．

  #align(center, prooftree(rule(
    name: [($Box$GL.3)],
    $Box Gamma => Box Delta$,
    $Gamma, Box Gamma, Box S_1 => S_1, Box(Delta without S_1)$,
    $dots.c$,
    $Gamma, Box Gamma, Box S_m => S_m, Box(Delta without S_m)$,
  )))
]

なお，$Delta = {A}$ の場合がちょうど $Box upright("GL")$ 規則である．

#leancode(links: ("ProvabilityLogic/Gentzen/GLPoint3/Basic.lean",))[
  ```
  | boxGLPoint3 {Γ Δ} (hΔ : Δ.Nonempty) :
      (∀ S : FormulaFinset α, S ⊆ Δ → S.Nonempty →
        ProofGentzen ((Γ.box ∪ Γ ∪ S.box) ⟹ (S ∪ (Δ \ S).box))) →
      ProofGentzen (Γ.box ⟹ Δ.box)
  ```
]

これらの特徴づけについて，#LogicGL と同様の同値性が成立する．

#theorem[@VS83][
  以下は同値である．
  1. $LogicGLPoint3 proves A$．
  2. $LogicGLPoint3$ のシークエント計算で $=> A$ が証明可能．
  3. 任意の有限$LogicGLPoint3$モデルの任意の点で $A$ が真．
  4. 任意の根付き有限$LogicGLPoint3$モデルの根で $A$ が真．
]
#leancode(links: ("ProvabilityLogic/Logic/GLPoint3/Completeness.lean",))[```
  theorem provability_TFAE [DecidableEq α] {A : Formula α} : [
    A ∈ LogicGLPoint3,
    ⊢ᵍ³ (∅ ⟹ {A}),
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGLPoint3] → M ⊧ A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLPoint3] → M.root.1 ⊩ A
  ].TFAE
  ```
]

特に閉論理式に関しては $LogicGLPoint3$ と $Logic("GL")$ は相違がない，という性質が @Art86 による閉論理式に対するトレースおよびシークエント計算を用いて示せる．

#theorem[@VS83[Theorem 2]][
  閉論理式 $A$ について，$LogicGLPoint3 proves A$ と $LogicGL proves A$ は同値．
]
#leancode(
  links: ("ProvabilityLogic/Logic/GLPoint3/Letterless.lean",),
)[
  ```
  theorem eq_LogicGL_on_letterless : @LogicGLPoint3 Empty = @LogicGL Empty
  ```
]

最後に $LogicGLPoint3$ のconsistency assertion による算術的完全性を述べる．

#definition[
  - 文 $sigma$ が _consistency assertion_ とは，$lnot Pr(T)(GoedelNum(bot))$ と $Pr(T)(GoedelNum(bot))$ から $Pr(T)(GoedelNum(dot))$，$lnot$，$land$，$lor$，$limp$ で閉じて生成されていることをいう．
  - 実現 $f$ が_consistency realization_であるとは，$f$ がすべての命題変数を consistency assertion に送ることをいう．
]

#leancode(links: ("ProvabilityLogic/ProvabilityLogic/GLPoint3/Basic.lean",))[
  ```
  inductive Provability.IsConsistencyAssertion (𝔅 : Provability T₀ T) : FirstOrder.Sentence L → Prop
    | con       : IsConsistencyAssertion 𝔅 (∼(𝔅 ⊥))
    | incon     : IsConsistencyAssertion 𝔅 (𝔅 ⊥)
    | prov {σ}  : IsConsistencyAssertion 𝔅 σ → IsConsistencyAssertion 𝔅 (𝔅 σ)
    | neg {σ}   : IsConsistencyAssertion 𝔅 σ → IsConsistencyAssertion 𝔅 (∼σ)
    | and {σ τ} : IsConsistencyAssertion 𝔅 σ → IsConsistencyAssertion 𝔅 τ → IsConsistencyAssertion 𝔅 (σ ⋏ τ)
    | or {σ τ}  : IsConsistencyAssertion 𝔅 σ → IsConsistencyAssertion 𝔅 τ → IsConsistencyAssertion 𝔅 (σ ⋎ τ)
    | imp {σ τ} : IsConsistencyAssertion 𝔅 σ → IsConsistencyAssertion 𝔅 τ → IsConsistencyAssertion 𝔅 (σ 🡒 τ)

  def Realization.IsConsistencyRealization {𝔅 : Provability T₀ T} (f : Realization α 𝔅) : Prop :=
    ∀ a, 𝔅.IsConsistencyAssertion (f.val a)

  abbrev StandardConsistencyRealization (α : Type*) (T : FirstOrder.ArithmeticTheory) [T.Δ₁] :=
    ConsistencyRealization α T.standardProvability
  ```
]

#theorem[@VS83[Theorem 1]][
  $LogicGLPoint3 proves A$ と，任意の $PeanoArithmetic$ 上の standard consistency realization $f$ に対して $PeanoArithmetic proves f (A)$ となることは同値．
]
#leancode(links: ("ProvabilityLogic/ProvabilityLogic/GLPoint3/Basic.lean",))[
  ```
  theorem arithmetical_completeness_iff_peano_arithmetic [DecidableEq α] :
    A ∈ LogicGLPoint3 ↔ ∀ f : StandardConsistencyRealization α 𝗣𝗔, 𝗣𝗔 ⊢ f A
  ```
]

== 今後の進展

論理 $LogicD$ のカットフリーなシークエント計算はKashimaら @KKIM25 によって検討されている．
