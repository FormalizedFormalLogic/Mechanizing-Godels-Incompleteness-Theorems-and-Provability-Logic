#import "init.typ": *
#import "notations.typ": *

#show: thmrules
#show: init.with(
  title: [Mechanizing Gödel's Incompleteness Theorems \ and Provability Logic],
  authors: (
    author(
      "Shogo Saito",
      insts:
        institute(
          "Tohoku University",
          addr: "Sendai, Japan",
          email: "saito.shogo.q8@dc.tohoku.ac.jp",
        ),
    ),
    author(
      "Mashu Noguchi",
      insts:
        institute(
          "Kobe University",
          addr: "Kobe, Japan",
          email: "me@sno2wman.net",
        ),
      oicd: "0009-0000-8653-3403"
    ),
  ),
  abstract: [
    We formalized proofs of Gödel's first and second incompleteness theorems and
    Solovay's arithmetical completeness of $LogicGL$ and related results in Lean4 theorem prover.
  ],
  keywords: (
    "incompleteness theorems",
    "provability logic",
    "formalization of mathematics",
    "Lean",
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
There are many well-known interactive theorem provers such as Rocq @RocqProver, Isabelle @Isabelle, HOL Light @HOLLight @HOLLightTutorial, Agda @Agda, and Lean @dMU21, and mathematics has been mechanized in each of them, including in the field of mathematical logic#footnote[Some of these mechanizations are summarized in @AwesomeLogicFormalization.].
In particular, for mechanizing Gödel's incompleteness theorems, this line of work began with Shankar in 1986 @Sha86 @Sha97, and continues with O'Connor @OCo05 @OCo09, Harrison @Har06, Paulson @Pau15, and Popescu and Traytel @PT19 @PT21, Kirst and Peters @KP23.
As for provability logic, modal-logical properties of #LogicGL, such as its semantical completeness and automated solvers, have been mechanized by Harrison @HOLLightTutorial[Chapter 20]#footnote[We don't know when Harrison's mechanization of modal logic was carried out.], Goré and Kelly @GK07, Goré, Ramanayake and Shillito @GRS21, Maggesi and Perini Brogi @MPB21 @MPB23, Gignoux @Gig26.
However, these are either abstract or not full mechanizations within arithmetic.
For instance, O'Connor's implementation assumes several facts needed for the proof of G2 as axioms, and Paulson's mechanization of G2 uses hereditarily finite sets, not arithmetic.
To the best of our knowledge, no full formalization of the incompleteness theorems entirely within arithmetic is known, and consequently, no mechanization about provability logic has been reported.

In this paper, we present machine-assisted formalizations of Gödel's 1st and 2nd incompleteness theorems and Solovay's arithmetical completeness theorem.
Our work is carried out in Lean 4, an interactive theorem prover, together with mathlib4 @mathlib2020, its community-developed mathematics library.
Lean 4 is based on the Calculus of Inductive Constructions (CIC) @dMU21,
and features dependent types, quotient types, and support for noncomputable definitions, making it highly expressive.
In addition, its powerful metaprogramming infrastructure like aesop @LF23 enables efficient proof automation and extensibility.

Our mechanization is currently hosted as a repository on GitHub, and the version we refer to is #link(REPO_SOURCES.at("Foundation")).
In this report, we will briefly and informally introduce the mathematical facts without omitting the essentials, and show the code of our mechanization corresponding to those facts.
However, for the sake of readability, note that in some places we have modified the hosted code.
Moreover, owing to motivations other than the incompleteness theorems and provability logic that this report focuses on, some implementations are stated as more general definitions.
We add comments where we deem it necessary, but for the actual working (verified) code, refer to the repository.

#include "first-order-logic.typ"

= Provability Logic

In this section, we describe our mechanization of modal logic, in particular of provability logic.
As the most fundamental and important result in the field of provability logic, we have succeeded in mechanizing Solovay's arithmetical completeness theorem @Sol76.
We have also mechanized the classification theorem of provability logics due to Beklemishev @Bek90.
As in the previous section, we keep the introduction of definitions and facts brief.
For the details of modal logic and provability logic, we refer the reader to the standard textbooks @CZ97 @Boo94 @Smo85 and the surveys @JdJ98 @AB05 @BV06 @Ver24.

== Basics of modal logic

We first set up the basic framework of modal logic.

#definition[
  Formulas of modal logic are built from propositional variables (denoted by #Prop), the primitive logical connectives $bot$ and $limp$, and the modal operator $Box$.
  The remaining operators $top, lnot, land, lor, liff, Dia$ are introduced as the usual abbreviations.
  We also abbreviate $Boxdot A equiv A land Box A$.
  A _substitution_ is a map $s$ assigning a formula to each propositional variable, and $A[s]$ denotes the formula obtained from $A$ by replacing every occurrence of each propositional variable $p$ with $s(p)$.
  For a finite set of formulas $Gamma$, we write $Box Gamma = { Box B | B in Gamma }$.
  The set of subformulas of $A$ is denoted by $subfml(A)$.
  A set of formulas is called a _logic_ when we want to emphasize this viewpoint, and we write $L proves A$ for $A in L$ when $L$ is a logic.
]

#leancode(
  note: [
    In the mechanization, the propositional variables are parameterized by a type `α`.
    For instance, taking `α` to be `Empty` yields the formulas containing no propositional variables (called closed or letterless formulas).
  ],
  links: (
    ("ProvabilityLogic", "ProvabilityLogic/Formula/Basic.lean"),
    ("ProvabilityLogic", "ProvabilityLogic/Formula/Substitution.lean"),
    ("ProvabilityLogic", "ProvabilityLogic/Logic/Basic.lean"),
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

In this paper, we mainly characterize the logic #LogicGL in three ways: by a Gentzen-style sequent calculus, by Kripke semantics, and by a Hilbert-style proof system.
Although #LogicGL is usually defined in the Hilbert style, when proving the Kripke completeness, introducing a sequent calculus makes both the mathematical proofs and the implementation of the mechanization simpler.
Moreover, as applications, the interpolation theorem and the fixed point theorem can be derived easily via the sequent calculus (we will discussed in @sect:application-of-sequent-calculus).
Hence, in our mechanization we first define the Gentzen-style sequent calculus, and eventually prove the equivalence of all these characterizations (@thm:GL_TFAE).

We first introduce the Gentzen-style sequent calculus.
Our sequent calculus for #LogicGL is due to Sambin and Valentini @SV82.

#definition[
  A _sequent_ $Gamma => Delta$ is a pair of finite sets of formulas.
  The sequent calculus $GentzenGL$ for #LogicGL consists of the following rules,
  where in the weakening rules (wkL) and (wkR) we assume $Gamma subset.eq Gamma'$ and $Delta subset.eq Delta'$ respectively. We write $GentzenGL proves Gamma => Delta$ if the sequent $Gamma => Delta$ is provable in $GentzenGL$.

  #align(center, grid(
    columns: 2,
    column-gutter: 4em,
    row-gutter: 2em,
    prooftree(rule(name: [(Ax)], $A => A$)),
    prooftree(rule(name: [($bot$L)], $bot =>$)),
    prooftree(rule(name: [(WL)], $Gamma' => Delta$, $Gamma => Delta$)),
    prooftree(rule(name: [(WR)], $Gamma => Delta'$, $Gamma => Delta$)),
    prooftree(rule(
      name: [($limp$L)],
      $A limp B, Gamma => Delta$,
      $Gamma => A, Delta$,
      $B, Gamma => Delta$,
    )),
    prooftree(rule(name: [($limp$R)], $Gamma => A limp B, Delta$, $A, Gamma => B, Delta$)),
    grid.cell(colspan: 2, prooftree(rule(
      name: [($Box_LogicGL$)],
      $Box Gamma => Box A$,
      $Box A, Gamma, Box Gamma => A$,
    ))),
  ))
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Gentzen/Basic.lean"),))[
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

Note that this system contains no cut rule.
We also define the system extended with the cut rule (denoted by `⊢ᵍᶜ` in the mechanization), and the equivalence corresponding to the cut-elimination theorem of Sambin and Valentini @SV82 is also mechanized as a part of @thm:GL_TFAE.

Next, we introduce Kripke semantics.
Since we are not concerned with modal logic in general, we omit the notion of frames and work only with models.

#definition[
  Let $W$ be a nonempty set, whose elements are called _worlds_ or _points_.
  A _Kripke model_ is a pair $M = chevron.l W, R, V chevron.r$, where $R subset.eq W times W$ (the _accessibility relation_) and $V colon W -> Prop -> 2$ (the _valuation_).
  When there is no danger of confusion, we write $x prec y$ for $x R y$.

  We use the following terminology for models.
  - A model is _finite_ if $W$ is a finite set.
  - A model is _transitive_ (resp. _irreflexive_) if $R$ is transitive (resp. irreflexive).
  - A point $r in W$ is a _root_ if $r R x$ for every $x in W$ with $x != r$. A model with a designated root is called a _rooted model_.
  - A model is a _$LogicGL$-model_ if $R$ is transitive and conversely well-founded. In particular, a finite, transitive, and irreflexive model is called a _finite $LogicGL$-model_; every such model is a $LogicGL$-model.

  For a model $M$, a point $x$ of $M$, and a formula $A$, the _forcing relation_ $M, x forces A$ is defined as follows.
  - $M, x forces p$ iff $V(x, p) = 1$.
  - $M, x forces.not bot$.
  - $M, x forces A limp B$ iff $M, x forces A$ implies $M, x forces B$.
  - $M, x forces Box A$ iff $M, y forces A$ for every $y in W$ with $x R y$.
]
#leancode(
  links: (
    ("ProvabilityLogic", "ProvabilityLogic/Kripke/Basic.lean"),
    ("ProvabilityLogic", "ProvabilityLogic/Kripke/RootedModel.lean"),
  ),
  note: [
    $W$ is given as an arbitrary nonempty type `κ`, and a model is implemented as a pair of a relation and a valuation.
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

For later use, we also introduce the notions of the _rank_ of a point and the _height_ of a finite $LogicGL$-model.

#definition[
  Let $M$ be a finite $LogicGL$-model.
  - The _rank_ $upright("rank")(x) < omega$ of a point $x$ is the maximal length $n$ of the $R$-chains $x prec y_1 prec dots.c prec y_n$ starting from $x$.
  - The _height_ of a rooted finite $LogicGL$-model $M$ is the rank of its root.
  These notions are well-defined since $M$ is conversely well-founded.
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Kripke/Rank.lean"),))[
  ```
  noncomputable def World.rank {M : Model κ α} [Fintype M.World] [M.IsGL] (x : M.World) : ℕ :=
    cwfHeight (· ≺ ·) x

  noncomputable def height (M : RootedModel κ α) [Fintype M.World] [M.IsGL] : ℕ := M.root.1.rank
  ```
]

Finally, we introduce the Hilbert-style proof system.

#definition[
  The Hilbert-style proof system $HilbertGL$ for #LogicGL consists of the following axioms and inference rules.
  We write $HilbertGL proves A$ if $A$ is provable in $HilbertGL$, and define logic $LogicGL := { A : HilbertGL proves A }$.

  1. Tautologies of classical propositional logic (cf. @CZ97)
  2. Axiom $AxiomK$: $Box(A limp B) limp (Box A limp Box B)$
  3. Axiom $Axiom("4")$: $Box A limp Box Box A$
  4. Axiom $AxiomL$: $Box(Box A limp A) limp Box A$
  5. Inference rules: modus ponens (MP) and the necessitation rule (Nec).
]
#leancode(
  links: (
    ("ProvabilityLogic", "ProvabilityLogic/Hilbert/Basic.lean"),
    ("ProvabilityLogic", "ProvabilityLogic/Logic/GL/Basic.lean"),
  ),
  note: [
    Łukasiewicz's three axioms would suffice to prove all tautologies of classical propositional logic, but then the axioms listed here would have to be proved syntactically, which is extremely tedious; so we adopt all of them as axioms.
    Axiom $Axiom("4")$ is syntactically derivable from the others (cf. @Boo94[Chapter 1, Theorem 18]), but its proof is a tedious puzzle, so our mechanization adopts it as an axiom.
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

As the equivalence of these characterizations, we mechanized the following.

#theorem[Characterization of #LogicGL][
  The following are equivalent.

  1. $LogicGL proves A$.
  2. $HilbertGL proves A$.
  2. $GentzenGL proves => A$.
  3. $GentzenWithCutGL proves => A$.
  4. $=> 0 : A$ is provable in the labelled sequent calculus (see @sect:labelled-sequent-calculus).
  5. $A$ is forced at every point of every finite $LogicGL$-model.
  6. $A$ is forced at the root of every rooted finite $LogicGL$-model.
  7. $A$ is forced at the root of every rooted finite $LogicGL$-model that is a tree.
] <thm:GL_TFAE>
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Logic/GL/Basic.lean"),))[
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

Here are a few remarks.
The Kripke completeness of $LogicGL$ (the equivalence of 1 and 6) is due to Segerberg @Seg71.
This is the usual Kripke completeness with respect to the class of finite $LogicGL$-models, and has already been mechanized in HOL Light by Maggesi and Perini Brogi @MPB21 @MPB23.
However, the proof of the arithmetical completeness theorem described later requires not the mere Kripke completeness, but the completeness with respect to rooted models (7, and furthermore 8).
The transformation of a rooted model into a tree model is done by the technique known as tree unraveling (cf. @CZ97[Theorem 3.18]).
The equivalence of 3 and 4 corresponds to the cut-elimination theorem.

Next, we introduce the modal logics $LogicS$ (due to Solovay @Sol76) and $LogicD$ (due to Japaridze (Dzhaparidze) @Jap86), which play important roles in provability logic.

#definition[
  For logics $L_1, L_2$, we write $sumQuasiNormal(L_1, L_2)$ for the logic obtained by closing the union of $L_1$ and $L_2$ under MP and substitution.

  Then Solovay's provability logic and Japaridze's provability logic are defined as follows.
  - $LogicS := sumQuasiNormal(LogicGL, { Box A limp A | A })$.
  - $LogicD := sumQuasiNormal(LogicGL, ({ lnot Box bot } union { Box(Box A lor Box B) limp Box A lor Box B | A, B }))$.
]
#leancode(links: (
  ("ProvabilityLogic", "ProvabilityLogic/Logic/SumQuasiNormal.lean"),
  ("ProvabilityLogic", "ProvabilityLogic/Logic/S/Basic.lean"),
  ("ProvabilityLogic", "ProvabilityLogic/Logic/D/Basic.lean"),
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

These logics are non-normal, i.e., not closed under the necessitation rule, so Kripke semantics cannot be applied directly.
However, they are known to be sound and complete with respect to classes of infinite models obtained by suitably extending finite $LogicGL$-models.
Such models for $LogicS$ are called tail models @Vis84, and for $LogicD$ the so-called pseudo tail models (cf. @Bek90) are used.
We omit the details of these constructions; via these semantic characterizations, we mechanized the following two propositions.

#proposition[cf. @Vis84][
  The following are equivalent.

  1. $LogicS proves A$
  2. On the chain of the tail model constructed from any finite $LogicGL$-model and any point $t$ of it, $A$ is eventually always forced.
  3. $and.big_(Box B in subfml(A)) (Box B limp B) limp A$ is forced at the root of every rooted finite $LogicGL$-model.
  4. $LogicGL proves and.big_(Box B in subfml(A)) (Box B limp B) limp A$
] <prop:S_characterization>
#leancode(
  links: (("ProvabilityLogic", "ProvabilityLogic/Logic/S/Basic.lean"),),
  note: [
    The last clause is provability of the Gentzen-style sequent calculi with two-level sequent @Kus20 @KK23.
    About this, we discusses as future work on @sect:provabilitylogic_futurework.
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
  The following are equivalent, where $prebox(X) = {B | Box B in X}$ for a set of formulas $X$.

  1. $LogicD proves A$
  2. $A$ is forced at the root of the pseudo tail model constructed from any finite $LogicGL$-model.
  3. $and.big_(Gamma subset.eq prebox(subfml(A))) (Box(or.big Box Gamma) limp or.big Box Gamma) limp A$ is forced at the root of every rooted finite $LogicGL$-model.
  4. $LogicGL proves and.big_(Gamma subset.eq prebox(subfml(A))) (Box(or.big Box Gamma) limp or.big Box Gamma) limp A$
] <prop:D_characterization>
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Logic/D/Basic.lean"),))[
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

The mere inclusions between these logics hold trivially by definition.
Moreover, by constructing countermodels via the semantics, the following proper inclusions hold.

#proposition[
  $LogicGL subset.neq LogicD subset.neq LogicS$
]
#leancode(
  links: (
    ("ProvabilityLogic", "ProvabilityLogic/Logic/D/Basic.lean"),
    ("ProvabilityLogic", "ProvabilityLogic/Logic/S/Basic.lean"),
  ),
)[
  ```
  lemma LogicGL_ssubset_LogicD [DecidableEq α] : (LogicGL : Logic α) ⊂ LogicD

  lemma LogicD_ssubset_LogicS [Inhabited α] [DecidableEq α] : (LogicD : Logic α) ⊂ LogicS
  ```
]

=== Applications of the sequent calculus <sect:application-of-sequent-calculus>

Sambin and Valentini @SV82 give several further applications of the sequent calculus for $LogicGL$.
First, since it is a pure sequent calculus, the Craig interpolation property (CIP) can be shown straightforwardly by Maehara's method @Mae61 (cf. @Tak87).

#theorem[Craig Interpolation Property for #LogicGL][
  If $LogicGL proves A limp B$, then there exists a formula $C$ such that $LogicGL proves A limp C$ and $LogicGL proves C limp B$, and every propositional variable of $C$ occurs in both $A$ and $B$.
] <thm:GL_CIP>
#leancode(links: (
  ("ProvabilityLogic", "ProvabilityLogic/Logic/GL/CIP.lean"),
  ("ProvabilityLogic", "ProvabilityLogic/Gentzen/Maehara.lean"),
))[
  ```
  theorem CIP (h : (A 🡒 B) ∈ LogicGL) :
    ∃ C : Formula α, (A 🡒 C) ∈ LogicGL ∧ (C 🡒 B) ∈ LogicGL ∧ C.atoms ⊆ A.atoms ∩ B.atoms
  ```
]

The CIP of $LogicGL$ is important in particular because it yields the fixed point theorem of #LogicGL @Smo78 @Boo79.
We have also mechanized the fixed point theorem of $LogicGL$ via the sequent calculus.

#definition[
  A propositional variable $p$ is _modalized_ in a formula $A$ if every occurrence of $p$ in $A$ is within the scope of $Box$.
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Formula/Modalized.lean"),))[
  ```
  def ModalizedIn (p : α) : Formula α → Prop
    | #a    => a ≠ p
    | ⊥     => True
    | A 🡒 B => A.ModalizedIn p ∧ B.ModalizedIn p
    | □_    => True
  ```
]

#theorem[Fixed point theorem of #LogicGL @SV82][
  Suppose that $p$ is modalized in $A$.
  Then there exists a formula $D$ not containing $p$ and consisting only of propositional variables of $A$ such that
  $ LogicGL proves A[p := D] <-> D $
  Moreover, the fixed point is unique up to provable equivalence:
  for a propositional variable $q$ not occurring in $A$,
  $ LogicGL proves Boxdot(A <-> p) land Boxdot(A[p := q] <-> q) limp (p <-> q) $
] <thm:GL_fixpoint>
#leancode(
  links: (("ProvabilityLogic", "ProvabilityLogic/Logic/GL/Fixedpoint.lean"),),
)[
  ```
  theorem fixpointTheorem {A : Formula α} {p q : α}
    (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    ∃ D : Formula α, D.atoms ⊆ A.atoms \ {p} ∧ ((A⟦p ↦ D⟧) 🡘 D) ∈ LogicGL

  theorem fixpoint_uniqueness (hA : A.ModalizedIn p) :
    ⊢ᵍ ({⊡(A 🡘 #p), ⊡((A⟦p ↦ #q⟧) 🡘 #q)} ⟹ {(#p : Formula α) 🡘 #q})
  ```
]

The fixed point theorem of #LogicGL has also been mechanized in Lean, by Gignoux @Gig26.
We note that, whereas Gignoux's mechanization proves it by a semantical method, in our mechanization the interpolants and the fixed points can be computed constructively inside Lean from derivation trees of the sequent calculus.
However, at present derivation trees of the sequent calculus cannot be constructed automatically by proof search or the like, so concrete derivation trees have to be input by hand. Also, when $LogicGL proves A$ is proved non-constructively, e.g., via Kripke semantics, the interpolants and the fixed points are of course not computable in Lean.

Finally, we have also mechanized facts on the CIP of $LogicS$ and $LogicD$, which we briefly mention.

#theorem[@Bek87][
  $LogicS$ has the CIP.
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Logic/S/CIP.lean"),))[
  ```
  theorem CIP (h : (A 🡒 B) ∈ LogicS) :
    ∃ C : Formula α, (A 🡒 C) ∈ LogicS ∧ (C 🡒 B) ∈ LogicS ∧ C.atoms ⊆ A.atoms ∩ B.atoms
  ```
]

#theorem[@Bek89][
  $LogicD$ does not have the CIP.
  In particular, for the following $A$ and $B$, $LogicD proves not A -> B$ but there exists no interpolant for it,
  where $a,b,c$ are distinct propositional variables.
  $
    A & equiv Box (Box b or a) -> Box b \
    B & equiv Box (a -> Box c) -> Box c
  $
] <thm:D_no_CIP>
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Logic/D/NotCIP.lean"),))[
  ```
  theorem notCIP {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ A B : Formula α, (A 🡒 B) ∈ LogicD ∧
      ¬ ∃ C : Formula α, (A 🡒 C) ∈ LogicD ∧ (C 🡒 B) ∈ LogicD ∧
        C.atoms ⊆ A.atoms ∩ B.atoms
  ```
]

=== On the labelled sequent calculus <sect:labelled-sequent-calculus>

We have also mechanized the labelled sequent calculus for #LogicGL by Negri @Neg05 @Neg14. As for prior work, our mechanization is almost the same in its method as the mechanization of the labelled sequent calculus for #LogicGL in HOL Light by Maggesi and Perini Brogi @MPB21 @MPB23, and in that sense it has little novelty.
We nevertheless touch on some differences between the implementations.

The termination of Maggesi and Perini Brogi's _implementation_ of the calculus is guaranteed as a mathematical fact on the meta-level.
That is, by the mathematical fact proved in @Neg14, the computation is guaranteed to terminate under the assumption that their implementation is correct.
On the other hand, when defining the proof search, we guarantee its termination inside the theorem prover itself, since Lean requires the definition to be well-founded.
In this respect, our mechanization gives a stronger guarantee.
However, Maggesi and Perini Brogi's mechanization has a practical utility: although the termination is not guaranteed, it can actually be executed and used as a tactic, which automates simple proofs of #LogicGL appearing in their mechanization.
In contrast, due to the implementation constraints in the well-foundedness proof, our labelled sequent calculus cannot be used, e.g., as a Lean tactic, and its properties are mechanized purely as mathematical facts.
Hence, regarding the practical utility, Maggesi and Perini Brogi's mechanization has the advantage.

Moreover, we remark that interpolation for labelled sequent calculi in general is discussed, e.g., in @vdGJK26[Section 5], but whether it is possible for the labelled sequent calculus for #LogicGL seems to be open at present.
From this, we conclude that labelled calculi are not so effective for mechanizing the properties of #LogicGL described in @sect:application-of-sequent-calculus.

== Arithmetical completeness theorems

In this section, we describe the main results of our mechanization of provability logic: the mechanization of Solovay's arithmetical completeness theorem @Sol76 and its generalization.

First, we define arithmetical interpretations, which translate modal formulas into arithmetical sentences.
In what follows, $T$ is an arithmetical theory with a $Delta_1$-definable axiomatization extending $Theory("I")Sigma_1$, and we consider only the standard provability predicate $Pr(T)$ of $T$.

#definition[
  A map $f colon Prop -> upright("Sent")_upright("A")$ is called an _arithmetical realization_ (or simply a _realization_).
  Given a realization $f$, the _(standard) arithmetical interpretation_ is the extension of $f$ translating each modal formula $A$ into an arithmetical sentence $f_(Pr(T))(A)$ as follows.
  - $f_(Pr(T)) (p) & = f(p)$
  - $f_(Pr(T)) (bot) & = bot$
  - $f_(Pr(T)) (A limp B) & = f_(Pr(T)) (A) limp f_(Pr(T)) (B)$
  - $f_(Pr(T)) (Box A) & = Pr(T) (GoedelNum(f_(Pr(T))(A)))$

]
#leancode(
  links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/Interpret.lean"),),
  note: [
    For technical reasons, realizations are implemented for an arbitrary provability predicate `𝔅`.
    However, since we consider only the standard provability predicate in this report, we always use `StandardRealization`, which takes `T.standardProvability` for `𝔅`.
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
  The _(standard) provability logic of $T$ relative to $U$_, written $ProvLogic(T, U)$, is defined as follows.
  $
    ProvLogic(T, U) = { A | #text[$U proves f_(Pr(T)) (A)$ for every realization $f$] }
  $
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/Interpret.lean"),))[
  ```
  def provabilityLogicRelativeTo (T U : ArithmeticTheory) [T.Δ₁] : Logic α :=
    {A | ∀ f : StandardRealization α T, U ⊢ f A}

  abbrev provabilityLogic (T : ArithmeticTheory) [T.Δ₁] : Logic α := T.provabilityLogicRelativeTo T
  ```
]

Solovay's arithmetical completeness theorem states that the behavior of the standard provability predicate, viewed as a modal operator, is captured exactly by the modal logic #LogicGL.
That is, for appropriate choices of $T$ and $U$, the provability logic $ProvLogic(T, U)$ coincides with #LogicGL.
Here we present the generalized version (@thm:arithmetical_completeness) using the notion of the _height_ of a theory due to Visser @Vis81.

#definition[Height of a theory][
  For $n >= 0$, $Pr(T)^n$ denotes the $n$-fold iteration of the provability predicate $Pr(T)$ (where $Pr(T)^0(x) equiv x$).
  The _height_ $height(T) <= omega$ of a theory $T$ is the least $n in omega$ such that $T proves Pr(T)^n (GoedelNum(bot))$; if no such $n$ exists, we set $height(T) = omega$.
]
#leancode(
  links: (("Foundation", "Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Height.lean"),),
  note: [
    As with realizations, it is defined for an arbitrary provability predicate `𝔅`, but we consider only the standard one in this report.
  ],
)[
  ```
  noncomputable def Provability.height (𝔅 : Provability T₀ T) : ENat := ENat.find (T ⊢ 𝔅^[·] ⊥)

  noncomputable abbrev ArithmeticTheory.height (T : ArithmeticTheory) [T.Δ₁] : ℕ∞ :=
    T.standardProvability.height
  ```
]

Note that if $T$ is $Sigma_1$-sound, then $T nproves Pr(T)^n (GoedelNum(bot))$ for every $n in omega$, and hence $height(T) = omega$.

#definition[
  For $n <= omega$, abusing notation, we define the logic #LogicGLPlusBoxBot($n$) as follows:
  for $n < omega$ it is $sumQuasiNormal(LogicGL, {Box^n bot})$, and for $n = omega$ it is #LogicGL itself.
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Logic/GLPlusBoxBot/Basic.lean"),))[
  ```
  def LogicGLPlusBoxBot {α} : ℕ∞ → Logic α
    | .some n => LogicGL +ᴸ □^[n]⊥
    | .none   => LogicGL
  ```
]

The main result of our mechanization of provability logic is the following.

#theorem[@Vis81][
  $ProvLogic(T, T) = LogicGLPlusBoxBot(height(T))$
] <thm:arithmetical_completeness>
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/GLPlusBoxBot/Basic.lean"),))[
  ```
  lemma eq_provabilityLogic : LogicGLPlusBoxBot (α := α) T.height = T.provabilityLogic
  ```
]

@thm:arithmetical_completeness is proved by embedding into arithmetic a rooted finite $LogicGL$-model of an appropriate height, obtained as a countermodel when $LogicGLPlusBoxBot(height(T)) nproves A$ (the construction of Solovay sentences).
This is where the completeness with respect to rooted models stated in @thm:GL_TFAE is needed.
As a corollary, we obtain Solovay's original statement.

#corollary[Solovay's (first) arithmetical completeness theorem @Sol76][
  If $T$ is $Sigma_1$-sound, then $ProvLogic(T, T) = LogicGL$.
  In particular, $ProvLogic(PeanoArithmetic, PeanoArithmetic) = LogicGL$.
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/GL/Basic.lean"),))[
  ```
  theorem eq_provabilityLogic_sigma1_sound [T.SoundOnHierarchy 𝚺 1] :
    @LogicGL α = T.provabilityLogic

  theorem eq_provabilityLogic_peano_arithmetic : @LogicGL α = (𝗣𝗔.provabilityLogic)
  ```
]

Furthermore, Solovay also proved that #LogicS is arithmetically complete with respect to the true arithmetic #TrueArithmetic.
The reduction of $LogicS$ to $LogicGL$ stated in @prop:S_characterization is essentially used in this proof.

#theorem[Solovay's (second) arithmetical completeness theorem @Sol76][
  Let $T$ be a sound theory.
  For every formula $A$, $LogicS proves A$ if and only if $NN models f_(Pr(T)) (A)$ for every realization $f$.
  That is, $ProvLogic(T, TrueArithmetic) = LogicS$.
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/S/Basic.lean"),))[
  ```
  theorem arithmetical_completeness_iff [DecidableEq α] :
    A ∈ LogicS ↔ (∀ f : StandardRealization α T, ℕ↓[ℒₒᵣ] ⊧ f A)

  theorem eq_provabilityLogicRelativeTo_TA [DecidableEq α] :
    @LogicS α = T.provabilityLogicRelativeTo 𝗧𝗔
  ```
]

== The classification theorem of provability logics

The classification of the provability logics obtained as $ProvLogic(T, U)$ for arbitrary theories $T$ and $U$ was studied by Artemov, Beklemishev, Visser, Japaridze, and others, and was finally completed by Beklemishev @Bek90.
We have also mechanized this classification theorem.
Since its proof involves difficult arguments in both arithmetic and Kripke semantics, we again omit the details of the proofs and list the main results.
For the details, see @Bek90 @AB05.

#definition[
  The _trace_ $trace(A) subset.eq omega$ of a formula $A$ is the set of all $n$ such that there exists a rooted finite $LogicGL$-model of height $n$ whose root does not force $A$.
  The _trace_ of a logic $L$ is defined by $trace(L) := union.big_(A in L) trace(A)$.
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/Classification/GeneralTrace.lean"),))[
  ```
  def trace (A : Formula α) : Set ℕ := { n |
    ∃ κ : Type u, ∃ _ : Nonempty κ, ∃ M : RootedModel κ α, ∃ _ : Fintype M.World, ∃ _ : M.IsGL,
    (M.height = n ∧ M.root.1 ⊮ A) }

  abbrev Logic.trace (L : Logic α) : Set ℕ := ⋃ A ∈ L, A.trace
  ```
]

#definition[
  For $n in omega$, define the formula $F_n := Box^(n+1) bot limp Box^n bot$.
  For $alpha subset.eq omega$ and cofinite $beta subset.eq omega$, we define the following non-normal modal logics.
  - $LogicGLAlpha(alpha) := sumQuasiNormal(LogicGL, { F_n : n in alpha })$
  - $LogicGLBetaMinus(beta) := sumQuasiNormal(LogicGL, { lnot and.big_(n in omega without beta) F_n })$

  In particular, we call $LogicGLAlpha(omega)$ as $LogicA$#footnote[We follow the naming of @JdJ98; it presumably stands for Artemov.].
]
#leancode(
  note: [
    Since $F_n$ is hard to use as an identifier, the mechanization names $F_n$ as `TBB` (axiom $Axiom("T")$ for Box Bot).
  ],
  links: (
    ("ProvabilityLogic", "ProvabilityLogic/Formula/Basic.lean"),
    ("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/Classification/LetterlessTrace.lean"),
  ),
)[
  ```
  def TBB (n : ℕ) : Formula α := (□^[(n + 1)]⊥) 🡒 (□^[n]⊥)

  abbrev LogicGLAlpha {α} (Alpha : Set ℕ) : Logic α := (@LogicGL α) +ᴸ ↑(Alpha.image $ TBB (α := Empty))

  abbrev LogicA {α} : Logic α := LogicGLAlpha Set.univ

  noncomputable abbrev TBBMinus [DecidableEq α] (X : Set ℕ) (X_finite : X.Finite) : Formula α :=
    ∼⋀(X_finite.toFinset.image TBB)

  abbrev LogicGLBetaMinus {α} [DecidableEq α] (Beta : Set ℕ) (Beta_cofinite : Betaᶜ.Finite) : Logic α :=
    (@LogicGL α) +ᴸ (LetterlessFormulaSet.lift { TBBMinus _ Beta_cofinite })
  ```
]

The most essential lemmas in the proof of the classification theorem are the following two facts.
One is proved by an arithmetical argument, and the other by a Kripke-semantical argument.

#lemma[@AB05[Corollary 55, Corollary 58]][
  Let $L$ be a provability logic with $trace(L) = omega$.
  1. It is impossible that $LogicA subset.neq L subset.neq LogicD$.
  2. It is impossible that $LogicD subset.neq L subset.neq LogicS$.
]
#leancode(links: (
  ("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/Classification/A_D.lean"),
  ("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/Classification/D_S.lean"),
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

The classification theorem is stated as follows.

#theorem[Classification theorem of provability logics @Bek90 @AB05[Theorem 40]][
  Let $L = ProvLogic(T, U)$ for arbitrary theories $T$ and $U$. Then $L$ is classified as follows:
  1. If $trace(L)$ is coinfinite, then $L = LogicGLAlpha(trace(L))$.
  2. If $trace(L)$ is cofinite and $L subset.eq.not LogicS$, then $L = LogicGLBetaMinus(trace(L))$.
  3. If $trace(L)$ is cofinite and $L subset.eq LogicS$, then $L$ is one of $LogicGLAlpha(trace(L))$, $LogicD inter LogicGLBetaMinus(trace(L))$, and $LogicS inter LogicGLBetaMinus(trace(L))$.
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/Classification/Result.lean"),))[
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

Furthermore, @Bek90 also proved the classification theorem for the _truth provability logics_, i.e., the logics of the form $ProvLogic(T, TrueArithmetic)$.
We have mechanized this fact as well.

#theorem[Classification theorem of truth provability logics @Bek90 @AB05[Corollary 41]][
  $L = ProvLogic(T, TrueArithmetic)$ is one of the following, and each case is characterized by the properties of $T$.
  1. $L = LogicS$ if and only if $T$ is sound.
  2. $L = LogicD$ if and only if $T$ is $Sigma_1$-sound but not sound.
  3. $L = LogicA$ if and only if $T$ is not $Sigma_1$-sound and $height(T) = omega$.
  4. $L = LogicGLBetaMinus(omega without {n})$ if and only if $height(T) = n < omega$.
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/Classification/Result.lean"),))[
  ```
  theorem classification_provabilityLogic_TA [DecidableEq α] [Nonempty α] :
    letI L : Logic α := T.provabilityLogicRelativeTo 𝗧𝗔;
    (ℕ↓[ℒₒᵣ] ⊧* T ∧ L = LogicS) ∨
    (T.SoundOnHierarchy 𝚺 1 ∧ ¬(ℕ↓[ℒₒᵣ] ⊧* T) ∧ L = LogicD) ∨
    (¬(T.SoundOnHierarchy 𝚺 1) ∧ T.height = (⊤ : ℕ∞) ∧ L = LogicA) ∨
    ∃ n : ℕ, T.height = n ∧ L = LogicGLBetaMinus {n}ᶜ (by simp)
  ```
]

== On some remaining `sorry`s

Although the mechanization of the classification theorem itself does not depend on them, some facts of provability logic currently remain with `sorry`.
We note them here.

The first is the statement that $LogicD$ is indeed a provability logic, which is currently not `sorry`-free.
#theorem[@Jap86 @AB05[Example 60]][
  $LogicD = ProvLogic(T, T + upright("Rfn")_(Sigma_1)(T))$,
  where $upright("Rfn")_(Sigma_1)(T)$ is the (local) reflection principle for $Sigma_1$ formulas of $T$.
] <thm:D_is_provability_logic>

This is because the following fact has not been mechanized in our development.
Proving it requires arguments involving partial truth definitions, which we have not yet completed.

#theorem[Unboundedness @KL68 @AB05[Theorem 23]][
  $upright("Rfn")_(Sigma_n)(T)$ is not provable in any consistent r.e. extension of $T$ by $Pi_n$ sentences.
]

The other is the uniform arithmetical completeness theorem.

#theorem[Uniform Arithmetical Completeness Theorem][
  For every $Sigma_1$-sound theory $T$, a uniform arithmetical interpretation $f$ can be constructed.
  That is, for every formula $A$, $LogicGL proves A$ if and only if $T proves f_(Pr(T)) (A)$.
]

== On $LogicGLPoint3$

A sequent calculus for $LogicGLPoint3$ was given by Valentini @VS83 @Val86.
In particular, @VS83 shows that $LogicGLPoint3$ enjoys a certain arithmetical completeness with respect to the class of arithmetical sentences called consistency assertions.
We briefly describe these results.

#definition[
  $LogicGLPoint3$ is the normal modal logic obtained from #LogicGL by adding the weak linearity axiom $Box(Boxdot A limp B) lor Box(Boxdot B limp A)$#footnote[In older literature, it was also written as $Logic("GLLin")$ @VS83 @Val86 or $Logic("K4.3W")$ @Seg71.].
]

#leancode(links: (
  ("ProvabilityLogic", "ProvabilityLogic/Logic/SumNormal.lean"),
  ("ProvabilityLogic", "ProvabilityLogic/Logic/GLPoint3/Basic.lean"),
))[
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
  A finite $LogicGL$-model is called _finite $LogicGLPoint3$_ when $prec$ is linear, i.e., $x prec y$ and $x prec z$ imply $y prec z$ or $y = z$ or $z prec y$.
]

#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Kripke/Linearity.lean"),))[
  ```
  class IsFiniteGLPoint3 (M : Model κ α) extends Model.IsFiniteGL M where
    linear : ∀ {x y z : M.World}, x ≺ y → x ≺ z → y ≺ z ∨ y = z ∨ z ≺ y
  ```
]

#definition[
  The sequent calculus $GentzenGLPoint3$ for $LogicGLPoint3$ is obtained from the sequent calculus for #LogicGL by replacing the $Box upright("GL")$ rule with the following rule,
  where $Delta != emptyset$ and ${S_1, dots, S_m} = PowerSet(Delta) without {emptyset}$ (hence $m = 2^(|Delta|) - 1$).

  #align(center, prooftree(rule(
    name: [($Box$GL.3)],
    $Box Gamma => Box Delta$,
    $Gamma, Box Gamma, Box S_1 => S_1, Box(Delta without S_1)$,
    $dots.c$,
    $Gamma, Box Gamma, Box S_m => S_m, Box(Delta without S_m)$,
  )))
]

Note that the case $Delta = {A}$ is exactly the $(Box_LogicGL)$ rule.

#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Gentzen/GLPoint3/Basic.lean"),))[
  ```
  inductive GLPoint3.ProofGentzen : Sequent α → Type u
  | axm (A) : ProofGentzen ({A} ⟹ {A})
  | botL : ProofGentzen ({⊥} ⟹ ∅)
  | wkL  {Γ Γ' Δ}  : ProofGentzen (Γ ⟹ Δ) → Γ ⊆ Γ' → ProofGentzen (Γ' ⟹ Δ)
  | wkR  {Γ Δ Δ'}  : ProofGentzen (Γ ⟹ Δ) → Δ ⊆ Δ' → ProofGentzen (Γ ⟹ Δ')
  | impL {Γ Δ A B} : ProofGentzen (Γ ⟹ (insert A Δ)) → ProofGentzen (insert B Γ ⟹ Δ) →
                     ProofGentzen ((insert (A 🡒 B) Γ) ⟹ Δ)
  | impR {Γ Δ A B} : ProofGentzen ((insert A Γ) ⟹ (insert B Δ)) →
                     ProofGentzen (Γ ⟹ (insert (A 🡒 B) Δ))
  | boxGLPoint3 {Γ Δ} (hΔ : Δ.Nonempty) :
      (∀ S : FormulaFinset α, S ⊆ Δ → S.Nonempty →
        ProofGentzen ((Γ.box ∪ Γ ∪ S.box) ⟹ (S ∪ (Δ \ S).box))) →
      ProofGentzen (Γ.box ⟹ Δ.box)
  prefix:120 "⊢ᵍ³! " => GLPoint3.ProofGentzen
  ```
]

For these characterizations, equivalences analogous to those for #LogicGL hold.

#theorem[@VS83][
  The following are equivalent.
  1. $LogicGLPoint3 proves A$.
  2. $GentzenGLPoint3 proves => A$.
  3. $A$ is forced at every point of every finite $LogicGLPoint3$-model.
  4. $A$ is forced at the root of every rooted finite $LogicGLPoint3$-model.
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Logic/GLPoint3/Completeness.lean"),))[```
  theorem provability_TFAE [DecidableEq α] {A : Formula α} : [
    A ∈ LogicGLPoint3,
    ⊢ᵍ³ (∅ ⟹ {A}),
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGLPoint3] → M ⊧ A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLPoint3] → M.root.1 ⊩ A
  ].TFAE
  ```
]

In particular, on closed formulas $LogicGLPoint3$ and $LogicGL$ do not differ; this can be shown using the trace for closed formulas due to @Art86 and the sequent calculus.

#theorem[@VS83[Theorem 2]][
  For a closed formula $A$, $LogicGLPoint3 proves A$ if and only if $LogicGL proves A$.
]
#leancode(
  links: (("ProvabilityLogic", "ProvabilityLogic/Logic/GLPoint3/Letterless.lean"),),
)[
  ```
  theorem eq_LogicGL_on_letterless : @LogicGLPoint3 Empty = @LogicGL Empty
  ```
]

Finally, we state the arithmetical completeness of $LogicGLPoint3$ with respect to consistency assertions.

#definition[
  - A sentence $sigma$ is a _consistency assertion_ if it is generated from $lnot Pr(T)(GoedelNum(bot))$ and $Pr(T)(GoedelNum(bot))$ by closing under $Pr(T)(x)$, $lnot$, $land$, $lor$, and $limp$.
  - A realization $f$ is a _consistency realization_ if $f$ sends every propositional variable to a consistency assertion.
]

#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/GLPoint3/Basic.lean"),))[
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

  abbrev ConsistencyRealization (α : Type*) (𝔅 : Provability T₀ T) :=
    {f : Realization α 𝔅 // f.IsConsistencyRealization}

  abbrev StandardConsistencyRealization (α : Type*) (T : FirstOrder.ArithmeticTheory) [T.Δ₁] :=
    ConsistencyRealization α T.standardProvability
  ```
]

#theorem[@VS83[Theorem 1]][
  $LogicGLPoint3 proves A$ if and only if $PeanoArithmetic proves f (A)$ for every consistency realization $f$ over $PeanoArithmetic$.
]
#leancode(
  links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/GLPoint3/Basic.lean"),),
)[
  ```
  theorem arithmetical_completeness_iff_peano_arithmetic [DecidableEq α] :
    A ∈ LogicGLPoint3 ↔ ∀ f : StandardConsistencyRealization α 𝗣𝗔, 𝗣𝗔 ⊢ f A
  ```
]

/*
== On $Logic("Grz")$

The facts described here are not currently included in Provability Logic and are outdated, but we mention them for the record.

#definition[
  #Logic("Grz")
]

#definition[Boxdot Translation][
]

#theorem[
  $Logic("Grz") proves A^Boxdot <==> LogicGL proves A$．
]

#definition[Strong Interpretation][
]

#theorem[Arithmetical Completeness of $Logic("Grz")$ @Gol78 @Boo80][
  Let $T$ is reasonable consistent extension of $PeanoArithmetic$.
  Then, $Logic("Grz") proves A$ if and only if strong interpretation of $A$ based on $Pr(T)(x)$ is provable in $T$.
]
*/

== Related works and Milestones <sect:provabilitylogic_futurework>

Finally, we mention on some prior work related to theorem provers and mechanizations for provability logic, and describe future directions.
In the following, we restrict our attention to prior work in the field of provability logic, and omit in the other areas of modal logic (e.g., tense logic and epistemic logic).

=== Proof theory <subsect:proof_theory_provability_logic>

The proof theory of #LogicGL has been studied extensively.
First, Gentzen-style sequent calculi have been investigated in numerous works @SV80 @Lei81 @SV82 @Val83 @Bor83 @Avr84 @Sas01 @Moe01 @GR12 @Bri16.
In particular, as a syntactic issue, whether the termination of the cut-elimination algorithm holds for sequent calculi based on multisets had long been a matter of debate, and the issue is considered to have been resolved by @GR12.
On the other hand, Brighton @Bri16 gave an alternative proof of the termination of the cut-elimination algorithm using the technique called _regression trees_, and this argument has been mechanized in Rocq by Goré, Ramanayake, and Shillito @GRS21.
Furthermore, Férée et al. @FvdGvGS24 mechanized in Rocq the uniform interpolation theorem @Bil16 for #LogicGL via sequent calculi.
In particular, although their proof is based on Bílková @Bil16, we mention that in the course of the mechanization they discovered an error in @Bil16 and were able to correct it #footnote[Quoted from @FvdGvGS24[p.2]: During our work on formalising this proof in Coq, we uncovered an incompleteness in it (@Bil16), and our formalisation contains a corrected version of the construction of...].
These mechanization can be regarded as a significant result in that it settled a debate over ambiguous pen-and-paper arguments by verifying on a computer strictly.

Besides, there are also many approaches to non-Gentzen-style proof systems for #LogicGL, i.e., systems obtained by adding further machinery to ordinary sequent calculi:
e.g., the _labelled sequent calculi_ by Negri @Neg05 @Neg14, the _tree-hypersequent calculus_ by Poggiolesi @Pog09, the _nested sequent calculi_ by Maniwa and Kashima @MK24, and the _non-wellfounded proofs_ (or _circular proofs_) by Shamkanov @Sha14#footnote[Here we mention only the systems for #LogicGL. For general discussions of each formalism, we refer the reader to the references of the respective papers.].
For discussions on the equivalence of the provability of several of these sequent systems, including the Gentzen-style ones, see Goré and Ramanayake @GR12A and Lyon @Lyo25.
In particular, Shamkanov's non-wellfounded proofs have the advantage that the Lyndon interpolation theorem can be proved syntactically @Sha14[Chapter 4]#footnote[This fact itself is also proved in @Sha11, but the proof there relies on Kripke-semantical techniques.].
As far as we know, the only mechanizations of the proof theory of sequent calculi equipped with such additional machinery are the mechanization of the labelled sequent calculus in HOL Light by Maggesi and Perini Brogi @MPB21 @MPB23 and, along that line, Bilotta's HOLMS project @Bil25.


Tableau method for #LogicGL are discussed in @Boo94[Chapter 10] for instance.
A tableau-based automated theorem prover for #LogicGL is implemented by Goré and Kelly @GK07, where the efficiency of the implementation is also discussed.

#let seq(l) = $attach(tr: #l, =>)$
#let seq1 = seq("1")
#let seq2 = seq("2")
#let seq3 = seq("3")

The proof theory of #LogicS and #LogicD has been developed only recently.
Sierra Miranda and Studer @SMS26 proved the Lyndon interpolation property of #LogicS using non-wellfounded proofs.
As a different approach, Kushida @Kus20 proposed a sequent calculus for #LogicS that uses two levels of sequents $seq1$ and $seq2$.
Roughly speaking, the provable #seq1;-sequents coincide with those provable in #GentzenGL, the system is equipped with a lift-up mechanism from #seq1 to #seq2, and on the level of #seq2 one can reason as in the logic $Logic("KT")$.
While @Kus20 gives a syntactic cut-elimination algorithm, Kashima and Kato @KK23 proved the cut elimination for #LogicS by a semantical method.
Furthermore, Kashima et al. @KKIM25 extended this approach and formulated two sequent calculi for #LogicD.
The former uses two levels of sequents as for #LogicS, but has the drawback that the cut rule cannot be eliminated.
The latter uses three levels of sequents #seq1, #seq2, and #seq3, and in particular admits cut elimination.

In the present work, we have mechanized the Gentzen-style sequent calculus for #LogicGL, the labelled sequent calculus for #LogicGL (see @sect:labelled-sequent-calculus), and the two-level sequent calculus for #LogicS (see @prop:S_characterization).
For the future work, we plan to mechanize sequent calculi with other machinery as well, together with the equivalence of their provability.
In particular, although Shamkanov's circular proofs involve infinitary structures, the studies by Sierra Miranda et al. @SM23 @SMSZ24 @HSMS25 @SMS26 have revealed that they have many applications, so their mechanization seems to be a technically challenging but worthwhile task.
We also plan to mechanize the three-level sequent calculus for #LogicD following @KKIM25.
We expect that this would provide, for instance, a syntactic proof of the failure of the CIP for #LogicD (@thm:D_no_CIP) and a concise implementation of its mechanization.

=== Provability logic of Heyting arithmetic

The provability logic of intuitionistic or constructive arithmetic, in particular, Heyting arithmetic $Theory("HA")$, has been a subject of study for long time (see, e.g., @BV06[Section 4]).
Even among the recent developments alone, there is prior work such as @AM18 @AM19 @SM23a @Moj24 @Moj26.

It is known that the provability logic of $Theory("HA")$ contains at least $Logic("iGL")$, that is, that $Logic("iGL")$ is arithmetically sound to $Theory("HA")$.
Here, $Logic("iGL")$ is the logic obtained by adding Löb's axiom $Box (Box A -> A) -> A$ to the intuitionistic modal logic #Logic("iK"), the logic obtained from intuitionistic propositional logic by adding the axiom $AxiomK$ for $Box$ and the necessitation rule.
As a purely logic researches of $Logic("iGL")$, consult @Urs79 @Lit14 @vdGI21.
As for mechanization, Shillito and Goré @GS22 gave a refined version of the proof of cut elimination for the sequent calculus for $Logic("iGL")$ due to van der Giessen and Iemhoff @vdGI21, and this proof has been mechanized in Rocq.

On the other hand, the logic called the intuitionistic strong Löb logic #Logic("iSL"), obtained by adding the strong Löb axiom $(Box A -> A) -> A$ to #Logic("iK"), is also important.
For a survey of #Logic("iSL") itself as a logic, see, e.g., @VL24.
Shillito et al. @SVDGGI23 gave a new sequent calculus for #Logic("iSL") admitting cut elimination, and mechanized it in Rocq.
Férée et al. @FvdGvGS24 mechanized the uniform interpolation theorem for #Logic("iSL") in Rocq (see also @subsect:proof_theory_provability_logic).

Finally, the provability logic of Heyting arithmetic is proposed by Mojtahedi's preprint @Moj26, but it is still under review as of 2026, in the time of writing this paper#footnote[The first version was submitted to arXiv in 2022.].
In the future, we plan to mechanize these arguments, which will make it possible to verify them rigorously and thus to settle this in a more reliable way.

=== Provability logics with many modalities

A

=== Interpretability Logic

C
