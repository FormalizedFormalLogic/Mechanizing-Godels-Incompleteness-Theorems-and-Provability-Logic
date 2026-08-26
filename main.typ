#import "init.typ": *
#import "notations.typ": *

#show: thmrules
#show: init.with(
  title: [Mechanizing Gödel's Incompleteness Theorems and Provability Logic],
  authors: (
    author(
      "Shogo Saito",
      insts: institute(
        "Tohoku University",
        addr: "Sendai, Japan",
        email: "saito.shogo.q8@dc.tohoku.ac.jp",
      ),
    ),
    author(
      "Mashu Noguchi",
      insts: institute(
        "Kobe University",
        addr: "Kobe, Japan",
        email: "me@sno2wman.net",
      ),
      oicd: "0009-0000-8653-3403",
    ),
  ),
  abstract: [
    We mechanized proofs of Gödel's first and second incompleteness theorems,
    Solovay's arithmetical completeness theorem for $LogicGL$, and related results in the Lean 4 theorem prover.
  ],
  keywords: (
    "incompleteness theorems",
    "provability logic",
    "formalization of mathematics",
    "Lean",
  ),
)

#remark[
  Since the word "formalize" is used in two different senses, which may cause confusion, we strictly distinguish between the words _formalize_ and _mechanize_.

  / _formalize_: the formalization of mathematics as a technique in the context of mathematical logic and metamathematics.
  / _mechanize_: the formalization of mathematics in an interactive theorem prover, verifiable on an actual computer.

  Following this convention, what we have done can be stated succinctly: _mechanizing formalized mathematics_.
]

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

On the other hand, recently, there has been much active work on mechanizing mathematics using interactive theorem provers, guaranteeing the validity of existing and new results, and providing AI/LLM-assisted or automated proving.
There are many well-known interactive theorem provers such as Rocq @RocqProver, Isabelle @Isabelle, HOL Light @HOLLight @HOLLightTutorial, Agda @Agda, and Lean @dMU21, and mathematics has been mechanized in each of them, including in the field of mathematical logic#footnote[Some of these mechanizations are summarized in @AwesomeLogicFormalization.].
In particular, for mechanizing Gödel's incompleteness theorems, this line of work began with Shankar in 1986 @Sha86 @Sha97, and continues with O'Connor @OCo05 @OCo09, Harrison @Har06, Paulson @Pau15, and Popescu and Traytel @PT19 @PT21, Kirst and Peters @KP23.
As for provability logic, modal-logical properties of #LogicGL, such as its semantical completeness and automated solvers, have been mechanized by Harrison @HOLLightTutorial[Chapter 20]#footnote[We don't know when Harrison's mechanization of modal logic was carried out.], Goré and Kelly @GK07, Goré, Ramanayake and Shillito @GRS21, Maggesi and Perini Brogi @MPB21 @MPB23, Gignoux @Gig26.
However, these are either abstract or not full mechanizations within arithmetic.
For instance, O'Connor's implementation assumes several facts needed for the proof of G2 as axioms, and Paulson's mechanization of G2 uses hereditarily finite sets, not arithmetic.
To the best of our knowledge, no full formalization of the incompleteness theorems entirely within arithmetic is known, and consequently, no mechanization about provability logic has been reported.

In the present paper, we describe our mechanizations of Gödel's first and second incompleteness theorems and Solovay's arithmetical completeness theorem.
Our work is carried out in Lean 4, an interactive theorem prover, together with mathlib4 @Mathlib2020, its community-developed mathematics library.
Lean 4 is based on the Calculus of Inductive Constructions (CIC) @dMU21,
and features dependent types, quotient types, and support for noncomputable definitions, making it highly expressive.
In addition, its powerful metaprogramming infrastructure like aesop @LF23 enables efficient proof automation and extensibility.

Our mechanization is currently hosted as a repository on GitHub, and the version we refer to is #link(REPO_SOURCES.at("Foundation")).
In the present paper, we will briefly and informally introduce the mathematical facts without omitting the essentials, and show the code of our mechanization corresponding to those facts.
However, for the sake of readability, note that in some places we have modified the hosted code.
Moreover, owing to motivations other than the incompleteness theorems and provability logic that the present paper focuses on, some implementations are stated as more general definitions.
We add comments where we deem it necessary, but for the actual working (verified) code, refer to the repository.

=== Declaration of AI usage

In the interest of novelty and fairness, we declare here how AI/LLMs were used in our development.
Our mechanization of the incompleteness theorems and of Solovay's arithmetical completeness theorem was carried out between 2023 and 2025, and up to that point it contained no AI-generated code.
This can be verified from the following commits, at which each result first became `sorry`-free.
#footnote[The first two commits were made in #link("https://github.com/FormalizedFormalLogic/Arithmetization")[FormalizedFormalLogic/Arithmetization], later merged into Foundation as a subtree.]

#let commit-link(hash) = link("https://github.com/FormalizedFormalLogic/Foundation/commit/" + hash)[#raw(hash.slice(
  0,
  8,
))]
- Gödel's first incompleteness theorem: #commit-link("e9325d82f6e4284b8dca530c8f9719650d7a21cf") (2024/09/04).
- Gödel's second incompleteness theorem: #commit-link("2da7151e1da0ce40ae222fec1651756f8ee7acce") (2024/09/04).
- Solovay's arithmetical completeness theorem: #commit-link("4a34d75c074c7614a1f16661ac73fd0725263c32") (2025/04/06).

On the other hand, since June 2026, the second author has adopted AI/LLM-assisted _vibe coding_ in Lean for #link(REPO_SOURCES.at("ProvabilityLogic"))[FormalizedFormalLogic/ProvabilityLogic], using interactive coding agents such as Anthropic's Claude both for refactoring the code and for mechanizing the new results, namely the sequent calculi for modal logics and the classification theorem of provability logics.
We have verified that the main parts of the generated code do not rely on any device regarded as illegitimate for mechanizing mathematics in Lean, such as `sorry`, additional nontrivial axioms, or `native_decide`#footnote[Some parts still contain `sorry`s; they are isolated from the main results of this paper and do not compromise the validity of the mechanization. See @subsect:remaining_sorry_in_provlogic.].
In @subsect:vibe-formalizing, we give a brief report on how we carried out the writing and generation of mechanized proofs using AI/LLMs in this project.

*The authors take full responsibility for the final artifact, including its AI-generated code.*

#include "first-order-logic.typ"

= Provability Logic <sect:provability_logic>

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

In the present paper, we mainly characterize the logic #LogicGL in three ways: by a Gentzen-style sequent calculus, by Kripke semantics, and by a Hilbert-style proof system.
Although #LogicGL is usually defined in the Hilbert style, when proving the Kripke completeness, introducing a sequent calculus makes both the mathematical proofs and the implementation of the mechanization simpler.
Moreover, as applications, the interpolation theorem and the fixed point theorem can be derived easily via the sequent calculus (we will discuss this in @sect:application-of-sequent-calculus).
Hence, in our mechanization we first define the Gentzen-style sequent calculus, and eventually prove the equivalence of all these characterizations (@thm:GL_TFAE).

We first introduce the Gentzen-style sequent calculus.
Our sequent calculus for #LogicGL is due to Sambin and Valentini @SV82.

#definition[
  A _sequent_ $Gamma => Delta$ is a pair of finite sets of formulas.
  The sequent calculus $GentzenGL$ for #LogicGL consists of the following rules,
  where in the weakening rules (WL) and (WR) we assume $Gamma subset.eq Gamma'$ and $Delta subset.eq Delta'$ respectively. We write $GentzenGL proves Gamma => Delta$ if the sequent $Gamma => Delta$ is provable in $GentzenGL$.

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

  Moreover, the sequent calculus $GentzenWithCutGL$ is obtained from $GentzenGL$ by adding the following cut rule.

  #align(center, prooftree(rule(
    name: [(Cut)],
    $Gamma_1, Gamma_2 => Delta_1, Delta_2$,
    $Gamma_1 => A, Delta_1$,
    $A, Gamma_2 => Delta_2$,
  )))
]
#leancode(links: (
  ("ProvabilityLogic", "ProvabilityLogic/Gentzen/Sequent.lean"),
  ("ProvabilityLogic", "ProvabilityLogic/Gentzen/GL/Basic.lean"),
))[
  ```
  structure Sequent (α : Type u) where
    ant : FormulaFinset α
    suc : FormulaFinset α
  infix:50 " ⟹ " => Sequent.mk

  inductive LogicGL.ProofGentzen : Sequent α → Type u
  | axm (A) : ProofGentzen ({A} ⟹ {A})
  | botL : ProofGentzen ({⊥} ⟹ ∅)
  | wkL  {Γ Γ' Δ}  : ProofGentzen (Γ ⟹ Δ) → Γ ⊆ Γ' → ProofGentzen (Γ' ⟹ Δ)
  | wkR  {Γ Δ Δ'}  : ProofGentzen (Γ ⟹ Δ) → Δ ⊆ Δ' → ProofGentzen (Γ ⟹ Δ')
  | impL {Γ Δ A B} : ProofGentzen (Γ ⟹ (insert A Δ)) → ProofGentzen (insert B Γ ⟹ Δ) →
                     ProofGentzen ((insert (A 🡒 B) Γ) ⟹ Δ)
  | impR {Γ Δ A B} : ProofGentzen ((insert A Γ) ⟹ (insert B Δ)) →
                     ProofGentzen (Γ ⟹ (insert (A 🡒 B) Δ))
  | boxGL {Γ A} : ProofGentzen ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A}) → ProofGentzen (Γ.box ⟹ {□A})
  notation:120 "⊢ᵍ[GL]! " S:121 => LogicGL.ProofGentzen S

  abbrev LogicGL.ProvableGentzen (S : Sequent α) : Prop := Nonempty (⊢ᵍ[GL]! S)
  notation:120 "⊢ᵍ[GL] " S:121 => LogicGL.ProvableGentzen S

  inductive LogicGL.GentzenWithCutProof : Sequent α → Type u
  | ...
  | cut {Γ₁ Γ₂ Δ₁ Δ₂ A} : GentzenWithCutProof (Γ₁ ⟹ insert A Δ₁) → GentzenWithCutProof (insert A Γ₂ ⟹ Δ₂) →
                          GentzenWithCutProof (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂)
  notation:120 "⊢ᵍᶜ[GL]! " S:121 => LogicGL.GentzenWithCutProof S

  abbrev LogicGL.GentzenWithCutProvable (S : Sequent α) : Prop := Nonempty (⊢ᵍᶜ[GL]! S)
  notation:120 "⊢ᵍᶜ[GL] " S:121 => LogicGL.GentzenWithCutProvable S
  ```
]

Note that $GentzenGL$ itself contains no cut rule.
The cut-elimination theorem for $GentzenWithCutGL$ is also mechanized.

#theorem[Cut elimination for $GentzenGL$ @SV82 @Avr84][
  If $GentzenWithCutGL proves Gamma => Delta$, then $GentzenGL proves Gamma => Delta$.
] <thm:GL_cut_elimination>
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Gentzen/GL/Kripke.lean"),))[
  ```
  theorem LogicGL.ProvableGentzen.of_with_cut {S : Sequent α} : ⊢ᵍᶜ[GL] S → ⊢ᵍ[GL] S
  ```
]

Here we note that this cut-elimination theorem is mechanized as a semantical cut elimination, via the Kripke semantics explained below.
In other words, we do not present a deterministic/computable/syntactic cut-elimination algorithm (`def cutEliminationAlgorithm : ⊢ᵍᶜ[GL]! S → ⊢ᵍ[GL]! S`), such as the ones repeatedly discussed in @SV82 @GR12.
For the purpose of our mechanization, the cut rule is introduced to show the equivalence with the Hilbert-style system, i.e., for modus ponens, and it suffices that it can be eliminated; hence we put off a rigorous mechanization of such an algorithm.
For a syntactic cut-elimination algorithm for the sequent calculus of $LogicGL$, see, e.g., the mechanization in Rocq by Goré, Ramanayake, and Shillito @GRS21.

Next, we introduce Kripke semantics.
Since we are not concerned with modal logic in general, we omit the notion of frames and work only with models.

#definition[
  Let $W$ be a nonempty set, whose elements are called _worlds_ or _points_.
  A _Kripke model_ is a triple $M = chevron.l W, R, V chevron.r$, where $R subset.eq W times W$ (the _accessibility relation_) and $V colon W -> Prop -> 2$ (the _valuation_).
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
    An advantage of taking the model `M` as an explicit argument of the forcing relation, as in `x ⊩[M] A`, is that the type of `x` (namely `M.World`) can be inferred from the notation.
    Conversely, if `x` is already inferred to be a world of `M`, then `M` is determined by unification, and hence can be omitted as in `x ⊩[_] A`.
  ],
)[
  ```
  structure Model (κ : Type u) [Nonempty κ] (α : Type v) where
    Rel' : κ → κ → Prop
    Val' : κ → α → Prop

  def Model.World.Forces (M : Model κ α) (x : M.World) : Formula α → Prop
  | #a    => M x a
  | ⊥     => False
  | A 🡒 B => Forces M x A → Forces M x B
  | □A    => ∀ y, x ≺ y → Forces M y A
  notation:55 x:56 " ⊩[" M "] " A:56 => Model.World.Forces M x A

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
  We write $HilbertGL proves A$ if $A$ is provable in $HilbertGL$, and define the logic $LogicGL := { A : HilbertGL proves A }$.

  1. Tautologies of classical propositional logic (cf. @CZ97)
  2. Axiom $AxiomK$: $Box(A limp B) limp (Box A limp Box B)$
  3. Axiom $Axiom("4")$: $Box A limp Box Box A$
  4. Axiom $AxiomL$: $Box(Box A limp A) limp Box A$
  5. Inference rules: modus ponens (MP) and the necessitation rule (Nec).
]
#leancode(
  links: (
    ("ProvabilityLogic", "ProvabilityLogic/Hilbert/GL/Basic.lean"),
    ("ProvabilityLogic", "ProvabilityLogic/Logic/GL/Basic.lean"),
  ),
  note: [
    Łukasiewicz's three axioms would suffice to prove all tautologies of classical propositional logic, but then the axioms listed here would have to be proved syntactically, which is extremely tedious; so we adopt all of them as axioms.
    Axiom $Axiom("4")$ is syntactically derivable from the others (cf. @Boo94[Chapter 1, Theorem 18]), but its proof is a tedious puzzle, so our mechanization adopts it as an axiom.
  ],
)[
  ```
  inductive LogicGL.ProofHilbert : Formula α → Type u
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
  notation:50 "⊢ʰ[GL]! " A:51 => LogicGL.ProofHilbert A

  abbrev LogicGL.ProvableHilbert (A : Formula α) := Nonempty (⊢ʰ[GL]! A)
  notation:50 "⊢ʰ[GL] " A:51 => LogicGL.ProvableHilbert A

  abbrev LogicGL {α} : Logic α := { A | ⊢ʰ[GL] A }
  ```
]

As the equivalence of these characterizations, we mechanized the following.

#theorem[Characterization of #LogicGL][
  The following are equivalent.

  1. $LogicGL proves A$.
  2. $HilbertGL proves A$.
  3. $GentzenGL proves => A$.
  4. $GentzenWithCutGL proves => A$.
  5. $=> 0 : A$ is provable in the labelled sequent calculus (see @sect:labelled-sequent-calculus).
  6. $A$ is forced at every point of every finite $LogicGL$-model.
  7. $A$ is forced at the root of every rooted finite $LogicGL$-model.
  8. $A$ is forced at the root of every rooted finite $LogicGL$-model that is a tree.
  9. $A$ is forced at every point of every finite $LogicGL$-model whose set of points is ${0, 1, dots.c, n - 1}$ for any $n >= 1$.
  10. $A$ is forced at the root of every rooted finite $LogicGL$-model whose set of points is ${0, 1, dots.c, n - 1}$ for any $n >= 1$.
] <thm:GL_TFAE>
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Logic/GL/Basic.lean"),))[
  ```
  theorem LogicGL.provability_TFAE {α : Type u} [DecidableEq α] {A : Formula α} : [
    A ∈ LogicGL,
    ⊢ʰ[GL] A,
    ⊢ᵍ[GL] (∅ ⟹ {A}),
    ⊢ᵍᶜ[GL] (∅ ⟹ {A}),
    ⊢ˡᵍ[GL] (∅ ⸴ ∅ ⟹ˡ {(0 : Label) ∶ A}),
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGL] → M.root.1 ⊩[_] A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLTree] → M.root.1 ⊩[_] A,
    ∀ (n : ℕ) [NeZero n] (M : Model (Fin n) α), [M.IsFiniteGL] → M ⊧ A,
    ∀ (n : ℕ) [NeZero n] (M : RootedModel (Fin n) α), [M.IsFiniteGL] → M.root.1 ⊩[_] A
  ].TFAE
  ```
]

Here are a few remarks.
The Kripke completeness of $LogicGL$ (the equivalence of 1 and 6) is due to Segerberg @Seg71.
This is the usual Kripke completeness with respect to the class of finite $LogicGL$-models, and has already been mechanized in HOL Light by Maggesi and Perini Brogi @MPB21 @MPB23.
However, the proof of the arithmetical completeness theorem described later requires not the mere Kripke completeness, but the completeness with respect to rooted models (7, and furthermore 8).
The transformation of a rooted model into a tree model is done by the technique known as tree unraveling (cf. @CZ97[Theorem 3.18]).
The equivalence of 3 and 4 is the special case of the cut-elimination theorem (@thm:GL_cut_elimination) for sequents of the form $=> A$.
The equivalence with 9 and 10 is provided for the sake of _concrete_ (or useful) countermodels.
Due to universe issues, the models in the completeness clauses range over types `κ` in the same universe level as the one that `α` belongs to.
Hence, to construct a countermodel, one would have to define it over a type lifted to the matching universe level, such as `PUnit` or `PLift (Fin n)` #footnote[https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#PLift].
However, dealing with such universe issues every time is quite tedious.
Thus we prepared some lemmas that internally dispose of the universe issues via a suitable type equivalence, so that countermodels can be constructed concretely over `Fin n`.

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
We omit the details of these constructions.

Both logics also admit Gentzen-style sequent calculi, but in the calculi, sequents have levels.
Kushida @Kus20 gave such a calculus for $LogicS$ with two levels of sequents, and Kashima et al. @KKIM25 extended his approach to a calculus for $LogicD$ with three levels.

#definition[Sequent calculi for $LogicS$ and $LogicD$ @Kus20 @KK23 @KKIM25][
  A _layered sequent_ is a sequent $Gamma => Delta$ together with a level.
  The calculus $GentzenS$ uses the two levels $seq1$ and $seq2$, and the calculus $GentzenD$ uses the three levels $seq1$, $seq2$, and $seq3$.
  At each level $l$ separately, both systems contain the propositional rules (Ax), ($bot$L), (WL), (WR), ($limp$L), and ($limp$R) of $GentzenGL$, with $=>$ replaced by $seq(l)$.
  In addition, both systems contain the following rules, except that (Lift$""^2_3$) belongs to $GentzenD$ only.

  #align(center, grid(
    columns: 2,
    column-gutter: 4em,
    row-gutter: 2em,
    prooftree(rule(
      name: [($Box_LogicGL$)],
      $Box Gamma seq1 Box A$,
      $Box A, Gamma, Box Gamma seq1 A$,
    )),
    prooftree(rule(name: [(Lift$""^1_2$)], $Gamma seq2 Delta$, $Gamma seq1 Delta$)),

    prooftree(rule(name: [($Box$L)], $Box A, Gamma seq2 Delta$, $A, Gamma seq2 Delta$)),
    prooftree(rule(
      name: [(Lift$""^2_3$)],
      $Box Gamma seq3 Box Delta$,
      $Box Gamma seq2 Box Delta$,
    )),
  ))

  Neither system contains a cut rule; $GentzenWithCutS$ and $GentzenWithCutD$ denote the systems extended with the cut rule, which is level-preserving.
] <def:layered_sequent_calculi>
#leancode(
  links: (
    ("ProvabilityLogic", "ProvabilityLogic/Gentzen/Sequent.lean"),
    ("ProvabilityLogic", "ProvabilityLogic/Gentzen/S/Basic.lean"),
    ("ProvabilityLogic", "ProvabilityLogic/Gentzen/D/Basic.lean"),
  ),
  note: [
    Levels are implemented as elements of `Fin 2` and `Fin 3`, hence are numbered from $0$ in the mechanization: the levels $seq1$, $seq2$, and $seq3$ above correspond to `⟹[0]`, `⟹[1]`, and `⟹[2]` respectively.
  ],
)[
  ```
  structure TwoLayeredSequent (α : Type u) extends Sequent α where
    level : Fin 2
  notation:50 Γ:51 " ⟹[" l "] " Δ:51 => TwoLayeredSequent.mk (Γ ⟹ Δ) l

  inductive LogicS.ProofGentzen : TwoLayeredSequent α → Type u
  | ...
  | boxGL  {Γ A}   : ProofGentzen ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A}) →
                     ProofGentzen (Γ.box ⟹[0] {□A})
  | liftUp {Γ Δ}   : ProofGentzen (Γ ⟹[0] Δ) → ProofGentzen (Γ ⟹[1] Δ)
  | boxL   {Γ Δ A} : ProofGentzen (insert A Γ ⟹[1] Δ) →
                     ProofGentzen (insert (□A) Γ ⟹[1] Δ)
  scoped prefix:120 "⊢ᵍ[S]! " => LogicS.ProofGentzen

  abbrev LogicS.ProvableGentzen (S : TwoLayeredSequent α) : Prop := Nonempty (⊢ᵍ[S]! S)
  scoped prefix:120 "⊢ᵍ[S] " => LogicS.ProvableGentzen

  structure ThreeLayeredSequent (α : Type u) extends Sequent α where
    level : Fin 3
  notation:50 Γ:51 " ⟹[" l "] " Δ:51 => ThreeLayeredSequent.mk (Γ ⟹ Δ) l

  inductive LogicD.ProofGentzen : ThreeLayeredSequent α → Type u
  | ...
  | boxGL {Γ : FormulaFinset α} {A}   : ProofGentzen ((insert (□A) (Γ ∪ □Γ)) ⟹[0] {A}) →
                                        ProofGentzen (□Γ ⟹[0] {□A})
  | liftUp₀₁ {Γ Δ}                    : ProofGentzen (Γ ⟹[0] Δ) → ProofGentzen (Γ ⟹[1] Δ)
  | boxL {Γ Δ A}                      : ProofGentzen (insert A Γ ⟹[1] Δ) →
                                        ProofGentzen (insert (□A) Γ ⟹[1] Δ)
  | liftUp₁₂ {Γ Δ : FormulaFinset α}  : ProofGentzen (□Γ ⟹[1] □Δ) →
                                        ProofGentzen (□Γ ⟹[2] □Δ)
  scoped prefix:120 "⊢ᵍ[D]! " => LogicD.ProofGentzen

  abbrev LogicD.ProvableGentzen (S : ThreeLayeredSequent α) : Prop := Nonempty (⊢ᵍ[D]! S)
  scoped prefix:120 "⊢ᵍ[D] " => LogicD.ProvableGentzen
  ```
]

By construction, the $seq1$-fragment of both systems is exactly $GentzenGL$, and the $seq1$ and $seq2$ fragments of $GentzenD$ are exactly $GentzenS$; these embeddings are mechanized as well, and are what lets the mechanization of $GentzenD$ reuse that of $GentzenS$.

As for $GentzenGL$, we can prove the cut-elimination theorem semantically.

#theorem[Cut elimination for $GentzenS$ and $GentzenD$ @KK23 @KKIM25][
  - If $GentzenWithCutS proves Gamma seq2 Delta$, then $GentzenS proves Gamma seq2 Delta$.
  - If $GentzenWithCutD proves Gamma seq3 Delta$, then $GentzenD proves Gamma seq3 Delta$.
] <prop:SD_cut_elimination>
#leancode(links: (
  ("ProvabilityLogic", "ProvabilityLogic/Gentzen/S/Kripke.lean"),
  ("ProvabilityLogic", "ProvabilityLogic/Gentzen/D/Kripke.lean"),
))[
  ```
  theorem LogicS.ProvableGentzen.of_with_cut {Γ Δ : FormulaFinset α}
    (h : ⊢ᵍᶜ[S] (Γ ⟹[1] Δ)) : ⊢ᵍ[S] (Γ ⟹[1] Δ)

  theorem LogicD.ProvableGentzen.of_with_cut {Γ Δ : FormulaFinset α}
    (h : ⊢ᵍᶜ[D] (Γ ⟹[2] Δ)) : ⊢ᵍ[D] (Γ ⟹[2] Δ)
  ```
]

With this result, the characterizations of $LogicS$ and $LogicD$ can be stated as follows.
First, the following holds for $LogicS$.

#proposition[cf. @Vis84][
  The following are equivalent.

  1. $LogicS proves A$
  2. $GentzenS proves seq2 A$
  3. On the chain of the tail model constructed from any finite $LogicGL$-model and any point $t$ of it, $A$ is eventually always forced.
  4. $and.big_(Box B in subfml(A)) (Box B limp B) limp A$ is forced at the root of every rooted finite $LogicGL$-model.
  5. Same as 3, but for the finite $LogicGL$-models whose set of points is ${0, 1, dots.c, n - 1}$ for any $n >= 1$.
  6. $LogicGL proves and.big_(Box B in subfml(A)) (Box B limp B) limp A$
] <prop:S_characterization>
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Logic/S/Basic.lean"),))[
  ```
  theorem LogicS.provability_TFAE [DecidableEq α] : [
    A ∈ LogicS,
    ⊢ᵍ[S] (∅ ⟹[1] {A}),
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (tail : M.World),
      ∃ k : ℕ, ∀ n : ℕ, k ≤ n → toTail.chainPoint n ⊩[(M.toTail tail).toModel] A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      M.root.1 ⊩[_] (⋀A.subfmlsS 🡒 A),
    ∀ (n : ℕ) [NeZero n] (M : Model (Fin n) α), [M.IsFiniteGL] → ∀ (tail : M.World),
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m → toTail.chainPoint m ⊩[(M.toTail tail).toModel] A,
    (⋀A.subfmlsS 🡒 A) ∈ LogicGL
  ].TFAE
  ```
]

Using this equivalence, we can show the following fact about the formulas obtained by replacing every $Box$ with $Boxdot$.

#definition[Boxdot translation][
  The _boxdot translation_ $A^Boxdot$ of a formula $A$ is obtained by replacing every occurrence of $Box$ with $Boxdot$, i.e., it is defined recursively as follows.
  - $p^Boxdot = p$
  - $bot^Boxdot = bot$
  - $(A limp B)^Boxdot = A^Boxdot limp B^Boxdot$
  - $(Box A)^Boxdot = Boxdot (A^Boxdot)$
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Formula/Basic.lean"),))[
  ```
  def Formula.boxdotTranslate : Formula α → Formula α
    | #a    => #a
    | ⊥     => ⊥
    | A 🡒 B => (boxdotTranslate A) 🡒 (boxdotTranslate B)
    | □A    => ⊡(boxdotTranslate A)
  postfix:90 "ᵇ" => Formula.boxdotTranslate
  ```
]

#proposition[
  For every formula $A$, $LogicGL proves A^Boxdot$ if and only if $LogicS proves A^Boxdot$.
] <prop:boxdot_S_boxdot_GL>
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Logic/S/Boxdot.lean"),))[
  ```
  theorem LogicS.iff_provable_boxdot_GL_provable_boxdot_S [DecidableEq α] :
    (Aᵇ) ∈ LogicGL ↔ (Aᵇ) ∈ LogicS
  ```
]

The boxdot translation and the equivalence of $LogicGL$ and $LogicS$ on boxdot-translated formulas are also important in the connection with $LogicGrz$, which we discuss later in @sect:Grz.

Next, we turn to $LogicD$.

#proposition[cf. @Bek90 @KKIM25][
  The following are equivalent, where $prebox(X) = {B | Box B in X}$ for a set of formulas $X$.

  1. $LogicD proves A$
  2. $GentzenD proves seq3 A$
  3. $A$ is forced at the root of the pseudo tail model constructed from any finite $LogicGL$-model.
  4. $and.big_(Gamma subset.eq prebox(subfml(A))) (Box(or.big Box Gamma) limp or.big Box Gamma) limp A$ is forced at the root of every rooted finite $LogicGL$-model.
  5. Same as 3, but for the finite $LogicGL$-models whose set of points is ${0, 1, dots.c, n - 1}$ for any $n >= 1$.
  6. $LogicGL proves and.big_(Gamma subset.eq prebox(subfml(A))) (Box(or.big Box Gamma) limp or.big Box Gamma) limp A$
] <prop:D_characterization>
#leancode(links: (
  ("ProvabilityLogic", "ProvabilityLogic/Logic/D/Basic.lean"),
  ("ProvabilityLogic", "ProvabilityLogic/Gentzen/D/Kripke.lean"),
))[
  ```
  theorem LogicD.provability_TFAE [DecidableEq α] : [
    A ∈ LogicD,
    ⊢ᵍ[D] (∅ ⟹[2] {A}),
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ r o,
      (M.toPseudoTail r o).root.1 ⊩[_] A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      M.root.1 ⊩[_] (⋀A.subfmlsD 🡒 A),
    ∀ (n : ℕ) [NeZero n] (M : Model (Fin n) α), [M.IsFiniteGL] → ∀ r o,
      (M.toPseudoTail r o).root.1 ⊩[_] A,
    (⋀A.subfmlsD 🡒 A) ∈ LogicGL
  ].TFAE
  ```
]

The inclusions $LogicGL subset.eq LogicD subset.eq LogicS$ hold trivially by definition.
Moreover, constructing countermodels via the semantics shows that these inclusions are proper.

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
  ("ProvabilityLogic", "ProvabilityLogic/Gentzen/GL/Maehara.lean"),
))[
  ```
  theorem LogicGL.CIP (h : (A 🡒 B) ∈ LogicGL) :
    ∃ C : Formula α, (A 🡒 C) ∈ LogicGL ∧ (C 🡒 B) ∈ LogicGL ∧ C.atoms ⊆ A.atoms ∩ B.atoms
  ```
]

// TODO: 不動点定理を de Jongh と Sambin に帰属させるべきかは要事実確認
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
  Moreover, such a fixed point is unique up to provable equivalence: for any formula $E$ such that $LogicGL proves A[p := E] <-> E$, we have $LogicGL proves D <-> E$.
] <thm:GL_fixpoint>
#leancode(
  links: (("ProvabilityLogic", "ProvabilityLogic/Logic/GL/Fixedpoint.lean"),),
  note: [
    The fresh propositional variable `q` serves only as a placeholder in the construction of the fixed point.
  ],
)[
  ```
  theorem LogicGL.fixpointTheorem
    (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    ∃ D : Formula α, D.atoms ⊆ A.atoms \ {p} ∧ ((A⟦p ↦ D⟧) 🡘 D) ∈ LogicGL ∧
      ∀ E : Formula α, ((A⟦p ↦ E⟧) 🡘 E) ∈ LogicGL → (D 🡘 E) ∈ LogicGL
  ```
]

The fixed point theorem of #LogicGL has also been mechanized in Lean, by Gignoux @Gig26.
We note that, whereas Gignoux's mechanization proves it by a semantical method, in our mechanization the interpolants and the fixed points can be computed constructively inside Lean from derivation trees of the sequent calculus.
However, at present derivation trees of the sequent calculus cannot be constructed automatically by proof search or the like, so concrete derivation trees have to be input by hand. Also, when $LogicGL proves A$ is proved non-constructively, e.g., via Kripke semantics, the interpolants and the fixed points are of course not computable in Lean.

Finally, we have also mechanized facts on the CIP of $LogicS$ and $LogicD$, which we briefly mention.

#theorem[@Bek87 @Bek89][
  $LogicS$ has CIP. But $LogicD$ does not.
]
#leancode(links: (
  ("ProvabilityLogic", "ProvabilityLogic/Logic/S/CIP.lean"),
  ("ProvabilityLogic", "ProvabilityLogic/Logic/D/NotCIP.lean"),
))[
  ```
  theorem LogicS.CIP (h : (A 🡒 B) ∈ LogicS) :
    ∃ C : Formula α, (A 🡒 C) ∈ LogicS ∧ (C 🡒 B) ∈ LogicS ∧ C.atoms ⊆ A.atoms ∩ B.atoms

  theorem LogicD.notCIP {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
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
However, Maggesi and Perini Brogi's mechanization has practical utility: although the termination is not guaranteed, it can actually be executed and used as a tactic, which automates simple proofs of #LogicGL appearing in their mechanization.
In contrast, due to the implementation constraints in the well-foundedness proof, our labelled sequent calculus cannot be used, e.g., as a Lean tactic, and its properties are mechanized purely as mathematical facts.
Hence, regarding the practical utility, Maggesi and Perini Brogi's mechanization has the advantage.

Moreover, we remark that interpolation for labelled sequent calculi in general is discussed, e.g., in @vdGJK26[Section 5], but whether it is possible for the labelled sequent calculus for #LogicGL seems to be open at present.
This suggests that labelled calculi are less suitable for mechanizing the properties of #LogicGL described in @sect:application-of-sequent-calculus.

== Arithmetical completeness theorems <sect:arithmetical_completeness>

In this section, we describe the main results of our mechanization of provability logic: the mechanization of Solovay's arithmetical completeness theorem @Sol76 and its generalization.

First, we define arithmetical interpretations, which translate modal formulas into arithmetical sentences.
In what follows, $T$ is an arithmetical theory with a $Delta_1$-definable axiomatization extending $Theory("I")Sigma_1$.
Moreover, $Bew$ denotes a provability in the sense of @subsect:provability_abstraction.
Although the definition allows $Bew$ to be arbitrary, we mainly consider the standard provability $Bew_T$ of $T$.

#definition[
  A map $f colon Prop -> upright("Sent")_upright("A")$, where $upright("Sent")_upright("A")$ denotes the set of arithmetical sentences, is called an _arithmetical realization_ (or simply a _realization_).
  Given a realization $f$ and a provability $Bew$, the _arithmetical interpretation_ of $A$ by $Bew$, denoted $f_Bew (A)$, is the extension of $f$ translating each modal formula $A$ into an arithmetical sentence as follows.

  - $f_Bew (p) & = f(p)$
  - $f_Bew (bot) & = bot$
  - $f_Bew (A limp B) & = f_Bew (A) limp f_Bew (B)$
  - $f_Bew (Box A) & = Bew (f_Bew (A))$

  In particular, the interpretation $f_(Bew_T) (A)$ by $Bew_T$ is called the _standard interpretation_ of $A$ and is written $f_T (A)$.
] <def:arithmetical_interpretation>
#leancode(
  links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/Interpret.lean"),),
  note: [
    The interpretation `A.interpret f 𝔅` corresponds to $f_Bew (A)$.
    By the coercion, the standard interpretation `A.standardInterpret f T` can be written as `f T A`, which corresponds to $f_T (A)$.
  ],
)[
  ```
  structure Realization (α : Type*) (L : FirstOrder.Language) where
    val : α → FirstOrder.Sentence L

  def Formula.interpret (f : Realization α L) {T₀ T : FirstOrder.Theory L} (𝔅 : Provability T₀ T) :
    Formula α → FirstOrder.Sentence L
    | #a    => f.val a
    | ⊥     => ⊥
    | A 🡒 B => (A.interpret f 𝔅) 🡒 (B.interpret f 𝔅)
    | □A    => 𝔅 (A.interpret f 𝔅)

  noncomputable abbrev Formula.standardInterpret (f : Realization α _)
    (T : FirstOrder.ArithmeticTheory) [T.Δ₁] := Formula.interpret f T.standardProvability

  noncomputable instance : CoeFun (Realization α ℒₒᵣ)
    (fun _ ↦ (T : FirstOrder.ArithmeticTheory) → [T.Δ₁] → Formula α → FirstOrder.Sentence ℒₒᵣ) :=
    ⟨Formula.standardInterpret⟩
  ```
]

#definition[
  The _(standard) provability logic of $T$ relative to $U$_, written $ProvLogic(T, U)$, is defined as follows.
  $
    ProvLogic(T, U) = { A | #text[$U proves f_(Bew_T) (A)$ for every realization $f$] }
  $
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/Interpret.lean"),))[
  ```
  def LO.FirstOrder.ArithmeticTheory.provabilityLogicRelativeTo
    (T U : FirstOrder.ArithmeticTheory) [T.Δ₁] : Logic α :=
    {A | ∀ f : Realization α ℒₒᵣ, U ⊢ f T A}

  abbrev LO.FirstOrder.ArithmeticTheory.provabilityLogic
    (T : FirstOrder.ArithmeticTheory) [T.Δ₁] : Logic α := T.provabilityLogicRelativeTo T
  ```
]

Solovay's arithmetical completeness theorem states that the behavior of the standard provability predicate, viewed as a modal operator, is captured exactly by the modal logic #LogicGL.
That is, for appropriate choices of $T$ and $U$, the provability logic $ProvLogic(T, U)$ coincides with #LogicGL.
Here we present the generalized version (@thm:arithmetical_completeness) using the notion of the _height_ of a theory due to Visser @Vis81.

#definition[Height of a theory][
  For $n >= 0$, $Bew^n$ denotes the $n$-fold iteration of the provability $Bew$ (where $Bew^0 sigma equiv sigma$).
  The _height_ $height(T) <= omega$ of a theory $T$ is the least $n in omega$ such that $T proves Bew_T^n bot$; if no such $n$ exists, we set $height(T) = omega$.
]
#leancode(
  links: (("Foundation", "Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Height.lean"),),
)[
  ```
  noncomputable def Provability.height (𝔅 : Provability T₀ T) : ENat := ENat.find (T ⊢ 𝔅^[·] ⊥)

  noncomputable abbrev ArithmeticTheory.height (T : ArithmeticTheory) [T.Δ₁] : ℕ∞ :=
    T.standardProvability.height
  ```
]

Note that if $T$ is $Sigma_1$-sound, then $T nproves Bew_T^n bot$ for every $n in omega$, and hence $height(T) = omega$.

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
  lemma LogicGLPlusBoxBot.eq_provabilityLogic :
    LogicGLPlusBoxBot (α := α) T.height = T.provabilityLogic
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
  theorem LogicGL.eq_provabilityLogic_sigma1_sound [T.SoundOnHierarchy 𝚺 1] :
    @LogicGL α = T.provabilityLogic

  theorem LogicGL.eq_provabilityLogic_peano_arithmetic : @LogicGL α = (𝗣𝗔.provabilityLogic)
  ```
]

Furthermore, Solovay also proved that #LogicS is arithmetically complete with respect to the true arithmetic #TrueArithmetic.
The reduction of $LogicS$ to $LogicGL$ stated in @prop:S_characterization is essentially used in this proof.

#theorem[Solovay's (second) arithmetical completeness theorem @Sol76][
  Let $T$ be a sound theory.
  For every formula $A$, $LogicS proves A$ if and only if $NN models f_(Bew_T) (A)$ for every realization $f$.
  That is, $ProvLogic(T, TrueArithmetic) = LogicS$.
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/S/Basic.lean"),))[
  ```
  theorem LogicS.arithmetical_completeness_iff [DecidableEq α] :
    A ∈ LogicS ↔ (∀ f : Realization α ℒₒᵣ, ℕ↓[ℒₒᵣ] ⊧ f T A)

  theorem LogicS.eq_provabilityLogicRelativeTo_TA [DecidableEq α] :
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
    (M.height = n ∧ M.root.1 ⊮[_] A) }

  abbrev Logic.trace (L : Logic α) : Set ℕ := ⋃ A ∈ L, A.trace
  ```
]

#definition[
  For $n in omega$, define the formula $F_n := Box^(n+1) bot limp Box^n bot$.
  For $alpha subset.eq omega$ and cofinite $beta subset.eq omega$, we define the following non-normal modal logics.
  - $LogicGLAlpha(alpha) := sumQuasiNormal(LogicGL, { F_n : n in alpha })$
  - $LogicGLBetaMinus(beta) := sumQuasiNormal(LogicGL, { lnot and.big_(n in omega without beta) F_n })$

  In particular, we call $LogicGLAlpha(omega)$ simply $LogicA$#footnote[We follow the naming of @JdJ98; it presumably stands for Artemov.].
]
#leancode(
  note: [
    Since $F_n$ is hard to use as an identifier, the mechanization names $F_n$ as `TBB` (axiom $Axiom("T")$ for Box Bot).
  ],
  links: (
    ("ProvabilityLogic", "ProvabilityLogic/Formula/Basic.lean"),
    ("ProvabilityLogic", "ProvabilityLogic/Logic/GLAlpha/Basic.lean"),
    ("ProvabilityLogic", "ProvabilityLogic/Logic/A/Basic.lean"),
    ("ProvabilityLogic", "ProvabilityLogic/Logic/GLBetaMinus/Basic.lean"),
  ),
)[
  ```
  def TBB (n : ℕ) : Formula α := (□^[(n + 1)]⊥) 🡒 (□^[n]⊥)

  abbrev LogicGLAlpha {α} (X : Set ℕ) : Logic α := (@LogicGL α) +ᴸ ↑(X.image $ TBB (α := Empty))

  abbrev LogicA {α} : Logic α := LogicGLAlpha Set.univ

  noncomputable abbrev TBBMinus [DecidableEq α] (X : Set ℕ) (X_finite : X.Finite) : Formula α :=
    ∼⋀(X_finite.toFinset.image TBB)

  abbrev LogicGLBetaMinus {α} [DecidableEq α] (X : Set ℕ) (X_cofinite : Xᶜ.Finite) : Logic α :=
    (@LogicGL α) +ᴸ (LetterlessFormulaSet.lift { TBBMinus _ X_cofinite })
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

=== On some remaining `sorry`s <subsect:remaining_sorry_in_provlogic>

Although the mechanization of the classification theorem itself does not depend on them, the mechanizations of some facts of provability logic still contain `sorry`s.
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
  For every $Sigma_1$-sound theory $T$, there exists a uniform realization $f$ such that
  for every formula $A$, $LogicGL proves A$ if and only if $T proves f_(Bew_T) (A)$.
]

== On $LogicGrz$ <sect:Grz>

The Grzegorczyk logic $LogicGrz$ is also closely related to #LogicGL.
Unlike #LogicGL, it is an extension of $LogicS4$, so that $Box$ behaves reflexively; nevertheless, as we describe below, it is tightly connected to #LogicGL and #LogicS through the boxdot translation, and this connection yields an arithmetical completeness theorem for $LogicGrz$ with respect to a _strong_ arithmetical interpretation.

We first introduce the Hilbert-style proof system, which is the usual definition of $LogicGrz$.

#definition[
  The Hilbert-style proof system $HilbertGrz$ for $LogicGrz$ is obtained from $HilbertGL$ by replacing the axiom $AxiomL$ with the following two axioms.

  1. Axiom $AxiomT$: $Box A limp A$
  2. Axiom $AxiomGrz$: $Box(Box(A limp Box A) limp A) limp A$

  As for #LogicGL, we define the logic $LogicGrz := { A | HilbertGrz proves A }$.
]
#leancode(
  links: (
    ("ProvabilityLogic", "ProvabilityLogic/Hilbert/Grz/Basic.lean"),
    ("ProvabilityLogic", "ProvabilityLogic/Logic/Grz/Basic.lean"),
  ),
  note: [
    As in $HilbertGL$, the propositional part is taken axiomatically, and the axiom $Axiom("4")$ is adopted as an axiom although it is derivable from $AxiomT$ and $AxiomGrz$.
  ],
)[
  ```
  inductive LogicGrz.ProofHilbert : Formula α → Type u
  | ...
  | modalK   {A B} : ProofHilbert $ □(A 🡒 B) 🡒 (□A 🡒 □B)
  | modal4   {A}   : ProofHilbert $ □A 🡒 □□A
  | modalT   {A}   : ProofHilbert $ □A 🡒 A
  | modalGrz {A}   : ProofHilbert $ □(□(A 🡒 □A) 🡒 A) 🡒 A
  | mdp      {A B} : ProofHilbert (A 🡒 B) → ProofHilbert A → ProofHilbert B
  | nec      {A}   : ProofHilbert A → ProofHilbert (□A)
  notation:50 "⊢ʰ[Grz]! " A:51 => LogicGrz.ProofHilbert A

  abbrev LogicGrz.ProvableHilbert (A : Formula α) := Nonempty (⊢ʰ[Grz]! A)
  notation:50 "⊢ʰ[Grz] " A:51 => LogicGrz.ProvableHilbert A

  abbrev LogicGrz {α} : Logic α := { A | ⊢ʰ[Grz] A }
  ```
]

Next we introduce the Kripke semantics.

#definition[$LogicGrz$-model][
  Let $R$ be a binary relation on $W$, and let $R^(eq.not) = { (x, y) | x R y "and" x != y }$ be the irreflexivization of $R$.
  $R$ is _weakly converse well-founded_ if $R^(eq.not)$ is conversely well-founded.
  If $R$ is transitive, this is equivalent to saying that $R$ admits no infinite ascending chain $x_0 R x_1 R dots.c$ consisting of pairwise distinct points.

  Using this notion, we define the following.
  - A model is a _$LogicGrz$-model_ if $R$ is reflexive, transitive, and weakly converse well-founded.
  - A finite model whose $R$ is reflexive, transitive, and antisymmetric (i.e., a finite partial order) is called a _finite $LogicGrz$-model_.
  We note that every finite $LogicGrz$-model is a $LogicGrz$-model.
]
#leancode(links: (
  ("ProvabilityLogic", "ProvabilityLogic/ToFoundation/Vorspiel/Rel/WCWF.lean"),
  ("ProvabilityLogic", "ProvabilityLogic/Kripke/Basic.lean"),
))[
  ```
  def Rel.IrreflGen (r : Rel α α) : Rel α α := fun x y => r x y ∧ x ≠ y

  abbrev WeaklyConverseWellFounded {α} (rel : Rel α α) := ConverseWellFounded rel.IrreflGen

  class IsWeaklyConverseWellFounded (α) (rel : Rel α α) : Prop where
    wcwf : WeaklyConverseWellFounded rel

  class Model.IsGrz (M : Model κ α) extends
    Std.Refl M.Rel, IsTrans _ M.Rel, IsWeaklyConverseWellFounded _ M.Rel

  class Model.IsFiniteGrz (M : Model κ α) extends
      Std.Refl M.Rel, IsTrans _ M.Rel, Std.Antisymm M.Rel where
    [finite : Finite M.World]

  instance [M.IsFiniteGrz] : M.IsGrz
  ```
]

Finally we introduce the sequent calculus.
Sequent calculi for $LogicGrz$ were formulated by Avron @Avr84 and by Borga and Gentilini @BG86; the former gives a semantic cut elimination, the latter a syntactic one.

#definition[
  The sequent calculus $GentzenGrz$ for $LogicGrz$ is obtained from $GentzenGL$ by replacing the rule $(Box_LogicGL)$ with the following two rules.

  #align(center, grid(
    columns: 2,
    column-gutter: 4em,
    prooftree(rule(name: [($Box$T)], $Box B, Gamma => Delta$, $B, Gamma => Delta$)),
    prooftree(rule(
      name: [($Box_LogicGrz$)],
      $Box Gamma => Box A$,
      $Box(A limp Box A), Box Gamma => A$,
    )),
  ))

  As for $GentzenGL$, this system contains no cut rule, and $GentzenWithCutGrz$ denotes the system extended with the cut rule.
]
#leancode(
  links: (("ProvabilityLogic", "ProvabilityLogic/Gentzen/Grz/Basic.lean"),),
  note: [
    In @Avr84, the rule $(Box_LogicGrz)$ carries arbitrary side formulas.
    As with $(Box_LogicGL)$, we adopt the more economical presentation in which the conclusion is exactly $Box Gamma => Box A$, and recover the side formulas afterwards by the weakening rules.
  ],
)[
  ```
  inductive LogicGrz.ProofGentzen : Sequent α → Type u
  | ...
  | boxT   {Γ Δ : FormulaFinset α} {B} :
      ProofGentzen (insert B Γ ⟹ Δ) → ProofGentzen (insert (□B) Γ ⟹ Δ)
  | boxGrz {Γ : FormulaFinset α} {A}   :
      ProofGentzen (insert (□(A 🡒 □A)) (□Γ) ⟹ {A}) → ProofGentzen (□Γ ⟹ {□A})
  notation:120 "⊢ᵍ[Grz]! " S:121 => LogicGrz.ProofGentzen S

  abbrev LogicGrz.ProvableGentzen (S : Sequent α) : Prop := Nonempty (⊢ᵍ[Grz]! S)
  notation:120 "⊢ᵍ[Grz] " S:121 => LogicGrz.ProvableGentzen S

  inductive LogicGrz.GentzenWithCutProof : Sequent α → Type u
  | ...
  | cut {Γ₁ Γ₂ Δ₁ Δ₂ A} :
      GentzenWithCutProof (Γ₁ ⟹ insert A Δ₁) → GentzenWithCutProof (insert A Γ₂ ⟹ Δ₂) →
      GentzenWithCutProof (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂)
  notation:120 "⊢ᵍᶜ[Grz]! " S:121 => LogicGrz.GentzenWithCutProof S

  abbrev LogicGrz.GentzenWithCutProvable (S : Sequent α) : Prop := Nonempty (⊢ᵍᶜ[Grz]! S)
  notation:120 "⊢ᵍᶜ[Grz] " S:121 => LogicGrz.GentzenWithCutProvable S
  ```
]

We mechanized the finite model property of $LogicGrz$ with respect to the Kripke semantics, and as its corollaries we mechanized the cut elimination for $GentzenGrz$ and its equivalence with the Hilbert-style system.

#theorem[Characterization of $LogicGrz$][
  The following are equivalent.

  1. $LogicGrz proves A$.
  2. $HilbertGrz proves A$.
  3. $GentzenGrz proves => A$.
  4. $GentzenWithCutGrz proves => A$.
  5. $A$ is forced at every point of every finite $LogicGrz$-model.
  6. $A$ is forced at the root of every rooted finite $LogicGrz$-model.
] <thm:Grz_TFAE>
#leancode(links: (
  ("ProvabilityLogic", "ProvabilityLogic/Logic/Grz/Basic.lean"),
  ("ProvabilityLogic", "ProvabilityLogic/Gentzen/Grz/Kripke.lean"),
))[
  ```
  theorem LogicGrz.provability_TFAE [DecidableEq α] {A : Formula α} : [
    A ∈ LogicGrz,
    ⊢ʰ[Grz] A,
    ⊢ᵍ[Grz] (∅ ⟹ {A}),
    ⊢ᵍᶜ[Grz] (∅ ⟹ {A}),
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGrz] → M ⊧ A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGrz] → M.root.1 ⊩[_] A
  ].TFAE
  ```
]

Furthermore, $LogicGrz$ is related to #LogicGL and #LogicS through the boxdot translation as follows.

#theorem[
  For every formula $A$, the following hold.
  1. $LogicGrz proves A$ if and only if $LogicGL proves A^Boxdot$.
  2. $LogicGrz proves A$ if and only if $LogicS proves A^Boxdot$ (cf. @prop:boxdot_S_boxdot_GL).
] <thm:Grz_boxdot>
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Logic/Grz/Boxdot.lean"),))[
  ```
  theorem iff_provable_boxdot_GL_provable_Grz : Aᵇ ∈ LogicGL ↔ A ∈ LogicGrz

  theorem iff_provable_boxdot_S_provable_Grz : Aᵇ ∈ LogicS ↔ A ∈ LogicGrz
  ```
]

Using this fact, Goldblatt @Gol78 and Boolos @Boo80 showed that $LogicGrz$ is arithmetical complete with respect to the _strong_ arithmetical interpretation, in which $Box$ is read as "provable and true" rather than merely "provable".

#definition[Strong interpretation][
  Given a realization $f$ and a provability $Bew$, the _strong (arithmetical) interpretation_ $f^upright("s")_(Bew)(A)$ is defined exactly as the interpretation $f_(Bew)(A)$ of @def:arithmetical_interpretation except for the modal clause, which reads
  $
    f^upright("s")_(Bew) (Box A) = f^upright("s")_(Bew) (A) land Bew (f^upright("s")_(Bew) (A)).
  $
  Equivalently, $f^upright("s")_(Bew)(A)$ is $T$-provably equivalent to $f_(Bew)(A^Boxdot)$, and this is how the arithmetical completeness of $LogicGrz$ is reduced to that of #LogicGL and #LogicS.
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/StrongInterpret.lean"),))[
  ```
  def Formula.strongInterpret (f : Realization α L) {T₀ T : FirstOrder.Theory L}
    (𝔅 : Provability T₀ T) : Formula α → FirstOrder.Sentence L
    | #a    => f.val a
    | ⊥     => ⊥
    | A 🡒 B => (A.strongInterpret f 𝔅) 🡒 (B.strongInterpret f 𝔅)
    | □A    => (A.strongInterpret f 𝔅) ⋏ 𝔅 (A.strongInterpret f 𝔅)

  lemma Formula.iff_interpret_boxdot_strongInterpret [𝔅.HBL2] :
    T ⊢ (Aᵇ).interpret f 𝔅 ↔ T ⊢ A.strongInterpret f 𝔅

  lemma Formula.iff_models_interpret_boxdot_strongInterpret
    {M} [Nonempty M] [Structure L M] [M↓[L] ⊧* T] [𝔅.HBL2] [𝔅.SoundOn M] :
    M↓[L] ⊧ (Aᵇ).interpret f 𝔅 ↔ M↓[L] ⊧ A.strongInterpret f 𝔅
  ```
]

#theorem[Arithmetical completeness of $LogicGrz$ @Gol78 @Boo80][
  Let $T$ be a theory with $height(T) = omega$ (in particular, any $Sigma_1$-sound $T$).
  Then $LogicGrz proves A$ if and only if $T proves f^upright("s")_(Bew_T) (A)$ for every realization $f$.
  Moreover, if $T$ is sound, then $LogicGrz proves A$ if and only if $NN models f^upright("s")_(Bew_T) (A)$ for every realization $f$.
] <thm:Grz_arithmetical_completeness>
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/Grz/Basic.lean"),))[
  ```
  theorem LogicGrz.arithmetical_completeness_iff_of_infinity_height
    (height : T.height = (⊤ : ℕ∞)) [DecidableEq α] :
    A ∈ LogicGrz ↔ (∀ f : Realization α ℒₒᵣ, T ⊢ A.strongInterpret f T.standardProvability)

  theorem LogicGrz.arithmetical_completeness_iff_of_sigma1_sound
    [T.SoundOnHierarchy 𝚺 1] [DecidableEq α] :
    A ∈ LogicGrz ↔ (∀ f : Realization α ℒₒᵣ, T ⊢ A.strongInterpret f T.standardProvability)

  theorem LogicGrz.arithmetical_completeness_model_iff [DecidableEq α] :
    A ∈ LogicGrz ↔ (∀ f : Realization α ℒₒᵣ, ℕ↓[ℒₒᵣ] ⊧ A.strongInterpret f T.standardProvability)
  ```
]

== On $LogicGLPoint3$

A sequent calculus for $LogicGLPoint3$ was given by Valentini and Solitro @VS83 and Valentini @Val86.
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
  A finite $LogicGL$-model is called a _finite $LogicGLPoint3$-model_ when $prec$ is linear, i.e., $x prec y$ and $x prec z$ imply $y prec z$ or $y = z$ or $z prec y$.
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
  inductive LogicGLPoint3.ProofGentzen : Sequent α → Type u
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
  notation:120 "⊢ᵍ[GLPoint3]! " S:121 => LogicGLPoint3.ProofGentzen S

  abbrev LogicGLPoint3.ProvableGentzen (S : Sequent α) : Prop :=
    Nonempty (⊢ᵍ[GLPoint3]! S)
  notation:120 "⊢ᵍ[GLPoint3] " S:121 => LogicGLPoint3.ProvableGentzen S
  ```
]

For these characterizations, equivalences analogous to those for #LogicGL hold.

#theorem[@VS83][
  The following are equivalent.
  1. $LogicGLPoint3 proves A$.
  2. $GentzenGLPoint3 proves => A$.
  3. $A$ is forced at every point of every finite $LogicGLPoint3$-model.
  4. $A$ is forced at the root of every rooted finite $LogicGLPoint3$-model.
  5. $A$ is forced at every point of every finite $LogicGLPoint3$-model whose set of points is ${0, 1, dots.c, n - 1}$ for any $n >= 1$.
  6. $A$ is forced at the root of every rooted finite $LogicGLPoint3$-model whose set of points is ${0, 1, dots.c, n - 1}$ for any $n >= 1$.
]
#leancode(links: (("ProvabilityLogic", "ProvabilityLogic/Logic/GLPoint3/Basic.lean"),))[```
  theorem LogicGLPoint3.provability_TFAE [DecidableEq α] {A : Formula α} : [
    A ∈ LogicGLPoint3,
    ⊢ᵍ[GLPoint3] (∅ ⟹ {A}),
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGLPoint3] → M ⊧ A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLPoint3] → M.root.1 ⊩[_] A,
    ∀ (n : ℕ) [NeZero n] (M : Model (Fin n) α), [M.IsFiniteGLPoint3] → M ⊧ A,
    ∀ (n : ℕ) [NeZero n] (M : RootedModel (Fin n) α), [M.IsFiniteGLPoint3] → M.root.1 ⊩[_] A
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
  theorem LogicGLPoint3.eq_LogicGL_on_letterless : @LogicGLPoint3 Empty = @LogicGL Empty
  ```
]

Finally, we state the arithmetical completeness of $LogicGLPoint3$ with respect to consistency assertions.

#definition[
  - A sentence $sigma$ is a _consistency assertion_ if it is generated from $lnot Bew bot$ and $Bew bot$ by closing under $Bew$, $lnot$, $land$, $lor$, and $limp$.
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

  def Realization.IsConsistencyRealization (f : Realization α L) (𝔅 : Provability T₀ T) : Prop :=
    ∀ a, 𝔅.IsConsistencyAssertion (f.val a)

  abbrev ConsistencyRealization (α : Type*) (𝔅 : Provability T₀ T) :=
    {f : Realization α L // f.IsConsistencyRealization 𝔅}

  instance {𝔅 : Provability T₀ T} :
    CoeFun (ConsistencyRealization α 𝔅) (fun _ => Formula α → FirstOrder.Sentence L) :=
    ⟨fun f => Formula.interpret f.1 𝔅⟩

  abbrev StandardConsistencyRealization (α : Type*) (T : FirstOrder.ArithmeticTheory) [T.Δ₁] :=
    ConsistencyRealization α T.standardProvability
  ```
]

#theorem[@VS83[Theorem 1]][
  $LogicGLPoint3 proves A$ if and only if $PeanoArithmetic proves f_(Bew_PeanoArithmetic) (A)$ for every consistency realization $f$ over $PeanoArithmetic$.
]
#leancode(
  links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/GLPoint3/Basic.lean"),),
)[
  ```
  theorem LogicGLPoint3.arithmetical_completeness_iff_peano_arithmetic [DecidableEq α] :
    A ∈ LogicGLPoint3 ↔ ∀ f : StandardConsistencyRealization α 𝗣𝗔, 𝗣𝗔 ⊢ f A
  ```
]

== Related work and milestones <sect:provabilitylogic_futurework>

Finally, we mention some prior work related to theorem provers and mechanizations for provability logic, and describe future directions.
In the following, we restrict our attention to prior work in the field of provability logic, and omit prior work in other areas of modal logic (e.g., tense logic and epistemic logic).

=== Proof theory <subsect:proof_theory_provability_logic>

The proof theory of #LogicGL has been studied extensively.
First, Gentzen-style sequent calculi have been investigated in numerous works @SV80 @Lei81 @SV82 @Val83 @Bor83 @Avr84 @Sas01 @Moe01 @GR12 @Bri16.
In particular, as a syntactic issue, whether the termination of the cut-elimination algorithm holds for sequent calculi based on multisets had long been a matter of debate, and the issue is considered to have been resolved by @GR12.
On the other hand, Brighton @Bri16 gave an alternative proof of the termination of the cut-elimination algorithm using the technique called _regression trees_, and this argument has been mechanized in Rocq by Goré, Ramanayake, and Shillito @GRS21.
Furthermore, Férée et al. @FvdGvGS24 mechanized in Rocq the uniform interpolation theorem @Bil16 for #LogicGL via sequent calculi.
In particular, although their proof is based on Bílková @Bil16, we mention that in the course of the mechanization they discovered an error in @Bil16 and were able to correct it #footnote[Quoted from @FvdGvGS24[p.2]: During our work on formalising this proof in Coq, we uncovered an incompleteness in it (@Bil16), and our formalisation contains a corrected version of the construction of...].
These mechanizations can be regarded as significant results in that they settled a debate over ambiguous pen-and-paper arguments by strict computer verification.

In addition, there are also many approaches to non-Gentzen-style proof systems for #LogicGL, i.e., systems obtained by adding further machinery to ordinary sequent calculi:
e.g., the _labelled sequent calculi_ by Negri @Neg05 @Neg14, the _tree-hypersequent calculus_ by Poggiolesi @Pog09, the _nested sequent calculi_ by Maniwa and Kashima @MK24, and the _non-wellfounded proofs_ (or _circular proofs_) by Shamkanov @Sha14#footnote[Here we mention only the systems for #LogicGL. For general discussions of each formalism, we refer the reader to the references of the respective papers.].
For discussions on the equivalence of the provability of several of these sequent systems, including the Gentzen-style ones, see Goré and Ramanayake @GR12a and Lyon @Lyo25.
In particular, Shamkanov's non-wellfounded proofs have the advantage that the Lyndon interpolation theorem can be proved syntactically @Sha14[Chapter 4]#footnote[This fact itself is also proved in @Sha11, but the proof there relies on Kripke-semantical techniques.].
As far as we know, the only mechanizations of the proof theory of sequent calculi equipped with such additional machinery are the mechanization of the labelled sequent calculus in HOL Light by Maggesi and Perini Brogi @MPB21 @MPB23 and, along that line, Bilotta's HOLMS project @Bil25.


Tableau methods for #LogicGL are discussed in @Boo94[Chapter 10] for instance.
A tableau-based automated theorem prover for #LogicGL was implemented by Goré and Kelly @GK07, where the efficiency of the implementation is also discussed.

The proof theory of #LogicS and #LogicD has been developed only recently.
Sierra Miranda and Studer @SMS26 proved the Lyndon interpolation property of #LogicS using non-wellfounded proofs.
As a different approach, Kushida @Kus20 proposed a sequent calculus for #LogicS that uses two levels of sequents $seq1$ and $seq2$ (see @def:layered_sequent_calculi).
Roughly speaking, the provable #seq1;-sequents coincide with those provable in #GentzenGL, the system is equipped with a lift-up mechanism from #seq1 to #seq2, and on the level of #seq2 one can reason as in the logic #LogicKT.
While @Kus20 gives a syntactic cut-elimination algorithm, Kashima and Kato @KK23 proved the cut elimination for #LogicS by a semantical method.
Furthermore, Kashima et al. @KKIM25 extended this approach and formulated two sequent calculi for #LogicD.
The former uses two levels of sequents as in the case of #LogicS, but has the drawback that the cut rule cannot be eliminated.
The latter uses three levels of sequents #seq1, #seq2, and #seq3, and in particular admits cut elimination; this is the system we have mechanized (see @def:layered_sequent_calculi).

In the present work, we have mechanized the Gentzen-style sequent calculus for #LogicGL, the labelled sequent calculus for #LogicGL (see @sect:labelled-sequent-calculus), and the two-level sequent calculus for #LogicS together with the three-level sequent calculus for #LogicD (see @def:layered_sequent_calculi).
For future work, we plan to mechanize sequent calculi with other machinery as well, together with the equivalence of their provability.
In particular, although Shamkanov's circular proofs involve infinitary structures, the studies by Sierra Miranda et al. @SM23 @SMSZ24 @HSMS25 @SMS26 have revealed that they have many applications, so their mechanization seems to be a technically challenging but worthwhile task.

=== Provability logic of Heyting arithmetic

The provability logic of intuitionistic or constructive arithmetic, in particular, Heyting arithmetic #HeytingArithmetic, has been a subject of study for a long time (see @AB05[Section 9] @BV06[Section 4]).
Even among the recent developments alone, there is prior work such as @AM18 @AM19 @SM23a @Moj24 @Moj26.

Here, we define #LogiciK and #LogiciGL.
Intuitionistic modal logic #LogiciK is obtained from intuitionistic propositional logic by adding the axiom $AxiomK$ for $Box$ and the necessitation rule (note that the language does not contain $Dia$),
and intuitionistic Gödel-Löb logic #LogiciGL is obtained by adding Löb's axiom $Box (Box A -> A) -> Box A$ to #LogiciK.
It is known that the provability logic of #HeytingArithmetic contains at least #LogiciGL, that is, #LogiciGL is arithmetically sound with respect to #HeytingArithmetic.
For purely logical studies of #LogiciGL, consult @Urs79 @Lit14 @vdGI21.
As for mechanization, Shillito and Goré @GS22 gave a refined version of the proof of cut elimination for the sequent calculus for #LogiciGL due to van der Giessen and Iemhoff @vdGI21, and this proof has been mechanized in Rocq.

On the other hand, the logic called the intuitionistic strong Löb logic #LogiciSL, obtained by adding the strong Löb axiom $(Box A -> A) -> A$ to #LogiciK, is also important.
For a survey of #LogiciSL itself as a logic, see, e.g., @VL24.
Shillito et al. @SvdGGI23 gave a new sequent calculus for #LogiciSL admitting cut elimination, and mechanized it in Rocq.
Férée et al. @FvdGvGS24 mechanized the uniform interpolation theorem for #LogiciSL in Rocq (see also @subsect:proof_theory_provability_logic).

Finally, the provability logic of Heyting arithmetic has been announced in Mojtahedi's preprint @Moj26.
However, at the time of writing, this preprint is still under review#footnote[The first version was submitted to arXiv in 2022.].
In the future, we plan to mechanize these arguments, which will make it possible to verify them rigorously and thus to settle this problem in a more reliable way.

=== Enriched Languages

There are also extensions in the direction of adding further modal operators in order to express various notions related to provability.
Here we mention two directions for which mechanizations can be found: polymodal provability logic and interpretability logic.

Japaridze @Jap86 @Jap88 extended the modality of #LogicGL to infinitely many modal operators $[1], [2], ...$ together with their duals $chevron.l 1 chevron.r, chevron.l 2 chevron.r, ...$, and introduced the logic #LogicGLP.
For the meaning of these modal operators, we may consult @AB05[Chapter 8.3].
#LogicGLP is useful in the proof-theoretic analysis of arithmetic and is moreover decidable, but it is also known to be Kripke incomplete.
It is complete with respect to topological semantics, but that semantics has the drawback of being technically hard to work with.
It turned out that the strictly positive fragment of #LogicGLP admits a technically much simpler formulation without losing much expressive power, and nowadays such a system is called _reflection calculus_ #LogicRC (see @Bek12).
At the time of writing, prior work on the mechanization of reflection calculi has been carried out mainly by Joosten's group.
Together with Joosten, de Almeida Borges proposed the _worm calculus_ #LogicWC @dABJ18, a variable-free subsystem of #LogicRC built up solely from $top$ and modal operators indexed by ordinals, and mechanized it in Rocq @dAB18.
They further proposed the _quantified reflection calculus with one modality_ #LogicQRC1 @dABJ20, a system that admits quantifiers while remaining reasonably tractable, and mechanized its soundness and completeness in Rocq @dAB22 @dAB23 #footnote[Only the mechanization of soundness direction is reported in @dAB22, but as far as we can tell from de Almeida Borges' doctoral thesis @dAB23, completeness and decidability have been mechanized since then.].
On the other hand, Santiago-Fernández et al. @SJF24 formulated a term-rewriting-like system (a tree rewriting system) for derivations of #LogicRC, and its mechanization in Rocq appears to be in progress in @SF25.

As another extension of provability logic, there is the _interpretability logic_ proposed by Visser @Vis90.
Interpretability logic is the extension of provability logic with an additional binary modal operator $interpret$ representing interpretability (informally, $A interpret B$ means that the extended theory $T + f(A)$ is interpretable in $T + f(B)$).
There are several semantics for interpretability logic, including _de Jongh–Veltman semantics_ @dJV90 and _Verbrugge semantics_ as known as _generalized Veltman semantics_ (cf. @JRMV24).
The latter one can handle completeness and definability for more axioms, but it has the drawback that the arguments become very involved.
As prior work, mechanization of frame definability for Verbrugge semantics has been carried out in Agda by Rovira @Rov20.

As for our own progress, we have mechanized syntactic proofs and frame definability for some additional axioms and weak interpretability logics based on work by Kurahashi and Okawa @KO21 #footnote[See: #link("https://github.com/FormalizedFormalLogic/InterpretabilityLogic")].
However, we have not yet established modal completeness with respect to frames, and as for the arithmetical completeness theorem, we have not been able to mechanize it at all.

= Concluding and Future works

== Vibe formalizing <subsect:vibe-formalizing>

We describe how the AI is used in our development.
Claude does not mechanize everything autonomously: the author first fixes the overall strategy for proving the main theorems and writes their formal statements, and only then delegates the actual proofs to Claude.
Within the proofs as well, the author gives appropriate directions and tactics, e.g., to proceed by induction on the structure of formulas or on the rules of a sequent calculus.
As a rule of thumb in pure mathematical logic, a fact proved by such an induction requires no special idea: one simply carries out the calculation, and on paper one typically works out a few representative cases and omits the rest.
In a mechanization, every case must be treated without omission; we saw little value in a human spending time on such code, so we actively delegated it to the AI.
In practice, the overall refactoring of #link(REPO_SOURCES.at("ProvabilityLogic"))[FormalizedFormalLogic/ProvabilityLogic] and the mechanization of the classification theorem were mostly completed in about three weeks of actual work, which the second author regards as a substantial gain in speed and efficiency.
