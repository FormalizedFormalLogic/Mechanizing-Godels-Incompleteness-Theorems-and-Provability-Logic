#import "./notations.typ": *

= First-Order Logic and Arithmetic

This section introduces the first-order framework used in our formalization.
We first describe the representation of syntax, derivability, and semantics, and then turn to the arithmetical notions needed to state the incompleteness theorems.

== Syntax

We represent first-order syntax using a locally nameless representation.
Thus variables are divided into two kinds: free variables, written informally as $\&x$, and bound variables, written $\#x$.
Free variables are named by an external type `ξ`, while bound variables are represented by de Bruijn indices.

To express this formally, formulas are defined from the generalized form _semiformula_ @Buss1998.

#leancode(links: (
  "Foundation/FirstOrder/Basic/Syntax/Formula.lean#L24-L32",
  ),
  note:[
    We write `Formula L ξ` for `Semiformula L ξ 0`, and `Sentence L` for sentences, namely `Formula L Empty`.
  ])[
  ```
  inductive Semiformula (L : Language) (ξ : Type*) :
      ℕ → Type _ where
  |  verum : Semiformula L ξ n
  | falsum : Semiformula L ξ n
  |    rel {arity : ℕ} :
    L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |   nrel {arity : ℕ} :
    L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |    and : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |     or : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |    all : Semiformula L ξ (n + 1) → Semiformula L ξ n
  |    exs : Semiformula L ξ (n + 1) → Semiformula L ξ n
  ```
]

In particular, arithmetic formulas are formulas over the language of arithmetic $LOR$, which consists of the symbols
of ordered ring ${0, 1, +, dot, =, <}$.

== First-Order Sequent Calculus

For derivability we use a one-sided sequent calculus for classical first-order logic.
A sequent is a finite list of formulas, and `Derivation Γ` is a type for proofs of the sequent `Γ`.

#leancode(links: (
  "Foundation/FirstOrder/Basic/Calculus.lean#L28-L41",
))[
  ```
  abbrev Sequent (L : Language) := List (Proposition L)

  inductive Derivation : Sequent L → Type _
  | identity (r : L.Rel k) (v) : Derivation [.rel r v, .nrel r v]
  | cut : Derivation (φ :: Γ) → Derivation (∼φ :: Δ) →
      Derivation (Γ ++ Δ)
  | contraction : Derivation Δ → Δ ⊆ Γ → Derivation Γ
  | verum : Derivation [⊤]
  | or : Derivation (φ :: ψ :: Γ) → Derivation (φ ⋎ ψ :: Γ)
  | and : Derivation (φ :: Γ) → Derivation (ψ :: Γ) →
      Derivation (φ ⋏ ψ :: Γ)
  | all : Derivation (φ.free :: Γ⁺) → Derivation ((∀¹ φ) :: Γ)
  | exs : Derivation (φ/[t] :: Γ) → Derivation ((∃¹ φ) :: Γ)
  ```
]

Here, the notation `Γ⁺` is a increment of the free variables in `Γ`, which guarantees that the new variable in `φ.free` is fresh.
`φ/[t]` is the result of substituting the term `t` for the only variable `#0` in `φ`.

The proof with axiom $T$ is defined as a pair consisting of a list of formulas in $T$, a proof that the disjunctions of negations of these formulas and the goal sentence is derivable in the one-sided sequent calculus.

#leancode(links: (
  "Foundation/FirstOrder/Basic/Calculus.lean#L28-L41",
))[
  ```
  structure Theory.Proof (T : Theory L) (σ : Sentence L) where
    axioms : List (Sentence L)
    axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
    derivation :
      OneSidedLK.Pullback Derivation Rewriting.emb (σ :: ∼axioms)
  ```
]

== Semantics and The Completeness Theorem

The semantics is the usual Tarski semantics for first-order logic.
An $L$-structure on a type `M` interprets each function symbol as a function on `M` and each relation symbol as a relation on `M`.
Terms are evaluated from assignments for bound and free variables, and formulas are then evaluated recursively.

#leancode(links: (
  "Foundation/FirstOrder/Basic/Semantics/Semantics.lean#L15-L18",
  "Foundation/FirstOrder/Basic/Semantics/Semantics.lean#L212-L220",
  ),
  note: [
    For a sentence `σ`, the notation `M↓[L] ⊧ σ` means that `σ` is true in the `L`-structure on `M`.
    Similarly, `M↓[L] ⊧* T` means that every sentence in the theory `T` is true in `M`.
  ]
)[
  ```
  class Structure (L : Language) (M : Type*) where
    func : {k : ℕ} → L.Func k → (Fin k → M) → M
    rel  : {k : ℕ} → L.Rel k → (Fin k → M) → Prop

  def EvalAux (s : Structure L M) (f : ξ → M)
      {n} (b : Fin n → M) : Semiformula L ξ n → Prop
    |  rel R v => s.rel R (fun i ↦ (v i).val b f)
    | nrel R v => ¬s.rel R (fun i ↦ (v i).val b f)
    |    φ ⋏ ψ => EvalAux s f b φ ∧ EvalAux s f b ψ
    |    φ ⋎ ψ => EvalAux s f b φ ∨ EvalAux s f b ψ
    |     ∀¹ φ => ∀ x : M, EvalAux s f (x :> b) φ
    |     ∃¹ φ => ∃ x : M, EvalAux s f (x :> b) φ
  ```
]

The completeness theorem is proved by a bit non-standard way #footnote[A forcing argument.].

#leancode(links: (
  "https://github.com/FormalizedFormalLogic/Foundation/blob/8dcdb31964545f3909fccd40eed4d59836f7df95/Foundation/FirstOrder/Completeness/CounterModel.lean#L253",
  ),
)[
  ```
  theorem Proof.complete_iff : T ⊨ φ ↔ T ⊢ φ
  ```
]

This theorem is important for our mechanization of the incompleteness theorems, as it allows us to reduce the syntactic provability,
which is often too complex, to the semantic truth in a model, which is often easier to handle.

== Arithmetic

== Bootstrapping

== Incompleteness Theorems
