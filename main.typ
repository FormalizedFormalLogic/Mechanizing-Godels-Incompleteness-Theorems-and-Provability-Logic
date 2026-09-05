#import "init.typ": *

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

#remark(numbering: none)[
  Since the word _formalize_ is used in two different senses, which may cause confusion, we strictly distinguish between the words _formalize_ and _mechanize_.

  / _formalize_: the formalization of mathematics as a technique in the context of mathematical logic and metamathematics.
  / _mechanize_: the formalization of mathematics in an interactive theorem prover, verifiable on an actual computer.

  Following this convention, what we have done can be stated succinctly: _mechanizing formalized mathematics_.
]

= Introduction

_Gödel's incompleteness theorems_ are among the most significant results in mathematical logic.
In his seminal paper @God31, he proved what is now known as the first incompleteness theorem (G1), and in a footnote, he outlined the second incompleteness theorem (G2).
G2 was later proved rigorously by Hilbert and Bernays @HB39.
We state the theorems in modern terms:
G1, with Rosser's improvement @Ros36, states that for any consistent axiomatic system with sufficient expressive power to execute arithmetic, there exists a proposition that can neither be proved nor disproved within the system (see @thm:G1 and @thm:GR).
G2 states that, for any consistent reasonable axiomatic system as in G1, the proposition formally representing the system's own consistency cannot be proved within the system itself (see @thm:G2).

Gödel also made another important observation: that provability can be regarded as a modality.
In his early work @God33, he observed that the provability of intuitionistic logic can be treated similarly to the modal operator $Box$ in the modal logic now called #LogicS4.
However, it follows from G2, that abstracting the behavior of the provability predicate, the most central notion of the incompleteness theorems, does not yield #LogicS4.
Solovay @Sol76 showed that the modal logic called #LogicGL precisely captures the behavior of the standard provability predicate.
This fact, known as _Solovay's arithmetical completeness theorem_, was a significant result that opened up the subfield of modal logic called _provability logic_.

On the other hand, recently, there has been much active work on mechanizing mathematics using interactive theorem provers, guaranteeing the validity of existing and new results, and providing AI/LLM-assisted or automated proving.
There are many well-known interactive theorem provers such as Rocq @RocqProver, Isabelle @Isabelle, HOL Light @HOLLight @HOLLightTutorial, Agda @Agda, and Lean @dMU21, and mathematics has been mechanized in each of them, including in the field of mathematical logic#footnote[Some of these mechanizations are summarized in @AwesomeLogicFormalization.].
In particular, for mechanizing Gödel's incompleteness theorems, this line of work began with Shankar in 1986 @Sha86 @Sha97, and continues with O'Connor @OCo05 @OCo09, Harrison @Har06, Paulson @Pau15, and Popescu and Traytel @PT19 @PT21, Kirst et al. @KP23 @KH23.
As for provability logic, modal-logical properties of #LogicGL, such as its semantical completeness and automated solvers, have been mechanized by Harrison @HOLLightTutorial[Chapter 20]#footnote[We do not know when Harrison's mechanization of modal logic was carried out.], Goré and Kelly @GK07, Goré, Ramanayake and Shillito @GRS21, Maggesi and Perini Brogi @MPB21 @MPB23, Gignoux @Gig26.
However, these are either abstract or not full mechanizations within arithmetic.
For instance, O'Connor's implementation assumes several facts needed for the proof of G2 as axioms, and Paulson's mechanization of G2 uses hereditarily finite sets, not arithmetic @Pau14.
To the best of our knowledge, no full mechanization of the incompleteness theorems entirely within arithmetic has been reported, and consequently neither has any mechanization of the arithmetical side of provability logic, such as Solovay's arithmetical completeness theorem.

In the present paper, we describe our mechanizations of Gödel's first and second incompleteness theorems and Solovay's arithmetical completeness theorem.
Our work is carried out in Lean 4, an interactive theorem prover, together with mathlib4 @Mathlib2020, its community-developed mathematics library.
Lean 4 is based on the Calculus of Inductive Constructions (CIC) @dMU21,
and features dependent types, quotient types, and support for noncomputable definitions, making it highly expressive.
In addition, its powerful metaprogramming infrastructure like `aesop` @LF23 and `grind` @MdM26 enables efficient proof automation and extensibility.

Our mechanization is currently hosted as a repository on GitHub, and the version we refer to is #link(REPO_SOURCES.at("Foundation")).
In the present paper, we will briefly and informally introduce the mathematical facts without omitting the essentials, and show the code of our mechanization corresponding to those facts.
However, for the sake of readability, note that in some places we have modified the hosted code.
Moreover, owing to motivations other than the incompleteness theorems and provability logic that the present paper focuses on, some implementations are stated as more general definitions.
We add comments where we deem it necessary, but for the actual working (verified) code, refer to the repository.

=== Declaration of AI usage

// In the interest of novelty and fairness, we declare here how AI/LLMs were used in our development.
Our main mechanizations of the three results, the first and second incompleteness theorems and Solovay's arithmetical completeness theorem were done between 2023 and 2025, and up to that point they contained no AI-generated code.
This can be verified from the following commits, at which each result first became `sorry`-free.
#footnote[The first two commits were made in #link("https://github.com/FormalizedFormalLogic/Arithmetization")[FormalizedFormalLogic/Arithmetization], later merged into Foundation as a subtree.]

#let commit-link(hash) = link("https://github.com/FormalizedFormalLogic/Foundation/commit/" + hash)[#raw(hash.slice(
  0,
  8,
))]
- Gödel's first incompleteness theorem: #commit-link("e9325d82f6e4284b8dca530c8f9719650d7a21cf") (2024/09/04).
- Gödel's second incompleteness theorem: #commit-link("2da7151e1da0ce40ae222fec1651756f8ee7acce") (2024/09/04).
- Solovay's arithmetical completeness theorem: #commit-link("4a34d75c074c7614a1f16661ac73fd0725263c32") (2025/04/06).
Some proofs in modal logic and provability logic make use of AI-assisted mechanizations. This is discussed in detail in
Appendix: @subsect:vibe-formalizing.

/*
On the other hand, since June 2026, the second author has adopted AI/LLM-assisted _vibe coding_ in Lean for #link(REPO_SOURCES.at("ProvabilityLogic"))[FormalizedFormalLogic/ProvabilityLogic], using interactive coding agents such as Anthropic's Claude both for refactoring the code and for mechanizing the new results, namely the sequent calculi for modal logics and the classification theorem of provability logics.
We have verified that the main parts of the generated code do not rely on any device regarded as illegitimate for mechanizing mathematics in Lean, such as `sorry`, additional nontrivial axioms, or `native_decide`#footnote[Some parts still contain `sorry`s; they are isolated from the main results of this paper and do not compromise the validity of the mechanization. See @subsect:remaining_sorry_in_provlogic.].
In @subsect:vibe-formalizing, we give a brief report on how we carried out the writing and generation of mechanized proofs using AI/LLMs in this project.
*/
// *The authors take full responsibility for the final artifact, including its AI-generated code.*

= Mechanization of the incompleteness theorems

We mechanized the following two results.
Here, arithmetic sentence/theory means a sentence/theory in the language $LOR = {0, 1, +, dot, <, =}$.

#theorem(number: thmnumber(<thm:G1>))[Gödel's First Incompleteness Theorem][
  Let $T$ be a $Delta_1$-definable, $Sigma_1$-sound arithmetic theory stronger than $R0$.
  Then $T$ is incomplete.
]

#theorem(number: thmnumber(<thm:G2>))[Gödel's Second Incompleteness Theorem][
  Let $T$ be a $Delta_1$-definable, $Sigma_1$-sound arithmetic theory stronger than $ISigma1$.
  Then $T nproves Con(T)$.
]

The proofs largely follow the standard approach using derivability conditions in the literature (see, for example, @HP93).
We therefore omit the details and instead comment on several technical and methodological aspects of the formalization.

=== Syntax
We use a locally nameless representation for terms and formulas of first-order logic.
A similar approach is adopted in @HvD20.

In standard logical terminology, this amounts to using _semiterms_ and _semiformulas_, which generalize terms and formulas, respectively @Bus98a.
Variable symbols are divided into two classes: infinitely many _free variables_ and finitely many _bound variables_.
A semiterm is a term generated using these two variables.
A semiformula is generated from semiterms in the usual way, but may contain bound variables that are not bound by any quantifier.
We mechanized the type of semiformulas that may contain free variables of type $xi$ and $n$ bound variables as `Semiformula L ξ n`:

#leancode(
  links: (
    ("Foundation", "Foundation/FirstOrder/Basic/Syntax/Formula.lean#L24-L32"),
  ),
  note: [
    We write `Formula L ξ` for `Semiformula L ξ 0`, and `Sentence L` for sentences, namely `Formula L Empty`.
  ],
)[
  ```
  inductive Semiformula (L : Language) (ξ : Type*) : ℕ → Type _ where
  |  verum : Semiformula L ξ n
  | falsum : Semiformula L ξ n
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |   nrel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |    and : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |     or : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |    all : Semiformula L ξ (n + 1) → Semiformula L ξ n
  |    exs : Semiformula L ξ (n + 1) → Semiformula L ξ n
  ```
]

Mechanization using semiterm/semiformulas is more than a technical device to deal with quantifiers; it also offers practical advantages.
For example, a frequently encountered situation in proof theory and model theory, such as a formula $phi(x, y, z)$ with parameters from $M$, can be expressed by the single type `Semiformula L M 3`.

=== On internal argument<subsubsection:internal>
In proofs of the incompleteness theorems, especially G2, the principal obstacle is often the internalization of metamathematics---terms, formulas, provability, elementary proof theory, and so forth---a process commonly called _arithmetization_ or _bootstrapping_.
In other words, these notions must be formally defined and their properties proved _within_ the formalized deductive system itself, which in our case is $ISigma1$.
A naïve, purely syntactic approach to this task encounters the following difficulties#footnote[
  Nevertheless, carrying out such a construction is worthwhile.
  These syntactic operations are constructive and can be developed over very weak base theories, such as $sans("S")^1_2$.
].

/ Bureaucracy of the deductive system:
  When sufficiently complex formulas are involved (which is most often the case in practice), the deductive system can become unmanageably intricate.
  A task that is already difficult to formalize in Lean becomes exceedingly burdensome when it must instead be carried out within a still more restrictive formal system that is itself defined inside a formal system (Lean).
  Moreover, tackling G2 requires climbing yet another level.
  One would have to work with a formal system inside a formal system inside a formal system, which is hardly practical.
/ Non-canonicity of bootstrapping:
  Bootstrapping is a formalization of metamathematics.
  This requires encoding of the metamathematical notions, the _Gödel numbering_.
  Unfortunately, there is neither a canonical choice of encoding nor a unique mathematically natural construction.
  One must instead develop a large body of intrinsically complicated combinatorics, often involving numerous ad-hoc constructions.
  This complicates the proofs and, for the reasons just discussed, makes mechanization difficult.

Our solution is to avoid syntactic bureaucracy by employing a model-theoretic argument via the completeness theorem of first-order logic.
That is, we show $T models phi$ instead of $T proves phi$.
This largely resolves the first problem. Although it does not eliminate the second, it mitigates its complexity to feasible levels.

In the weak mathematics considered here, one frequently needs to track restrictions on formula complexity, e.g. $Sigma_i, Pi_i$.
With a model-theoretic argument, however, it is unnecessary to exhibit an actual formula; it suffices to establish that the predicate in question is _definable_ in appropriate complexity.
As discussed below, we designed this part of the development so that it can be handled almost automatically using Aesop @LF23.
Thus, the bureaucratic overhead of syntax, especially that associated with (external) formulas, can be _almost_ eliminated.
There nevertheless remain situations in which a concrete formula must be supplied.
For example, the second incompleteness theorem asserts $T nproves Con(T)$, and stating this result requires an explicit, model-independent formula $Con(T)$.

In addition, to avoid directly handling formalized statements, such as $Pr(T)(x)$, as much as possible, we use an abstract characterization of provability predicates when discussing the derivability conditions. We discuss this in detail in @subsect:provability_abstraction.

== First incompleteness theorem

It is known that the first incompleteness theorem holds even for extremely weak arithmetic theories.
Among these, we use the arithmetic theory $R0$ due to Cobham (cf. @Vau62).

#definition[
  The theory $R0$ consists of the equality axioms for $LOR$, together with the following variable-free atomic formulas in $LOR$,

  $
      num(n) + num(m) = & num(n + m) wide   && "for all" n, m in Nat \
    num(n) dot num(m) = & num(n dot m) wide && "for all" n, m in Nat \
          num(n) eq.not & num(m) wide       && "for all" n, m in Nat "such that" n eq.not m \
  $
  together with the following axiom scheme:
  $
    fal(x)[x < num(n) <-> or.big_(i < n) (x = num(i))]
  $
]

#leancode[
  ```
  inductive R0 : ArithmeticTheory
  | equal : ∀ φ ∈ 𝗘𝗤 ℒₒᵣ, R0 φ
  | Ω₁ (n m : ℕ) : R0 “↑n + ↑m = ↑(n + m)”
  | Ω₂ (n m : ℕ) : R0 “↑n * ↑m = ↑(n * m)”
  | Ω₃ (n m : ℕ) : n ≠ m → R0 “↑n ≠ ↑m”
  | Ω₄ (n : ℕ) : R0 “∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”

  notation "𝗥₀" => R0
  ```
]


The key theorem is that every $Sigma_1$-sound theory extending $R0$ has a weak representation of every recursively enumerable (r.e.) predicate @Vau62 @JS83.
More precisely:

#theorem[
  Let $T supset.eq R0$ be a $Sigma_1$-sound theory and let $S$ be an r.e. set.
  Then there is a $LOR$-formula $sans("Rep")_(S)(x)$ such that
  $
    n in S <==> T proves sans("Rep")_(S)(num(n))
  $
]<thm:repr>

Let $godel(bullet)$ denote a Gödel coding of formulas.
Define the set $D$ by $godel(phi) in D <==> T proves not phi(godel(phi))$.
As shown below, there is a provability predicate $Pr(T)(x)$, definable by a $Sigma_1$-formula, such that
$Nat models Pr(T)(godel(psi)) <==> T proves psi$; hence $D$ is r.e.
@thm:G1 now follows from @thm:repr by the standard diagonal argument.

#theorem[Gödel's First Incompleteness Theorem @God31 @Vau62 @JS83][
  Let $T$ be a $Delta_1$-definable, $Sigma_1$-sound arithmetic theory stronger than $R0$.
  Then $T$ is incomplete;
  that is, there exists an arithmetic sentence $phi$ such that $T nproves phi$ and $T nproves not phi$.
]<thm:G1>

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/ee84d9d25d88aec25a0c6b5203881e8515437f40/Foundation/FirstOrder/Incompleteness/First.lean#L16",
    ),
  ),
  note: [
    Here `Incomplete T` is an abbreviation of `∃ φ, T ⊬ φ ∧ T ⊬ ∼φ`.
  ],
)[
  ```
  theorem incomplete (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : Incomplete T
  ```
]
== Provability abstraction <subsect:provability_abstraction>

Before proving G2, we introduce a theory of the provability predicate, called _provability abstraction_, because working directly with a raw provability predicate is technically cumbersome.
This notion is closely related to provability logic, which treats provability as a modality (see @sect:provability_logic).
With these abstractions, the incompleteness theorems can be mechanized abstractly, by purely syntactic manipulations.
Concretely constructing a "provability" satisfying the abstract derivability conditions then immediately yields the concrete statements of the incompleteness theorems.
Mechanizing the incompleteness theorems via such an abstract provability has previously been studied by Popescu and Traytel @PT19 @PT21.

#definition[Provability predicate][
  Suppose that $cal(L)$-sentences admit a Gödel numbering in language $Lang(0)$.
  For an $Lang(0)$-theory $T_0$ and an $cal(L)$-theory $T$, a unary $Lang(0)$-semisentence $Bew(x)$ is called a _$T$-provability predicate over $T_0$_, if the following holds for every $cal(L)$-sentence $sigma$.

  #align(center, table(
    columns: (auto, auto),
    inset: 6pt,
    align: (right + horizon, left + horizon),
    stroke: none,
    $bold("D1")$,
    [
      $T proves sigma ==> T_0 proves Bew(godel(sigma))$
    ],
  ))

  That is, $Bew(x)$ is required to satisfy at least the derivability condition $bold("D1")$.
  In what follows, we simply write $Bew sigma$ for $Bew(godel(sigma))$.
  We further define the following properties, where $sigma$ and $pi$ range over $cal(L)$-sentences.
  The conditions $bold("D3")$ and $bold("Kre")$ are defined only when $T_0$ and $T$ are theories in the same language, i.e., when $Lang(0) = cal(L)$.

  #align(center, table(
    columns: (auto, auto),
    inset: 6pt,
    align: (right + horizon, left + horizon),
    stroke: none,
    $bold("D2")$,
    [
      $T_0 proves Bew (sigma -> pi) -> Bew sigma -> Bew pi$
    ],

    $bold("D3")$,
    [
      $T_0 proves Bew sigma -> Bew Bew sigma$
    ],

    $bold("Kre")$,
    [
      $T proves Bew sigma$ implies $T proves sigma$
    ],

    $bold("Ros")$,
    [
      $T proves not sigma$ implies $T_0 proves not Bew sigma$
    ],
  ))
  // - $bold("FC")$ (on an $cal(L)$-sentence $sigma$): $T_0 proves sigma -> Bew sigma$.
  // - $bold("S")$ (on an $L_0$-structure $M$) : $M models Bew sigma ==> T proves sigma$.
] <def:provability_abstraction>

#leancode[
  ```
  structure Provability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
    prov : Semisentence L₀ 1
    bew_def {σ : Sentence L} : T ⊢ σ → T₀ ⊢ prov/[⌜σ⌝]

  variable {L₀ L : Language} [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

  @[coe] def pr (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L₀ := 𝔅.prov/[⌜σ⌝]
  instance : CoeFun (Provability T₀ T) (fun _ ↦ Sentence L → Sentence L₀) := ⟨pr⟩

  class HBL2 [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
    D2 {σ τ : Sentence L} : T₀ ⊢ 𝔅 (σ 🡒 τ) 🡒 𝔅 σ 🡒 𝔅 τ

  class HBL3 [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) where
    D3 {σ : Sentence L} : T₀ ⊢ 𝔅 σ 🡒 𝔅 (𝔅 σ)

  class Kreisel [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) where
    KR {σ : Sentence L} : T ⊢ 𝔅 σ → T ⊢ σ

  class Rosser [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
    Ros {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ ∼𝔅 σ
  ```
]

The standard provability predicate $Pr(T)$ satisfies $bold("D2")$, $bold("D3")$ and $bold("Kre")$.
In provability logic discussed in @sect:provability_logic, we mainly assume those conditions on the provability predicate.
The condition $bold("Kre")$ is a derivability condition introduced by Visser @Vis21 under the name _Kreisel's condition_ #footnote[Visser attributes the origin of this condition to @Kre54. To be precise, Visser required both directions.].
/*Our motivation for this abstraction is to formalize the arguments in a purely syntactic way, without involving models or structures.*/
Anticipating the later construction, the standard provability predicate is a $Sigma_1$-predicate, so the condition $bold("Kre")$ can be regarded as a purely syntactic counterpart of the $Sigma_1$-soundness of $T$; the converse implication, which corresponds to $Sigma_1$-completeness, is the content of $bold("D1")$.

In fact, abstracting provability alone does not suffice to mechanize the incompleteness theorems: we also need to abstract the diagonalization.

#definition[Diagonalization abstraction][
  Suppose that $cal(L)$-sentences admit a Gödel numbering in $cal(L)$.
  An $cal(L)$-theory $T$ is called _diagonalizable_ if one can construct a map $fixpoint(bullet)$, sending an unary $cal(L)$-formula to an $cal(L)$-sentence,
  such that
  $
    T proves fixpoint(theta) <-> theta (godel(fixpoint(theta)))
  $
  for any $theta(x)$. We call $fixpoint(theta)$ the _fixed point_ of $theta$.

  Let $T_0, T$ be $cal(L)$-theories such that $T_0$ is diagonalizable, and let $Bew$ be a provability of $T_0, T$. Then the fixed point of $not Bew (x)$ is called the _Gödel sentence_ and is denoted by $Godel(Bew)$.
] <def:diagonalization_abstraction>

#leancode[
  ```
  class Diagonalization [L.ReferenceableBy L] (T : Theory L) where
    fixedpoint : Semisentence L 1 → Sentence L
    diag (θ) : T ⊢ fixedpoint θ 🡘 θ/[⌜fixedpoint θ⌝]

  variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L} [Diagonalization T₀]

  def gödel (𝔅 : Provability T₀ T) : Sentence L := fixedpoint T₀ “x. ¬!𝔅.prov x”
  ```
]

For the arithmetic theory stronger than $ISigma1$, we have a _standard diagonalization_,
which is obtained by the standard construction of diagonalization.

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/25dda5090b03e9d74b23d4537ca76e546c7197af/Foundation/FirstOrder/Bootstrapping/FixedPoint.lean#L130",
    ),
  ),
)[
  ```
  theorem diagonal {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T] (θ : ArithmeticSemisentence 1) :
      T ⊢ fixedpoint θ 🡘 θ/[⌜fixedpoint θ⌝]
  ```
]

With these tools at hand, the incompleteness theorems and their corollaries can be proved by syntactic manipulations alone.
In what follows, let $T_0 subset.eq T$ be $cal(L)$-theories such that $T_0$ is diagonalizable and $T$ is consistent,
and let $Bew$ be a $T$-provability predicate over $T_0$.
The first incompleteness theorem is proved as follows.

#proposition[Abstract version of G1][
  1. $T nproves Godel(Bew)$.
  2. If $Bew$ satisfies $bold("Kre")$, then $T nproves not Godel(Bew)$.

  Hence $Godel(Bew)$ is independent of $T$, and therefore $T$ is incomplete.
] <prop:abstract_G1>

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Basic.lean#L194",
    ),
  ),
)[
  ```
  variable {L : Language} [L.ReferenceableBy L] [L.DecidableEq]
  variable {T₀ T : Theory L} [Diagonalization T₀] [T₀ ⪯ T] [Consistent T]
  variable {𝔅 : Provability T₀ T}

  theorem unprovable_gödel : T ⊬ gödel 𝔅

  theorem unrefutable_gödel [𝔅.Kreisel] : T ⊬ ∼gödel 𝔅

  theorem gödel_independent [𝔅.Kreisel] : Independent T (gödel 𝔅)

  theorem first_incompleteness [𝔅.Kreisel] : Incomplete T
  ```
]

The second incompleteness theorem can likewise be mechanized.

#proposition[Abstract version of G2][
  Assume that $Bew$ satisfies $bold("D2")$ and $bold("D3")$.
  The sentence $not Bew bot$ is a natural expression of consistency; we denote it by $Con(Bew)$.
  Then the following hold.
  1. $T nproves Con(Bew)$.
  2. If $Bew$ satisfies $bold("Kre")$, then $T nproves not Con(Bew)$. Hence $Con(Bew)$ is also independent of $T$.
] <prop:abstract_G2>

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Basic.lean#L35",
    ),
  ),
)[
  ```
  variable {L₀ L : Language} [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

  def con (𝔅 : Provability T₀ T) : Sentence L₀ := ∼𝔅 ⊥

  variable {L : Language} [L.ReferenceableBy L] [L.DecidableEq]
  variable {T₀ T : Theory L} [Diagonalization T₀] [T₀ ⪯ T]
  variable {𝔅 : Provability T₀ T} [𝔅.HBL]

  theorem con_unprovable [Consistent T] : T ⊬ 𝔅.con

  theorem con_unrefutable [Consistent T] [𝔅.Kreisel] : T ⊬ ∼𝔅.con

  theorem con_independent [Consistent T] [𝔅.Kreisel] : Independent T 𝔅.con
  ```
]

There is, however, a view that $Con(Bew)$ is not the only natural expression of consistency.
Variants of G2 arising from this view are discussed later.

As further results, we can also mechanize Löb's theorem and the formalized Löb's theorem.

#proposition[Abstract version of Löb's Theorem][
  Assume that $Bew$ satisfies $bold("D2")$ and $bold("D3")$. Then the following hold,
  where $sigma$ is an arbitrary $cal(L)$-sentence.

  #align(center, table(
    columns: (auto, auto),
    inset: 6pt,
    align: (right + horizon, left + horizon),
    stroke: none,
    [Löb's theorem], [$T proves Bew sigma -> sigma$ implies $T proves sigma$.],
    [Formalized Löb's theorem], [$T_0 proves Bew (Bew sigma -> sigma) -> Bew sigma$.],
  ))
] <prop:abstract_Löb>

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Basic.lean#L286",
    ),
  ),
)[
  ```
  variable {L : Language} [L.ReferenceableBy L] [L.DecidableEq]
  variable {T₀ T : Theory L} [Diagonalization T₀] [T₀ ⪯ T]
  variable {𝔅 : Provability T₀ T} [𝔅.HBL]

  theorem löb_theorem {σ : Sentence L} (H : T ⊢ 𝔅 σ 🡒 σ) : T ⊢ σ

  theorem formalized_löb_theorem {σ : Sentence L} : T₀ ⊢ 𝔅 (𝔅 σ 🡒 σ) 🡒 𝔅 σ
  ```
]

Note that $bold("D1"), bold("D2"), bold("D3")$ and the formalized Löb's theorem correspond roughly to the necessitation rule and the axioms $AxiomK$, $Axiom("4")$, and $Axiom("L")$ of modal logic, respectively.
This yields the observation that arithmetical soundness holds for the standard provability predicate.

In view of the reason we gave for introducing $bold("Kre")$ into the abstraction, requiring $bold("Kre")$ in the abstract G1 of @prop:abstract_G1 corresponds to requiring the $Sigma_1$-soundness of $T$.
If we instead impose on $Bew$ the condition $bold("Ros")$, then the abstract G1 can be proved assuming only that $T$ is consistent.
This is precisely an abstraction of the incompleteness theorem as improved by Rosser @Ros36.

#proposition[Abstract version of Gödel--Rosser theorem][
  Assume that the provability predicate $Rosser$ satisfies $bold("Ros")$.
  In this case, the Gödel sentence for $Rosser$ is called the _Rosser sentence_.
  Then we have $T nproves Godel(Rosser)$ and $T nproves not Godel(Rosser)$.
  That is, $Godel(Rosser)$ is independent of $T$; note in particular that $bold("Kre")$ is not required.
  On the other hand, for the consistency statement $Con(Rosser)$ defined above, we have $T proves Con(Rosser)$ #footnote[In the Japanese mathematical logic community, this is often called _Kreisel's remark_.].
] <prop:abstract_GR>

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Basic.lean#L323",
    ),
  ),
)[
  ```
  variable {L : Language} [L.ReferenceableBy L]
  variable {T₀ T : Theory L} [Diagonalization T₀] [T₀ ⪯ T] [Consistent T]
  variable {𝔅 : Provability T₀ T} [𝔅.Rosser]

  theorem unrefutable_rosser : T ⊬ ∼(gödel 𝔅)

  theorem rosser_independent : Independent T (gödel 𝔅)

  theorem rosser_first_incompleteness (𝔅 : Provability T₀ T) : Incomplete T

  theorem kreisel_remark : T ⊢ 𝔅.con
  ```
]

Indeed, the concrete statement of the Gödel--Rosser theorem given later, obtained by instantiating this abstraction, does not require $Sigma_1$-soundness.

We next describe refutability (_Widerlegbar_) $Wid$.
Concerning G2, formal consistency can be expressed in ways other than the formalized consistency $not Bew bot$ introduced in @prop:abstract_G2.
For instance, the statement "no sentence is both provable and refutable" may also be regarded as a natural expression of consistency.
The version of G2 obtained by formalizing this consistency is usually attributed to Jeroslow @Jer73 #footnote[See, e.g., Kurahashi @Kur20 for how subtle differences in the required conditions, and various versions of the statement of G2, arise depending on how consistency is formalized.].
A naive attempt to formalize Jeroslow's G2 on top of the provability abstraction, however, becomes slightly cumbersome if only $Bew$ is available.
The reason is that $Bew$ is in fact an arithmetical predicate taking the Gödel number of a formula: dealing with refutability, that is, with negated sentences, would force us to handle a "function" computing the Gödel number of $not sigma$ from that of $sigma$, and such a function is awkward to accommodate within the provability abstraction.
We therefore abstract refutability itself, rather than a function computing the Gödel number of a negation.
This allows us to formalize Jeroslow's G2 concisely.

#definition[Refutability abstraction][
  For an $Lang(0)$-theory $T_0$ and an $cal(L)$-theory $T$, a unary $Lang(0)$-semisentence $Wid(x)$ is called a _$T$-refutability predicate over $T_0$_, if the following holds for every $cal(L)$-sentence $sigma$.
  $
    T proves not sigma ==> T_0 proves Wid(godel(sigma))
  $

  As with $Bew$, we abbreviate $Wid(godel(sigma))$ as $Wid sigma$.
  We say that $Wid$ is _sound on_ an $cal(L)$-sentence $sigma$ if $T proves Wid sigma ==> T proves not sigma$.

  Let $Wid$ be a $T$-refutability predicate over $T_0$ and suppose that $T_0$ is diagonalizable. Then the fixed point of $Wid(x)$ is called the _Jeroslow sentence_ and is denoted by $Jeroslow(Wid)$.
]

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Refutability.lean#L15",
    ),
  ),
)[
  ```
  structure Refutability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
    refu : Semisentence L₀ 1
    refu_def {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ refu/[⌜σ⌝]

  @[coe] def Refutability.rf (𝔚 : Refutability T₀ T) (σ : Sentence L) : Sentence L₀ := 𝔚.refu/[⌜σ⌝]
  instance : CoeFun (Refutability T₀ T) (fun _ ↦ Sentence L → Sentence L₀) := ⟨Refutability.rf⟩

  variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L} [Diagonalization T₀]

  class Refutability.SoundOn (𝔚 : Refutability T₀ T) (σ : Sentence L) where
    sound_on : T ⊢ 𝔚 σ → T ⊢ ∼σ

  def jeroslow (𝔚 : Refutability T₀ T) : Sentence L := fixedpoint T₀ 𝔚.refu
  ```
]

The following is immediate for the Jeroslow sentence.

#proposition[
  If $T$ is consistent and $Wid$ is sound on $Jeroslow(Wid)$, then $T nproves Jeroslow(Wid)$.
]

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Refutability.lean#L73",
    ),
  ),
)[
  ```
  lemma unprovable_jeroslow [T₀ ⪯ T] [Consistent T] [𝔚.SoundOn (jeroslow 𝔚)] : T ⊬ jeroslow 𝔚
  ```
]

We now state Jeroslow's incompleteness theorem.

#proposition[Abstract version of Jeroslow's G2 @Jer73][
  Let $Safe(Bew, Wid) (x) equiv not (Bew x and Wid x)$ be the unary formula stating that a sentence is not both provable and refutable (_safe_), and let $FLoN(Bew, Wid) equiv forall x, Safe(Bew, Wid)(x)$ be the sentence expressing consistency in the sense that every sentence is safe (the _formalized law of non-contradiction_).

  If $T$ is consistent and $T_0 proves Jeroslow(Wid) -> Bew Jeroslow(Wid)$, then $T nproves FLoN(Bew, Wid)$.
] <prop:abstract_JG2>

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Refutability.lean#L90",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Basic.lean#L84",
    ),
  ),
  note: [
    The hypothesis $T_0 proves Jeroslow(Wid) -> Bew Jeroslow(Wid)$ is mechanized as the class `FormalizedCompleteOn`, which is an abstract version of formalized $Gamma$-completeness for $Bew$.
    For instance, formalized $Sigma_1$-completeness is expressed as `[∀ σ ∈ 𝚺₁, 𝔅.FormalizedCompleteOn σ]`.
  ],
)[
  ```
  variable [L.DecidableEq] [L.ReferenceableBy L] {T₀ T : Theory L}
  variable [Diagonalization T₀] [T₀ ⪯ T] {𝔅 : Provability T₀ T} {𝔚 : Refutability T₀ T}

  def safe (𝔅 : Provability T₀ T) (𝔚 : Refutability T₀ T) : Semisentence L 1 :=
    “x. ¬(!𝔅.prov x ∧ !𝔚.refu x)”

  def flon (𝔅 : Provability T₀ T) (𝔚 : Refutability T₀ T) : Sentence L := “∀ x, !(safe 𝔅 𝔚) x”

  class FormalizedCompleteOn (𝔅 : Provability T₀ T) (σ) where
    formalized_complete_on : T₀ ⊢ σ 🡒 𝔅 σ

  lemma unprovable_flon [Consistent T] [𝔅.FormalizedCompleteOn (jeroslow 𝔚)] : T ⊬ flon 𝔅 𝔚
  ```
]

Making this abstraction concrete, that is, actually constructing the desired provability $Bew$ and refutability $Wid$, is the goal of the following sections.

== Second incompleteness theorem

By making the abstraction @prop:abstract_G2 introduced in the previous section concrete, the goal of this section is to
construct a _standard_ provability predicate.
We first take $ISigma1$ as the base theory for our proof of G2.

#definition[
  We call $PAMinus$ (the theory of discrete ordered semirings) the finite axiom system consisting of
  universal $LOR$-sentences describing basic properties.
  For a unary arithmetical formula $phi(x)$ (which may contain parameters), we define the formula $Ind(φ)$ expressing the universal closure of following instance of mathematical induction:
  $
    phi(0) -> (forall x phi(x) -> phi(x + 1)) -> forall x phi(x)
  $
  For a class of formulas $Gamma$, we define $Ind(Gamma)$ as the union of $PAMinus$ with $Ind(φ)$ for every formula $φ$ belonging to $Gamma$.
  We then let $ISigma1$ be the theory in which mathematical induction is available for all $Sigma_1$-formulas, and $Peano$ the theory in which it is available for all formulas.
]

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Refutability.lean#L90",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Basic.lean#L84",
    ),
  ),
)[
  ```
  abbrev       addZero : ArithmeticSentence := “∀ x, x + 0 = x”
  abbrev      addAssoc : ArithmeticSentence := “∀ x y z, (x + y) + z = x + (y + z)”
  abbrev       addComm : ArithmeticSentence := “∀ x y, x + y = y + x”
  abbrev     addEqOfLt : ArithmeticSentence := “∀ x y, x < y → ∃ z, x + z = y”
  abbrev        zeroLe : ArithmeticSentence := “∀ x, 0 ≤ x”
  abbrev     zeroLtOne : ArithmeticSentence := “0 < 1”
  abbrev oneLeOfZeroLt : ArithmeticSentence := “∀ x, 0 < x → 1 ≤ x”
  abbrev      addLtAdd : ArithmeticSentence := “∀ x y z, x < y → x + z < y + z”
  abbrev       mulZero : ArithmeticSentence := “∀ x, x * 0 = 0”
  abbrev        mulOne : ArithmeticSentence := “∀ x, x * 1 = x”
  abbrev      mulAssoc : ArithmeticSentence := “∀ x y z, (x * y) * z = x * (y * z)”
  abbrev       mulComm : ArithmeticSentence := “∀ x y, x * y = y * x”
  abbrev      mulLtMul : ArithmeticSentence := “∀ x y z, x < y ∧ 0 < z → x * z < y * z”
  abbrev         distr : ArithmeticSentence := “∀ x y z, x * (y + z) = x * y + x * z”
  abbrev      ltIrrefl : ArithmeticSentence := “∀ x, x ≮ x”
  abbrev       ltTrans : ArithmeticSentence := “∀ x y z, x < y ∧ y < z → x < z”
  abbrev         ltTri : ArithmeticSentence := “∀ x y, x < y ∨ x = y ∨ x > y”

  inductive PeanoMinus : ArithmeticTheory
    | equal         : ∀ φ ∈ 𝗘𝗤 ℒₒᵣ, PeanoMinus φ
    | addZero       : PeanoMinus PeanoMinus.Axiom.addZero
    | addAssoc      : PeanoMinus PeanoMinus.Axiom.addAssoc
    | ...
  notation "𝗣𝗔⁻" => PeanoMinus

  def succInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ :=
    “!φ 0 → (∀ x, !φ x → !φ (x + 1)) → ∀ x, !φ x”

  def InductionScheme (Γ : Semiformula L ℕ 1 → Prop) : Theory L :=
    { ψ | ∃ φ : Semiformula L ℕ 1, Γ φ ∧ ψ = .univCl (succInd φ) }

  abbrev InductionOnHierarchy (Γ : Polarity) (k : ℕ) : ArithmeticTheory := 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ (Arithmetic.Hierarchy Γ k)
  prefix:max "𝗜𝗡𝗗 " => InductionOnHierarchy

  abbrev ISigma (k : ℕ) : ArithmeticTheory := 𝗜𝗡𝗗 𝚺 k
  notation "𝗜𝚺₁" => ISigma 1

  abbrev Peano : ArithmeticTheory := 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ Set.univ
  notation "𝗣𝗔" => Peano
  ```
]

$ISigma1$ is in fact unnecessarily strong. For a sharper result, one could weaken the base theory to Buss's theory $sans("S")^1_2$ @Bus86, over which the standard proof can be carried out with few changes#footnote[
  In many proofs, including ours, derivability condition D3 is established using formalized $Sigma_1$-completeness.
  Whether this principle holds in $sans("S")^1_2$ remains an open problem @BV06.
  One must therefore prove the sharper formalized $Sigma^"b"_1$-completeness theorem.
].
Moreover, Nelson's interpretation $Robinson triangle.small.r sans("S")^1_2$ extends the second incompleteness theorem to a broad class of theories that interpret Robinson arithmetic $Robinson$ @Vis11.
Although this is an appealing direction, we do not pursue it because it would make the mechanization prohibitively complex (See @subsect:future_interpretability for future work).
Working in $ISigma1$ makes recursive definitions of predicates and functions easier to handle, since @thm:recursive-def is available.

As noted above, our internal arithmetical arguments are carried out in an arbitrarily fixed model of $ISigma1$, which we henceforth denote by $Universe$.
A _class_ is a subset of $Universe$.

Because only induction restricted to $Sigma_1$-formulas is available over $Universe$, the ($Sigma_i$-, $Pi_i$-, and $Delta_i$-) definability of relations and functions on $Universe$ is important.
In practice, this can often be inferred automatically from the stated definition.
To automate the substantial amount of such reasoning, we make extensive use of Aesop @LF23 whenever no explicit defining formula is needed.

Let $Bit(x, y)$ be the predicate asserting that the $x$-th digit in the binary expansion of $y$ is $1$.
Ackermann coding, obtained from the membership relation defined below, provides a means of representing hereditarily finite sets within arithmetic @Pet09.
$
  x in y <==> Bit(x, y)
$
To work with $Bit(x, y)$ in weak arithmetic, we also mechanized the well-known fact due to Gaifman and Dimitracopoulos @GD82,
that the graph of exponentiation is representable by a $Delta_0$-formula and that its inductive properties are provable in $Ind(Delta_0)$.

The $ISigma1$ version of the Knaster--Tarski theorem, stated below, is useful for defining recursively defined structures over $Universe$ with appropriate complexity.

#theorem[Version of the Knaster--Tarski theorem][
  Let $Phi: cal(P)(Universe) -> cal(P)(Universe)$ be a class-valued function.
  Assume that this satisfies the following conditions.
  / Definability: A predicate $P(x, c) := x in Phi({z | z in c})$ is $Delta_1$-definable with parameters.
  / Monotonicity: $bold(C) subset.eq bold(C')$ implies $Phi(bold(C)) subset.eq Phi(bold(C'))$.
  / Finiteness: If $x in Phi(bold(C))$ holds, then $x in Phi({z in bold(C) | z < m})$ holds for some $m in Universe$.
  Then we have a $Sigma_1$ class $Fix_Phi$ such that
  $
    Phi(Fix_Phi) = Fix_Phi
  $
  Additionally, if it satisfies the following condition, $Fix_Phi$ is $Delta_1$.
  / Strong finiteness: If $x in Phi(bold(C))$ holds, then $x in Phi({z in bold(C) | z < x})$ holds.
]<thm:recursive-def>

This satisfies the following structural induction principle.

#theorem[Structural induction][
  Assume that $Phi$ satisfies the strong finiteness property.
  The predicate $Fix_Phi$ above satisfies the induction principle of the following form.
  Let $psi$ be a $Sigma_1$ or $Pi_1$-predicate (which may contain parameters from $Universe$):
  $
    fal(bold(C) subset.eq Fix_Phi)[fal(x in bold(C))psi(x) -> fal(x in Phi(bold(C)))psi(x)]
    quad "implies" quad
    fal(x in Fix_Phi)psi(x)
  $
]<thm:recursive-ind>

A practically important point is that the defining formulas of $Fix_Phi$ can be explicitly constructible from the defining formula of $P(x, c)$.
In the mechanization, we first call such a formula a `Blueprint k` (`k` is a number of parameters).
Obviously it is purely syntactic and independent of any model.
We then define `Construction V φ`, the model-theoretic realization of a `φ : Blueprint k`.
Our mechanization of @thm:recursive-def and @thm:recursive-ind is stated with
these two parameters.

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Arithmetic/HFS/Fixpoint.lean#L25",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Arithmetic/HFS/Fixpoint.lean#L54",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Arithmetic/HFS/Fixpoint.lean#L59",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Arithmetic/HFS/Fixpoint.lean#L62",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Arithmetic/HFS/Fixpoint.lean#L184",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Arithmetic/HFS/Fixpoint.lean#L222",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Arithmetic/HFS/Fixpoint.lean#L256",
    ),
  ),
)[
  ```
  structure Blueprint (k : ℕ) where
    core : 𝚫₁.Semisentence (k + 2)

  structure Construction {k : ℕ} (φ : Blueprint k) where
    Φ : (Fin k → V) → Set V → V → Prop
    defined : 𝚫₁.Defined (fun v ↦ Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0)) φ.core
    monotone {C C' : Set V} (h : C ⊆ C') {v x} : Φ v C x → Φ v C' x

  class Construction.Finite {k : ℕ} {φ : Blueprint k} (c : Construction V φ) where
    finite {C : Set V} {v x} : c.Φ v C x → ∃ m, c.Φ v {y ∈ C | y < m} x

  class Construction.StrongFinite {k : ℕ} {φ : Blueprint k} (c : Construction V φ) where
    strong_finite {C : Set V} {v x} : c.Φ v C x → c.Φ v {y ∈ C | y < x} x

  variable (c : Construction V φ)

  def Construction.Fixpoint (v) (x : V) : Prop

  theorem Construction.case [c.Finite] : c.Fixpoint v x ↔ c.Φ v {z | c.Fixpoint v z} x

  theorem Construction.induction [c.StrongFinite] {P : V → Prop} (hP : Γ-[1]-Predicate P)
      (H : ∀ C : Set V, (∀ x ∈ C, c.Fixpoint v x ∧ P x) → ∀ x, c.Φ v C x → P x) :
      ∀ x, c.Fixpoint v x → P x
  ```
]

Syntactic structures such as terms, formulas, and proofs are all recursively generated and can therefore be constructed using `Blueprint` and `Construction`.
Moreover, because these structures are generated well-foundedly, they satisfy the strong finiteness property.
It follows uniformly that the corresponding predicates are $Delta_1$-definable and satisfy the structural induction principles.
These facts immediately yield definitions over $Universe$ of basic syntactic operations such as substitution.
#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Bootstrapping/Syntax/Formula/Basic.lean#L1218",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean#L519",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean#L467",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean#L525",
    ),
  ),
)[
  ```
  variable {L : Language} [L.Encodable] [L.LORDefinable]

  instance IsSemiformula.definable : 𝚫₁-Relation[V] (IsSemiformula L)

  instance Proof.definable {T : Theory L} [T.Δ₁] : 𝚫₁-Relation[V] (Proof T)

  def Provable (φ : V) : Prop := ∃ d, Proof T d φ

  instance Provable.definable : 𝚺₁-Predicate[V] Provable T
  ```
]


We can routinely verify that the predicate `provabilityPred` is a provability predicate in the sense of @def:provability_abstraction,
and moreover that it satisfies the derivability conditions $bold("D1")$, $bold("D2")$, $bold("D3")$, and $bold("Kre")$.

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Bootstrapping/DerivabilityCondition/D1.lean#L23",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Bootstrapping/DerivabilityCondition/D2.lean#L20",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Bootstrapping/DerivabilityCondition/D3.lean#L160",
    ),
    ("Foundation", "Foundation/FirstOrder/Incompleteness/StandardProvability.lean#L38-L44"),
    ("Foundation", "Foundation/FirstOrder/Incompleteness/StandardProvability.lean#L83"),
  ),
)[
  ```
  variable {L : Language} [L.Encodable] [L.LORDefinable]

  /-- Hilbert–Bernays provability condition D1 -/
  theorem internalize_provability {φ} : T ⊢ φ → Provable T (⌜φ⌝ : V)

  /-- Hilbert–Bernays provability condition D2 -/
  theorem modus_ponens {φ ψ : Proposition L}
      (hφψ : Provable T (⌜φ 🡒 ψ⌝ : V)) (hφ : Provable T (⌜φ⌝ : V)) :
      Provable T (⌜ψ⌝ : V)

  /-- A formalized 𝚺₁-completeness -/
  theorem sigma_one_complete {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
      V↓[ℒₒᵣ] ⊧ σ → Provable T (⌜σ⌝ : V) := fun h ↦ by
    simpa [tprovable_iff_provable]
      using! Bootstrapping.Arithmetic.sigma_one_provable_of_models T hσ h

  /-- Hilbert–Bernays provability condition D3 -/
  theorem provable_internalize {σ : ArithmeticSentence} :
      Provable T (⌜σ⌝ : V) → Provable T (⌜provabilityPred T σ⌝ : V)

  noncomputable abbrev Theory.standardProvability : Provability 𝗜𝚺₁ T where
    prov := provable T
    bew_def := provable_D1

  instance : T.standardProvability.HBL2 := ⟨provable_D2⟩

  instance [𝗣𝗔⁻ ⪯ T] : T.standardProvability.HBL3 := ⟨provable_D3⟩
  ```
]

On the other hand, making @prop:abstract_G2 concrete requires the theory to be diagonalizable (@def:diagonalization_abstraction).
Since $T supset.eq ISigma1$, the fixed point theorem holds.

#theorem[
  Suppose $T supset.eq ISigma1$. For any unary arithmetical formula $theta(x)$, one can construct an arithmetic sentence $fixpoint(theta)$ such that
  $
    T proves fixpoint(theta) <-> theta (godel(fixpoint(theta)))
  $
  Hence the theory $T$ is diagonalizable.
] <thm:fixedpoint>

#leancode(
  links: (
    ("Foundation", "Foundation/FirstOrder/Bootstrapping/FixedPoint.lean#L126-L131"),
    ("Foundation", "Foundation/FirstOrder/Incompleteness/StandardProvability.lean#L18-L20"),
  ),
)[
  ```
  noncomputable def diag (θ : ArithmeticSemisentence 1) : ArithmeticSemisentence 1 :=
    “x. ∀ y, !ssnum y x x → !θ y”

  noncomputable def fixedpoint (θ : ArithmeticSemisentence 1) : ArithmeticSentence :=
    (diag θ)/[⌜diag θ⌝]

  theorem diagonal (θ : ArithmeticSemisentence 1) : T ⊢ fixedpoint θ 🡘 θ/[⌜fixedpoint θ⌝]

  noncomputable instance : Diagonalization 𝗜𝚺₁ where
    fixedpoint := fixedpoint
    diag θ := diagonal θ
  ```
]

Combining the results above, @prop:abstract_G2 immediately yields our final result: a mechanization of the second incompleteness theorem.

#theorem[Gödel's Second Incompleteness Theorem @God31][
  Let $T$ be a $Delta_1$-definable, $Sigma_1$-sound arithmetic theory stronger than $ISigma1$.
  Then $T nproves Con(T)$,
  where $Con(T)$ is a consistency statement of $T$.
]<thm:G2>

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Incompleteness/Second.lean#L18",
    ),
  ),
)[
  ```
  /-- Gödel's second incompleteness theorem -/
  theorem consistent_unprovable [Consistent T] : T ⊬ T.consistent.val

  theorem inconsistent_unprovable [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T ⊬ ∼T.consistent.val
  ```
]

== Some further results related to the incompleteness theorems <subsect:further_incompleteness>

Using the tools developed so far, we have also proved several theorems related to Gödel's incompleteness theorems.

=== Variants of fixedpoint lemma
The following fixed point theorems, which generalize @thm:fixedpoint, also hold; see @Boo94 for the proofs.
Although we omit the details, they are needed when we establish arithmetical completeness in @sect:provability_logic.
Throughout this subsection, we assume $T supset.eq ISigma1$.

#theorem[
  For any family $(theta_i)_(i < k)$ of $k$-arity arithmetical formulas $theta_i (x_0, ..., x_(k - 1))$, one can construct arithmetic sentences $sans("fixedpoint")_0, ..., sans("fixedpoint")_(k - 1)$ such that, for every $i < k$,
  $
    T proves sans("fixedpoint")_i <-> theta_i (godel(sans("fixedpoint")_0), ..., godel(sans("fixedpoint")_(k - 1)))
  $
] <thm:multi_fixedpoint>

#leancode(
  links: (("Foundation", "Foundation/FirstOrder/Bootstrapping/FixedPoint.lean#L151-L159"),),
)[
  ```
  noncomputable def multifixedpoint (θ : Fin k → ArithmeticSemisentence k) (i : Fin k)
    : ArithmeticSentence := ...

  theorem multidiagonal (θ : Fin k → ArithmeticSemisentence k)
    : T ⊢ multifixedpoint θ i 🡘 (Rew.subst fun j ↦ ⌜multifixedpoint θ j⌝) ▹ (θ i) :=
  ```
]

#theorem[
  For any $(k + 1)$-arity arithmetical formula $theta(x, arrow(y))$, one can construct a $k$-arity arithmetical formula $fixpoint(theta)(arrow(y))$ such that
  $
    T proves forall arrow(y), (fixpoint(theta)(arrow(y)) <-> theta(godel(fixpoint(theta)), arrow(y)))
  $
] <thm:parameterized_fixedpoint>

#leancode(
  links: (("Foundation", "Foundation/FirstOrder/Bootstrapping/FixedPoint.lean#L204-L210"),),
)[
  ```
  noncomputable def parameterizedFixedpoint (θ : ArithmeticSemisentence (k + 1))
    : ArithmeticSemisentence k := ...

  theorem parameterized_diagonal (θ : ArithmeticSemisentence (k + 1))
    : T ⊢ ∀¹* (parameterizedFixedpoint θ 🡘 “!θ !!(⌜parameterizedFixedpoint θ⌝) ⋯”)
  ```
]

=== Löb's Theorem
Instantiating the abstract version stated in @prop:abstract_Löb, we immediately obtain the concrete Löb's theorem.
As related work, Löb's theorem has also been mechanized in Isabelle by Bailitis, on top of Paulson's mechanization of the incompleteness theorems (see @AFP-Incompleteness[Chapter 13]), and in Rocq by Bailitis @Bai24.

#theorem[Löb's theorem and formalized Löb's theorem @Lob55][
  Let $T supset.eq ISigma1$ be a $Delta_1$-definable theory and let $sigma$ be any sentence.
  / Löb's theorem: If $T proves Pr(T)(godel(sigma)) -> sigma$, then $T proves sigma$.
  / Formalized Löb's theorem: $ISigma1 proves Pr(T)(godel(Pr(T)(godel(sigma)) -> sigma)) -> Pr(T)(godel(sigma))$.
]

#leancode(links: (("Foundation", "Foundation/FirstOrder/Incompleteness/Löb.lean"),))[
  ```
  variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence}

  theorem löb_theorem : T ⊢ provabilityPred T σ 🡒 σ → T ⊢ σ

  theorem formalized_löb_theorem : 𝗜𝚺₁ ⊢ provabilityPred T (provabilityPred T σ 🡒 σ) 🡒 provabilityPred T σ
  ```
]

=== Gödel--Rosser First Incompleteness Theorem
In the setting of @thm:G1, the theory $T$ was required to be $Sigma_1$-sound.
By instantiating @prop:abstract_GR, we can prove the Gödel--Rosser incompleteness theorem @Ros36, which weakens this requirement to mere consistency.

#theorem[Gödel--Rosser First Incompleteness Theorem @Ros36][
  Let $T supset.eq ISigma1$ be a $Delta_1$-definable and consistent theory.
  Then $T$ is incomplete.
] <thm:GR>

#leancode(
  links: (("Foundation", "Foundation/FirstOrder/Incompleteness/RosserProvability.lean"),),
  note: [
    Note that the assumption `[T.SoundOnHierarchy 𝚺 1]` in the mechanization of @thm:G1 is replaced by `[Entailment.Consistent T]`.
  ],
)[
  ```
  variable {T : Theory L} [T.Δ₁] [Entailment.Consistent T]

  noncomputable abbrev Theory.rosserProvability : Provability 𝗜𝚺₁ T where
    prov := T.rosserProvable
    bew_def := rosserProvable_D1

  instance : T.rosserProvability.Rosser := ⟨rosserProvable_rosser⟩

  theorem incomplete_GR (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T] : Entailment.Incomplete T
  ```
]

The required provability predicate satisfying $bold("Ros")$ is constructed by so-called _witness comparison_ (see @HP93 @Lin97); we omit the details here.

=== Jeroslow's Second Incompleteness Theorem
Similarly, from @prop:abstract_JG2, we can also concretely mechanize Jeroslow's second incompleteness theorem @Jer73.
We mention that Popescu and Traytel @PT21[Theorem 30] mechanized Jeroslow's theorem only at the abstract level.

#theorem[Jeroslow's Second Incompleteness Theorem @Jer73][
  Let $T supset.eq ISigma1$ be a $Delta_1$-definable and consistent theory.
  Then $T nproves forall x. not (Pr(T)(x) and Pr(T)(dot(not) x))$,
  where $dot(not)$ denotes the function taking the Gödel number of a sentence to that of its negation, i.e., $dot(not) godel(sigma) = godel(not sigma)$.
]

#leancode(links: (("Foundation", "Foundation/FirstOrder/Incompleteness/Jeroslow.lean"),))[
  ```
  theorem unprovable_formalized_law_of_noncontradiction {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T]
  : T ⊬ (∀¹ ∼(T.provable ⋏ T.refutable))
  ```
]

=== $Sigma_1$-soundness and $Delta_1$-definability of $ISigma1$ and $Peano$
To instantiate the theorems stated so far with a concrete theory such as $ISigma1$ or $Peano$, the $Sigma_1$-soundness and the $Delta_1$-definability of these theories must themselves be mechanized.
We have done this as well.

#proposition[
  $ISigma1$ and $Peano$ are $Sigma_1$-sound, hence consistent.
]

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/12fc07a5019847beb6b2217d2a5edbd853c24258/Foundation/FirstOrder/Arithmetic/Schemata.lean#L390",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/12fc07a5019847beb6b2217d2a5edbd853c24258/Foundation/FirstOrder/Arithmetic/Schemata.lean#L392",
    ),
  ),
)[
  ```
  instance sigmaOneSound_ISigmaOne : 𝗜𝚺₁.SoundOnHierarchy 𝚺 1

  instance sigmaOneSound_Peano : 𝗣𝗔.SoundOnHierarchy 𝚺 1
  ```
]

#proposition[
  $ISigma1$ and $Peano$ are $Delta_1$-definable.
]

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/8f2c66de8c404e51758bcb5988545858150d828d/Foundation/FirstOrder/Incompleteness/InductionSchemeDelta1.lean#L1386",
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/8f2c66de8c404e51758bcb5988545858150d828d/Foundation/FirstOrder/Incompleteness/InductionSchemeDelta1.lean#L1389",
    ),
  ),
)[
  ```
  noncomputable instance PA_delta1Definable : 𝗣𝗔.Δ₁

  noncomputable instance ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁
  ```
]

Hence all the theorems above can indeed be instantiated with concrete theories such as $ISigma1$ and $Peano$.

=== Tarski's Undefinability Theorem
As a corollary of the fixed point theorem, we can prove Tarski's theorem on the undefinability of truth.
First, we prove the following lemma.

#lemma[
  Let $T supset.eq ISigma1$ be a consistent theory.
  Then there is no unary formula $tau(x)$ such that $T proves sigma <-> tau(godel(sigma))$ for any sentence $sigma$.
]

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/8f2c66de8c404e51758bcb5988545858150d828d/Foundation/FirstOrder/Incompleteness/Tarski.lean#L12",
    ),
  ),
)[
  ```
  lemma not_exists_tarski_predicate {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T] [Consistent T] : ¬∃ τ : ArithmeticSemisentence 1, ∀ σ, T ⊢ σ 🡘 τ/[⌜σ⌝]
  ```
]

Taking as $T$ the _true arithmetic_ $TrueArithmetic$, the theory of all sentences true in $Nat$, we immediately obtain the desired theorem.

#theorem[Tarski's Undefinability Theorem @Tar35][
  There is no truth predicate $True(x)$ such that $Nat models sigma$ if and only if $Nat models True(godel(sigma))$ for any sentence $sigma$.
]<thm:undefinability_of_truth>

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/8f2c66de8c404e51758bcb5988545858150d828d/Foundation/FirstOrder/Incompleteness/Tarski.lean#L20",
    ),
  ),
)[
  ```
  theorem undefinability_of_truth : ¬∃ τ : ArithmeticSemisentence 1, ∀ σ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ σ ↔ ℕ↓[ℒₒᵣ] ⊧ τ/[⌜σ⌝]
  ```
]

In contrast to this theorem, it is known that for a complexity class $Gamma$ of formulas, there is a partial truth predicate $TruePartial(Gamma, x)$, obtained by replacing "for any sentence" with "for any $Gamma$-sentence" in the definition of $True(x)$, which is itself definable by a $Gamma$-formula (cf. @HP93).
This fact has not been mechanized yet; consequently, several statements of provability logic proved via partial truth predicates remain unmechanized, as we discuss further in @subsect:remaining_sorry_in_provlogic.

=== Church's Theorem and Undecidability of First-Order Logic
In Mathlib, computability of a predicate (at the meta level of Lean) is defined by `ComputablePred` (cf. @Car19), which requires the types of the domain and the range to be `Primcodable` #footnote[That is, encoding into and decoding from natural numbers are primitive recursive.].
Since the type of formulas of our arithmetic is `Primcodable` via a suitable encoding, we can ask whether the set $upright("Thm")(T)$ of sentences provable from a theory $T$ is computable.
This yields the following theorem, commonly known as Church's theorem.

#theorem[Church's Theorem (for $Sigma_1$-sound theories)][
  For a $Sigma_1$-sound theory $T supset.eq R0$, $upright("Thm")(T)$ is not computable.
]

#leancode(links: (("Foundation", "Foundation/FirstOrder/Incompleteness/Church.lean"),))[
  ```
  theorem uncomputable_theory_of_sigma1Sound {T : ArithmeticTheory} [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
  : ¬ComputablePred T.theory
  ```
]

Now take as $T$ the theory $PAMinus$, a finitely axiomatized $Sigma_1$-sound fragment of $Peano$ stronger than $R0$.
Since its axioms can be conjoined into a single sentence, the deduction theorem applies, and the undecidability of first-order logic over the language of arithmetic follows.

#theorem[Undecidability of First-Order Logic][
  First-order logic over the language $LOR$ is not computable.
  That is, for an $LOR$-sentence $sigma$, it is undecidable whether $emptyset proves sigma$ or $emptyset nproves sigma$.
]

#leancode(links: (("Foundation", "Foundation/FirstOrder/Incompleteness/Church.lean"),))[
  ```
  theorem undecidability_first_order_logic : ¬ComputablePred ((∅ : ArithmeticTheory).theory)
  ```
]

For the speed-up theorem (@thm:speedup) below, we have also mechanized a version that weakens $Sigma_1$-soundness to mere consistency, at the cost of strengthening the base theory from $R0$ to $ISigma1$.

#theorem[Church's Theorem (for consistent theories)][
  For a consistent theory $T supset.eq ISigma1$, $upright("Thm")(T)$ is not computable.
] <thm:church2>

#leancode(links: (("Foundation", "Foundation/FirstOrder/Incompleteness/Church.lean"),))[
  ```
  theorem uncomputable_theory_of_consistent {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T]
  : ¬ComputablePred T.theory
  ```
]

Note that this version does not apply to the above proof of the undecidability of first-order logic, since $PAMinus$ is weaker than $ISigma1$.

=== On proof size
Formalization also allows us to discuss provability by a proof of _feasible_ length or complexity in a certain sense.

#theorem[
  Let $T supset.eq ISigma1$ be a $Delta_1$-definable and $Sigma_1$-sound theory, let $f$ be a $Sigma_1$-definable function, and let $e$ be an arbitrary natural number.
  Then we can construct the _restricted provability predicate_ $RPr(T, f, e) (x)$, a further restriction of the provability predicate expressing that "provable by a $T$-proof whose Gödel number is less than $f(e)$".
  As with the usual Gödel sentence, let $RGodel(T, f, e)$ be a fixed point of $not RPr(T, f, e) (x)$.

  Then $NN models RGodel(T, f, e)$ and $T proves RGodel(T, f, e)$, but every $T$-proof of $RGodel(T, f, e)$ has code at least $f(e)$.
]

#leancode(
  links: (("Foundation", "Foundation/FirstOrder/Incompleteness/RestrictedProvability.lean"),),
  note: [
    To use these theorems, one must supply both a concrete function `f` and a $Sigma_1$-formula `fDef` representing it; the instance `[𝚺₁-Function₁ f via fDef]` states that `fDef` actually defines `f`.
    `T ⊢! T.restrictedGödel fDef e` denotes the `Type` of "$T$-proofs of $RGodel(T, f, e)$" (not the `Prop` of provability).
  ],
)[
  ```
  variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
           {fDef : 𝚺₁.Semisentence 2} {e : ℕ}

  theorem true_restrictedGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] :
    ℕ↓[ℒₒᵣ] ⊧ T.restrictedGödel fDef e

  theorem provable_restrictedGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] :
    T ⊢ T.restrictedGödel fDef e

  theorem lower_bound_gödelNumber_proof_restrictedGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] :
    ∀ b : T ⊢! T.restrictedGödel fDef e, f (ORingStructure.numeral e) ≤ ⌜b⌝
  ```
]

As a concrete example of such an $f$, we can take the superexponential function $supexp$ #footnote[
  Define $iterexp(x, y)$ by $iterexp(x, 0) = x$ and $iterexp(x, y + 1) = 2^(iterexp(x, y))$, and let $supexp(x) = iterexp(x, x)$. For example, $supexp(2) = 16$ and $supexp(3) = 2^256$; also $2^x <= supexp(x)$ holds for $x >= 1$.
], formalized over $ISigma1$, which yields the following corollary.

#corollary[
  Let $T supset.eq ISigma1$ be a $Delta_1$-definable and $Sigma_1$-sound theory, and let $e$ be an arbitrary natural number.
  Then $T proves RGodel(T, supexp, e)$, but every $T$-proof of $RGodel(T, supexp, e)$ has code at least $supexp(e)$.
]

#leancode(links: (
  ("Foundation", "Foundation/FirstOrder/Arithmetic/HFS/Superexp.lean"),
  ("Foundation", "Foundation/FirstOrder/Incompleteness/RestrictedProvability.lean"),
))[
  ```
  variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] {e : ℕ}

  theorem provable_restrictedGödel_superexp : T ⊢ T.restrictedGödel superexpDef e

  theorem lower_bound_gödelNumber_proof_restrictedGödel_superexp :
    ∀ b : T ⊢! T.restrictedGödel superexpDef e, Superexp.superexp e ≤ ⌜b⌝
  ```
]

In our mechanization, coding an $n$-character formula or proof yields a Gödel number roughly of the order of $2^n$.
Hence, taking as $f$ the far faster-growing $supexp$ and taking $e$ extremely large, say $10^9$, this corollary suggests that there are true statements that humans can _practically_ never prove (or even read).

Furthermore, we have also mechanized the speed-up theorem due to Ehrenfeucht--Mycielski @EM71 #footnote[Observations of this kind go back to Gödel @God36.].

#theorem[Ehrenfeucht--Mycielski speed-up theorem @EM71][
  Let $min_T (sigma)$ be the least Gödel number of a $T$-proof of $sigma$ if $T proves sigma$, and $0$ if $T nproves sigma$.

  Let $T supset.eq ISigma1$ be a $Delta_1$-definable theory and take a sentence $sigma$ with $T nproves sigma$.
  Then, for any computable function $f$, there exists a sentence $pi$ such that $T proves pi$ and $f (min_(T + sigma)(pi)) < min_T (pi)$.

  For example, taking $f(x) = 2^(x + 1)$, there is a sentence $pi$ with $min_(T + sigma)(pi) < log_2 min_T (pi)$: adding $sigma$ as an axiom shrinks its proof to logarithmic order.
] <thm:speedup>

#leancode(links: (("Foundation", "Foundation/FirstOrder/Incompleteness/Speedup.lean"),))[
  ```
  noncomputable def Theory.minProof (T : Theory L) [T.Δ₁] (σ : Sentence L) : ℕ
    := sInf {d : ℕ | Proof T d (⌜σ⌝ : ℕ)}

  theorem ehrenfeucht_mycielski_speedup {T : Theory L} [T.Δ₁] {σ : Sentence L}
    (hU : ¬ComputablePred (insert (∼σ) T).theory) (f : ℕ → ℕ) (hf : Computable f) :
    ∃ π : Sentence L, T ⊢ π ∧ f ((insert σ T).minProof π) < T.minProof π

  variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence} (hσ : T ⊬ σ)

  theorem ehrenfeucht_mycielski_speedup_arithmetic (f : ℕ → ℕ) (hf : Computable f) :
    ∃ π : ArithmeticSentence, T ⊢ π ∧ f ((insert σ T).minProof π) < T.minProof π

  example : ∃ π : ArithmeticSentence, T ⊢ π ∧ (insert σ T).minProof π < Nat.log 2 (T.minProof π)
  ```
]

#remark[
  For a general, not necessarily arithmetic, theory $T$, the same conclusion follows assuming that provability in $T + not sigma$ is not computable (`ehrenfeucht_mycielski_speedup` above).
  In the arithmetic case, this assumption follows from @thm:church2, since $T nproves sigma$ makes $T + not sigma$ a consistent theory containing $ISigma1$.
]

Although one may question measuring the complexity of a proof simply by its Gödel number,
such discussions of restricted provability are closely related to Parikh's feasibility @Par71 and to bounded arithmetic @Bus86.
We consider these mechanizations to be a first step in that direction.

=== Lindenbaum Algebra
The _Lindenbaum algebra_ $frak(A)_T$ of a theory $T$ is obtained by the usual construction quotienting sentences by the equivalence relation given by $T proves sigma <-> pi$.
We have also mechanized some results on these algebras: in particular, for a theory $T$ for which the Gödel--Rosser first incompleteness theorem holds, $frak(A)_T$ is a dense Boolean algebra.

#theorem[
  Let $T supset.eq ISigma1$ be a $Delta_1$-definable theory.
  Then the Lindenbaum algebra $frak(A)_T$ of $T$ is densely ordered:
  whenever $phi < psi$ in $frak(A)_T$, there exists $xi$ such that $phi < xi < psi$.
]

#leancode(links: (("Foundation", "Foundation/FirstOrder/Incompleteness/Dense.lean"),))[
  ```
  lemma dense (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T] [T.Δ₁] {φ ψ : LindenbaumAlgebra T} :
      φ < ψ → ∃ ξ, φ < ξ ∧ ξ < ψ

  instance (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T] [T.Δ₁] : DenselyOrdered (LindenbaumAlgebra T)
  ```
]

Now, it is clear that the Lindenbaum algebra of an arithmetic theory is countable.
Combined with the well-known fact that any two countable, dense, and nontrivial Boolean algebras are order isomorphic (cf. @HG09[Chapter 16]#footnote[This fact is usually stated in terms of atomlessness, but our mechanization states it in terms of density, following Mathlib's `DenselyOrdered` class.]), we immediately obtain the following result.

#theorem[
  For any $Delta_1$-definable consistent theories $T, U supset.eq ISigma1$, the Lindenbaum algebras $frak(A)_T$ and $frak(A)_U$ are isomorphic.
]

#leancode(links: (
  ("Foundation", "Foundation/Vorspiel/Order/BooleanAlgebra/Iso.lean"),
  ("Foundation", "Foundation/FirstOrder/Incompleteness/Dense.lean"),
))[
  ```
  theorem iso_of_countable_atomless {α β : Type*}
      [BooleanAlgebra α] [Countable α] [Nontrivial α] [DenselyOrdered α]
      [BooleanAlgebra β] [Countable β] [Nontrivial β] [DenselyOrdered β] :
      Nonempty (α ≃o β)

  theorem lindenbaum_iso (T U : ArithmeticTheory)
      [𝗜𝚺₁ ⪯ T] [T.Δ₁] [Consistent T] [𝗜𝚺₁ ⪯ U] [U.Δ₁] [Consistent U] :
      Nonempty (LindenbaumAlgebra T ≃o LindenbaumAlgebra U)
  ```
]

That is, the Lindenbaum algebras of $ISigma1$, $Peano$, and even $ZF$ (although not mechanized) are all isomorphic; in this sense these algebras are not interesting.
By a theorem of Pour-El and Kripke @PK67, this isomorphism can moreover be taken to be recursive, but such a refinement has not been mechanized at present.

The algebras obtained by extending the Lindenbaum algebra with provability as an explicit unary operator are called _diagonalizable algebras_ or _Magari algebras_ (cf. @Mag75 @Sha93).
It is known, for example, that the diagonalizable algebras of $Peano$ and $ZF$ are not isomorphic @Sha93a, and these algebras are deeply related to provability logic, which we discuss in @sect:provability_logic.
No mechanization of these algebras has been carried out at present.

= Provability Logic <sect:provability_logic>

In this section, we describe our mechanization of modal logic, in particular of provability logic.
As the most fundamental and important result in the field of provability logic, we have succeeded in mechanizing Solovay's arithmetical completeness theorem @Sol76.
We have also mechanized the classification theorem of provability logics due to Beklemishev @Bek90.
As in the previous section, we keep the introduction of definitions and facts brief.
For the details of modal logic and provability logic, we refer the reader to the standard textbooks @CZ97 @Boo94 @Smo85 and the surveys @JdJ98 @AB05 @BV06 @Ver24.

== Basics of modal logic

We first set up the basic framework of modal logic.

#definition[
  Formulas of modal logic are built from propositional variables (denoted by #PropVar), the primitive logical connectives $bot$ and $limp$, and the modal operator $Box$.
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
  A _Kripke model_ is a triple $M = chevron.l W, R, V chevron.r$, where $R subset.eq W times W$ (the _accessibility relation_) and $V colon W times PropVar -> {0, 1}$ (the _valuation_).
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

== Applications of the sequent calculus <sect:application-of-sequent-calculus>

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

A special case of the fixed point theorem of #LogicGL has also been mechanized in Lean by Gignoux @Gig26, as a supporting lemma for a mechanization of the CIP of #LogicGL based on non-wellfounded proof systems formulated coalgebraically.
We note that Gignoux's mechanization treats formulas of the form $Box A$ and $Dia A$ and proves the fixed point equivalence semantically over Kripke frames, and its interpolants are given by a noncomputable function, whereas in our mechanization the interpolants and the fixed points can be computed constructively inside Lean from derivation trees of the sequent calculus.
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

== On the labelled sequent calculus <sect:labelled-sequent-calculus>

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

First, we define arithmetical interpretations, which translate modal formulas into arithmetic sentences.
In what follows, $T$ is an arithmetic theory with a $Delta_1$-definable axiomatization extending $ISigma1$.
Moreover, $Bew$ denotes a provability in the sense of @subsect:provability_abstraction.
Although the definition allows $Bew$ to be arbitrary, we mainly consider the standard provability $Bew_T$ of $T$.

#definition[
  A map $f colon PropVar -> upright("Sent")_upright("A")$, where $upright("Sent")_upright("A")$ denotes the set of arithmetic sentences, is called an _arithmetical realization_ (or simply a _realization_).
  Given a realization $f$ and a provability $Bew$, the _arithmetical interpretation_ of $A$ by $Bew$, denoted $f_Bew (A)$, is the extension of $f$ translating each modal formula $A$ into an arithmetic sentence as follows.

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
  In particular, $ProvLogic(Peano, Peano) = LogicGL$.
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

The classification of the provability logics obtained as $ProvLogic(T, U)$, where $T$ is as in @sect:arithmetical_completeness and $U$ is an arbitrary arithmetic theory, was studied by Artemov, Beklemishev, Visser, Japaridze, and others, and was finally completed by Beklemishev @Bek90.
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
  Let $L = ProvLogic(T, U)$, where $T$ is a $Delta_1$-definable arithmetic theory extending $ISigma1$ and $U$ is an arbitrary arithmetic theory.
  Then $L$ is classified as follows:
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

== On some remaining `sorry`s <subsect:remaining_sorry_in_provlogic>

Although the mechanization of the classification theorem itself does not depend on them, the mechanizations of some facts of provability logic still contain `sorry`s.
We note them here.

The first is the statement that $LogicD$ is indeed a provability logic, which is currently not `sorry`-free.
#theorem[@Jap86 @AB05[Example 60]][
  Let $T$ be $Sigma_1$-sound. Then
  $LogicD = ProvLogic(T, T + upright("Rfn")_(Sigma_1)(T))$,
  where $upright("Rfn")_(Sigma_1)(T)$ is the (local) reflection principle for $Sigma_1$ formulas of $T$.
] <thm:D_is_provability_logic>

This is because the following fact has not been mechanized in our development.
Proving it requires arguments involving partial truth definitions, which we have not yet completed.

#theorem[Unboundedness @KL68 @AB05[Theorem 23]][
  For $T$ as above, $upright("Rfn")_(Sigma_n)(T)$ is not provable in any consistent r.e. extension of $T$ by $Pi_n$ sentences.
]

The other is the uniform arithmetical completeness theorem.

#theorem[Uniform Arithmetical Completeness Theorem][
  For every $Sigma_1$-sound theory $T$, there exists a uniform realization $f$ such that
  for every formula $A$, $LogicGL proves A$ if and only if $T proves f_(Bew_T) (A)$.
]

== On $LogicGrz$ <sect:Grz>

The Grzegorczyk logic $LogicGrz$ is also closely related to #LogicGL.
Unlike #LogicGL, it is an extension of $LogicS4$, so that $Box$ behaves reflexively; nevertheless, as we describe below, it is tightly connected to #LogicGL and #LogicS through the boxdot translation, and this connection yields an arithmetical completeness theorem for $LogicGrz$ with respect to a _strong_ arithmetical interpretation.
We also mention that $LogicGrz$ has been mechanized in HOL Light by Bilotta's HOLMS project @BMPB26a.
For instance, what they call the Kuznetsov--Goldblatt--Boolos theorem @BMPB26a[Theorem 2] is mechanized in our development as @thm:Grz_boxdot.

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
Non-wellfounded proof systems for $LogicGrz$ are studied by Savateev and Shamkanov @SS21.

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

Using this fact, Goldblatt @Gol78 and Boolos @Boo80 showed that $LogicGrz$ is arithmetically complete with respect to the _strong_ arithmetical interpretation, in which $Box$ is read as "provable and true" rather than merely "provable".

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
In particular, @VS83 shows that $LogicGLPoint3$ enjoys a certain arithmetical completeness with respect to the class of arithmetic sentences called consistency assertions.
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
  $LogicGLPoint3 proves A$ if and only if $Peano proves f_(Bew_Peano) (A)$ for every consistency realization $f$ over $Peano$.
]
#leancode(
  links: (("ProvabilityLogic", "ProvabilityLogic/ProvabilityLogic/GLPoint3/Basic.lean"),),
)[
  ```
  theorem LogicGLPoint3.arithmetical_completeness_iff_peano_arithmetic [DecidableEq α] :
    A ∈ LogicGLPoint3 ↔ ∀ f : StandardConsistencyRealization α 𝗣𝗔, 𝗣𝗔 ⊢ f A
  ```
]

= Related work and future work <sect:provabilitylogic_futurework>

Finally, in this section, we mention some prior work related to our mechanization, that is, mechanizations of the incompleteness theorems and of facts concerning provability logic in proof assistants.
Moreover, on that basis, we indicate several directions in which we plan to proceed.
For facts that we have not mechanized, see also @subsect:further_incompleteness and @subsect:remaining_sorry_in_provlogic.
Concerning provability logic, there is much prior work on mechanizations in the broader area of modal logic in general (e.g., tense logic and epistemic logic), but since these are outside the interest of the present report, we omit them.

== Further metamathematical topics

Our mechanization of the incompleteness theorems is an achievement, but it is a start rather than a goal.
@subsect:further_incompleteness collects several further results, but many metamathematical facts about arithmetic and the incompleteness theorems remain unmechanized.
For example, there are many important tools for the metamathematical analysis of arithmetic, such as reflection principles, partial truth definitions, arguments about nonstandard models of arithmetic, and the arithmetized completeness theorem.
Our development does not contain these tools at present.
Without them, we cannot prove facts such as Ryll-Nardzewski's theorem @Ryl52, which states that $Peano$ is not finitely axiomatizable.
We also cannot fill some of the `sorry`s that we left in @subsect:remaining_sorry_in_provlogic.
For these topics, we plan to mechanize the arguments of the standard textbooks @Lin97 @HP93.

Proof-theoretic analysis is another direction.
As for prior work, Hydras \& Co. @CDPPZ21 @Cas24 is a Rocq mechanization of the termination (in Rocq) of the hydra game @KP82, and of related arguments about the ordinals that proof theory frequently uses.
In our framework, we experimented with autoformalization by an LLM.
We tried to mechanize the sequent calculus for $Peano$ with the $omega$-rule, its cut-elimination theorem, and the fact that $Peano$ does not prove the termination of Goodstein sequences @KP82.
The proofs in the generated code#footnote[For more details, see #link("https://github.com/FormalizedFormalLogic/goodstein-independence").] contain no `sorry` and no additional axiom.
However, a human check of its definitions and statements is still in progress.
We mechanized almost no other proof-theoretic result, thus we plan to work on proof-theoretic analysis and ordinal analysis in the future.

These tools are also necessary for the polymodal provability logics of @subsect:enrich_modalities, because they give the arithmetical meaning of these logics.

== Interpretability <subsect:future_interpretability>

We formalized the incompleteness theorems above in arithmetic, that is, in theories of the language $LOR$.
They depend on the choice of the language and on the details of the coding.
Thus, even if we mechanize set theory in our framework, we cannot conclude the incompleteness theorems for it immediately.
The mechanization of interpretability is important for this problem.
Let $T$ be a theory of the language $Lang(T)$, and let $U$ be a theory of the language $Lang(U)$.
Roughly speaking, $T$ is interpretable in $U$ if there is a suitable translation $t$ such that $T proves phi ==> U proves t(phi)$ for every $Lang(T)$-sentence $phi$; we write $U interpret T$.
Interpretability is a tool for the comparison of theories: if $U interpret T$ and $T$ is essentially undecidable, then $U$ is also essentially undecidable (cf. @TMR53).
See, e.g., Lindström @Lin97[Section 4] for a further discussion.
As far as we know, no prior work mechanized interpretability itself in a proof assistant.

@subsect:settheory discusses the set theories $ZF$ and $ZFC$.
If we mechanize the fact that $ZF interpret Peano$, we can also mechanize the incompleteness theorems for these set theories.
Then we do not have to repeat inside set theory the arguments that we carried out for arithmetic, and we expect that this skips a large part of the proof.
In another direction, we can consider other theories, because the analysis of the incompleteness phenomena is not restricted to arithmetic.
The theory of concatenation $Concatenation$ is a first-order theory that directly axiomatizes the concatenation of strings, and Grzegorczyk initiated its study @Grz05 @GZ08.
In particular, $Concatenation interpret Robinson$ holds @Ste08 @Gan09 @Sve09 @Vis09.
Such a minimal system can be easier to mechanize than arithmetic itself.

Interpretability logic develops provability logic further and treats interpretability itself as a modality.
We discuss it in @subsect:enrich_modalities.

== Intuitionistic first-order logic and arithmetic

Intuitionistic logic is classical logic without the law of excluded middle, and the corresponding predicate logic is intuitionistic first-order logic $LogicIQL$.
$LogicIQL$ satisfies several constructive principles.
It has the disjunction property: if $LogicIQL proves phi or psi$, then $LogicIQL proves phi$ or $LogicIQL proves psi$.
It also has the existence property: if $LogicIQL proves exists x phi(x)$, then there is a closed term $t$ such that $LogicIQL proves phi(t)$.
Intuitionistic predicate logic also has connections to other fields, for example to dependent type theory via the Curry--Howard correspondence.

At present, our mechanization of intuitionistic predicate logic is not far advanced, but it contains the cut-elimination theorem.
If we develop the semantics of intuitionistic predicate logic, we can prove the cut elimination of the sequent calculus semantically (cf. @Avi01).
As a corollary, via the Gödel--Gentzen negative translation, we also obtain a semantic cut elimination for classical first-order logic.
As prior work, Herbelin and Lee @HL09#footnote[Implementation: #link("https://formal.hknu.ac.kr/Kripke").] already mechanized cut elimination for intuitionistic logic in Rocq #footnote[Note that, by similar mean with negative translation, we mechanized cut-elimination theorem for classical logic. See #link("https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/FirstOrder/Hauptsatz.lean")].

Forster, Kirst, Wehr, and their colleagues carried out a series of mechanizations in Rocq @FKW21 @KHD22#footnote[See #link("https://github.com/uds-psl/coq-library-fol").].
This prior work has a wider scope than ours.
Their design is notable: they take intuitionistic logic as the base, and they obtain classical logic as the extension by Peirce's law, controlled by a flag.
They give Tarski, Kripke, algebraic, and game semantics, and for each one they analyse which non-constructive principles the completeness theorem requires in the constructive type theory of Rocq.
Our implementation is specific to classical logic: it defines dual connectives as primitives, and it uses a Tait calculus.

Heyting arithmetic #HeytingArithmetic is intuitionistic logic together with the axioms of Peano arithmetic.
The library of Forster et al. discusses $Robinson$ and $Peano$ over intuitionistic natural deduction, so that provability in the latter is exactly provability in #HeytingArithmetic.
Kirst and Hermes @KH23 proved that these systems are undecidable, through a reduction from Hilbert's tenth problem (the MRDP theorem), and that every axiomatization that is sound in the standard model is incomplete.
The same authors also analysed, in the same setting, Tennenbaum's theorem, which states that no nonstandard model of $Peano$ has computable addition and multiplication @HK24.
The same library mechanizes the Friedman translation, which transforms a proof in classical logic into a proof in minimal logic, and thus shows that $Robinson$ and $Peano$ over minimal or intuitionistic logic are also undecidable.
Our framework already covers the classical side, so the mechanization of such translations is a practical route to #HeytingArithmetic.

The exact axiomatization of the provability logic of Heyting arithmetic has remained a difficult open problem for a long time.
We mention it again in @subsect:provlogic_of_HA.

== Set theory and Forcing <subsect:settheory>

One of our current goal is to mechanize a general framework for forcing and to establish foundational results such as the independence of the continuum hypothesis.
Han and van Doorn @HvD20 have already mechanized the latter result, but their approach is based on Boolean-valued models and has more limited applicability than forcing.

There are several possible ways to mechanize forcing. Two basic approaches are as follows:
1. The standard textbook model-theoretic approach:
  As in, for example, Kunen @Kun11, one begins with a countable transitive model $M$ of $ZFC$ and a forcing poset $PP$ with generic filter $G subset.eq PP$, and constructs a new model by the forcing extension $M[G]$.
2. An approach using proof-theoretic forcing:
  One constructs a kind of interpretation between theories $T_1$ and $T_2$, called a _forcing interpretation_, and establishes an appropriate conservativity result $T_1 prec.eq_Gamma T_2$ @Avi04.
  For example, let $T_1 := ZFC + not CH$, ($CH$: the continuum hypothesis), $T_2 := ZFC$, and $Gamma := {bot}$.
  Suppose that one can construct a $Gamma$-conservative forcing interpretation of $T_1$ in $T_2$.
  A proof of $ZFC proves CH$ easily yield a proof of $ZFC + not CH proves bot$,
  from which the forcing interpretation would in turn yield $ZFC proves bot$.

The first approach is the standard choice.
A frequently noted drawback is that the existence of a countable transitive model of $ZFC$ (or of a similar set theory) is strictly stronger than the mere consistency of $ZFC$.
Given the strength of Lean as an ambient formal system, however, this is unlikely to pose a serious problem.

The second approach is attractive in several respects.
First, it yields a stronger result than the first approach: as the preceding example illustrates, proving the independence of $CH$ requires only the consistency of $ZFC$, with no need for any additional stronger assumption.
It also has constructive and finitistic advantages, since the translation of proofs induced by a forcing interpretation is essentially syntactic and finitary, and can moreover be computed by a polynomial-time function.
This is a substantively stronger result than mere independence.

Although we have not yet undertaken a mechanization of forcing for set theory, we have already used a highly simplified version of forcing to mechanize the completeness theorem for first-order logic.
The idea underlying this proof is due to Avigad @Avi01.
We briefly describe it here, assuming that the language is countable.

Let $PP$ be the set of $LK$-sequents $Gamma$ for which the judgment $LK proves not Gamma$ is not derivable.
Endow $PP$ with the relation inductively defined by the following rules. This relation is a preorder whose greatest element is the empty sequent:
$
  Xi prec.eq Xi \
  phi, psi, Gamma prec.eq Xi ==> phi and psi, Gamma prec.eq Xi \
  phi(t) prec.eq Xi ==> fal(x) phi(x), Gamma prec.eq Xi \
  Delta prec.eq Xi "and" Delta subset.eq Gamma ==> Gamma prec.eq Xi
$
If $LK proves phi$, then the Gödel--Gentzen translation gives $LJ proves phi^"GG"$.
Since Kripke semantics is sound for $LJ$, we have $p forces phi^"GG"$ for every $p in PP$.
Viewing $p forces phi^"GG"$ as a _weak forcing_ relation $p wforces phi$ yields a sound Kripke model for $LK$.
Moreover, this model is canonical in the following sense: for every formula $phi$,
$
  LK proves phi quad "iff" quad fal(p in PP) (p wforces phi)
$

#leancode[
  ```lean
  lemma complete {φ : Proposition L} : ℙ⁻ ∀⊩ᶜ φ ↔ 𝐋𝐊¹ ⊢ φ
  ```
]

Now suppose that $LK nproves not sigma$.
Since $p := {sigma} in PP$, we can construct a filter $G subset.eq PP$ that contains $p$ and is generic with respect to the following two countable families of dense sets:
$
  cal(D)_phi := & {p in PP | p wforces phi or p wforces not phi} \
  cal(H)_psi := & {p in PP | fal(q prec.eq p) (q wforces exs(x) psi(x) ==> exs(t : "term") q wforces psi(t))}
$
If the atomic formulas of the term model $frak(T)$ are interpreted according to $frak(T) models alpha <=> exs(p in G)(p wforces alpha)$, then the forcing lemma can be proved:
$
  frak(T) models phi quad "iff" quad exs(p in G)(p wforces phi)
$
#leancode[
  ```lean
  def GenericForces (p : ℙ⁻) (φ : Proposition K) : Prop := ∃ q ∈ genericFilter p, q ⊩ᶜ φ

  local infix: 60 " ⊫ " => GenericForces

  lemma forcing_lemma (φ : Semiformula K ξ n) {fv : ξ → 𝔗} {bv : Fin n → 𝔗} :
      φ.Eval (s := termModelOf p) bv fv ↔ p ⊫ Rew.bind bv fv ▹ φ :=
  ```
]
Since $G$ contains ${sigma}$ and ${sigma} wforces sigma$, it follows that $frak(T) models sigma$.
This proves the completeness theorem for $LK$.

#leancode[
  ```lean
  lemma satisfiable_of_irrefutable (σ : Sentence L) (h : 𝐋𝐊¹ ⊬ ∼(σ : Proposition L)) :
      Satisfiable {σ}
  ```
]

To develop forcing interpretations for set theory, an argument of the kind just described must be carried out _internally_ to the set theory.
As discussed in the section of incompleteness theorems (@subsubsection:internal), a direct syntactic treatment is likely to be too complex.

The same remedy may be applicable here: one can instead proceed model-theoretically via the completeness theorem.
This may make it possible to reuse the externally defined weak forcing relation $wforces$ and the general theory of Kripke models.
Moreover, such an external argument may be technically close to the forcing arguments ordinarily employed by set theorists.

== Proof theory of provability logics <subsect:proof_theory_provability_logic>

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
As far as we know, the only mechanizations of the proof theory of sequent calculi equipped with such additional machinery are the mechanization of the labelled sequent calculus in HOL Light by Maggesi and Perini Brogi @MPB21 @MPB23, along that line, Bilotta's HOLMS project @Bil25 @BMPB26 @BMPB26a, and the recent mechanization in Lean by Gignoux @Gig26 of non-wellfounded proof systems for #LogicGL, formulated coalgebraically, through which the CIP of #LogicGL is proved.

Tableau methods for #LogicGL are discussed in @Boo94[Chapter 10] for instance.
A tableau-based automated theorem prover for #LogicGL was implemented by Goré and Kelly @GK07, where the efficiency of the implementation is also discussed.

The proof theory of #LogicS and #LogicD has been developed only recently.
Sierra Miranda and Studer @SMS26 proved the Lyndon interpolation property of #LogicS using non-wellfounded proofs.
As a different approach, Kushida @Kus20 proposed a sequent calculus for #LogicS with two levels of sequents, and Kashima et al. @KK23 @KKIM25 developed this approach further, obtaining a sequent calculus for #LogicD with three levels of sequents; these are the systems we have mechanized (see @def:layered_sequent_calculi).

In the present work, we have mechanized the Gentzen-style sequent calculus for #LogicGL, the labelled sequent calculus for #LogicGL (see @sect:labelled-sequent-calculus), and the two-level sequent calculus for #LogicS together with the three-level sequent calculus for #LogicD (see @def:layered_sequent_calculi).
For future work, we plan to mechanize sequent calculi with other machinery as well, together with the equivalence of their provability.
In particular, although Shamkanov's circular proofs involve infinitary structures, the studies by Sierra Miranda et al. @SM23 @SMSZ24 @HSMS25 @SMS26 have revealed that they have many applications, so their mechanization seems to be a technically challenging but worthwhile task.
Gignoux's coalgebraic mechanization of non-wellfounded proof systems for #LogicGL @Gig26 mentioned above can be regarded as a first step in this direction.

== Provability logic of Heyting arithmetic <subsect:provlogic_of_HA>

The provability logic of intuitionistic or constructive arithmetic, in particular, Heyting arithmetic #HeytingArithmetic, has been a subject of study for a long time (see @AB05[Section 9] @BV06[Section 4]).
Even among the recent developments alone, there is prior work such as @AM18 @AM19 @SM23a @Moj24 @Moj26.

Here, we define #LogiciK and #LogiciGL.
Intuitionistic modal logic #LogiciK is obtained from intuitionistic propositional logic by adding the axiom $AxiomK$ for $Box$ and the necessitation rule (note that the language does not contain $Dia$),
and intuitionistic Gödel--Löb logic #LogiciGL is obtained by adding Löb's axiom $Box (Box A -> A) -> Box A$ to #LogiciK.
It is known that the provability logic of #HeytingArithmetic contains at least #LogiciGL, that is, #LogiciGL is arithmetically sound with respect to #HeytingArithmetic.
For purely logical studies of #LogiciGL, consult @Urs79 @Lit14 @vdGI21.
As for mechanization, Shillito and Goré @GS22 gave a refined version of the proof of cut elimination for the sequent calculus for #LogiciGL due to van der Giessen and Iemhoff @vdGI21, and this proof has been mechanized in Rocq (see also @Shi22).

On the other hand, the logic called the intuitionistic strong Löb logic #LogiciSL, obtained by adding the strong Löb axiom $(Box A -> A) -> A$ to #LogiciK, is also important.
For a survey of #LogiciSL itself as a logic, see, e.g., @VL24.
Shillito et al. @SvdGGI23 gave a new sequent calculus for #LogiciSL admitting cut elimination, and mechanized it in Rocq.
Férée et al. @FvdGvGS24 mechanized the uniform interpolation theorem for #LogiciSL in Rocq (see also @subsect:proof_theory_provability_logic).

Finally, the provability logic of Heyting arithmetic has been announced in Mojtahedi's preprint @Moj26.
However, at the time of writing, this preprint is still under review#footnote[The first version was submitted to arXiv in 2022.].
In the future, we plan to mechanize these arguments, which will make it possible to verify them rigorously and thus to settle this problem in a more reliable way.

== Enriched modalities <subsect:enrich_modalities>

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
Interpretability logic is the extension of provability logic with an additional binary modal operator $interpret$ representing interpretability (informally, $A interpret B$ means that the extended theory $T + f(A)$ interprets $T + f(B)$; see also @subsect:future_interpretability).
There are several semantics for interpretability logic, including _de Jongh--Veltman semantics_ @dJV90 and _Verbrugge semantics_ as known as _generalized Veltman semantics_ (cf. @JRMV24).
The latter one can handle completeness and definability for more axioms, but it has the drawback that the arguments become very involved.
As prior work, mechanization of frame definability for Verbrugge semantics has been carried out in Agda by Rovira @Rov20.

As for our own progress, we have mechanized syntactic proofs and frame definability for some additional axioms and weak interpretability logics based on work by Kurahashi and Okawa @KO21 #footnote[See: #link("https://github.com/FormalizedFormalLogic/InterpretabilityLogic")].
However, we have not yet established modal completeness with respect to frames, and as for the arithmetical completeness theorem, we have not been able to mechanize it at all.

// = Concluding and Future works

= Appendix: Vibe formalizing <subsect:vibe-formalizing>

We describe how the AI is used in our development.
Claude does not mechanize everything autonomously: the author first fixes the overall strategy for proving the main theorems and writes their formal statements, and only then delegates the actual proofs to Claude.
Within the proofs as well, the author gives appropriate directions and tactics, e.g., to proceed by induction on the structure of formulas or on the rules of a sequent calculus.
As a rule of thumb in pure mathematical logic, a fact proved by such an induction requires no special idea: one simply carries out the calculation, and on paper one typically works out a few representative cases and omits the rest.
In a mechanization, every case must be treated without omission; we saw little value in a human spending time on such code, so we actively delegated it to the AI.
In practice, the overall refactoring of #link(REPO_SOURCES.at("ProvabilityLogic"))[FormalizedFormalLogic/ProvabilityLogic] and the mechanization of the classification theorem were mostly completed in about three weeks of actual work, which the second author regards as a substantial gain in speed and efficiency.
