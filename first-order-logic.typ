#import "./notations.typ": *

= Mechanization of the incompleteness theorems

We mechanized the following two results.
Here, arithmetic sentence/theory means a sentence/theory in the language $LOR = {0, 1, +, dot, <, =}$. 

#theorem[Gödel's First Incompleteness Theorem @God31 @Vau62 @JS83][
  Let $T$ be a $Delta_1$-definable, $Sigma_1$-sound arithmetic theory stronger than $R0$,
  Then $T$ is incomplete,
  that is, there exists a arithmetic sentence $phi$ such that $T nproves phi$ and $T nproves not phi$.
]<thm:G1>

#theorem[Gödel's Second Incompleteness Theorem @God31][
  Let $T$ be a $Delta_1$-definable, $Sigma_1$-sound arithmetic theory stronger than $ISigma1$.
  Then $T nproves Con(T)$,
  where $Con(T)$ is a consistency statement of $T$.
]<thm:G2>

The proofs largely follow the standard approach using derivability conditions in the literature (see, for example, @HP16).
We therefore omit the details and instead comment on several technical and methodological aspects of the formalization.

=== Syntax
We use a locally nameless representation for terms and formulas of first-order logic.
A similar approach is adopted in @HvD20.

In standard logical terminology, this amounts to using _semiterms_ and _semiformulas_, which generalize terms and formulas, respectively @Bus98a.
Variable symbols are divided into two classes: infinite _free variables_ and finite _bound variables_.
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
For example, a frequently encountered situation in proof theory and model theory, such as a formula $phi(x, y, z)$ with parameters from $M$, can be expressed by the solely type `Semiformula M 3`.

=== On internal argument
In proofs of the incompleteness theorems, especially G2, the principal obstacle is often the internalization of metamathematics---terms, formulas, provability, elementary proof theory, and so forth---a process commonly called _arithmetization_ or _bootstrapping_.
In other words, these notions must be formally defined and their properties proved _within_ the formalized deductive system itself, which in our case is $ISigma1$.
A naïve, purely syntactic approach to this task encounters the following difficulties#footnote[
  Nevertheless, carrying out such a construction is worthwhile.
  These syntactic operations are constructive and can be developed over very weak base theories, such as $sans("S")^1_2$.
].

/ Bureaucracy of the deductive system:
  When sufficiently complex formulas are involved (which is most of the case in practice), the deductive system can become unmanageably intricate.
  A task that is already difficult to formalize in Lean becomes exceedingly burdensome when it must instead be carried out within a still more restrictive formal system defined in formal system (Lean).
  さらに，G2 に取り組むには階段をさらに上る必要がある．
  formal system の中で定義された formal system のなかで定義された formal system を扱うことが求められるが，これはほとんど現実的でない．
/ Non-canonicity of bootstrapping:
  Bootstrapping is a formalization of metamathematics.
  This requires encoding the metamathematical notions, the _Gödel numbering_.
  Unfortunately, there is neither a canonical choice of encoding nor a unique mathematically natural construction.
  One must instead develop a large body of intrinsically complicated combinatorics, often involving numerous ad-hoc constructions...
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

加えて， $Pr(T)(x)$ のような怪物的複雑さをもつ formalized statements を直接扱うことをできるだけ避けるため，Derivability condition に関する議論においては provability predicate に関する abstract characterization を用いる．これについては ... で詳しく述べる．

#let num(x) = $overline(#x)$

== First incompleteness theorem
The theory $R0$ consists of the following variable-free atomic formulas in $LOR$,

$
    num(n) + num(m) = & num(n + m) wide   && "for all" n, m in Nat \
  num(n) dot num(m) = & num(n dot m) wide && "for all" n, m in Nat \
             num(n) < & num(m) wide       && "for all" n, m in Nat "such that" n < m \
        num(n) eq.not & num(m) wide       && "for all" n, m in Nat "such that" n eq.not m \
$
together with the following axiom scheme:
$
  fal(x)[x < num(n) <-> or.big_(i < n) (x = num(i))]
$

The key theorem is that every $Sigma_1$-sound theory extending $R0$ has a weak representation of every recursively enumerable (r.e.) predicate @Vau62,@JS83.
More precisely:

#theorem[
  Let $T supset.eq R0$ be a $Sigma_1$-sound theory and let $S$ be a r.e. set.
  Then there is a $cal(L)_"OR"$-formula $Rho_(S)(x)$ such that
  $
    n in S <==> T proves Rho_(S)(num(n))
  $
]<thm:repr>

Let $godel(bullet)$ denote a Gödel coding of formulas.
Define the set $D$ by $godel(phi) in D <==> T proves not phi(godel(phi))$.
As shown below, there is a provability predicate $Pr(T)(x)$, definable by a $Sigma_1$-formula, such that
$Nat models Pr(T)(godel(psi)) <==> T proves psi$; hence $D$ is r.e.
Theorem @thm:G1 now follows from @thm:repr by the standard diagonal argument.

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/ee84d9d25d88aec25a0c6b5203881e8515437f40/Foundation/FirstOrder/Incompleteness/First.lean#L16",
    ),
  ),
  note: [
    Here `Incomplete T` is a abbreviation of `∃ φ, T ⊬ φ ∧ T ⊬ ∼φ`.
  ],
)[
  ```
  theorem incomplete (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    Incomplete T :=
  ```
]

== Second incompleteness theorem

#let Universe = $bold(upright(V))$
#let Bit = $"Bit"$

We take $ISigma1$ as the base theory for our proof of the second incompleteness theorem.
This theory is in fact unnecessarily strong. For a sharper result, one could weaken the base theory to Buss's theory $sans("S")^1_2$ @Bus86, over which the standard proof can be carried out with few changes#footnote[
  In many proofs, including ours, derivability condition D3 is established using formalized $Sigma_1$-completeness.
  Whether this principle holds in $sans("S")^1_2$ remains an open problem @BV06a.
  One must therefore prove the sharper formalized $Sigma^"b"_1$-completeness theorem.
].
Moreover, Nelson's interpretation $Robinson triangle.small.r sans("S")^1_2$ extends the second incompleteness theorem to a broad class of theories that interpret Robinson arithmetic $Robinson$ @Vis11.
Although this is an appealing direction, we do not pursue it because it would make the mechanization prohibitively complex.
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

The $ISigma1$-restricted version of the Knaster-Tarski theorem, stated below, is useful for defining recursively defined structures over $Universe$ with appropriate complexity.

#let Fix = $bold("Fix")$

#theorem[Version of the Knaster-Tarski theorem][
  Let $Phi: cal(P)(Universe) -> cal(P)(Universe)$ be a class-valued function.
  Assume that this satisfies the following conditions.
  / Definability: A predicate $P(x, c) := x in Phi({z | z in c})$ is $Delta_1$-definable with parameters.
  / Monotonicity: $bold(C) subset.eq bold(C')$ implies $Phi(bold(C)) subset.eq Phi(bold(C'))$.
  / Finiteness: If $x in Phi(bold(C))$ holds, then $x in Phi({z in bold(C) | z < m})$ holds for some $m in Universe$.
  Then we have a $Sigma_1$ class $Fix_Phi$ such that
  $
    Phi(Fix_Phi) = Fix_Phi
  $
  Additionally, if it satisfies following condition, $Fix_Phi$ is $Delta_1$.
  / Strong finiteness: If $x in Phi(bold(C))$ holds, then $x in Phi({z in bold(C) | z < x})$ holds.
]<thm:recursive-def>

This satisfies the following structural induction principle.

#theorem[Structural induction][
  Assume that $Phi$ satisfies the strong finiteness property.
  The predicate $Fix_Phi$ above satisfies the induction principle of following form.
  Let $psi$ be a $Sigma_1$ or $Pi_1$-predicate (which may contains parameters from $Universe$):
  $
    fal(bold(C) subset.eq Fix_Phi)[fal(x in bold(C))psi(x) -> fal(x in Phi(bold(C)))psi(x)]
    quad "implies" quad
    fal(x in Fix_Phi)psi(x)
  $
]<thm:recursive-ind>

Practically important point is that the defining formulas of $Fix_Phi$ can be explicitly constructible from the defining formulas of $P(x, c)$.
In the mechanization, we first call such a formula a `Blueprint k` (`k` is a number of parameters).
Obviously it is purely syntactic and independent of any model.
We then define `Construction V φ`, the model-theoretic realization of a `φ : Blueprint k`.
Our mechanization of @thm:recursive-def and @thm:recursive-ind is stated with
these two parameters.

#leancode(
  links: (
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/FirstOrder/Arithmetic/HFS/Fixpoint.lean",
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
  ),
)[
  ```
  variable {L : Language} [L.Encodable] [L.LORDefinable]

  instance IsSemiformula.definable : 𝚫₁-Relation[V] (IsSemiformula L)

  instance Proof.definable {T : Theory L} [T.Δ₁] : 𝚫₁-Relation[V] (Proof T)
  ```
]

The crucial ingredient in the proof of G2 is that the provability predicate $Pr(T)(x)$ satisfies the derivability conditions.
Their verification is routine.

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
  ```
]

Finally, the second incompleteness theorem follows by the usual argument from the derivability conditions.

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

== Some further results related to the incompleteness theorems

Using the tools developed so far, we have also proved several theorems related to Gödel's incompleteness theorems.

=== Tarski's Undefinability Theorem

As a corollary of the fixed point theorem, we can prove Tarski's theorem on the undefinability of truth.
First, we prove the following lemma.

#lemma[
  Let $T supset.eq ISigma1$ be a consistent theory.
  Then there is no predicate $tau(x)$ such that $T proves sigma <-> tau(godel(sigma))$ for any sentence $sigma$.
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

Taking True Arithmetic $TrueArithmetic$ as the theory $T$ in this lemma, we immediately obtain the desired theorem.

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

In contrast to this theorem, it is known that for a complexity class $Gamma$ of formulas, there is a partial truth predicate $TruePartial(Gamma, x)$, obtained by replacing "for any sentence" with "for any $Gamma$-sentence" in the definition of $True(x)$, which is itself definable by a $Gamma$-formula (cf. @HP16).
However, this fact has not been mechanized yet.
We mention that, consequently, several statements of provability logic that are proved by using partial truth predicates have not been mechanized so far.
We will discuss this point further in @subsect:remaining_sorry_in_provlogic.
