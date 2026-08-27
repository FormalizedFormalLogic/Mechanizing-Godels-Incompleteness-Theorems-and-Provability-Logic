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
  Moreover, tackling G2 requires climbing yet another level.
  One would have to work with a formal system inside a formal system inside a formal system, which is hardly practical.
/ Non-canonicity of bootstrapping:
  Bootstrapping is a formalization of metamathematics.
  This requires encoding of the metamathematical notions, the _Gödel numbering_.
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

In addition, to avoid directly handling formalized statements, such as $Pr(T)(x)$, as much as possible, we use an abstract characterization of provability predicates when discussing the derivability conditions. We discuss this in detail in @subsect:provability_abstraction.

#let num(x) = $overline(#x)$

== First incompleteness theorem
The theory $R0$ consists of the following variable-free atomic formulas in $LOR$,

$
    num(n) + num(m) = & num(n + m) wide   && "for all" n, m in Nat \
  num(n) dot num(m) = & num(n dot m) wide && "for all" n, m in Nat \
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
  Then there is a $cal(L)_"OR"$-formula $sans("Rep")_(S)(x)$ such that
  $
    n in S <==> T proves sans("Rep")_(S)(num(n))
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
  theorem incomplete
      (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : Incomplete T
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

The $ISigma1$ version of the Knaster-Tarski theorem, stated below, is useful for defining recursively defined structures over $Universe$ with appropriate complexity.

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

Practically important point is that the defining formulas of $Fix_Phi$ can be explicitly constructible from the defining formula of $P(x, c)$.
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
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Arithmetic/HFS/Fixpoint.lean#L54"
    ),
    (
      "Foundation",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/a3dd617f88bda178eb6c206dd5db91f88b6a2a42/Foundation/FirstOrder/Arithmetic/HFS/Fixpoint.lean#L59"
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
    )
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
    )
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

== Provability abstraction <subsect:provability_abstraction>

#let Godel(B) = $sans("G")_#B$
#let Con(B) = $sans("Con")_#B$

Working directly with a raw provability predicate is technically cumbersome.
We therefore introduce the notion of _provability abstraction_, an abstraction of the provability predicate.
This notion is closely related to provability logic, which treats provability as a modality (see @sect:provability_logic).
With these abstractions, the incompleteness theorems can be mechanized abstractly, by purely syntactic manipulations.
Concretely constructing a "provability" satisfying the abstract derivability conditions then immediately yields the concrete statements of the incompleteness theorems.
Mechanizing the incompleteness theorems via such an abstract provability has previously been studied by Popescu and Traytel @PT19 @PT21.

#definition[Provability predicate][
  Suppose that $cal(L)$-sentences admit a Gödel numbering in the language $cal(L)_0$.
  For an $cal(L)_0$-theory $T_0$ and an $cal(L)$-theory $T$, a unary $cal(L)_0$-semisentence $Bew(x)$ is called a _$T$-provability predicate over $T_0$_, if the following holds for every $cal(L)$-sentence $sigma$.

  #align(center, table(
    columns: (auto, auto),
    inset: 6pt,
    align: (right + horizon, left + horizon),
    stroke: none,
    $bold("D1")$, [
      $T proves sigma ==> T_0 proves Bew(GoedelNum(sigma))$
    ],
  ))

  That is, $Bew(x)$ is required to satisfy at least the derivability condition $bold("D1")$.
  In what follows, we simply write $Bew sigma$ for $Bew(GoedelNum(sigma))$.
  We further define the following properties, where $sigma$ and $pi$ range over $cal(L)$-sentences.
  The conditions $bold("D3")$ and $bold("Kre")$ are defined only when $T_0$ and $T$ are theories in the same language, i.e., when $cal(L)_0 = cal(L)$.

  #align(center, table(
    columns: (auto, auto),
    inset: 6pt,
    align: (right + horizon, left + horizon),
    stroke: none,
    $bold("D2")$, [
      $T_0 proves Bew (sigma -> pi) -> Bew sigma -> Bew pi$
    ],
    $bold("D3")$, [
      $T_0 proves Bew sigma -> Bew Bew sigma$
    ],
    $bold("Kre")$, [
      $T proves Bew sigma$ implies $T proves sigma$
    ],
    $bold("Ros")$, [
      $T proves not sigma$ implies $T_0 proves not Bew sigma$
    ]
  ))
  // - $bold("FC")$ (on an $cal(L)$-sentence $sigma$): $T_0 proves sigma -> Bew sigma$.
  // - $bold("S")$ (on an $L_0$-structure $M$) : $M models Bew sigma ==> T proves sigma$.
]

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
Anticipating the later construction, the standard provability predicate is a $Sigma_1$-predicate, so the condition $bold("Kre")$ can be regarded as a purely syntactic counterpart of the $Sigma_1$-soundness and $Sigma_1$-completeness of $T$.

In fact, abstracting provability alone does not suffice to mechanize the incompleteness theorems: we also need to abstract the diagonalization.

#let fixpoint(x) = $sans("fixedpoint")_#x$

#definition[Diagonalization abstraction][
  Suppose that $cal(L)$-sentences admit a Gödel numbering in $cal(L)$.
  An $cal(L)$-theory $T$ is called _diagonalizable_ if one can construct a map $fixpoint(bullet)$, sending an unary $cal(L)$-formula to an $cal(L)$-sentence,
  such that
  $
    T proves fixpoint(theta) <-> theta (GoedelNum(fixpoint(theta)))
  $
  for any $theta(x)$. We call $fixpoint(theta)$ the _fixed point_ of $theta$.

  Let $T_0, T$ be $cal(L)$-theories such that $T_0$ is diagonalizable, and let $Bew$ be a provability of $T_0, T$. Then the fixed point of $not Bew (x)$ is called the _Gödel sentence_ and is denoted by $Godel(Bew)$.
]

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
      "https://github.com/FormalizedFormalLogic/Foundation/blob/25dda5090b03e9d74b23d4537ca76e546c7197af/Foundation/FirstOrder/Bootstrapping/FixedPoint.lean#L130"
    ),
  )
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
    [Löb's theorem],
    [$T proves Bew sigma -> sigma$ implies $T proves sigma$.],
    [Formalized Löb's theorem],
    [$T_0 proves Bew (Bew sigma -> sigma) -> Bew sigma$.],
  ))
]

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

  theorem löb_theorem {σ : Sentence L}　(H : T ⊢ 𝔅 σ 🡒 σ) : T ⊢ σ

  theorem formalized_löb_theorem {σ : Sentence L} : T₀ ⊢ 𝔅 (𝔅 σ 🡒 σ) 🡒 𝔅 σ
  ```
]

Note that $bold("D1"), bold("D2"), bold("D3")$ and the formalized Löb's theorem correspond roughly to the necessitation rule and the axioms $AxiomK$, $Axiom("4")$, and $Axiom("L")$ of modal logic, respectively.
This yields the observation that arithmetical soundness holds for the standard provability predicate.

In view of the reason we gave for introducing $bold("Kre")$ into the abstraction, requiring $bold("Kre")$ in the abstract G1 of @prop:abstract_G1 corresponds to requiring the $Sigma_1$-soundness of $T$.
If we instead impose on $Bew$ the condition $bold("Ros")$, then the abstract G1 can be proved assuming only that $T$ is consistent.
This is precisely an abstraction of the incompleteness theorem as improved by Rosser @Ros36.

#let Rosser = $frak(R)$

#proposition[Abstract version of Gödel-Rosser theorem][
  Assume that the provability predicate $Rosser$ satisfies $bold("Ros")$.
  In this case, the Gödel sentence for $Rosser$ is called the _Rosser sentence_.
  Then we have $T nproves Godel(Rosser)$ and $T nproves not Godel(Rosser)$.
  That is, $Godel(Rosser)$ is independent of $T$; note in particular that $bold("Kre")$ is not required.
  On the other hand, for the consistency statement $Con(Rosser)$ defined above, we have $T proves Con(Rosser)$ #footnote[In the Japanese mathematical logic community, this is often called _Kreisel's remark_.].
]

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

Indeed, the concrete statement of the Gödel-Rosser theorem given later, obtained by instantiating this abstraction, does not require $Sigma_1$-soundness.

We next describe refutability (_Widerlegbar_) $Wid$.
Concerning G2, formal consistency can be expressed in ways other than the formalized consistency $not Bew bot$ introduced in @prop:abstract_G2.
For instance, the statement "no sentence is both provable and refutable" may also be regarded as a natural expression of consistency.
The version of G2 obtained by formalizing this consistency is usually attributed to Jeroslow @Jer73 #footnote[See, e.g., Kurahashi @Kur20 for how subtle differences in the required conditions, and various versions of the statement of G2, arise depending on how consistency is formalized.].
A naive attempt to formalize Jeroslow's G2 on top of the provability abstraction, however, becomes slightly cumbersome if only $Bew$ is available.
The reason is that $Bew$ is in fact an arithmetical predicate taking the Gödel number of a formula: dealing with refutability, that is, with negated sentences, would force us to handle a "function" computing the Gödel number of $not sigma$ from that of $sigma$, and such a function is awkward to accommodate within the provability abstraction.
We therefore abstract refutability itself, rather than a function computing the Gödel number of a negation.
This allows us to formalize Jeroslow's G2 concisely.

#let Jeroslow(W) = $sans("J")_#W$

#definition[Refutability abstraction][
  For an $cal(L)_0$-theory $T_0$ and an $cal(L)$-theory $T$, a unary $cal(L)_0$-semisentence $Wid(x)$ is called a _$T$-refutability predicate over $T_0$_, if the following holds for every $cal(L)$-sentence $sigma$.
  $
    T proves not sigma ==> T_0 proves Wid(GoedelNum(sigma))
  $

  As with $Bew$, we abbreviate $Wid(GoedelNum(sigma))$ as $Wid sigma$.
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

#let Safe(B,W) = $sans("Safe")_(#B,#W)$
#let FLoN(B, W) = $sans("FLoN")_(#B,#W)$

#proposition[Abstract version of Jeroslow's G2 @Jer73][
  Let $Safe(Bew,Wid) (x) equiv not (Bew x and Wid x)$ be the unary formula stating that a sentence is not both provable and refutable (_safe_), and let $FLoN(Bew, Wid) equiv forall x, Safe(Bew, Wid)(x)$ be the sentence expressing consistency in the sense that every sentence is safe (the _formalized law of non-contradiction_).

  If $T$ is consistent and $T_0 proves Jeroslow(Wid) -> Bew Jeroslow(Wid)$, then $T nproves FLoN(Bew, Wid)$.
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

== Some further results related to the incompleteness theorems

Using the tools developed so far, we have also proved several theorems related to Gödel's incompleteness theorems.

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

Taking the _true arithmetic $TrueArithmetic$_, the arithmetic theory consisting of all true arithmetic sentences,
as the theory $T$ in this lemma, we immediately obtain the desired theorem.

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
