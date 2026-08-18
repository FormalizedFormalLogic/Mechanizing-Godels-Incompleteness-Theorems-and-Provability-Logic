#import "./notations.typ": *

= Mechanization of the incompleteness theorems

We mechanized the following two results.

#theorem[Gödel's First Incompleteness Theorem @God31 @Vau62 @JS83][
  Let $T$ be a $Delta_1$-definable, $Sigma_1$-sound $LOR$-theory stronger than $R0$,
  Then $T$ is incomplete,
  that is, there exists a $LOR$-sentence $phi$ such that $T nproves phi$ and $T nproves not phi$.
]<thm:G1>

#theorem[Gödel's Second Incompleteness Theorem @God31][
  Let $T$ be a $Delta_1$-definable, $Sigma_1$-sound $LOR$-theory stronger than $ISigma1$.
  Then $T nproves Con(T)$,
  where $Con(T)$ is a consistency statement of $T$.
]<thm:G2>

The proofs largely follow the standard approach in the literature (see, for example, @HP16).
We therefore omit the details and instead comment on several technical and methodological aspects of the formalization.

=== Syntax
We use a locally nameless representation for terms and formulas of first-order logic.
A similar approach is adopted in @HvD20.

In standard logical terminology, this amounts to using _semiterms_ and _semiformulas_, which generalize terms and formulas, respectively @Bus98a.
Variable symbols are divided into two classes: free variables, denoted by $\&x, "for" x in xi$, and bound variables, denoted by $\#z, "for" z in [n]$.
A semiterm is a term generated using variables of these two kinds.
A semiformula is generated from semiterms in the usual way, but may contain bound variables that are not bound by any quantifier.
We formalized the type of semiformulas that may contain free variables of type $xi$ and $n$ bound variables as `Semiformula L ξ n`.

#leancode(
  links: (
    ("Foundation", "Foundation/FirstOrder/Basic/Syntax/Formula.lean#L24-L32"),
  ),
  note: [
    We write `Formula L ξ` for `Semiformula L ξ 0`, and `Sentence L` for sentences, namely `Formula L Empty`.
  ],
)[
  ```
  inductive Semiformula (L : Language) (ξ : Type*) :
      ℕ → Type _ where
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

Formalization using semiformulas is more than a technical device for defining formulas; it also offers practical advantages.
For example, a condition frequently encountered in proof theory and model theory, such as a formula $A[x, y, z]$ with parameters from $M$, can be expressed by the single type `Semiformula M 3`.

=== On internal argument
In proofs of the incompleteness theorems, especially G2, the principal obstacle is often the internalization of metamathematics---terms, formulas, provability, elementary proof theory, and so forth---a process commonly called arithmetization or bootstrapping.
In other words, these notions must be formally defined and their properties proved within the formalized deductive system itself, which in our case is $ISigma1$.
A naive, purely syntactic approach to this task encounters the following difficulties#footnote[
  Nevertheless, carrying out such a construction is worthwhile.
  These syntactic operations are constructive and can be developed over very weak base theories, such as $sans("S")^1_2$.
].

/ Bureaucracy of the deductive system: When sufficiently complex formulas are involved, the deductive system can become unmanageably intricate.
  A task that is already difficult to formalize directly in Lean becomes exceedingly burdensome when it must instead be carried out within a still more restrictive formal system defined in Lean.
  Moreover, we must manipulate metamathematical notions that have themselves been formalized internally, such as formalized provability. This is scarcely practical.
/ Non-canonicity of bootstrapping:
  Bootstrapping is primarily concerned with the formalization of metamathematics.
  This requires encoding the relevant notions, the _Gödel numbering_.
  Unfortunately, there is neither a canonical choice of encoding nor a unique mathematically natural construction.
  One must instead develop a large body of intrinsically complicated combinatorics, often involving numerous ad hoc constructions...
  This complicates the proofs and, for the reasons just discussed, makes mechanization difficult.

Our solution is to avoid syntactic bureaucracy by employing a model-theoretic argument via the completeness theorem.
This largely resolves the first problem. Although it does not eliminate the second, it mitigates its complexity to some extent.

In the weak mathematics considered here, one frequently needs to track restrictions on formula complexity, as in $ISigma1$.
With a model-theoretic argument, however, it is unnecessary to exhibit an actual formula; it suffices to establish that the predicate in question is definable in appropriate complexity.
As discussed below, we designed this part of the development so that it can be handled almost automatically using Aesop @LF23.
Thus, the bureaucratic overhead of syntax, especially that associated with (external) formulas, can be _almost_ eliminated.
There nevertheless remain situations in which a concrete formula must be supplied.
For example, the second incompleteness theorem asserts $T nproves Con(T)$, and stating this result requires an explicit, model-independent formula $Con(T)$.

#let num(x) = $overline(#x)$

== First incompleteness theorem
The theory $R0$ consists of the following variable-free graphs and literals in $cal(L)_"OR" = {0, 1, +, dot, <, =}$,

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
Define the set $D$ by $godel(phi[x]) in D <==> T proves not phi[godel(phi[x])]$.
As shown below, there is a provability predicate $Pr(T)[x]$, definable by a $Sigma_1$-formula, such that
$Nat models Pr(T)[godel(phi)] <==> T proves phi$; hence $D$ is r.e.
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
This theory is in fact unnecessarily strong. For a sharper result, one could weaken the base theory to Buss's theory $sans("S")^1_2$, over which the standard proof can be carried out with few changes#footnote[
  In many proofs, including ours, derivability condition D3 is established using formalized $Sigma_1$-completeness.
  Whether this principle holds in $sans("S")^1_2$ remains an open problem @BV06a.
  One must therefore prove the sharper formalized $Sigma^"b"_1$-completeness theorem.
].
Moreover, Nelson's interpretation $Robinson triangle.small.r sans("S")^1_2$ extends the second incompleteness theorem to a broad class of theories that interpret Robinson arithmetic $Robinson$ @Vis11.
Although this is an appealing direction, we do not pursue it because it would make the formalization prohibitively complex.
Working in $ISigma1$ makes recursive definitions of predicates and functions easier to handle, since @thm:recursive-def is available.

As noted above, our internal arithmetical arguments are carried out in an arbitrarily fixed model of $ISigma1$, which we henceforth denote by $Universe$.

Because only induction restricted to $Sigma_1$-formulas is available over $Universe$, the ($Sigma_i$-, $Pi_i$-, and $Delta_i$-) definability of relations and functions on $Universe$ is technically important.
In practice, this can often be inferred automatically from the stated definition.
To automate the substantial amount of such reasoning required by the proofs, we make extensive use of Aesop @LF23 whenever no explicit defining formula is needed.

Let $Bit(x, y)$ be the predicate asserting that the $x$-th digit in the binary expansion of $y$ is $1$.
Ackermann coding, obtained from the membership relation defined below, provides a means of representing hereditarily finite sets within arithmetic @Pet09.
$
  x in y <==> Bit(x, y)
$
To work with $Bit(x, y)$ in weak arithmetic, we also mechanized the well-known fact that the graph of exponentiation is representable by a $Delta_0$-formula and that its inductive properties are provable in $Ind(Delta_0)$ @GD82.

The following theorem is useful for handling recursively defined structures, such as terms and formulas, over $Universe$.
It states that predicates defined recursively with parameters from $Universe$ can be constructed together with the requisite definability properties.

#theorem[Recursive definition][
  Let $Phi(bold(C); arrow(v), x)$ be a predicate over $Universe$ which takes a class $bold(C) subset.eq Universe$ as a parameter.
  Assume that this satisfies following conditions.
  / Definability: A predicate $P(c, arrow(v), x) := Phi({z | z in c}; arrow(v), x)$ is $Delta_1$.
  / Monotonicity: $bold(C) subset.eq bold(C')$ and $Phi(bold(C); arrow(v), x)$ implies $Phi(bold(C'); arrow(v), x)$.
  / Finiteness: If $Phi(bold(C); arrow(v), x)$ holds, then there is $m in V$, such that $Phi({z in bold(C) | z < m}; arrow(v), x)$ holds.
  Then we have a $Sigma_1$-predicate $"Fix"_Phi (arrow(v), x)$ such that
  $
    "Fix"_Phi (arrow(v), x) <==> Phi({z | "Fix"_Phi (arrow(v), z)}; arrow(v), x)
  $
  Additionally, if it satisfies following condition, $"Fix"_Phi (arrow(v), x)$ is $Delta_1$.
  / Strong finiteness: If $Phi(bold(C); arrow(v), x)$ holds, then $Phi({z in bold(C) | z < x}; arrow(v), x)$ holds.
]<thm:recursive-def>

This predicate also satisfies the following structural induction principle.

#theorem[Induction of recursive definition][
  Assume that $Phi$ satisfies the strong finiteness property.
  The predicate $"Fix"_Phi$ above satisfies the induction principle of following form.
  Let $psi$ be a $Sigma_1$ or $Pi_1$-predicate (which may contains parameters from $Universe$) and $arrow(v) in Universe$:
  $
    fal(bold(C) subset.eq Universe)[fal(y in bold(C))("Fix"_Phi (arrow(v), y) and psi(y)) -> fal(x in Universe)[Phi(bold(C), arrow(v), x) -> psi(x)]]
  $
  implies
  $
    fal(x in Universe)["Fix"_Phi (arrow(v), x) -> psi(x)]
  $
]

To obtain explicit predicates such as $sans("IsFormula")[x]$ and $Pr(T)[x]$, we must also provide the defining formulas whose existence is guaranteed by the corresponding definability properties.
In the mechanization, we first call such a formula---the syntactic essence of a recursive definition---a `Blueprint k`.
A blueprint is independent of any model.
We then define `Construction (φ : Blueprint k)`, the model-theoretic realization of a `Blueprint k`.

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

Metamathematical structures such as terms, formulas, and proofs are all recursively generated and can therefore be constructed using `Blueprint` and `Construction`.
Moreover, because these structures are generated in a well-founded manner, they satisfy the strong finiteness property.
It follows uniformly that the corresponding predicates are $Delta_1$-definable and satisfy appropriate structural induction principles.
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

The crucial ingredient in the proof of the second incompleteness theorem is that the provability predicate $Pr(T)(x)$ satisfies the derivability conditions.
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

生の証明可能性述語を扱うのは技術的に扱いが面倒で取り回しが悪い．
そのため，我々は証明可能性述語を抽象化したprovability abstractionという概念を導入する．
このprovability abstractionは，証明可能性を様相として捉える証明可能性論理（@sect:provability_logic で議論する）と非常に関係が深い．
これらの抽象化を用いることで，我々は不完全性定理を純粋な構文論的な操作によって抽象的に形式化出来る．
抽象化された導出可能性条件などを満たす "provability" を具体的に構成することによって，我々は実際のコンクリートな不完全性定理の主張を即座に得ることが出来る．
このようなabstractなprovabilityによる不完全性定理の形式化の議論は Popescu and Traytel @PT19 @PT21 らの先行研究がある．

#definition[Provability abstraction][
  言語 $cal(L)$ は言語 $cal(L)_0$ に対するGödel numberingが可能であるとする．
  $cal(L)_0$-理論 $T_0$ と $cal(L)$-理論 $T$ に対し，unary な $cal(L)_0$-論理式 $Bew(x)$ が $T_0, T$ のprovabilityであるとは，任意の $cal(L)$-文に対して以下が成立することとする．
  $
    T proves sigma ==> T_0 proves Bew(GoedelNum(sigma))
  $
  つまり，$Bew(x)$ は最低限の導出可能性条件 $bold("D1")$ を持つものとする．
  以下では $Bew(GoedelNum(sigma))$ は単に $Bew sigma$ と書くことにする．
  更に，以下の性質を定める．

  - $bold("D2")$: 任意の $cal(L)$-文 $sigma, pi$ に対して，$T_0 proves Bew (sigma -> pi) -> Bew sigma -> Bew pi$．
  - $bold("D3")$: $T_0$ と $T$ は同じ $cal(L)$-理論とする．任意の $cal(L)$-文 $sigma$ に対して，$T_0 proves Bew sigma -> Bew Bew sigma$．
  - $bold("Kre")$: $T_0$ と $T$ は同じ $cal(L)$-理論とする．任意の $cal(L)$-文 $sigma$ に対して，$T proves Bew sigma ==> T proves sigma$．
  - $bold("Ros")$: 任意の $cal(L)$-文 $sigma$ に対して，$T proves not sigma ==> T_0 proves not Bew sigma$．
  // - $bold("FC")$ (on $cal(L)$-文 $sigma$): $T_0 proves sigma -> Bew sigma$．
  // - $bold("S")$ (on $L_0$-structure $M$) : 任意の $cal(L)$-文 $sigma$ に対して，$M models Bew sigma ==> T proves sigma$．
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

後述する標準的な方法により構成する standard なprovability $Bew_T$ は $bold("D2")$ と $bold("D3")$ を満たす．
@sect:provability_logic で議論する証明可能性論理は主にstandardなprovabilityによって議論する．
条件 $bold("Kre")$ はVisser @Vis21 でKreisel's conditionと呼ばれて導入された導出可能性条件である #footnote[Visserはこの条件の由来を @Kre54 に帰している．また正確には，Visserは両側を要請していた．]．
いま，この抽象化のモチベーションとして，純粋に構文論的な方法によって議論を形式化(formalize)したいので，model / structureに関与したくない．
天下り的に構成を先取りすると，実際に後で構成するstandardな $Bew$ は $Sigma_1$-述語であるから，条件 $bold("Kre")$ は理論 $T$ の $Sigma_1$-健全性および完全性の純粋に構文論的な対応物と見做せる．

さて，実際にはprovabilityの抽象化のみでは不十分で，理論の対角化可能性についても抽象化する必要がある．

#definition[Diagonalization abstraction][
  言語 $cal(L)$ は $cal(L)$ 自身に対するGödel numberingが可能であるとする．
  $cal(L)$-理論 $T$ がdiagonalizableであるとは，$cal(L)$-semisentence を受け取り $cal(L)$-sentenceを返す写像 $upright("fixpoint")_T$ であって，
  任意の $cal(L)$-semisentence $theta$ に対し $T proves upright("fixpoint")_T (theta) <-> theta (GoedelNum(upright("fixpoint")_T (theta)))$ が構成できることを言う．$upright("fixpoint")_T (theta)$ を $theta$ の不動点と呼ぶ．

  $cal(L)$-理論 $T_0, T$ で，$T_0$ はdiagonalizableであり，$Bew$ を $T_0, T$ のprovabilityとしたとき，$not Bew (x)$ の不動点をGödel文と呼んで $upright("G")_Bew$ と表す．
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

これらの道具立てを用意することによって，不完全性定理やそれらの系などを構文論的な操作によって証明することが可能である．
以降では，$cal(L)$-理論 $T_0 subset.eq T$ とし， $T_0$ はdiagonalizable，$T$ は consistentとする．
また $Bew$ を $T_0, T$-provabilityとしよう．
まず，第1不完全性定理は以下のように示される．

#proposition[Abstract version of G1][
  1. $T nproves upright("G")_Bew$．
  2. $Bew$ が $bold("Kre")$ を満たすなら $T nproves not upright("G")_Bew$．故に $upright("G")_Bew$ は $T$ の独立命題であり，そして $T$ は不完全である．
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

  theorem unprovable_gödel : T ⊬ (gödel 𝔅)

  theorem unrefutable_gödel [𝔅.Kreisel] : T ⊬ ∼(gödel 𝔅)

  theorem gödel_independent [𝔅.Kreisel] : Independent T (gödel 𝔅)

  theorem first_incompleteness [𝔅.Kreisel] : Incomplete T
  ```
]

更に，第2不完全性定理に関しても以下のように形式化出来る．

#proposition[Abstract version of G2][
  $Bew$ は $bold("D2")$ と $bold("D3")$ を満たすと仮定する．
  いま，$not Bew bot$ という文は自然な無矛盾性の表現の1つである．これを $upright("Con")_Bew$ とする．
  さてこのとき以下が成立する．
  1. $T nproves upright("Con")_Bew$．
  2. $Bew$ が $bold("Kre")$ を満たすなら $T nproves not upright("Con")_Bew$．故に $upright("Con")_Bew$ も $T$ の独立命題である．
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

ここで，$upright("Con")_Bew$ だけが無矛盾性を表す自然な表現ではないという観点も存在する．
そのような点についてのG2のvariantについては後述する．
さて，より発展的な事実としてLöbの定理，およびその系として形式化(formalized)された不完全性定理やLöbの定理も形式化出来る．

#proposition[Abstract version of Löb's Theorem and formalized theorems][
  $Bew$ は $bold("D2")$ と $bold("D3")$ を満たすとする．このとき以下が成立する．
  文 $sigma$ は任意の $cal(L)$-文 $sigma$ とする．

  / Löb's theorem: $T proves Bew sigma -> sigma$ ならば $T proves sigma$．
  / Formalized Löb's theorem: $T_0 proves Bew (Bew sigma -> sigma) -> Bew sigma$．

  更に$Bew$ が $bold("Kre")$ を満たすとすると，以下が成立する．

  / Formalized G1: $T nproves upright("Con")_Bew -> not Bew not upright("G")_Bew$
  / Formalized G2: $T nproves upright("Con")_Bew -> not Bew not upright("Con")_Bew$
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

  lemma formalized_unrefutable_gödel [Consistent T] [𝔅.Kreisel] : T ⊬ 𝔅.con 🡒 ∼𝔅 (∼(gödel 𝔅))

  lemma formalized_unprovable_not_con [Consistent T] [𝔅.Kreisel] : T ⊬ 𝔅.con 🡒 ∼𝔅 (∼𝔅.con)
  ```
]

$bold("D1"), bold("D2"), bold("D3")$ およびformalized Löb's theoremが，それぞれ様相論理のネセシテーション規則，公理 $AxiomK$，公理 $Axiom("4")$，公理 $Axiom("L")$ と概ね対応していることに注意しておこう．
この事実は標準的なprovability $Bew_T$ で算術的健全性が成立する観察を与える．

抽象化において $bold("Kre")$ の導入を述べた理由を踏まえると，@prop:abstract_G1 で示した抽象的なG1について $bold("Kre")$ が要請されていることはおおまかには $T$ の $Sigma_1$-健全性を要請することと等しいと言える．
しかし $Bew$ に $bold("Kre")$ ではなく別の条件 $bold("Ros")$ を要請すれば $T$ がconsistentであるという要請のみでabstractなG1を示すことが出来る．
これはまさにRosserによって改良化された不完全性定理 @Ros36 の抽象化になる．

#proposition[Abstract version of Gödel-Rosser theorem][
  $Bew$ は $bold("Ros")$ を満たすとする．
  この $Bew$ によるGödel文を，特別にRosser文 $upright("R")_Bew$ と呼ぶことにする．
  このとき $T nproves upright("R")_Bew$ かつ $T nproves not upright("R")_Bew$ が成立する．
  つまり $upright("R")_Bew$ は独立命題．特に後者に関して $bold("Kre")$ を要請しない．
  しかし，この $Bew$ による無矛盾性 $upright("Con")_Bew$ について，$T proves upright("Con")_Bew$ である #footnote[日本の数理論理学のコミュニティでは Kreisel's remarkとかと呼ばれる．]．
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

実際に，この抽象化を具体化した結果として得られる，後述する具体的なGödel-Rosserの定理のステートメントには $Sigma_1$-健全性を要請しない．

refutability (Widerlegbar) $Wid$ についても述べておこう．
G2について，@prop:abstract_G2 で導入したformalized consistency $not Bew bot$ 以外にも，異なる方法で形式的な無矛盾性を表現することが可能である．
例えば「任意の文に対して，証明可能かつ反証可能であることはない」という言明もまた無矛盾性を自然に表していると言える．
この無矛盾性を形式化することで得られるG2は通常Jeroslow @Jer73 に帰する #footnote[無矛盾性をどのように形式化するかによって要請される条件の微妙な相違やG2のステートメントの様々なversionが得られるという緊張関係については，例えばKurahashi @Kur20 などを参照しなさい．]．
さてこのJeroslowのG2をprovability abstraction上で素朴に形式化しようとすると，$Bew$ のみでは微妙に面倒な形式化(formalize)が要求される．
なぜなら，$Bew$ は実際には論理式のGödel数を受け取る算術上の述語であるから，反証可能性，つまり否定文を扱うとなると文 $sigma$ のGödel数から $not sigma$ のGödel数を得る"関数"を取り扱わなければならず，その抽象化をprovability abstraction内で議論するのはやや面倒である．
そこで我々はこのような否定のGödel数を計算する関数の抽象化ではなく，refutabilityそのものを抽象化する．
これによってJeroslowのG2を簡潔に形式化出来る．

#definition[Refutability abstraction][
  $cal(L)_0$-理論 $T_0$ と $cal(L)$-理論 $T$ に対し，unary な $cal(L)_0$-semisentence $Wid(x)$ が $T_0, T$ のrefutabilityであるとは，任意の $cal(L)$-文に対して以下が成立することとする．
  $
    T proves not sigma ==> T_0 proves Wid(GoedelNum(sigma))
  $

  やはり $Bew$ と同様に $Wid(GoedelNum(sigma))$ は $Wid sigma$ と略して書く．
  $Wid$ が $cal(L)$-文 $sigma$ に対してsoundであるとは，$T proves Wid sigma ==> T proves not sigma$ が成立することとする．

  $Wid$ を $T_0, T$-refutabilityとして，$T_0$ がdiagonalizableであるとき，$Wid(x)$ の不動点を Jeroslow文と呼んで $upright("J")_Wid$ で表す．
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

Jeroslow文に関して，すぐに次のことはわかる．

#proposition[
  $T$ が無矛盾かつ，$Wid$ が $upright("J")_Wid$ に対してsoundであるとき，$T nproves upright("J")_Wid$．
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

さて，Jeroslowの不完全性定理について述べる．

#proposition[Abstract version of Jeroslow's G2 @Jer73][
  "証明できてかつ反証可能であることはない" という事態 (_safe_) の形式化を表すsemisentence $upright("Safe")_(Bew,Wid) (x) equiv not (Bew x and Wid x)$ とし，すべての文がsafeであるという意味での無矛盾性 (_formalized law of non-contradiction_) を表す文 $upright("FLoN")_(Bew, Wid) equiv forall x, upright("Safe")_(Bew, Wid)(x)$ とする．

  このとき， $T$ が無矛盾かつ $T_0 proves upright("J")_Wid -> Bew (upright("J")_Wid)$ なら，$T nproves upright("FLoN")_(Bew, Wid)$．
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

この抽象化を具体的にすること，つまり，所望のprovability $Bew$ や refutability $Wid$ を実際に構成することが次節以降の目標になる．

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
