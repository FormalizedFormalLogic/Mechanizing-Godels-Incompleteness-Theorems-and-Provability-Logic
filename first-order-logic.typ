#import "./notations.typ": *

= First-Order Logic and Arithmetic

This section introduces the first-order framework used in our formalization.
We first describe the representation of syntax, derivability, and semantics, and then turn to the arithmetical notions needed to state the incompleteness theorems.

== Syntax

We represent first-order syntax using a locally nameless representation.
Thus variables are divided into two kinds: free variables, written informally as $\&x$, and bound variables, written $\#x$.
Free variables are named by an external type `ξ`, while bound variables are represented by de Bruijn indices.

To express this formally, formulas are defined from the generalized form _semiformula_ @Buss1998.

#definition[Semiterm and Semiformula][
  Fix a set of free-variables $xi$, and let $cal(L)$ be a first-order language.
  - _Semiterms_ of language $cal(L)$ are defined inductively as follows:
    $
      t ::= \&x | \#z | f(t, ..., t)
    $
    where $x in xi$ is a _free-variable_, $z in Nat$ is a _bound-variable_, and $f$ is a function symbol in $cal(L)$.
  - _Semiformulas_ of language $cal(L)$ are defined inductively as follows:
    $
      A ::= top | bot | R(t_1, ..., t_n) | overline(R)(t_1, ..., t_n) | A and A | A or A | forall A | exists A
    $
    where $R$ is a relation symbol in $cal(L)$, and $t_i$ are _semiterms_ of $cal(L)$.
]

#leancode(links: (
  ("Foundation", "Foundation/FirstOrder/Basic/Syntax/Formula.lean#L24-L32"),
  ),
  note:[
    We write `Formula L ξ` for `Semiformula L ξ 0`, and `Sentence L` for sentences, namely `Formula L Empty`.
  ])[
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

量化子はその位置から見て $0$-番目の bound variables を束縛する；
すなわち， $forall A$ なる論理式の最外の $forall$ は，
$A$ に $n$ 個のネストした quantifier があるならば bounded-variable $\#n$ を束縛する．

以降 bound or free-variable $x, y$, (semi)term $t, u$, (semi)formula $phi$ について，
論理式の代入を $phi[t \/ x, u \/ y]$ のように表記する．

== First-Order Sequent Calculus

規則の簡易さのため，ここでは one-sided な場合の sequent calculus を用いる．

#definition[$LK1$][
  The _one-sided sequent calculus $LK1$_ consists of the following rules:
  #align(center, table(
    columns: (auto, auto, auto, auto),
    stroke: none,
    inset: 8pt,
    align: center,
    [
      #prooftree(
        rule(
          name: "identity",
          $proves phi, not phi$
        )
      )
    ],
    [
      #prooftree(
        rule(
          name: "cut",
          $proves Gamma, Delta$,
          $proves Gamma, phi$,
          $proves not phi, Delta$,
        )
      )
    ],
    [
      #prooftree(
        rule(
          name: "contraction",
          $proves Gamma$,
          $proves Delta$,
        )
      )
      ($Delta subset.eq Gamma$)
    ],
    [
      #prooftree(
        rule(
          name: "verum",
          $proves top$
        )
      )
    ],
    [
      #prooftree(
        rule(
          name: $or$,
          $proves phi or psi, Gamma$,
          $proves phi, psi, Gamma$,
        )
      )
    ],
    [
      #prooftree(
        rule(
          name: $and$,
          $proves phi and psi, Gamma$,
          $proves phi, Gamma$,
          $proves psi, Gamma$,
        )
      )
    ],
    [
      #prooftree(
        rule(
          name: $forall$,
          $proves forall phi, Gamma$,
          $proves "free"(phi), Gamma^+$,
        )
      )
    ],
    [
      #prooftree(
        rule(
          name: $exists$,
          $proves exists phi, Gamma$,
          $proves phi[t], Gamma$,
        )
      )
    ]
  ))
  A _$cal(L)$-theory_ is a set of $cal(L)$-sentences.
  For a theory $T$ and a sentence $sigma$, _$T$ proves $sigma$_, denoted $T proves sigma$,
  if there is a finite list of sentences $phi_1, ..., phi_n$ in $T$ such that a sequent
  $proves not phi_1, ..., not phi_n, sigma$ is provable in $LK1$.
]

#leancode(links: (
  ("Foundation", "Foundation/FirstOrder/Basic/Calculus.lean#L28-L41"),
  ("Foundation", "Foundation/FirstOrder/Basic/Calculus.lean#L28-L41"),
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

  structure Theory.Proof (T : Theory L) (σ : Sentence L) where
    axioms : List (Sentence L)
    axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
    derivation :
      OneSidedLK.Pullback Derivation Rewriting.emb (σ :: ∼axioms)
  ```
]

$forall$-規則の uppersequent $"free"(phi), Gamma^+$ はその eigenvariable を常にフレッシュに取るための手続きである．
$phi^+$ は $phi$ に現れる free-variable $\&x$ をすべて $\&(x+1)$ に置き換えたもの，
$Gamma^+ := phi_1^+, ..., phi_n^+$, ($Gamma = phi_1, ..., phi_n$)， $"free"(phi) := phi^+[\&0 \/ \#0]$ と定義する．

The completeness theorem is proved by a bit non-standard way #footnote[A forcing argument.].

#leancode(links: (
  ("Foundation", "Foundation/FirstOrder/Completeness/CounterModel.lean#L253"),
  ),
)[
  ```
  theorem Proof.complete_iff : T ⊨ φ ↔ T ⊢ φ
  ```
]

This theorem is technically important for our mechanization of the incompleteness theorems, as it allows us to reduce the syntactic provability,
which is often too complex, to the semantic truth in a model, which is often easier to handle.

== Arithmetic

第二不完全性定理を証明するにあたって基礎となる体系として，ここでは $ISigma1$ を選ぶ．
これは実際には過剰に強い理論であり， より強い結果を得たいならば理論を弱めて
Buss's theory $sans("S")^1_2$ でも標準的な証明はほとんど同様に#footnote[
  Derivability condition D3 は多くの証明（私達が採用した証明も含む）では，
  formalized $Sigma_1$-completeness によって証明されるが，
  これは $sans("S")^1_2$ で成立するかは未解決な問題である @Bek2006．
  このため，よりシャープな formalized $Sigma^"b"_1$-completeness を証明する必要がある．
]実行可能である．
加えて， Nelson による interpretation $Robinson triangle.small.r sans("S")^1_2$ を用いれば，
第二不完全性定理は Robinson arithmetic $Robinson$ を interpret する広範な理論に拡大できる @Vis2011．
これは魅力的な方向性ではあるが，形式化があまりにも複雑になることからこの道は選ばない．
$ISigma1$ では @thm:recursive-def が成立するため帰納的な述語及び関数の定義が扱うことが楽である．

#theorem[$ISigma1$][
  Let $Phi_(bold(C))(arrow(v), x)$ be a predicate over $bold(V)$ which takes a class $bold(C) subset.eq bold(V)$ as a parameter.
  Assume that this satisfies following conditions.
  1. Definability: A predicate $P(c, arrow(v), x) := Phi_{z | z in c}(arrow(v), x)$ is $Delta_1$-definable.
  2. Monotonicity: $bold(C) subset.eq bold(C')$ and $Phi_bold(C)(arrow(v), x)$ implies $Phi_bold(C')(arrow(v), x)$.
  3. Finite: If $Phi_bold(C)(arrow(v), x)$ holds, then there is $m in V$, such that $Phi_{z in bold(C) | z < m}(arrow(v), x)$ holds.

  Then we have a $Sigma_1$-definable predicate $"Fix"_Phi (arrow(v), x)$ such that
  $
    "Fix"_Phi (arrow(v), x) <==> Phi_{x | "Fix"_Phi (arrow(v), x)}(arrow(v), x)
  $
  Additionally, if it satisfies following condition, $"Fix"_Phi (arrow(v), x)$ is $Delta_1$-definable.
  4. Strongly finite: If $Phi_bold(C)(arrow(v), x)$ holds, then $Phi_{z in bold(C) | z < x}(arrow(v), x)$ holds.

]<thm:recursive-def>

== Bootstrapping

== Incompleteness Theorems
