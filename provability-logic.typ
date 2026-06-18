#import "./notations.typ": *

= Provability Logic

In this section we present our mechanization of Solovay's arithmetical completeness theorem @solovay1976.
As before, definitions and facts are introduced minimally, and are stated somewhat informally.
On the modal logic side, we give the definitions of the Gödel–Löb logic #LogicGL and of Solovay's non-normal modal logic #LogicS, and we state their completeness with respect to Kripke semantics.
We then introduce the arithmetical interpretation and related notions, and finally state Solovay's arithmetical completeness theorem.
For proofs and further details, the reader is referred to standard text @chagrovModalLogic2001 for modal logic and to @boolosLogicProvability1994 or survey @artemovProvabilityLogic2005 @japaridzeLogicProvability1998 for provability logic.

Formulas of modal logic are defined from propositional variables (denotes #Prop), the primitive logical connectives $bot$ and $limp$, and the modal operator $Box$.
The remaining operators $top, lnot, land, lor, Dia$ are introduced as the usual abbreviations.
We write $[p := B]$ for substitution, and write $A[p := B]$ for the result of substituting $B$ for all occurrences of $p$ in $A$.
In our mechanization, we mainly consider #Prop as type of natural numbers `Nat`(`ℕ`).

#definition[
  The Gödel–Löb modal logic #LogicGL is the logic defined in Hilbert style by the following axioms and rules.
  #grid(
    columns: 2,
    column-gutter: 16pt,
    align: top,
    [
      1. Tautologies of propositional logic
      2. Axiom $AxiomK$: $Box(p -> q) -> (Box p -> Box q)$
      3. Axiom $AxiomL$: $Box(Box p -> p) -> Box p$
    ],
    [
      4. #prooftree(rule(name: "MP", $B$, $A -> B$, $B$))
      5. #prooftree(rule(name: "Nec", $Box A$, $A$))
      6. #prooftree(rule(name: "Subst", $A[p := B]$, $A$))
    ],
  )
]

#definition[
  Solovay's logic #LogicS is the non-normal logic obtained by closing all theorems of #LogicGL together with the axiom $AxiomT$: $Box p -> p$ under modus ponens and the substitution rule.

  #leancode(
    links: (
      "https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/Modal/Logic/SumQuasiNormal.lean#L13-L17",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/Modal/Logic/S/Basic.lean#L14",
    ),
  )[
    ```
    inductive sumQuasiNormal (L₁ L₂ : Logic α) : Logic α
    | mem₁ {φ}    : L₁ ⊢ φ → sumQuasiNormal L₁ L₂ φ
    | mem₂ {φ}    : L₂ ⊢ φ → sumQuasiNormal L₁ L₂ φ
    | mdp  {φ ψ}  : sumQuasiNormal L₁ L₂ (φ 🡒 ψ) → sumQuasiNormal L₁ L₂ φ → sumQuasiNormal L₁ L₂ ψ
    | subst {φ s} : sumQuasiNormal L₁ L₂ φ → sumQuasiNormal L₁ L₂ (φ⟦s⟧)

    protected abbrev S := sumQuasiNormal Modal.GL {Axioms.T (.atom 0)}
    ```
  ]
]

We introduce Kripke semantics, the standard semantics for modal logic.

#definition[
  A _Kripke model_ is a triple $chevron.l W, R, V chevron.r$, where $W$ is a nonempty set (called _points_), $R subset.eq W times W$, and $V : Prop -> W -> 2$ (called the _valuation_).
  We say the following terminology for models.
  - A model is _finite_ if $W$ is a finite set.
  - A _root_ of a model is a point $r in W$ such that $r R x$ for every $x in W$ with $x != r$. If a model has a root, we call it a _rooted model_.
  - A model is _transitive_ if, for all $x, y, z in W$, $x R y$ and $y R z$ imply $x R z$.
  - A model is _irreflexive_ if no $x in W$ satisfies $x R x$.

  #leancode(
    links: (
      "https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/Modal/Kripke/Basic.lean",
    ),
    note: [
      We only describe Kripke frame and model, and satisfication relation in our mechanization.
      Since we have notation class for `⊧`, we can write `x ⊧ φ` for `Satisfies M x φ`.
    ],
  )[
    ```
    structure Frame where
      World : Type
      Rel : Rel World World
      [world_nonempty : Nonempty World]

    abbrev Frame.Rel' (x y : F.World) := F.Rel x y
    infix:45 " ≺ " => Frame.Rel'

    abbrev Valuation (F : Frame) := ℕ → F.World → Prop

    structure Model extends Frame where
      Val : Valuation toFrame

    def Satisfies (M : Kripke.Model) (x : M.World) : Formula ℕ → Prop
      | atom a  => M a x
      | ⊥       => False
      | φ 🡒 ψ   => (Satisfies M x φ) 🡒 (Satisfies M x ψ)
      | □φ      => ∀ y, x ≺ y → (Satisfies M y φ)
    ```
  ]
]

First we mechanized the Kripke completeness of #LogicGL.
We note that Kripke completeness of #LogicGL is already mechanized in HOL/Light by Maggesi and Pelini-Brogi @maggesiMechanisingGodelLob2023.
However, for the arithmetical completeness theorem, we need not merely Kripke completeness but Kripke completeness with respect to rooted models.
// The transformation into a rooted model is carried out by a method known as _tree unraveling_ (cf. @chagrovModalLogic2001[Theorem 3.18]).

#theorem[Kripke completeness of #LogicGL][
  $LogicGL proves A$ if and only if $M, r forces A$ at the root $r$ of every transitive, irreflexive, rooted finite model $M$.

  #leancode(
    links: (
      "https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/Modal/Kripke/Logic/GL/Completeness.lean#L217-L222",
    ),
    note: [
      In this mechanization, the statement is the equivalence between the first and fourth propositions.
      Equivalence to the second proposition is the usual Kripke completeness (which is due to Segerberg @Segerberg1971 and already mechanized in @maggesiMechanisingGodelLob2023) for the class of all transitive and irreflexive finite frames, and to the third proposition is the completeness for the class of models with the additional condition of being rooted.
    ],
  )[
    ```
    theorem finite_completeness_TFAE : [
      Modal.GL ⊢ φ,
      FrameClass.finite_GL ⊧ φ,
      ∀ F : Kripke.Frame, [F.IsFinite] → [F.IsTransitive] → [F.IsIrreflexive] → [F.IsRooted] → F ⊧ φ,
      ∀ M : Kripke.Model, [M.IsFinite] → [M.IsTransitive] → [M.IsIrreflexive] → [M.IsRooted] → M.root.1 ⊧ φ,
    ].TFAE
    ```
  ]
]

By this theorem, we henceforth call a transitive and irreflexive finite model a $LogicGL$-model.
Now, although the modal logic #LogicS is non-normal, an analogous rooted completeness holds with respect to a class of infinite Kripke models with reasonably good properties, called _tail models_.
This fact plays an important role in the discussion of the arithmetical completeness of #LogicS, but we do not show it here.
For a detail of tail models, see @Visser1984.

We next define the arithmetical interpretation, which translates modal formulas into arithmetic sentences.
Throughout, $T$ and $U$ denote nice theories extending #PeanoArithmetic, and consider only the standard provability predicate $Pr(T)$ for $T$.

#definition[
  A map $f colon Prop -> upright("Sent")_upright("A")$ is called an _arithmetic realization_ or shortly _realization_.
  Given a realization $f$, the _(standard) arithmetic interpretation_ is the extension of $f$ that translates a modal formula $A$ into an arithmetic sentence $f_(Pr(T))(A)$ as follows:
  $
         f_(Pr(T)) (p) & = f(p) \
       f_(Pr(T)) (bot) & = bot \
    f_(Pr(T)) (A -> B) & = f_(Pr(T)) (A) -> f_(Pr(T)) (B) \
     f_(Pr(T)) (Box A) & = Pr(T) (GoedelNum(f_(Pr(T))(A)))
  $

  #leancode(
    links: (
      "https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/ProvabilityLogic/Realization.lean#L17-L32",
    ),
    note: [
      For technical reasons, our implementation of realization depends on an arbitrary provability `𝔅`.
      However, in this report we only consider the standard provability, so we always consider `T.standardProvability` as `𝔅`.
    ],
  )[
    ```
    structure Realization (𝔅 : Provability T₀ T) where
      val : ℕ → FirstOrder.Sentence L

    abbrev _root_.LO.FirstOrder.ArithmeticTheory.StandardRealization (T : ArithmeticTheory) [T.Δ₁] := Realization T.standardProvability

    def interpret {𝔅 : Provability T₀ T} (f : Realization 𝔅) : Formula ℕ → FirstOrder.Sentence L
      | .atom a => f.val a
      |       ⊥ => ⊥
      |   φ 🡒 ψ => (f.interpret φ) 🡒 (f.interpret ψ)
      |      □φ => 𝔅 (f.interpret φ)
    ```
  ]
]


#definition[
  The _(standard) provability logic of $T$ relative to $U$_, written $ProvLogic(T, U)$, is defined as follows:
  $
    ProvLogic(T, U) = { A | #text[ $U proves f_(Pr(T)) (A)$ for any realization $f$ ] }
  $

  #leancode(
    links: (
      "https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/ProvabilityLogic/Arithmetic.lean#L80",
    ),
  )[
    ```
    def provabilityLogicOn (T U : ArithmeticTheory) [T.Δ₁] : Modal.Logic ℕ := {A | ∀ f : T.StandardRealization, U ⊢ f A}
    ```
  ]
]

Solovay's arithmetical completeness theorem states that the behavior of the standard provability predicate, regarded simply as a modal operator, is captured exactly by the modal logic #LogicGL.
In other words, for appropriate choices of $T$ and $U$, the provability logic $ProvLogic(T, U)$ coincides with #LogicGL.
Here we present the generalized version, @thm:arithmetical_completeness, using the notion of the _height_ of a theory due to Visser @Visser1981.

#definition[Height of Theory][
  For $n >= 1$, we write $Pr(T)^n$ for the $n$-times iteration of the provability predicate $Pr(T)$.
  The _height_ of theory $T$, denoted $height(T) <= omega$, is the minimum $n in omega$ such that $T proves Pr(T)^n (GoedelNum(bot))$, or $omega$ if no such $n$ exists.

  #leancode(
    links: (
      "https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Height.lean#L18",
    ),
    note: [
      Same here, we can take any provability `𝔅`, but in this report we only consider the standard provability.
    ],
  )[
    ```
    noncomputable def Provability.height (𝔅 : Provability T₀ T) : ENat := ENat.find (T ⊢ 𝔅^[·] ⊥)
    ```
  ]
]

Note that if $T$ is $Sigma_1$-sound, $T$ does not prove $Pr(T)^n (GoedelNum(bot))$ for any $n in omega$, therefore $height(T) = omega$.

#definition[
  For $n <= omega$, we define #LogicGLPlusBoxBot($n$) as follows: if $n < omega$, it is the non-normal modal logic obtained by closing all theorems of #LogicGL together with the formula $Box^n bot$ under modus ponens and the substitution rule; if $n = omega$, it is #LogicGL itself.

  #leancode(
    links: (
      "https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/Modal/Logic/GLPlusBoxBot/Basic.lean#L17-L20",
    ),
  )[
    ```
    protected def GLPlusBoxBot (n : ℕ∞) :=
    match n with
    | .some n => Modal.GL.sumQuasiNormal {□^[n]⊥}
    | .none   => Modal.GL
    ```
  ]
]

The main result of our provability logic mechanization is the following.

#theorem[@Visser1981][
  $ProvLogic(T, T) = LogicGLPlusBoxBot(height(T))$.

  #leancode(
    links: (
      "https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/ProvabilityLogic/GL/Completeness.lean#L104-L105",
    ),
  )[
    ```
    theorem provabilityLogic_eq_GLPlusBoxBot : (T.provabilityLogicOn T) ≊ Modal.GLPlusBoxBot T.height
    ```
  ]
] <thm:arithmetical_completeness>

@thm:arithmetical_completeness is proved by embedding into arithmetic an appropriate $LogicGL$-model of suitable height, obtained as a countermodel when $LogicGLPlusBoxBot(height(T)) nproves A$.
As a corollary, we obtain Solovay's original statement.

#corollary[Solovay's Arithmetical Completeness Theorem 1 @solovay1976][
  If $T$ is $Sigma_1$-sound, then $ProvLogic(T, T) = LogicGL$.
  In particular, $ProvLogic(PeanoArithmetic, PeanoArithmetic) = LogicGL$.

  #leancode(
    links: (
      "https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/ProvabilityLogic/GL/Completeness.lean#L110",
    ),
  )[
    ```
    instance : (𝗣𝗔.provabilityLogicOn 𝗣𝗔) ≊ Modal.GL
    ```
  ]
]

Moreover, Solovay also consider proved that #LogicS is arithmetically complete with respect to true arithmetic #TrueArithmetic.

#theorem[Solovay's Arithmetical Completeness Theorem 2 @solovay1976][
  For any formula $A$, $LogicS proves A$ if and only if $NN models f_(Pr(T)) (A)$ for every arithmetic interpretation $f$.
  That is, $ProvLogic(T, TrueArithmetic) = LogicS$.

  #leancode(
    links: (
      "https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/ProvabilityLogic/S/Completeness.lean#L184",
      "https://github.com/FormalizedFormalLogic/Foundation/blob/master/Foundation/ProvabilityLogic/S/Completeness.lean#L186",
    ),
  )[
    ```
    theorem S.arithmetical_completeness_iff : Modal.S ⊢ A ↔ ∀ f : T.StandardRealization, ℕ ⊧ₘ f A

    theorem provabilityLogic_PA_TA_eq_S : (T.provabilityLogicOn 𝗧𝗔) ≊ Modal.S
    ```
  ]
]
