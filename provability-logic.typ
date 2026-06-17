#import "./notations.typ": *

= Provability Logic

In this section we present our mechanization of Solovay's arithmetical completeness theorem @solovay1976.
As before, definitions and facts are introduced minimally, and are stated somewhat informally.
On the modal logic side, we give the definitions of the Gödel–Löb logic #LogicGL and of Solovay's non-normal modal logic #LogicS, and we state their completeness with respect to Kripke semantics.
We then introduce the arithmetical interpretation and related notions, and finally state Solovay's arithmetical completeness theorem.
For proofs and further details, the reader is referred to standard text @chagrovModalLogic2001 for modal logic and to @boolosLogicProvability1994 or survey @artemovProvabilityLogic2005 @japaridzeLogicProvability1998 for provability logic.

Formulas of modal logic are defined from propositional variables (denotes #Prop), the primitive logical connectives $bot$ and $limp$, and the modal operator $Box$.
The remaining operators $top, lnot, land, lor, Dia$ are introduced as the usual abbreviations.

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
]

We introduce Kripke semantics, the standard semantics for modal logic.

#definition[
  A _Kripke model_ is a triple $chevron.l W, R, V chevron.r$, where $W$ is a nonempty set (called _points_), $R subset.eq W times W$, and $V : Prop -> W -> 2$ (called the _valuation_).
  We say the following terminology for models.
  - A model is _finite_ if $W$ is a finite set.
  - A _root_ of a model is a point $r in W$ such that $r R x$ for every $x in W$ with $x != r$. If a model has a root, we call it a _rooted model_.
  - A model is _transitive_ if, for all $x, y, z in W$, $x R y$ and $y R z$ imply $x R z$.
  - A model is _irreflexive_ if no $x in W$ satisfies $x R x$.
]

We first mechanized the Kripke completeness of #LogicGL.
We note that Kripke completeness of #LogicGL is already mechanized in HOL/Light by Maggesi and Pelini-Brogi @maggesiMechanisingGodelLob2023.
However, for the arithmetical completeness theorem, we need not merely Kripke completeness but Kripke completeness with respect to rooted models. The transformation into a rooted model is carried out by a method known as _tree unraveling_ (cf. @chagrovModalLogic2001[Theorem 3.18]).

#theorem[Kripke completeness of #LogicGL][
  $LogicGL proves A$ if and only if $M, r forces A$ at the root $r$ of every transitive, irreflexive, rooted finite model $M$.
]

By this theorem, we henceforth call a transitive and irreflexive finite model a $LogicGL$-model.
Now, although the modal logic #LogicS is non-normal, an analogous rooted completeness holds with respect to a class of infinite Kripke models with reasonably good properties, called _tail models_.
This fact plays an important role in the discussion of the arithmetical completeness of #LogicS, but we do not show it here.
For a detail of tail models, see @Visser1984.

We next define the arithmetical interpretation, which translates modal formulas into arithmetic sentences.
Throughout, $T$ and $U$ denote nice theories extending #PeanoArithmetic.

#definition[
  A map $f colon Prop -> upright("Sent")_upright("A")$ is called an _arithmetic realization_ or shortly _realization_.
  Given a realization $f$ and a provability predicate $Prov(T)(x)$, the _arithmetic interpretation_ is the extension of $f$ that translates a modal formula $A$ into an arithmetic sentence $f_(Prov(T))(A)$ as follows:
  $
         f_(Prov(T)) (p) & = f(p) \
       f_(Prov(T)) (bot) & = bot \
    f_(Prov(T)) (A -> B) & = f_(Prov(T)) (A) -> f_(Prov(T)) (B) \
     f_(Prov(T)) (Box A) & = Prov(T) (GoedelNum(f_(Prov(T))(A)))
  $
  When the provability predicate $Prov(T)$ is obvious from context, we omit this and simply write $f(A)$.
]

In what follows, we consider only the standard provability predicate $Pr(T)$.

#definition[
  The _(standard) provability logic of $T$ relative to $U$_, written $ProvLogic(T, U)$, is defined as follows:
  $
    ProvLogic(T, U) = { A | #text[ $U proves f_(Pr(T)) (A)$ for any realization $f$ ] }
  $
]

Solovay's arithmetical completeness theorem states that the behavior of the standard provability predicate, regarded simply as a modal operator, is captured exactly by the modal logic #LogicGL.
In other words, for appropriate choices of $T$ and $U$, the provability logic $ProvLogic(T, U)$ coincides with #LogicGL.
Here we present the generalized version of the theorem, using the notion of the _height_ of a theory due to Visser @Visser1981.

#definition[Height of Theory][
  For $n >= 1$, we write $Pr(T)^n$ for the $n$-times iteration of the provability predicate $Pr(T)$.
  The _height_ of theory $T$, denoted $height(T) <= omega$, is the minimum $n in omega$ such that $T proves Pr(T)^n (GoedelNum(bot))$, or $omega$ if no such $n$ exists.
]

Note that if $T$ is $Sigma_1$-sound, $T$ does not prove $Pr(T)^n (GoedelNum(bot))$ for any $n in omega$, therefore $height(T) = omega$.

#definition[
  For $n <= omega$, we define #LogicGLPlusBoxBot($n$) as follows: if $n < omega$, it is the non-normal modal logic obtained by closing all theorems of #LogicGL together with the formula $Box^n bot$ under modus ponens and the substitution rule; if $n = omega$, it is #LogicGL itself.
]

#theorem[@Visser1981][
  $ProvLogic(T, T) = LogicGLPlusBoxBot(height(T))$.
] <thm:arithmetical_completeness>

@thm:arithmetical_completeness is proved by embedding into arithmetic an appropriate $LogicGL$-model of suitable height, obtained as a countermodel when $LogicGLPlusBoxBot(height(T)) nproves A$.
As a corollary, we obtain Solovay's original statement.

#corollary[Solovay's Arithmetical Completeness Theorem 1 @solovay1976][
  If $T$ is $Sigma_1$-sound, then $ProvLogic(T, T) = LogicGL$.
]

Solovay also proved that #LogicS is arithmetically complete with respect to true arithmetic #TrueArithmetic.

#theorem[Solovay's Arithmetical Completeness Theorem 2 @solovay1976][
  $ProvLogic(T, TrueArithmetic) = LogicS$.
  That is, for any formula $A$, $LogicS proves A$ if and only if $NN models f_(Pr(T)) (A)$ for every arithmetic interpretation $f$.
]
