#import "./notations.typ": *

= Future Work

In the following, based on our present results, we outline the directions in which we would like to pursue further formalization.

== Incompleteness Results

== Information-theoretic Incompleteness a la Chaitin

== Classification of Provability Logics

One important result in provability logic is the _classification of provability logics_ obtained in the 1980s.
Classification of provability logic is mainly studied by Artemov, Beklemishev, Japaridze (Dzhaparidze), Visser, and finally completed by Beklemishev @Beklemishev1990.
The statement is that: when $T$ and $U$ range appropriately over consistent theories, $ProvLogic(T, U)$ is exhausted by one of four families given by suitable extensions of the logics $LogicGL$, $Logic("D")$, and $Logic("S")$.
Here, the logic $Logic("D")$ is a non-normal modal logic introduced by Japaridze @Japaridze1986, and it placed strictly between the logics $LogicGL$ and $Logic("S")$.
For a detailed survey of the classification, see Artemov and Beklemishev @artemovProvabilityLogic2005[Section 6].
We have mechanized several facts at the early stages of the classification theorem.
For instance, preparing the semantics for the logic $Logic("D")$ by Beklemishev @Beklemishev1989, and using the notions of trace and spectrum of logic introduced by Artemov.
However, the full classification theorem requires very hard handling of Kripke frames and various complicated arguments, and we have not been able to mechanize it completely.
We expect that taking on the mechanization of classification would be a very hard and challenging task.

== Interpretability Logic

#let interpret = $class("binary", triangle.r.small)$

Another advanced topic in provability logic, there is the _interpretability logic_ proposed by Visser @Visser1990.
Interpretability logic is the extension of provability logic with addition binary modal operators $interpret$ representing interpretability (informally explanation of $A interpret B$ is that extended theory $T + f(A)$ is interpretable in $T + f(B)$).
There are several semantics for interpretability logic, including _de Jongh–Veltman semantics_ @deJonghVeltman1990, _Visser semantics_, and _Verbrugge semantics_ (as known as _generalized Veltman semantics_) @JoostenRoviraMikecVukovic2024.
The later ones can handle completeness and definability for more axioms, but they have the drawback that the arguments become very involved.
For Verbrugge semantics, prior work, has been carried out in Agda by Rovira @Rovira2020 for the verification of frame definability.
For now our progress, we have mechanized syntactic proofs and frame definability for some additional axioms and weak interpretability logics based on work by Kurahashi & Okawa @KurahashiOkawa2021.
However, we have not yet established modal completeness with respect to frames, and as for the arithmetical completeness theorem, we have not been able to mechanize it at all.

#let Boxdot = $class("unary", ⊡)$

== Syntactical Arguements for Modal Logics

Apart from the perspective of provability logic, since $LogicGL$ is very interesting modal logic, we also consider it an interesting  the general properties of #LogicGL, #LogicS, and other pure logics, and in particular the syntactic argument such as cut-elimination of sequent calculi for these logic, interpolation calcululation, and automated deduction.
Historically, cut-elimination for the sequent calculus of #LogicGL required a delicate analysis, see @GoreRamanayake2012.
Recently, the termination of cut-elimination for #LogicGL using a method called regress process by Brighton @Brighton2016 has been verified in Rocq by Goré, Ramanayake and Shillito @GoreRamanayakeShillito2021.
In addition, for other logic, HOLMS @Bilotta2025 @BilottaMaggesiPeriniBrogi2025 @BilottaMaggesiPeriniBrogi2026a @BilottaMaggesiPeriniBrogi2026b, that continues Maggesi and Perini Brogi's mechanization of #LogicGL @maggesiMechanisingGodelLob2023, and furthermore mechanizes content concerning automated proving for well-knowm modal logics on modal-cube like $Logic("K"), Logic("K4"), Logic("S4")$, and moreover, Grzegorczyk's modal logic #Logic("Grz")
#footnote[
  Although we did not mention it, we also mechanizes the Kripke completeness of #Logic("Grz"), and moreover mechanizes the arithmetical completeness theorem of #Logic("Grz") based on @goldblattArithmeticalNecessityProvability1978 @boolosProvabilityArithmeticSchema1980.
  Outline is here:
  Define _boxdot translation_ $(dot)^Boxdot$, which maps $(Box A)^Boxdot$ to $A and Box A$.
  At that point, the fact holds that $Logic("Grz") proves A <==> LogicGL proves A^Box$ (called the _Kuznetsov-Goldblatt-Boolos Theorem_ in @BilottaMaggesiPeriniBrogi2026b[Theorem 2]).
  From the arithmetical completeness of #LogicGL, it follows that #Logic("Grz") also has arithmetical completeness under the "true and provable" interpretation.
  #Logic("Grz") has interesting properties as a modal logic;
  for example, it is known to be the largest modal companion of intuitionistic propositional logic.
  We have also mechanized this facts.
].
A sequent calculus for #Logic("S") had not been proposed until recently.
Kushida @Kushida2020 proposed a sequent calculus using two-level sequents and gave a syntactical algorithm for its cut-elimination.
And Kashima et al @KashimaKurahashiIwataMorioka2025, extending Kushida's approach, proposed a sequent calculus for #Logic("D") using third-level sequents.
To our knowledge, neither these sequent calculi nor the algorithms has been mechanized, and we would like to mechanize them.
