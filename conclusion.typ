#import "./notations.typ": *

= Future Work

In the following, based on our present results, we outline the directions in which we would like to pursue further formalization.

== Incompleteness Results

== Information-theoretic Incompleteness a la Chaitin

== Classification of Provability Logics

One important result in provability logic is the _classification of provability logics_ obtained in the 1980s.
Classification of provability logic is mainly studied by Artemov, Beklemishev, Japaridge, Visser, and finally completed by Beklemishev.
The statement is that: when $T$ and $U$ range appropriately over consistent theories, $ProvLogic(T, U)$ is exhausted by one of four families given by suitable extensions of the logics $LogicGL$, $Logic("D")$, and $Logic("S")$.
Here, the logic $Logic("D")$ is a non-normal modal logic introduced by Japaridze (Dzhaparidze), and it lies strictly between the logics $LogicGL$ and $Logic("S")$.
For a detailed survey of the classification theorem, see Beklemishev @artemovProvabilityLogic2005.
We have mechanized several facts at the early stages of the classification theorem.
For instance, preparing the semantics for the non-normal logic $Logic("D")$, and using the notions of trace and spectrum of logic introduced by Artemov.
However, the full classification theorem requires very hard handling of Kripke frames and various complicated arguments, and we have not been able to mechanize it completely.
We expect that taking on the mechanization of classification would be a very hard and challenging task.

== Interpretability Logic

Another advanced topic in provability logic, there is the _interpretability logic_ proposed by Visser.
Interpretability logic is the extension of provability logic by binary modal operators $triangle.r$ representing interpretability (informally interpretation of $A triangle.r B$ is that extended theory $T + f(A)$ is interpretable in $T + f(B)$).
There are several semantics for interpretability logic, including _de Jongh–Veltman semantics_, _Visser semantics_, and _Verbrugge semantics_ (as known as _generalized Veltman semantics_).
The later ones can handle completeness and definability for more axioms, but they have the drawback that the arguments become very involved.
For Verbrugge semantics, prior work such as the verification of frame definability in Agda has been carried out.
Currently, based on work by Kurahashi & Okawa, we have mechanized syntactic proofs and frame definability for weak axiomatic systems of interpretability logic.
However, we have not yet established modal completeness with respect to frames, and as for the arithmetical completeness theorem, we have not been able to mechanize it at all.

== Syntactical Arguements for Modal Logics

Apart from the perspective of provability logic, since $LogicGL$ is very interesting modal logic, we also consider it an interesting  the general properties of #LogicGL, #LogicS, and other pure logics, and in particular the syntactic argument such as cut-elimination of sequent calculi for these logic, interpolation calcululation, and automated deduction.
Historically, cut-elimination for the sequent calculus of #LogicGL required a delicate analysis.
Recently, the termination of cut-elimination for #LogicGL using a method called regression by Brighton has been mechanized in Rocq.
In addition, for other logic, HOLMS, that continues Maggesi and Perini Brogi's mechanization of #LogicGL, and furthermore mechanizes content concerning automated proving for well-knowm modal logics on modal-cube like $Logic("K"), Logic("K4"), Logic("S4")$, and moreover, Grzegorczyk's modal logic #Logic("Grz")
#footnote[
  Although we did not mention it, our repository also mechanizes the Kripke completeness of #Logic("Grz"), and moreover mechanizes the arithmetical completeness theorem of #Logic("Grz") based on @goldblattArithmeticalNecessityProvability1978 @boolosProvabilityArithmeticSchema1980.
  #Logic("Grz") has interesting properties as a modal logic; for example, it is known to be the greatest modal companion of intuitionistic propositional logic.
  We have also mechanized this fact.
].
A sequent calculus for #Logic("S") had not been proposed until recently.
Kushida proposed a sequent calculus using two-level sequents and gave a syntactical algorithm for its cut-elimination.
And Kashima et al, extending Kushida's approach, proposed a sequent calculus for #Logic("D") using third-level sequents.
To our knowledge, neither these sequent calculi nor the algorithms has been mechanized, and we would like to mechanize them.
