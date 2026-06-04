#import "init.typ": *
#import "notations.typ": *
#import "@preview/curryst:0.3.0": rule

#show: thmrules
#show: init

#set page(footer: none)

#align(
  center,
  stack(
    LARGE[Mechanizing Gödel's Incompleteness Theorems \ and Provability Logic],
    v(10mm),
    grid(
      columns: (1fr, 1fr),
      stack(
        Large[Shogo Saito],
        normalsize[Tohoku University \ Mathematical Institute],
        normalsize[`saito.shogo.q8@dc.tohoku.ac.jp`]
      ),
      stack(
        Large[Mashu Noguchi],
        normalsize[Kobe Unversity \ Graduate School of System Informatics],
        normalsize[`251x054x@stu.kobe-u.ac.jp`]
      ),
    ),
    v(4mm),
    large[June 4, 2026],
    v(4mm),
  )
)

#align(
  center,
  stack(
    [*Abstract*],
    v(4mm),
    box(width: 80%, align(left)[
      We formalized proofs of Gödel's first and second incompleteness theorems and
      Solovay's arithmetical completeness of $LogicGL$ and related results in Lean4 theorem prover.
    ]),
    v(8mm),
  )
)

= Introduction

Gödel's incompleteness theorems are among the most significant results in mathematical logic.
In his seminal paper @godel1931, he proved what is now known as the first incompleteness theorem (G1),
and in a footnote, he outlined the second incompleteness theorem (G2), which was later proved rigorously by Hilbert and Bernays @hilbertGrundlagenMathematikBd1939.

Another short but impactful work by Gödel in the early development of intuitionistic propositional logic and modal logic @godelInterpretationIntuitionischenAussagenkalkuls1933 introduced a unary operator $frak(B)$,
interpreted as "provable somehow", and investigated its behavior.
From a modern perspective, he observed that the modal operator $Box$ in the modal logic $LogicSFour$ plays a similar role, though it differs in subtle but important ways.
Later, some logicians proposed the modal operator $Box$ interpret as a formal provability, i.e. provability predicate, which plays important role in proof of incompleteness theorem.
The subfield of modal logic under this interpretation is called provability logic.
The first important result in provability logic is Solovay's arithmetical completeness theorem @solovay1976,
which states that the behavior of standard provability predicate sufficient to derive G2 is precisely captured by the modal logic $LogicGL$.
See more topic of provability logic in textbook @boolosLogicProvability1994, @smorynskiSelfReferenceModalLogic1985 and survey @artemovProvabilityLogic2005,@japaridzeLogicProvability1998.

In this paper, we present machine-assisted formalizations of Gödel's incompleteness theorems and provability logic.
Our work is carried out in Lean 4, an interactive theorem prover, together with mathlib4, its community-developed mathematics library.
Lean 4 is based on the Calculus of Inductive Constructions (CIC) @moura2021lean,
and features dependent types, quotient types, and support for noncomputable definitions, making it highly expressive.
In addition, its powerful metaprogramming infrastructure like aesop @inproceedings enables efficient proof automation and extensibility.
