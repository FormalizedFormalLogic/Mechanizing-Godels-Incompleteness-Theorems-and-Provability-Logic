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
        normalsize[`saito.shogo.q8@dc.tohoku.ac.jp`],
      ),
      stack(
        Large[Mashu Noguchi],
        normalsize[Kobe Unversity \ Graduate School of System Informatics],
        normalsize[`251x054x@stu.kobe-u.ac.jp`],
      ),
    ),
    v(4mm),
    large[June 4, 2026],
    v(4mm),
  ),
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
  ),
)

= Introduction

_Gödel's incompleteness theorems_ are among the most significant results in mathematical logic.
In his seminal paper @godel1931, he proved what is now known as the first incompleteness theorem (G1), and in a footnote, he outlined the second incompleteness theorem (G2).
G2 was later proved rigorously by Hilbert and Bernays @hilbertGrundlagenMathematikBd1939.
We state the theorems in modern terms:
G1, with Rosser's improvement, states that for any consistent axiomatic system with sufficient expressive power to execute arithmetic, we can construct a proposition that can neither be proved nor disproved within the system.
G2 states that, as in G1, for any consistent _nice_ axiomatic system, the proposition formally asserting the system's own consistency cannot be proved within the system itself.

Gödel also made another important observation: that provability can be regarded as a modality.
In his early work @godelInterpretationIntuitionischenAussagenkalkuls1933, he observed that the provability in intuitionistic logic can be treated similarly to the modal operator $Box$ in the modal logic now called #LogicSFour.
It follows from G2, however, that abstracting the behavior of the provability predicate, the most central notion of the incompleteness theorems, does not yield #LogicSFour.
Solovay @solovay1976 showed that a modal logic called #LogicGL precisely captures the behavior of the standard provability predicate.
This fact, known as _Solovay's arithmetical completeness theorem_, was a significant result that opened up the subfield of modal logic called _provability logic_.

In this paper, we present machine-assisted formalizations of Gödel's incompleteness theorems and provability logic.
Our work is carried out in Lean 4, an interactive theorem prover, together with mathlib4, its community-developed mathematics library.
Lean 4 is based on the Calculus of Inductive Constructions (CIC) @moura2021lean,
and features dependent types, quotient types, and support for noncomputable definitions, making it highly expressive.
In addition, its powerful metaprogramming infrastructure like aesop @inproceedings enables efficient proof automation and extensibility.
