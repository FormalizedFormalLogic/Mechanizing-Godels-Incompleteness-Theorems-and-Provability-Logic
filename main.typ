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
    box(width: 60%, align(left)[
      We formalized proofs of Gödel's first and second incompleteness theorems and
      Solovay's arithmetical completeness of $LogicGL$ and related results in Lean4 theorem prover.
    ])
  )
)