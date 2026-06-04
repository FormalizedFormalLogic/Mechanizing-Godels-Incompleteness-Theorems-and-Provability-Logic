#import "init.typ": *
#show: thmrules

#let Huge(x) = rect(stroke: none, text(size: 24.88pt)[#x])
#let huge(x) = rect(stroke: none, text(size: 20.74pt)[#x])
#let LARGE(x) = rect(stroke: none, text(size: 17.28pt)[#x])
#let Large(x) = rect(stroke: none, text(size: 14.4pt)[#x])
#let large(x) = rect(stroke: none, text(size: 12pt)[#x])
#let normalsize(x) = rect(stroke: none, text(size: 10.95pt)[#x])
#let small(x) = rect(stroke: none, text(size: 10pt)[#x])
#let footnotesize(x) = rect(stroke: none, text(size: 9pt)[#x])
#let scriptsize(x) = rect(stroke: none, text(size: 8pt)[#x])
#let tiny(x) = rect(stroke: none, text(size: 6pt)[#x])

#let dand = $⩕$
#let dor = $⩖$

#let scr(it) = text(
  features: ("ss01",),
  box($cal(it)$),
)

= General math symbols

#let Nat = $bb(N)$
#let Rat = $bb(Q)$
#let Real = $bb(R)$
#let Bool = $bb(B)$

#let family(x) = $cal(#x)$
#let PowerSet = $cal(upright("P"))$
#let nle = $lt.eq.not$
#let And = $class("relation", \&)$
#let Not = $class("normal", "not")$
#let Or = $class("relation", "or")$
#let Implies = $class("relation", "implies")$
#let sim = $class("unary", \~)$


#let LogicGL = $sans("GL")$