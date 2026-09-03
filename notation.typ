// 本文（main.typ）中で導入していた記法をここに集約する．
// 汎用の記法は init.typ の Notations 節にある．

// --- Numerals ---

#let num(x) = $overline(#x)$

// --- Internal arithmetic (second incompleteness theorem) ---

// An arbitrarily fixed model of IΣ₁
#let Universe = $bold(upright(V))$
#let Bit = $"Bit"$
// The fixpoint of a class-valued function Φ (Knaster--Tarski)
#let Fix = $bold("Fix")$

// --- Provability abstraction ---

// Gödel sentence of a provability predicate
#let Godel(B) = $sans("G")_#B$
#let fixpoint(x) = $sans("fixedpoint")_#x$
// A provability predicate satisfying the Rosser condition
#let Rosser = $frak(R)$

// --- Refutability abstraction ---

// Jeroslow sentence of a refutability predicate
#let Jeroslow(W) = $sans("J")_#W$
#let Safe(B, W) = $sans("Safe")_(#B,#W)$
// Formalized law of non-contradiction
#let FLoN(B, W) = $sans("FLoN")_(#B,#W)$
