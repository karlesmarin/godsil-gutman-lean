/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

/-
# Sturm's theorem (real-root counting via the signed remainder sequence)

Reverse-engine target (2026-06-15): confirmed ABSENT from Mathlib (Lean 4 has `signVariations`
of coefficients / Descartes' rule of signs, but NOT the Sturm sequence nor Sturm's theorem).
Already formalized in Coq (Cohen), Isabelle/HOL (Li–Paulson, Sturm–Tarski) and HOL Light, so this
is **first in Lean**, not first in any ITP. Genuine Mathlib gap, our exact domain (real-root
counting), PR-able.

This file is **P0 of the plan**: the two missing definitions + the main statement (with `sorry`).
The real work (P1–P5: chain algebra, local constancy, root crossing, assembly) lands incrementally.

## Definitions
* `Sturm.sturmSeq p` — the signed remainder sequence `p, p', -(p % p'), …` of `p : ℝ[X]`.
* `Sturm.signVarAt L x` — number of sign changes in the list `L` **evaluated** at `x` (zeros
  dropped), the eval-analogue of `Polynomial.signVariations` (which is on coefficients).

## Main statement
* `Sturm.sturm` — for squarefree `p` and `a < b` neither a root of `p`,
  `signVarAt (sturmSeq p) a - signVarAt (sturmSeq p) b` equals the number of DISTINCT real roots
  of `p` in `(a, b]`.

## Reference route
Wikipedia "Sturm's theorem"; Cohen (Coq); Li & Paulson, Sturm–Tarski (Isabelle, Cauchy index);
Li, Budan–Fourier in Isabelle/HOL (arXiv:1811.11093); "Sturm's theorem with endpoints"
(arXiv:2208.07904).
-/
public import RealStable
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.List.Destutter
public import Mathlib.Data.Sign.Basic

open Polynomial

namespace Sturm

/-- The signed remainder chain starting from `(p, q)`: `p :: q :: -(p % q) :: …`, stopping when a
remainder hits `0`. Terminates because `(p % q).degree < q.degree`. -/
public noncomputable def sturmAux (p q : Polynomial ℝ) : List (Polynomial ℝ) :=
  haveI : Decidable (q = 0) := Classical.propDecidable _
  if hq : q = 0 then [p] else p :: sturmAux q (-(p % q))
termination_by q.degree
decreasing_by
  · rw [degree_neg]; exact degree_mod_lt p hq

/-- **Sturm sequence** of `p`: the signed remainder sequence of `p` and its derivative. -/
public noncomputable def sturmSeq (p : Polynomial ℝ) : List (Polynomial ℝ) :=
  sturmAux p (derivative p)

/-- Sign variations of a list of polynomials **evaluated** at `x`: count sign changes in
`L.map (eval x)`, ignoring zeros. Eval-analogue of `Polynomial.signVariations`. -/
public noncomputable def signVarAt (L : List (Polynomial ℝ)) (x : ℝ) : ℕ :=
  letI signs := (L.map (fun p => SignType.sign (p.eval x))).filter (· ≠ 0)
  (signs.destutter (· ≠ ·)).length - 1

/-- **Sturm's theorem.** For squarefree `p` and `a < b` with neither endpoint a root of `p`, the
drop in sign variations of the Sturm sequence equals the number of distinct real roots in `(a, b]`.
-/
public theorem sturm (p : Polynomial ℝ) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    signVarAt (sturmSeq p) a - signVarAt (sturmSeq p) b =
      (p.roots.toFinset.filter (fun x => a < x ∧ x ≤ b)).card := by
  sorry

end Sturm
