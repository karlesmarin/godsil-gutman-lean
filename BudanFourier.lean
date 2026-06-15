/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

/-
# The Budan–Fourier theorem (real-root counting via the derivative tower)

Reverse-engine target (2026-06-15): confirmed ABSENT from Mathlib (Loogle `Budan` → unknown
identifier; Mathlib has `Polynomial.signVariations` for Descartes' rule of signs but not the
Budan–Fourier theorem). Formalized in Isabelle/HOL (Wenda Li, arXiv:1811.11093), so this is
**first in Lean**, not first in any ITP. Genuine Mathlib gap, our exact domain (real-root
counting), the natural companion of Sturm: the same sign-variation count, on the *derivative tower*
`p, p', p'', …, p^(deg p)` instead of the signed-remainder sequence.

## The theorem
For a nonzero real polynomial `p` and `a < b` with `p(a), p(b) ≠ 0`, the number of real roots of
`p` in `(a, b]` **counted with multiplicity** is at most the drop `V(a) − V(b)` in the sign
variations of the Fourier (derivative-tower) sequence, and differs from it by an even number:
* `#roots(a,b] ≤ V(a) − V(b)`        (Budan–Fourier inequality)
* `V(a) − V(b) − #roots(a,b]` is even (the parity refinement; Descartes' even-difference rule).

Descartes' rule of signs is the special case read off the coefficients (the `b → ∞` Fourier
sequence); Mathlib already has that count, so this completes the picture for a bounded interval.

This file is **P0**: the two definitions + the main statement (with `sorry`). The reusable
sign-variation toolkit (zeros invisible, the `wallCount` parity engine, local sign constancy) lives
in `Sturm.lean`; the proof phase will factor that shared core out and reuse it here.

## Reference route
Wikipedia "Budan's theorem"; Basu–Pollack–Roy, *Algorithms in Real Algebraic Geometry* (Ch. 2);
W. Li, *The Budan–Fourier theorem and counting real roots with multiplicity*, arXiv:1811.11093.
-/
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.List.Destutter
public import Mathlib.Data.Sign.Basic
public import Mathlib.Data.Real.Basic

open Polynomial

namespace BudanFourier

/-- The **Fourier sequence** (derivative tower) of `p`: `p, p', p'', …, p^(deg p)`. -/
public noncomputable def fourierSeq (p : Polynomial ℝ) : List (Polynomial ℝ) :=
  (List.range (p.natDegree + 1)).map (fun k => (derivative^[k]) p)

/-- The Fourier sequence has `deg p + 1` entries. -/
public theorem fourierSeq_length (p : Polynomial ℝ) :
    (fourierSeq p).length = p.natDegree + 1 := by
  unfold fourierSeq; simp

/-- The Fourier sequence is never empty (it always contains at least `p`). -/
public theorem fourierSeq_ne_nil (p : Polynomial ℝ) : fourierSeq p ≠ [] := by
  have hlen : 0 < (fourierSeq p).length := by
    simpa [fourierSeq, List.length_map, List.length_range, Nat.succ_eq_add_one] using
      Nat.succ_pos p.natDegree
  exact List.ne_nil_of_length_pos hlen

/-- Membership in the Fourier sequence: its entries are exactly the iterated derivatives
`p^(k)` for `0 ≤ k ≤ deg p`. -/
public theorem fourierSeq_mem (p q : Polynomial ℝ) :
    q ∈ fourierSeq p ↔ ∃ k, k ≤ p.natDegree ∧ q = (derivative^[k]) p := by
  unfold fourierSeq
  constructor
  · intro h
    rcases List.mem_map.1 h with ⟨k, hk, rfl⟩
    exact ⟨k, Nat.le_of_lt_succ (List.mem_range.1 hk), rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact List.mem_map.2 ⟨k, List.mem_range.2 (Nat.lt_succ_of_le hk), rfl⟩

/-- **Fourier sign variations** of `p` at `x`: the number of sign changes in the derivative tower
evaluated at `x`, with zeros dropped. The eval-analogue, on the derivative tower, of the count used
for Sturm's theorem. -/
public noncomputable def fourierVar (p : Polynomial ℝ) (x : ℝ) : ℕ :=
  ((((fourierSeq p).map (fun q => SignType.sign (q.eval x))).filter (· ≠ 0)).destutter (· ≠ ·)).length - 1

/-- **The Budan–Fourier theorem.** For nonzero `p` and `a < b` with neither endpoint a root, the
number of real roots of `p` in `(a, b]` counted with multiplicity is bounded by the drop in Fourier
sign variations, and has the same parity as that drop. -/
public theorem budan_fourier (p : Polynomial ℝ) (hp : p ≠ 0) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (p.roots.filter (fun x => a < x ∧ x ≤ b)).card ≤ fourierVar p a - fourierVar p b ∧
    Even (fourierVar p a - fourierVar p b - (p.roots.filter (fun x => a < x ∧ x ≤ b)).card) := by
  sorry

end BudanFourier
