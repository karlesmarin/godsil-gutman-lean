/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Ihara.Bass

/-!
# The graph trace formula — Part III (the matching ↔ Ihara bridge)

This file begins Part III: the bridge uniting the two sides formalized earlier, the matching
polynomial (the **tree / Plancherel** side, in `MSS`) and the Hashimoto non-backtracking operator
(the **cycle / π₁** side, in `Ihara/Bass.lean`). The bridge is a sharp trace-formula gap law.

## The locked statement (numerically verified, NOT yet proved in Lean)

With `A` the adjacency matrix, `B` the Hashimoto operator (`Ihara/Bass.lean`), and
`p_k = Σ θᵢᵏ` the power sums of the matching-polynomial roots (Godsil's *tree-like walk* count),
define `gap_k := tr(Aᵏ) − p_k`. Then, for a finite graph of girth `g`:

  `gap_k = tr(Bᵏ)`  for all `1 ≤ k ≤ g+1`,  and this is SHARP (it fails at `k = g+2`);

  the first nonzero value is at `k = g`:  `tr(B^g) = 2·g·(#shortest cycles)`.

Independently re-verified (Python, `research/_tmp/traceformula_lock.py`) on
`K₃, C₅, K₄, K_{3,3}, Q₃, Petersen` — all six match, sharp at `g+2`, first gaps
`120, 72, 48, 24` (Petersen, K₃₃, Q₃, K₄) confirmed. This is CLASSICAL mathematics (Godsil's
moment theorem + the non-backtracking trace); the contribution is the *formalization* — the first
ITP record of the bridge, joining the two existing Lean files. No new theorem is claimed.

## Roadmap (the three pieces)

1. `tr(Aᵏ) = #closed walks of length k` — **this file** (free from
   `adjMatrix_pow_apply_eq_card_walk`).
2. `N_k = tr(Bᵏ) = #closed non-backtracking walks` — needs a non-backtracking-walk count
   (Mathlib lacks it); `B` is in `Ihara/Bass.lean`.
3. **`p_k = Σ θᵢᵏ = #closed tree-like walks` — Godsil's moment theorem. THE HARD BRICK**
   (Mathlib has no tree-like walks); plus the girth-threshold argument tying 1–3 together.

This file lands piece 1.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Piece 1 of the trace formula.** The trace of the `k`-th power of the adjacency matrix counts
the closed walks of length `k`: `tr(Aᵏ) = Σ_v #{closed walks of length k at v}`. -/
theorem trace_adjMatrix_pow (k : ℕ) :
    (G.adjMatrix ℕ ^ k).trace = ∑ v : V, #(G.finsetWalkLength k v v) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_congr rfl fun v _ => by
    rw [adjMatrix_pow_apply_eq_card_walk, Nat.cast_id, card_set_walk_length_eq]

open Polynomial Matrix

section Spectral
variable (R : Type*) [CommRing R]

/-- Evaluating the determinant of a polynomial-matrix at `u` = determinant of the matrix with
each entry evaluated at `u` (the eval ring-hom commutes with `det`). -/
private theorem eval_det_eq (u : R) (P : Matrix V V R[X]) :
    (P.det).eval u = (P.map (Polynomial.evalRingHom u)).det :=
  (Polynomial.evalRingHom u).map_det P

/-- The Hashimoto polynomial-matrix `1 - X•B`, evaluated at `u`, is `1 - u•B`. -/
private theorem map_eval_hashimoto (u : R) :
    (1 - (X : R[X]) • (G.hashimoto R).map C).map (Polynomial.evalRingHom u)
      = 1 - u • G.hashimoto R := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, Polynomial.coe_evalRingHom, apply_ite (eval u),
    eval_sub, eval_mul, eval_X, eval_C, eval_one, eval_zero]

/-- The A/D polynomial-matrix `1 - X•A + X²•(D-1)`, evaluated at `u`, is `1 - u•A + u²•(D-1)`. -/
private theorem map_eval_adj (u : R) :
    (1 - (X : R[X]) • (G.adjMatrix R).map C + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).map
        (Polynomial.evalRingHom u)
      = 1 - u • G.adjMatrix R + u ^ 2 • (G.degMatrix R - 1) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, Polynomial.coe_evalRingHom, apply_ite (eval u),
    eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_zero]

end Spectral

section SpectralField
variable (R : Type*) [Field R] [Infinite R] [LinearOrder V]

/-- **Piece 2 — Bass as a polynomial identity (the charpoly form).** Lifting `bass_determinant`
(pointwise over an infinite field) to an identity in `R[X]`, with the non-backtracking side
expressed through `Matrix.charpolyRev B = det(1 - X•B)`. This is the foundation for extracting the
non-backtracking trace counts `N_k = tr(Bᵏ)` from the adjacency data. -/
theorem bass_charpolyRev :
    (1 - (X : R[X]) ^ 2) ^ (Fintype.card V) * (1 - (X : R[X]) • (G.hashimoto R).map C).det
      = (1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card
        * (1 - (X : R[X]) • (G.adjMatrix R).map C
            + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).det := by
  refine Polynomial.funext fun u => ?_
  simp only [eval_mul, eval_pow, eval_sub, eval_one, eval_X, eval_det_eq,
    map_eval_hashimoto, map_eval_adj]
  exact G.bass_determinant R u

end SpectralField

end SimpleGraph
