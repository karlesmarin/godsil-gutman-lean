/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
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

This file currently lands: piece 1 (`trace_adjMatrix_pow`), the spectral lift of Bass
(`bass_charpolyRev`), and — via the general-matrix interlude below — the complete
trace-generating-function bridge: the eigenvalue-free resolvent side (`resolventSeries` and
friends), **Jacobi's formula** `(det M)′ = tr(adj M · M′)` (`derivative_det`), and their fusion,
**Newton's identity for matrix traces** `(charpolyRev M)′ = -charpolyRev M · ∑ₖ tr(Mᵏ⁺¹) Xᵏ`
(`charpolyRev_logDeriv`). Composing with `bass_charpolyRev` then yields the Ihara `N_k` counts.
-/

/-! ## The trace generating function (Part III, brick 2)

A general-matrix interlude, independent of graphs. The **resolvent series** `∑ₖ Mᵏ Xᵏ`, viewed as a
matrix of formal power series, is the formal inverse of `1 - X•M`, and its trace is the trace
generating function `∑ₖ tr(Mᵏ) Xᵏ`. Everything here is eigenvalue-free and over an arbitrary
`CommRing` — the half of the Newton/trace-generating-function bridge that needs no determinant.
The determinant half is Jacobi's formula `(det F)′ = tr(adj F · F′)`, proved below in `derivative_det`;
together they will tie the trace power sums to `charpolyRev` and so to Bass's identity
(`bass_charpolyRev`). -/
namespace Matrix

open PowerSeries

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The matrix **resolvent series** `∑ₖ Mᵏ Xᵏ`, an `n × n` matrix of formal power series whose
`(i,j)` entry has `k`-th coefficient `(Mᵏ) i j`. -/
noncomputable def resolventSeries (M : Matrix n n R) : Matrix n n R⟦X⟧ :=
  fun i j => mk fun k => (M ^ k) i j

@[simp] theorem coeff_resolventSeries (M : Matrix n n R) (i j : n) (k : ℕ) :
    coeff k (resolventSeries M i j) = (M ^ k) i j :=
  coeff_mk k _

/-- **The trace generating function.** The trace of the resolvent collects the trace power sums:
`tr(resolventSeries M) = ∑ₖ tr(Mᵏ) Xᵏ`. -/
theorem trace_resolventSeries (M : Matrix n n R) :
    (resolventSeries M).trace = mk fun k => (M ^ k).trace := by
  ext k
  simp only [Matrix.trace, Matrix.diag_apply, map_sum, coeff_resolventSeries, coeff_mk]

/-- The resolvent series satisfies the geometric fixed-point equation
`resolventSeries M = 1 + X • (M · resolventSeries M)`, the formal-power-series shadow of
`(1 - X M)⁻¹ = 1 + X M (1 - X M)⁻¹`. -/
theorem resolventSeries_fixedPoint (M : Matrix n n R) :
    resolventSeries M = 1 + (X : R⟦X⟧) • (M.map (C : R →+* R⟦X⟧) * resolventSeries M) := by
  ext i j t
  simp only [coeff_resolventSeries, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, map_add]
  rcases t with _ | s
  · simp only [pow_zero, Matrix.one_apply, coeff_zero_eq_constantCoeff, map_mul,
      constantCoeff_X, zero_mul, add_zero, apply_ite (constantCoeff (R := R)), map_one, map_zero]
  · simp only [pow_succ', Matrix.mul_apply, Matrix.map_apply, coeff_succ_X_mul, map_sum,
      coeff_C_mul, coeff_resolventSeries, apply_ite (coeff (R := R) (s + 1)), coeff_one,
      Nat.succ_ne_zero, if_false, map_zero, ite_self, zero_add]

/-- **The resolvent inverts `1 - X•M`.** Hence `resolventSeries M = (1 - X•M)⁻¹` in
`Matrix n n R⟦X⟧`, and the trace generating function `trace_resolventSeries` is `tr((1 - X M)⁻¹)`. -/
theorem one_sub_smul_mul_resolventSeries (M : Matrix n n R) :
    (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)) * resolventSeries M = 1 := by
  rw [sub_mul, one_mul, smul_mul_assoc]
  nth_rewrite 1 [resolventSeries_fixedPoint M]
  abel

/-- The adjugate of `1 - X•M` over `R⟦X⟧` is `det(1 - X•M)` times the resolvent series — the matrix
form of `adj F = det F · F⁻¹`, valid because the resolvent inverts `1 - X•M`
(`one_sub_smul_mul_resolventSeries`). -/
theorem smul_resolventSeries_eq_adjugate (M : Matrix n n R) :
    (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)).det • resolventSeries M
      = adjugate (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)) :=
  calc (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)).det • resolventSeries M
      = ((1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)).det • (1 : Matrix n n R⟦X⟧))
          * resolventSeries M := by rw [smul_mul_assoc, one_mul]
    _ = adjugate (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧))
          * ((1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)) * resolventSeries M) := by
        rw [← adjugate_mul, mul_assoc]
    _ = adjugate (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)) := by
        rw [one_sub_smul_mul_resolventSeries, mul_one]

/-- The shifted trace generating function: `tr(resolvent · M) = ∑ₖ tr(Mᵏ⁺¹) Xᵏ`. -/
theorem trace_resolventSeries_mul (M : Matrix n n R) :
    (resolventSeries M * M.map (C : R →+* R⟦X⟧)).trace = mk fun k => (M ^ (k + 1)).trace := by
  ext k
  simp only [Matrix.trace, Matrix.diag_apply, map_sum, Matrix.mul_apply, Matrix.map_apply,
    coeff_mul_C, coeff_resolventSeries, coeff_mk, pow_succ]

/-! ### Jacobi's formula (Part III, brick 1)

The determinant half of the trace-generating-function bridge: the derivative of `det` of a matrix of
polynomials is the trace of the adjugate times the entrywise derivative,
`(det M)′ = tr(adj M · M′)`. This is the crux brick — it is what links `det`/`charpolyRev` to traces,
and (wheel-checked 2026-06-07) it has not previously been recorded in any proof assistant. The proof
is the Leibniz rule for `det`: differentiate one column at a time, then read each single-column
derivative off Cramer's rule / the adjugate. -/
section Jacobi

open Polynomial

variable {R : Type*} [CommRing R]

/-- **Column-wise Leibniz rule for the determinant.** Differentiating `det M` is the sum, over the
columns `k`, of the determinant of `M` with column `k` replaced by its entrywise derivative. -/
private theorem derivative_det_eq_sum_updateCol (M : Matrix n n R[X]) :
    derivative M.det = ∑ k, (M.updateCol k fun a => derivative (M a k)).det := by
  rw [det_apply', map_sum]
  simp only [derivative_intCast_mul, derivative_prod_finset, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [← Finset.prod_erase_mul Finset.univ
    (fun i => (M.updateCol k fun a => derivative (M a k)) (σ i) i) (Finset.mem_univ k)]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [updateCol_apply, if_neg (Finset.ne_of_mem_erase hi)]
  · rw [updateCol_apply, if_pos rfl]

/-- **Jacobi's formula.** For a square matrix of polynomials, the derivative of the determinant is
the trace of the adjugate times the entrywise-differentiated matrix: `(det M)′ = tr(adj M · M′)`. -/
theorem derivative_det (M : Matrix n n R[X]) :
    derivative M.det = (M.adjugate * M.map derivative).trace := by
  rw [derivative_det_eq_sum_updateCol]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.map_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← cramer_apply, cramer_eq_adjugate_mulVec]
  rfl

omit [Fintype n] in
/-- The entrywise derivative of the polynomial matrix `1 - X•M` is `-M`. -/
theorem map_derivative_one_sub_smul (M : Matrix n n R) :
    (1 - (X : R[X]) • M.map (C : R →+* R[X])).map derivative = -(M.map (C : R →+* R[X])) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.neg_apply, Polynomial.derivative_sub, apply_ite Polynomial.derivative,
    Polynomial.derivative_one, Polynomial.derivative_zero, ite_self, zero_sub,
    Polynomial.derivative_mul, Polynomial.derivative_X, one_mul, Polynomial.derivative_C,
    mul_zero, add_zero]

/-- **Newton's identity for matrix traces** — the fusion of Jacobi's formula (`derivative_det`) and
the resolvent trace generating function (`trace_resolventSeries`). The logarithmic derivative of the
reversed characteristic polynomial, as a formal power series, collects the trace power sums:
`(charpolyRev M)′ = -charpolyRev M · ∑ₖ tr(Mᵏ⁺¹) Xᵏ`.

Equivalently `∑_{k≥1} tr(Mᵏ) Xᵏ = -X · (charpolyRev M)′ / charpolyRev M`. Over an arbitrary
`CommRing`, eigenvalue-free. This is the matrix-trace form of Newton's identities — the bridge that
`Mathlib`'s `MvPolynomial.NewtonIdentities` does not provide and that, at `k = 1`, specialises to
the existing `coeff_charpolyRev_eq_neg_trace`. -/
theorem charpolyRev_logDeriv (M : Matrix n n R) :
    d⁄dX R (charpolyRev M : R⟦X⟧)
      = -(charpolyRev M : R⟦X⟧) * PowerSeries.mk fun k => (M ^ (k + 1)).trace := by
  have hcp : (charpolyRev M : R[X]) = (1 - (X : R[X]) • M.map (C : R →+* R[X])).det := rfl
  have hMC : (M.map (C : R →+* R[X])).map Polynomial.coeToPowerSeries.ringHom
      = M.map (PowerSeries.C : R →+* R⟦X⟧) := by
    ext a b
    simp only [Matrix.map_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
  have hFs : (1 - (X : R[X]) • M.map (C : R →+* R[X])).map Polynomial.coeToPowerSeries.ringHom
      = 1 - (PowerSeries.X : R⟦X⟧) • M.map (PowerSeries.C : R →+* R⟦X⟧) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      map_sub, map_mul, map_one, map_zero, apply_ite ⇑Polynomial.coeToPowerSeries.ringHom,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C]
  have hadj : (1 - (X : R[X]) • M.map (C : R →+* R[X])).adjugate.map
        Polynomial.coeToPowerSeries.ringHom
      = adjugate (1 - (PowerSeries.X : R⟦X⟧) • M.map (PowerSeries.C : R →+* R⟦X⟧)) := by
    rw [← hFs]; exact RingHom.map_adjugate _ _
  have hdet : (((1 - (X : R[X]) • M.map (C : R →+* R[X])).det : R[X]) : R⟦X⟧)
      = (1 - (PowerSeries.X : R⟦X⟧) • M.map (PowerSeries.C : R →+* R⟦X⟧)).det := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, RingHom.map_det]
    exact congrArg Matrix.det hFs
  rw [derivative_coe, hcp, derivative_det, map_derivative_one_sub_smul, mul_neg, Matrix.trace_neg,
    ← Polynomial.coeToPowerSeries.ringHom_apply, map_neg, AddMonoidHom.map_trace, Matrix.map_mul,
    hMC, hadj, ← smul_resolventSeries_eq_adjugate, smul_mul_assoc, trace_smul,
    trace_resolventSeries_mul, smul_eq_mul, hdet, neg_mul]

end Jacobi

end Matrix

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

omit [Fintype V] [DecidableRel G.Adj] in
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

/-- **The differentiated Bass identity** — composing Bass with Jacobi (brick 1). Applying `d/dX` to
Bass's determinant formula and expanding both determinant derivatives by Jacobi's formula
(`Matrix.derivative_det`): the non-backtracking side `(1-X²)^|V|·det(1-X·B)` and the adjacency side
`(1-X²)^|E|·det(1-X·A+X²(D-1))` have equal derivatives, term by term. This is the polynomial heart of
the Ihara `N_k` spectral formula — the trace generating functions arise on dividing through by the
two determinants (both units in `R⟦X⟧`). -/
theorem derivative_bass :
    derivative ((1 - (X : R[X]) ^ 2) ^ Fintype.card V)
        * (1 - (X : R[X]) • (G.hashimoto R).map C).det
      + (1 - (X : R[X]) ^ 2) ^ Fintype.card V
        * ((1 - (X : R[X]) • (G.hashimoto R).map C).adjugate
          * (1 - (X : R[X]) • (G.hashimoto R).map C).map derivative).trace
    = derivative ((1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card)
        * (1 - (X : R[X]) • (G.adjMatrix R).map C
            + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).det
      + (1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card
        * ((1 - (X : R[X]) • (G.adjMatrix R).map C
            + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).adjugate
          * (1 - (X : R[X]) • (G.adjMatrix R).map C
            + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).map derivative).trace := by
  have h := congrArg derivative (G.bass_charpolyRev R)
  rwa [derivative_mul, derivative_mul, Matrix.derivative_det, Matrix.derivative_det] at h

open scoped PowerSeries in
/-- **The isolated Ihara `N_k` identity** (cleared form). Differentiating Bass's identity in `R⟦X⟧`
and substituting Newton's identity for matrix traces (`Matrix.charpolyRev_logDeriv`) on the
non-backtracking side isolates the `N_k = tr(Bᵏ)` generating function, expressed through the
adjacency data `Q = det(1 - X·A + X²(D-1))`:
`(1-X²)^|V| · det(1-X·B) · ∑ₖ tr(Bᵏ⁺¹)Xᵏ = det(1-X·B)·((1-X²)^|V|)′ - (1-X²)^|E|·Q′ - Q·((1-X²)^|E|)′`.
The two `(1-X²)`-powers and the determinants are units in `R⟦X⟧`, so dividing through gives the
generating function `∑ₖ N_{k+1} Xᵏ` purely in terms of the adjacency spectrum. -/
theorem ihara_Nk_isolated :
    (((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
        * ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)
        * PowerSeries.mk (fun k => ((G.hashimoto R) ^ (k + 1)).trace)
      = ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)
          * d⁄dX R (((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
        - (((1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card : R[X]) : R⟦X⟧)
          * d⁄dX R ((1 - (X : R[X]) • (G.adjMatrix R).map C
              + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).det : R⟦X⟧)
        - ((1 - (X : R[X]) • (G.adjMatrix R).map C
              + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).det : R⟦X⟧)
          * d⁄dX R (((1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card : R[X]) : R⟦X⟧) := by
  have hbass := congrArg Polynomial.coeToPowerSeries.ringHom (G.bass_charpolyRev R)
  rw [map_mul, map_mul] at hbass
  simp only [Polynomial.coeToPowerSeries.ringHom_apply] at hbass
  have hN : d⁄dX R ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)
      = -((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)
        * PowerSeries.mk (fun k => ((G.hashimoto R) ^ (k + 1)).trace) :=
    Matrix.charpolyRev_logDeriv (G.hashimoto R)
  have hd := congrArg (⇑(d⁄dX R)) hbass
  rw [Derivation.leibniz, Derivation.leibniz, hN] at hd
  simp only [smul_eq_mul] at hd
  linear_combination -hd

open scoped PowerSeries in
/-- **The explicit Ihara `N_k` generating function.** Dividing `ihara_Nk_isolated` through by the
unit `(1-X²)^|V|·det(1-X·B)` (constant term `1`, inverted by `PowerSeries.invOfUnit`) yields the
non-backtracking trace power sums `∑ₖ tr(Bᵏ⁺¹) Xᵏ` explicitly in terms of the adjacency spectrum. -/
theorem ihara_Nk_explicit :
    PowerSeries.mk (fun k => ((G.hashimoto R) ^ (k + 1)).trace)
      = PowerSeries.invOfUnit
          ((((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
            * ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)) 1
        * (((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)
            * d⁄dX R (((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
          - (((1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card : R[X]) : R⟦X⟧)
            * d⁄dX R ((1 - (X : R[X]) • (G.adjMatrix R).map C
                + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).det : R⟦X⟧)
          - ((1 - (X : R[X]) • (G.adjMatrix R).map C
                + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).det : R⟦X⟧)
            * d⁄dX R (((1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card : R[X]) : R⟦X⟧)) := by
  have hcc : PowerSeries.constantCoeff
      ((((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
        * ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)) = ((1 : Rˣ) : R) := by
    rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_eq_eval_zero, eval_det_eq,
      map_eval_hashimoto, Units.val_one]
    simp
  have key : PowerSeries.invOfUnit
      ((((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
        * ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)) 1
      * ((((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
        * ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)) = 1 := by
    rw [mul_comm]; exact PowerSeries.mul_invOfUnit _ 1 hcc
  rw [← G.ihara_Nk_isolated R, ← mul_assoc, key, one_mul]

end SpectralField

section Ihara
open scoped PowerSeries
variable (R : Type*) [CommRing R]

/-- **The Ihara `N_k` generating function.** Specialising Newton's identity for matrix traces
(`Matrix.charpolyRev_logDeriv`) to the Hashimoto non-backtracking operator `B = G.hashimoto R`: the
logarithmic derivative of the reciprocal Ihara zeta `det(1 - X·B) = charpolyRev B` generates the
non-backtracking closed-walk counts `N_{k+1} = tr(B^{k+1})`,
`(det(1 - X·B))′ = -det(1 - X·B) · ∑ₖ N_{k+1} Xᵏ`. -/
theorem ihara_Nk_genfn :
    d⁄dX R (charpolyRev (G.hashimoto R) : R⟦X⟧)
      = -(charpolyRev (G.hashimoto R) : R⟦X⟧)
        * PowerSeries.mk fun k => ((G.hashimoto R) ^ (k + 1)).trace :=
  Matrix.charpolyRev_logDeriv (G.hashimoto R)

end Ihara

end SimpleGraph
