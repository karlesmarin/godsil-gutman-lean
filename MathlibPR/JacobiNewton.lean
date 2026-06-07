/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Jacobi's formula and Newton's identity for matrix traces

For a square matrix over a commutative ring this file proves two classical facts that, although
elementary, were missing from the library:

* `Matrix.derivative_det` — **Jacobi's formula** `(det M)′ = tr(adjugate M · M′)` for a matrix `M`
  of polynomials. Mathlib previously had only the analytic statement (the derivative of `det` as a
  map between normed spaces); this is the purely algebraic version, over an arbitrary commutative
  ring, with `Polynomial.derivative`.
* `Matrix.charpolyRev_logDeriv` — **Newton's identity for matrix traces**: the logarithmic
  derivative of the reversed characteristic polynomial collects the trace power sums,
  `(charpolyRev M)′ = - charpolyRev M · ∑ₖ tr(Mᵏ⁺¹) Xᵏ` in `R⟦X⟧`. This is the matrix-trace
  counterpart of `Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities` (which only treats
  the abstract symmetric polynomials), and it specialises at the linear coefficient to the existing
  `Matrix.coeff_charpolyRev_eq_neg_trace`.

The proof of Newton's identity is eigenvalue-free: it goes through the **resolvent series**
`resolventSeries M = ∑ₖ Mᵏ Xᵏ`, the formal inverse of `1 - X • M` in `Matrix n n R⟦X⟧`, whose trace
is the trace generating function `∑ₖ tr(Mᵏ) Xᵏ`.

## Main definitions

* `Matrix.resolventSeries`

## Main results

* `Matrix.one_sub_smul_mul_resolventSeries` — the resolvent is the inverse of `1 - X • M`.
* `Matrix.trace_resolventSeries` — its trace is `∑ₖ tr(Mᵏ) Xᵏ`.
* `Matrix.derivative_det` — Jacobi's formula.
* `Matrix.charpolyRev_logDeriv` — Newton's identity for matrix traces.
-/

open Finset

namespace Matrix

open PowerSeries

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-! ## The resolvent series and the trace generating function -/

/-- The matrix **resolvent series** `∑ₖ Mᵏ Xᵏ`, an `n × n` matrix of formal power series whose
`(i, j)` entry has `k`-th coefficient `(Mᵏ) i j`. -/
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

/-- **The resolvent inverts `1 - X • M`.** Hence `resolventSeries M = (1 - X • M)⁻¹` in
`Matrix n n R⟦X⟧`, and the trace generating function `trace_resolventSeries` is `tr((1 - X M)⁻¹)`. -/
theorem one_sub_smul_mul_resolventSeries (M : Matrix n n R) :
    (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)) * resolventSeries M = 1 := by
  rw [sub_mul, one_mul, smul_mul_assoc]
  nth_rewrite 1 [resolventSeries_fixedPoint M]
  abel

/-- The adjugate of `1 - X • M` over `R⟦X⟧` is `det(1 - X • M)` times the resolvent series — the
matrix form of `adj F = det F · F⁻¹`, valid because the resolvent inverts `1 - X • M`. -/
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

/-- The shifted trace generating function: `tr(resolventSeries M · M) = ∑ₖ tr(Mᵏ⁺¹) Xᵏ`. -/
theorem trace_resolventSeries_mul (M : Matrix n n R) :
    (resolventSeries M * M.map (C : R →+* R⟦X⟧)).trace = mk fun k => (M ^ (k + 1)).trace := by
  ext k
  simp only [Matrix.trace, Matrix.diag_apply, map_sum, Matrix.mul_apply, Matrix.map_apply,
    coeff_mul_C, coeff_resolventSeries, coeff_mk, pow_succ]

/-! ## Jacobi's formula -/

section Jacobi

open Polynomial

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
/-- The entrywise derivative of the polynomial matrix `1 - X • M` is `-M`. -/
theorem map_derivative_one_sub_smul (M : Matrix n n R) :
    (1 - (X : R[X]) • M.map (C : R →+* R[X])).map derivative = -(M.map (C : R →+* R[X])) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.neg_apply, Polynomial.derivative_sub, apply_ite Polynomial.derivative,
    Polynomial.derivative_one, Polynomial.derivative_zero, ite_self, zero_sub,
    Polynomial.derivative_mul, Polynomial.derivative_X, one_mul, Polynomial.derivative_C,
    mul_zero, add_zero]

/-! ## Newton's identity for matrix traces -/

/-- **Newton's identity for matrix traces** — the fusion of Jacobi's formula (`derivative_det`) and
the resolvent trace generating function (`trace_resolventSeries`). The logarithmic derivative of the
reversed characteristic polynomial, as a formal power series, collects the trace power sums:
`(charpolyRev M)′ = - charpolyRev M · ∑ₖ tr(Mᵏ⁺¹) Xᵏ`.

Equivalently `∑_{k ≥ 1} tr(Mᵏ) Xᵏ = - X · (charpolyRev M)′ / charpolyRev M`. Over an arbitrary
`CommRing`, eigenvalue-free. At the linear coefficient this specialises to
`Matrix.coeff_charpolyRev_eq_neg_trace`. -/
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
