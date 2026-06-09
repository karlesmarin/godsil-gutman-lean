/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Resolvent generating function of a matrix — Godsil moment theorem, Stone 3 (Neumann brick)

The trace side of Godsil's moment theorem needs the **generating function of the diagonal matrix
powers** `Σ_k (Mᵏ)_{ii} Xᵏ` to be the diagonal entry of the resolvent `(1 - X·M)⁻¹`. This file lands
that Neumann (geometric) series for matrices over a commutative ring, in the formal-power-series
ring `R⟦X⟧`:

  `(1 - X·M) · resolventGenfun M = 1 = resolventGenfun M · (1 - X·M)`,

where `resolventGenfun M` is the matrix over `R⟦X⟧` with `(i,j)` entry `Σ_k (Mᵏ)_{ij} Xᵏ`. Since
`det(1 - X·M)` has constant term `det 1 = 1` (a unit), `1 - X·M` is invertible over `R⟦X⟧` and the
resolvent generating function IS its inverse (`resolventGenfun_eq_inv`).

This is the matrix analogue of `PowerSeries.geomSeries_mul_one_sub` (Stone 4); together with the
adjugate-diagonal = principal-minor identity (the remaining Stone-3 brick, relating
`(1 - X·M)⁻¹_{ii}` to `charpolyRev` of the deleted matrix) it expresses `Σ_k (Mᵏ)_{ii} Xᵏ` as the
ratio `charpolyRev(M∖i)/charpolyRev(M)` — de-risked in `research/godsil-numeric/verify_moment_bridge.py`
(identity A2, exact across 6 graphs).
-/

open PowerSeries

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The **resolvent generating function** of `M`: the matrix over `R⟦X⟧` whose `(i,j)` entry is the
generating function `Σ_k (Mᵏ)_{ij} Xᵏ` of the matrix powers. -/
noncomputable def resolventGenfun (M : Matrix n n R) : Matrix n n R⟦X⟧ :=
  Matrix.of fun i j => mk fun k => (M ^ k) i j

@[simp] theorem resolventGenfun_apply (M : Matrix n n R) (i j : n) :
    M.resolventGenfun i j = mk fun k => (M ^ k) i j := rfl

/-- `(M.map C) · resolventGenfun M` shifts the powers up by one: its `(i,j)` entry is
`Σ_k (Mᵏ⁺¹)_{ij} Xᵏ`. (Coefficient `k`: `Σ_l M_{il} (Mᵏ)_{lj} = (M·Mᵏ)_{ij} = (Mᵏ⁺¹)_{ij}`.) -/
theorem map_C_mul_resolventGenfun (M : Matrix n n R) :
    M.map (C : R →+* R⟦X⟧) * M.resolventGenfun
      = Matrix.of fun i j => mk fun k => (M ^ (k + 1)) i j := by
  ext i j n
  rw [mul_apply, map_sum]
  simp only [map_apply, resolventGenfun_apply, coeff_C_mul, coeff_mk, of_apply]
  rw [← mul_apply, ← pow_succ']

/-- **Matrix Neumann series (left form).** `(1 - X·M) · resolventGenfun M = 1` over `R⟦X⟧`. The
telescoping geometric series `Σ_k Xᵏ Mᵏ`: coefficient `k` of the product is `(Mᵏ) - (Mᵏ) = 0` for
`k ≥ 1`, and `M⁰ = 1` at `k = 0`. -/
theorem one_sub_X_smul_mul_resolventGenfun (M : Matrix n n R) :
    (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)) * M.resolventGenfun = 1 := by
  rw [sub_mul, one_mul, smul_mul_assoc, map_C_mul_resolventGenfun]
  ext i j k
  rw [sub_apply, resolventGenfun_apply, smul_apply, of_apply, smul_eq_mul, map_sub]
  rcases k with _ | m
  · rw [coeff_zero_X_mul, sub_zero, coeff_mk, one_apply]
    by_cases h : i = j <;> simp [coeff_one, h]
  · rw [coeff_succ_X_mul, coeff_mk, coeff_mk, one_apply]
    by_cases h : i = j <;> simp [coeff_one, h]

/-- **Matrix Neumann series (right form).** `resolventGenfun M · (1 - X·M) = 1`. Same telescoping
with the powers shifted on the right (`Σ_l (Mᵏ)_{il} M_{lj} = (Mᵏ⁺¹)_{ij}`). -/
theorem resolventGenfun_mul_one_sub_X_smul (M : Matrix n n R) :
    M.resolventGenfun * (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)) = 1 := by
  have hQM : M.resolventGenfun * M.map (C : R →+* R⟦X⟧)
      = Matrix.of fun i j => mk fun k => (M ^ (k + 1)) i j := by
    ext i j n
    rw [mul_apply, map_sum]
    simp only [map_apply, resolventGenfun_apply, coeff_mul_C, coeff_mk, of_apply]
    rw [← mul_apply, ← pow_succ]
  rw [mul_sub, mul_one, mul_smul_comm, hQM]
  ext i j k
  rw [sub_apply, resolventGenfun_apply, smul_apply, of_apply, smul_eq_mul, map_sub]
  rcases k with _ | m
  · rw [coeff_zero_X_mul, sub_zero, coeff_mk, one_apply]
    by_cases h : i = j <;> simp [coeff_one, h]
  · rw [coeff_succ_X_mul, coeff_mk, coeff_mk, one_apply]
    by_cases h : i = j <;> simp [coeff_one, h]

/-- **`1 - X·M` is invertible over `R⟦X⟧`, with inverse the resolvent generating function.** Its
determinant `charpolyRev`-style series has constant term `det 1 = 1`, a unit; the explicit two-sided
inverse is `resolventGenfun M` (`one_sub_X_smul_mul_resolventGenfun` + `resolventGenfun_mul_…`). -/
theorem resolventGenfun_eq_inv (M : Matrix n n R) :
    M.resolventGenfun = (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧))⁻¹ :=
  (inv_eq_left_inv (resolventGenfun_mul_one_sub_X_smul M)).symm

end Matrix
