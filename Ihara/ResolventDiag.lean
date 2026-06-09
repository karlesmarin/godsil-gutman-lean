/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Ihara.ResolventGenfun
import Ihara.AdjugateDiagMinor
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Resolvent diagonal = principal-minor / determinant — Godsil moment theorem, Stone 3 (assembly)

Welding the two Stone-3 bricks:
* `resolventGenfun_eq_inv` (3a): the generating function `Σ_k (Mᵏ)_{ii} Xᵏ` is the diagonal entry of
  `(1 - X·M)⁻¹` over `R⟦X⟧`;
* `adjugate_diag_eq_det_submatrix_ne` (3b): `adjugate B i i = det(B∖i)` for an arbitrary `Fintype`;

through Cramer's rule (`Matrix.inv_def`, `B⁻¹ = Ring.inverse(det B) • adjugate B`). The result is the
**diagonal resolvent as a determinant ratio**, in cleared-denominator form:

  `(Σ_k (Mᵏ)_{ii} Xᵏ) · det(1 - X·M) = det((1 - X·M)∖i)`.

Both determinants are `charpolyRev`-style series (`det(1 - X·M)` over `R⟦X⟧`); `(1 - X·M)∖i = 1 -
X·(M∖i)` is the same construction for the deleted matrix, so the right side is the resolvent
denominator of `M∖i`. This is exactly identity A2 of `research/godsil-numeric/verify_moment_bridge.py`
(diagonal resolvent `= charpoly(T∖root)/charpoly(T)`), now sorry-free for a general index. Composed
with `godsil_resolvent_charpoly_form` (`charpoly(T∖r)·μ(G) = charpoly(T)·μ(G∖v)`) and summed over the
base vertex it lands the trace side of Godsil's moment theorem.
-/

open PowerSeries

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

omit [Fintype n] in
/-- **Deleting row/column `i` of `1 - X·M` gives `1 - X·(M∖i)`.** The construction commutes with the
principal `{j ≠ i}` submatrix (`1`, the `X•` scalar, and `map C` all restrict entrywise; `1`
restricts to `1` because `Subtype.val` is injective). -/
theorem one_sub_X_smul_submatrix_ne (M : Matrix n n R) (i : n) :
    (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)).submatrix
        (Subtype.val : {j // j ≠ i} → n) (Subtype.val : {j // j ≠ i} → n)
      = 1 - (X : R⟦X⟧) •
        (M.submatrix (Subtype.val : {j // j ≠ i} → n) (Subtype.val : {j // j ≠ i} → n)).map
          (C : R →+* R⟦X⟧) := by
  ext s t
  simp only [submatrix_apply, sub_apply, smul_apply, map_apply, smul_eq_mul, one_apply,
    Subtype.val_injective.eq_iff]

/-- **Diagonal resolvent as a determinant ratio (cleared denominators), Stone 3.** For any matrix `M`
over a commutative ring and index `i`, the generating function of the diagonal matrix powers times
`det(1 - X·M)` equals the determinant of the `i`-deleted block:

  `(Σ_k (Mᵏ)_{ii} Xᵏ) · det(1 - X·M) = det((1 - X·M)∖i)`.

`1 - X·M` is invertible over `R⟦X⟧` (`det` has constant term `det 1 = 1`, a unit — extracted from the
Neumann identity `(1-X·M)·resolventGenfun = 1`); Cramer turns the diagonal of its inverse into
`Ring.inverse(det)·adjugate`, the determinant cancels the inverse, and `adjugate B i i = det(B∖i)`
(`adjugate_diag_eq_det_submatrix_ne`). -/
theorem resolventGenfun_diag_mul_det (M : Matrix n n R) (i : n) :
    M.resolventGenfun i i * det (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧))
      = det ((1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)).submatrix
          (Subtype.val : {j // j ≠ i} → n) (Subtype.val : {j // j ≠ i} → n)) := by
  set B := (1 : Matrix n n R⟦X⟧) - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧) with hBdef
  have hBQ : B * M.resolventGenfun = 1 := one_sub_X_smul_mul_resolventGenfun M
  have hdet1 : det B * det M.resolventGenfun = 1 := by rw [← det_mul, hBQ, det_one]
  have hunit : IsUnit (det B) :=
    ⟨⟨det B, det M.resolventGenfun, hdet1, by rw [mul_comm]; exact hdet1⟩, rfl⟩
  rw [resolventGenfun_eq_inv, inv_def, smul_apply, smul_eq_mul, mul_right_comm,
    Ring.inverse_mul_cancel _ hunit, one_mul, adjugate_diag_eq_det_submatrix_ne]

/-! ## Bridge to `charpolyRev`

`det(1 - X·M)` over `R⟦X⟧` is the image of the reversed characteristic polynomial `charpolyRev M`
(a `R[X]` object) under the canonical coercion `R[X] → R⟦X⟧`. This connects the resolvent
determinants above to the polynomial world where Godsil's matching/charpoly identities live. -/

/-- **`det(1 - X·M)` over `R⟦X⟧` is the coercion of `charpolyRev M`.** The canonical ring
homomorphism `R[X] → R⟦X⟧` commutes with `det` (`RingHom.map_det`) and sends `X ↦ X`, `C a ↦ C a`
(`Polynomial.coe_X`, `Polynomial.coe_C`), turning Mathlib's `charpolyRev M = det(1 - X·M.map C)` in
`R[X]` into the same determinant in `R⟦X⟧`. -/
theorem coe_charpolyRev_eq_det (M : Matrix n n R) :
    (charpolyRev M : R⟦X⟧)
      = det (1 - (PowerSeries.X : R⟦X⟧) • M.map (PowerSeries.C : R →+* R⟦X⟧)) := by
  rw [charpolyRev, ← Polynomial.coeToPowerSeries.ringHom_apply, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, map_apply, sub_apply, smul_apply, one_apply, smul_eq_mul,
    map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X, Polynomial.coe_C]

/-- **Diagonal resolvent as a `charpolyRev` ratio (cleared denominators), Stone 3 + bridge.**
`(Σ_k (Mᵏ)_{ii} Xᵏ) · ↑charpolyRev(M) = ↑charpolyRev(M∖i)`: combine `resolventGenfun_diag_mul_det`
with `coe_charpolyRev_eq_det` on both determinants (`one_sub_X_smul_submatrix_ne` identifies the
deleted block as `1 - X·(M∖i)`). The matching-polynomial form of Godsil's resolvent step. -/
theorem resolventGenfun_diag_mul_coe_charpolyRev (M : Matrix n n R) (i : n) :
    M.resolventGenfun i i * (charpolyRev M : R⟦X⟧)
      = (charpolyRev (M.submatrix (Subtype.val : {j // j ≠ i} → n)
          (Subtype.val : {j // j ≠ i} → n)) : R⟦X⟧) := by
  rw [coe_charpolyRev_eq_det, coe_charpolyRev_eq_det, resolventGenfun_diag_mul_det,
    one_sub_X_smul_submatrix_ne]

end Matrix
