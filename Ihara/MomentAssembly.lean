/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Ihara.MomentBridge
import Ihara.GodsilMoment
import Ihara.PowerSumLogDeriv
import Ihara.ResolventDiag

/-!
# Godsil moment theorem — final assembly (weld)

This file welds the matching side and the trace side of Godsil's moment theorem
`matchingPowerSum G k = treeLikeWalkCount G k` into a single power-series identity.

## The chain

Trace side (per path tree `T_v = pathTree v`, root `r`):
* Stone 1 `treeLikeWalkCount_eq_sum_pathTree_adjMatrix_pow`: `tlwc G k = Σ_v [A(T_v)ᵏ]_{r r}`.
* Stone 3 `resolventGenfun_diag_mul_coe_charpolyRev`: `(Σ_k [A(T_v)ᵏ]_{rr} Xᵏ)·↑charpolyRev(A T_v) =
  ↑charpolyRev(A(T_v)∖r)` (submatrix form).
* **Reconciliation (this file):** `charpolyRev(A(T_v)∖r) = charpolyRev(A((T_v).deleteIncidenceSet r))`
  — the isolated-root path tree. Because `A(deleteIncidenceSet r)` has a zero row/column at `r`, the
  matrix `1 - X·A(delInc r)` has row `r` equal to `eᵣ`, so its determinant collapses to the `{≠r}`
  minor (`det_eq_det_submatrix_ne_of_row_eq_single`, the block-triangular lemma below), which is the
  same minor `Stone 3` produces; the `{≠r}` blocks of `A(delInc r)` and `A(T_v)` agree.
* Forest bridge `matchingPoly_pathTree_eq_charpoly` + `godsil_resolvent_charpoly_form`: turn the
  per-tree `charpolyRev` ratio into the **graph** ratio `↑reverse μ(G−v)/↑reverse μ(G)`.

Matching side: `matchingPowerSum_genfun` + `geomSeries_sum_mul_prod` (★) + `derivative_prod_X_sub_C`
(B2) + `reverse_prod_X_sub_C` (B3) + splitting `μ_ℂ = ∏(X-θ)`.

Both meet at `mk(·)·↑reverse μ = ↑reverse(X·μ')` (vertex-deletion `Σ_v μ(G.deleteIncidenceSet v) =
X·μ'`), and `↑reverse μ` is a unit (constant term = leading coeff of the monic `μ` = 1), so the two
generating functions coincide and the coefficients give the moment theorem.

This file proceeds milestone by milestone; see the section markers.
-/

open Matrix PowerSeries

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- **(GL) Determinant collapses to a principal minor when a row is a basis vector.** If row `i` of
`B` is `eᵢ = Pi.single i 1`, then `det B = det (B∖i)` (the `{j ≠ i}` principal minor). Block-triangular
reindex `n ≃ {·=i} ⊕ {·≠i}` (`Equiv.sumCompl`): row `i` being `eᵢ` kills the top-right block, so
`det_fromBlocks_zero₁₂` factors the determinant as `(1×1 block = 1) · det(B∖i)`. This is the
matrix-with-an-isolated-index determinant, the abstraction of `adjugate_diag_eq_det_submatrix_ne`. -/
theorem det_eq_det_submatrix_ne_of_row_eq_single (B : Matrix n n R) (i : n)
    (hrow : B i = Pi.single i (1 : R)) :
    det B = det (B.submatrix (Subtype.val : {j // j ≠ i} → n) (Subtype.val : {j // j ≠ i} → n)) := by
  classical
  haveI : Unique {a : n // a = i} := ⟨⟨⟨i, rfl⟩⟩, fun y => Subtype.ext y.2⟩
  rw [← det_submatrix_equiv_self (Equiv.sumCompl (· = i)) B,
    ← fromBlocks_toBlocks (B.submatrix (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i)))]
  have h12 : (B.submatrix (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i))).toBlocks₁₂ = 0 := by
    ext s t
    simp only [toBlocks₁₂, of_apply, submatrix_apply, Equiv.sumCompl_apply_inl,
      Equiv.sumCompl_apply_inr, zero_apply]
    rw [show ((s : {a // a = i}) : n) = i from s.2, hrow, Pi.single_apply, if_neg t.2]
  have h11 : (B.submatrix (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i))).toBlocks₁₁.det = 1 := by
    rw [det_unique]
    simp only [toBlocks₁₁, of_apply, submatrix_apply, Equiv.sumCompl_apply_inl]
    rw [show ((default : {a // a = i}) : n) = i from (default : {a // a = i}).2, hrow,
      Pi.single_eq_same]
  have h22 : (B.submatrix (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i))).toBlocks₂₂
      = B.submatrix (Subtype.val : {j // j ≠ i} → n) (Subtype.val : {j // j ≠ i} → n) := by
    ext s t
    simp only [toBlocks₂₂, of_apply, submatrix_apply, Equiv.sumCompl_apply_inr]
  rw [h12, det_fromBlocks_zero₁₂, h11, h22, one_mul]

end Matrix

namespace SimpleGraph

open Matrix PowerSeries

variable {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]

omit [Fintype V] in
/-- The `r`-th **row** of the adjacency matrix of `G.deleteIncidenceSet r` is zero: deleting all
edges incident to `r` makes `r` isolated, so `r` is adjacent to nothing. -/
theorem adjMatrix_deleteIncidenceSet_self (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (r : V) :
    ((G.deleteIncidenceSet r).adjMatrix R) r = 0 := by
  funext j
  simp [adjMatrix_apply, deleteIncidenceSet_adj]

omit [Fintype V] in
/-- The `{≠r}` **principal submatrix** is unaffected by deleting the edges at `r`: an entry between
two vertices `≠ r` is an edge of `G.deleteIncidenceSet r` iff it is an edge of `G`. -/
theorem adjMatrix_submatrix_deleteIncidenceSet (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (r : V) :
    ((G.deleteIncidenceSet r).adjMatrix R).submatrix
        (Subtype.val : {j // j ≠ r} → V) (Subtype.val : {j // j ≠ r} → V)
      = (G.adjMatrix R).submatrix
        (Subtype.val : {j // j ≠ r} → V) (Subtype.val : {j // j ≠ r} → V) := by
  ext s t
  simp only [submatrix_apply, adjMatrix_apply, deleteIncidenceSet_adj, s.2, t.2, ne_eq,
    not_false_eq_true, and_true]

/-- **(M1) `charpolyRev` reconciliation: deleting all edges at the root = deleting the root index.**
`↑charpolyRev(A(G.deleteIncidenceSet r)) = ↑charpolyRev(A(G)∖r)` in `R⟦X⟧`. `A(G.deleteIncidenceSet r)`
has a zero row at `r`, so `1 - X·A(deleteIncidenceSet r)` has row `r` equal to `eᵣ`; its determinant
collapses to the `{≠r}` minor (`det_eq_det_submatrix_ne_of_row_eq_single`), whose blocks agree with
`A(G)∖r` (`adjMatrix_submatrix_deleteIncidenceSet`). This bridges the **submatrix** form of Stone 3
(`resolventGenfun_diag_mul_coe_charpolyRev`) to the **isolated-root** path tree of
`godsil_resolvent_charpoly_form`. -/
theorem coe_charpolyRev_adjMatrix_deleteIncidenceSet (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (r : V) :
    (charpolyRev ((G.deleteIncidenceSet r).adjMatrix R) : R⟦X⟧)
      = (charpolyRev ((G.adjMatrix R).submatrix
          (Subtype.val : {j // j ≠ r} → V) (Subtype.val : {j // j ≠ r} → V)) : R⟦X⟧) := by
  rw [coe_charpolyRev_eq_det, coe_charpolyRev_eq_det]
  have hrow : (1 - (X : R⟦X⟧) • ((G.deleteIncidenceSet r).adjMatrix R).map
      (C : R →+* R⟦X⟧)) r = Pi.single r 1 := by
    funext j
    simp only [sub_apply, smul_apply, map_apply, smul_eq_mul, one_apply,
      congrFun (adjMatrix_deleteIncidenceSet_self (R := R) G r) j, Pi.zero_apply, map_zero,
      mul_zero, sub_zero, Pi.single_apply, eq_comm (a := r)]
  rw [det_eq_det_submatrix_ne_of_row_eq_single _ r hrow, one_sub_X_smul_submatrix_ne,
    adjMatrix_submatrix_deleteIncidenceSet]

end SimpleGraph
