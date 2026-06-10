/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Diagonal of the adjugate = principal-minor determinant (arbitrary `Fintype` index)

Mathlib has the cofactor identity `adjugate A i i = det (minor of A deleting row/col i)` only for
the indexed type `Fin n.succ` (`adjugate_fin_succ_eq_det_submatrix`, via `Fin.succAbove` cofactor
expansion). This file proves the same fact for an **arbitrary `Fintype` index** `n`, with no
`Fin`-reindexing, by a block-triangular argument.

## Main result

* `Matrix.adjugate_diag_eq_det_submatrix_ne` — `adjugate A i i = det (A.submatrix val val)` where
  `val : {j // j ≠ i} → n`.

## Proof sketch

`adjugate A i i = det (A.updateRow i eᵢ)` (`adjugate_apply`). Reindex `n ≃ {·=i} ⊕ {·≠i}`
(`Equiv.sumCompl`); the `i`-th row of `A.updateRow i eᵢ` is `eᵢ`, so the top-right block vanishes
and `det_fromBlocks_zero₁₂` gives `det = (1×1 block `= 1`) · det(A ∖ i)`.

This is the general-index companion of `adjugate_fin_succ_eq_det_submatrix`; it is used to express
the diagonal of a matrix resolvent `(1 - X • M)⁻¹ᵢᵢ` as a principal-minor ratio of (reversed)
characteristic polynomials.
-/

open Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- **Diagonal of the adjugate is the principal-minor determinant**, for an arbitrary `Fintype`
index: `adjugate A i i = det (A restricted to the indices ≠ i)`. The `Fin`-only Mathlib lemma
`adjugate_fin_succ_eq_det_submatrix` generalised by a block-triangular reindex `n ≃ {·=i} ⊕ {·≠i}`:
`A.updateRow i eᵢ` has its `i`-row equal to `eᵢ`, killing the top-right block, so its determinant
is the product of the `1×1` block (`= 1`) and the `{≠i}` minor. -/
public theorem adjugate_diag_eq_det_submatrix_ne (A : Matrix n n R) (i : n) :
    adjugate A i i
      = det (A.submatrix (Subtype.val : {j // j ≠ i} → n) (Subtype.val : {j // j ≠ i} → n)) := by
  classical
  haveI : Unique {a : n // a = i} := ⟨⟨⟨i, rfl⟩⟩, fun y => Subtype.ext y.2⟩
  rw [adjugate_apply,
    ← det_submatrix_equiv_self (Equiv.sumCompl (· = i)) (A.updateRow i (Pi.single i (1 : R))),
    ← fromBlocks_toBlocks
        ((A.updateRow i (Pi.single i (1 : R))).submatrix
          (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i)))]
  -- top-right block vanishes: row `i` of `A.updateRow i eᵢ` is `eᵢ`, zero off the `i`-th column
  have h12 : ((A.updateRow i (Pi.single i (1 : R))).submatrix
      (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i))).toBlocks₁₂ = 0 := by
    ext s t
    simp only [toBlocks₁₂, of_apply, submatrix_apply, Equiv.sumCompl_apply_inl,
      Equiv.sumCompl_apply_inr, zero_apply]
    rw [show ((s : {a // a = i}) : n) = i from s.2, updateRow_self, Pi.single_apply, if_neg t.2]
  -- `1×1` top-left block has determinant `1`
  have h11 : ((A.updateRow i (Pi.single i (1 : R))).submatrix
      (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i))).toBlocks₁₁.det = 1 := by
    rw [det_unique]
    simp only [toBlocks₁₁, of_apply, submatrix_apply, Equiv.sumCompl_apply_inl]
    rw [show ((default : {a // a = i}) : n) = i from (default : {a // a = i}).2, updateRow_self,
      Pi.single_eq_same]
  -- bottom-right block is `A ∖ i`
  have h22 : ((A.updateRow i (Pi.single i (1 : R))).submatrix
      (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i))).toBlocks₂₂
      = A.submatrix (Subtype.val : {j // j ≠ i} → n) (Subtype.val : {j // j ≠ i} → n) := by
    ext s t
    simp only [toBlocks₂₂, of_apply, submatrix_apply, Equiv.sumCompl_apply_inr]
    rw [updateRow_ne s.2]
  rw [h12, det_fromBlocks_zero₁₂, h11, h22, one_mul]

end Matrix
