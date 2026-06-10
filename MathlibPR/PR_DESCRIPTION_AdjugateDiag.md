# feat(LinearAlgebra/Matrix): diagonal of the adjugate as a principal-minor determinant (general index)

## Summary

Adds one classical, elementary lemma that was missing from Mathlib for a general `Fintype` index:

- **`Matrix.adjugate_diag_eq_det_submatrix_ne`** — `adjugate A i i = det (A.submatrix val val)` where
  `val : {j // j ≠ i} → n`, for `A : Matrix n n R` over any `CommRing R`. In words: the `(i, i)` entry
  of the adjugate equals the determinant of the principal minor of `A` obtained by deleting row `i` and
  column `i`.

## Why

Mathlib already has this cofactor identity, but **only for `Fin n.succ`**
(`adjugate_fin_succ_eq_det_submatrix`), proved via `Fin.succAbove` cofactor expansion. The
general-`Fintype` version was absent. It is the natural companion lemma, and it is needed whenever the
deleted-index set is not literally `Fin`: e.g. expressing the diagonal entry of a matrix resolvent
`(1 - X • M)⁻¹ᵢᵢ` as a ratio of (reversed) characteristic polynomials of `M` and `M ∖ i`.

## Design notes

- The proof avoids cofactor expansion and `Fin.succAbove` reindexing entirely. It uses a
  **block-triangular** decomposition: reindex `n ≃ {· = i} ⊕ {· ≠ i}` via `Equiv.sumCompl`, observe
  that `A.updateRow i eᵢ` (whose determinant is `adjugate A i i` by `adjugate_apply`) has its `i`-th row
  equal to the basis vector `eᵢ`, so the top-right `{=i} × {≠i}` block is `0`. Then
  `det_fromBlocks_zero₁₂` factors the determinant into the `1 × 1` block (`= 1`) times the `{≠i}` minor.
- Over an arbitrary `CommRing`; no field, no algebraic closure.

## Files / placement

Self-contained lemma. Imports `Mathlib.LinearAlgebra.Matrix.Adjugate` (where the `Fin` version lives)
and `Mathlib.LinearAlgebra.Matrix.SchurComplement` (for `toBlocks`/`det_fromBlocks_zero₁₂`).

Two reasonable homes (reviewer's choice):
1. Append to `Mathlib/LinearAlgebra/Matrix/Adjugate.lean` — next to `adjugate_fin_succ_eq_det_submatrix`;
   would add the `SchurComplement` import there.
2. New small file `Mathlib/LinearAlgebra/Matrix/AdjugateDiagMinor.lean` (this file) — no import churn in
   `Adjugate.lean`.

Sorry-free; axioms = `[propext, Classical.choice, Quot.sound]`. ~35-line proof, zero linter warnings.

## Provenance

Extracted from a sorry-free formalization of Godsil's moment theorem for the matching polynomial
(`karlesmarin/godsil-gutman-lean`, `Ihara/AdjugateDiagMinor.lean`), where it is the general-index step
`Stone 3b`. Graph-free and of independent linear-algebra interest, hence proposed for upstreaming.
