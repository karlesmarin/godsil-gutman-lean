import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card

/-!
# Cauchy–Binet formula  (WIP — statement first, proof skeleton)

`det (A * B)` for a non-square pair `A : m×n`, `B : n×m` equals the sum over `m`-element subsets
`S ⊆ n` of the product of the two maximal minors selected by `S`.  Absent from Mathlib; entry point
for the Kirchhoff matrix-tree theorem (see `CAUCHY_BINET_PLAN.md`).

Indexing: an `m`-subset `S` of `n` (a `{s : Finset n // s.card = Fintype.card m}`) gives an order
embedding `S.orderEmbOfFin : Fin (card m) ↪o n`; reindex rows of `A` (resp. cols of `B`) through
`Fintype.equivFin m` to get square `Fin (card m) × Fin (card m)` minors.
-/

open Matrix Finset

namespace Matrix

/-- **Cauchy–Binet formula.** (Statement; proof is WIP.) -/
theorem det_mul_cauchyBinet {R : Type*} [CommRing R]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [LinearOrder n]
    (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det =
      ∑ S : {s : Finset n // s.card = Fintype.card m},
        (A.submatrix (Fintype.equivFin m).symm (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) (Fintype.equivFin m).symm).det := by
  /- Proof skeleton (5 steps, see plan):
     1. `det_apply` + `mul_apply`: det(AB) = ∑_σ sgn σ ∏_i ∑_k A i k * B k (σ i)
     2. `Finset.prod_sum`: expand the inner product over `∑_k` into `∑ (φ : m → n) ∏_i …`
     3. swap sums: `∑_φ (∏_i A i (φ i)) * (∑_σ sgn σ ∏_i B (φ i) (σ i))`,
        inner sum = `det (B.submatrix φ id)`
     4. non-injective `φ` ⇒ minor has a repeated row ⇒ det = 0; drop them
     5. group injective `φ` by image `S` (card m): factor `φ = orderEmbOfFin S ∘ perm`,
        sign bookkeeping ⇒ `det(A_{·,S}) * det(B_{S,·})`. -/
  -- Step 1: expand `det (A*B)` over permutations and the matrix product.
  conv_lhs => rw [det_apply']
  simp_rw [mul_apply]
  -- Goal: `∑ σ, sign σ * ∏ i, ∑ k, A (σ i) k * B k i = (subset sum)`.
  sorry

end Matrix
