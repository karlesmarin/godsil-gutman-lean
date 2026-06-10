import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card

/-!
# Cauchy–Binet formula  (WIP — Lemma A proven, regrouping is `sorry`)

`det (A * B)` for a non-square pair `A : m×n`, `B : n×m` equals the sum over `m`-element subsets
`S ⊆ n` of the product of the two maximal minors selected by `S`.  Absent from Mathlib; entry point
for the Kirchhoff matrix-tree theorem (see `CAUCHY_BINET_PLAN.md`).

Indexing: an `m`-subset `S` of `n` (a `{s : Finset n // s.card = Fintype.card m}`) gives an order
embedding `S.orderEmbOfFin : Fin (card m) ↪o n`; reindex rows of `A` (resp. cols of `B`) through
`Fintype.equivFin m` to get square `Fin (card m) × Fin (card m)` minors.

## Proof architecture
* `det_mul_eq_sum_submatrix` (**Lemma A**, proven): the determinant-of-product expanded over *all*
  functions `g : m → n`, each weighting the column-minor `det (A.submatrix id g)` by `∏ i, B (g i) i`.
* the main theorem then regroups: non-injective `g` give a repeated-column minor (det 0); injective
  `g` factor through a sorted `m`-subset `S` and a permutation, and summing the permutation rebuilds
  `det (B.submatrix S e.symm)`.  (this regrouping is the remaining `sorry`.)
-/

open Matrix Finset Equiv

namespace Matrix

/-- **Lemma A** — determinant of a product expanded over all index functions `g : m → n`.
Each `g` contributes the `m×m` column-minor `A.submatrix id g` weighted by `∏ i, B (g i) i`.
This is Cauchy–Binet *before* grouping the `g`'s by their image. -/
theorem det_mul_eq_sum_submatrix {R : Type*} [CommRing R]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ g : m → n, (A.submatrix id g).det * ∏ i, B (g i) i := by
  conv_lhs => rw [det_apply']
  simp_rw [mul_apply, Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [det_apply', Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id_eq, Finset.prod_mul_distrib]
  ring

/-- **Cauchy–Binet formula.** (Statement; regrouping step is WIP.) -/
theorem det_mul_cauchyBinet {R : Type*} [CommRing R]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [LinearOrder n]
    (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det =
      ∑ S : {s : Finset n // s.card = Fintype.card m},
        (A.submatrix (Fintype.equivFin m).symm (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) (Fintype.equivFin m).symm).det := by
  rw [det_mul_eq_sum_submatrix]
  /- Remaining (the combinatorial regrouping):
     * non-injective `g : m → n` ⇒ `A.submatrix id g` has two equal columns ⇒ det 0;
     * injective `g` factor as `g = (S.orderEmbOfFin) ∘ π ∘ e` with `S = Set.range g` (card m),
       `e := Fintype.equivFin m`, `π : Perm (Fin (card m))`; the sign of `π` moves between the two
       minors and summing over `π` rebuilds `det (B.submatrix (S.orderEmbOfFin) e.symm)`. -/
  sorry

end Matrix
