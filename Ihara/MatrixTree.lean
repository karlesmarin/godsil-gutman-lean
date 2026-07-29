/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Ihara.CauchyBinet
import Ihara.OrientedIncidence

/-!
# Reduced Laplacian and the sum-of-squared-minors identity  (Stone 2 of matrix-tree)

Delete a root vertex `v₀`: the reduced Laplacian `L₀` (rows/cols `≠ v₀`) factors through the
reduced oriented incidence matrix `N₀` as `L₀ = N₀ * N₀ᵀ` (restriction of Stone 1), and
Cauchy–Binet (`Ihara/CauchyBinet.lean`) turns its determinant into a sum of *squares* of maximal
minors, one per `(card V − 1)`-subset of potential edges:

  `det L₀ = ∑_S det(N₀_S)²`  (`det_reducedLapMatrix_eq_sum_sq`).

Stone 3 will identify `det(N₀_S) = ±1` exactly when `S` is (the edge set of) a spanning tree and
`0` otherwise, giving Kirchhoff's matrix-tree theorem `det L₀ = #spanning trees`.

A `LinearOrder` on `Sym2 V` (needed by Cauchy–Binet's sorted-subset indexing) is induced from the
linear order on `V` by `e ↦ (inf e, sup e)` lexicographically.
-/

open Finset Matrix Sym2

namespace SimpleGraph

/-- Linear order on unordered pairs, via the lexicographic order on `(inf, sup)`.  Scoped: this is
just the indexing device Cauchy–Binet needs, not a canonical structure. -/
scoped instance sym2LinearOrder {V : Type*} [LinearOrder V] : LinearOrder (Sym2 V) :=
  LinearOrder.lift' (fun e => toLex (e.inf, e.sup)) fun e₁ e₂ h =>
    Sym2.inf_eq_inf_and_sup_eq_sup.1 (by
      have := toLex.injective h
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩)

variable (R : Type*) {V : Type*} (G : SimpleGraph V)
variable [Fintype V] [LinearOrder V] [DecidableRel G.Adj] (v₀ : V)

/-- The reduced oriented incidence matrix: delete the row of the root `v₀`. -/
def reducedIncMatrix [Zero R] [One R] [Neg R] : Matrix {v // v ≠ v₀} (Sym2 V) R :=
  (G.orientedIncMatrix R).submatrix Subtype.val id

/-- The reduced Laplacian: delete row and column of the root `v₀`. -/
def reducedLapMatrix [AddGroupWithOne R] : Matrix {v // v ≠ v₀} {v // v ≠ v₀} R :=
  (G.lapMatrix R).submatrix Subtype.val Subtype.val

variable {R}

/-- Stone 1 restricted: the reduced Laplacian is the Gram matrix of the reduced oriented
incidence matrix. -/
theorem reducedLapMatrix_eq_mul_transpose [Ring R] :
    G.reducedLapMatrix R v₀ = G.reducedIncMatrix R v₀ * (G.reducedIncMatrix R v₀)ᵀ := by
  rw [reducedLapMatrix, ← orientedIncMatrix_mul_transpose,
    submatrix_mul _ _ _ id _ Function.bijective_id, reducedIncMatrix, transpose_submatrix]

/-- **Sum-of-squared-minors identity.** Cauchy–Binet applied to `L₀ = N₀ * N₀ᵀ`: the determinant
of the reduced Laplacian is the sum, over all `(card V − 1)`-subsets `S` of `Sym2 V`, of the
square of the maximal minor of `N₀` with columns `S`. -/
theorem det_reducedLapMatrix_eq_sum_sq [CommRing R] :
    (G.reducedLapMatrix R v₀).det
      = ∑ S : {s : Finset (Sym2 V) // s.card = Fintype.card {v // v ≠ v₀}},
          ((G.reducedIncMatrix R v₀).submatrix
            (Fintype.equivFin {v // v ≠ v₀}).symm (S.1.orderEmbOfFin S.2)).det ^ 2 := by
  rw [reducedLapMatrix_eq_mul_transpose, Matrix.det_mul_cauchyBinet]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [sq]
  congr 1
  rw [← Matrix.det_transpose, transpose_submatrix, Matrix.transpose_transpose]

end SimpleGraph
