import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Sym.Sym2.Order

/-!
# Oriented incidence matrix and the Laplacian factorization  (Stone 1 of matrix-tree)

`G.orientedIncMatrix R` is the `V × Sym2 V` matrix with, for each edge `e = s(u,w)`, a `+1` at the
larger endpoint, a `-1` at the smaller endpoint (orientation induced by a `LinearOrder` on `V`),
and `0` elsewhere.  Main result: the factorization

  `N * Nᵀ = G.lapMatrix R`  (`orientedIncMatrix_mul_transpose`),

the first step of the Kirchhoff matrix-tree theorem (see `CAUCHY_BINET_PLAN.md`, Target 2):
Cauchy–Binet (`Ihara/CauchyBinet.lean`) applied to a reduced version of this factorization turns
`det L₀` into a sum of squared maximal minors of `N`, which count spanning trees.

Mathlib has only the *unoriented* `G.incMatrix` (whose Gram matrix is `D + A`, not `D - A`);
the oriented version and the Laplacian factorization are absent (checked v4.30, 2026-06-10).
-/

open Finset Matrix Sym2

namespace SimpleGraph

variable (R : Type*) {V : Type*} (G : SimpleGraph V)

/-- The oriented incidence matrix: for an edge `e` incident to `v`, the entry is `+1` if `v` is
the larger endpoint of `e` and `-1` if it is the smaller one; entries vanish off the incidence
set.  The orientation (edge points from larger to smaller endpoint) is induced by the linear
order on `V`; any orientation gives the same Gram matrix `N * Nᵀ`. -/
def orientedIncMatrix [Zero R] [One R] [Neg R] [LinearOrder V] [DecidableRel G.Adj] :
    Matrix V (Sym2 V) R :=
  .of fun v e => if e ∈ G.incidenceSet v then (if v = e.sup then 1 else -1) else 0

variable {R}

section Ring
variable [Ring R] [LinearOrder V] [DecidableRel G.Adj] {u v w : V} {e : Sym2 V}

theorem orientedIncMatrix_apply :
    G.orientedIncMatrix R v e
      = if e ∈ G.incidenceSet v then (if v = e.sup then 1 else -1) else 0 := rfl

theorem orientedIncMatrix_of_notMem_incidenceSet (h : e ∉ G.incidenceSet v) :
    G.orientedIncMatrix R v e = 0 := by
  rw [orientedIncMatrix_apply, if_neg h]

/-- On its incidence set the oriented entry squares to `1`, so the square of any entry is the
corresponding unoriented incidence entry. -/
theorem orientedIncMatrix_mul_self :
    G.orientedIncMatrix R v e * G.orientedIncMatrix R v e = G.incMatrix R v e := by
  rw [orientedIncMatrix_apply, incMatrix_apply']
  by_cases h : e ∈ G.incidenceSet v
  · rw [if_pos h, if_pos h]
    by_cases hs : v = e.sup <;> simp [hs]
  · simp [h]

/-- The two endpoints of an edge carry opposite signs: the product of the oriented entries of
`u ≠ w` at their common edge `s(u,w)` is `-1`. -/
theorem orientedIncMatrix_apply_mul_apply_of_adj (hadj : G.Adj u w) :
    G.orientedIncMatrix R u s(u, w) * G.orientedIncMatrix R w s(u, w) = -1 := by
  have hne : u ≠ w := hadj.ne
  have hu : s(u, w) ∈ G.incidenceSet u := G.mk'_mem_incidenceSet_left_iff.2 hadj
  have hw : s(u, w) ∈ G.incidenceSet w := G.mk'_mem_incidenceSet_right_iff.2 hadj
  rw [orientedIncMatrix_apply, orientedIncMatrix_apply, if_pos hu, if_pos hw, sup_mk]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs : u ⊔ w = w := sup_eq_right.2 hlt.le
    rw [if_neg (fun h => hlt.ne (h.trans hs)), if_pos (hs.symm)]
    simp
  · have hs : u ⊔ w = u := sup_eq_left.2 hgt.le
    rw [if_pos (hs.symm), if_neg (fun h => hgt.ne (h.trans hs))]
    simp

/-- Distinct vertices see disjoint signed columns away from their common edge: the product of
oriented entries vanishes at every `e ≠ s(u,w)`. -/
theorem orientedIncMatrix_apply_mul_apply_of_ne (hne : u ≠ w) (he : e ≠ s(u, w)) :
    G.orientedIncMatrix R u e * G.orientedIncMatrix R w e = 0 := by
  by_cases hu : e ∈ G.incidenceSet u
  · by_cases hw : e ∈ G.incidenceSet w
    · exact absurd (G.incidenceSet_inter_incidenceSet_subset hne ⟨hu, hw⟩) he
    · rw [G.orientedIncMatrix_of_notMem_incidenceSet hw, mul_zero]
  · rw [G.orientedIncMatrix_of_notMem_incidenceSet hu, zero_mul]

end Ring

section Lap
variable [Ring R] [Fintype V] [LinearOrder V] [DecidableRel G.Adj]

/-- **Laplacian factorization.** The Gram matrix of the oriented incidence matrix is the graph
Laplacian: `N * Nᵀ = D - A`.  (The unoriented incidence matrix gives `D + A` instead; the signs
are what make the Laplacian.) -/
theorem orientedIncMatrix_mul_transpose :
    G.orientedIncMatrix R * (G.orientedIncMatrix R)ᵀ = G.lapMatrix R := by
  ext u w
  rw [mul_apply]
  simp_rw [transpose_apply]
  by_cases huw : u = w
  · subst huw
    simp_rw [G.orientedIncMatrix_mul_self]
    rw [sum_incMatrix_apply, lapMatrix, sub_apply, degMatrix, diagonal_apply_eq,
      adjMatrix_apply, if_neg (G.irrefl), sub_zero]
  · rw [lapMatrix, sub_apply, degMatrix, diagonal_apply_ne _ huw, adjMatrix_apply, zero_sub]
    by_cases hadj : G.Adj u w
    · rw [if_pos hadj, Finset.sum_eq_single s(u, w)
        (fun e _ he => G.orientedIncMatrix_apply_mul_apply_of_ne huw he)
        (fun he => absurd (mem_univ _) he)]
      exact G.orientedIncMatrix_apply_mul_apply_of_adj hadj
    · rw [if_neg hadj, neg_zero]
      refine Finset.sum_eq_zero fun e _ => ?_
      rcases eq_or_ne e s(u, w) with rfl | he
      · rw [G.orientedIncMatrix_of_notMem_incidenceSet
          (fun hmem => hadj (G.mk'_mem_incidenceSet_left_iff.1 hmem)), zero_mul]
      · exact G.orientedIncMatrix_apply_mul_apply_of_ne huw he

end Lap

end SimpleGraph
