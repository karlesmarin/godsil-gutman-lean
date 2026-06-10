import Ihara.SpanningTreeMinor
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Kirchhoff's matrix-tree theorem  (Stone 4 — the assembly)

`det L₀ = #spanning trees`: the determinant of the reduced Laplacian (root row/column deleted)
counts the spanning trees of `G`, i.e. the `(card V − 1)`-subsets `S` of `Sym2 V` consisting of
genuine edges whose spanning subgraph `fromEdgeSet S` is a tree.

Chain: `det L₀ = ∑_S det(N₀_S)²` (Stone 2, Cauchy–Binet on `L₀ = N₀N₀ᵀ`) and
`det(N₀_S)² = [S spans a tree]` (Stone 3 dichotomy), so the sum counts the spanning trees.
With `card V − 1` edges, *connected ⟺ tree* (`isTree_iff_connected_and_card`), which is how the
Stone-3 condition is converted to the headline `IsTree` form.

Works over any integral domain (ℤ, ℚ, ℝ, …).
-/

open Finset Matrix Sym2

namespace SimpleGraph

variable (R : Type*) {V : Type*} (G : SimpleGraph V)
variable [Fintype V] [LinearOrder V] [DecidableRel G.Adj] (v₀ : V)

/-- Deleting one vertex drops the cardinality by exactly one. -/
theorem card_ne_root_add_one : Fintype.card {v : V // v ≠ v₀} + 1 = Fintype.card V := by
  classical
  have h1 : Fintype.card {v : V // v ≠ v₀}
      = Fintype.card V - Fintype.card {v : V // v = v₀} :=
    Fintype.card_subtype_compl _
  rw [Fintype.card_subtype_eq] at h1
  have h2 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨v₀⟩
  omega

omit [DecidableRel G.Adj] in
/-- For a `(card V − 1)`-set of genuine edges, the spanning subgraph is connected iff it is a
tree: the edge count is exactly the tree count, so acyclicity is free. -/
theorem connected_fromEdgeSet_iff_isTree (S : Finset (Sym2 V))
    (hS : S.card = Fintype.card {v : V // v ≠ v₀}) (hsub : ↑S ⊆ G.edgeSet) :
    (fromEdgeSet (↑S : Set (Sym2 V))).Connected ↔ (fromEdgeSet (↑S : Set (Sym2 V))).IsTree := by
  constructor
  · intro hconn
    rw [isTree_iff_connected_and_card]
    refine ⟨hconn, ?_⟩
    have hno_diag : (↑S : Set (Sym2 V)) \ Sym2.diagSet = ↑S :=
      sdiff_eq_left.mpr (Set.disjoint_left.mpr fun e heS hediag =>
        G.not_isDiag_of_mem_edgeSet (hsub heS) hediag)
    have hcard_edge : Nat.card (fromEdgeSet (↑S : Set (Sym2 V))).edgeSet = S.card := by
      rw [edgeSet_fromEdgeSet, hno_diag, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    rw [hcard_edge, hS, Nat.card_eq_fintype_card]
    exact card_ne_root_add_one v₀
  · exact fun h => h.connected

open scoped Classical in
/-- **Kirchhoff's matrix-tree theorem.**  Over any integral domain, the determinant of the
reduced Laplacian of `G` (delete the row and column of any root `v₀`) equals the number of
spanning trees of `G`, counted as the `(card V − 1)`-subsets of `Sym2 V` consisting of edges of
`G` that span a tree. -/
theorem det_reducedLapMatrix_eq_card_spanningTrees [CommRing R] [IsDomain R] :
    (G.reducedLapMatrix R v₀).det
      = ((Finset.univ.filter
          (fun S : {s : Finset (Sym2 V) // s.card = Fintype.card {v : V // v ≠ v₀}} =>
            ↑S.1 ⊆ G.edgeSet ∧ (fromEdgeSet (↑S.1 : Set (Sym2 V))).IsTree)).card : R) := by
  rw [det_reducedLapMatrix_eq_sum_sq]
  calc ∑ S : {s : Finset (Sym2 V) // s.card = Fintype.card {v : V // v ≠ v₀}},
        ((G.reducedIncMatrix R v₀).submatrix
          (Fintype.equivFin {v : V // v ≠ v₀}).symm (S.1.orderEmbOfFin S.2)).det ^ 2
      = ∑ S : {s : Finset (Sym2 V) // s.card = Fintype.card {v : V // v ≠ v₀}},
          if ↑S.1 ⊆ G.edgeSet ∧ (fromEdgeSet (↑S.1 : Set (Sym2 V))).IsTree
            then (1 : R) else 0 := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [sq_det_minor_eq_ite R G v₀ S.1 S.2]
        refine if_congr (and_congr_right fun hsub => ?_) rfl rfl
        exact connected_fromEdgeSet_iff_isTree G v₀ S.1 S.2 hsub
    _ = _ := by
        rw [Finset.sum_boole]

end SimpleGraph

