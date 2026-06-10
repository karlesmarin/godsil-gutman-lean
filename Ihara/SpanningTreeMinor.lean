import Ihara.MatrixTree
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The spanning-tree minor dichotomy  (Stone 3 of matrix-tree)

For a `(card V − 1)`-subset `S` of `Sym2 V`, the maximal minor `N₀_S` of the reduced oriented
incidence matrix satisfies:

* `det N₀_S = 0` unless `S ⊆ G.edgeSet` and `fromEdgeSet S` is connected
  (zero column, resp. a rootless-component row dependency);
* `det N₀_S ∈ {1, -1}` (stated as `det² = 1`) when `S ⊆ G.edgeSet` and `fromEdgeSet S` is
  connected — with `card V − 1` edges this forces a spanning tree.

Design (Sage-validated, see `CAUCHY_BINET_PLAN.md`): NO leaf-peeling induction.  Connectivity
gives every non-root vertex `u` a *parent edge* (first edge of a geodesic to the root `v₀`);
vertex ↦ parent-edge is injective by distance arithmetic, hence a bijection onto `S` by
cardinality; recolumning the minor by it and sorting rows/columns by the lexicographic key
`(dist · v₀, ·)` makes the matrix upper-triangular with `±1` diagonal.

## Part A — parent machinery (no matrices; works for any connected graph)
-/

open Finset Matrix Sym2

namespace SimpleGraph

variable {V : Type*} {H : SimpleGraph V} {v₀ : V}

/-- Every non-root vertex of a connected graph has a neighbour strictly closer to the root:
the second vertex of a geodesic walk to the root. -/
theorem Connected.exists_adj_dist_succ (hconn : H.Connected) {u : V} (hu : u ≠ v₀) :
    ∃ w, H.Adj u w ∧ H.dist w v₀ + 1 = H.dist u v₀ := by
  obtain ⟨p, hp⟩ := (hconn u v₀).exists_walk_length_eq_dist
  cases p with
  | nil => exact absurd rfl hu
  | @cons _ w _ h q =>
    refine ⟨w, h, le_antisymm ?_ ?_⟩
    · -- dist w v₀ + 1 ≤ dist u v₀ : the tail of a geodesic bounds dist w v₀
      have hq : H.dist w v₀ ≤ q.length := dist_le q
      have : q.length + 1 = H.dist u v₀ := by simpa using hp
      omega
    · -- dist u v₀ ≤ dist w v₀ + 1 : prepend the edge to a geodesic from w
      obtain ⟨r, hr⟩ := (hconn w v₀).exists_walk_length_eq_dist
      have := dist_le (Walk.cons h r)
      simpa [hr] using this

variable (hconn : H.Connected) (v₀)

/-- The parent of a non-root vertex: a fixed neighbour strictly closer to the root. -/
noncomputable def treeParent (u : {v : V // v ≠ v₀}) : V :=
  (hconn.exists_adj_dist_succ u.2).choose

theorem treeParent_adj (u : {v : V // v ≠ v₀}) : H.Adj ↑u (treeParent v₀ hconn u) :=
  (hconn.exists_adj_dist_succ u.2).choose_spec.1

theorem treeParent_dist (u : {v : V // v ≠ v₀}) :
    H.dist (treeParent v₀ hconn u) v₀ + 1 = H.dist ↑u v₀ :=
  (hconn.exists_adj_dist_succ u.2).choose_spec.2

/-- The parent edge of a non-root vertex. -/
noncomputable def parentEdge (u : {v : V // v ≠ v₀}) : Sym2 V :=
  s(↑u, treeParent v₀ hconn u)

theorem parentEdge_mem_edgeSet (u : {v : V // v ≠ v₀}) :
    parentEdge v₀ hconn u ∈ H.edgeSet := (treeParent_adj v₀ hconn u)

/-- Distance arithmetic kills the swap case: the parent-edge map is injective. -/
theorem parentEdge_injective : Function.Injective (parentEdge v₀ hconn) := by
  intro u u' h
  rw [parentEdge, parentEdge, Sym2.eq_iff] at h
  rcases h with ⟨h₁, _⟩ | ⟨h₁, h₂⟩
  · exact Subtype.ext h₁
  · -- u = parent u' and parent u = u' force dist u = dist u + 2
    have d₁ := treeParent_dist v₀ hconn u
    have d₂ := treeParent_dist v₀ hconn u'
    rw [← h₁] at d₂
    rw [h₂] at d₁
    omega

/-- Membership of a vertex in a parent edge pins it down: the vertex itself, or the parent
(which is strictly closer to the root). -/
theorem eq_or_dist_lt_of_mem_parentEdge {x : V} {w : {v : V // v ≠ v₀}}
    (hx : x ∈ parentEdge v₀ hconn w) :
    x = ↑w ∨ H.dist x v₀ < H.dist ↑w v₀ := by
  rw [parentEdge, Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · right
    have := treeParent_dist v₀ hconn w
    omega

/-!
## Part B — the degenerate cases: `det = 0`

(a) a non-edge in `S` gives a zero column; (b) if `fromEdgeSet S` is disconnected, the rows of a
component avoiding the root sum to zero.
-/

section PartB

variable {R : Type*} {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [LinearOrder V] [DecidableRel G.Adj] {v₀ : V}

omit [Fintype V] in
/-- The two endpoints of an edge carry cancelling signs: the column of an edge sums to zero over
its two endpoints. -/
theorem orientedIncMatrix_apply_add_apply_of_adj [Ring R] {u w : V} (hadj : G.Adj u w) :
    G.orientedIncMatrix R u s(u, w) + G.orientedIncMatrix R w s(u, w) = 0 := by
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

variable (R G v₀)

/-- **Case (a).** A `(card V − 1)`-subset containing a non-edge has a zero column in the reduced
incidence minor, so the minor is singular. -/
theorem det_minor_eq_zero_of_not_subset_edgeSet [CommRing R]
    (S : Finset (Sym2 V)) (hS : S.card = Fintype.card {v // v ≠ v₀})
    (hx : ¬ ↑S ⊆ G.edgeSet) :
    ((G.reducedIncMatrix R v₀).submatrix
      (Fintype.equivFin {v // v ≠ v₀}).symm (S.orderEmbOfFin hS)).det = 0 := by
  obtain ⟨x, hxS, hxE⟩ := Set.not_subset.1 hx
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, S.orderEmbOfFin hS j₀ = x := by
    have hx' : x ∈ Set.range (S.orderEmbOfFin hS) := (S.range_orderEmbOfFin hS).symm ▸ hxS
    exact hx'
  refine det_eq_zero_of_column_eq_zero j₀ fun i => ?_
  rw [submatrix_apply, hj₀, reducedIncMatrix, submatrix_apply]
  exact G.orientedIncMatrix_of_notMem_incidenceSet fun hmem =>
    hxE (G.incidenceSet_subset _ hmem)

/-- **Case (b).** If the spanning subgraph on `S` is disconnected, some component misses the
root; its rows sum to zero, so the reduced incidence minor is singular. -/
theorem det_minor_eq_zero_of_not_connected [CommRing R] [IsDomain R]
    (S : Finset (Sym2 V)) (hS : S.card = Fintype.card {v // v ≠ v₀})
    (hsub : ↑S ⊆ G.edgeSet) (hdis : ¬ (fromEdgeSet (↑S : Set (Sym2 V))).Connected) :
    ((G.reducedIncMatrix R v₀).submatrix
      (Fintype.equivFin {v // v ≠ v₀}).symm (S.orderEmbOfFin hS)).det = 0 := by
  classical
  set H : SimpleGraph V := fromEdgeSet (↑S : Set (Sym2 V)) with hH
  -- a vertex unreachable from the root
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, ¬ H.Reachable v₀ u₀ := by
    by_contra hall
    push Not at hall
    haveI : Nonempty V := ⟨v₀⟩
    exact hdis ⟨fun u v => (hall u).symm.trans (hall v)⟩
  have hu₀v₀ : u₀ ≠ v₀ := by rintro rfl; exact hu₀ (Reachable.refl u₀)
  -- the component indicator, on all of V
  set wt : V → R := fun v => if H.Reachable v u₀ then 1 else 0 with hwt
  have hwt_v₀ : wt v₀ = 0 := if_neg fun h => hu₀ h
  -- the full-vertex-sum of any S-edge column against wt vanishes
  have hcol : ∀ x ∈ S, ∑ v, wt v * G.orientedIncMatrix R v x = 0 := by
    intro x hxS
    induction x with | _ a b =>
    have hGadj : G.Adj a b := G.mem_edgeSet.1 (hsub hxS)
    have hHadj : H.Adj a b := by
      rw [hH, fromEdgeSet_adj]; exact ⟨hxS, hGadj.ne⟩
    have hsupp : ∀ v ∈ (Finset.univ : Finset V), v ∉ ({a, b} : Finset V) →
        wt v * G.orientedIncMatrix R v s(a, b) = 0 := by
      intro v _ hv
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      rw [G.orientedIncMatrix_of_notMem_incidenceSet, mul_zero]
      intro hmem
      rcases (Sym2.mem_iff).1 hmem.2 with rfl | rfl
      · exact hv.1 rfl
      · exact hv.2 rfl
    rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset V)) hsupp,
      Finset.sum_pair hGadj.ne]
    have hreach : wt a = wt b := by
      simp only [hwt]
      by_cases h : H.Reachable a u₀
      · rw [if_pos h, if_pos (hHadj.symm.reachable.trans h)]
      · rw [if_neg h, if_neg fun h' => h (hHadj.reachable.trans h')]
    rw [hreach, ← mul_add, orientedIncMatrix_apply_add_apply_of_adj hGadj, mul_zero]
  -- transport to a vecMul kernel vector of the minor
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  set e := Fintype.equivFin {v : V // v ≠ v₀} with he
  refine ⟨fun i => wt ↑(e.symm i), ?_, ?_⟩
  · intro hzero
    have h1 : wt ↑(e.symm (e ⟨u₀, hu₀v₀⟩)) = (0 : R) := congrFun hzero (e ⟨u₀, hu₀v₀⟩)
    rw [Equiv.symm_apply_apply] at h1
    have : wt u₀ = 1 := if_pos (Reachable.refl u₀)
    rw [this] at h1
    exact one_ne_zero h1
  · funext j
    have hxS : S.orderEmbOfFin hS j ∈ S := S.orderEmbOfFin_mem hS j
    have hsum := hcol _ hxS
    rw [Matrix.vecMul, Pi.zero_apply]
    simp only [dotProduct, submatrix_apply, reducedIncMatrix]
    -- sum over the subtype = sum over V minus the (vanishing) root term
    calc ∑ i, wt ↑(e.symm i)
          * G.orientedIncMatrix R ↑(e.symm i) (S.orderEmbOfFin hS j)
        = ∑ u : {v : V // v ≠ v₀}, wt ↑u
          * G.orientedIncMatrix R ↑u (S.orderEmbOfFin hS j) :=
          Fintype.sum_equiv e.symm _ _ fun i => rfl
      _ = ∑ v ∈ Finset.univ.erase v₀, wt v
          * G.orientedIncMatrix R v (S.orderEmbOfFin hS j) := by
          exact (Finset.sum_subtype (Finset.univ.erase v₀)
            (fun x => by simp [Finset.mem_erase])
            (fun v => wt v * G.orientedIncMatrix R v (S.orderEmbOfFin hS j))).symm
      _ = 0 := by
          have h2 : (∑ v ∈ Finset.univ.erase v₀,
                wt v * G.orientedIncMatrix R v (S.orderEmbOfFin hS j))
              + wt v₀ * G.orientedIncMatrix R v₀ (S.orderEmbOfFin hS j)
              = ∑ v, wt v * G.orientedIncMatrix R v (S.orderEmbOfFin hS j) :=
            Finset.sum_erase_add Finset.univ _ (Finset.mem_univ v₀)
          rw [hwt_v₀, zero_mul, add_zero] at h2
          rw [h2]
          exact hsum

end PartB

/-!
## Part C — the connected case: `det² = 1`

Recolumn the minor by the parent-edge bijection and sort by the key `(dist · v₀, ·)`: the result
is upper-triangular with `±1` diagonal.  No acyclicity needed — connectivity plus the edge count
do all the work (and force `fromEdgeSet S` to be a spanning tree a posteriori).
-/

section PartC

variable {R : Type*} {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [LinearOrder V] [DecidableRel G.Adj] {v₀ : V}

variable (R G v₀)

/-- **Case (c).** If `S` consists of `card V − 1` genuine edges spanning a connected graph, the
reduced incidence minor has determinant `±1`. -/
theorem sq_det_minor_eq_one_of_connected [CommRing R]
    (S : Finset (Sym2 V)) (hS : S.card = Fintype.card {v // v ≠ v₀})
    (hsub : ↑S ⊆ G.edgeSet) (hconn : (fromEdgeSet (↑S : Set (Sym2 V))).Connected) :
    ((G.reducedIncMatrix R v₀).submatrix
      (Fintype.equivFin {v // v ≠ v₀}).symm (S.orderEmbOfFin hS)).det ^ 2 = 1 := by
  classical
  set k := Fintype.card {v : V // v ≠ v₀} with hk
  set e := Fintype.equivFin {v : V // v ≠ v₀} with he
  set M := (G.reducedIncMatrix R v₀).submatrix e.symm (S.orderEmbOfFin hS) with hM
  -- parent edges live in S
  have hpe_mem : ∀ u : {v : V // v ≠ v₀}, parentEdge v₀ hconn u ∈ S := by
    intro u
    have h1 : (fromEdgeSet (↑S : Set (Sym2 V))).Adj ↑u (treeParent v₀ hconn u) :=
      treeParent_adj v₀ hconn u
    rw [fromEdgeSet_adj] at h1
    rw [parentEdge]
    exact Finset.mem_coe.1 h1.1
  -- parent edges are G-edges, incident to their vertex
  have hpe_inc : ∀ u : {v : V // v ≠ v₀}, parentEdge v₀ hconn u ∈ G.incidenceSet ↑u := by
    intro u
    exact ⟨hsub (hpe_mem u), by rw [parentEdge]; exact Sym2.mem_mk_left _ _⟩
  -- the sorting key
  set key : {v : V // v ≠ v₀} → ℕ ×ₗ V :=
    fun u => toLex ((fromEdgeSet (↑S : Set (Sym2 V))).dist ↑u v₀, ↑u) with hkey
  have hkey_inj : Function.Injective key := by
    intro u u' h
    have h2 := congrArg (Prod.snd ∘ ofLex) h
    exact Subtype.ext h2
  -- entry analysis: a nonzero entry against a parent edge forces equality or a key drop
  have hentry : ∀ u w : {v : V // v ≠ v₀},
      G.orientedIncMatrix R ↑u (parentEdge v₀ hconn w) ≠ 0 → u = w ∨ key u < key w := by
    intro u w hne
    have hmem : ↑u ∈ parentEdge v₀ hconn w := by
      by_contra hmem
      exact hne (G.orientedIncMatrix_of_notMem_incidenceSet fun hinc => hmem hinc.2)
    rcases eq_or_dist_lt_of_mem_parentEdge v₀ hconn hmem with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Prod.Lex.toLex_lt_toLex.2 (Or.inl h))
  -- squared diagonal entries are 1
  have hdiag : ∀ u : {v : V // v ≠ v₀},
      G.orientedIncMatrix R ↑u (parentEdge v₀ hconn u) ^ 2 = 1 := by
    intro u
    rw [sq, G.orientedIncMatrix_mul_self, G.incMatrix_of_mem_incidenceSet (hpe_inc u)]
  -- the parent-edge bijection onto S, as an equiv to Fin k
  have hbij : Function.Bijective
      (fun u : {v : V // v ≠ v₀} => (⟨parentEdge v₀ hconn u, hpe_mem u⟩ : {x // x ∈ S})) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun u u' h => parentEdge_injective v₀ hconn (Subtype.ext_iff.1 h), ?_⟩
    rw [Fintype.card_coe, hS]
  set ce : {v : V // v ≠ v₀} ≃ Fin k :=
    (Equiv.ofBijective _ hbij).trans (S.orderIsoOfFin hS).toEquiv.symm with hce
  have hce_apply : ∀ u, S.orderEmbOfFin hS (ce u) = parentEdge v₀ hconn u := by
    intro u
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [hce]
  -- the recolumned matrix is M reindexed by (e, ce)
  set T : Matrix {v : V // v ≠ v₀} {v : V // v ≠ v₀} R :=
    Matrix.of fun u w => G.orientedIncMatrix R ↑u (parentEdge v₀ hconn w) with hT
  have hTM : T = M.submatrix e ce := by
    ext u w
    rw [hT, hM]
    simp only [Matrix.of_apply, submatrix_apply, Equiv.symm_apply_apply,
      reducedIncMatrix, hce_apply]
    rfl
  -- det T = ± det M, so the squares agree
  have hdet_sq : T.det ^ 2 = M.det ^ 2 := by
    have hsplit : T = (M.submatrix e e).submatrix id ⇑(ce.trans e.symm) := by
      rw [hTM]; ext u w
      simp only [Matrix.submatrix_apply, id_eq, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [hsplit, det_permute', Matrix.det_submatrix_equiv_self, mul_pow]
    have hsgn : ((Equiv.Perm.sign (ce.trans e.symm) : ℤ) : R) ^ 2 = 1 := by
      rw [← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq, Units.val_one, Int.cast_one]
    rw [hsgn, one_mul]
  -- sort the index by the key: an equiv Fin k ≃ {v ≠ v₀} along which the key is strictly mono
  have hkeycard : (Finset.univ.image key).card = k := by
    rw [Finset.card_image_of_injective _ hkey_inj, Finset.card_univ]
  have hbij2 : Function.Bijective
      (fun u : {v : V // v ≠ v₀} =>
        (⟨key u, Finset.mem_image_of_mem key (Finset.mem_univ u)⟩ :
          {x // x ∈ Finset.univ.image key})) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun u u' h => hkey_inj (Subtype.ext_iff.1 h), ?_⟩
    rw [Fintype.card_coe, hkeycard]
  set σ : Fin k ≃ {v : V // v ≠ v₀} :=
    ((Finset.univ.image key).orderIsoOfFin hkeycard).toEquiv.trans
      (Equiv.ofBijective _ hbij2).symm with hσ
  have hσ_key : ∀ i, key (σ i) = (Finset.univ.image key).orderEmbOfFin hkeycard i := by
    intro i
    rw [← Finset.coe_orderIsoOfFin_apply]
    have h3 : (⟨key (σ i), Finset.mem_image_of_mem key (Finset.mem_univ _)⟩ :
        {x // x ∈ Finset.univ.image key})
        = (Finset.univ.image key).orderIsoOfFin hkeycard i := by
      rw [hσ]
      exact (Equiv.ofBijective _ hbij2).apply_symm_apply _
    exact Subtype.ext_iff.1 h3
  have hσ_mono : StrictMono fun i => key (σ i) := by
    intro i j hij
    show key (σ i) < key (σ j)
    rw [hσ_key, hσ_key]
    exact ((Finset.univ.image key).orderEmbOfFin hkeycard).strictMono hij
  -- triangularity of the sorted matrix
  have htri : (T.submatrix σ σ).BlockTriangular id := by
    intro i j hji
    by_contra hne
    rcases hentry (σ i) (σ j) hne with h | h
    · exact absurd (σ.injective h) (fun h' => absurd (h' ▸ hji) (lt_irrefl _))
    · exact absurd (hσ_mono.lt_iff_lt.1 h) (not_lt.2 hji.le)
  -- assemble
  have hdet' : (T.submatrix σ σ).det = T.det := Matrix.det_submatrix_equiv_self σ T
  rw [← hdet_sq, ← hdet', Matrix.det_of_upperTriangular htri, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [submatrix_apply]
  exact hdiag (σ i)

end PartC

/-!
## Stone 3 — the dichotomy, packaged for Stone 4
-/

section Dichotomy

variable (R : Type*) {V : Type*} (G : SimpleGraph V)
variable [Fintype V] [LinearOrder V] [DecidableRel G.Adj] (v₀ : V)

open scoped Classical in
/-- **The spanning-tree minor dichotomy.**  The squared maximal minor of the reduced oriented
incidence matrix is `1` when `S` spans a connected subgraph of genuine edges (with
`card V − 1` of them, a spanning tree), and `0` otherwise. -/
theorem sq_det_minor_eq_ite [CommRing R] [IsDomain R]
    (S : Finset (Sym2 V)) (hS : S.card = Fintype.card {v // v ≠ v₀}) :
    ((G.reducedIncMatrix R v₀).submatrix
      (Fintype.equivFin {v // v ≠ v₀}).symm (S.orderEmbOfFin hS)).det ^ 2
      = if ↑S ⊆ G.edgeSet ∧ (fromEdgeSet (↑S : Set (Sym2 V))).Connected then 1 else 0 := by
  classical
  by_cases hsub : (↑S : Set (Sym2 V)) ⊆ G.edgeSet
  · by_cases hconn : (fromEdgeSet (↑S : Set (Sym2 V))).Connected
    · rw [if_pos ⟨hsub, hconn⟩]
      exact sq_det_minor_eq_one_of_connected R G v₀ S hS hsub hconn
    · rw [if_neg fun h => hconn h.2,
        det_minor_eq_zero_of_not_connected R G v₀ S hS hsub hconn]
      ring
  · rw [if_neg fun h => hsub h.1,
      det_minor_eq_zero_of_not_subset_edgeSet R G v₀ S hS hsub]
    ring

end Dichotomy

end SimpleGraph

