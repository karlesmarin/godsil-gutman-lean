/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import RealStable
public import MatchingPoly
public import MSS.GodsilGutman
public import MSS.PathTree
public import MSS.ForestComponents

/-!
# Real-rootedness of forest matching polynomials (route A, path-tree)

The autonomous HL real-rootedness program (`HL_AUTORUN/ROADMAP.md`). Goal: `μ(G)`
real-rooted for every finite graph, via the path-tree route — `μ(G) ∣ μ(T(G,u))`
with `T(G,u)` a forest, and `μ(forest)` real-rooted because on a forest the matching
polynomial is the characteristic polynomial of the (real symmetric) adjacency matrix.

This file lays the mechanical Mathlib-assembly bricks of that route:

* **T3** `charpoly_symmetric_realRooted` — the characteristic polynomial of a real
  symmetric matrix is real-rooted (Hermitian spectral theorem ⟹ real eigenvalues ⟹
  `charpoly = ∏ (X − C λᵢ)` splits over `ℝ`).

The harder component/band walls (`pathTree_matchingPoly_dvd`, the `2√(Δ−1)` bound)
are queued separately.
-/

@[expose] public section

namespace MSS

open Polynomial Matrix

/-- **T3 — charpoly of a real symmetric matrix is real-rooted.** Over `ℝ` a symmetric
matrix is Hermitian (`star` is trivial, so `Aᴴ = Aᵀ = A`); the Hermitian spectral
theorem gives `A.charpoly = ∏ i, (X − C (eigenvalues i))` with the eigenvalues real, a
product of monic linears, hence `RealRooted`. This is the spectral half of
`μ(forest)` real-rootedness (the matching polynomial of a forest equals this charpoly,
T2). -/
theorem charpoly_symmetric_realRooted {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℝ} (hA : A.IsSymm) : RealRooted A.charpoly := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA
  rw [hH.charpoly_eq]
  exact realRooted_prod_X_sub_C _ _

end MSS

namespace SimpleGraph

open Polynomial Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The all-`+` signing matrix is exactly the (unsigned) adjacency matrix over `ℝ`: every
edge gets the entry `+1`, off the edge set `0`. -/
theorem signingMatrix_const_true : G.signingMatrix (fun _ => true) = G.adjMatrix ℝ := by
  ext i j
  rw [signingMatrix_apply, adjMatrix_apply]
  by_cases h : G.Adj i j <;> simp [h]

omit [DecidableRel G.Adj] in
/-- **The forest involution lemma (route B crux — PROVEN).** On a forest (`IsAcyclic`), any
permutation `σ` whose every non-fixed point is adjacent to its image is an involution `σ² = 1`.
If not, some `x` has a `σ`-orbit of minimal period `p ≥ 3`; its consecutive points
`x, σx, …, σ^{p-1}x` are distinct and adjacent, so deleting the edge `{x, σx}` still leaves
`x` and `σx` connected (go around the orbit the long way, `σx → σ²x → ⋯ → σ^p x = x`), i.e.
`{x, σx}` is not a bridge — contradicting `isAcyclic_iff_forall_edge_isBridge`. This is the
combinatorial heart of "matching polynomial = characteristic polynomial on a forest": in the
permutation expansion of `charpoly(A)` the surviving terms are exactly the matchings. -/
theorem acyclic_perm_support_isInvolution (hac : G.IsAcyclic) {σ : Equiv.Perm V}
    (hsupp : ∀ i, σ i ≠ i → G.Adj (σ i) i) : σ ^ 2 = 1 := by
  by_contra hσ
  obtain ⟨x, hx⟩ : ∃ x, (σ ^ 2) x ≠ x := by
    by_contra hcon; push_neg at hcon
    exact hσ (Equiv.ext fun y => by simpa using hcon y)
  -- σ x ≠ x  and  σ² x ≠ x
  have hsx : σ x ≠ x := by
    intro h; apply hx; rw [pow_two, Equiv.Perm.mul_apply, h, h]
  -- minimal period p of x under σ
  set p := Function.minimalPeriod (⇑σ) x with hp
  have hper : Function.IsPeriodicPt (⇑σ) (orderOf σ) x := by
    show (⇑σ)^[orderOf σ] x = x
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]; rfl
  have hp_pos : 0 < p := by
    have := hper.minimalPeriod_pos (orderOf_pos σ); rwa [← hp] at this
  have hpx : (σ ^ p) x = x := by
    have h := Function.iterate_minimalPeriod (f := ⇑σ) (x := x)
    rw [← hp] at h; rwa [← Equiv.Perm.coe_pow] at h
  have hinj : (Set.Iio p).InjOn (fun n => (⇑σ)^[n] x) := by
    have := Function.iterate_injOn_Iio_minimalPeriod (f := ⇑σ) (x := x); rwa [← hp] at this
  have hdistinct : ∀ a b, a < p → b < p → (σ ^ a) x = (σ ^ b) x → a = b := by
    intro a b ha hb h
    simp only [Equiv.Perm.coe_pow] at h
    exact hinj (Set.mem_Iio.2 ha) (Set.mem_Iio.2 hb) h
  have hp3 : 3 ≤ p := by
    rcases Nat.lt_or_ge p 3 with hlt | hge
    · interval_cases p
      · rw [pow_one] at hpx; exact absurd hpx hsx
      · exact absurd hpx hx
    · exact hge
  -- consecutive orbit points are adjacent
  have hsucc : ∀ k, (σ ^ (k + 1)) x = σ ((σ ^ k) x) := by
    intro k; rw [pow_succ', Equiv.Perm.mul_apply]
  have hadjG : ∀ k, (σ ^ k) x ≠ (σ ^ (k + 1)) x → G.Adj ((σ ^ k) x) ((σ ^ (k + 1)) x) := by
    intro k hk
    rw [hsucc k]
    have hne : σ ((σ ^ k) x) ≠ (σ ^ k) x := fun h => hk (by rw [hsucc k, h])
    exact (hsupp ((σ ^ k) x) hne).symm
  have hnonfix : ∀ k, k < p → (σ ^ k) x ≠ (σ ^ (k + 1)) x := by
    intro k hkp heq
    rcases Nat.lt_or_ge (k + 1) p with h | h
    · exact absurd (hdistinct k (k + 1) hkp h heq) (by omega)
    · have hk1 : k + 1 = p := by omega
      have hkx : (σ ^ k) x = x := by rw [heq, hk1, hpx]
      have hk0 : k = 0 := hdistinct k 0 hkp hp_pos (by rw [hkx, pow_zero, Equiv.Perm.one_apply])
      rw [hk0] at heq
      simp only [pow_zero, Equiv.Perm.one_apply, zero_add, pow_one] at heq
      exact hsx heq.symm
  -- each interior step is an edge of `G − {x,σx}`
  have hstep : ∀ k, 1 ≤ k → k + 1 ≤ p →
      (G.deleteEdges {s(x, σ x)}).Adj ((σ ^ k) x) ((σ ^ (k + 1)) x) := by
    intro k hk1 hk2
    have hkp : k < p := by omega
    rw [deleteEdges_adj]
    refine ⟨hadjG k (hnonfix k hkp), ?_⟩
    rw [Set.mem_singleton_iff, Sym2.eq_iff]
    push_neg
    refine ⟨fun e1 _ => ?_, fun e1 e2 => ?_⟩
    · exact absurd (hdistinct k 0 hkp hp_pos (by rw [e1, pow_zero, Equiv.Perm.one_apply])) (by omega)
    · have hk1' : k = 1 := hdistinct k 1 hkp (by omega) (by rw [e1, pow_one])
      rw [hk1'] at e2
      exact absurd (hdistinct (1 + 1) 0 (by omega) hp_pos
        (by rw [e2, pow_zero, Equiv.Perm.one_apply])) (by omega)
  -- go around the orbit: σx is reachable to x avoiding the edge {x,σx}
  have hreach : ∀ k, k + 1 ≤ p →
      (G.deleteEdges {s(x, σ x)}).Reachable ((σ ^ 1) x) ((σ ^ (k + 1)) x) := by
    intro k
    induction k with
    | zero => intro _; exact Reachable.refl _
    | succ m ih => intro hk; exact (ih (by omega)).trans (hstep (m + 1) (by omega) (by omega)).reachable
  have hfin : (G.deleteEdges {s(x, σ x)}).Reachable ((σ ^ 1) x) ((σ ^ p) x) := by
    have h := hreach (p - 1) (by omega)
    rwa [show p - 1 + 1 = p from by omega] at h
  rw [hpx, pow_one] at hfin
  -- but every edge of an acyclic graph is a bridge
  have hmem : s(x, σ x) ∈ G.edgeSet := by rw [SimpleGraph.mem_edgeSet]; exact (hsupp x hsx).symm
  have hbridge := isAcyclic_iff_forall_edge_isBridge.mp hac hmem
  rw [isBridge_iff] at hbridge
  exact hbridge.2 hfin.symm

/-- **The gauge step (T2's open core — design fork, see `HL_AUTORUN/DECISIONS.md`).**
On a forest (`IsAcyclic`) every `±1` edge-signing `A_cfg` has the *same* characteristic
polynomial as the all-`+` adjacency matrix: `A_cfg` is conjugate to `A_+` by a diagonal
`±1` "vertex potential" `D` (`A_cfg = D · A_+ · D⁻¹`), which exists because a forest has
`H¹(·;ℤ/2) = 0` (no cycles ⟹ every edge-cocycle is a coboundary). `charpoly_units_conj`
then gives equal charpolys. Stated as a `def … : Prop` (honesty floor — NOT a vacuous
theorem); its proof is the queued graph-theory chunk. -/
def forest_signing_charpoly_invariant_target : Prop :=
  G.IsAcyclic → ∀ cfg : Sym2 V → Bool,
    (G.signingMatrix cfg).charpoly = (G.adjMatrix ℝ).charpoly

/-- **T2 (conditional on the gauge step).** For a forest, the matching polynomial equals the
characteristic polynomial of the adjacency matrix: `μ(F) = charpoly(A)`. Mechanical reduction —
given that all `±1` signings share the charpoly of `A_+` (`hinv`), the Godsil–Gutman identity
`∑_cfg charpoly(A_cfg) = (#cfg)·μ(G)` collapses its left side to `(#cfg)·charpoly(A_+)`, and the
positive-`ℕ`-multiple cancels in the (characteristic-zero, domain) ring `ℝ[X]`. The *only* deferred
input is `hinv` (= `forest_signing_charpoly_invariant_target`). -/
theorem matchingPoly_forest_eq_charpoly_of_invariant
    (hinv : G.forest_signing_charpoly_invariant_target) (hac : G.IsAcyclic) :
    G.matchingPoly = (G.adjMatrix ℝ).charpoly := by
  have hgg : (∑ cfg : Sym2 V → Bool, (G.signingMatrix cfg).charpoly)
      = (Fintype.card (Sym2 V → Bool)) • G.matchingPoly := G.godsil_gutman
  have hsum : (∑ cfg : Sym2 V → Bool, (G.signingMatrix cfg).charpoly)
      = (Fintype.card (Sym2 V → Bool)) • (G.adjMatrix ℝ).charpoly := by
    rw [Finset.sum_congr rfl (fun cfg (_ : cfg ∈ Finset.univ) => hinv hac cfg),
        Finset.sum_const, Finset.card_univ]
  have key : (Fintype.card (Sym2 V → Bool)) • (G.adjMatrix ℝ).charpoly
      = (Fintype.card (Sym2 V → Bool)) • G.matchingPoly := by rw [← hsum, hgg]
  rw [nsmul_eq_mul, nsmul_eq_mul] at key
  have hN : (Fintype.card (Sym2 V → Bool) : ℝ[X]) ≠ 0 := by
    haveI : Nonempty (Sym2 V → Bool) := ⟨fun _ => true⟩
    exact_mod_cast Fintype.card_ne_zero
  exact (mul_left_cancel₀ hN key).symm

/-- **T4 (conditional on T2).** A forest's matching polynomial is real-rooted. Immediate from
`μ(F) = charpoly(A)` (T2) and `charpoly` of the symmetric adjacency matrix being real-rooted (T3,
`MSS.charpoly_symmetric_realRooted`, via `isSymm_adjMatrix`). -/
theorem matchingPoly_forest_realRooted_of_eq
    (heq : G.matchingPoly = (G.adjMatrix ℝ).charpoly) :
    MSS.RealRooted G.matchingPoly := by
  rw [heq]
  exact MSS.charpoly_symmetric_realRooted G.isSymm_adjMatrix

/-! ### Route B (unconditional): `μ(forest) = charpoly` via the permutation expansion -/

/-- On the all-`+` signing (= adjacency matrix), each support factor is `−C 1 = −1`, so an
edge-involution's support product is `(−1)^{|support|} = (−1)^{2|M|} = 1`. -/
theorem prod_support_const_true_eq_one {σ : Equiv.Perm V} (hP : G.IsEdgeInvolution σ) :
    (∏ i ∈ σ.support, (- Polynomial.C (G.signingMatrix (fun _ => true) (σ i) i))) = 1 := by
  have hfac : ∀ i ∈ σ.support,
      (- Polynomial.C (G.signingMatrix (fun _ => true) (σ i) i)) = (-1 : Polynomial ℝ) := by
    intro i hi
    rw [signingMatrix_apply, if_pos (hP.2 i hi)]; simp
  rw [Finset.prod_congr rfl hfac, Finset.prod_const, G.support_card_eq hP, pow_mul]; simp

/-- On a forest, a permutation that is *not* an edge-involution must have a non-adjacent support
pair (if all its support pairs were edges it would be an involution, by
`acyclic_perm_support_isInvolution`), so its support product vanishes. -/
theorem prod_support_const_true_eq_zero (hac : G.IsAcyclic) {σ : Equiv.Perm V}
    (hP : ¬ G.IsEdgeInvolution σ) :
    (∏ i ∈ σ.support, (- Polynomial.C (G.signingMatrix (fun _ => true) (σ i) i))) = 0 := by
  by_cases hsq : σ ^ 2 = 1
  · have hnall : ¬ (∀ i ∈ σ.support, G.Adj (σ i) i) := fun hall => hP ⟨hsq, hall⟩
    push_neg at hnall
    obtain ⟨i, hi, hni⟩ := hnall
    exact G.prod_support_eq_zero_of_not_adj _ σ hi hni
  · have hnall : ¬ (∀ i, σ i ≠ i → G.Adj (σ i) i) :=
      fun h => hsq (G.acyclic_perm_support_isInvolution hac h)
    push_neg at hnall
    obtain ⟨i, hi_ne, hni⟩ := hnall
    exact G.prod_support_eq_zero_of_not_adj _ σ (Equiv.Perm.mem_support.mpr hi_ne) hni

/-- **T2 (unconditional, route B).** For a forest, the matching polynomial equals the characteristic
polynomial of the adjacency matrix: `μ(F) = charpoly(A)`. The permutation expansion of
`charpoly(A)` restricts to edge-involutions — non-edge-involutions vanish (a non-adjacent support
pair, or, on a forest, the involution lemma forces one) — and edge-involutions biject with
matchings carrying the sign `(−1)^{|M|}`, reassembling `μ(G)`. -/
theorem matchingPoly_forest_eq_charpoly (hac : G.IsAcyclic) :
    G.matchingPoly = (G.adjMatrix ℝ).charpoly := by
  have hcollapse : (G.signingMatrix (fun _ => true)).charpoly
      = ∑ σ ∈ Finset.univ.filter G.IsEdgeInvolution,
          Polynomial.C ((-1 : ℝ) ^ (matchingOfPerm σ).card)
            * Polynomial.X ^ (Fintype.card V - 2 * (matchingOfPerm σ).card) := by
    rw [charpoly_signingMatrix_eq_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [prod_charmatrix_split]
    by_cases hP : G.IsEdgeInvolution σ
    · rw [if_pos hP, G.prod_support_const_true_eq_one hP, mul_one]
      exact G.edgeInv_term hP
    · rw [if_neg hP, G.prod_support_const_true_eq_zero hac hP, mul_zero, mul_zero]
  rw [← signingMatrix_const_true, hcollapse, G.sum_filter_eq_sum_matchings,
      G.sum_matchings_eq_matchingPoly]

/-- **T4 (unconditional).** A forest's matching polynomial is real-rooted (T2 + T3). -/
theorem matchingPoly_forest_realRooted (hac : G.IsAcyclic) :
    MSS.RealRooted G.matchingPoly :=
  G.matchingPoly_forest_realRooted_of_eq (G.matchingPoly_forest_eq_charpoly hac)

/-- **T5 — connected real-rootedness (sorry-free).** The matching polynomial of any connected finite
graph is real-rooted. Godsil's path-tree divisibility (brick (e), T1) gives `μ(G) ∣ μ(T(G,u))` for a
vertex `u` (which exists since `G` is connected hence nonempty); the path tree is a forest
(`pathTree_isAcyclic`), so `μ(T(G,u))` is real-rooted (T4); and a nonzero divisor of a real-rooted
polynomial is real-rooted (`RealRooted.of_dvd`). The path tree is monic, hence nonzero. -/
theorem matchingPoly_connected_realRooted (hG : G.Connected) :
    MSS.RealRooted G.matchingPoly := by
  obtain ⟨u⟩ := hG.nonempty
  exact ((G.pathTree u).matchingPoly_forest_realRooted (pathTree_isAcyclic G u)).of_dvd
    (matchingPoly_monic (G.pathTree u)).ne_zero
    (connected_matchingPoly_dvd_pathTree G hG u)

/-- **T6 — Heilmann–Lieb real-rootedness (general, sorry-free).** The matching polynomial of *any*
finite graph is real-rooted. `μ(G) = ∏_C μ(G[C.supp])` over connected components
(`matchingPoly_eq_prod_components`); each induced component is connected
(`ConnectedComponent.maximal_connected_induce_supp`), so its matching polynomial is real-rooted (T5);
and real-rootedness is closed under finite products (`RealRooted.prod`). -/
theorem matchingPoly_realRooted (G : SimpleGraph V) [DecidableRel G.Adj] :
    MSS.RealRooted G.matchingPoly := by
  rw [matchingPoly_eq_prod_components]
  refine MSS.RealRooted.prod (fun C _ => ?_)
  exact (G.induce (C.supp : Set V)).matchingPoly_connected_realRooted
    C.maximal_connected_induce_supp.1

end SimpleGraph
