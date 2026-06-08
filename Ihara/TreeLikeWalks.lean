/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Ihara.TraceFormula
import Mathlib.Combinatorics.SimpleGraph.Girth
import MatchingPoly
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Tree-like walks and Godsil's moment theorem — Part III, brick 3 (the hard brick)

This file opens the remaining brick of the matching ↔ Ihara trace formula: the **matching side**,
relating the power sums `p_k = Σ θᵢᵏ` of the matching-polynomial roots to a count of walks.

## Tree-like walks (Godsil 1981, *Matchings and walks in graphs*)

A closed walk is **tree-like** when the subgraph of edges it traverses is acyclic (a forest):
in a forest, every closed walk merely retraces edges and never encloses a cycle. Godsil's moment
theorem states that the `k`-th moment of the matching polynomial counts closed tree-like walks:

  `p_k = Σᵢ θᵢᵏ = Σ_v #{ closed tree-like walks of length k at v }`,

the matching-polynomial mirror of `trace_adjMatrix_pow` (`tr(Aᵏ) = #closed walks`).

## The girth half (this file's reachable target)

Below the girth, *every* closed walk is tree-like — a cycle inside the walk's support would be a
cycle of `G` of length `≤ w.length < girth`, impossible. Hence for `k < g`, tree-like walks and
all walks coincide, so `gap_k := tr(Aᵏ) − p_k = 0`; the first gap appears at `k = g`. This is the
girth-threshold mechanism tying brick 3 to pieces 1–2 of `Ihara/TraceFormula.lean`.

No prior formalization of tree-like walks or Godsil's moment theorem exists in a proof assistant.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A closed walk is **tree-like** when the subgraph of edges it traverses is acyclic (a forest).
This is Godsil's combinatorial class: in a forest every closed walk merely retraces, never
enclosing a cycle. -/
def Walk.IsTreeLike {v : V} (w : G.Walk v v) : Prop :=
  w.toSubgraph.coe.IsAcyclic

/-- The edges of a walk in the coerced support `w.toSubgraph.coe`, pushed into `G`, all lie among
the edges of `w` itself: the mapped walk's support is contained in `w.toSubgraph`. -/
theorem Walk.edges_map_hom_subset_edges {v : V} (w : G.Walk v v) {u : w.toSubgraph.verts}
    (c : w.toSubgraph.coe.Walk u u) :
    (c.map w.toSubgraph.hom).edges ⊆ w.edges := by
  have hle : (c.map w.toSubgraph.hom).toSubgraph ≤ w.toSubgraph := by
    rw [Walk.toSubgraph_map]
    refine ⟨?_, ?_⟩
    · rintro x ⟨a, -, rfl⟩; exact a.2
    · rintro x y ⟨a, b, hab, rfl, rfl⟩
      exact (Subgraph.coe_adj ..).mp (c.toSubgraph.adj_sub hab)
  intro e he
  rw [← Walk.mem_edges_toSubgraph] at he ⊢
  exact Subgraph.edgeSet_mono hle he

/-- **Girth threshold.** A closed walk strictly shorter than the (extended) girth is tree-like: any
cycle in its edge-support lifts to a cycle of `G` no longer than the walk, contradicting the girth
bound. (For an acyclic `G`, `egirth = ⊤`, so this holds for every closed walk.) -/
theorem Walk.isTreeLike_of_length_lt_egirth {v : V} (w : G.Walk v v)
    (h : (w.length : ℕ∞) < G.egirth) : w.IsTreeLike := by
  intro u c hc
  -- map the support-cycle `c` into `G`; injective `hom` keeps it a cycle
  have hcyc : (c.map w.toSubgraph.hom).IsCycle :=
    (map_isCycle_iff_of_injective Subgraph.hom_injective).mpr hc
  -- girth bounds its length from below
  have hg : G.egirth ≤ (c.map w.toSubgraph.hom).length := G.egirth_le_length hcyc
  rw [Walk.length_map] at hg
  -- the cycle uses distinct edges, all among `w`'s, so its length ≤ `w.length`
  have hnodup : (c.map w.toSubgraph.hom).edges.Nodup := hcyc.edges_nodup
  have hsub : (c.map w.toSubgraph.hom).edges ⊆ w.edges := w.edges_map_hom_subset_edges c
  have hlen : c.length ≤ w.length := by
    have := (hnodup.subperm hsub).length_le
    rwa [Walk.length_edges, Walk.length_edges, Walk.length_map] at this
  -- chain: w.length < egirth ≤ c.length ≤ w.length, contradiction
  have hcontra : G.egirth ≤ (w.length : ℕ∞) := hg.trans (by exact_mod_cast hlen)
  exact absurd (lt_of_lt_of_le h hcontra) (lt_irrefl _)

/-! ## Below the girth: tree-like walks are all closed walks (`tr(Aᵏ)` counts them) -/

section Counting
variable [Fintype V] [DecidableRel G.Adj]
open Classical

/-- Below the (extended) girth, **every** closed walk of length `k` is tree-like, so filtering the
closed walks of length `k` by `IsTreeLike` keeps all of them. -/
theorem card_filter_isTreeLike_of_lt_egirth {k : ℕ} {v : V} (h : (k : ℕ∞) < G.egirth) :
    #((G.finsetWalkLength k v v).filter fun w => w.IsTreeLike)
      = #(G.finsetWalkLength k v v) := by
  congr 1
  refine Finset.filter_true_of_mem fun w hw => ?_
  exact w.isTreeLike_of_length_lt_egirth (by rw [mem_finsetWalkLength_iff.mp hw]; exact h)

/-- **Below the girth, `tr(Aᵏ)` counts closed tree-like walks.** Combining piece 1 of the trace
formula (`trace_adjMatrix_pow`, `tr(Aᵏ) = #closed walks`) with the girth threshold: for `k <
girth`, *every* closed walk is tree-like, so `tr(Aᵏ) = Σ_v #{closed tree-like walks of length k at
v}`. This is the `gap_k = 0` half of the matching↔Ihara headline (`tr(Aᵏ) = p_k` below girth, once
Godsil's `p_k = #tree-like walks` lands). -/
theorem trace_adjMatrix_pow_eq_treeLike_of_lt_egirth (k : ℕ) (h : (k : ℕ∞) < G.egirth) :
    (G.adjMatrix ℕ ^ k).trace
      = ∑ v : V, #((G.finsetWalkLength k v v).filter fun w => w.IsTreeLike) := by
  rw [trace_adjMatrix_pow]
  exact Finset.sum_congr rfl fun v _ => (card_filter_isTreeLike_of_lt_egirth h).symm

/-! ## The matching side: Godsil's tree-like walk count (Part III, brick 3 — scaffold)

The trace side above is settled. Godsil's **moment theorem** is the remaining (open) brick:

  `p_k = Σᵢ θᵢᵏ  =  treeLikeWalkCount G k`,

where `θᵢ` are the roots of `matchingPoly G` and `treeLikeWalkCount` is defined below. Proving the
equality with `p_k` needs (i) Newton's identities for the roots of `matchingPoly` (bridging
Mathlib's `MvPolynomial.NewtonIdentities` to a univariate polynomial's power sums) and (ii) Godsil's
path-tree involution exhibiting `μ(G−v)/μ(G)` as the tree-like walk generating function — neither
yet in Mathlib. What this scaffold pins down, sorry-free: the count itself, its `k = 0` value
(`p_0 = n`), and its identification with `tr(Aᵏ)` below the girth (so the open step `p_k = tr(Aᵏ)`
below girth reduces exactly to Newton + Sachs/Godsil). -/

/-- **Godsil's tree-like walk count** `Σ_v #{closed tree-like walks of length k at v}` — the
matching side of the trace-formula bridge. -/
noncomputable def treeLikeWalkCount (k : ℕ) : ℕ :=
  ∑ v : V, #((G.finsetWalkLength k v v).filter fun w => w.IsTreeLike)

/-- **Trace link (below girth).** For `k < girth`, `treeLikeWalkCount G k = tr(Aᵏ)`, since below
the girth every closed walk is tree-like. The proved half of the bridge: combined with Godsil's
(open) `p_k = treeLikeWalkCount`, it yields `p_k = tr(Aᵏ)` below the girth. -/
theorem treeLikeWalkCount_eq_trace_of_lt_egirth (k : ℕ) (h : (k : ℕ∞) < G.egirth) :
    G.treeLikeWalkCount k = (G.adjMatrix ℕ ^ k).trace := by
  rw [treeLikeWalkCount, trace_adjMatrix_pow_eq_treeLike_of_lt_egirth k h]

/-- The empty walk `nil` is tree-like: its edge-support is the single-vertex subgraph
`G.singletonSubgraph v`, whose coercion is a tree, hence acyclic. -/
theorem Walk.nil_isTreeLike (v : V) : (Walk.nil : G.Walk v v).IsTreeLike :=
  (IsTree.coe_singletonSubgraph G v).isAcyclic

/-- **`k = 0` moment anchor:** `treeLikeWalkCount G 0 = n`. The only closed walk of length `0` at
each vertex is `nil` (tree-like), so the count is `1` per vertex. This is the matching-side mirror
of the trivial power sum `p_0 = Σᵢ θᵢ⁰ = n` (`μ` has `n` roots). -/
theorem treeLikeWalkCount_zero : G.treeLikeWalkCount 0 = Fintype.card V := by
  have key : ∀ v : V, #((G.finsetWalkLength 0 v v).filter fun w => w.IsTreeLike) = 1 := by
    intro v
    have hset : G.finsetWalkLength 0 v v = {Walk.nil} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun w hw => ?_⟩
      · simp [mem_finsetWalkLength_iff]
      · rw [mem_finsetWalkLength_iff, Walk.length_eq_zero_iff] at hw; exact hw
    rw [hset, Finset.filter_singleton, if_pos (Walk.nil_isTreeLike v), Finset.card_singleton]
  rw [treeLikeWalkCount, Finset.sum_congr rfl (fun v _ => key v), Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one]

/-! ## The matching-side power sums `p_k` (the other half of the bridge) -/

/-- **Matching-side power sum** `p_k = Σᵢ θᵢᵏ` over the (complex) roots of the matching polynomial.
Godsil's moment theorem is the (open) bridge `matchingPowerSum G k = treeLikeWalkCount G k`. -/
noncomputable def matchingPowerSum (k : ℕ) : ℂ :=
  ((G.matchingPoly.map (algebraMap ℝ ℂ)).roots.map (· ^ k)).sum

/-- **`k = 0` anchor:** `matchingPowerSum G 0 = n`. The matching polynomial is monic of degree
`n = card V`, so over the algebraically closed `ℂ` it splits into exactly `n` linear factors, i.e.
its multiset of roots has cardinality `n`; each root contributes `θ⁰ = 1` to the power sum. Together
with `treeLikeWalkCount_zero` this confirms Godsil's bridge `matchingPowerSum = treeLikeWalkCount` at
`k = 0` on both sides. -/
theorem matchingPowerSum_zero : G.matchingPowerSum 0 = (Fintype.card V : ℂ) := by
  have hcard : (G.matchingPoly.map (algebraMap ℝ ℂ)).roots.card = Fintype.card V := by
    rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _),
      Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective, matchingPoly_natDegree]
  unfold matchingPowerSum
  simp only [pow_zero, Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul, mul_one]

/-! ## The trace-formula gap (first Sachs term)

`treeLikeGap G k := tr(Aᵏ) − treeLikeWalkCount G k` counts the closed walks of length `k` that are
**not** tree-like — those whose edge-support encloses a cycle. It vanishes below the girth
(`treeLikeGap_eq_zero_of_lt_egirth`, proved here). At `k = girth` it takes the value

  `treeLikeGap G g = 2·g·c_g`,   `c_g` = number of cycles of length `g = girth`,

since the only closed walks of length `g` enclosing a cycle are the single traversals of a
shortest cycle (`2g` per cycle: `g` starting points × `2` orientations). This is a classical
result of spectral cycle-counting / Godsil's tree-like-walk interpretation (C. Godsil,
*Counting Matchings and Tree-Like Walks in Regular Graphs*); the value formula is **not yet
formalized** here — it needs the walk↔shortest-cycle bijection — but the gap framework and the
below-girth vanishing are pinned down sorry-free, and `treeLikeGap G g = 2·g·c_g` is the first
Sachs term, the entry point to the matching↔charpoly comparison below girth. -/

/-- **Trace-formula gap** `tr(Aᵏ) − treeLikeWalkCount G k`: the count of closed length-`k` walks
that are not tree-like (they enclose a cycle). -/
noncomputable def treeLikeGap (k : ℕ) : ℤ :=
  ((G.adjMatrix ℕ ^ k).trace : ℤ) - (G.treeLikeWalkCount k : ℤ)

/-- **The gap vanishes below the girth.** Every closed walk shorter than the girth is tree-like,
so `tr(Aᵏ) = treeLikeWalkCount G k` there. The first nonzero gap appears exactly at `k = girth`
(value `2·girth·c_g`, classical, not yet formalized). -/
theorem treeLikeGap_eq_zero_of_lt_egirth (k : ℕ) (h : (k : ℕ∞) < G.egirth) :
    G.treeLikeGap k = 0 := by
  rw [treeLikeGap, treeLikeWalkCount_eq_trace_of_lt_egirth k h, sub_self]

/-- **The gap counts the non-tree-like closed walks** (bijection, piece 1): `treeLikeGap G k =
Σ_v #{closed length-k walks at v that are not tree-like}`. Immediate from `tr(Aᵏ) = Σ_v #(all)`
and `treeLikeWalkCount = Σ_v #(tree-like)`, since all = tree-like ⊔ not-tree-like. -/
theorem treeLikeGap_eq_card_not_treeLike (k : ℕ) :
    G.treeLikeGap k
      = ∑ v : V, (#((G.finsetWalkLength k v v).filter fun w => ¬ w.IsTreeLike) : ℤ) := by
  rw [treeLikeGap, trace_adjMatrix_pow, treeLikeWalkCount, Nat.cast_sum, Nat.cast_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hc := Finset.filter_card_add_filter_neg_card_eq_card
    (s := G.finsetWalkLength k v v) (p := fun w => w.IsTreeLike)
  rw [← hc]; push_cast; ring

end Counting

end SimpleGraph
