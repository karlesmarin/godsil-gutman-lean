/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Ihara.TraceFormula
import Mathlib.Combinatorics.SimpleGraph.Girth

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

end Counting

end SimpleGraph
