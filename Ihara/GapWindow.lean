/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Ihara.NbVanishing

/-!
# Stone B of the trace-formula gap law: the window `k ∈ {g, g+1}`

Stone A (`Ihara/NbVanishing.lean`) settles the gap law `tr(Aᵏ) − p_k = tr(Bᵏ)` below the
girth (both sides vanish). Stone B is the window where the law has content: at `k = g` and
`k = g+1` both sides equal `2k·c_k` (`c_k` = number of `k`-cycles). The architecture avoids
counting `c_k` directly: in this window, **structure** identifies the three families:

```
closed NB dart walks of length k  =  rooted k-cycle traversals  =  non-tree-like closed walks
        (B-side, tr(Bᵏ))                  (Walk.IsCycle)              (matching side, gap_k)
```

## Stones

* **B-1** (this file, in progress): a cycle yields both memberships —
  (a) `IsTrail → darts.IsChain nbRel` (consecutive darts of a trail never reverse: a reversal
      repeats an edge) — DONE below;
  (b) a cycle's dart list, closed at its basepoint dart, sits in `relWalks G.nbRel`;
  (c) a cycle is NOT tree-like (its path-tree lift retreats into the wrong vertex at the
      closing step).
* **B-2** (the wall): a closed NB walk of length `k ≤ g+1` *is* a cycle traversal. Route:
  the strengthened Stone A crux gives a cycle `C` on the walk's edges with `g ≤ |C| ≤ k`;
  if `|C| = k` the walk's edges are exactly `C`'s, each once, and the walk traverses `C`;
  the case `|C| = g, k = g+1` dies by parity (one leftover edge gives odd incidence) /
  direction-reversal (a backtrack on the cycle violates the chain).
* **B-3**: the matching side — a non-tree-like closed walk of length `k ≤ g+1` is a cycle
  traversal (lift analysis on `liftSeq`), and conversely (B-1c).
* **B-4**: assembly — the bijections count, `treeLikeGap k = tr(Bᵏ)` for `k ≤ g+1`.

Numerical locks: 12 064-graph exhaustive sweep + four deployed IEEE 802.11n Tanner graphs
(`research/ldpc-gaplaw/`). Closing Stone B makes the LDPC short-cycle census theorem-backed
end to end.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## W1: parity of edge incidences — for ARBITRARY walks

Mathlib's `IsTrail.even_countP_edges_iff` carries an `IsTrail` hypothesis that its own proof
only uses to feed the induction; the statement is true for every walk. We need the general
form: in Stone B's case `|C| = g, k = g+1` the walk is NOT a trail (it may repeat an edge),
and the parity of incidences at the extra edge's endpoint is exactly what kills the case. -/

/-- **Parity of edge incidences, general form.** For any walk `u → v` and any vertex `x`, the
number of edge slots incident to `x` is even iff `x` avoids the endpoints whenever they are
distinct. (Mathlib's version assumes `IsTrail`; the hypothesis is not needed.) -/
theorem Walk.even_countP_edges_iff' {u v : V} [DecidableEq V] (p : G.Walk u v) (x : V) :
    Even (p.edges.countP fun e => x ∈ e) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
  induction p with
  | nil => simp
  | cons huv p ih =>
    simp only [List.countP_cons, Ne, edges_cons, Sym2.mem_iff]
    split_ifs with h
    · rw [decide_eq_true_eq] at h
      obtain (rfl | rfl) := h
      · rw [Nat.even_add_one, ih]
        simp only [huv.ne, imp_false, Ne, not_false_iff, true_and, not_forall,
          Classical.not_not, exists_prop, not_true, false_and,
          and_iff_right_iff_imp]
        rintro rfl rfl
        exact G.loopless.irrefl _ huv
      · have := huv.ne; grind
    · grind

/-- **Closed walks have even incidence everywhere.** The parity workhorse for Stone B. -/
theorem Walk.even_countP_edges_of_closed {u : V} [DecidableEq V] (p : G.Walk u u) (x : V) :
    Even (p.edges.countP fun e => x ∈ e) :=
  (p.even_countP_edges_iff' x).mpr fun h => absurd rfl h

/-- **Trails never backtrack.** Consecutive darts of a trail form a non-backtracking chain:
a reversal `d_{i+1} = d_i.symm` would repeat the edge `d_i.edge` at two distinct positions,
contradicting `edges_nodup`. This gives every cycle (in particular) its NB chain. -/
theorem Walk.isChain_nbRel_darts_of_isTrail {u v : V} {w : G.Walk u v} (hw : w.IsTrail) :
    w.darts.IsChain G.nbRel := by
  refine List.isChain_iff_getElem.mpr fun i hi => ⟨w.isChain_dartAdj_darts.getElem i hi, ?_⟩
  intro hsymm
  have hb1 : i + 1 < w.edges.length := by
    rw [Walk.length_edges, ← Walk.length_darts]; omega
  have hb0 : i < w.edges.length := by omega
  have hedge : w.edges[i + 1]'hb1 = w.edges[i]'hb0 := by
    simp only [Walk.edges, List.getElem_map, hsymm, Dart.edge_symm]
  have hinj := List.nodup_iff_injective_get.mp hw.edges_nodup
  have := hinj (a₁ := ⟨i + 1, hb1⟩) (a₂ := ⟨i, hb0⟩)
    (by simp only [List.get_eq_getElem, hedge])
  simp only [Fin.mk.injEq] at this
  omega

end SimpleGraph
