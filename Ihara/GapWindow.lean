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

/-! ## W2: incidence counts on a cycle

Transfer of `IsCycle.ncard_neighborSet_toSubgraph_eq_two` from neighbour sets to edge-slot
incidence counts: a cycle meets each vertex of its support in exactly two edge slots, and
vertices outside the support in none. Together with W1 (parity) this is what bounds the
shapes a window walk can take. -/

/-- No edge of a walk is incident to a vertex outside its support. -/
theorem Walk.countP_edges_eq_zero_of_notMem_support [DecidableEq V] {u v x : V}
    {w : G.Walk u v} (hx : x ∉ w.support) :
    w.edges.countP (fun e => x ∈ e) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  simp only [decide_eq_true_eq]
  exact fun hxe => hx (Walk.mem_support_of_mem_edges he hxe)

/-- **W2: a cycle meets each of its support vertices in exactly two edge slots.** -/
theorem Walk.countP_edges_of_isCycle [DecidableEq V] {u x : V} {c : G.Walk u u}
    (hc : c.IsCycle) (hx : x ∈ c.support) :
    c.edges.countP (fun e => x ∈ e) = 2 := by
  have hnd : c.edges.Nodup := hc.isCircuit.isTrail.edges_nodup
  have hfin : (c.toSubgraph.neighborSet x).Finite := c.finite_neighborSet_toSubgraph
  have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hx
  rw [Set.ncard_eq_toFinset_card _ hfin] at h2
  have hndf : (c.edges.filter (fun e => decide (x ∈ e))).Nodup := hnd.filter _
  have hflen : (c.edges.filter (fun e => decide (x ∈ e))).length
      = (c.edges.filter (fun e => decide (x ∈ e))).toFinset.card := by
    rw [List.card_toFinset, List.dedup_eq_self.mpr hndf]
  rw [List.countP_eq_length_filter, hflen, ← h2]
  have hmem : ∀ e ∈ (c.edges.filter fun e => decide (x ∈ e)).toFinset, x ∈ e := by
    intro e he
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at he
    exact he.2
  refine Finset.card_bij' (fun e he => Sym2.Mem.other' (hmem e he))
    (fun y _ => s(x, y)) ?_ ?_ ?_ ?_
  · intro e he
    rw [Set.Finite.mem_toFinset, Subgraph.mem_neighborSet, ← Subgraph.mem_edgeSet,
      Sym2.other_spec' (hmem e he), Walk.mem_edges_toSubgraph]
    have := List.mem_toFinset.mp he
    exact (List.mem_filter.mp this).1
  · intro y hy
    rw [Set.Finite.mem_toFinset, Subgraph.mem_neighborSet] at hy
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    refine ⟨?_, Sym2.mem_mk_left x y⟩
    rw [← Walk.mem_edges_toSubgraph, Subgraph.mem_edgeSet]
    exact hy
  · intro e he
    exact Sym2.other_spec' (hmem e he)
  · intro y hy
    exact Sym2.congr_right.mp (Sym2.other_spec' _)

/-! ## W3: a closed trail on exactly a cycle's edges is that cycle

If a closed walk's edge list is a permutation of a cycle's edge list, the walk is itself a
cycle. The crux: a repeated support vertex `x` would, after rotating the walk to base `x`,
sit at three pairwise-distinct edge slots `{0, m−1, m}`; the walk is a trail (its edges are
the cycle's, nodup), so these are three DISTINCT edges incident to `x` — contradicting the
exact incidence count 2 of W2. -/

/-- Both endpoints of the `t`-th edge slot: `getVert t` and `getVert (t+1)` lie in
`edges[t]`. -/
theorem Walk.getVert_mem_edges_getElem {u v : V} {p : G.Walk u v} {t : ℕ} (ht : t < p.length) :
    p.getVert t ∈ p.edges[t]'(by rw [Walk.length_edges]; exact ht)
      ∧ p.getVert (t + 1) ∈ p.edges[t]'(by rw [Walk.length_edges]; exact ht) := by
  have htd : t < p.darts.length := by rw [Walk.length_darts]; exact ht
  have he : p.edges[t]'(by rw [Walk.length_edges]; exact ht) = (p.darts[t]'htd).edge := by
    simp only [Walk.edges, List.getElem_map]
  have hf : (p.darts[t]'htd).fst = p.getVert t := by
    rw [Walk.fst_darts_getElem htd, List.getElem_dropLast,
      Walk.support_getElem_eq_getVert]
  have hs : (p.darts[t]'htd).snd = p.getVert (t + 1) := by
    rw [Walk.snd_darts_getElem htd, List.getElem_tail,
      Walk.support_getElem_eq_getVert]
  rw [he]
  have hde : (p.darts[t]'htd).edge = s((p.darts[t]'htd).fst, (p.darts[t]'htd).snd) := rfl
  rw [hde, hf, hs]
  exact ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _⟩

/-- **W3.** A closed walk of positive length whose edge list is a permutation of a cycle's
edge list is itself a cycle. -/
theorem Walk.isCycle_of_edges_perm [DecidableEq V] {v a : V} {w : G.Walk v v}
    {c : G.Walk a a} (hc : c.IsCycle) (hperm : w.edges.Perm c.edges)
    (hpos : 0 < w.length) : w.IsCycle := by
  have hwnd : w.edges.Nodup := hperm.nodup_iff.mpr hc.isCircuit.isTrail.edges_nodup
  have hnenil : w ≠ Walk.nil := by
    intro h
    rw [h] at hpos
    simp at hpos
  refine ⟨⟨⟨hwnd⟩, hnenil⟩, ?_⟩
  by_contra htail
  -- a duplicated vertex x in the tail
  obtain ⟨x, hx2⟩ : ∃ x, 2 ≤ w.support.tail.count x := by
    by_contra hno
    push_neg at hno
    exact htail (List.nodup_iff_count_le_one.mpr fun y => by have := hno y; omega)
  have hxtail : x ∈ w.support.tail := List.count_pos_iff.mp (by omega)
  have hxsupp : x ∈ w.support := List.mem_of_mem_tail hxtail
  -- rotate the walk to base x: trail and incidence counts survive
  set w' := w.rotate x hxsupp with hw'
  have hlen' : w'.length = w.length := by
    rw [hw', Walk.length_rotate]
  have hperm' : w'.edges.Perm w.edges := (w.rotate_edges x hxsupp).perm
  have hwnd' : w'.edges.Nodup := hperm'.nodup_iff.mpr hwnd
  have htperm : w'.support.tail.Perm w.support.tail := (w.support_rotate x hxsupp).perm
  have hx2' : 2 ≤ w'.support.tail.count x := by rw [htperm.count_eq]; exact hx2
  -- an interior occurrence: x = getVert m with 1 ≤ m ≤ length − 1
  have htne : w'.support.tail ≠ [] := by
    intro h0
    rw [h0] at hx2'
    simp at hx2'
  have hxdl : x ∈ w'.support.tail.dropLast := by
    by_contra hno
    have hsplit := List.dropLast_concat_getLast htne
    have : w'.support.tail.count x ≤ 1 := by
      rw [← hsplit, List.count_append]
      have h0 : w'.support.tail.dropLast.count x = 0 :=
        List.count_eq_zero_of_not_mem hno
      have h1 : [w'.support.tail.getLast htne].count x ≤ 1 := by
        rcases em (w'.support.tail.getLast htne = x) with h | h <;> simp [h]
      omega
    omega
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxdl
  rw [List.getElem_dropLast] at hix
  have hilt : i + 1 ≤ w'.length - 1 := by
    have h1 : w'.support.tail.dropLast.length = w'.length - 1 := by
      rw [List.length_dropLast, List.length_tail, Walk.length_support]
      omega
    omega
  set m := i + 1 with hm
  have hgm : w'.getVert m = x := by
    have := List.getElem_tail (l := w'.support) (i := i)
      (h := by rw [List.length_tail, Walk.length_support]; omega)
    rw [this] at hix
    rw [← Walk.support_getElem_eq_getVert]
    exact hix
  have hg0 : w'.getVert 0 = x := Walk.getVert_zero _
  -- m = 1 is a loop; kill it
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · exfalso
      have hm1 : m = 1 := by omega
      have hg1 : w'.getVert 1 = x := by rw [← hm1]; exact hgm
      have hadj := w'.adj_getVert_succ (i := 0) (by omega)
      rw [hg0, hg1] at hadj
      exact G.irrefl hadj
    · exact h
  -- three distinct edges incident to x: slots 0, m−1, m
  have hke : w'.edges.length = w'.length := Walk.length_edges _
  have hb0 : 0 < w'.edges.length := by omega
  have hbm1 : m - 1 < w'.edges.length := by omega
  have hbm : m < w'.edges.length := by omega
  have he0 : x ∈ w'.edges[0]'hb0 := by
    have := (w'.getVert_mem_edges_getElem (t := 0) (by omega)).1
    rwa [hg0] at this
  have hem1 : x ∈ w'.edges[m - 1]'hbm1 := by
    have := (w'.getVert_mem_edges_getElem (t := m - 1) (by omega)).2
    rwa [show m - 1 + 1 = m by omega, hgm] at this
  have hem : x ∈ w'.edges[m]'hbm := by
    have := (w'.getVert_mem_edges_getElem (t := m) (by omega)).1
    rwa [hgm] at this
  have hinj := List.nodup_iff_injective_get.mp hwnd'
  have hne1 : w'.edges[0]'hb0 ≠ w'.edges[m - 1]'hbm1 := fun h => by
    have := hinj (a₁ := ⟨0, hb0⟩) (a₂ := ⟨m - 1, hbm1⟩)
      (by simp only [List.get_eq_getElem, h])
    simp only [Fin.mk.injEq] at this
    omega
  have hne2 : w'.edges[0]'hb0 ≠ w'.edges[m]'hbm := fun h => by
    have := hinj (a₁ := ⟨0, hb0⟩) (a₂ := ⟨m, hbm⟩)
      (by simp only [List.get_eq_getElem, h])
    simp only [Fin.mk.injEq] at this
    omega
  have hne3 : w'.edges[m - 1]'hbm1 ≠ w'.edges[m]'hbm := fun h => by
    have := hinj (a₁ := ⟨m - 1, hbm1⟩) (a₂ := ⟨m, hbm⟩)
      (by simp only [List.get_eq_getElem, h])
    simp only [Fin.mk.injEq] at this
    omega
  -- hence the incidence count at x is ≥ 3
  have hcnt3 : 3 ≤ w'.edges.countP (fun e => x ∈ e) := by
    have hndf : (w'.edges.filter (fun e => decide (x ∈ e))).Nodup := hwnd'.filter _
    have hsubF : ({w'.edges[0]'hb0, w'.edges[m - 1]'hbm1, w'.edges[m]'hbm} : Finset _)
        ⊆ (w'.edges.filter (fun e => decide (x ∈ e))).toFinset := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rw [List.mem_toFinset, List.mem_filter]
      rcases he with rfl | rfl | rfl
      · exact ⟨List.getElem_mem _, by simpa using he0⟩
      · exact ⟨List.getElem_mem _, by simpa using hem1⟩
      · exact ⟨List.getElem_mem _, by simpa using hem⟩
    have hcard3 : ({w'.edges[0]'hb0, w'.edges[m - 1]'hbm1, w'.edges[m]'hbm}
        : Finset _).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hne1, hne2]),
        Finset.card_insert_of_notMem (by simp [hne3]), Finset.card_singleton]
    have hle := Finset.card_le_card hsubF
    rw [hcard3] at hle
    have htf : (w'.edges.filter (fun e => decide (x ∈ e))).toFinset.card
        = w'.edges.countP (fun e => x ∈ e) := by
      rw [List.card_toFinset, List.dedup_eq_self.mpr hndf, List.countP_eq_length_filter]
    omega
  -- but the count transfers to the cycle, where it is at most 2
  have hctrans : w'.edges.countP (fun e => x ∈ e) = c.edges.countP (fun e => x ∈ e) :=
    (hperm'.trans hperm).countP_eq _
  have hcle2 : c.edges.countP (fun e => x ∈ e) ≤ 2 := by
    by_cases hxc : x ∈ c.support
    · rw [Walk.countP_edges_of_isCycle hc hxc]
    · rw [Walk.countP_edges_eq_zero_of_notMem_support hxc]
      omega
  omega

/-! ## W4: a closed walk is never "a cycle plus one extra edge slot"

The Stone B case `|C| = g, k = g+1` dies here: if a closed walk's edge multiset were a
cycle's edges plus a single extra slot `f`, then any endpoint `x` of `f` would have odd
incidence count (`2 + 1` if `x` lies on the cycle, `0 + 1` if not) — contradicting the
parity lemma W1. Note: no trail or non-backtracking hypothesis is needed; parity alone
kills the case. -/

/-- **W4.** No closed walk has edge multiset = (edges of a cycle) + one extra slot. -/
theorem Walk.not_closed_of_isCycle_edges_add_one [DecidableEq V] {v a : V} {w : G.Walk v v}
    {c : G.Walk a a} (hc : c.IsCycle) (hsub : c.edges ⊆ w.edges)
    (hlen : w.length = c.length + 1) : False := by
  have hnd : c.edges.Nodup := hc.isCircuit.isTrail.edges_nodup
  -- multiset surgery: w.edges = f ::ₘ c.edges for a single extra slot f
  have hsp : (c.edges : Multiset (Sym2 V)) ≤ (w.edges : Multiset (Sym2 V)) :=
    Multiset.coe_le.mpr (hnd.subperm hsub)
  have hsac := Multiset.sub_add_cancel hsp
  have hcards := congrArg Multiset.card hsac
  rw [Multiset.card_add] at hcards
  simp only [Multiset.coe_card, Walk.length_edges] at hcards
  have hcard1 : ((w.edges : Multiset (Sym2 V)) - (c.edges : Multiset (Sym2 V))).card = 1 := by
    omega
  obtain ⟨f, hf⟩ := Multiset.card_eq_one.mp hcard1
  have hw : (w.edges : Multiset (Sym2 V)) = f ::ₘ (c.edges : Multiset (Sym2 V)) := by
    rw [← hsac, hf, Multiset.singleton_add]
  obtain ⟨x, hxf⟩ : ∃ x, x ∈ f := Sym2.ind (fun y z => ⟨y, Sym2.mem_mk_left y z⟩) f
  -- the incidence count at x is odd, contradicting W1
  have heven := w.even_countP_edges_of_closed x
  have hcnt : w.edges.countP (fun e => x ∈ e)
      = c.edges.countP (fun e => x ∈ e) + 1 := by
    have hmc := congrArg (Multiset.countP fun e => decide (x ∈ e)) hw
    simpa [Multiset.countP_cons, hxf] using hmc
  by_cases hxs : x ∈ c.support
  · rw [hcnt, Walk.countP_edges_of_isCycle hc hxs, Nat.even_iff] at heven
    omega
  · rw [hcnt, Walk.countP_edges_eq_zero_of_notMem_support hxs, Nat.even_iff] at heven
    omega

/-! ## W5 = STONE B-2: in the window, a closed non-backtracking walk IS a cycle

The composition: the strengthened Stone A crux extracts a cycle `C` on the walk's edges with
`g ≤ |C| ≤ k ≤ g+1`, so either `|C| = k` (W3: the walk is a permutation of the cycle, hence
the cycle) or `|C| = k−1` (W4: parity kills it). -/

/-- **Stone B-2.** A closed non-backtracking walk of positive length at most `girth + 1`
is a cycle. -/
theorem Walk.isCycle_of_nbChain_window [DecidableEq V] {v : V} {w : G.Walk v v}
    (hnb : w.darts.IsChain G.nbRel) (hpos : 0 < w.length)
    (hwin : (w.length : ℕ∞) ≤ G.egirth + 1) : w.IsCycle := by
  have hdup : ¬ w.support.Nodup := fun hnod => by
    have hnil := (Walk.isPath_iff_eq_nil w).mp (w.isPath_def.mpr hnod)
    rw [hnil] at hpos
    simp at hpos
  obtain ⟨a, c, hcyc, hlen, hsub⟩ := w.exists_isCycle_of_nbChain_of_not_nodup hnb hdup
  have hg := G.egirth_le_length hcyc
  have hcw : w.length ≤ c.length + 1 := by
    have h1 : (w.length : ℕ∞) ≤ (c.length : ℕ∞) + 1 :=
      hwin.trans (add_le_add hg le_rfl)
    exact_mod_cast h1
  rcases Nat.lt_or_ge c.length w.length with hlt | hge
  · exact (Walk.not_closed_of_isCycle_edges_add_one hcyc hsub (by omega)).elim
  · have hsp : List.Subperm c.edges w.edges :=
      hcyc.isCircuit.isTrail.edges_nodup.subperm hsub
    have hperm : w.edges.Perm c.edges := by
      refine (hsp.perm_of_length_le ?_).symm
      rw [Walk.length_edges, Walk.length_edges]
      omega
    exact Walk.isCycle_of_edges_perm hcyc hperm hpos

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
