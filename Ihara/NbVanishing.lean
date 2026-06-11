/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Ihara.NbWalkCount
import Ihara.TreeLikeWalks

/-!
# Stone A of the trace-formula gap law: `tr(Bᵏ) = 0` below the girth

Part III's final composition is the sharp gap law `tr(Aᵏ) − p_k = tr(Bᵏ)` for `1 ≤ k ≤ g+1`
(`g` the girth). Numerically locked twice: on the six named graphs
(`research/_tmp/traceformula_lock.py`) and exhaustively on ALL 12 064 connected cyclic graphs
with 4–8 vertices (`research/_tmp/gaplaw_sweep.py`, Sage `nauty_geng` sweep: 0 violations in
the window, 0 sharpness exceptions at `g+2`). This file lands **Stone A**, the below-girth
third: for `1 ≤ k < g` both sides vanish — the matching side by
`treeLikeGap_eq_zero_of_lt_egirth` (already proved), and the non-backtracking side because
**a closed non-backtracking walk shorter than the girth cannot exist**.

## The crux (`Walk.exists_isCycle_of_nbChain_of_not_nodup`)

A walk whose dart list is a `Chain' G.nbRel` (no two consecutive darts mutually reverse) and
whose support repeats a vertex contains a genuine cycle of length `≤` its own length. The proof
is structural induction on the walk, NOT the classical max-distance argument:

* `w = cons h p` with `p.support.Nodup` failing → recurse into `p` (the chain restricts by
  `tail`).
* `w = cons h p` with `p.support.Nodup` and `u ∈ p.support` → `c := p.takeUntil u` is a path
  (`IsPath.takeUntil`). Either the closing edge `s(u, u₁)` avoids `c.edges` — then `cons h c`
  is a cycle by `cons_isCycle_iff` — or `s(u, u₁) ∈ c.edges`, which by
  `IsPath.eq_penultimate_of_mem_edges` pins `c` to the single dart `(u₁, u) = (dart h).symm`
  and contradicts the non-backtracking chain at its first link.

No rotation is used anywhere: rotating would break the *linear* `Chain'` at the seam, and the
seam condition is never needed below `g + 2`.

## Assembly

`relWalks G.nbRel k e e = ∅` for `1 ≤ k < g`: a member list assembles (via
`exists_walk_of_dartChain`) into a closed `G.Walk` of length `k` with non-backtracking darts
and a repeated support vertex; the crux extracts a cycle of length `≤ k < g`, contradicting
`egirth_le_length`. The Hashimoto trace then vanishes by `trace_hashimoto_pow`.
-/

open Finset

/-! ## Anatomy of `relWalks` members (generic relation) -/

section RelWalks

variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop} [DecidableRel r]

/-- Every walk in `relWalks r k i j` is an `r`-chain. -/
theorem isChain_of_mem_relWalks {k : ℕ} {i j : V} {w : List V} (hw : w ∈ relWalks r k i j) :
    w.IsChain r := by
  induction k generalizing i w with
  | zero =>
    rw [relWalks] at hw
    split_ifs at hw with h
    · simp only [Finset.mem_singleton] at hw; subst hw; simp
    · simp at hw
  | succ k ih =>
    rw [relWalks, Finset.mem_biUnion] at hw
    obtain ⟨l, -, hl⟩ := hw
    split_ifs at hl with h
    · rw [Finset.mem_map] at hl
      obtain ⟨p, hp, rfl⟩ := hl
      have hhead := head?_of_mem_relWalks hp
      cases p with
      | nil => simp at hhead
      | cons a as =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        exact List.isChain_cons_cons.mpr ⟨h, ih hp⟩
    · simp at hl

/-- Every walk in `relWalks r k i j` ends at `j`. -/
theorem getLast?_of_mem_relWalks {k : ℕ} {i j : V} {w : List V} (hw : w ∈ relWalks r k i j) :
    w.getLast? = some j := by
  induction k generalizing i w with
  | zero =>
    rw [relWalks] at hw
    split_ifs at hw with h
    · simp only [Finset.mem_singleton] at hw; subst hw; simp [h]
    · simp at hw
  | succ k ih =>
    rw [relWalks, Finset.mem_biUnion] at hw
    obtain ⟨l, -, hl⟩ := hw
    split_ifs at hl with h
    · rw [Finset.mem_map] at hl
      obtain ⟨p, hp, rfl⟩ := hl
      have hlast := ih hp
      cases p with
      | nil => simp at hlast
      | cons a as => simpa using hlast
    · simp at hl

/-- Every walk in `relWalks r k i j` visits `k + 1` vertices. -/
theorem length_of_mem_relWalks {k : ℕ} {i j : V} {w : List V} (hw : w ∈ relWalks r k i j) :
    w.length = k + 1 := by
  induction k generalizing i w with
  | zero =>
    rw [relWalks] at hw
    split_ifs at hw with h
    · simp only [Finset.mem_singleton] at hw; subst hw; rfl
    · simp at hw
  | succ k ih =>
    rw [relWalks, Finset.mem_biUnion] at hw
    obtain ⟨l, -, hl⟩ := hw
    split_ifs at hl with h
    · rw [Finset.mem_map] at hl
      obtain ⟨p, hp, rfl⟩ := hl
      simp [ih hp]
    · simp at hl

end RelWalks

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## Dart-list anatomy of short walks -/

/-- A walk of length one consists of a single dart joining its endpoints. -/
theorem Walk.darts_eq_singleton_of_length_eq_one {x y : V} {q : G.Walk x y}
    (hq : q.length = 1) : ∃ hadj : G.Adj x y, q.darts = [⟨(x, y), hadj⟩] := by
  cases q with
  | nil => simp at hq
  | cons h q' =>
    cases q' with
    | nil => exact ⟨h, rfl⟩
    | cons h' q'' => simp only [Walk.length_cons] at hq; omega

/-! ## The crux: a non-backtracking chain with a repeated vertex contains a cycle -/

/-- **The cycle-extraction crux.** A walk whose darts form a non-backtracking chain
(`Chain' G.nbRel`) and whose support repeats a vertex contains a cycle of length at most the
walk's length. Structural induction; the `takeUntil` prefix of a nodup support is a path, so
the only obstruction to closing the cycle — the closing edge already lying on the path —
forces an immediate backtrack, contradicting the chain. -/
theorem Walk.exists_isCycle_of_nbChain_of_not_nodup [DecidableEq V] {u v : V} (w : G.Walk u v)
    (hnb : w.darts.IsChain G.nbRel) (hdup : ¬ w.support.Nodup) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ c.length ≤ w.length := by
  induction w with
  | nil => simp at hdup
  | @cons u u₁ v h p ih =>
    rw [Walk.support_cons, List.nodup_cons] at hdup
    rw [Walk.darts_cons] at hnb
    by_cases hp : p.support.Nodup
    · -- the repeat must be `u` re-entering `p`
      have hu : u ∈ p.support := by tauto
      have hcPath : (p.takeUntil u hu).IsPath := (p.isPath_def.mpr hp).takeUntil hu
      by_cases hedge : s(u, u₁) ∈ (p.takeUntil u hu).edges
      · -- the closing edge lies on the path: forces a backtrack, contradicting the chain
        exfalso
        set c := p.takeUntil u hu with hc
        have hpen : u₁ = c.penultimate := hcPath.eq_penultimate_of_mem_edges hedge
        -- the path starts at its own penultimate vertex, so it has length exactly one
        have hlc0 : c.length ≠ 0 := by
          intro h0
          have hver := c.getVert_length
          rw [h0, Walk.getVert_zero] at hver
          exact h.ne hver.symm
        have hl1 : c.length = 1 := by
          by_contra hne
          have hgg : c.support[0]'(by simp) =
              c.support[c.length - 1]'(by rw [Walk.length_support]; omega) := by
            rw [Walk.support_getElem_eq_getVert, Walk.support_getElem_eq_getVert,
              Walk.getVert_zero]
            exact hpen
          have hfin := c.isPath_iff_injective_get_support.mp hcPath hgg
          have hval : (0 : ℕ) = c.length - 1 := congrArg Fin.val hfin
          omega
        obtain ⟨hadj, hcd⟩ := Walk.darts_eq_singleton_of_length_eq_one hl1
        -- the first dart of `p` is the reverse of the entering dart
        have hpd : p.darts = ⟨(u₁, u), hadj⟩ :: (p.dropUntil u hu).darts := by
          conv_lhs => rw [← p.take_spec hu]
          rw [Walk.darts_append, ← hc, hcd]
          rfl
        rw [hpd] at hnb
        exact (List.isChain_cons_cons.mp hnb).1.2 (Dart.ext _ _ rfl)
      · -- the closing edge is fresh: `cons h (takeUntil)` is a genuine cycle
        refine ⟨u, Walk.cons h (p.takeUntil u hu),
          ((p.takeUntil u hu).cons_isCycle_iff h).mpr ⟨hcPath, hedge⟩, ?_⟩
        rw [Walk.length_cons, Walk.length_cons]
        exact Nat.succ_le_succ (p.length_takeUntil_le hu)
    · -- the repeat is inside `p`: recurse
      obtain ⟨a, c, hc, hlen⟩ := ih (List.isChain_of_isChain_cons hnb) hp
      exact ⟨a, c, hc, hlen.trans (by rw [Walk.length_cons]; exact Nat.le_succ _)⟩

/-! ## From dart lists to graph walks -/

/-- A nonempty chained dart list assembles into a graph walk using all but the last dart:
the walk starts at the first dart's tail and ends at the last dart's tail. -/
theorem exists_walk_of_dartChain (d : G.Dart) (l : List G.Dart)
    (hch : (d :: l).IsChain fun a b => a.snd = b.fst) :
    ∃ w : G.Walk d.fst ((d :: l).getLast (by simp)).fst,
      w.darts = (d :: l).dropLast := by
  induction l generalizing d with
  | nil => exact ⟨Walk.nil, rfl⟩
  | cons e rest ih =>
    obtain ⟨hde, hch'⟩ := List.isChain_cons_cons.mp hch
    obtain ⟨w', hw'⟩ := ih e hch'
    refine ⟨Walk.cons d.adj (w'.copy hde.symm rfl), ?_⟩
    rw [Walk.darts_cons, Walk.darts_copy, hw']
    rfl

/-! ## Assembly: emptiness, vanishing trace, and the below-girth gap law -/

variable [Fintype V] [DecidableEq V] (G) [DecidableRel G.Adj]

/-- **No closed non-backtracking walk below the girth.** -/
theorem relWalks_nbRel_closed_eq_empty {k : ℕ} (hk : 0 < k) (hg : (k : ℕ∞) < G.egirth)
    (e : G.Dart) : relWalks G.nbRel k e e = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro L hL
  have hch := isChain_of_mem_relWalks hL
  have hlen := length_of_mem_relWalks hL
  have hhead := head?_of_mem_relWalks hL
  have hlast := getLast?_of_mem_relWalks hL
  cases L with
  | nil => simp at hhead
  | cons d l =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    -- assemble the closed walk of length `k`
    have hch2 : (d :: l).IsChain (fun a b => a.snd = b.fst) := hch.imp fun _ _ hab => hab.1
    obtain ⟨w, hw⟩ := exists_walk_of_dartChain d l hch2
    have hgl : (d :: l).getLast (by simp) = d := by
      rw [List.getLast?_eq_getLast_of_ne_nil (by simp), Option.some.injEq] at hlast
      exact hlast
    set W : G.Walk d.fst d.fst := w.copy rfl (by rw [hgl]) with hW
    have hWd : W.darts = (d :: l).dropLast := by rw [hW, Walk.darts_copy, hw]
    have hWlen : W.length = k := by
      have := congrArg List.length hWd
      rw [Walk.length_darts, List.length_dropLast, hlen] at this
      simpa using this
    -- its support repeats the basepoint
    have hdup : ¬ W.support.Nodup := by
      intro hnd
      have hnil := (Walk.isPath_iff_eq_nil W).mp (W.isPath_def.mpr hnd)
      rw [hnil] at hWlen
      simp at hWlen
      omega
    -- non-backtracking chain on the walk's darts
    have hWnb : W.darts.IsChain G.nbRel := by
      rw [hWd]
      refine List.isChain_iff_getElem.mpr fun i hi => ?_
      simp only [List.getElem_dropLast]
      exact hch.getElem i (by simp only [List.length_dropLast] at hi; omega)
    -- extract a cycle shorter than the girth: contradiction
    obtain ⟨a, c, hcyc, hclen⟩ := W.exists_isCycle_of_nbChain_of_not_nodup hWnb hdup
    have h1 : G.egirth ≤ (c.length : ℕ∞) := G.egirth_le_length hcyc
    have h2 : (c.length : ℕ∞) ≤ (k : ℕ∞) := by
      rw [hWlen] at hclen
      exact_mod_cast hclen
    exact absurd ((h1.trans h2).trans_lt hg) (lt_irrefl _)

/-- **Stone A, non-backtracking side.** Below the girth the Hashimoto traces vanish:
`tr(Bᵏ) = 0` for `1 ≤ k < g`. -/
theorem trace_hashimoto_pow_eq_zero_of_lt_egirth (R : Type*) [CommRing R] {k : ℕ}
    (hk : 0 < k) (hg : (k : ℕ∞) < G.egirth) :
    ((G.hashimoto R) ^ k).trace = 0 := by
  rw [trace_hashimoto_pow]
  simp [relWalks_nbRel_closed_eq_empty G hk hg]

/-- **Stone A: the gap law below the girth.** For `1 ≤ k < g` both sides of the trace-formula
gap law vanish, so `gap_k = tr(Bᵏ)` holds (trivially) on the whole below-girth range. The
remaining window `k ∈ {g, g+1}` (where both sides equal `2k·c_k`) is Stone B. -/
theorem treeLikeGap_eq_trace_hashimoto_of_lt_egirth {k : ℕ} (hk : 0 < k)
    (hg : (k : ℕ∞) < G.egirth) :
    G.treeLikeGap k = ((G.hashimoto ℤ) ^ k).trace := by
  rw [G.treeLikeGap_eq_zero_of_lt_egirth k hg,
    G.trace_hashimoto_pow_eq_zero_of_lt_egirth ℤ hk hg]

end SimpleGraph
