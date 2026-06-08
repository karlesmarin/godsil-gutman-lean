/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Ihara.TraceFormula
import Mathlib.Combinatorics.SimpleGraph.Girth

/-!
# Godsil's path-tree tree-like walks (CORRECT definition) — dev for Part III brick 3

The earlier `Walk.IsTreeLike := acyclic edge-support` (in `Ihara/TreeLikeWalks.lean`) is WRONG for
Godsil's moment theorem: it undercounts (Sage `verify_godsil.py`: K4, k=6 gives acyclic-count 276,
but the matching power sum is `p_6 = 324`). The correct notion is the **path-tree lift**
(`verify_pathtree.py`, matches `p_k` for P4/C4/K4/K5/Petersen/K_{3,3}, k=0..8).

**Path tree `T(G,v)`** (Godsil 1981): vertices are the simple paths in `G` starting at `v`; a path
is adjacent to its one-vertex extensions. A closed walk in `G` is **tree-like** iff it lifts to a
closed walk at the root of `T(G,v)`. The lift is *deterministic*: maintaining the current simple
path as a stack (root → current vertex), each step of the walk is either
* an **EXTEND** — the next vertex is new (not on the current path): push it; or
* a **RETREAT** — the next vertex is the parent (the penultimate vertex of the current path): pop;
* anything else fails (no such edge in the tree).
Extend (`c ∉ stack`) and retreat (`c ∈ stack`) are mutually exclusive, so the lift is a fold.

This dev file pins the CORRECT definition + decidability + the `nil` base case sorry-free.
Remaining sub-brick: the below-girth lift lemma (every closed walk shorter than the girth lifts),
after which this subsumes `TreeLikeWalks.lean` and we swap.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Deterministic lift of a sequence of visited vertices into the path tree, threading the current
simple path (`stack`, from root to current vertex). For each next vertex `c`: if `c ∉ stack` push it
(EXTEND); else if `c` is the penultimate vertex of `stack` pop the last (RETREAT to parent); else
fail. Returns the final stack, or `none` if some step is neither extend nor retreat. -/
def liftSeq : List V → List V → Option (List V)
  | [], stack => some stack
  | c :: rest, stack =>
      if c ∈ stack then
        (if stack.dropLast.getLast? = some c then liftSeq rest stack.dropLast else none)
      else liftSeq rest (stack ++ [c])

/-- Definitional unfolding of `liftSeq` on a `cons`. -/
theorem liftSeq_cons (c : V) (rest stack : List V) :
    liftSeq (c :: rest) stack
      = if c ∈ stack then
          (if stack.dropLast.getLast? = some c then liftSeq rest stack.dropLast else none)
        else liftSeq rest (stack ++ [c]) := rfl

/-- A closed walk is **tree-like** (Godsil's path-tree class) iff its deterministic lift, started at
the root path `[v]`, returns to the root path `[v]` (a closed walk at the root of `T(G,v)`). This is
the path-tree-faithful definition (matches `verify_pathtree.py`; e.g. K4, k=6 → 324). -/
def Walk.IsTreeLike {v : V} (w : G.Walk v v) : Prop :=
  liftSeq w.support.tail [v] = some [v]

instance {v : V} (w : G.Walk v v) : Decidable w.IsTreeLike := by
  unfold Walk.IsTreeLike; infer_instance

/-- The empty walk lifts trivially: its only visited vertex is the root, the lift never moves, and
the stack stays `[v]`. -/
theorem Walk.nil_isTreeLike (v : V) : (Walk.nil : G.Walk v v).IsTreeLike := by
  simp [Walk.IsTreeLike, liftSeq]

/-! ## Below the girth: every closed walk lifts (the remaining sub-brick)

Below the (extended) girth the walk's edge-support is acyclic (a forest). On a forest the lift
*always* succeeds: the deterministic stack stays equal to the unique forest-path from the root to
the current vertex, so each step is forced to be EXTEND (edge away from root) or RETREAT (edge back
toward root, hitting the penultimate vertex). A closed walk returns the stack to `[v]`.

The core inductive invariant is `liftSeq_eq_pathSupport_of_acyclic`: matching `liftSeq`'s `List V`
stack to the graph-theoretic unique forest-path. The crux — acyclicity forcing each RETREAT to the
penultimate vertex — is isolated in `eq_penultimate_of_acyclic` (build a cycle from the would-be
chord and contradict `H.coe.IsAcyclic`). Now **sorry-free**: `Walk.isTreeLike_of_acyclic` closes the
acyclic ⇒ path-tree-tree-like direction, subsuming `TreeLikeWalks.lean`'s below-girth result for the
path-tree-faithful definition. -/

section BelowGirth
variable [Fintype V] [DecidableRel G.Adj]

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
/-- A subgraph of an acyclic (coerced) subgraph is acyclic: pull a cycle back along the injective
inclusion `H₁.coe →g H₂.coe`. -/
theorem Subgraph.coe_isAcyclic_mono {H₁ H₂ : G.Subgraph} (hle : H₁ ≤ H₂)
    (h : H₂.coe.IsAcyclic) : H₁.coe.IsAcyclic :=
  h.comap (Subgraph.inclusion hle) (Subgraph.inclusion.injective hle)

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
/-- A cycle of `G` whose edges all lie inside a subgraph `H` lifts to a cycle of `H.coe`, so an
acyclic `H.coe` admits none. Lift `C` first to its own subgraph (`mapToSubgraph`, injective via
`toSubgraph.hom`), then along the injective inclusion `C.toSubgraph ↪ H`. -/
theorem not_isCycle_of_toSubgraph_le {x : V} {H : G.Subgraph} (C : G.Walk x x)
    (hC : C.IsCycle) (hle : C.toSubgraph ≤ H) (hac : H.coe.IsAcyclic) : False := by
  have h1 : C.mapToSubgraph.IsCycle :=
    (Walk.map_isCycle_iff_of_injective Subgraph.hom_injective).mp
      (by rw [Walk.map_mapToSubgraph_hom]; exact hC)
  exact hac _ (h1.map (Subgraph.inclusion.injective hle))

omit [Fintype V] [DecidableRel G.Adj] in
/-- **The acyclicity crux.** In an acyclic ambient subgraph `H` containing a simple path
`sp : root → a` and the edge `a ~ c`, if `c` lies on `sp` then `c` must be the penultimate vertex of
`sp` (its neighbour along the path). Otherwise the `sp`-segment from `c` to `a` together with the
closing edge `a~c` would form a cycle inside `H`, contradicting `hac`. -/
theorem eq_penultimate_of_acyclic {root a c : V} {H : G.Subgraph} (sp : G.Walk root a)
    (hsp : sp.IsPath) (h : G.Adj a c) (hv : c ∈ sp.support)
    (hcsub : G.subgraphOfAdj h ≤ H) (hspsub : sp.toSubgraph ≤ H) (hac : H.coe.IsAcyclic) :
    c = sp.penultimate := by
  by_contra hne
  -- the closing edge is not among the `c→a` segment's edges (else `c` would be `sp.penultimate`).
  have hedge : s(a, c) ∉ (sp.dropUntil c hv).edges := fun hmem =>
    hne (hsp.eq_penultimate_of_mem_edges (sp.edges_dropUntil_subset hv hmem))
  -- `C` := the closing edge `a→c` followed by the `c→a` segment of `sp`: a genuine cycle.
  have hC : (Walk.cons h (sp.dropUntil c hv)).IsCycle :=
    (Walk.cons_isCycle_iff (sp.dropUntil c hv) h).mpr ⟨hsp.dropUntil hv, hedge⟩
  have hCle : (Walk.cons h (sp.dropUntil c hv)).toSubgraph ≤ H := by
    have hCsg : (Walk.cons h (sp.dropUntil c hv)).toSubgraph
        = G.subgraphOfAdj h ⊔ (sp.dropUntil c hv).toSubgraph := rfl
    rw [hCsg]
    refine sup_le hcsub (le_trans ?_ hspsub)
    conv_rhs => rw [← Walk.take_spec sp hv]
    rw [Walk.toSubgraph_append]; exact le_sup_right
  exact not_isCycle_of_toSubgraph_le _ hC hCle hac

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
/-- For a non-nil walk, the last entry of its support with the endpoint dropped is the penultimate
vertex (`getLast?` of `support.dropLast`). -/
theorem Walk.support_dropLast_getLast?_eq_penultimate {u v : V} (p : G.Walk u v) (hp : ¬ p.Nil) :
    p.support.dropLast.getLast? = some p.penultimate := by
  rw [← Walk.support_dropLast hp,
    List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _), Walk.getLast_support]

omit [Fintype V] [DecidableRel G.Adj] in
/-- **Invariant.** If the ambient is acyclic, running `liftSeq` on the tail of a path `p`'s
support, started from the vertex list of a simple path `sp` from the root to `p`'s source, returns
the vertex list of the simple path from the root to `p`'s target. (Forest unique-path bookkeeping:
each step extends or retreats the unique root-path; this is where the `List ↔ graph-path` friction
lives.) -/
theorem liftSeq_eq_pathSupport_of_acyclic {root a b : V} (p : G.Walk a b)
    (sp : G.Walk root a) (hsp : sp.IsPath)
    (hacyc : (p.toSubgraph ⊔ sp.toSubgraph).coe.IsAcyclic) :
    ∃ sq : G.Walk root b, sq.IsPath ∧ liftSeq p.support.tail sp.support = some sq.support := by
  induction p with
  | nil =>
      -- p = nil: support = [a], tail = [], liftSeq [] sp.support = some sp.support; take sq = sp
      exact ⟨sp, hsp, by simp [liftSeq, Walk.support_nil]⟩
  | @cons a' c b' h q ih =>
      -- step a' → c (h : G.Adj a' c), then q : Walk c b'. Next vertex = c.
      have e1 : (Walk.cons h q).support.tail = c :: q.support.tail := by
        rw [Walk.support_cons, List.tail_cons]; exact (Walk.cons_tail_support q).symm
      rw [e1, liftSeq_cons]
      by_cases hv : c ∈ sp.support
      · -- RETREAT: c already on the path. Acyclicity forces c = penultimate (parent), pop to it.
        rw [if_pos hv]
        -- `sp` is non-nil: `c` is on it and `c ≠ a'` (an edge has distinct ends).
        have hnil_sp : ¬ sp.Nil := by
          intro hn
          have hc_root : c = root := by
            have hsupp := Walk.nil_iff_support_eq.mp hn
            rw [hsupp] at hv; exact List.mem_singleton.mp hv
          exact G.ne_of_adj h (hc_root.trans hn.eq).symm
        -- ambient contains the closing edge `a'~c`.
        have hcsub : G.subgraphOfAdj h ≤ (Walk.cons h q).toSubgraph ⊔ sp.toSubgraph := by
          have hcons : (Walk.cons h q).toSubgraph = G.subgraphOfAdj h ⊔ q.toSubgraph := rfl
          rw [hcons]; exact le_sup_of_le_left le_sup_left
        -- (A) acyclicity forces `c` to be the parent (penultimate) of `a'` on `sp`; the guard fires.
        have hpen : c = sp.penultimate :=
          eq_penultimate_of_acyclic sp hsp h hv hcsub le_sup_right hacyc
        have hguard : sp.support.dropLast.getLast? = some c := by
          rw [hpen]; exact sp.support_dropLast_getLast?_eq_penultimate hnil_sp
        rw [if_pos hguard]
        -- (C) newsp = the root→c prefix of sp; its support is `sp.support` minus the last vertex.
        have hnewpath : (sp.takeUntil c hv).IsPath := hsp.takeUntil hv
        have hnewsupp : (sp.takeUntil c hv).support = sp.support.dropLast := by
          have hnd := hsp.support_nodup
          have hlen1 : 1 ≤ sp.length := by
            rw [Nat.one_le_iff_ne_zero, Ne, ← Walk.nil_iff_length_eq]; exact hnil_sp
          have hbound : sp.length - 1 < sp.support.length := by
            rw [Walk.length_support]; lia
          have hcget : sp.support[sp.length - 1]'hbound = c := by
            rw [Walk.support_getElem_length_sub_one_eq_penultimate]; exact hpen.symm
          have hidx : sp.support.idxOf c = sp.length - 1 := by
            rw [← hcget]; exact hnd.idxOf_getElem _ hbound
          rw [Walk.takeUntil_eq_take, Walk.support_copy, hidx,
            ← Walk.support_dropLast hnil_sp]
          simp only [Walk.dropLast]
        -- (D) acyclic for the IH, by monotonicity: takeUntil ≤ sp ≤ ambient
        have hle : (sp.takeUntil c hv).toSubgraph ≤ sp.toSubgraph := by
          conv_rhs => rw [← Walk.take_spec sp hv]
          rw [Walk.toSubgraph_append]; exact le_sup_left
        have hamb : q.toSubgraph ⊔ (sp.takeUntil c hv).toSubgraph
            ≤ (Walk.cons h q).toSubgraph ⊔ sp.toSubgraph := by
          have hcons : (Walk.cons h q).toSubgraph = G.subgraphOfAdj h ⊔ q.toSubgraph := rfl
          rw [hcons]
          exact sup_le (le_sup_of_le_left le_sup_right) (le_sup_of_le_right hle)
        have hac : (q.toSubgraph ⊔ (sp.takeUntil c hv).toSubgraph).coe.IsAcyclic :=
          Subgraph.coe_isAcyclic_mono hamb hacyc
        obtain ⟨sq, hsq, hlift⟩ := ih (sp.takeUntil c hv) hnewpath hac
        rw [hnewsupp] at hlift
        exact ⟨sq, hsq, hlift⟩
      · -- EXTEND: c is new; push it. Lift continues from sp.concat h.
        rw [if_neg hv]
        have hpath : (sp.concat h).IsPath := hsp.concat hv h
        have hsupp : (sp.concat h).support = sp.support ++ [c] := Walk.support_concat sp h
        have hac : (q.toSubgraph ⊔ (sp.concat h).toSubgraph).coe.IsAcyclic := by
          have hcons : (Walk.cons h q).toSubgraph = G.subgraphOfAdj h ⊔ q.toSubgraph := rfl
          have key : q.toSubgraph ⊔ (sp.concat h).toSubgraph
              = (Walk.cons h q).toSubgraph ⊔ sp.toSubgraph := by
            rw [hcons, Walk.concat_eq_append, Walk.toSubgraph_append,
              Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
            ac_rfl
          rw [key]; exact hacyc
        obtain ⟨sq, hsq, hlift⟩ := ih (sp.concat h) hpath hac
        rw [hsupp] at hlift
        exact ⟨sq, hsq, hlift⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- A closed walk whose edge-support is acyclic is tree-like: take `sp = nil` (root path `[v]`) in
the invariant; the returned simple path from `v` to `v` is `nil`, support `[v]`. -/
theorem Walk.isTreeLike_of_acyclic {v : V} (w : G.Walk v v)
    (hacyc : w.toSubgraph.coe.IsAcyclic) : w.IsTreeLike := by
  have hsing : (Walk.nil : G.Walk v v).toSubgraph = G.singletonSubgraph v := by simp
  have heq : w.toSubgraph ⊔ (Walk.nil : G.Walk v v).toSubgraph = w.toSubgraph := by
    rw [hsing, sup_eq_left]
    exact (G.singletonSubgraph_le_iff v _).mpr w.start_mem_verts_toSubgraph
  obtain ⟨sq, hsqpath, hlift⟩ :=
    liftSeq_eq_pathSupport_of_acyclic w (Walk.nil : G.Walk v v) (by simp) (heq.symm ▸ hacyc)
  -- a simple path from v to v is nil, so its support is [v]
  have hsqnil : sq = Walk.nil := (Walk.isPath_iff_eq_nil sq).mp hsqpath
  rw [Walk.IsTreeLike]
  simpa [hsqnil] using hlift

end BelowGirth

end SimpleGraph
