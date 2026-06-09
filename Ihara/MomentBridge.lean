/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Ihara.TreeLikeWalks
import MSS.PathTree
import MSS.Divisibility
import MSS.ForestRealRooted

/-!
# Welding Godsil's path tree to tree-like walk counts — moment theorem, stone 1

Godsil's moment theorem `p_k = Σᵢ θᵢᵏ = treeLikeWalkCount G k` (the matching side of the
matching↔Ihara trace-formula bridge) routes through the **path tree** `T(G,v) = pathTree G v`
(`MSS/PathTree.lean`, built for the Heilmann–Lieb formalisation): the SAME forest that carries the
real spectrum of `μ(G)` also counts the closed tree-like walks of `G`.

The connection is the **down-projection** `π : T(G,v) →g G`, a path ↦ its endpoint. A closed walk
at the root of `T(G,v)` projects under `π` to a closed walk at `v` of `G`; because `T(G,v)` is a
forest, that projection lands exactly in the tree-like class (`Ihara/PathTree.lean`), and the lift
is unique — so the projection is a length-preserving bijection onto the tree-like walks. That
bijection turns `[A(T(G,v))ᵏ]_{root,root}` (a spectral quantity, via `μ(T−root)/μ(T)`) into
`treeLikeWalkCount`, which is Godsil's theorem.

This file lands the first stone: the projection hom and its basic properties. The bijection,
the resolvent identity `μ(G−v)/μ(G) = μ(T−root)/μ(T)`, and the Newton step are the remaining stones.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **The down-projection `π : T(G,v) →g G`**, sending a path-tree vertex (a path of `G` from `v`)
to its endpoint. Adjacency in the path tree means one path extends the other by a single edge, so
the two endpoints are adjacent in `G`; hence `π` is a graph homomorphism. This is the map along
which closed walks at the root of the (forest) path tree project to closed tree-like walks of `G`. -/
def pathTreeProj (G : SimpleGraph V) (u : V) : G.pathTree u →g G where
  toFun a := a.1
  map_rel' {a b} h := by
    rcases h with ⟨he, _⟩ | ⟨he, _⟩
    · exact he
    · exact he.symm

@[simp] theorem pathTreeProj_apply (G : SimpleGraph V) (u : V) (a : G.PathFrom u) :
    G.pathTreeProj u a = a.1 := rfl

/-- The projection sends the path-tree root (the trivial path at `u`) to `u`. -/
@[simp] theorem pathTreeProj_root (G : SimpleGraph V) (u : V) :
    G.pathTreeProj u (pathTreeRoot G u) = u := rfl

/-- A closed walk at the root of the path tree projects, under `π`, to a closed walk at `u` of `G`
of the same length: this is the map whose image is exactly the tree-like walks (next stone). -/
theorem pathTreeProj_map_length {u : V} (w : (G.pathTree u).Walk (pathTreeRoot G u) (pathTreeRoot G u)) :
    (w.map (G.pathTreeProj u)).length = w.length :=
  Walk.length_map _ _

/-! ## Local injectivity of the projection (the path tree is an immersion of `G`)

The bijection "closed walks at the root of `T(G,v)` ↔ closed tree-like walks of `G` at `v`" is
realised by `Walk.map (pathTreeProj G v)`. Its injectivity rests on a purely local fact: `π` is
injective on the neighbours of *each* path-tree vertex `p`. The neighbours of `p` are its unique
parent (`dropLast`) and its children (one-edge extensions); `π` sends the parent to `p`'s penultimate
vertex (which lies on `p`) and each child to its fresh endpoint (which does not), and distinct
children have distinct endpoints — so the projection separates all neighbours of `p`. -/

/-- **Child uniqueness** (dual of `Grows.parent_unique`): a one-edge extension of `p` is determined
by its endpoint. If `a` and `a'` both grow from `p` and share an endpoint, they are equal. -/
theorem Grows.child_unique {u : V} {p a a' : G.PathFrom u}
    (h : Grows p a) (h' : Grows p a') (hv : a.1 = a'.1) : a = a' := by
  obtain ⟨he, hb⟩ := h
  obtain ⟨he', hb'⟩ := h'
  obtain ⟨av, aw, hawp⟩ := a
  obtain ⟨a'v, a'w, ha'wp⟩ := a'
  subst hv
  obtain rfl : aw = a'w := hb.trans hb'.symm
  rfl

/-- **`π` is injective on the neighbour set of each path-tree vertex** — the path tree is an
immersion of `G`. Parents coincide by `parent_unique`, children by `child_unique`; a child's
endpoint is fresh (`∉ p.support`) while a parent's endpoint is `p`'s penultimate (`∈ p.support`),
so the two families never collide. This local injectivity drives the walk-lift bijection. -/
theorem pathTreeProj_injOn_neighborSet (G : SimpleGraph V) (u : V) (p : G.PathFrom u) :
    Set.InjOn (G.pathTreeProj u) ((G.pathTree u).neighborSet p) := by
  intro a ha a' ha' hva
  rw [SimpleGraph.mem_neighborSet, pathTree_adj] at ha ha'
  simp only [pathTreeProj_apply] at hva
  have child_new : ∀ {c : G.PathFrom u}, Grows p c → c.1 ∉ p.2.1.support := by
    rintro c ⟨he, hb⟩
    exact ((Walk.concat_isPath_iff he).mp (hb ▸ c.2.2)).2
  have parent_on : ∀ {c : G.PathFrom u}, Grows c p → c.1 ∈ p.2.1.support := by
    rintro c ⟨he, hb⟩
    have hpen : p.2.1.penultimate = c.1 := by rw [hb, Walk.penultimate_concat]
    have hmem : p.2.1.penultimate ∈ p.2.1.support := Walk.getVert_mem_support _ _
    exact hpen ▸ hmem
  rcases ha with hpa | hap <;> rcases ha' with hpa' | hap'
  · exact Grows.child_unique hpa hpa' hva
  · exact absurd (parent_on hap') (hva ▸ child_new hpa)
  · exact absurd (parent_on hap) (hva.symm ▸ child_new hpa')
  · exact Grows.parent_unique hap hap'

/-- **`Walk.map π` is injective on walks of the path tree** (with fixed endpoints): a walk of the
forest `T(G,v)` is recovered from its `G`-projection. By induction, each step's next vertex is a
neighbour of the current one, and `π` separates neighbours (`pathTreeProj_injOn_neighborSet`), so the
lift is forced — the injective half of the stone-1 bijection. -/
theorem pathTreeProj_walk_injective {v : V} : ∀ {x y : G.PathFrom v}
    (p p' : (G.pathTree v).Walk x y),
    p.map (G.pathTreeProj v) = p'.map (G.pathTreeProj v) → p = p' := by
  intro x y p
  induction p with
  | nil => intro p' h; cases p' <;> simp_all
  | @cons x w y hxw p ih =>
    intro p' h
    cases p' with
    | nil => simp at h
    | @cons _ w' _ hxw' p' =>
      simp only [Walk.map_cons, Walk.cons.injEq] at h
      obtain ⟨hsnd, htail⟩ := h
      have hww : w = w' :=
        pathTreeProj_injOn_neighborSet G v x
          (((G.pathTree v).mem_neighborSet x w).mpr hxw)
          (((G.pathTree v).mem_neighborSet x w').mpr hxw') hsnd
      subst hww
      rw [ih p' (eq_of_heq htail)]

/-! ## The `liftSeq`↔path invariant (image is tree-like + surjectivity of the lift)

`liftSeq` (the intrinsic tree-like test of `Ihara/PathTree.lean`) run on a projected path-tree walk
tracks the current tree-vertex's path. One step in `T(G,v)` — `Grows s y` (extend) or `Grows y s`
(retreat to parent) — mirrors exactly one `liftSeq` step (EXTEND push / RETREAT pop). -/

/-- **One path-tree step = one `liftSeq` step.** Walking `T(G,v)` from `s` to a neighbour `y`,
feeding `liftSeq` the next projected vertex `y.1` with stack `s`'s path-support turns the stack into
`y`'s path-support: an EXTEND when `y` is a child of `s` (fresh endpoint, push) and a RETREAT when `y`
is its parent (endpoint = penultimate, pop). -/
theorem liftSeq_step [DecidableEq V] {v : V} {s y : G.PathFrom v}
    (h : (G.pathTree v).Adj s y) (M : List V) :
    liftSeq (y.1 :: M) s.2.1.support = liftSeq M y.2.1.support := by
  rw [liftSeq_cons]
  rcases h with ⟨he, hb⟩ | ⟨he, hb⟩
  · -- Grows s y : EXTEND (y is a child of s; y.1 is fresh)
    have hnotin : y.1 ∉ s.2.1.support := ((Walk.concat_isPath_iff he).mp (hb ▸ y.2.2)).2
    rw [if_neg hnotin]
    congr 1
    rw [hb, Walk.support_concat]
  · -- Grows y s : RETREAT (s is a child of y; y.1 = penultimate of s)
    have hnnil : ¬ s.2.1.Nil := by
      rw [hb, Walk.nil_iff_length_eq, Walk.length_concat]; omega
    have hpenu : s.2.1.penultimate = y.1 := by rw [hb, Walk.penultimate_concat]
    have hmem : y.1 ∈ s.2.1.support := hpenu ▸ Walk.getVert_mem_support _ _
    rw [if_pos hmem]
    have hgl : s.2.1.support.dropLast.getLast? = some y.1 := by
      rw [s.2.1.support_dropLast_getLast?_eq_penultimate hnnil, hpenu]
    rw [if_pos hgl]
    congr 1
    rw [hb, Walk.support_concat, List.dropLast_concat]

/-- **The invariant.** Running `liftSeq` on the `G`-projection of a path-tree walk `W : s ⟶ x`,
started from `s`'s path-support, returns `x`'s path-support. Each tree step is one `liftSeq` step
(`liftSeq_step`), so the stack walks in lockstep with the current tree-vertex's path. -/
theorem liftSeq_map_invariant [DecidableEq V] {v : V} {s x : G.PathFrom v}
    (W : (G.pathTree v).Walk s x) :
    liftSeq (W.map (G.pathTreeProj v)).support.tail s.2.1.support = some x.2.1.support := by
  induction W with
  | nil => simp [liftSeq]
  | @cons s y x h rest ih =>
    rw [Walk.map_cons, Walk.support_cons, List.tail_cons,
      show (rest.map (G.pathTreeProj v)).support
          = y.1 :: (rest.map (G.pathTreeProj v)).support.tail from
        (Walk.cons_tail_support _).symm,
      liftSeq_step h]
    exact ih

/-- **Image is tree-like (down well-definedness).** The `G`-projection of any closed walk at the root
of `T(G,v)` is a tree-like closed walk at `v`: instantiate the invariant at `s = x = root`, whose
path-support is `[v]`, giving `liftSeq (W.map π).support.tail [v] = some [v]`, i.e. `IsTreeLike`. -/
theorem pathTreeProj_map_isTreeLike [DecidableEq V] {v : V}
    (W : (G.pathTree v).Walk (pathTreeRoot G v) (pathTreeRoot G v)) :
    (W.map (G.pathTreeProj v)).IsTreeLike := by
  have h := liftSeq_map_invariant W
  rwa [show (pathTreeRoot G v).2.1.support = [v] from rfl] at h

/-! ## Surjectivity of the lift (the last half of the stone-1 bijection)

Conversely, a `G`-walk that `liftSeq` accepts from a current tree-vertex `⟨a, pp⟩` lifts to a path-tree
walk projecting back to it. The hypothesis `liftSeq w.support.tail pp.support = some t` supplies, at
each step, exactly the EXTEND (fresh vertex → child) or RETREAT (penultimate → parent) decision, so
the lift is built by recursion with no failure branch. -/

/-- **Existence of the lift.** If `liftSeq` accepts the `G`-walk `w : a ⟶ b` started from the path
`pp : v ⟶ a` (current tree-vertex `⟨a, pp⟩`), returning final stack `t`, then `w` lifts to a path-tree
walk `W` from `⟨a, pp⟩` to a vertex `q` with `q`'s path-support `= t` whose projection has the same
support as `w`. (Support equality dodges the dependent endpoint; `support_injective` upgrades it to
walk equality once the endpoints are pinned, in the closed-walk corollary.) -/
theorem exists_lift [DecidableEq V] {v : V} {a b : V} (w : G.Walk a b) :
    ∀ (pp : G.Walk v a) (hpp : pp.IsPath) {t : List V},
      liftSeq w.support.tail pp.support = some t →
      ∃ (q : G.PathFrom v) (W : (G.pathTree v).Walk ⟨a, pp, hpp⟩ q),
        (W.map (G.pathTreeProj v)).support = w.support ∧ q.2.1.support = t := by
  induction w with
  | nil =>
    intro pp hpp t h
    simp only [Walk.support_nil, List.tail_nil, liftSeq] at h
    exact ⟨⟨_, pp, hpp⟩, Walk.nil, by simp, Option.some.inj h⟩
  | @cons a c b e w' ih =>
    intro pp hpp t h
    rw [Walk.support_cons, List.tail_cons,
      show w'.support = c :: w'.support.tail from (Walk.cons_tail_support _).symm,
      liftSeq_cons] at h
    by_cases hc : c ∈ pp.support
    · -- RETREAT: c is on pp; the lift retreats to the parent (dropLast)
      rw [if_pos hc] at h
      by_cases hpen : pp.support.dropLast.getLast? = some c
      · rw [if_pos hpen] at h
        have hnnil : ¬ pp.Nil := by
          rintro hn
          rw [Walk.nil_iff_support_eq.mp hn] at hpen; simp at hpen
        have hpenu : pp.penultimate = c :=
          Option.some.inj ((pp.support_dropLast_getLast?_eq_penultimate hnnil).symm.trans hpen)
        subst hpenu
        obtain ⟨q, W', hmap, hsupp⟩ := ih pp.dropLast (hpp.take (pp.length - 1))
          (by rwa [Walk.support_dropLast hnnil])
        exact ⟨q,
          Walk.cons (Or.inr ⟨pp.adj_penultimate hnnil, (Walk.concat_dropLast _).symm⟩) W',
          by rw [Walk.map_cons, Walk.support_cons, hmap, Walk.support_cons, pathTreeProj_apply], hsupp⟩
      · rw [if_neg hpen] at h; simp at h
    · -- EXTEND: c is fresh; the lift extends pp by the edge to c
      rw [if_neg hc] at h
      obtain ⟨q, W', hmap, hsupp⟩ := ih (pp.concat e) ((Walk.concat_isPath_iff e).mpr ⟨hpp, hc⟩)
        (by simpa [Walk.support_concat] using h)
      exact ⟨q, Walk.cons (Or.inl ⟨e, rfl⟩) W',
        by rw [Walk.map_cons, Walk.support_cons, hmap, Walk.support_cons, pathTreeProj_apply], hsupp⟩

/-- **Surjectivity of the projection onto tree-like walks.** Every closed tree-like walk of `G` at
`v` is the `π`-projection of a closed walk at the root of `T(G,v)`: lift it from the root path
(`exists_lift`), note the lift returns to the root (its final path-support is `[v]`), and upgrade the
support equality to walk equality via `support_injective`. -/
theorem exists_root_lift [DecidableEq V] {v : V} (w : G.Walk v v) (hw : w.IsTreeLike) :
    ∃ W : (G.pathTree v).Walk (pathTreeRoot G v) (pathTreeRoot G v),
      W.map (G.pathTreeProj v) = w := by
  obtain ⟨q, W, hsupp, hqsupp⟩ :=
    exists_lift w Walk.nil Walk.IsPath.nil (by simpa [Walk.IsTreeLike] using hw)
  have hq : q = pathTreeRoot G v := by
    obtain ⟨qv, qw, qhp⟩ := q
    have hnil : qw.Nil := Walk.nil_iff_support_eq.mpr hqsupp
    obtain rfl := hnil.eq
    obtain rfl := hnil.eq_nil
    rfl
  subst hq
  exact ⟨W, Walk.support_injective hsupp⟩

/-! ## The stone-1 count equality

Assembling the bijection: the number of closed tree-like walks of `G` at `v` of length `k` equals the
number of closed walks of length `k` at the root of the path tree `T(G,v)`. This is the matching-side
input `treeLikeWalkCount`-summand `= [A(T(G,v))ᵏ]_{root}` of Godsil's moment theorem. -/

/-- **Stone 1 (count form).** `#{closed tree-like walks of `G` at `v`, length `k`}` =
`#{closed walks at the root of `T(G,v)`, length `k`}`, via the bijection `W ↦ W.map π`
(injective `pathTreeProj_walk_injective`, image-is-tree-like `pathTreeProj_map_isTreeLike`,
surjective `exists_root_lift`). -/
theorem card_treeLike_eq_pathTreeWalks [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (k : ℕ) (v : V) :
    #((G.finsetWalkLength k v v).filter fun w => w.IsTreeLike)
      = #((G.pathTree v).finsetWalkLength k (pathTreeRoot G v) (pathTreeRoot G v)) := by
  refine (Finset.card_bij (fun W _ => W.map (G.pathTreeProj v)) ?_ ?_ ?_).symm
  · intro W hW
    rw [mem_finsetWalkLength_iff] at hW
    rw [Finset.mem_filter, mem_finsetWalkLength_iff]
    refine ⟨?_, pathTreeProj_map_isTreeLike W⟩
    show (W.map (G.pathTreeProj v)).length = k
    rw [Walk.length_map]; exact hW
  · intro W₁ _ W₂ _ heq
    exact pathTreeProj_walk_injective W₁ W₂ heq
  · intro w hw
    rw [Finset.mem_filter, mem_finsetWalkLength_iff] at hw
    obtain ⟨W, hWeq⟩ := exists_root_lift w hw.2
    refine ⟨W, ?_, hWeq⟩
    rw [mem_finsetWalkLength_iff, ← Walk.length_map (G.pathTreeProj v) W, hWeq]
    exact hw.1

/-- **Stone 1 → linear algebra.** Godsil's tree-like walk count is the sum, over base vertices `v`,
of the root–root entry of the `k`-th power of the path tree's adjacency matrix:

  `treeLikeWalkCount G k = ∑_v [A(T(G,v))ᵏ]_{root,root}`.

Combines `card_treeLike_eq_pathTreeWalks` (the stone-1 bijection) with
`adjMatrix_pow_apply_eq_card_walk` (matrix powers count walks). This is the matching side of the
trace-formula bridge expressed spectrally on each path tree — the entry point to the resolvent /
Newton stones (`[A(T)ᵏ]_root` = the `k`-th moment coefficient of `μ(T−root)/μ(T)`). -/
theorem treeLikeWalkCount_eq_sum_pathTree_adjMatrix_pow
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (k : ℕ) :
    G.treeLikeWalkCount k
      = ∑ v : V, ((G.pathTree v).adjMatrix ℕ ^ k) (pathTreeRoot G v) (pathTreeRoot G v) := by
  rw [treeLikeWalkCount]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [card_treeLike_eq_pathTreeWalks, adjMatrix_pow_apply_eq_card_walk, Nat.cast_id,
    card_set_walk_length_eq]

/-- **The path tree is a forest, so its matching polynomial is the characteristic polynomial** of its
adjacency matrix (`matchingPoly_forest_eq_charpoly` at `pathTree_isAcyclic`). This identifies the
spectral object `charpoly(A(T(G,v)))` — whose `(root,root)` resolvent generates `[A(T)ᵏ]_root` — with
the matching polynomial `μ(T(G,v))` that enters Godsil's ratio identity `μ(T−root)/μ(T) =
μ(G−v)/μ(G)`. The hinge between the linear-algebra side (stone 3) and the matching-polynomial side
(stone 2 = `godsil_identity`). -/
theorem matchingPoly_pathTree_eq_charpoly [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    (G.pathTree v).matchingPoly = ((G.pathTree v).adjMatrix ℝ).charpoly :=
  matchingPoly_forest_eq_charpoly (G.pathTree v) (pathTree_isAcyclic G v)

/-- **Stone 2 in resolvent (charpoly) form.** Substituting the forest bridge
`μ(forest) = charpoly(adjacency)` into Godsil's identity `godsil_identity`
(`μ(G)·μ(T−r) = μ(G−u)·μ(T)`, the matching↔path-tree ratio, MSS/Divisibility) turns the
matching-polynomial ratio into the **spectral** one:

  `charpoly(A(T(G,u)−r)) · μ(G) = charpoly(A(T(G,u))) · μ(G−u)`,

i.e. the path tree's root–root resolvent `charpoly(T−r)/charpoly(T)` equals the graph ratio
`μ(G−u)/μ(G)`. (`T−r` and `G−u` are the incidence-isolated forms `deleteIncidenceSet`, so both
sides carry the same isolated-vertex factor `X`.) This is the exact spectral input that the
generating-function step (Stone 3) consumes — the diagonal resolvent
`Σ_k [A(T)ᵏ]_root z^k = charpoly(T−r)/charpoly(T)` is now pinned to `μ(G−u)/μ(G)`, which the
vertex-deletion law `sum_matchingPoly_deleteIncidenceSet` sums (over `u`) to `μ'(G)/μ(G)`.
Both forest bridges are sound: `T` is acyclic (`pathTree_isAcyclic`) and `T−r ≤ T` stays acyclic
(`IsAcyclic.anti`). -/
theorem godsil_resolvent_charpoly_form [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (u : V) :
    (((G.pathTree u).deleteIncidenceSet (pathTreeRoot G u)).adjMatrix ℝ).charpoly * G.matchingPoly
      = ((G.pathTree u).adjMatrix ℝ).charpoly * (G.deleteIncidenceSet u).matchingPoly := by
  have hT : (G.pathTree u).matchingPoly = ((G.pathTree u).adjMatrix ℝ).charpoly :=
    matchingPoly_pathTree_eq_charpoly G u
  have hTr : ((G.pathTree u).deleteIncidenceSet (pathTreeRoot G u)).matchingPoly
      = (((G.pathTree u).deleteIncidenceSet (pathTreeRoot G u)).adjMatrix ℝ).charpoly :=
    matchingPoly_forest_eq_charpoly _
      ((pathTree_isAcyclic G u).anti ((G.pathTree u).deleteIncidenceSet_le (pathTreeRoot G u)))
  have hgod := godsil_identity G u
  unfold godsil_identity_target at hgod
  rw [hT, hTr] at hgod
  linear_combination hgod

end SimpleGraph
