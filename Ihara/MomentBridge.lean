/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Ihara.TreeLikeWalks
import MSS.PathTree

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

end SimpleGraph
