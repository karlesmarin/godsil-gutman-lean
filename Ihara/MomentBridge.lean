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

end SimpleGraph
