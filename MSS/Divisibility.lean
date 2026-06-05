/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import MatchingPoly
public import MSS.MatchingSum
public import MSS.PathTree
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-!
# Godsil's path-tree divisibility `μ(G) ∣ μ(T(G,u))` — targets and proof route

Godsil's theorem (*Matchings and walks in graphs*, J. Graph Theory 5 (1981) 285–297):
for every graph `G` and vertex `u`, the matching polynomial `μ(G)` **divides** the matching
polynomial of the path tree `μ(T(G,u))`. Since `T(G,u)` is a forest (`pathTree_isAcyclic`),
`μ(T(G,u))` is the characteristic polynomial of a symmetric matrix — real-rooted — so `μ(G)`
is real-rooted too, and its roots inherit the tree spectral bound `2√(Δ−1)` (Heilmann–Lieb).
**No proof assistant has Godsil's divisibility or Heilmann–Lieb** (verified 2026-06-03).

## The classical proof (induction on `|V(G)|`) and what is already in hand

```
  (★)  μ(G)·μ(T−r) = μ(G−a)·μ(T)                    [Godsil's identity]
  (D)  T(G,u) − r  ≅  ⊔_{b∼u} T(G−u, b)             [root decomposition]
       ⟹  μ(T−r) = ∏_{b∼u} μ(T(G−u,b))              [via `matchingPoly_sum`, PROVEN]
  IH:  for b ∼ u,  μ(G−u) ∣ μ(T(G−u,b))             [induction, |V(G−u)| < |V(G)|]
       ⟹  μ(G−u) ∣ μ(T−r)                            [divides one factor of the product]
  (★)+IH+`dvd_of_godsil_identity`  ⟹  μ(G) ∣ μ(T)    [PROVEN algebraic core]
```

* **Engine — PROVEN** (`MatchingPoly.matchingPoly_recurrence`): the signed vertex-deletion
  recurrence `X²·μ(G) = X²·μ(G−v) − Σ_{u∼v} μ(G−v−u)`. Godsil's identity `(★)` is obtained
  by applying this recurrence on both `G` (at `u`) and on the tree `T` (at its root `r`),
  then matching the two expansions through the root decomposition `(D)`.
* **Product step — PROVEN** (`MatchingSum.matchingPoly_sum`): `μ(G ⊕ H) = μ(G)·μ(H)`, the
  binary case of the product `μ(T−r) = ∏ μ(T(G−u,b))` once `(D)` is established.
* **Algebraic core — PROVEN** (`MatchingPoly.dvd_of_godsil_identity`): from `(★)` plus the
  inductive `μ(G−u) ∣ μ(T−r)` (and `μ(G−u) ≠ 0`, which holds as `μ` is monic), conclude
  `μ(G) ∣ μ(T)`.
* **Forest object — PROVEN** (`PathTree.pathTree_isAcyclic`).

## What remains (the two graph-combinatorial lemmas)

1. **Root decomposition `(D)`**: a `SimpleGraph` isomorphism
   `(G.pathTree u).deleteIncidenceSet (pathTreeRoot G u) ≅ ⊔_{b∼u} (G−u).pathTree b`
   (the subtree hanging from each child `(u,b)` of the root is the path tree of `G−u` rooted
   at `b`), lifted to `μ` via `matchingPoly_sum` (indexed form).
2. **Godsil's identity `(★)`** as a theorem, from `matchingPoly_recurrence` applied at `u`
   and at the tree root, glued by `(D)`.

These two close the induction. The remaining infrastructure friction is a `Fintype`
instance for `G.PathFrom u` (paths of a finite graph), needed to *evaluate* `μ(T(G,u))`;
the targets below carry it as an explicit hypothesis so the goals typecheck independently.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The root decomposition `T(G,u) − r ≅ ⊔_{b∼u} T(G−u,b)`: the inverse `dropRoot` -/

/-- The tail of a non-root path of `T(G,u)` has all its edges in `G−u` (it avoids `u`). -/
theorem dropRoot_aux {G : SimpleGraph V} {u : V} (p : G.PathFrom u) (hp : ¬ p.2.1.Nil) :
    ∀ e, e ∈ p.2.1.tail.edges → e ∈ (G.deleteIncidenceSet u).edgeSet := by
  intro e he
  rw [SimpleGraph.mem_edgeSet_deleteIncidenceSet]
  refine ⟨p.2.1.tail.edges_subset_edgeSet he, fun hu => ?_⟩
  have hns : u ∉ p.2.1.tail.support := by
    have hnd := p.2.2.support_nodup
    rw [← Walk.cons_support_tail hp, List.nodup_cons] at hnd
    exact hnd.1
  exact hns (Walk.mem_support_of_mem_edges he hu)

/-- **Inverse of `prependRoot`.** Drop the root edge from a non-root path of `T(G,u)`: its
`Walk.tail` is a path of `G−u` from the second vertex (the tail avoids `u`, which appears only
at the head of the original path, so every tail edge survives in `G−u`). -/
def dropRoot {G : SimpleGraph V} {u : V} (p : G.PathFrom u) (hp : ¬ p.2.1.Nil) :
    (G.deleteIncidenceSet u).PathFrom p.2.1.snd :=
  ⟨p.1, (p.2.1.tail).transfer _ (dropRoot_aux p hp), (p.2.2.tail).transfer (dropRoot_aux p hp)⟩

/-- `mapLe` of a `transfer` into the supergraph is the identity walk (both `= transfer` into
that graph, via `transfer_eq_map_ofLE` + `transfer_transfer` + `transfer_self`). -/
theorem mapLe_transfer_self {G H : SimpleGraph V} (hle : H ≤ G) {a b : V}
    (w : G.Walk a b) (h : ∀ e ∈ w.edges, e ∈ H.edgeSet) :
    (w.transfer H h).mapLe hle = w := by
  show (w.transfer H h).map (Hom.ofLE hle) = w
  rw [← Walk.transfer_eq_map_ofLE (hp := fun e he =>
        SimpleGraph.edgeSet_mono hle (by rw [Walk.edges_transfer] at he; exact h e he)),
      Walk.transfer_transfer, Walk.transfer_self]

/-- `prependRoot ∘ dropRoot = id`: re-attaching the root edge recovers the original path. -/
theorem prependRoot_dropRoot {G : SimpleGraph V} {u : V} (p : G.PathFrom u)
    (hp : ¬ p.2.1.Nil) :
    prependRoot G (p.2.1.adj_snd hp) (dropRoot p hp) = p := by
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
  show Walk.cons (p.2.1.adj_snd hp)
    ((p.2.1.tail.transfer _ (dropRoot_aux p hp)).mapLe (G.deleteIncidenceSet_le u)) = p.2.1
  rw [mapLe_transfer_self (G.deleteIncidenceSet_le u) p.2.1.tail (dropRoot_aux p hp),
      Walk.cons_tail_eq p.2.1 hp]

/-- An image of `prependRoot` is never the root (it starts with the root edge). -/
theorem prependRoot_not_nil {G : SimpleGraph V} {u b : V} (hub : G.Adj u b)
    (q : (G.deleteIncidenceSet u).PathFrom b) : ¬ (prependRoot G hub q).2.1.Nil :=
  Walk.not_nil_cons

/-- A path of `T(G,u)` whose walk is `Nil` is the root. -/
theorem pathFrom_eq_root_of_nil {G : SimpleGraph V} {u : V} (p : G.PathFrom u)
    (hp : p.2.1.Nil) : p = pathTreeRoot G u := by
  obtain ⟨v, w, hw⟩ := p
  cases w with
  | nil => rfl
  | cons _ _ => exact absurd hp Walk.not_nil_cons

/-- The second vertex of `prependRoot G hub q` is `b` (the root edge's far end). -/
@[simp] theorem prependRoot_snd {G : SimpleGraph V} {u b : V} (hub : G.Adj u b)
    (q : (G.deleteIncidenceSet u).PathFrom b) : (prependRoot G hub q).2.1.snd = b :=
  Walk.snd_cons _ hub

/-- **`prependRoot` is injective even across the far endpoint** (`HEq`). Equal images force
equal second vertices (`prependRoot_snd`), and once those are identified (`b₁`, `b₂` are free
here, so `subst` works — this is what dissolves the `b ∈ snd` circularity), it is the ordinary
injectivity of `prependRoot` (the root-edge proof is irrelevant). -/
theorem prependRoot_heq_inj {G : SimpleGraph V} {u b₁ b₂ : V} (h₁ : G.Adj u b₁) (h₂ : G.Adj u b₂)
    {x : (G.deleteIncidenceSet u).PathFrom b₁} {y : (G.deleteIncidenceSet u).PathFrom b₂}
    (h : prependRoot G h₁ x = prependRoot G h₂ y) : HEq x y := by
  have hsnd : b₁ = b₂ := by simpa using congrArg (fun p => p.2.1.snd) h
  subst hsnd
  rw [Subsingleton.elim h₂ h₁] at h
  exact heq_of_eq (prependRoot_injective G h₁ h)

/-- `dropRoot ∘ prependRoot = id` (the second round-trip, `HEq`): `prependRoot_dropRoot`
re-attaches the dropped root edge to give back `prependRoot q`, and `prependRoot_heq_inj`
cancels the outer `prependRoot`. -/
theorem dropRoot_prependRoot {G : SimpleGraph V} {u b : V} (hub : G.Adj u b)
    (q : (G.deleteIncidenceSet u).PathFrom b) :
    HEq (dropRoot (prependRoot G hub q) (prependRoot_not_nil hub q)) q :=
  prependRoot_heq_inj _ hub
    (prependRoot_dropRoot (prependRoot G hub q) (prependRoot_not_nil hub q))



/-- The walk underlying `prependRoot` (definitionally a `cons` of the root edge). -/
theorem prependRoot_walk {G : SimpleGraph V} {u b : V} (hub : G.Adj u b)
    (q : (G.deleteIncidenceSet u).PathFrom b) :
    (prependRoot G hub q).2.1 = Walk.cons hub (q.2.1.mapLe (G.deleteIncidenceSet_le u)) := rfl

/-- `Grows` preserves the second vertex: if `b` extends `a` (non-root) by one edge at the
end, they share the same first step. -/
theorem Grows_snd_eq {G : SimpleGraph V} {u : V} {a b : G.PathFrom u} (h : Grows a b)
    (ha : ¬ a.2.1.Nil) : a.2.1.snd = b.2.1.snd := by
  obtain ⟨v, w, hwp⟩ := a
  obtain ⟨he, hw⟩ := h
  rw [hw]
  cases w with
  | nil => exact absurd Walk.nil_nil ha
  | cons h' w' => rw [Walk.concat_cons, Walk.snd_cons, Walk.snd_cons]

/-- **Per-fibre adjacency of the path tree under `prependRoot`.** Two branch paths are
adjacent in `T(G,u)` iff they sit in the same fibre and are adjacent in `T(G−u, b)` —
i.e. exactly the adjacency of the indexed disjoint union. Same trick as `prependRoot_heq_inj`:
`b₁`, `b₂` are FREE, so the same-fibre case `subst`s cleanly (`prependRoot_grows`), and the
cross-fibre case is impossible (`Grows` preserves the second vertex, `snd_cons`). -/
theorem pathTree_adj_prependRoot {G : SimpleGraph V} {u b₁ b₂ : V}
    (h₁ : G.Adj u b₁) (h₂ : G.Adj u b₂) (x : (G.deleteIncidenceSet u).PathFrom b₁)
    (y : (G.deleteIncidenceSet u).PathFrom b₂) :
    (G.pathTree u).Adj (prependRoot G h₁ x) (prependRoot G h₂ y) ↔
      (sigmaFamily fun b : {b : V // G.Adj u b} => (G.deleteIncidenceSet u).pathTree b.val).Adj
        ⟨⟨b₁, h₁⟩, x⟩ ⟨⟨b₂, h₂⟩, y⟩ := by
  by_cases hb : b₁ = b₂
  · subst hb
    rw [Subsingleton.elim h₂ h₁, pathTree_adj, prependRoot_grows, prependRoot_grows,
        sigmaFamily_adj, pathTree_adj]
  · constructor
    · intro hadj
      exfalso; apply hb
      rw [pathTree_adj] at hadj
      rw [← prependRoot_snd h₁ x, ← prependRoot_snd h₂ y]
      rcases hadj with hg | hg
      · exact Grows_snd_eq hg (prependRoot_not_nil h₁ x)
      · exact (Grows_snd_eq hg (prependRoot_not_nil h₂ y)).symm
    · exact fun hadj => absurd hadj
        (sigmaFamily_not_adj_of_fst_ne _ fun h => hb (congrArg Subtype.val h))

open Classical in
/-- **Root-decomposition vertex equivalence.** A path of `T(G,u)` is either the root or a
path `u`-prepended to a path of `G−u` from a neighbour `b`. So
`PathFrom G u ≃ Unit ⊕ Σ b:{b // u∼b}, PathFrom (G−u) b`. Forward = case on `Nil`
(root ↦ `inl`, else ↦ `dropRoot`); inverse = root / `prependRoot`. The two round-trips
`prependRoot_dropRoot` (Eq) and `dropRoot_prependRoot` (HEq) supply the inverses. -/
noncomputable def rootDecompEquiv (G : SimpleGraph V) (u : V) :
    G.PathFrom u ≃ Unit ⊕ Σ b : {b : V // G.Adj u b}, (G.deleteIncidenceSet u).PathFrom b.val where
  toFun p := if h : p.2.1.Nil then Sum.inl () else
    Sum.inr ⟨⟨p.2.1.snd, p.2.1.adj_snd h⟩, dropRoot p h⟩
  invFun x := x.elim (fun _ => pathTreeRoot G u) (fun b => prependRoot G b.1.2 b.2)
  left_inv p := by
    by_cases h : p.2.1.Nil
    · simp only [h, dif_pos]; exact (pathFrom_eq_root_of_nil p h).symm
    · simp only [h, dif_neg, Sum.elim_inr]; exact prependRoot_dropRoot p h
  right_inv x := by
    rcases x with ⟨⟩ | ⟨b, q⟩
    · exact dif_pos Walk.nil_nil
    · simp only [Sum.elim_inr, dif_neg (prependRoot_not_nil b.2 q), Sum.inr.injEq]
      exact Sigma.ext (Subtype.ext (prependRoot_snd b.2 q)) (dropRoot_prependRoot b.2 q)

open Classical in
/-- **Root-decomposition graph isomorphism.** `T(G,u) − r ≃g (⊥ on the root) ⊕ ⊔_{b∼u}
T(G−u,b)`. The vertex part is `rootDecompEquiv`; adjacency: the root is isolated (in
`deleteIncidenceSet` and in `⊥ Unit` / across the sum), and branch adjacency is exactly
`pathTree_adj_prependRoot`. -/
noncomputable def rootDecompIso (G : SimpleGraph V) (u : V) :
    (G.pathTree u).deleteIncidenceSet (pathTreeRoot G u) ≃g
      (⊥ : SimpleGraph Unit).sum
        (sigmaFamily fun b : {b : V // G.Adj u b} => (G.deleteIncidenceSet u).pathTree b.val) where
  toEquiv := rootDecompEquiv G u
  map_rel_iff' := by
    intro p p'
    by_cases hp : p.2.1.Nil
    · refine iff_of_false ?_ (fun hadj =>
        (SimpleGraph.deleteIncidenceSet_adj.mp hadj).2.1 (pathFrom_eq_root_of_nil p hp))
      rw [show rootDecompEquiv G u p = Sum.inl () from dif_pos hp]
      rintro hadj
      cases h : rootDecompEquiv G u p' <;> rw [h] at hadj <;> simp_all [SimpleGraph.sum]
    · by_cases hp' : p'.2.1.Nil
      · refine iff_of_false ?_ (fun hadj =>
          (SimpleGraph.deleteIncidenceSet_adj.mp hadj).2.2 (pathFrom_eq_root_of_nil p' hp'))
        rw [show rootDecompEquiv G u p' = Sum.inl () from dif_pos hp']
        rintro hadj
        cases h : rootDecompEquiv G u p <;> rw [h] at hadj <;> simp_all [SimpleGraph.sum]
      · rw [show rootDecompEquiv G u p =
              Sum.inr ⟨⟨p.2.1.snd, p.2.1.adj_snd hp⟩, dropRoot p hp⟩ from dif_neg hp,
            show rootDecompEquiv G u p' =
              Sum.inr ⟨⟨p'.2.1.snd, p'.2.1.adj_snd hp'⟩, dropRoot p' hp'⟩ from dif_neg hp']
        show (sigmaFamily _).Adj _ _ ↔ _
        rw [← pathTree_adj_prependRoot, prependRoot_dropRoot p hp, prependRoot_dropRoot p' hp',
            SimpleGraph.deleteIncidenceSet_adj]
        refine ⟨fun h => ⟨h, fun hr => hp (hr ▸ Walk.nil_nil), fun hr => hp' (hr ▸ Walk.nil_nil)⟩,
          fun h => h.1⟩

set_option maxHeartbeats 4000000 in
open Classical in
/-- `μ` of `(⊥ on a point) ⊕ ⊔_i H_i` is `X · ∏_i μ(H_i)`. Proved in a clean context (no
graph iso), so `matchingPoly_sigmaFamily` applies on the *direct* `Σ`-`Fintype` with no
instance diamond. -/
theorem matchingPoly_bot_sum_sigmaFamily {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] (H : ∀ i, SimpleGraph (β i)) :
    ((⊥ : SimpleGraph Unit).sum (sigmaFamily H)).matchingPoly
      = Polynomial.X * ∏ i, (H i).matchingPoly := by
  rw [matchingPoly_sum]
  congr 1
  · rw [matchingPoly_bot]; simp
  · exact matchingPoly_sigmaFamily H

set_option maxHeartbeats 4000000 in
open Classical in
/-- `μ` of `(⊥ on a point) ⊕ ⊔_i H_i` with one fibre-`b` vertex `⟨b,y⟩` deleted is
`X · μ(H_b − y) · ∏_{i≠b} μ(H_i)`. Clean context (no graph iso): `sumDeleteIncidenceSetInr`
isolates the right summand, `sigmaFamilyDelete` replaces the `b`-fibre by `H_b − y`, and
`matchingPoly_sigmaFamily` + `prod_update` evaluate the product. The evaluation half of the
`(★)` sub-decomposition `μ(T−r−c_b) = X·μ(T_b−r_b)·∏_{b'≠b} μ(T_b')`. -/
theorem matchingPoly_bot_sum_sigmaFamily_delete {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (H : ∀ i, SimpleGraph (β i)) (b : ι) (y : β b) :
    (((⊥ : SimpleGraph Unit).sum (sigmaFamily H)).deleteIncidenceSet (Sum.inr ⟨b, y⟩)).matchingPoly
      = Polynomial.X * ((H b).deleteIncidenceSet y).matchingPoly
        * ∏ i ∈ Finset.univ.erase b, (H i).matchingPoly := by
  have hprod : (∏ i, ((Function.update H b ((H b).deleteIncidenceSet y)) i).matchingPoly)
      = ((H b).deleteIncidenceSet y).matchingPoly
        * ∏ i ∈ Finset.univ.erase b, (H i).matchingPoly := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b), Function.update_self]
    refine congrArg₂ (· * ·) (matchingPoly_inst_irrel _ _ _ _ _)
      (Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
  rw [matchingPoly_iso (sumDeleteIncidenceSetInr _ _ _), matchingPoly_sum, matchingPoly_bot,
      Fintype.card_unit, pow_one, matchingPoly_iso (sigmaFamilyDeleteIncidenceSet H b y),
      matchingPoly_sigmaFamily, hprod, ← mul_assoc]

set_option maxHeartbeats 1000000 in
open Classical in
/-- **(D) — the root-decomposition matching-polynomial identity.**
`μ(T(G,u) − r) = X · ∏_{b∼u} μ(T(G−u, b))`. Chains the two proven halves —
`matchingPoly_iso (rootDecompIso G u) : μ(T−r) = μ[(⊥)⊕⊔_b T(G−u,b)]` (the graph iso) and
`matchingPoly_bot_sum_sigmaFamily : μ[(⊥)⊕⊔_b H_b] = X·∏ μ(H_b)` (the evaluation). `convert`
matches the two structurally up to depth 2 and discharges the leftover `Fintype`/`Decidable`
instance mismatches (the `Σ`-type diamond) via `Subsingleton.elim` — sidestepping the
`whnf`-reduction of `μ` over the `Σ`-type that blows the heartbeat budget on a direct chain. -/
theorem matchingPoly_pathTree_deleteRoot (G : SimpleGraph V) (u : V)
    [Fintype (G.PathFrom u)]
    [∀ b : {b : V // G.Adj u b}, Fintype ((G.deleteIncidenceSet u).PathFrom b.val)] :
    ((G.pathTree u).deleteIncidenceSet (pathTreeRoot G u)).matchingPoly =
      Polynomial.X *
        ∏ b : {b : V // G.Adj u b}, ((G.deleteIncidenceSet u).pathTree b.val).matchingPoly := by
  rw [matchingPoly_iso (rootDecompIso G u)]
  convert matchingPoly_bot_sum_sigmaFamily (ι := {b : V // G.Adj u b})
    (fun b => (G.deleteIncidenceSet u).pathTree b.val) using 2

/-! ### Piece 2 of `(★)`: the root's neighbours are the children `prependRoot` of `b ∼ u` -/

/-- **A path is adjacent to the root iff it is a single edge `u → b`.** `Grows c r` is
impossible (a `concat` is never `nil`), so the only neighbours of `r` are the length-one paths,
i.e. `prependRoot` of the trivial path of `G−u` at a neighbour `b ∼ u`. The index `b` is kept
free (not `c.1`) so the backward direction can `subst`. -/
theorem pathTree_root_adj_iff (G : SimpleGraph V) (u : V) (c : G.PathFrom u) :
    (G.pathTree u).Adj (pathTreeRoot G u) c
      ↔ ∃ (b : V) (h : G.Adj u b),
          c = prependRoot G h (pathTreeRoot (G.deleteIncidenceSet u) b) := by
  rw [pathTree_adj]
  constructor
  · rintro (⟨he, hc⟩ | ⟨he, hc⟩)
    · refine ⟨c.1, he, Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))⟩
      rw [hc]; simp [prependRoot, pathTreeRoot, Walk.map_nil, Walk.concat]
    · exact absurd (congrArg Walk.length hc) (by
        simp [pathTreeRoot, Walk.length_concat])
  · rintro ⟨b, h, rfl⟩
    exact Or.inl ⟨h, by simp [prependRoot, pathTreeRoot, Walk.map_nil, Walk.concat]⟩

/-- The child map `b ↦ (u → b)` is injective: the path's endpoint recovers `b`. -/
theorem prependRoot_root_injective (G : SimpleGraph V) (u : V) :
    Function.Injective (fun b : {b : V // G.Adj u b} =>
      prependRoot G b.2 (pathTreeRoot (G.deleteIncidenceSet u) b.val)) := by
  intro b b' h
  exact Subtype.ext (by simpa [prependRoot, pathTreeRoot] using congrArg Sigma.fst h)

open Classical in
/-- **The root's neighbour set is the image of `b ∼ u` under the child embedding.** -/
theorem pathTreeRoot_neighborFinset (G : SimpleGraph V) (u : V) [Fintype (G.PathFrom u)]
    [DecidableRel (G.pathTree u).Adj] :
    (G.pathTree u).neighborFinset (pathTreeRoot G u)
      = Finset.univ.image (fun b : {b : V // G.Adj u b} =>
          prependRoot G b.2 (pathTreeRoot (G.deleteIncidenceSet u) b.val)) := by
  ext c
  simp only [mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
  rw [pathTree_root_adj_iff]
  constructor
  · rintro ⟨b, h, rfl⟩; exact ⟨⟨b, h⟩, rfl⟩
  · rintro ⟨b, rfl⟩; exact ⟨b.val, b.2, rfl⟩

open Classical in
/-- **Reindex a sum over the root's neighbours by `b ∼ u`** (the form the tree recurrence
needs in `(★)`). -/
theorem sum_root_neighbors {M : Type*} [AddCommMonoid M] (G : SimpleGraph V) (u : V)
    [Fintype (G.PathFrom u)] [DecidableRel (G.pathTree u).Adj] (F : G.PathFrom u → M) :
    ∑ c ∈ (G.pathTree u).neighborFinset (pathTreeRoot G u), F c
      = ∑ b : {b : V // G.Adj u b},
          F (prependRoot G b.2 (pathTreeRoot (G.deleteIncidenceSet u) b.val)) := by
  rw [pathTreeRoot_neighborFinset,
      Finset.sum_image fun b _ b' _ h => prependRoot_root_injective G u h]

open Classical in
/-- **(★) sub-decomposition (TARGET — blocked by a Lean `whnf` performance wall).**
`μ(T(G,u) − r − c_b) = X · μ(T(G−u,b) − r_b) · ∏_{b'≠b} μ(T(G−u,b'))` for the child
`c_b = prependRoot G b.2 r_b = (u → b)`. The math is settled: `c_b ↦ inr ⟨b, r_b⟩` under
`rootDecompEquiv`, and `matchingPoly_bot_sum_sigmaFamily_delete` (proven) evaluates the image.
The gap is transporting `μ` across `(rootDecompIso).deleteIncidenceSet c_b`:
`matchingPoly_iso`/`matchingNumber_iso` of the **doubly-deleted** `Σ`-of-paths graph blows the
`whnf`/`isDefEq` budget. RESISTS every tactic-level fix tried (1M/4M/16M heartbeats; the
simple-codomain `▸`; the general wrapper `matchingPoly_deleteIncidenceSet_iso`; the Socratic
free-vertex abstraction). Unlike the `HEq` wall (logical), this is pure elaboration cost: passing
the complex iso `rootDecompIso` to the transport triggers it regardless. Fix needs either a
`whnf`-free reproof of `matchingNumber_iso`, or the Herglotz/`u = 1/R` route (avoids the path
tree entirely). -/
def matchingPoly_pathTree_deleteRoot_child_target (G : SimpleGraph V) (u : V)
    [Fintype (G.PathFrom u)]
    [∀ b : {b : V // G.Adj u b}, Fintype ((G.deleteIncidenceSet u).PathFrom b.val)]
    (b : {b : V // G.Adj u b}) : Prop :=
  (((G.pathTree u).deleteIncidenceSet (pathTreeRoot G u)).deleteIncidenceSet
      (prependRoot G b.2 (pathTreeRoot (G.deleteIncidenceSet u) b.val))).matchingPoly
    = Polynomial.X
      * (((G.deleteIncidenceSet u).pathTree b.val).deleteIncidenceSet
          (pathTreeRoot (G.deleteIncidenceSet u) b.val)).matchingPoly
      * ∏ b' ∈ Finset.univ.erase b,
          ((G.deleteIncidenceSet u).pathTree b'.val).matchingPoly

set_option maxHeartbeats 4000000 in
open Classical in
/-- **(★) sub-decomposition — PROVEN** (the formerly `whnf`-blocked `child_target`). The vertex
`c_b = prependRoot G b.2 r_b` maps under `rootDecompIso` to `Sum.inr ⟨b, r_b⟩` — this is exactly
`rootDecompEquiv`'s `apply_symm_apply` (since `rootDecompEquiv.symm (inr ⟨b,r_b⟩) = prependRoot …`
by `rfl`). The general transport `matchingPoly_deleteIncidenceSet_iso (rootDecompIso G u) c_b`
moves `μ` to the `(⊥)⊕sigmaFamily` side. The KEY to dodge the `whnf` wall: do NOT *cite*
`matchingPoly_bot_sum_sigmaFamily_delete` (that forces unifying the transport-produced `Σ`-graph
with the lemma's `Σ`-graph — a `whnf` loop over the path `Fintype`). Instead INLINE its proof
(`sumDeleteIncidenceSetInr` → `sigmaFamilyDeleteIncidenceSet` → `matchingPoly_sigmaFamily`),
rewriting the goal's *own* graph term in place — no second graph, no unification. -/
theorem matchingPoly_pathTree_deleteRoot_child (G : SimpleGraph V) (u : V)
    [Fintype (G.PathFrom u)]
    [∀ b : {b : V // G.Adj u b}, Fintype ((G.deleteIncidenceSet u).PathFrom b.val)]
    (b : {b : V // G.Adj u b}) :
    matchingPoly_pathTree_deleteRoot_child_target G u b := by
  unfold matchingPoly_pathTree_deleteRoot_child_target
  have hmap : (rootDecompIso G u)
        (prependRoot G b.2 (pathTreeRoot (G.deleteIncidenceSet u) b.val))
      = Sum.inr ⟨b, pathTreeRoot (G.deleteIncidenceSet u) b.val⟩ := by
    show (rootDecompEquiv G u)
        (prependRoot G b.2 (pathTreeRoot (G.deleteIncidenceSet u) b.val)) = _
    exact (rootDecompEquiv G u).apply_symm_apply
      (Sum.inr ⟨b, pathTreeRoot (G.deleteIncidenceSet u) b.val⟩)
  have hprod : (∏ i : {b : V // G.Adj u b},
        (Function.update (fun b : {b : V // G.Adj u b} => (G.deleteIncidenceSet u).pathTree b.val) b
          (((G.deleteIncidenceSet u).pathTree b.val).deleteIncidenceSet
            (pathTreeRoot (G.deleteIncidenceSet u) b.val)) i).matchingPoly)
      = (((G.deleteIncidenceSet u).pathTree b.val).deleteIncidenceSet
          (pathTreeRoot (G.deleteIncidenceSet u) b.val)).matchingPoly
        * ∏ i ∈ Finset.univ.erase b, ((G.deleteIncidenceSet u).pathTree i.val).matchingPoly := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b), Function.update_self]
    refine congrArg₂ (· * ·) (matchingPoly_inst_irrel _ _ _ _ _)
      (Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
  have iso2 : (((G.pathTree u).deleteIncidenceSet (pathTreeRoot G u)).deleteIncidenceSet
        (prependRoot G b.2 (pathTreeRoot (G.deleteIncidenceSet u) b.val)))
      ≃g ((⊥ : SimpleGraph Unit).sum
            (sigmaFamily fun b : {b : V // G.Adj u b} =>
              (G.deleteIncidenceSet u).pathTree b.val)).deleteIncidenceSet
          (Sum.inr ⟨b, pathTreeRoot (G.deleteIncidenceSet u) b.val⟩) :=
    hmap ▸ Iso.deleteIncidenceSet (rootDecompIso G u)
      (prependRoot G b.2 (pathTreeRoot (G.deleteIncidenceSet u) b.val))
  rw [matchingPoly_iso iso2, matchingPoly_iso (sumDeleteIncidenceSetInr _ _ _),
      matchingPoly_sum, matchingPoly_bot, Fintype.card_unit, pow_one,
      matchingPoly_iso (sigmaFamilyDeleteIncidenceSet _ b _),
      matchingPoly_sigmaFamily, hprod, ← mul_assoc]

set_option maxHeartbeats 800000 in
open Classical in
/-- **Godsil's identity — the inductive step `(★)`.** Given the identity on `G−u` at every
neighbour `b` (the IH), it holds for `G` at `u`. Cancel `X²` (a non-zero-divisor); expand the
vertex-deletion recurrence at `u` in `G` and at the root `r` in the tree `T`; feed the root
decomposition `(D)` `μ(T−r)=X·∏ μ(T_b)`, the sub-decomposition of each tree-recurrence defect
term `μ(T−r−c_b)=X·μ(T_b−r_b)·∏_{b'≠b}μ(T_b')`, and the `Σ/∏` rearrangement
`godsil_sum_prod_rearrange` fed by the IH; close by `linear_combination`. -/
theorem godsil_identity_step (G : SimpleGraph V) (u : V)
    [Fintype (G.PathFrom u)]
    [∀ b : {b : V // G.Adj u b}, Fintype ((G.deleteIncidenceSet u).PathFrom b.val)]
    (IH : ∀ b : {b : V // G.Adj u b},
      (G.deleteIncidenceSet u).matchingPoly
          * (((G.deleteIncidenceSet u).pathTree b.val).deleteIncidenceSet
              (pathTreeRoot (G.deleteIncidenceSet u) b.val)).matchingPoly
        = ((G.deleteIncidenceSet u).deleteIncidenceSet b.val).matchingPoly
          * ((G.deleteIncidenceSet u).pathTree b.val).matchingPoly)
    (hchild : ∀ b : {b : V // G.Adj u b},
      (((G.pathTree u).deleteIncidenceSet (pathTreeRoot G u)).deleteIncidenceSet
          (prependRoot G b.2 (pathTreeRoot (G.deleteIncidenceSet u) b.val))).matchingPoly
        = Polynomial.X
          * (((G.deleteIncidenceSet u).pathTree b.val).deleteIncidenceSet
              (pathTreeRoot (G.deleteIncidenceSet u) b.val)).matchingPoly
          * ∏ b' ∈ Finset.univ.erase b,
              ((G.deleteIncidenceSet u).pathTree b'.val).matchingPoly) :
    G.matchingPoly * ((G.pathTree u).deleteIncidenceSet (pathTreeRoot G u)).matchingPoly
      = (G.deleteIncidenceSet u).matchingPoly * (G.pathTree u).matchingPoly := by
  have hX2 : (Polynomial.X : Polynomial ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 Polynomial.X_ne_zero
  have hD : ((G.pathTree u).deleteIncidenceSet (pathTreeRoot G u)).matchingPoly
      = Polynomial.X * ∏ b : {b : V // G.Adj u b},
          ((G.deleteIncidenceSet u).pathTree b.val).matchingPoly :=
    matchingPoly_pathTree_deleteRoot G u
  have h1 : Polynomial.X ^ 2 * G.matchingPoly
      = Polynomial.X ^ 2 * (G.deleteIncidenceSet u).matchingPoly
        - ∑ b : {b : V // G.Adj u b},
            ((G.deleteIncidenceSet u).deleteIncidenceSet b.val).matchingPoly := by
    have h := matchingPoly_recurrence G u
    unfold matchingPoly_recurrence_target at h
    rw [h, ← Finset.sum_subtype (G.neighborFinset u)
      (fun x => SimpleGraph.mem_neighborFinset G u x)
      (fun v => ((G.deleteIncidenceSet u).deleteIncidenceSet v).matchingPoly)]
  have hST : ∑ c ∈ (G.pathTree u).neighborFinset (pathTreeRoot G u),
        (((G.pathTree u).deleteIncidenceSet (pathTreeRoot G u)).deleteIncidenceSet c).matchingPoly
      = Polynomial.X * ∑ b : {b : V // G.Adj u b},
          (((G.deleteIncidenceSet u).pathTree b.val).deleteIncidenceSet
              (pathTreeRoot (G.deleteIncidenceSet u) b.val)).matchingPoly
          * ∏ b' ∈ Finset.univ.erase b,
              ((G.deleteIncidenceSet u).pathTree b'.val).matchingPoly := by
    rw [sum_root_neighbors, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      rw [hchild b]; ring
  have h2 : Polynomial.X ^ 2 * (G.pathTree u).matchingPoly
      = Polynomial.X ^ 2 * (Polynomial.X * ∏ b : {b : V // G.Adj u b},
            ((G.deleteIncidenceSet u).pathTree b.val).matchingPoly)
        - Polynomial.X * ∑ b : {b : V // G.Adj u b},
            (((G.deleteIncidenceSet u).pathTree b.val).deleteIncidenceSet
                (pathTreeRoot (G.deleteIncidenceSet u) b.val)).matchingPoly
            * ∏ b' ∈ Finset.univ.erase b,
                ((G.deleteIncidenceSet u).pathTree b'.val).matchingPoly := by
    have h := matchingPoly_recurrence (G.pathTree u) (pathTreeRoot G u)
    unfold matchingPoly_recurrence_target at h
    rw [h, hST, hD]
  have hrearr := godsil_sum_prod_rearrange (G.deleteIncidenceSet u).matchingPoly
    (fun b : {b : V // G.Adj u b} =>
      ((G.deleteIncidenceSet u).deleteIncidenceSet b.val).matchingPoly)
    (fun b => (((G.deleteIncidenceSet u).pathTree b.val).deleteIncidenceSet
        (pathTreeRoot (G.deleteIncidenceSet u) b.val)).matchingPoly)
    (fun b => ((G.deleteIncidenceSet u).pathTree b.val).matchingPoly)
    IH
  rw [hD]
  apply mul_left_cancel₀ hX2
  linear_combination (Polynomial.X * ∏ b : {b : V // G.Adj u b},
      ((G.deleteIncidenceSet u).pathTree b.val).matchingPoly) * h1
    - (G.deleteIncidenceSet u).matchingPoly * h2
    + Polynomial.X * hrearr

/-- **★ Godsil's identity** `μ(G)·μ(T(G,u)−r) = μ(G−u)·μ(T(G,u))` — stated target.
**The induction is fully written and `godsil_identity_step` (the inductive step) is PROVEN**
(strong induction on edge count: `G−u` has strictly fewer edges whenever `u` has a neighbour;
`Fintype (G.PathFrom u)` synthesized from `SimpleGraph.Path.instFintype` + `Sigma`). The only
missing input to the induction is `matchingPoly_pathTree_deleteRoot_child_target` (the `whnf`-
blocked sub-decomposition `hchild` that `godsil_identity_step` takes as a hypothesis). Once that
child target is discharged, `godsil_identity_step` + the written induction close this in full. -/
def godsil_identity_target (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    [Fintype (G.PathFrom u)] [DecidableRel (G.pathTree u).Adj] : Prop :=
  G.matchingPoly * ((G.pathTree u).deleteIncidenceSet (pathTreeRoot G u)).matchingPoly
    = (G.deleteIncidenceSet u).matchingPoly * (G.pathTree u).matchingPoly

/-- `PathFrom u = Σ v, Path u v` is a finite type (a `def`, so synthesis needs this explicit
instance via `Path.instFintype` + `Sigma`). Registering it globally lets the edge-count induction
synthesize all `Fintype (· .PathFrom ·)` arguments for the induced subgraphs `G − u`. -/
noncomputable instance instFintypePathFrom (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Fintype (G.PathFrom u) :=
  inferInstanceAs (Fintype (Σ v, G.Path u v))

/-- **Canonical `DecidableRel (pathTree.Adj)`.** `pathTree.Adj = Grows` carries no structural
`Decidable` instance, so it is decided `Classical`ly — but with no *registered* choice, each call
synthesizes its own `Classical.propDecidable`, and the `μ(pathTree)` / `μ(T−r)` terms they build
become syntactically distinct `Subsingleton`-equal instances, forcing a divergent `whnf` over the
`Σ`-paths `μ` when the path-tree divisibility assembly meets `godsil_identity`/`(D)`. Registering
one choice (keyed on the `pathTree.Adj` head — no `abbrev` unfolding ambiguity) makes them agree. -/
noncomputable instance instDecidableRelPathTreeAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) : DecidableRel (G.pathTree u).Adj := fun a b => Classical.propDecidable _

set_option maxHeartbeats 1000000 in
open Classical in
/-- **★ Godsil's identity — PROVEN.** `μ(G)·μ(T(G,u)−r) = μ(G−u)·μ(T(G,u))`, for every finite
graph. Strong induction on the edge count: `godsil_identity_step` reduces it to the identity on
`G − u` at each neighbour `b ∼ u` (the IH — `G − u` has strictly fewer edges, the edge `{u,b}`
being gone) plus the now-proven child sub-decomposition `matchingPoly_pathTree_deleteRoot_child`. -/
theorem godsil_identity (G : SimpleGraph V) (u : V) :
    godsil_identity_target G u := by
  -- measure: edge count as `Set.ncard` (no `DecidableRel` instance — dodges the
  -- propDecidable-vs-derived diamond that `edgeFinset` would introduce on `G − u`).
  suffices H : ∀ n : ℕ, ∀ G : SimpleGraph V, G.edgeSet.ncard ≤ n → ∀ u : V,
      godsil_identity_target G u from H G.edgeSet.ncard G le_rfl u
  clear! G u
  intro n
  induction n with
  | zero =>
    intro G hG u
    refine godsil_identity_step G u (fun b => ?_)
      (fun b => matchingPoly_pathTree_deleteRoot_child G u b)
    exact absurd hG (by
      have : 0 < G.edgeSet.ncard :=
        (Set.ncard_pos G.edgeSet.toFinite).mpr ⟨s(u, b.val), G.mem_edgeSet.mpr b.2⟩
      omega)
  | succ n IH =>
    intro G hG u
    refine godsil_identity_step G u (fun b => ?_)
      (fun b => matchingPoly_pathTree_deleteRoot_child G u b)
    have hss : (G.deleteIncidenceSet u).edgeSet ⊂ G.edgeSet :=
      (Set.ssubset_iff_of_subset (edgeSet_mono (deleteIncidenceSet_le G u))).mpr
        ⟨s(u, b.val), G.mem_edgeSet.mpr b.2,
          fun h => (deleteIncidenceSet_adj.mp ((G.deleteIncidenceSet u).mem_edgeSet.mp h)).2.1 rfl⟩
    have hlt := Set.ncard_lt_ncard hss G.edgeSet.toFinite
    -- IH uses `propDecidable` for `(G−u).Adj` (abstract `G`); the goal uses the derived
    -- `instDecidableRelAdjDeleteIncidenceSet`. They differ only in that one `Subsingleton`
    -- instance — fold the goal (`show`) so the head is `godsil_identity_target` (no `whnf`
    -- unfolding into `matchingPoly`), then `convert using 1` peels the args and `Subsingleton`.
    show (G.deleteIncidenceSet u).godsil_identity_target b.val
    convert IH (G.deleteIncidenceSet u) (Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hG)) b.val using 1

/-- **Godsil's path-tree divisibility** `μ(G) ∣ μ(T(G,u))` as a stated target. Closed by
induction on `|V(G)|` via `godsil_identity_target` + the root decomposition `(D)` +
`dvd_of_godsil_identity`; not yet a theorem. -/
def pathTree_matchingPoly_dvd_target (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    [Fintype (G.PathFrom u)] [DecidableEq (G.PathFrom u)]
    [DecidableRel (G.pathTree u).Adj] : Prop :=
  G.matchingPoly ∣ (G.pathTree u).matchingPoly

end SimpleGraph
