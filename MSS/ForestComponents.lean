/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import MatchingPoly
public import MSS.MatchingSum
public import MSS.PathTree
public import MSS.Divisibility

/-!
# The matching polynomial decomposes over connected components

`μ(G) = ∏_{C : ConnectedComponent} μ(G⟦C.supp⟧)` — a finite graph is the disjoint union of its
connected components, and `μ` is multiplicative over disjoint unions (`matchingPoly_sigmaFamily`).
This is the keystone brick for the path-tree divisibility `μ(G) ∣ μ(T(G,u))` (route A, T1) on a
connected graph (where `G − u` is generally disconnected) and for the general real-rootedness
result T6.
-/

@[expose] public section

namespace SimpleGraph

open Polynomial

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The vertex equivalence `V ≃ Σ C : ConnectedComponent, ↥C.supp` (every vertex lies in exactly
one component; `C.supp = {v | mk v = C}` is the fibre of `connectedComponentMk` over `C`). -/
def componentDecompEquiv : V ≃ Σ C : G.ConnectedComponent, ↥(C.supp) where
  toFun v := ⟨G.connectedComponentMk v, ⟨v, ConnectedComponent.connectedComponentMk_mem⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨C, ⟨v, hv⟩⟩
    have hv' : G.connectedComponentMk v = C := hv
    subst hv'; rfl

/-- **`G` is the disjoint union of its component-induced subgraphs.** The decomposition graph
isomorphism `G ≃g ⊔_C G⟦C.supp⟧`: adjacency only ever occurs within a single component
(`connectedComponentMk_eq_of_adj`), where it is the induced adjacency. -/
def componentDecompIso :
    G ≃g sigmaFamily (fun C : G.ConnectedComponent => G.induce (C.supp : Set V)) where
  toEquiv := componentDecompEquiv G
  map_rel_iff' := by
    intro v w
    dsimp only [componentDecompEquiv, Equiv.coe_fn_mk]
    constructor
    · rintro ⟨i, a, b, hab, hx, hy⟩
      have hav : v = a.1 :=
        congrArg (fun x : Σ C : G.ConnectedComponent, ↥(C.supp) => x.2.1) hx
      have hbw : w = b.1 :=
        congrArg (fun x : Σ C : G.ConnectedComponent, ↥(C.supp) => x.2.1) hy
      rw [hav, hbw]; exact induce_adj.mp hab
    · intro hvw
      have h : G.connectedComponentMk v = G.connectedComponentMk w :=
        ConnectedComponent.connectedComponentMk_eq_of_adj hvw
      refine ⟨G.connectedComponentMk v, ⟨v, ConnectedComponent.connectedComponentMk_mem⟩,
        ⟨w, ?_⟩, induce_adj.mpr hvw, rfl, ?_⟩
      · rw [ConnectedComponent.mem_supp_iff]; exact h.symm
      · exact (componentDecompEquiv G).symm.injective rfl

open Classical in
/-- **The matching polynomial is multiplicative over connected components.** -/
theorem matchingPoly_eq_prod_components :
    G.matchingPoly = ∏ C : G.ConnectedComponent, (G.induce (C.supp : Set V)).matchingPoly := by
  rw [matchingPoly_iso (componentDecompIso G), matchingPoly_sigmaFamily]
  exact Finset.prod_congr rfl fun C _ => matchingPoly_inst_irrel _ _ _ _ _

/-- **On a connected graph, every vertex `w ≠ u` has a `u`-neighbour reachable to it in `G − u`**
(i.e. its `G − u` connected component contains a neighbour of `u`). A path `u → w` (connected)
begins with an edge `u → b`; its tail is a path avoiding `u`, hence a walk in `G − u` from `b` to
`w`. This is the brick that, in the path-tree divisibility, attaches each non-`u` component of
`G − u` to a child subtree `T(G−u, b)`. -/
theorem exists_adj_reachable_of_ne (hG : G.Connected) {u w : V} (hw : w ≠ u) :
    ∃ b, G.Adj u b ∧ (G.deleteIncidenceSet u).Reachable b w := by
  obtain ⟨p, hpath⟩ := (hG.preconnected u w).some.toPath
  cases p with
  | nil => exact absurd rfl hw
  | cons h q =>
    rw [Walk.cons_isPath_iff] at hpath
    refine ⟨_, h, ?_⟩
    refine ⟨q.transfer (G.deleteIncidenceSet u) (fun e he => ?_)⟩
    rw [mem_edgeSet_deleteIncidenceSet]
    exact ⟨q.edges_subset_edgeSet he,
      fun hue => hpath.2 (Walk.mem_support_of_mem_edges he hue)⟩

/-! ### Path-tree confinement to a component (brick c) -/

namespace Walk
variable {V : Type*} {H : SimpleGraph V} {s : Set V}

/-- **Transport a walk into an induced subgraph.** A walk of `H` whose support lies in `s`
becomes a walk of `H.induce s` between the corresponding subtype endpoints. -/
def toInduce : {w x : V} → (hw : w ∈ s) → (hx : x ∈ s) →
    (p : H.Walk w x) → (∀ y ∈ p.support, y ∈ s) → (H.induce s).Walk ⟨w, hw⟩ ⟨x, hx⟩
  | _, _, _, _, .nil, _ => .nil
  | w, x, hw, hx, .cons (v := y) h q, hsupp =>
      have hy : y ∈ s := hsupp y (by rw [support_cons]; exact List.mem_cons_of_mem _ q.start_mem_support)
      .cons (SimpleGraph.induce_adj.mpr h)
        (toInduce hy hx q (fun z hz => hsupp z (by rw [support_cons]; exact List.mem_cons_of_mem _ hz)))

/-- Mapping a transported walk back through the induced-subgraph embedding recovers the original. -/
theorem map_toInduce : ∀ {w x : V} (hw : w ∈ s) (hx : x ∈ s) (p : H.Walk w x)
    (hsupp : ∀ y ∈ p.support, y ∈ s),
    (p.toInduce hw hx hsupp).map (SimpleGraph.Embedding.induce s).toHom = p
  | _, _, _, _, .nil, _ => rfl
  | _, _, hw, hx, .cons h q, hsupp => by
      simp only [toInduce, Walk.map_cons]
      rw [map_toInduce]
      rfl

/-- Lifting a walk that was mapped down from `H.induce s` recovers it (the other roundtrip). -/
theorem toInduce_map {a b : ↥s} (p : (H.induce s).Walk a b)
    (hsupp : ∀ y ∈ (p.map (SimpleGraph.Embedding.induce s).toHom).support, y ∈ s) :
    (p.map (SimpleGraph.Embedding.induce s).toHom).toInduce a.2 b.2 hsupp = p := by
  refine SimpleGraph.Walk.map_injective_of_injective
    (f := (SimpleGraph.Embedding.induce (G := H) s).toHom)
    (SimpleGraph.Embedding.induce (G := H) s).injective a b ?_
  rw [map_toInduce]

/-- The transported walk is a path when the original is (its support is unchanged). -/
theorem toInduce_isPath {w x : V} (hw : w ∈ s) (hx : x ∈ s) (p : H.Walk w x)
    (hsupp : ∀ y ∈ p.support, y ∈ s) (hp : p.IsPath) : (p.toInduce hw hx hsupp).IsPath :=
  SimpleGraph.Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce s).toHom)
    (by rw [map_toInduce]; exact hp)

/-- Every vertex on a walk starting at `w` lies in `w`'s connected component. -/
theorem mem_component_supp_of_mem_support [DecidableEq V] {w x : V} (p : H.Walk w x)
    {y : V} (hy : y ∈ p.support) : y ∈ (H.connectedComponentMk w).supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
  exact (p.takeUntil y hy).reachable.symm

/-- `map` commutes with `concat` (appending one edge). -/
theorem map_concat {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} (f : G₁ →g G₂)
    {u v z : V₁} (p : G₁.Walk u v) (h : G₁.Adj v z) :
    (p.concat h).map f = (p.map f).concat (f.map_adj h) := by
  rw [SimpleGraph.Walk.concat_eq_append, SimpleGraph.Walk.map_append,
      SimpleGraph.Walk.concat_eq_append]
  rfl

end Walk

/-! ### The confinement bijection on path-tree vertices -/

/-- **Confinement vertex bijection.** Paths of `H` from `w` correspond to paths of the
component-induced subgraph `H.induce (comp w).supp` from `⟨w, _⟩`: a path of `H` from `w` stays in
`w`'s component, so it transports (both ways) across the induced-subgraph embedding. Forward =
`Path.mapEmbedding`; injective by `mapEmbedding_injective`; surjective by the lift `Walk.toInduce`
(with `map_toInduce` the roundtrip). -/
noncomputable def pathTreeComponentEquiv [DecidableEq V] (H : SimpleGraph V) (w : V) :
    (H.induce (H.connectedComponentMk w).supp).PathFrom
        ⟨w, ConnectedComponent.connectedComponentMk_mem⟩ ≃ H.PathFrom w :=
  Equiv.ofBijective
    (fun a => ⟨a.1.1, a.2.mapEmbedding (SimpleGraph.Embedding.induce _)⟩)
    ⟨by
      rintro ⟨⟨z, hz⟩, q⟩ ⟨⟨z', hz'⟩, q'⟩ h
      rw [Sigma.mk.injEq] at h
      obtain ⟨hzz, hqq⟩ := h
      subst hzz
      have : q = q' := Path.mapEmbedding_injective _ _ _ (eq_of_heq hqq)
      subst this; rfl,
     by
      rintro ⟨x, p⟩
      have hx : x ∈ (H.connectedComponentMk w).supp :=
        Walk.mem_component_supp_of_mem_support p.1 p.1.end_mem_support
      have hsupp : ∀ y ∈ p.1.support, y ∈ (H.connectedComponentMk w).supp :=
        fun y hy => Walk.mem_component_supp_of_mem_support p.1 hy
      refine ⟨⟨⟨x, hx⟩, ⟨p.1.toInduce ConnectedComponent.connectedComponentMk_mem hx hsupp,
        Walk.toInduce_isPath _ _ _ _ p.2⟩⟩, ?_⟩
      refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
      simpa [Path.mapEmbedding] using
        Walk.map_toInduce ConnectedComponent.connectedComponentMk_mem hx p.1 hsupp⟩

open Classical in
/-- **★ Path-tree confinement (brick c).** The matching polynomial of the path tree from `w`
depends only on `w`'s connected component: `μ(T(H,w)) = μ(T(H⟦comp w⟧, w))`. Proof: the vertex
bijection `pathTreeComponentEquiv` is a graph isomorphism of path trees — it preserves the `Grows`
(extend-by-one-edge) relation because `Path.mapEmbedding` commutes with `concat` (`map_concat`) and
the embedding is injective — so `matchingPoly_iso` applies. This is the input the path-tree
divisibility needs: in `(D)`, the child subtree `T(G−u, b)` (for `b` in component `C`) has the same
`μ` as `T(C, b)`, where the inductive hypothesis applies. -/
theorem matchingPoly_pathTree_eq_induce_component [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (w : V) :
    (H.pathTree w).matchingPoly
      = ((H.induce (H.connectedComponentMk w).supp).pathTree
          ⟨w, ConnectedComponent.connectedComponentMk_mem⟩).matchingPoly := by
  set s := (H.connectedComponentMk w).supp with hs
  set ι := (SimpleGraph.Embedding.induce (G := H) s) with hι
  have hgrows : ∀ a b : (H.induce s).PathFrom ⟨w, ConnectedComponent.connectedComponentMk_mem⟩,
      Grows (pathTreeComponentEquiv H w a) (pathTreeComponentEquiv H w b) ↔ Grows a b := by
    intro a b
    constructor
    · rintro ⟨he, heq⟩
      refine ⟨SimpleGraph.induce_adj.mpr he, ?_⟩
      refine SimpleGraph.Walk.map_injective_of_injective (f := ι.toHom) ι.injective _ _ ?_
      rw [Walk.map_concat]
      exact heq
    · rintro ⟨he, heq⟩
      refine ⟨ι.toHom.map_adj he, ?_⟩
      show (b.2.1).map ι.toHom = ((a.2.1).map ι.toHom).concat _
      rw [heq, Walk.map_concat]
  symm
  exact matchingPoly_iso
    { toEquiv := pathTreeComponentEquiv H w
      map_rel_iff' := by
        intro a b
        simp only [pathTree_adj]
        rw [hgrows a b, hgrows b a] }

/-! ### Brick (e) — the path-tree divisibility assembly (T1) -/

/-- `μ(H⟦C.supp⟧)` depends only on the component `C` — a congruence used to bridge a component
named via a representative (`comp b`) with the same component appearing as a product index. Proven
by `subst` so as to never `rw` the set inside `induce`/`matchingPoly` (the `DecidableRel`-motive
trap documented for brick (c)/Lemma A). -/
theorem matchingPoly_induce_supp_congr (H : SimpleGraph V) [DecidableRel H.Adj]
    {C C' : H.ConnectedComponent} (h : C = C') :
    (H.induce C.supp).matchingPoly = (H.induce C'.supp).matchingPoly := by
  subst h; rfl

open Classical in
/-- **Lemma A.** When `u` is isolated in `H` (no `H`-neighbours), its connected component is the
singleton `{u}`, the induced subgraph is edgeless, and `μ(H⟦comp u⟧) = X`. Proven without
rewriting the graph inside `μ` (the `DecidableRel`-motive trap): a walk out of an isolated `u`
must be `nil`, so `comp u` is a subsingleton; build the identity iso to `⊥` on the (subsingleton)
carrier and evaluate `matchingPoly_bot` at card `1`. -/
theorem matchingPoly_induce_isolated_component (H : SimpleGraph V) [DecidableRel H.Adj] (u : V)
    (hiso : ∀ c, ¬ H.Adj u c) :
    (H.induce (H.connectedComponentMk u).supp).matchingPoly = X := by
  have hsub : ∀ x ∈ (H.connectedComponentMk u).supp, x = u := by
    intro x hx
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] at hx
    obtain ⟨p⟩ := hx.symm
    cases p with
    | nil => rfl
    | cons h _ => exact absurd h (hiso _)
  have hcard : Fintype.card ↥(H.connectedComponentMk u).supp = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨u, ConnectedComponent.connectedComponentMk_mem⟩, fun y => Subtype.ext (hsub y.1 y.2)⟩
  have hsubsing : Subsingleton ↥(H.connectedComponentMk u).supp :=
    ⟨fun a b => Subtype.ext ((hsub a.1 a.2).trans (hsub b.1 b.2).symm)⟩
  have e : H.induce (H.connectedComponentMk u).supp
      ≃g (⊥ : SimpleGraph ↥(H.connectedComponentMk u).supp) :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := fun {a b} =>
        ⟨fun h => h.elim, fun hab => absurd (Subsingleton.elim a b) hab.ne⟩ }
  rw [matchingPoly_iso e, matchingPoly_bot, hcard, pow_one]

set_option maxHeartbeats 1000000 in
open Classical in
/-- **Generalized brick (e)**, the engine of `connected_matchingPoly_dvd_pathTree`. Strong
induction on `|V|`, polymorphic over the vertex type (components are subtypes). The step
(`dvd_of_godsil_identity` with the proven `godsil_identity` and `μ(G−u) ≠ 0`) reduces to
`μ(G−u) ∣ μ(T−r)`. `(D)` gives `μ(T−r) = X·∏_{b∼u} μ(T(G−u,b))`; `matchingPoly_eq_prod_components`
gives `μ(G−u) = ∏_C μ(G−u⟦C⟧)`. The `{u}`-component is isolated in `G−u` (`μ = X`, Lemma A) and
matches the explicit `X`; every other component `C` carries a `u`-neighbour `b_C`
(`exists_adj_reachable_of_ne`), `C ↦ b_C` is injective, and `μ(G−u⟦C⟧) ∣ μ(T(G−u,b_C))` by the IH on
`G−u⟦C⟧` (connected, fewer vertices) composed with confinement (c). A `prod_dvd_prod`/`prod_image`
chain over the injective reindex closes it. -/
private theorem brick_e_aux : ∀ (n : ℕ) {W : Type*} [Fintype W] [DecidableEq W]
    (G' : SimpleGraph W) [DecidableRel G'.Adj], Fintype.card W ≤ n → G'.Connected →
    ∀ u' : W, G'.matchingPoly ∣ (G'.pathTree u').matchingPoly := by
  intro n
  induction n with
  | zero =>
    intro W _ _ G' _ hcard _ u'
    exact ((Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)).false u').elim
  | succ n IH =>
    intro W _ _ G' _ hcard hconn u'
    -- **Instance determinism.** `godsil_identity`/`(D)` (file `Divisibility`, under `open Classical`)
    -- synthesize every `Decidable (G'.Adj a b)` as `Classical.propDecidable`, whereas a default
    -- synthesis here would pick the `[DecidableRel G'.Adj]` binder. The two are `Subsingleton`-equal
    -- but syntactically distinct, and any `matchingPoly` (over `W`, `PathFrom`, …) built from them
    -- then mismatches — forcing a divergent `whnf` on the `Σ`-paths `μ`. Pin `DecidableRel G'.Adj` to
    -- the same `propDecidable` choice so *all* derived instances below agree with `Divisibility`'s.
    letI : DecidablePred (G'.Adj u') := fun a => Classical.propDecidable (G'.Adj u' a)
    -- Work with the bare term `G' − u'` everywhere (no `set` abbreviation): the proven `(D)` and
    -- `godsil_identity` emit it unfolded, and any `set`-fold would leave their outputs syntactically
    -- distinct from the local hypotheses, forcing a `whnf` over `μ(pathTree)` (the `Σ`-paths wall).
    have hiso : ∀ c, ¬ (G'.deleteIncidenceSet u').Adj u' c :=
      fun c h => (deleteIncidenceSet_adj.mp h).2.1 rfl
    set Cu := (G'.deleteIncidenceSet u').connectedComponentMk u' with hCu
    -- every non-`u` component carries a `u`-neighbour
    have key : ∀ C : (G'.deleteIncidenceSet u').ConnectedComponent, C ≠ Cu →
        ∃ b : {b : W // G'.Adj u' b}, (G'.deleteIncidenceSet u').connectedComponentMk b.val = C := by
      intro C hCneq
      obtain ⟨w, hw⟩ := C.exists_rep
      have hwu : w ≠ u' :=
        fun h => hCneq (hw.symm.trans
          ((congrArg (G'.deleteIncidenceSet u').connectedComponentMk h).trans hCu.symm))
      obtain ⟨b, hadj, hreach⟩ := exists_adj_reachable_of_ne G' hconn hwu
      exact ⟨⟨b, hadj⟩, (ConnectedComponent.eq.mpr hreach).trans hw⟩
    -- choice of `b_C` on the components other than `{u}`
    let φ : ↥(Finset.univ.erase Cu) → {b : W // G'.Adj u' b} :=
      fun C => Classical.choose (key C.val (Finset.mem_erase.mp C.2).1)
    have hφspec : ∀ C : ↥(Finset.univ.erase Cu),
        (G'.deleteIncidenceSet u').connectedComponentMk (φ C).val = C.val :=
      fun C => Classical.choose_spec (key C.val (Finset.mem_erase.mp C.2).1)
    have hφinj : Function.Injective φ := by
      intro C₁ C₂ h
      exact Subtype.ext (by rw [← hφspec C₁, ← hφspec C₂, h])
    -- per-component divisibility via IH + confinement (c)
    have hdvd_comp : ∀ C : ↥(Finset.univ.erase Cu),
        ((G'.deleteIncidenceSet u').induce C.val.supp).matchingPoly ∣
          ((G'.deleteIncidenceSet u').pathTree (φ C).val).matchingPoly := by
      intro C
      have hbC := hφspec C
      have hu_notin : u' ∉ ((G'.deleteIncidenceSet u').connectedComponentMk (φ C).val).supp := by
        rw [ConnectedComponent.mem_supp_iff, hbC]
        intro hcontra
        exact (Finset.mem_erase.mp C.2).1 (hcontra.symm.trans hCu.symm)
      have hcardlt :
          Fintype.card ↥((G'.deleteIncidenceSet u').connectedComponentMk (φ C).val).supp ≤ n :=
        Nat.lt_succ_iff.mp (lt_of_lt_of_le (Fintype.card_subtype_lt hu_notin) hcard)
      have hih := IH ((G'.deleteIncidenceSet u').induce
          ((G'.deleteIncidenceSet u').connectedComponentMk (φ C).val).supp) hcardlt
        (ConnectedComponent.connected_toSimpleGraph _)
        ⟨(φ C).val, ConnectedComponent.connectedComponentMk_mem⟩
      rw [← matchingPoly_pathTree_eq_induce_component (G'.deleteIncidenceSet u') (φ C).val] at hih
      rwa [matchingPoly_induce_supp_congr (G'.deleteIncidenceSet u') hbC] at hih
    -- carve the `{u}` component out of `μ(G−u)` and match the explicit `X` of `(D)`
    have hGu : ((G'.deleteIncidenceSet u').induce Cu.supp).matchingPoly = X :=
      matchingPoly_induce_isolated_component (G'.deleteIncidenceSet u') u' hiso
    have hHfac : (G'.deleteIncidenceSet u').matchingPoly
        = X * ∏ C ∈ Finset.univ.erase Cu, ((G'.deleteIncidenceSet u').induce C.supp).matchingPoly := by
      rw [matchingPoly_eq_prod_components (G'.deleteIncidenceSet u'),
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ Cu), hGu]
    have hdvd : (G'.deleteIncidenceSet u').matchingPoly ∣
        ((G'.pathTree u').deleteIncidenceSet (pathTreeRoot G' u')).matchingPoly := by
      rw [hHfac, matchingPoly_pathTree_deleteRoot G' u']
      refine mul_dvd_mul_left X ?_
      -- `∏_C μ(G−u⟦C⟧) ∣ ∏_{b∈image φ} μ(T(G−u,b))`, then `image φ ⊆ univ`. Split the final subset
      -- step out of the `calc` and discharge it by `exact` against the goal, so its superset `univ`
      -- unifies with the neighbour-index `Fintype` that `(D)` produced (not a re-synthesized one).
      have step :
          (∏ C ∈ Finset.univ.erase Cu, ((G'.deleteIncidenceSet u').induce C.supp).matchingPoly) ∣
            ∏ b ∈ Finset.univ.image φ, ((G'.deleteIncidenceSet u').pathTree b.val).matchingPoly :=
        calc (∏ C ∈ Finset.univ.erase Cu, ((G'.deleteIncidenceSet u').induce C.supp).matchingPoly)
            = ∏ C : ↥(Finset.univ.erase Cu),
                ((G'.deleteIncidenceSet u').induce C.val.supp).matchingPoly :=
              (Finset.prod_coe_sort _ _).symm
          _ ∣ ∏ C : ↥(Finset.univ.erase Cu),
                ((G'.deleteIncidenceSet u').pathTree (φ C).val).matchingPoly :=
              Finset.prod_dvd_prod_of_dvd _ _ (fun C _ => hdvd_comp C)
          _ = ∏ b ∈ Finset.univ.image φ, ((G'.deleteIncidenceSet u').pathTree b.val).matchingPoly :=
              (Finset.prod_image (s := Finset.univ) (g := φ)
                (f := fun b : {b : W // G'.Adj u' b} =>
                  ((G'.deleteIncidenceSet u').pathTree b.val).matchingPoly)
                hφinj.injOn).symm
      exact step.trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _))
    -- **The close of brick (e)** (formerly the one blocked line; `godsil_identity` + `hdvd` proven).
    -- `hid` (from `godsil_identity`) carries Divisibility's *baked* (def-time, `open Classical`)
    -- `Fintype`/`DecidableRel` instances on every `μ`; `hne`/`hdvd`/goal carry freshly-synthesized
    -- *local* ones (the `Σ`-of-paths `PathFrom` `abbrev` lets a structural `Sigma` instance compete
    -- with the `Classical` one). Feeding `hid` straight into `dvd_of_godsil_identity` forces its
    -- implicit-`μ` unification to `whnf`-reduce `μ` over the `Σ`-paths type — diverges (1M+
    -- heartbeats; `convert`/`isDefEq` hit the same wall). FIX: rewrite each of `hid`'s four `μ`
    -- terms in place to the LOCAL instances via `matchingPoly_inst_irrel` (graph pinned ⇒ keyed,
    -- syntactic match — no `whnf`; the RHS instance metavars resolve by TC to the local canonical
    -- ones). Then `hid`, `hne`, `hdvd`, goal are all-local ⇒ `dvd_of_godsil_identity` needs no
    -- `whnf`. No `PathFrom`-`def` refactor required.
    have hid := godsil_identity G' u'
    unfold godsil_identity_target at hid
    rw [matchingPoly_inst_irrel _ _ G' _ _,
        matchingPoly_inst_irrel _ _
          ((G'.pathTree u').deleteIncidenceSet (pathTreeRoot G' u')) _ _,
        matchingPoly_inst_irrel _ _ (G'.deleteIncidenceSet u') _ _,
        matchingPoly_inst_irrel _ _ (G'.pathTree u') _ _] at hid
    exact dvd_of_godsil_identity
      (matchingPoly_monic (G'.deleteIncidenceSet u')).ne_zero hid hdvd

open Classical in
/-- **★ Brick (e) — path-tree divisibility (connected case), T1.** `μ(G) ∣ μ(T(G,u))` for every
connected finite graph (`brick_e_aux` specialized to `|V|`). The final specialization is bridged by
`matchingPoly_inst_irrel` rather than `exact`, so `isDefEq` never has to structurally compare the
`Fintype (PathFrom)`/`DecidableRel (pathTree.Adj)` instances of the goal against the generalized
statement (a `whnf` blow-up over the `Σ`-of-paths type). -/
theorem connected_matchingPoly_dvd_pathTree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (u : V) :
    G.matchingPoly ∣ (G.pathTree u).matchingPoly := by
  have h := brick_e_aux (Fintype.card V) G le_rfl hG u
  rwa [matchingPoly_inst_irrel _ _ (G.pathTree u) _ _] at h

end SimpleGraph
