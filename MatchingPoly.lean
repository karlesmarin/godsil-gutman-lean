/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import RealStable

/-!
# The matching polynomial and the Heilmann–Lieb target (MSS right cordada)

The **right cordada** of the Marcus–Spielman–Srivastava (MSS) Ramanujan-existence
expedition: the matching polynomial of a graph and the Heilmann–Lieb theorem.

For a finite graph `G` on `n` vertices, the **matching polynomial** is
```
  μ(G, x) = Σ_k (-1)^k m_k x^{n-2k},    m_k = #{k-edge matchings}.
```
Statistical-mechanics reading: `m_k` counts configurations of a monomer-dimer gas
with `k` dimers; `μ` is its (characteristic form of the) partition function.

**Heilmann–Lieb (1972):** `μ(G)` is real-rooted, and for max degree `Δ ≥ 2` all
roots lie in `[−2√(Δ−1), 2√(Δ−1)]` — i.e. `MSS.BoundedBy (μ G) (2√(Δ−1))`. This
is the *same* `BoundedBy` substrate that governs the spectral / discrete-RH side
(`IharaZeta.lean`), and the engine of MSS: the expected characteristic polynomial
of a random signing equals `μ(G)`, so an interlacing family yields a signing whose
characteristic polynomial stays in the Ramanujan band. The Heilmann–Lieb proof is
itself by interlacing — provable via the muscle already built in `RealStable`.

## Status (2026-05-30)
* `matchingPoly`, `matchingNumber`, `IsMatchingSet`: defined.
* `matchingNumber_zero` (the empty matching, `m_0 = 1`): PROVEN sorry-free.
* `heilmann_lieb` and `mss_expected_charpoly` are documented targets (stubs).
-/

@[expose] public section

namespace SimpleGraph

open Classical Polynomial Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finset of edges is a **matching set** if its edges are pairwise
vertex-disjoint (no vertex lies in two of them). -/
def IsMatchingSet (s : Finset (Sym2 V)) : Prop :=
  ∀ e ∈ s, ∀ f ∈ s, e ≠ f → ∀ v, v ∈ e → v ∉ f

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The finset of `k`-edge matchings of `G`: `k`-subsets of the edge set whose
edges are pairwise disjoint. -/
noncomputable def matchingsOfCard (k : ℕ) : Finset (Finset (Sym2 V)) :=
  (G.edgeFinset.powersetCard k).filter IsMatchingSet

/-- The matching number `m_k = #{k-edge matchings}` of `G`. -/
noncomputable def matchingNumber (k : ℕ) : ℕ := (G.matchingsOfCard k).card

/-- The **matching polynomial** `μ(G, x) = Σ_k (-1)^k m_k x^{n-2k}`, summed over
`k ≤ n/2` (a matching of `k` edges covers `2k ≤ n` vertices). -/
noncomputable def matchingPoly : Polynomial ℝ :=
  ∑ k ∈ Finset.range (Fintype.card V / 2 + 1),
    Polynomial.C ((-1 : ℝ) ^ k * (G.matchingNumber k : ℝ))
      * Polynomial.X ^ (Fintype.card V - 2 * k)

/-- **The empty matching.** There is exactly one `0`-edge matching (the empty
set), so `m_0 = 1`. This is the leading coefficient of `μ(G)` and the base anchor
that the definition behaves. -/
theorem matchingNumber_zero : G.matchingNumber 0 = 1 := by
  unfold matchingNumber matchingsOfCard
  rw [Finset.powersetCard_zero, Finset.filter_singleton, if_pos, Finset.card_singleton]
  intro e he
  exact absurd he (Finset.notMem_empty e)

/-! ## Heilmann–Lieb by interlacing — first cala: the base case -/

/-- For the **edgeless graph** `⊥`, the only matching is the empty one:
`m_k = 1` if `k = 0`, else `0`. -/
theorem matchingNumber_bot (k : ℕ) :
    (⊥ : SimpleGraph V).matchingNumber k = if k = 0 then 1 else 0 := by
  by_cases h : k = 0
  · subst h; rw [if_pos rfl]; exact matchingNumber_zero ⊥
  · simp only [matchingNumber, matchingsOfCard, if_neg h, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, Finset.mem_powersetCard]
    rintro x ⟨hsub, hcard⟩
    have hx0 : x = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      have hmem := hsub he
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_bot,
        Set.mem_empty_iff_false] at hmem
    rw [hx0, Finset.card_empty] at hcard
    exact absurd hcard.symm h

/-- **Base case of the Heilmann–Lieb induction.** The matching polynomial of the
edgeless graph is `μ(⊥) = X^n` (all roots `0`, trivially in the band). -/
theorem matchingPoly_bot : (⊥ : SimpleGraph V).matchingPoly = X ^ (Fintype.card V) := by
  have h0 : ∀ k ∈ Finset.range (Fintype.card V / 2 + 1), k ≠ 0 →
      Polynomial.C ((-1 : ℝ) ^ k * ((⊥ : SimpleGraph V).matchingNumber k : ℝ))
        * X ^ (Fintype.card V - 2 * k) = 0 := by
    intro k _ hk
    rw [matchingNumber_bot, if_neg hk]; simp
  unfold matchingPoly
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos _)) h0,
      matchingNumber_bot]
  simp

/-- The base case is real-rooted: `μ(⊥) = X^n` splits over `ℝ` (root `0`,
multiplicity `n`). The anchor of the interlacing induction toward Heilmann–Lieb. -/
theorem matchingPoly_bot_realRooted :
    MSS.RealRooted ((⊥ : SimpleGraph V).matchingPoly) := by
  rw [matchingPoly_bot]
  have hX : MSS.RealRooted (X : Polynomial ℝ) := by
    have h := MSS.realRooted_X_sub_C (0 : ℝ); simpa using h
  exact Submonoid.pow_mem _ hX _

/-! ## Degree and monicity of `μ(G)` -/

/-- `μ(G)` with its leading (`k = 0`) term `X^n` split off. The `k=0` summand is
`C((-1)^0 · m_0) X^{n-0} = X^n` (since `m_0 = 1`); the rest are the lower terms. -/
theorem matchingPoly_eq_X_pow_add_erase (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.matchingPoly =
      X ^ Fintype.card V
      + ∑ k ∈ (Finset.range (Fintype.card V / 2 + 1)).erase 0,
          C ((-1 : ℝ) ^ k * (G.matchingNumber k : ℝ)) * X ^ (Fintype.card V - 2 * k) := by
  rw [matchingPoly, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (Nat.succ_pos _))]
  congr 1
  rw [matchingNumber_zero]
  simp

/-- The non-leading terms of `μ(G)` all have degree `< n = |V|`: term `k ≥ 1` has
degree `≤ n - 2k < n`. -/
theorem matchingPoly_erase_degree_lt (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ k ∈ (Finset.range (Fintype.card V / 2 + 1)).erase 0,
        C ((-1 : ℝ) ^ k * (G.matchingNumber k : ℝ)) * X ^ (Fintype.card V - 2 * k)).degree
      < (Fintype.card V : WithBot ℕ) := by
  apply lt_of_le_of_lt (degree_sum_le _ _)
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro k hk
  rw [Finset.mem_erase, Finset.mem_range] at hk
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast (by omega : Fintype.card V - 2 * k < Fintype.card V)

/-- **`μ(G)` is monic.** Its leading term is the `k=0` summand `X^n`. -/
theorem matchingPoly_monic (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.matchingPoly).Monic := by
  rw [matchingPoly_eq_X_pow_add_erase]
  exact (monic_X_pow _).add_of_left
    (by rw [degree_X_pow]; exact matchingPoly_erase_degree_lt G)

/-- **`deg μ(G) = n = |V|`.** -/
theorem matchingPoly_degree (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.matchingPoly).degree = (Fintype.card V : WithBot ℕ) := by
  rw [matchingPoly_eq_X_pow_add_erase,
      degree_add_eq_left_of_degree_lt
        (by rw [degree_X_pow]; exact matchingPoly_erase_degree_lt G),
      degree_X_pow]

@[simp] theorem matchingPoly_natDegree (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.matchingPoly).natDegree = Fintype.card V :=
  natDegree_eq_of_degree_eq_some (matchingPoly_degree G)

/-! ## Vertex deletion (first cala of the matching recurrence) -/

/-- **Vertex deletion, edge level.** `G.deleteIncidenceSet v` (Mathlib) is `G` with
all edges at `v` removed — `v` becomes isolated, the vertex type `V` is preserved
(no subtypes). An edge survives iff it was an edge of `G` not containing `v`.
This is the foundational identity of the matching recurrence: a matching of `G`
that avoids `v` is exactly a matching of `G.deleteIncidenceSet v`. -/
theorem mem_edgeSet_deleteIncidenceSet (G : SimpleGraph V) (v : V) (e : Sym2 V) :
    e ∈ (G.deleteIncidenceSet v).edgeSet ↔ e ∈ G.edgeSet ∧ v ∉ e := by
  rw [edgeSet_deleteIncidenceSet]
  simp only [Set.mem_diff, SimpleGraph.incidenceSet, Set.mem_sep_iff, not_and]
  constructor
  · rintro ⟨he, hni⟩; exact ⟨he, hni he⟩
  · rintro ⟨he, hv⟩; exact ⟨he, fun _ => hv⟩

/-- **`v` is isolated after deletion.** No surviving edge contains `v`. The clean
statement of "vertex `v` removed": every matching of `G.deleteIncidenceSet v`
avoids `v`, which is what the `v`-not-covered branch of the recurrence needs. -/
theorem notMem_of_mem_edgeSet_deleteIncidenceSet (G : SimpleGraph V) (v : V)
    {e : Sym2 V} (he : e ∈ (G.deleteIncidenceSet v).edgeSet) : v ∉ e :=
  ((mem_edgeSet_deleteIncidenceSet G v e).mp he).2

/-- The deleted graph is a subgraph: every edge of `G.deleteIncidenceSet v` is an
edge of `G`. -/
theorem edgeSet_deleteIncidenceSet_subset (G : SimpleGraph V) (v : V) :
    (G.deleteIncidenceSet v).edgeSet ⊆ G.edgeSet :=
  fun _ he => ((mem_edgeSet_deleteIncidenceSet G v _).mp he).1

/-! ## Count decomposition, branch (a): matchings avoiding `v` -/

/-- The `edgeFinset` version of `mem_edgeSet_deleteIncidenceSet`. -/
theorem mem_edgeFinset_deleteIncidenceSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (e : Sym2 V) :
    e ∈ (G.deleteIncidenceSet v).edgeFinset ↔ e ∈ G.edgeFinset ∧ v ∉ e := by
  simp only [SimpleGraph.mem_edgeFinset]
  exact mem_edgeSet_deleteIncidenceSet G v e

/-- **Decomposition, the `v`-avoiding branch.** The `k`-matchings of
`G.deleteIncidenceSet v` are exactly the `k`-matchings of `G` that avoid `v`:
```
  (G−v).matchingsOfCard k = (G.matchingsOfCard k).filter (no edge contains v).
```
This is the first half of the matching recurrence `m_k(G) = m_k(G−v) + …`: the
matchings not covering `v` are precisely those of the deleted graph. -/
theorem matchingsOfCard_deleteIncidenceSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (k : ℕ) :
    (G.deleteIncidenceSet v).matchingsOfCard k
      = (G.matchingsOfCard k).filter (fun s => ∀ e ∈ s, v ∉ e) := by
  ext s
  simp only [matchingsOfCard, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hmatch⟩
    refine ⟨⟨⟨fun e he => ((mem_edgeFinset_deleteIncidenceSet G v e).mp (hsub he)).1, hcard⟩,
      hmatch⟩, fun e he => ((mem_edgeFinset_deleteIncidenceSet G v e).mp (hsub he)).2⟩
  · rintro ⟨⟨⟨hsub, hcard⟩, hmatch⟩, hv⟩
    exact ⟨⟨fun e he => (mem_edgeFinset_deleteIncidenceSet G v e).mpr ⟨hsub he, hv e he⟩,
      hcard⟩, hmatch⟩

/-- Consequently the matching number of `G−v` counts the `v`-avoiding
`k`-matchings of `G`. -/
theorem matchingNumber_deleteIncidenceSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (k : ℕ) :
    (G.deleteIncidenceSet v).matchingNumber k
      = ((G.matchingsOfCard k).filter (fun s => ∀ e ∈ s, v ∉ e)).card := by
  rw [matchingNumber, matchingsOfCard_deleteIncidenceSet]

/-! ## Count decomposition, branch (b): matchings covering `v` -/

/-- **Double deletion, edge level.** `G − v − u` (delete the incidence sets of
both `v` and `u`) keeps exactly the edges of `G` containing neither. -/
theorem mem_edgeSet_deleteIncidenceSet_two (G : SimpleGraph V) (v u : V) (e : Sym2 V) :
    e ∈ ((G.deleteIncidenceSet v).deleteIncidenceSet u).edgeSet
      ↔ e ∈ G.edgeSet ∧ v ∉ e ∧ u ∉ e := by
  rw [mem_edgeSet_deleteIncidenceSet, mem_edgeSet_deleteIncidenceSet]
  tauto

/-- **`G − v − u` matchings = `G` matchings avoiding both `v` and `u`.** Composing
the `v`-avoiding branch twice. This is the codomain side of branch (b): removing
the edge `{v,u}` from a `k`-matching of `G` covering `v` (via `u`) lands in the
`(k−1)`-matchings of `G − v − u`. -/
theorem matchingsOfCard_deleteIncidenceSet_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (v u : V) (k : ℕ) :
    ((G.deleteIncidenceSet v).deleteIncidenceSet u).matchingsOfCard k
      = (G.matchingsOfCard k).filter (fun s => (∀ e ∈ s, v ∉ e) ∧ (∀ e ∈ s, u ∉ e)) := by
  rw [matchingsOfCard_deleteIncidenceSet, matchingsOfCard_deleteIncidenceSet,
      Finset.filter_filter]

/-- **Matchings are subset-closed.** Removing edges from a matching keeps a
matching — the `erase`-the-`{v,u}`-edge direction of the branch-(b) bijection. -/
theorem IsMatchingSet.subset {s t : Finset (Sym2 V)} (hs : IsMatchingSet s)
    (hts : t ⊆ s) : IsMatchingSet t :=
  fun e he f hf hef w hwe => hs e (hts he) f (hts hf) hef w hwe

/-- **Inserting a disjoint edge keeps a matching.** If `e` shares no vertex with
any edge of the matching `t`, then `insert e t` is a matching — the `insert`-the
-`{v,u}`-edge direction of the branch-(b) bijection. -/
theorem IsMatchingSet.insert {e : Sym2 V} {t : Finset (Sym2 V)} (ht : IsMatchingSet t)
    (hd : ∀ f ∈ t, ∀ w, w ∈ e → w ∉ f) (hd' : ∀ f ∈ t, ∀ w, w ∈ f → w ∉ e) :
    IsMatchingSet (insert e t) := by
  intro a ha b hb hab w hwa
  rw [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact absurd rfl hab
  · exact hd b hb w hwa
  · exact hd' a ha w hwa
  · exact ht a ha b hb hab w hwa

/-- The `edgeFinset` version of `mem_edgeSet_deleteIncidenceSet_two`. -/
theorem mem_edgeFinset_deleteIncidenceSet_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (v u : V) (e : Sym2 V) :
    e ∈ ((G.deleteIncidenceSet v).deleteIncidenceSet u).edgeFinset
      ↔ e ∈ G.edgeFinset ∧ v ∉ e ∧ u ∉ e := by
  simp only [SimpleGraph.mem_edgeFinset]
  exact mem_edgeSet_deleteIncidenceSet_two G v u e

/-- Membership in `matchingsOfCard`: a `k`-edge subset of the edge set that is a
matching. -/
theorem mem_matchingsOfCard {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    {s : Finset (Sym2 V)} :
    s ∈ G.matchingsOfCard k ↔ s ⊆ G.edgeFinset ∧ s.card = k ∧ IsMatchingSet s := by
  simp only [matchingsOfCard, Finset.mem_filter, Finset.mem_powersetCard]
  tauto

/-! ## Isomorphism invariance of `μ` -/

section Iso
variable {G} {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W}
  [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- A graph isomorphism carries `k`-matchings to `k`-matchings (image under `Sym2.map e`):
edges go to edges (`map_mem_edgeSet_iff`), the matching condition is preserved (`e` injective
on vertices), and the cardinality is unchanged (`Sym2.map e` injective). -/
theorem image_map_mem_matchingsOfCard (e : G ≃g H) {k : ℕ} {s : Finset (Sym2 V)}
    (hs : s ∈ G.matchingsOfCard k) : s.image (Sym2.map ⇑e) ∈ H.matchingsOfCard k := by
  rw [mem_matchingsOfCard] at hs ⊢
  obtain ⟨hsub, hcard, hmatch⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [SimpleGraph.mem_edgeFinset, e.map_mem_edgeSet_iff, ← SimpleGraph.mem_edgeFinset]
    exact hsub hy
  · rw [Finset.card_image_of_injective _ (Sym2.map.injective e.injective), hcard]
  · intro a ha b hb hab w hwa hwb
    rw [Finset.mem_image] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [Sym2.mem_map] at hwa hwb
    obtain ⟨wa, hwa', rfl⟩ := hwa
    obtain ⟨wb, hwb', hwe⟩ := hwb
    have hwab : wb = wa := e.injective hwe
    exact hmatch a' ha' b' hb' (fun h => hab (by rw [h])) wa hwa' (hwab ▸ hwb')

/-- The matching numbers are isomorphism invariants. -/
theorem matchingNumber_iso (e : G ≃g H) (k : ℕ) :
    G.matchingNumber k = H.matchingNumber k := by
  unfold matchingNumber
  apply Finset.card_bij'
    (fun s _ => s.image (Sym2.map ⇑e)) (fun t _ => t.image (Sym2.map ⇑e.symm))
  · -- left_inv (hi/hj are still metavariables here; the equation does not mention them)
    intro s _
    rw [Finset.image_image, ← Sym2.map_comp, e.symm_comp_self, Sym2.map_id, Finset.image_id]
  · -- right_inv
    intro t _
    rw [Finset.image_image, ← Sym2.map_comp,
        show (⇑e ∘ ⇑e.symm) = (id : W → W) from funext e.apply_symm_apply,
        Sym2.map_id, Finset.image_id]
  · -- hi
    exact fun s hs => image_map_mem_matchingsOfCard e hs
  · -- hj
    exact fun t ht => image_map_mem_matchingsOfCard e.symm ht

/-- **`μ` is an isomorphism invariant.** This lets the matching polynomial of each subtree
`T(G−u, b)` be read off through the structural iso `prependRoot_grows`, en route to the
root-decomposition product `μ(T−r) = X·∏_{b∼u} μ(T(G−u,b))`. -/
theorem matchingPoly_iso (e : G ≃g H) : G.matchingPoly = H.matchingPoly := by
  unfold matchingPoly
  rw [Fintype.card_congr e.toEquiv]
  exact Finset.sum_congr rfl fun k _ => by rw [matchingNumber_iso e k]

end Iso

/-- **`μ` is independent of the `Fintype`/`Decidable` instances.** All three are
`Subsingleton`s, so `μ(G)` computed with any pair of instance choices agree. This lets a
`matchingPoly` term produced by one elaboration path (e.g. an iso transport) be matched
against one produced by another (e.g. a direct `Σ`-decomposition) *propositionally*, without
forcing `isDefEq` to `whnf`-reduce the polynomial — which over a `Σ`-type blows the heartbeat
budget. -/
theorem matchingPoly_inst_irrel {V : Type*} (fV₁ fV₂ : Fintype V)
    (G : SimpleGraph V) (rG₁ rG₂ : DecidableRel G.Adj) :
    @matchingPoly V fV₁ G rG₁ = @matchingPoly V fV₂ G rG₂ := by
  cases Subsingleton.elim fV₁ fV₂
  cases Subsingleton.elim rG₁ rG₂
  rfl

/-- **The branch-(b) bijection.** For a neighbour `u ∼ v`, the `(k+1)`-matchings of
`G` that cover `v` via the edge `{v,u}` are in bijection (erase / insert that
edge) with the `k`-matchings of `G − v − u`:
```
  #{w ∈ matchingsOfCard (k+1) | s(v,u) ∈ w} = m_k(G − v − u).
```
This is the `v`-covering half of the matching recurrence. PROVEN 2026-05-30. -/
theorem card_filter_covering (G : SimpleGraph V) [DecidableRel G.Adj]
    {v u : V} (huv : G.Adj v u) (k : ℕ) :
    ((G.matchingsOfCard (k + 1)).filter (fun w => s(v, u) ∈ w)).card
      = ((G.deleteIncidenceSet v).deleteIncidenceSet u).matchingNumber k := by
  rw [matchingNumber]
  have hvmem : v ∈ s(v, u) := by simp
  have humem : u ∈ s(v, u) := by simp
  have heG : s(v, u) ∈ G.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact huv
  apply Finset.card_bij' (fun w _ => w.erase s(v, u)) (fun x _ => insert s(v, u) x)
  · -- left inverse : insert (erase) = id  on matchings covering v
    intro w hw
    rw [Finset.mem_filter] at hw
    exact Finset.insert_erase hw.2
  · -- right inverse : erase (insert) = id  on matchings of G − v − u
    intro x hx
    rw [mem_matchingsOfCard] at hx
    exact Finset.erase_insert (fun hmem =>
      ((mem_edgeFinset_deleteIncidenceSet_two G v u _).mp (hx.1 hmem)).2.1 hvmem)
  · -- hi : erase lands in the (k)-matchings of G − v − u
    intro w hw
    rw [Finset.mem_filter, mem_matchingsOfCard] at hw
    obtain ⟨⟨hsub, hcard, hmatch⟩, hcov⟩ := hw
    rw [mem_matchingsOfCard]
    refine ⟨fun f hf => ?_, ?_, hmatch.subset (Finset.erase_subset _ _)⟩
    · rw [Finset.mem_erase] at hf
      rw [mem_edgeFinset_deleteIncidenceSet_two]
      exact ⟨hsub hf.2, hmatch s(v, u) hcov f hf.2 (Ne.symm hf.1) v hvmem,
        hmatch s(v, u) hcov f hf.2 (Ne.symm hf.1) u humem⟩
    · rw [Finset.card_erase_of_mem hcov]; omega
  · -- hj : insert lands in the (k+1)-matchings of G covering v
    intro x hx
    rw [mem_matchingsOfCard] at hx
    obtain ⟨hsub, hcard, hmatch⟩ := hx
    have hnotin : s(v, u) ∉ x := fun hmem =>
      ((mem_edgeFinset_deleteIncidenceSet_two G v u _).mp (hsub hmem)).2.1 hvmem
    rw [Finset.mem_filter, mem_matchingsOfCard]
    refine ⟨⟨fun f hf => ?_, ?_, ?_⟩, Finset.mem_insert_self _ _⟩
    · rw [Finset.mem_insert] at hf
      rcases hf with rfl | hf
      · exact heG
      · exact ((mem_edgeFinset_deleteIncidenceSet_two G v u f).mp (hsub hf)).1
    · rw [Finset.card_insert_of_notMem hnotin, hcard]
    · refine hmatch.insert (fun f hf z hze hzf => ?_) (fun f hf z hzf hze => ?_)
      · have hf2 := (mem_edgeFinset_deleteIncidenceSet_two G v u f).mp (hsub hf)
        rcases Sym2.mem_iff.mp hze with rfl | rfl
        · exact hf2.2.1 hzf
        · exact hf2.2.2 hzf
      · have hf2 := (mem_edgeFinset_deleteIncidenceSet_two G v u f).mp (hsub hf)
        rcases Sym2.mem_iff.mp hze with rfl | rfl
        · exact hf2.2.1 hzf
        · exact hf2.2.2 hzf

/-- **The matching-number recurrence.** Deleting a vertex `v`:
```
  m_{k+1}(G) = m_{k+1}(G − v) + ∑_{u ∼ v} m_k(G − v − u).
```
A `(k+1)`-matching of `G` either avoids `v` (a `(k+1)`-matching of `G − v`,
branch (a)) or covers `v` via a unique edge `{v,u}` with `u ∼ v` (bijecting with
a `k`-matching of `G − v − u`, branch (b)). The covering matchings partition over
the neighbour `u` matched to `v` (unique, since a matching has one edge at `v`).
PROVEN 2026-05-30 — the count recurrence, both cordadas' engine. -/
theorem matchingNumber_recurrence (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (k : ℕ) :
    G.matchingNumber (k + 1)
      = (G.deleteIncidenceSet v).matchingNumber (k + 1)
        + ∑ u ∈ G.neighborFinset v,
            ((G.deleteIncidenceSet v).deleteIncidenceSet u).matchingNumber k := by
  classical
  -- the covering matchings = ⋃ over neighbours u of {matchings with edge {v,u}}
  have hcov : (G.matchingsOfCard (k + 1)).filter (fun s => ¬ ∀ e ∈ s, v ∉ e)
      = (G.neighborFinset v).biUnion
          (fun u => (G.matchingsOfCard (k + 1)).filter (fun s => s(v, u) ∈ s)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hsM, hcov⟩
      push_neg at hcov
      obtain ⟨e, hes, hve⟩ := hcov
      refine ⟨Sym2.Mem.other hve, ?_, hsM, ?_⟩
      · rw [SimpleGraph.mem_neighborFinset]
        have he : s(v, Sym2.Mem.other hve) = e := Sym2.other_spec hve
        have : e ∈ G.edgeFinset := (mem_matchingsOfCard.mp hsM).1 hes
        rwa [← he, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      · rw [Sym2.other_spec hve]; exact hes
    · rintro ⟨u, _, hsM, hvu⟩
      exact ⟨hsM, fun hall => hall s(v, u) hvu (Sym2.mem_mk_left v u)⟩
  -- distinct neighbours give disjoint covering-matching sets
  have hdisj : ∀ u ∈ G.neighborFinset v, ∀ u' ∈ G.neighborFinset v, u ≠ u' →
      Disjoint ((G.matchingsOfCard (k + 1)).filter (fun s => s(v, u) ∈ s))
        ((G.matchingsOfCard (k + 1)).filter (fun s => s(v, u') ∈ s)) := by
    intro u _ u' hu' huu'
    rw [Finset.disjoint_left]
    intro s hs hs'
    rw [Finset.mem_filter] at hs hs'
    obtain ⟨hsM, hvu⟩ := hs
    obtain ⟨_, hvu'⟩ := hs'
    obtain ⟨_, _, hmatch⟩ := mem_matchingsOfCard.mp hsM
    by_cases heq : s(v, u) = s(v, u')
    · rw [Sym2.eq_iff] at heq
      rcases heq with ⟨_, h⟩ | ⟨h, _⟩
      · exact huu' h
      · rw [SimpleGraph.mem_neighborFinset] at hu'; exact hu'.ne h
    · exact absurd (Sym2.mem_mk_left v u')
        (hmatch s(v, u) hvu s(v, u') hvu' heq v (Sym2.mem_mk_left v u))
  -- assemble: split M into avoiding / covering, identify each piece
  show (G.matchingsOfCard (k + 1)).card = _
  rw [(Finset.card_filter_add_card_filter_not (s := G.matchingsOfCard (k + 1))
        (fun w => ∀ e ∈ w, v ∉ e)).symm, matchingNumber_deleteIncidenceSet G v (k + 1)]
  congr 1
  rw [hcov, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl
    (fun u hu => card_filter_covering G (by rwa [SimpleGraph.mem_neighborFinset] at hu) k)

/-- **Polynomial recurrence (target — statement type-checks).** The count
recurrence lifts to the matching polynomial. Because `deleteIncidenceSet` keeps
the deleted vertex **isolated** (fixed vertex count `n`), each deletion pads `μ`
by a factor `X`, so the recurrence carries an `X²`:
```
  X² · μ(G) = X² · μ(G−v) − ∑_{u∼v} μ(G−v−u).
```
Verified numerically on the edge and `P₃`. Mathematically clean (index shift
`j = k−1`, the `X²` absorbing the `X^{-2}` from the shift); the Lean proof is a
`Finset.sum` reindexing over the `ℕ`-exponents `n − 2k` of the definition.
Equivalent (divide by `X²`) to the textbook `μ(G) = X·μ'(G−v) − Σ μ''(G−v−u)`
with true `(n−1)`/`(n−2)`-vertex deletions. Deferred. -/
def matchingPoly_recurrence_target (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Prop :=
    Polynomial.X ^ 2 * G.matchingPoly
        = Polynomial.X ^ 2 * (G.deleteIncidenceSet v).matchingPoly
          - ∑ u ∈ G.neighborFinset v,
              ((G.deleteIncidenceSet v).deleteIncidenceSet u).matchingPoly

/-! ## The clean recurrence via the monomer-dimer partition function -/

/-- **Matching-size bound (the one gap).** A `k`-matching covers `2k` distinct
vertices, so if `n < 2k` there is none: `m_k(G) = 0`. Each edge of a matching
contributes `2` distinct vertices (`Sym2.card_toFinset_of_not_isDiag`), pairwise
disjoint (the matching condition), so `card_biUnion` gives `2k` covered vertices,
`≤ n`. -/
theorem matchingNumber_eq_zero_of_card_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (h : Fintype.card V < 2 * k) : G.matchingNumber k = 0 := by
  rw [matchingNumber, Finset.card_eq_zero, matchingsOfCard, Finset.filter_eq_empty_iff]
  intro s hs hmatch
  rw [Finset.mem_powersetCard] at hs
  obtain ⟨hsub, hcard⟩ := hs
  have hdisj : (↑s : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf hef
    simp only [Finset.disjoint_left, Sym2.mem_toFinset]
    intro w hwe hwf
    exact hmatch e (Finset.mem_coe.mp he) f (Finset.mem_coe.mp hf) hef w hwe hwf
  have hcard2 : ∀ e ∈ s, e.toFinset.card = 2 := fun e he =>
    Sym2.card_toFinset_of_not_isDiag e
      (G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hsub he)))
  have hcov : (s.biUnion Sym2.toFinset).card = 2 * k := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard2, Finset.sum_const, hcard,
        smul_eq_mul, Nat.mul_comm]
  have hle : 2 * k ≤ Fintype.card V := by
    rw [← hcov, ← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  omega

/-- The **monomer-dimer partition function** `P(G, X) = ∑_k m_k(G) X^k` (dimers
weighted by `X`, monomers by `1`). Unlike `matchingPoly`, this carries no signs
and no fixed-`n` exponent shift, so its deletion recurrence is clean. -/
noncomputable def matchingPartition (G : SimpleGraph V) [DecidableRel G.Adj] :
    Polynomial ℝ :=
  ∑ k ∈ Finset.range (Fintype.card V + 1),
    Polynomial.C (G.matchingNumber k : ℝ) * Polynomial.X ^ k

/-- The coefficients of `P(G, X)` are exactly the matching numbers (the bound
kills everything past the range). -/
theorem matchingPartition_coeff (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    (G.matchingPartition).coeff d = (G.matchingNumber d : ℝ) := by
  rw [matchingPartition, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (Fintype.card V + 1)) d (fun k => (G.matchingNumber k : ℝ))]
  by_cases hd : d ∈ Finset.range (Fintype.card V + 1)
  · rw [if_pos hd]
  · rw [if_neg hd, Finset.mem_range, not_lt] at *
    rw [matchingNumber_eq_zero_of_card_lt G (by omega), Nat.cast_zero]

/-! ## The bridge `μ ↔ P`: `reflect_card μ(G) = P(G) ∘ (−X²)`

The matching polynomial `μ(G,x) = Σ (-1)^k m_k x^{n-2k}` and the partition function
`P(G,X) = Σ m_k X^k` are reverses of each other after the substitution `X ↦ -X²`:
reflecting `μ(G)` at degree `n` sends `X^{n-2k} ↦ X^{2k}`, exactly `P(G)` evaluated at
`-X²` (the sign `(-1)^k` coming from `(-X²)^k`). This is the load-bearing identity that
transfers the real-rootedness / root-bound of `P` (where the interlacing machinery lives)
to `μ` (where Heilmann–Lieb states the Ramanujan band), and it makes `μ` multiplicative on
disjoint unions out of the clean `P`-multiplicativity. -/
theorem matchingPoly_reflect_card (G : SimpleGraph V) [DecidableRel G.Adj] :
    Polynomial.reflect (Fintype.card V) (G.matchingPoly)
      = (G.matchingPartition).comp (C (-1) * X ^ 2) := by
  classical
  -- reflect and comp both distribute over the defining finite sums
  have refl_sum : ∀ (s : Finset ℕ) (f : ℕ → ℝ[X]),
      Polynomial.reflect (Fintype.card V) (∑ i ∈ s, f i)
        = ∑ i ∈ s, Polynomial.reflect (Fintype.card V) (f i) := by
    intro s f
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, reflect_add, ih, Finset.sum_insert ha]
  have comp_sum : ∀ (s : Finset ℕ) (f : ℕ → ℝ[X]),
      (∑ i ∈ s, f i).comp (C (-1) * X ^ 2) = ∑ i ∈ s, (f i).comp (C (-1) * X ^ 2) := by
    intro s f
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, add_comp, ih, Finset.sum_insert ha]
  -- the left side, term by term: `reflect (C c_k X^{n-2k}) = C c_k X^{2k}`
  have hL : Polynomial.reflect (Fintype.card V) (G.matchingPoly)
      = ∑ k ∈ Finset.range (Fintype.card V / 2 + 1),
          C ((-1 : ℝ) ^ k * (G.matchingNumber k : ℝ)) * X ^ (2 * k) := by
    rw [matchingPoly, refl_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [reflect_C_mul_X_pow, revAt_le (Nat.sub_le _ _)]
    congr 2
    omega
  -- the right side, term by term: `(C m_k X^k) ∘ (-X²) = C ((-1)^k m_k) X^{2k}`,
  -- with the upper terms (`2k > n`) vanishing because `m_k = 0` there
  have hR : (G.matchingPartition).comp (C (-1) * X ^ 2)
      = ∑ k ∈ Finset.range (Fintype.card V / 2 + 1),
          C ((-1 : ℝ) ^ k * (G.matchingNumber k : ℝ)) * X ^ (2 * k) := by
    rw [matchingPartition, comp_sum,
        ← Finset.sum_subset (s₁ := Finset.range (Fintype.card V / 2 + 1))
          (s₂ := Finset.range (Fintype.card V + 1))
          (by intro x hx; rw [Finset.mem_range] at hx ⊢; omega)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comp, C_comp, pow_comp, X_comp, mul_pow, ← C_pow, ← pow_mul, C_mul]
      ring
    · intro k _ hk2
      rw [Finset.mem_range, not_lt] at hk2
      rw [matchingNumber_eq_zero_of_card_lt G (by omega), Nat.cast_zero]
      simp
  rw [hL, hR]

/-- **The clean recurrence.** Deleting a vertex `v`:
```
  P(G) = P(G − v) + X · ∑_{u ∼ v} P(G − v − u).
```
No signs, no `X²`: the partition function lifts the count recurrence directly.
Proved coefficient-wise via `matchingNumber_recurrence`. PROVEN 2026-05-30. -/
theorem matchingPartition_recurrence (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.matchingPartition
      = (G.deleteIncidenceSet v).matchingPartition
        + Polynomial.X * ∑ u ∈ G.neighborFinset v,
            ((G.deleteIncidenceSet v).deleteIncidenceSet u).matchingPartition := by
  ext d
  rw [Polynomial.coeff_add, matchingPartition_coeff, matchingPartition_coeff]
  rcases d with _ | e
  · simp [matchingNumber_zero]
  · rw [Polynomial.coeff_X_mul, Polynomial.finsetSum_coeff]
    simp only [matchingPartition_coeff]
    rw [matchingNumber_recurrence G v e]
    push_cast
    ring

/-! ## The signed vertex-deletion recurrence for `μ` (lifts the clean `P` recurrence) -/

/-- `reflect` distributes over a finite sum. -/
theorem reflect_finsetSum {ι : Type*} (N : ℕ) (s : Finset ι) (f : ι → ℝ[X]) :
    Polynomial.reflect N (∑ i ∈ s, f i) = ∑ i ∈ s, Polynomial.reflect N (f i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, reflect_add, ih, Finset.sum_insert ha]

/-- `comp` distributes over a finite sum (in the composed polynomial). -/
theorem comp_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) (r : ℝ[X]) :
    (∑ i ∈ s, f i).comp r = ∑ i ∈ s, (f i).comp r := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, add_comp, ih, Finset.sum_insert ha]

/-- Reflecting `X²·μ(G)` at degree `n+2` lands on `reflect_n μ(G)` (both `= P(G)∘(−X²)`):
the extra `X²` is exactly absorbed by the two-larger reflection degree. -/
theorem reflect_card_add_two_Xsq_mul (G : SimpleGraph V) [DecidableRel G.Adj] :
    Polynomial.reflect (Fintype.card V + 2) (X ^ 2 * G.matchingPoly)
      = Polynomial.reflect (Fintype.card V) G.matchingPoly := by
  rw [matchingPoly, Finset.mul_sum, reflect_finsetSum, reflect_finsetSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [mul_left_comm, ← pow_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
      revAt_le (by omega), revAt_le (Nat.sub_le _ _)]
  congr 2
  omega

/-- Reflecting `μ(G)` at degree `n+2` introduces one factor `X²` over `reflect_n μ(G)`. -/
theorem reflect_card_add_two (G : SimpleGraph V) [DecidableRel G.Adj] :
    Polynomial.reflect (Fintype.card V + 2) G.matchingPoly
      = X ^ 2 * Polynomial.reflect (Fintype.card V) G.matchingPoly := by
  rw [matchingPoly, reflect_finsetSum, reflect_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [reflect_C_mul_X_pow, reflect_C_mul_X_pow, revAt_le (by omega),
      revAt_le (Nat.sub_le _ _), mul_left_comm, ← pow_add]
  congr 2
  omega

/-- **The signed vertex-deletion recurrence** `X²·μ(G) = X²·μ(G−v) − Σ_{u∼v} μ(G−v−u)`
(`matchingPoly_recurrence_target`). Proved by reflecting at degree `n+2` (an injection,
via `reflect_reflect`) and using the `μ ↔ P` bridge to reduce to the already-proved clean
partition recurrence `matchingPartition_recurrence`, pushed through `comp (−X²)`. This is
the engine of Godsil's identity `μ(G)·μ(T−r) = μ(G−a)·μ(T)`, hence of the path-tree
divisibility `μ(G) ∣ μ(T(G,u))`. -/
theorem matchingPoly_recurrence (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    matchingPoly_recurrence_target G v := by
  unfold matchingPoly_recurrence_target
  have hinj : Function.Injective
      (Polynomial.reflect (Fintype.card V + 2) : ℝ[X] → ℝ[X]) := fun p q hpq => by
    have h := congrArg (Polynomial.reflect (Fintype.card V + 2)) hpq
    rwa [reflect_reflect, reflect_reflect] at h
  rw [eq_sub_iff_add_eq]
  apply hinj
  rw [reflect_add, reflect_finsetSum]
  simp only [reflect_card_add_two_Xsq_mul, reflect_card_add_two, matchingPoly_reflect_card]
  rw [matchingPartition_recurrence G v, add_comp, mul_comp, X_comp, comp_finsetSum,
      ← Finset.mul_sum]
  simp only [C_neg, C_1]
  ring

/-- **Divisibility transfer — the algebraic core of Godsil's path-tree induction.**
Given Godsil's identity `μ(G)·μ(T−r) = μ(G−a)·μ(T)` (`hid`) and the inductive divisibility
`μ(G−a) ∣ μ(T−r)` (`hdvd`), with `μ(G−a) ≠ 0`, conclude `μ(G) ∣ μ(T)`. Pure `ℝ[X]`
cancellation: `μ(T−r) = μ(G−a)·Q ⟹ μ(G−a)·μ(T) = μ(G−a)·(μ(G)·Q)`, cancel `μ(G−a)`. -/
theorem dvd_of_godsil_identity {μG μGa μT μTr : ℝ[X]} (hGa : μGa ≠ 0)
    (hid : μG * μTr = μGa * μT) (hdvd : μGa ∣ μTr) : μG ∣ μT := by
  obtain ⟨Q, hQ⟩ := hdvd
  refine ⟨Q, mul_left_cancel₀ hGa ?_⟩
  rw [← hid, hQ]; ring

/-- **The Σ/∏ rearrangement at the inductive step of Godsil's identity.** Indexing over the
neighbours `b ∼ u`, write `μGu = μ(G−u)`, `d b = μ((G−u)−b)`, `t b = μ(T(G−u,b))` and
`s b = μ(T(G−u,b) − r_b)`. Given the per-neighbour inductive hypothesis
`μGu · s b = d b · t b` (Godsil's identity on the smaller graph `G−u` at `b`), the tree-side
sum `μGu · Σ_b s b·∏_{b'≠b} t b'` collapses to `(Σ_b d b)·∏_b t b` — exactly what equates the
tree recurrence's defect term with the `G` recurrence's after the root decomposition `(D)`.
Each summand: `μGu·(s b·∏_{≠b} t) = (d b·t b)·∏_{≠b} t = d b·∏_all t` via `mul_prod_erase`. -/
theorem godsil_sum_prod_rearrange {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (μGu : R) (d s t : ι → R)
    (hIH : ∀ b, μGu * s b = d b * t b) :
    μGu * ∑ b, s b * ∏ b' ∈ Finset.univ.erase b, t b' = (∑ b, d b) * ∏ b, t b := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← mul_assoc, hIH, mul_assoc, Finset.mul_prod_erase _ t (Finset.mem_univ b)]

/-! ## Heilmann–Lieb by interlacing — the summit (base case + spine) -/

/-- `P(⊥) = 1`: the edgeless graph has only the empty matching. The base of the
edge-count induction for Heilmann–Lieb. -/
theorem matchingPartition_bot : (⊥ : SimpleGraph V).matchingPartition = 1 := by
  have h0 : ∀ k ∈ Finset.range (Fintype.card V + 1), k ≠ 0 →
      Polynomial.C (((⊥ : SimpleGraph V).matchingNumber k : ℝ)) * Polynomial.X ^ k = 0 := by
    intro k _ hk; rw [matchingNumber_bot, if_neg hk]; simp
  rw [matchingPartition,
      Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos _)) h0,
      matchingNumber_bot]
  simp

/-- **Base case of Heilmann–Lieb.** `P(⊥) = 1` is real-rooted (a nonzero
constant splits trivially). The induction (on edge count, via
`matchingPartition_recurrence`) builds from here. -/
theorem matchingPartition_bot_realRooted :
    MSS.RealRooted ((⊥ : SimpleGraph V).matchingPartition) := by
  rw [matchingPartition_bot]; exact MSS.realRooted_one

/-- **Heilmann–Lieb (target — the summit).** Every graph's matching partition
function is real-rooted, with roots in the band that maps to `[−2√(Δ−1),
2√(Δ−1)]` for the matching polynomial — i.e. `MSS.BoundedBy`. Proof: induction on
edge count via `matchingPartition_recurrence`, where the recurrence terms share a
common interlacer, so the sum stays real-rooted (the convex cone + sign-change
muscle of `RealStable`, once the HKO mortar `f_alternates_at_g_roots` is closed).
Base case `matchingPartition_bot_realRooted` is done. Deferred — the dependency
chain (HKO mortar → common-interlacer cone → this induction) is the remaining
climb. -/
def matchingPartition_realRooted_target (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
    MSS.RealRooted (G.matchingPartition)

/-! ## Targets of the right cordada (stubs) -/

/-! **Matching recurrence (TARGET — NOT formalized).** Deleting a
vertex `v`: `μ(G) = X·μ(G−v) − Σ_{u∼v} μ(G−v−u)`. Combinatorially, a `k`-matching
either avoids `v` (→ a `k`-matching of `G−v`) or uses one edge `{v,u}` (→ a
`(k−1)`-matching of `G−v−u`). This is the recurrence that drives the interlacing
induction. Requires vertex-deletion machinery + the count decomposition. Deferred.
(Was a vacuous `theorem … : True := trivial` stub; removed for honesty.) -/

/-! **Interlacing step (TARGET — NOT formalized).** `μ(G−v)` interlaces `μ(G)`
(`RealStable.Interlace`), so induction on `|V|` from the `matchingPoly_bot_realRooted`
base, through the matching recurrence, yields Heilmann–Lieb. This is where the right
cordada consumes the convex cone and sign-change muscle of `RealStable`. Deferred.
(Was a vacuous `theorem … : True := trivial` stub; removed for honesty.) -/

/-- **Heilmann–Lieb target (stub).** The matching polynomial of a finite graph of
max degree `Δ ≥ 2` is `MSS.BoundedBy (2√(Δ−1))`: real-rooted with every root in
`[−2√(Δ−1), 2√(Δ−1)]`. Same `BoundedBy` predicate as the spectral/RH side.

**The interlacing engine for this is already formalised, sorry-free, in Lean 4:**
`PerAlexandersson/RealRooted` (GitHub) — its `Compatible.of_commonInterleaver` and
`pairwiseCompatible_of_commonLeftInterleaver` are exactly "a common interlacer of
a family ⟹ every positive combination (hence the sum / average) is real-rooted"
(Chudnovsky–Seymour), the heart of Heilmann–Lieb. **We deliberately do NOT
re-formalise that engine** (catalog-first: it exists). The novel contribution
here is the *graph side*: `matchingPartition` and its clean recurrence
`matchingPartition_recurrence` (`P(G) = P(G−v) + X·∑ P(G−v−u)`), which supplies
the common-interlacer structure that engine consumes. Closing this would bridge
our recurrence to that external machinery (toolchain alignment / port of the few
key lemmas); the math is settled. Deferred by design. -/
def heilmann_lieb_target : Prop :=
    2 ≤ G.maxDegree → MSS.BoundedBy (G.matchingPoly) (2 * Real.sqrt ((G.maxDegree : ℝ) - 1))

/-! **MSS keystone (TARGET — NOT formalized).** The expectation over uniform random `±1` edge
signings of the characteristic polynomial of the signed adjacency matrix equals
the matching polynomial: `E_s[charpoly(A_s)] = matchingPoly G`. Combined with
Heilmann–Lieb (`BoundedBy`) and the interlacing-family method, a single signing's
characteristic polynomial stays in the Ramanujan band, yielding a Ramanujan
2-lift — hence Ramanujan graphs of every degree. This is where the two cordadas
meet. Deferred. (Was a vacuous `theorem … : True := trivial` stub; removed for honesty.) -/

end SimpleGraph
