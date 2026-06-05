/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import MatchingPoly
public import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Multiplicativity of the matching polynomial on disjoint unions (Godsil L25.3.1)

`μ[G ⊕ H] = μ[G] · μ[H]` for the disjoint sum `G ⊕g H : SimpleGraph (V ⊕ W)`.

This is Lemma 25.3.1 of the Godsil path-tree route to Heilmann–Lieb: a matching of a
disjoint union splits uniquely into a matching of each part, so the matching numbers
convolve, `m_k(G ⊕ H) = ∑_{j} m_j(G) · m_{k-j}(H)`, and the matching polynomials
multiply. It is the lemma that turns the path-tree decomposition
`T_a(G) − a = ⊔_{b∼a} T_b(G−a)` into `μ[T_a(G) − a] = ∏_{b∼a} μ[T_b(G−a)]`.

## Status (in progress)
* `mem_edgeSet_sum`: every edge of `G ⊕g H` is the `inl`-image of a `G`-edge or the
  `inr`-image of an `H`-edge — PROVEN. The combinatorial foundation of the split.
* `matchingNumber_sum`: the convolution `m_k(G ⊕ H) = ∑_{j≤k} m_j(G)·m_{k-j}(H)` —
  PROVEN via a `Finset.card_bij'` between matchings of the sum and pairs of matchings
  (`combineEdges` / `splitL`,`splitR`).
* `matchingPartition_sum`: `P(G ⊕ H) = P(G)·P(H)` (clean Cauchy product) — PROVEN.
* `matchingPoly_sum`: `μ[G ⊕ H] = μ[G]·μ[H]` — PROVEN, by lifting `matchingPartition_sum`
  through the `μ ↔ P` bridge (`matchingPoly_reflect_card`) and `reverse_mul_of_domain`.
  This is the lemma the path-tree decomposition `T_a(G) − a = ⊔_{b∼a} T_b(G−a)` needs to
  become a product `μ[T_a(G) − a] = ∏_{b∼a} μ[T_b(G−a)]`.
-/

@[expose] public section

namespace SimpleGraph

open Finset Polynomial

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- **Edges of a disjoint sum split.** Every edge of `G ⊕g H` is either the `inl`-image
of an edge of `G` or the `inr`-image of an edge of `H` — there are no cross edges. The
combinatorial foundation of the matching convolution. -/
theorem mem_edgeSet_sum {e : Sym2 (V ⊕ W)} :
    e ∈ (G.sum H).edgeSet ↔
      (∃ eV ∈ G.edgeSet, e = eV.map Sum.inl) ∨ (∃ eW ∈ H.edgeSet, e = eW.map Sum.inr) := by
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ p q =>
      rw [mem_edgeSet] at he
      cases p <;> cases q
      · rename_i a b; exact Or.inl ⟨s(a, b), by rw [mem_edgeSet]; exact he, by rw [Sym2.map_mk]⟩
      · exact absurd he (by simp [SimpleGraph.sum])
      · exact absurd he (by simp [SimpleGraph.sum])
      · rename_i a b; exact Or.inr ⟨s(a, b), by rw [mem_edgeSet]; exact he, by rw [Sym2.map_mk]⟩
  · rintro (⟨eV, heV, rfl⟩ | ⟨eW, heW, rfl⟩)
    · induction eV using Sym2.ind with
      | _ a b => rw [Sym2.map_mk, mem_edgeSet]; rw [mem_edgeSet] at heV; exact heV
    · induction eW using Sym2.ind with
      | _ a b => rw [Sym2.map_mk, mem_edgeSet]; rw [mem_edgeSet] at heW; exact heW

/-! ## The matching convolution -/

section Convolution

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Combine a `G`-edge finset and an `H`-edge finset into an edge finset of `G ⊕g H`,
by tagging each side with `inl` / `inr`. -/
def combineEdges (a : Finset (Sym2 V)) (b : Finset (Sym2 W)) :
    Finset (Sym2 (V ⊕ W)) :=
  a.image (Sym2.map Sum.inl) ∪ b.image (Sym2.map Sum.inr)

/-- An `inl`-tagged edge and an `inr`-tagged edge are never equal. -/
theorem map_inl_ne_map_inr (eV : Sym2 V) (eW : Sym2 W) :
    Sym2.map Sum.inl eV ≠ Sym2.map Sum.inr eW := by
  induction eV using Sym2.ind with
  | _ a b =>
    induction eW using Sym2.ind with
    | _ c d =>
      rw [Sym2.map_mk, Sym2.map_mk]
      simp [Sym2.eq_iff]

theorem mem_combineEdges {a : Finset (Sym2 V)} {b : Finset (Sym2 W)} {x : Sym2 (V ⊕ W)} :
    x ∈ combineEdges a b ↔
      (∃ eV ∈ a, x = eV.map Sum.inl) ∨ (∃ eW ∈ b, x = eW.map Sum.inr) := by
  simp only [combineEdges, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨eV, h, rfl⟩ | ⟨eW, h, rfl⟩)
    · exact Or.inl ⟨eV, h, rfl⟩
    · exact Or.inr ⟨eW, h, rfl⟩
  · rintro (⟨eV, h, rfl⟩ | ⟨eW, h, rfl⟩)
    · exact Or.inl ⟨eV, h, rfl⟩
    · exact Or.inr ⟨eW, h, rfl⟩

/-- The two tagged images are disjoint, so the combined edge finset has additive card. -/
theorem card_combineEdges (a : Finset (Sym2 V)) (b : Finset (Sym2 W)) :
    (combineEdges a b).card = a.card + b.card := by
  rw [combineEdges, Finset.card_union_of_disjoint, Finset.card_image_of_injective _
        (Sym2.map.injective Sum.inl_injective),
      Finset.card_image_of_injective _ (Sym2.map.injective Sum.inr_injective)]
  rw [Finset.disjoint_left]
  rintro x hx hx'
  rw [Finset.mem_image] at hx hx'
  obtain ⟨eV, _, rfl⟩ := hx
  obtain ⟨eW, _, he⟩ := hx'
  exact map_inl_ne_map_inr eV eW he.symm

/-! ### Vertex-membership of tagged edges -/

@[simp] theorem inl_mem_map_inl (v : V) (eV : Sym2 V) :
    (Sum.inl v : V ⊕ W) ∈ Sym2.map Sum.inl eV ↔ v ∈ eV := by
  rw [Sym2.mem_map]
  exact ⟨fun ⟨a, ha, h⟩ => (Sum.inl_injective h) ▸ ha, fun h => ⟨v, h, rfl⟩⟩

@[simp] theorem inr_mem_map_inr (w : W) (eW : Sym2 W) :
    (Sum.inr w : V ⊕ W) ∈ Sym2.map Sum.inr eW ↔ w ∈ eW := by
  rw [Sym2.mem_map]
  exact ⟨fun ⟨a, ha, h⟩ => (Sum.inr_injective h) ▸ ha, fun h => ⟨w, h, rfl⟩⟩

@[simp] theorem inr_notMem_map_inl (w : W) (eV : Sym2 V) :
    (Sum.inr w : V ⊕ W) ∉ Sym2.map Sum.inl eV := by
  rw [Sym2.mem_map]; rintro ⟨a, _, h⟩; exact absurd h (by simp)

@[simp] theorem inl_notMem_map_inr (v : V) (eW : Sym2 W) :
    (Sum.inl v : V ⊕ W) ∉ Sym2.map Sum.inr eW := by
  rw [Sym2.mem_map]; rintro ⟨a, _, h⟩; exact absurd h (by simp)

variable (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]

noncomputable instance : DecidableRel (G.sum H).Adj := fun _ _ => Classical.propDecidable _

/-- The `G`-part of an edge set of the sum: the `G`-edges whose `inl`-tag lies in `s`. -/
def splitL (s : Finset (Sym2 (V ⊕ W))) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => Sym2.map Sum.inl e ∈ s)

/-- The `H`-part of an edge set of the sum. -/
def splitR (s : Finset (Sym2 (V ⊕ W))) : Finset (Sym2 W) :=
  H.edgeFinset.filter (fun e => Sym2.map Sum.inr e ∈ s)

theorem mem_splitL {s : Finset (Sym2 (V ⊕ W))} {eV : Sym2 V} :
    eV ∈ splitL G s ↔ eV ∈ G.edgeFinset ∧ Sym2.map Sum.inl eV ∈ s := Finset.mem_filter

theorem mem_splitR {s : Finset (Sym2 (V ⊕ W))} {eW : Sym2 W} :
    eW ∈ splitR H s ↔ eW ∈ H.edgeFinset ∧ Sym2.map Sum.inr eW ∈ s := Finset.mem_filter

theorem combineEdges_subset {a : Finset (Sym2 V)} {b : Finset (Sym2 W)}
    (ha : a ⊆ G.edgeFinset) (hb : b ⊆ H.edgeFinset) :
    combineEdges a b ⊆ (G.sum H).edgeFinset := by
  intro x hx
  rw [mem_combineEdges] at hx
  rw [SimpleGraph.mem_edgeFinset, mem_edgeSet_sum]
  rcases hx with ⟨eV, h, rfl⟩ | ⟨eW, h, rfl⟩
  · exact Or.inl ⟨eV, by rw [← SimpleGraph.mem_edgeFinset]; exact ha h, rfl⟩
  · exact Or.inr ⟨eW, by rw [← SimpleGraph.mem_edgeFinset]; exact hb h, rfl⟩

theorem splitL_combineEdges {a : Finset (Sym2 V)} {b : Finset (Sym2 W)}
    (ha : a ⊆ G.edgeFinset) : splitL G (combineEdges a b) = a := by
  ext eV
  rw [mem_splitL, mem_combineEdges]
  constructor
  · rintro ⟨_, (⟨eV', h, he⟩ | ⟨eW, h, he⟩)⟩
    · rwa [Sym2.map.injective Sum.inl_injective he]
    · exact absurd he (map_inl_ne_map_inr eV eW)
  · exact fun h => ⟨ha h, Or.inl ⟨eV, h, rfl⟩⟩

theorem splitR_combineEdges {a : Finset (Sym2 V)} {b : Finset (Sym2 W)}
    (hb : b ⊆ H.edgeFinset) : splitR H (combineEdges a b) = b := by
  ext eW
  rw [mem_splitR, mem_combineEdges]
  constructor
  · rintro ⟨_, (⟨eV, h, he⟩ | ⟨eW', h, he⟩)⟩
    · exact absurd he.symm (map_inl_ne_map_inr eV eW)
    · rwa [Sym2.map.injective Sum.inr_injective he]
  · exact fun h => ⟨hb h, Or.inr ⟨eW, h, rfl⟩⟩

theorem combineEdges_splitL_splitR {s : Finset (Sym2 (V ⊕ W))}
    (hs : s ⊆ (G.sum H).edgeFinset) : combineEdges (splitL G s) (splitR H s) = s := by
  ext x
  rw [mem_combineEdges]
  constructor
  · rintro (⟨eV, h, rfl⟩ | ⟨eW, h, rfl⟩)
    · exact (mem_splitL G).mp h |>.2
    · exact (mem_splitR H).mp h |>.2
  · intro hx
    have hxe := hs hx
    rw [SimpleGraph.mem_edgeFinset, mem_edgeSet_sum] at hxe
    rcases hxe with ⟨eV, heV, rfl⟩ | ⟨eW, heW, rfl⟩
    · exact Or.inl ⟨eV, (mem_splitL G).mpr ⟨by rwa [SimpleGraph.mem_edgeFinset], hx⟩, rfl⟩
    · exact Or.inr ⟨eW, (mem_splitR H).mpr ⟨by rwa [SimpleGraph.mem_edgeFinset], hx⟩, rfl⟩

theorem isMatchingSet_splitL {s : Finset (Sym2 (V ⊕ W))} (hs : IsMatchingSet s) :
    IsMatchingSet (splitL G s) := by
  intro e he f hf hef v hve hvf
  rw [mem_splitL] at he hf
  exact hs _ he.2 _ hf.2 (fun h => hef (Sym2.map.injective Sum.inl_injective h)) (Sum.inl v)
    ((inl_mem_map_inl v e).mpr hve) ((inl_mem_map_inl v f).mpr hvf)

theorem isMatchingSet_splitR {s : Finset (Sym2 (V ⊕ W))} (hs : IsMatchingSet s) :
    IsMatchingSet (splitR H s) := by
  intro e he f hf hef w hwe hwf
  rw [mem_splitR] at he hf
  exact hs _ he.2 _ hf.2 (fun h => hef (Sym2.map.injective Sum.inr_injective h)) (Sum.inr w)
    ((inr_mem_map_inr w e).mpr hwe) ((inr_mem_map_inr w f).mpr hwf)

theorem isMatchingSet_combineEdges {a : Finset (Sym2 V)} {b : Finset (Sym2 W)}
    (ha : IsMatchingSet a) (hb : IsMatchingSet b) : IsMatchingSet (combineEdges a b) := by
  intro e he f hf hef x hxe hxf
  rw [mem_combineEdges] at he hf
  rcases he with ⟨eV, heV, rfl⟩ | ⟨eW, heW, rfl⟩ <;>
    rcases hf with ⟨fV, hfV, rfl⟩ | ⟨fW, hfW, rfl⟩
  · -- inl, inl
    induction x using Sum.rec with
    | inl v =>
      rw [inl_mem_map_inl] at hxe hxf
      exact ha _ heV _ hfV (fun h => hef (by rw [h])) v hxe hxf
    | inr w => exact absurd hxe (inr_notMem_map_inl w eV)
  · -- inl, inr
    induction x using Sum.rec with
    | inl v => exact absurd hxf (inl_notMem_map_inr v fW)
    | inr w => exact absurd hxe (inr_notMem_map_inl w eV)
  · -- inr, inl
    induction x using Sum.rec with
    | inl v => exact absurd hxe (inl_notMem_map_inr v eW)
    | inr w => exact absurd hxf (inr_notMem_map_inl w fV)
  · -- inr, inr
    induction x using Sum.rec with
    | inl v => exact absurd hxe (inl_notMem_map_inr v eW)
    | inr w =>
      rw [inr_mem_map_inr] at hxe hxf
      exact hb _ heW _ hfW (fun h => hef (by rw [h])) w hxe hxf

/-- **The matching convolution.** A matching of the disjoint sum splits uniquely into a
matching of each part, so the matching numbers convolve:
`m_k(G ⊕ H) = ∑_{j ≤ k} m_j(G) · m_{k-j}(H)`. -/
theorem matchingNumber_sum (k : ℕ) :
    (G.sum H).matchingNumber k
      = ∑ j ∈ Finset.range (k + 1), G.matchingNumber j * H.matchingNumber (k - j) := by
  have key : ((G.sum H).matchingsOfCard k).card
      = ((Finset.range (k + 1)).sigma
          (fun j => (G.matchingsOfCard j) ×ˢ (H.matchingsOfCard (k - j)))).card := by
    apply Finset.card_bij'
      (fun s _ => (⟨(splitL G s).card, (splitL G s, splitR H s)⟩ :
        Σ _ : ℕ, Finset (Sym2 V) × Finset (Sym2 W)))
      (fun p _ => combineEdges p.2.1 p.2.2)
    · -- hi : i lands in the sigma
      intro s hs
      rw [mem_matchingsOfCard] at hs
      obtain ⟨hsub, hcard, hmatch⟩ := hs
      have hsum : (splitL G s).card + (splitR H s).card = k := by
        rw [← card_combineEdges, combineEdges_splitL_splitR G H hsub, hcard]
      refine Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · show (splitL G s).card < k + 1; omega
      · rw [mem_matchingsOfCard]
        exact ⟨Finset.filter_subset _ _, rfl, isMatchingSet_splitL G hmatch⟩
      · rw [mem_matchingsOfCard]
        refine ⟨Finset.filter_subset _ _, ?_, isMatchingSet_splitR H hmatch⟩
        show (splitR H s).card = k - (splitL G s).card; omega
    · -- hj : j lands in the matchings of the sum
      intro p hp
      rw [Finset.mem_sigma, Finset.mem_product] at hp
      obtain ⟨hj, ha, hb⟩ := hp
      rw [mem_matchingsOfCard] at ha hb ⊢
      obtain ⟨hasub, hacard, hamatch⟩ := ha
      obtain ⟨hbsub, hbcard, hbmatch⟩ := hb
      refine ⟨combineEdges_subset G H hasub hbsub, ?_, isMatchingSet_combineEdges hamatch hbmatch⟩
      rw [card_combineEdges, hacard, hbcard]
      rw [Finset.mem_range] at hj; omega
    · -- left_inv
      intro s hs
      rw [mem_matchingsOfCard] at hs
      exact combineEdges_splitL_splitR G H hs.1
    · -- right_inv
      intro p hp
      rw [Finset.mem_sigma, Finset.mem_product] at hp
      obtain ⟨_, ha, hb⟩ := hp
      obtain ⟨j, a, b⟩ := p
      rw [mem_matchingsOfCard] at ha hb
      simp only
      rw [splitL_combineEdges G ha.1, splitR_combineEdges H hb.1, ha.2.1]
  change ((G.sum H).matchingsOfCard k).card = _
  rw [key, Finset.card_sigma]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [Finset.card_product, matchingNumber]

/-- **Multiplicativity of the monomer–dimer partition function** on disjoint unions:
`P(G ⊕ H) = P(G) · P(H)`. A clean Cauchy product — the convolution of matching numbers
is exactly the coefficient product. (The signless companion of Godsil L25.3.1.) -/
theorem matchingPartition_sum :
    (G.sum H).matchingPartition = G.matchingPartition * H.matchingPartition := by
  ext d
  rw [matchingPartition_coeff, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, matchingNumber_sum]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by rw [matchingPartition_coeff, matchingPartition_coeff]

/-- **Multiplicativity of the matching polynomial on disjoint unions** (Godsil L25.3.1):
`μ[G ⊕ H] = μ[G] · μ[H]`. Lifts the clean partition multiplicativity `matchingPartition_sum`
through the `μ ↔ P` bridge `matchingPoly_reflect_card`: at the common degree the reflection
of `μ` is `P ∘ (−X²)`, and reflecting the product turns it into a `reverse`, which is
multiplicative over the domain `ℝ[X]` (`reverse_mul_of_domain`). The Godsil decomposition
`T_a(G) − a = ⊔_{b∼a} T_b(G−a)` then becomes `μ[T_a(G) − a] = ∏_{b∼a} μ[T_b(G−a)]`. -/
theorem matchingPoly_sum :
    (G.sum H).matchingPoly = G.matchingPoly * H.matchingPoly := by
  have hrev : ∀ p : ℝ[X], p.reverse = Polynomial.reflect p.natDegree p := fun _ => rfl
  have hdeg : (G.matchingPoly * H.matchingPoly).natDegree
      = Fintype.card V + Fintype.card W := by
    rw [Polynomial.natDegree_mul (matchingPoly_monic G).ne_zero (matchingPoly_monic H).ne_zero,
        matchingPoly_natDegree, matchingPoly_natDegree]
  have hcard : Fintype.card (V ⊕ W) = Fintype.card V + Fintype.card W := Fintype.card_sum
  have key : Polynomial.reflect (Fintype.card (V ⊕ W)) ((G.sum H).matchingPoly)
      = Polynomial.reflect (Fintype.card (V ⊕ W)) (G.matchingPoly * H.matchingPoly) := by
    rw [matchingPoly_reflect_card, hcard, ← hdeg, ← hrev (G.matchingPoly * H.matchingPoly),
        reverse_mul_of_domain, hrev G.matchingPoly, hrev H.matchingPoly]
    simp only [matchingPoly_natDegree]
    rw [matchingPoly_reflect_card, matchingPoly_reflect_card, ← mul_comp, ← matchingPartition_sum]
  have h := congrArg (Polynomial.reflect (Fintype.card (V ⊕ W))) key
  rwa [reflect_reflect, reflect_reflect] at h

end Convolution

/-! ## Indexed disjoint union of graphs (the `n`-ary generalisation of `SimpleGraph.sum`)

Toward the path-tree root decomposition `T(G,u) − r ≅ ⊔_{b∼u} T(G−u, b)`: we need the
disjoint union of a *family* of graphs and the multiplicativity of `μ` over it. Mathlib has
only the binary `SimpleGraph.sum`, so we build the `Σ`-indexed union. -/

section SigmaFamily

variable {ι : Type*} {β : ι → Type*}

/-- The **disjoint union of an indexed family of graphs** on `Σ i, β i`: two vertices are
adjacent iff they share a fibre `i` and are adjacent there. (Witness-style, avoiding `▸`.) -/
def sigmaFamily (G : ∀ i, SimpleGraph (β i)) : SimpleGraph (Σ i, β i) where
  Adj x y := ∃ (i : ι) (a b : β i), (G i).Adj a b ∧ x = ⟨i, a⟩ ∧ y = ⟨i, b⟩
  symm := by
    rintro x y ⟨i, a, b, hab, rfl, rfl⟩
    exact ⟨i, b, a, hab.symm, rfl, rfl⟩
  loopless := ⟨fun x hx => by
    obtain ⟨i, a, b, hab, rfl, hy⟩ := hx
    rw [Sigma.mk.injEq] at hy
    obtain ⟨_, hab2⟩ := hy
    obtain rfl := eq_of_heq hab2
    exact (G i).loopless.irrefl a hab⟩

@[simp] theorem sigmaFamily_adj (G : ∀ i, SimpleGraph (β i)) {i : ι} (a b : β i) :
    (sigmaFamily G).Adj ⟨i, a⟩ ⟨i, b⟩ ↔ (G i).Adj a b := by
  constructor
  · rintro ⟨i', a', b', hab, hx, hy⟩
    rw [Sigma.mk.injEq] at hx hy
    obtain ⟨rfl, ha⟩ := hx
    obtain ⟨_, hb⟩ := hy
    rw [eq_of_heq ha, eq_of_heq hb]
    exact hab
  · intro hab; exact ⟨i, a, b, hab, rfl, rfl⟩

/-- Vertices in different fibres are never adjacent in `sigmaFamily`. -/
theorem sigmaFamily_not_adj_of_fst_ne (G : ∀ i, SimpleGraph (β i)) {x y : Σ i, β i}
    (h : x.1 ≠ y.1) : ¬ (sigmaFamily G).Adj x y := by
  rintro ⟨i, a, b, _, rfl, rfl⟩; exact h rfl

end SigmaFamily

/-! ### `Option`-decomposition: `sigmaFamily` over `Option α` is a binary `sum` -/

section SigmaOption
variable {α : Type*} {γ : Option α → Type*}

/-- The vertex equivalence `(Σ i : Option α, γ i) ≃ γ none ⊕ Σ a, γ (some a)`. -/
def sigmaOptionEquiv : (Σ i, γ i) ≃ γ none ⊕ (Σ a, γ (some a)) where
  toFun
    | ⟨none, y⟩ => Sum.inl y
    | ⟨some a, y⟩ => Sum.inr ⟨a, y⟩
  invFun
    | Sum.inl y => ⟨none, y⟩
    | Sum.inr ⟨a, y⟩ => ⟨some a, y⟩
  left_inv := by rintro ⟨_ | a, y⟩ <;> rfl
  right_inv := by rintro (y | ⟨a, y⟩) <;> rfl

/-- **`sigmaFamily` over `Option α` splits as a binary `sum`**: the `none` fibre summed with
the family over `α`. The Option-step of the induction proving `μ` multiplicative over
`sigmaFamily`. -/
def sigmaFamilyOptionIso (G : ∀ i : Option α, SimpleGraph (γ i)) :
    sigmaFamily G ≃g (G none).sum (sigmaFamily fun a => G (some a)) where
  toEquiv := sigmaOptionEquiv
  map_rel_iff' := by
    rintro ⟨_ | a, x⟩ ⟨_ | b, y⟩
    · -- none, none : sum reduces to `G none`, both sides `(G none).Adj x y`
      show (G none).Adj x y ↔ (sigmaFamily G).Adj ⟨none, x⟩ ⟨none, y⟩
      rw [sigmaFamily_adj]
    · -- none, some : cross fibre, both False
      refine iff_of_false ?_ (sigmaFamily_not_adj_of_fst_ne G (by simp))
      simp [sigmaOptionEquiv, SimpleGraph.sum]
    · -- some, none : cross fibre, both False
      refine iff_of_false ?_ (sigmaFamily_not_adj_of_fst_ne G (by simp))
      simp [sigmaOptionEquiv, SimpleGraph.sum]
    · -- some, some
      show (sigmaFamily fun a => G (some a)).Adj ⟨a, x⟩ ⟨b, y⟩
          ↔ (sigmaFamily G).Adj ⟨some a, x⟩ ⟨some b, y⟩
      by_cases h : a = b
      · subst h; rw [sigmaFamily_adj, sigmaFamily_adj]
      · exact iff_of_false (sigmaFamily_not_adj_of_fst_ne _ (by simpa using h))
          (sigmaFamily_not_adj_of_fst_ne G (by simpa using h))

/-- Reindexing `sigmaFamily` along an equivalence of the index type. -/
def sigmaFamilyCongr {α₁ α₂ : Type*} (e : α₁ ≃ α₂) {γ : α₂ → Type*}
    (G : ∀ i, SimpleGraph (γ i)) :
    sigmaFamily (fun a => G (e a)) ≃g sigmaFamily G where
  toEquiv := Equiv.sigmaCongrLeft e
  map_rel_iff' := by
    rintro ⟨a₁, x⟩ ⟨a₂, y⟩
    by_cases h : a₁ = a₂
    · subst h
      simp only [Equiv.sigmaCongrLeft, Equiv.coe_fn_mk, sigmaFamily_adj]
    · refine iff_of_false ?_ ?_
      · simp only [Equiv.sigmaCongrLeft, Equiv.coe_fn_mk]
        exact sigmaFamily_not_adj_of_fst_ne G (by simpa using fun he => h (e.injective he))
      · exact sigmaFamily_not_adj_of_fst_ne _ (by simpa using h)

end SigmaOption

/-- The equiv `({w ≠ v} ⊕ Unit) ≃ V` re-attaching the single vertex `v` to the rest. A top-level
`def` (not a `let`/`.symm`) with `@[simp]` lemmas keyed on the `Sum` *constructors`, so that after
`obtain`-splitting a sum vertex the applications reduce reliably (a `.symm` coe does not). -/
def unIsolate [DecidableEq V] (v : V) : ({w // w ≠ v} ⊕ Unit) ≃ V where
  toFun := Sum.elim (fun w => (w : V)) (fun _ => v)
  invFun a := if h : a = v then Sum.inr () else Sum.inl ⟨a, h⟩
  left_inv s := by rcases s with ⟨w, hw⟩ | u <;> simp_all
  right_inv a := by by_cases h : a = v <;> simp [h]

@[simp] theorem unIsolate_inl [DecidableEq V] (v : V) (w : {w // w ≠ v}) :
    unIsolate v (Sum.inl w) = (w : V) := rfl

@[simp] theorem unIsolate_inr [DecidableEq V] (v : V) (u : Unit) :
    unIsolate v (Sum.inr u) = v := rfl

open Classical in
/-- **Isolated-vertex bridge (route A).** `μ(G − v) = μ(G⟦≠v⟧) · X`. Deleting `v`'s incidences
leaves `v` isolated, so `G.deleteIncidenceSet v ≅g (G.induce {w ≠ v}) ⊕ (⊥ on a point)`; `μ` of an
isolated point is `X`. Relates the fixed-`n` deletion (same vertex type, what `matchingPoly_recurrence`
uses) to the genuine induced subgraph (variable degree, what `hl_geom_recurrence` consumes). -/
theorem matchingPoly_deleteIncidenceSet_isolate [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) :
    (G.deleteIncidenceSet v).matchingPoly
      = (G.induce {w | w ≠ v}).matchingPoly * Polynomial.X := by
  -- Build the iso with the sum as *domain* so `obtain` turns the `SimpleGraph.sum` matcher's
  -- discriminants into constructors (then `.symm` for the direction `matchingPoly_iso` wants).
  have e' : (G.induce {w | w ≠ v}).sum (⊥ : SimpleGraph Unit) ≃g (G.deleteIncidenceSet v) := by
    refine ⟨unIsolate v, fun {a b} => ?_⟩
    -- The map_rel_iff' goal uses the `RelIso` coe, which `simp` lemmas keyed on the plain `Equiv`
    -- coe will not rewrite; but `unIsolate v (Sum.inl ⟨a,_⟩) ≡ a` and `unIsolate v (Sum.inr _) ≡ v`
    -- hold *definitionally*, so term-mode (`.mp`/`.mpr`, `rfl`) closes every case via defeq.
    obtain (⟨a, ha⟩ | a) := a <;> obtain (⟨b, hb⟩ | b) := b
    -- inl/inl: genuine adjacency in the induced subgraph (`G.Adj a b` on both sides, defeq)
    · exact ⟨fun h => (SimpleGraph.deleteIncidenceSet_adj.mp h).1,
            fun h => SimpleGraph.deleteIncidenceSet_adj.mpr ⟨h, ha, hb⟩⟩
    -- inl/inr: the right endpoint is `v`, so both sides are false.
    · exact iff_of_false
        (fun h => absurd rfl (SimpleGraph.deleteIncidenceSet_adj.mp h).2.2)
        (fun h => by simp [SimpleGraph.sum] at h)
    -- inr/inl: symmetric — the left endpoint is `v`.
    · exact iff_of_false
        (fun h => absurd rfl (SimpleGraph.deleteIncidenceSet_adj.mp h).2.1)
        (fun h => by simp [SimpleGraph.sum] at h)
    -- inr/inr: both endpoints are `v` (a self-loop, impossible), and the summands are non-adjacent.
    · exact iff_of_false
        (fun h => absurd rfl (SimpleGraph.deleteIncidenceSet_adj.mp h).2.1)
        (fun h => by simp [SimpleGraph.sum] at h)
  rw [matchingPoly_iso e'.symm, matchingPoly_sum, matchingPoly_bot, Fintype.card_unit, pow_one]

/-- The equiv `((({≠v,≠t}) ⊕ Unit) ⊕ Unit) ≃ V` re-attaching the two distinct vertices `v`, `t`. -/
def unIsolate₂ [DecidableEq V] (v t : V) (htv : t ≠ v) :
    ((({w // w ≠ v ∧ w ≠ t} ⊕ Unit) ⊕ Unit)) ≃ V where
  toFun := Sum.elim (Sum.elim (fun w => (w : V)) (fun _ => v)) (fun _ => t)
  invFun a := if hv : a = v then Sum.inl (Sum.inr ())
              else if ht : a = t then Sum.inr ()
              else Sum.inl (Sum.inl ⟨a, hv, ht⟩)
  left_inv s := by rcases s with (⟨w, hwv, hwt⟩ | _) | _ <;> simp_all
  right_inv a := by by_cases hv : a = v <;> by_cases ht : a = t <;> simp_all

open Classical in
/-- **Two-vertex isolation (route A, double step).** `μ((G−v)−t) = μ(G⟦≠v,≠t⟧)·X²` for `t ≠ v`. -/
theorem matchingPoly_deleteIncidenceSet_isolate₂ [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {v t : V} (htv : t ≠ v) :
    ((G.deleteIncidenceSet v).deleteIncidenceSet t).matchingPoly
      = (G.induce {w | w ≠ v ∧ w ≠ t}).matchingPoly * Polynomial.X ^ 2 := by
  have e : (((G.induce {w | w ≠ v ∧ w ≠ t}).sum (⊥ : SimpleGraph Unit)).sum (⊥ : SimpleGraph Unit))
      ≃g (G.deleteIncidenceSet v).deleteIncidenceSet t := by
    refine ⟨unIsolate₂ v t htv, fun {A B} => ?_⟩
    obtain ((⟨a, ha⟩ | _) | _) := A <;> obtain ((⟨b, hb⟩ | _) | _) := B
    · -- (LL,LL): genuine adjacency, `G.Adj a b` both sides (defeq)
      exact ⟨fun h => (SimpleGraph.deleteIncidenceSet_adj.mp
              (SimpleGraph.deleteIncidenceSet_adj.mp h).1).1,
            fun h => SimpleGraph.deleteIncidenceSet_adj.mpr
              ⟨SimpleGraph.deleteIncidenceSet_adj.mpr ⟨h, ha.1, hb.1⟩, ha.2, hb.2⟩⟩
    · -- (LL,LR): right endpoint = v
      exact iff_of_false (fun h => absurd rfl (SimpleGraph.deleteIncidenceSet_adj.mp
        (SimpleGraph.deleteIncidenceSet_adj.mp h).1).2.2) (fun h => by simp [SimpleGraph.sum] at h)
    · -- (LL,R): right endpoint = t
      exact iff_of_false (fun h => absurd rfl (SimpleGraph.deleteIncidenceSet_adj.mp h).2.2)
        (fun h => by simp [SimpleGraph.sum] at h)
    · -- (LR,LL): left endpoint = v
      exact iff_of_false (fun h => absurd rfl (SimpleGraph.deleteIncidenceSet_adj.mp
        (SimpleGraph.deleteIncidenceSet_adj.mp h).1).2.1) (fun h => by simp [SimpleGraph.sum] at h)
    · -- (LR,LR): both = v
      exact iff_of_false (fun h => absurd rfl (SimpleGraph.deleteIncidenceSet_adj.mp
        (SimpleGraph.deleteIncidenceSet_adj.mp h).1).2.1) (fun h => by simp [SimpleGraph.sum] at h)
    · -- (LR,R): left = v, right = t
      exact iff_of_false (fun h => absurd rfl (SimpleGraph.deleteIncidenceSet_adj.mp
        (SimpleGraph.deleteIncidenceSet_adj.mp h).1).2.1) (fun h => by simp [SimpleGraph.sum] at h)
    · -- (R,LL): left endpoint = t
      exact iff_of_false (fun h => absurd rfl (SimpleGraph.deleteIncidenceSet_adj.mp h).2.1)
        (fun h => by simp [SimpleGraph.sum] at h)
    · -- (R,LR): left = t, right = v
      exact iff_of_false (fun h => absurd rfl (SimpleGraph.deleteIncidenceSet_adj.mp h).2.1)
        (fun h => by simp [SimpleGraph.sum] at h)
    · -- (R,R): both = t
      exact iff_of_false (fun h => absurd rfl (SimpleGraph.deleteIncidenceSet_adj.mp h).2.1)
        (fun h => by simp [SimpleGraph.sum] at h)
  rw [← matchingPoly_iso e, matchingPoly_sum, matchingPoly_sum, matchingPoly_bot,
    Fintype.card_unit, pow_one]
  ring

open Classical in
/-- **True (variable-degree) matching recurrence (Godsil / Spielman L25.3.2).**
`μ(G) = X·μ(G⟦≠v⟧) − Σ_{u∼v} μ(G⟦≠v,≠u⟧)`, deletions being genuine induced subgraphs. Obtained
from the `X²`-padded fixed-`n` `matchingPoly_recurrence` by substituting the isolated-vertex bridges
(`μ(G−v)=X·μ(G⟦≠v⟧)`, `μ((G−v)−u)=X²·μ(G⟦≠v,≠u⟧)`) and cancelling `X²` (`ℝ[X]` is a domain).
This is the recurrence the geometric Heilmann–Lieb induction (`hl_geom_recurrence`) consumes. -/
theorem matchingPoly_true_recurrence [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V) :
    G.matchingPoly = Polynomial.X * (G.induce {w | w ≠ v}).matchingPoly
      - ∑ u ∈ G.neighborFinset v, (G.induce {w | w ≠ v ∧ w ≠ u}).matchingPoly := by
  have hrec := matchingPoly_recurrence G v
  unfold matchingPoly_recurrence_target at hrec
  have hsum : ∑ u ∈ G.neighborFinset v,
        ((G.deleteIncidenceSet v).deleteIncidenceSet u).matchingPoly
      = ∑ u ∈ G.neighborFinset v,
        (G.induce {w | w ≠ v ∧ w ≠ u}).matchingPoly * Polynomial.X ^ 2 :=
    Finset.sum_congr rfl fun u hu =>
      matchingPoly_deleteIncidenceSet_isolate₂ G ((G.mem_neighborFinset v u).mp hu).ne'
  rw [matchingPoly_deleteIncidenceSet_isolate G v, hsum] at hrec
  refine mul_left_cancel₀ (pow_ne_zero 2 Polynomial.X_ne_zero) ?_
  rw [hrec, mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun u _ => by ring

open Classical in
/-- **Induce-of-induce = induce-of-intersection (for `μ`).** `μ((G⟦≠a⟧)⟦≠b⟧) = μ(G⟦≠a,≠b⟧)`.
Lets the recurrence's second-deletion terms `μ(G⟦≠a,≠b⟧)` be read as one-step deletions of the
induced subgraph `G⟦≠a⟧`, so the induction hypothesis on `G⟦≠a⟧` (fewer vertices) applies to them.
The vertex equiv is `Equiv.subtypeSubtypeEquivSubtypeInter`; adjacency is definitional
(`induce_adj` is `rfl`). -/
theorem matchingPoly_induce_induce [Fintype V] [DecidableEq V] (G : SimpleGraph V) (a b : V) :
    ((G.induce {w | w ≠ a}).induce {x | x.1 ≠ b}).matchingPoly
      = (G.induce {w | w ≠ a ∧ w ≠ b}).matchingPoly := by
  have e : ((G.induce {w | w ≠ a}).induce {x | x.1 ≠ b})
      ≃g (G.induce {w | w ≠ a ∧ w ≠ b}) := by
    refine ⟨Equiv.subtypeSubtypeEquivSubtypeInter (fun w => w ≠ a) (fun w => w ≠ b), ?_⟩
    intro x y
    rfl
  rw [matchingPoly_iso e]

/-! ### Vertex deletion through isomorphisms and disjoint unions

For Godsil's identity `(★)` we apply the vertex-deletion recurrence to the path tree at its
root and must evaluate `μ(T − r − c)` for each child `c`. Transporting through `rootDecompIso`,
that is deleting one more vertex inside one component of `(⊥ Unit) ⊕ ⊔_b T(G−u,b)`. These three
isos do the bookkeeping: deletion commutes with any iso, deleting a right-summand only touches
the right graph, and deleting a vertex of one `sigmaFamily` fibre only touches that fibre. -/

/-- A graph isomorphism transports incidence deletion: deleting `v` from `G` is isomorphic to
deleting `e v` from `H`, with the same vertex map `e`. -/
def Iso.deleteIncidenceSet (e : G ≃g H) (v : V) :
    G.deleteIncidenceSet v ≃g H.deleteIncidenceSet (e v) where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    simp only [deleteIncidenceSet_adj]
    rw [show e.toEquiv a = e a from rfl, show e.toEquiv b = e b from rfl]
    simp only [e.map_adj_iff, e.injective.ne_iff]

/-- **`μ` transports through an iso composed with one incidence deletion.** A *general* lemma:
`μ(G−v) = μ(H−(e v))`. Proving it once for an abstract `e` keeps `matchingPoly_iso`'s
`matchingNumber_iso`/`whnf` work over the deleted graph *abstract*; applying it to a concrete
complex iso (e.g. `rootDecompIso`) is then a pure instantiation, dodging the `whnf` blow-up that
`matchingPoly_iso (e.deleteIncidenceSet v)` triggers inline on a doubly-deleted `Σ`-graph. -/
theorem matchingPoly_deleteIncidenceSet_iso [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) (v : V) :
    (G.deleteIncidenceSet v).matchingPoly = (H.deleteIncidenceSet (e v)).matchingPoly :=
  matchingPoly_iso (e.deleteIncidenceSet v)

/-- Deleting a right-summand vertex `Sum.inr y` from `G ⊕g H` only touches `H`. -/
def sumDeleteIncidenceSetInr (G : SimpleGraph V) (H : SimpleGraph W) (y : W) :
    (G.sum H).deleteIncidenceSet (Sum.inr y) ≃g G.sum (H.deleteIncidenceSet y) where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    rintro (a | a) (b | b) <;> simp [deleteIncidenceSet_adj, SimpleGraph.sum]

section SigmaFamilyDelete
variable {ι : Type*} [DecidableEq ι] {β : ι → Type*}

/-- Deleting a vertex `⟨b, y⟩` of one fibre `b` from `sigmaFamily G` only touches that fibre:
the result is `sigmaFamily` with `G b` replaced by `(G b).deleteIncidenceSet y`. -/
def sigmaFamilyDeleteIncidenceSet (G : ∀ i, SimpleGraph (β i)) (b : ι) (y : β b) :
    (sigmaFamily G).deleteIncidenceSet ⟨b, y⟩
      ≃g sigmaFamily (Function.update G b ((G b).deleteIncidenceSet y)) where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    rintro ⟨i, a⟩ ⟨j, a'⟩
    by_cases hij : i = j
    · subst hij
      by_cases hib : i = b
      · subst hib
        simp [Function.update_self, sigmaFamily_adj, deleteIncidenceSet_adj, Sigma.mk.injEq]
      · simp [sigmaFamily_adj, deleteIncidenceSet_adj, Sigma.mk.injEq, hib]
    · refine iff_of_false (sigmaFamily_not_adj_of_fst_ne _ hij) ?_
      exact fun h => sigmaFamily_not_adj_of_fst_ne G hij (deleteIncidenceSet_adj.mp h).1

end SigmaFamilyDelete

/-! ## `μ` is multiplicative over the indexed disjoint union -/

open Classical in
/-- **`μ[sigmaFamily G] = ∏ μ[G i]`** over a finite index — the product the path-tree root
decomposition needs. Proved by induction on `n = |ι|` over `Fin n` (so all `Fintype`s are the
canonical `Fin`/`Option`/`⊕` ones — avoiding the `Fintype.ofEquiv` diamond that makes the
direct `Fintype.induction_empty_option` route diverge in `whnf`), then transported to a general
index by one `equivFin` reindex. The successor step is `matchingPoly_sum` through
`sigmaFamilyOptionIso` after `finSuccEquiv`; the transport is `matchingPoly_iso` through
`sigmaFamilyCongr` + `Equiv.prod_comp`. -/
theorem matchingPoly_sigmaFamily.{u, v} {ι : Type u} [Fintype ι] {β : ι → Type v}
    [∀ i, Fintype (β i)] (G : ∀ i, SimpleGraph (β i)) :
    (sigmaFamily G).matchingPoly = ∏ i, (G i).matchingPoly := by
  suffices h : ∀ (n : ℕ) (β : Fin n → Type v) [∀ i, Fintype (β i)]
      (G : ∀ i, SimpleGraph (β i)),
      (sigmaFamily G).matchingPoly = ∏ i, (G i).matchingPoly by
    rw [← matchingPoly_iso (sigmaFamilyCongr (Fintype.equivFin ι).symm G)]
    exact (h _ _ _).trans
      (Equiv.prod_comp (Fintype.equivFin ι).symm fun i => (G i).matchingPoly)
  intro n
  induction n with
  | zero =>
    intro β _ G
    rw [eq_one_of_monic_natDegree_zero (matchingPoly_monic _)
          (by rw [matchingPoly_natDegree]; exact Fintype.card_eq_zero), Fin.prod_univ_zero]
  | succ n ih =>
    intro β _ G
    rw [← matchingPoly_iso (sigmaFamilyCongr (finSuccEquiv n).symm G),
        matchingPoly_iso (sigmaFamilyOptionIso fun o => G ((finSuccEquiv n).symm o)),
        matchingPoly_sum,
        ← Equiv.prod_comp (finSuccEquiv n).symm fun i => (G i).matchingPoly,
        Fintype.prod_option]
    congr 1
    exact ih (fun a => β ((finSuccEquiv n).symm (some a)))
             (fun a => G ((finSuccEquiv n).symm (some a)))
