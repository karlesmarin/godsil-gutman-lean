/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib.Combinatorics.Hall.Finite

/-!
# The equality case of Hall's condition

For an indexed family of finite sets `t : ι → Finset α`, Hall's condition asks that
`#s ≤ #(s.biUnion t)` for every `s : Finset ι`. This file studies the sets where that
inequality is an equality: `#(s.biUnion t) = #s`, classically called *tight* or *critical*.

The key fact is that the neighbourhood function `s ↦ #(s.biUnion t)` is submodular. Given
Hall's condition, submodularity forces the tight sets to be closed under both union and
intersection, so they form a sublattice of the Boolean lattice on `Finset ι`.

## Main results

* `Finset.inter_biUnion_subset`: `(s ∩ u).biUnion t ⊆ s.biUnion t ∩ u.biUnion t`.
* `Finset.card_biUnion_union_add_card_biUnion_inter_le`: the neighbourhood function is
  submodular.
* `Finset.card_biUnion_union_eq_card_union`, `Finset.card_biUnion_inter_eq_card_inter`: under
  Hall's condition, the union and the intersection of two tight sets are tight.

## References

The equality case of Hall's condition underlies Ore's defect formula and the
Dulmage--Mendelsohn decomposition of a bipartite graph.
-/

open Finset

namespace Finset

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α] (t : ι → Finset α) (s u : Finset ι)

/-- The neighbourhood of an intersection is contained in the intersection of the
neighbourhoods. The reverse inclusion fails in general. -/
theorem inter_biUnion_subset : (s ∩ u).biUnion t ⊆ s.biUnion t ∩ u.biUnion t := by
  intro a ha
  rw [mem_biUnion] at ha
  obtain ⟨i, hi, hai⟩ := ha
  rw [mem_inter] at hi
  exact mem_inter.2 ⟨mem_biUnion.2 ⟨i, hi.1, hai⟩, mem_biUnion.2 ⟨i, hi.2, hai⟩⟩

/-- The neighbourhood function `s ↦ #(s.biUnion t)` of an indexed family of finite sets is
submodular. -/
theorem card_biUnion_union_add_card_biUnion_inter_le :
    #((s ∪ u).biUnion t) + #((s ∩ u).biUnion t) ≤ #(s.biUnion t) + #(u.biUnion t) := by
  calc #((s ∪ u).biUnion t) + #((s ∩ u).biUnion t)
      ≤ #(s.biUnion t ∪ u.biUnion t) + #(s.biUnion t ∩ u.biUnion t) := by
        rw [union_biUnion]
        exact Nat.add_le_add_left (card_le_card (inter_biUnion_subset t s u)) _
    _ = #(s.biUnion t) + #(u.biUnion t) := card_union_add_card_inter _ _

variable {t s u}

/-- Under Hall's condition, the union of two tight sets is tight: if `s` and `u` both meet the
Hall bound with equality, so does `s ∪ u`. -/
theorem card_biUnion_union_eq_card_union (hall : ∀ v : Finset ι, #v ≤ #(v.biUnion t))
    (hs : #(s.biUnion t) = #s) (hu : #(u.biUnion t) = #u) :
    #((s ∪ u).biUnion t) = #(s ∪ u) := by
  have hsub := card_biUnion_union_add_card_biUnion_inter_le t s u
  have hcard := card_union_add_card_inter s u
  have h₁ := hall (s ∪ u)
  have h₂ := hall (s ∩ u)
  omega

/-- Under Hall's condition, the intersection of two tight sets is tight. Together with
`Finset.card_biUnion_union_eq_card_union`, the tight sets form a sublattice. -/
theorem card_biUnion_inter_eq_card_inter (hall : ∀ v : Finset ι, #v ≤ #(v.biUnion t))
    (hs : #(s.biUnion t) = #s) (hu : #(u.biUnion t) = #u) :
    #((s ∩ u).biUnion t) = #(s ∩ u) := by
  have hsub := card_biUnion_union_add_card_biUnion_inter_le t s u
  have hcard := card_union_add_card_inter s u
  have h₁ := hall (s ∪ u)
  have h₂ := hall (s ∩ u)
  omega

end Finset
