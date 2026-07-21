import Theorems.TransversalMatroid
import Mathlib.Combinatorics.Matroid.Closure

/-!
Author: Carles Marín

# The canonical obstruction of a partial transversal

Program: the tight-set lattice of a partial transversal and its maximum element.
Purpose: upgrade the existence of a tight obstruction (`exists_tight_witness_of_not_insert`)
  into a decision procedure: one canonical tight set decides every insertion.
Input: a finite indexed set system `A : Fin t → Finset α` and a partial transversal `I`.
Output: `IsTight`, the union/intersection closure of tight subsets, the maximum tight
  subset `maxTight A I`, and the characterisation `insert_iff_not_subset_maxTight`.
Verification status: formal proof; every public theorem is `sorry`-free and Lean-checked.

Mathematical contract. Call `R ⊆ I` *tight* when its compatible slots are exactly
saturated, `|N(R)| = |R|`. Tight subsets of a partial transversal are closed under
union *and* intersection, so they form a sublattice of the Boolean lattice on `I`;
in particular there is a largest one, `maxTight A I`. An element `e ∉ I` can be added
to `I` precisely when its compatible slots are **not** contained in `N(maxTight A I)`.
-/

namespace Theorems

namespace TransversalMatroid

variable {α : Type*} [DecidableEq α] {t : Nat}

/-- The compatible slots of a whole finite set: `N(S)`. -/
def slotsOf (A : Fin t → Finset α) (S : Finset α) : Finset (Fin t) :=
  S.biUnion (compatibleSlots A)

/-- A finite set is *tight* when it exactly saturates its compatible slots. -/
def IsTight (A : Fin t → Finset α) (R : Finset α) : Prop :=
  (slotsOf A R).card = R.card

instance decidableIsTight (A : Fin t → Finset α) : DecidablePred (IsTight A) :=
  fun R => Nat.decEq (slotsOf A R).card R.card

theorem slotsOf_union (A : Fin t → Finset α) (R S : Finset α) :
    slotsOf A (R ∪ S) = slotsOf A R ∪ slotsOf A S := by
  ext i
  simp only [slotsOf, Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨x, hx | hx, hi⟩
    · exact Or.inl ⟨x, hx, hi⟩
    · exact Or.inr ⟨x, hx, hi⟩
  · rintro (⟨x, hx, hi⟩ | ⟨x, hx, hi⟩)
    · exact ⟨x, Or.inl hx, hi⟩
    · exact ⟨x, Or.inr hx, hi⟩

theorem slotsOf_inter_subset (A : Fin t → Finset α) (R S : Finset α) :
    slotsOf A (R ∩ S) ⊆ slotsOf A R ∩ slotsOf A S := by
  intro i hi
  rw [slotsOf, Finset.mem_biUnion] at hi
  obtain ⟨x, hx, hxi⟩ := hi
  have hx' := Finset.mem_inter.mp hx
  exact Finset.mem_inter.mpr
    ⟨Finset.mem_biUnion.mpr ⟨x, hx'.1, hxi⟩, Finset.mem_biUnion.mpr ⟨x, hx'.2, hxi⟩⟩

theorem slotsOf_mono (A : Fin t → Finset α) {R S : Finset α} (h : R ⊆ S) :
    slotsOf A R ⊆ slotsOf A S :=
  Finset.biUnion_subset_biUnion_of_subset_left (compatibleSlots A) h

/-- Hall's inequality, phrased with `slotsOf`. -/
theorem hall_card_le {A : Fin t → Finset α} {I S : Finset α} (hSI : S ⊆ I)
    (hI : IsPartialTransversal A I) : S.card ≤ (slotsOf A S).card :=
  partialTransversal_hall A hSI hI

/-- **The tight sets are a lattice.** Both the union and the intersection of two tight
subsets of a partial transversal are tight. The two halves are one submodular squeeze:
`|N(R∪S)| + |N(R∩S)| ≤ |N(R)| + |N(S)| = |R| + |S| = |R∪S| + |R∩S|`, and Hall bounds each
left-hand term from below, so both inequalities are forced to equalities. -/
theorem tight_union_and_inter {A : Fin t → Finset α} {I R S : Finset α}
    (hI : IsPartialTransversal A I) (hRI : R ⊆ I) (hSI : S ⊆ I)
    (hR : IsTight A R) (hS : IsTight A S) :
    IsTight A (R ∪ S) ∧ IsTight A (R ∩ S) := by
  have hSubmod : (slotsOf A (R ∪ S)).card + (slotsOf A (R ∩ S)).card ≤
      (slotsOf A R).card + (slotsOf A S).card := by
    rw [slotsOf_union]
    calc
      (slotsOf A R ∪ slotsOf A S).card + (slotsOf A (R ∩ S)).card
          ≤ (slotsOf A R ∪ slotsOf A S).card + (slotsOf A R ∩ slotsOf A S).card :=
        Nat.add_le_add_left (Finset.card_le_card (slotsOf_inter_subset A R S)) _
      _ = (slotsOf A R).card + (slotsOf A S).card :=
        Finset.card_union_add_card_inter _ _
  have hUnionHall := hall_card_le (Finset.union_subset hRI hSI) hI
  have hInterHall := hall_card_le (S := R ∩ S)
    (fun x hx => hRI (Finset.mem_inter.mp hx).1) hI
  have hCardRS : (R ∪ S).card + (R ∩ S).card = R.card + S.card :=
    Finset.card_union_add_card_inter R S
  unfold IsTight at *
  omega

theorem tight_union' {A : Fin t → Finset α} {I R S : Finset α}
    (hI : IsPartialTransversal A I) (hRI : R ⊆ I) (hSI : S ⊆ I)
    (hR : IsTight A R) (hS : IsTight A S) : IsTight A (R ∪ S) :=
  (tight_union_and_inter hI hRI hSI hR hS).1

/-- Tight subsets of a partial transversal are closed under **intersection**. This is the
half the augmentation proof never needs, and the half that makes the family a lattice. -/
theorem tight_inter {A : Fin t → Finset α} {I R S : Finset α}
    (hI : IsPartialTransversal A I) (hRI : R ⊆ I) (hSI : S ⊆ I)
    (hR : IsTight A R) (hS : IsTight A S) : IsTight A (R ∩ S) :=
  (tight_union_and_inter hI hRI hSI hR hS).2

/-- The empty set is tight. -/
theorem tight_empty (A : Fin t → Finset α) : IsTight A (∅ : Finset α) := by
  simp [IsTight, slotsOf]

/-- The tight subsets of `I`, as a finite family. -/
def tightSubsets (A : Fin t → Finset α) (I : Finset α) : Finset (Finset α) :=
  I.powerset.filter (IsTight A)

theorem mem_tightSubsets {A : Fin t → Finset α} {I R : Finset α} :
    R ∈ tightSubsets A I ↔ R ⊆ I ∧ IsTight A R := by
  simp [tightSubsets, Finset.mem_filter, Finset.mem_powerset]

/-- **The canonical obstruction of `I`**: the union of every tight subset of `I`. -/
def maxTight (A : Fin t → Finset α) (I : Finset α) : Finset α :=
  (tightSubsets A I).biUnion id

theorem maxTight_subset (A : Fin t → Finset α) (I : Finset α) : maxTight A I ⊆ I := by
  intro x hx
  rw [maxTight, Finset.mem_biUnion] at hx
  obtain ⟨R, hRF, hxR⟩ := hx
  exact (mem_tightSubsets.mp hRF).1 hxR

/-- Every tight subset of `I` is contained in `maxTight A I`: it is the **maximum**, not
merely a maximal, tight set. -/
theorem subset_maxTight {A : Fin t → Finset α} {I R : Finset α} (hRI : R ⊆ I)
    (hR : IsTight A R) : R ⊆ maxTight A I := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨R, mem_tightSubsets.mpr ⟨hRI, hR⟩, hx⟩

/-- The maximum tight set is itself tight. -/
theorem maxTight_isTight {A : Fin t → Finset α} {I : Finset α}
    (hI : IsPartialTransversal A I) : IsTight A (maxTight A I) := by
  have h := tight_biUnion A hI (tightSubsets A I)
    (fun R hR => (mem_tightSubsets.mp hR).1)
    (fun R hR => (mem_tightSubsets.mp hR).2)
  exact h

/-- A tight subset avoiding `e` and already owning every slot of `e` blocks the insertion.
This is the converse of `exists_tight_witness_of_not_insert`: the tight certificate is not
just necessary, it is sufficient. -/
theorem not_insert_of_tight_cover {A : Fin t → Finset α} {I R : Finset α} {e : α}
    (hRI : R ⊆ I) (heR : e ∉ R) (hR : IsTight A R)
    (hcover : compatibleSlots A e ⊆ slotsOf A R) :
    ¬ IsPartialTransversal A (insert e I) := by
  intro hins
  have hsub : insert e R ⊆ insert e I := Finset.insert_subset_insert e hRI
  have hHall := partialTransversal_hall A hsub hins
  have hslots : slotsOf A (insert e R) = slotsOf A R := by
    apply Finset.Subset.antisymm
    · intro i hi
      rw [slotsOf, Finset.mem_biUnion] at hi
      obtain ⟨x, hx, hxi⟩ := hi
      rcases Finset.mem_insert.mp hx with rfl | hxR
      · exact hcover hxi
      · exact Finset.mem_biUnion.mpr ⟨x, hxR, hxi⟩
    · exact slotsOf_mono A (Finset.subset_insert e R)
  have hcard : (insert e R).card = R.card + 1 := Finset.card_insert_of_notMem heR
  rw [show (insert e R).biUnion (compatibleSlots A) = slotsOf A (insert e R) from rfl,
    hslots, hR, hcard] at hHall
  omega

/-- The existence lemma of the base development, restated with `IsTight`. -/
theorem exists_tight_of_not_insert {A : Fin t → Finset α} {I : Finset α} {e : α}
    (hI : IsPartialTransversal A I) (hnot : ¬ IsPartialTransversal A (insert e I)) :
    ∃ R ⊆ I, e ∉ R ∧ IsTight A R ∧ compatibleSlots A e ⊆ slotsOf A R := by
  obtain ⟨R, hRI, heR, hR, hcov⟩ := exists_tight_witness_of_not_insert A hI hnot
  exact ⟨R, hRI, heR, hR, hcov⟩

/-- **Failure is exactly a tight cover.** For a partial transversal `I` and an element
`e ∉ I`, the insertion fails if and only if some tight subset of `I` already owns every
slot compatible with `e`. -/
theorem not_insert_iff_exists_tight {A : Fin t → Finset α} {I : Finset α} {e : α}
    (hI : IsPartialTransversal A I) (heI : e ∉ I) :
    ¬ IsPartialTransversal A (insert e I) ↔
      ∃ R ⊆ I, IsTight A R ∧ compatibleSlots A e ⊆ slotsOf A R := by
  constructor
  · intro hnot
    obtain ⟨R, hRI, _, hR, hcov⟩ := exists_tight_of_not_insert hI hnot
    exact ⟨R, hRI, hR, hcov⟩
  · rintro ⟨R, hRI, hR, hcov⟩
    exact not_insert_of_tight_cover hRI (fun h => heI (hRI h)) hR hcov

/-- **One set decides every insertion.** For a partial transversal `I` and `e ∉ I`, the
set `insert e I` is a partial transversal if and only if `e` has a compatible slot outside
the neighbourhood of the single canonical obstruction `maxTight A I`. -/
theorem insert_iff_not_subset_maxTight {A : Fin t → Finset α} {I : Finset α} {e : α}
    (hI : IsPartialTransversal A I) (heI : e ∉ I) :
    IsPartialTransversal A (insert e I) ↔
      ¬ compatibleSlots A e ⊆ slotsOf A (maxTight A I) := by
  constructor
  · intro hins hcov
    exact (not_insert_of_tight_cover (maxTight_subset A I)
      (fun h => heI (maxTight_subset A I h)) (maxTight_isTight hI) hcov) hins
  · intro hcov
    by_contra hnot
    obtain ⟨R, hRI, hR, hcovR⟩ := (not_insert_iff_exists_tight hI heI).mp hnot
    exact hcov (hcovR.trans (slotsOf_mono A (subset_maxTight hRI hR)))

/-- The contrapositive of `insert_iff_not_subset_maxTight`: the insertion fails exactly when the
canonical obstruction already owns every slot of `e`. Stated positively for readability; it makes
no claim about the matroid's closure operator (for that, see
`mem_closure_iff_subset_maxTight`). -/
theorem not_insert_iff_subset_maxTight {A : Fin t → Finset α} {I : Finset α} {e : α}
    (hI : IsPartialTransversal A I) (heI : e ∉ I) :
    ¬ IsPartialTransversal A (insert e I) ↔
      compatibleSlots A e ⊆ slotsOf A (maxTight A I) := by
  rw [← not_not (a := compatibleSlots A e ⊆ slotsOf A (maxTight A I))]
  exact not_congr (insert_iff_not_subset_maxTight hI heI)

/-- The ground set of the transversal matroid is all of `α`: an element lying in no presenting set
is a loop, not an absentee. -/
@[simp] theorem transversalMatroid_ground (A : Fin t → Finset α) :
    (transversalMatroid A).E = Set.univ := rfl

/-- **The canonical obstruction computes the closure.** For a partial transversal `I` and `e ∉ I`,
the element `e` lies in the closure of `I` in the matroid `transversalMatroid A` exactly when the
single finite set `maxTight A I` already owns every slot compatible with `e`.

This is the statement in Mathlib's own matroid vocabulary: `Matroid.closure` is a genuine matroid
invariant, and the theorem says that on independent sets it is decided by one containment test
against one canonical set, with no search over subsets and no matching recomputed. -/
theorem mem_closure_iff_subset_maxTight {A : Fin t → Finset α} {I : Finset α} {e : α}
    (hI : IsPartialTransversal A I) (heI : e ∉ I) :
    e ∈ (transversalMatroid A).closure (I : Set α) ↔
      compatibleSlots A e ⊆ slotsOf A (maxTight A I) := by
  have hInd : (transversalMatroid A).Indep (I : Set α) :=
    (transversalMatroid_indep A I).mpr hI
  have heI' : e ∉ (I : Set α) := by simpa using heI
  have hmem : e ∈ (transversalMatroid A).E := by simp
  have key : (transversalMatroid A).Indep (insert e (I : Set α)) ↔
      ¬ compatibleSlots A e ⊆ slotsOf A (maxTight A I) := by
    rw [← Finset.coe_insert, transversalMatroid_indep]
    exact insert_iff_not_subset_maxTight hI heI
  rw [← not_iff_not, Matroid.Indep.notMem_closure_iff_of_notMem hInd heI' hmem, key]

end TransversalMatroid

end Theorems
