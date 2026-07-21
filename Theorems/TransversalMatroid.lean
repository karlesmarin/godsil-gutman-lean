import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.Matroid.IndepAxioms

/-!
Author: Carles Marín

# Partial transversals and transversal matroids

This module is the formal entry point for Perfect's transversal matroid theorem.

Input: a finite indexed set system `A : Fin t → Finset α`.
Output: a formal predicate for partial transversals, its empty-set and
heredity axioms, Hall characterization, and tight-set obstruction lemmas.
Verification: Lean kernel checks every completed theorem in this module.

Mathematical contract. Given a finite indexed family `A : Fin t → Finset α`, a
finite set `X` is a partial transversal if there is an injective assignment of
its elements to indices whose associated sets contain them. The target theorem
will show that these `X` satisfy the matroid independent-set axioms.
-/

namespace Theorems

/-- The compatibility relation of a set-system presentation. -/
def Compatible {α : Type*} {t : Nat} (A : Fin t → Set α) (x : α) (i : Fin t) : Prop :=
  x ∈ A i

/-- The compatibility predicate is definitionally the membership condition in the
presenting set system. -/
theorem compatible_iff {α : Type*} {t : Nat} (A : Fin t → Set α) (x : α) (i : Fin t) :
    Compatible A x i ↔ x ∈ A i :=
  Iff.rfl

namespace TransversalMatroid

/-- The available indices of sets in `A` that contain `x`. -/
def compatibleSlots {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) (x : α) : Finset (Fin t) :=
  Finset.univ.filter fun i => x ∈ A i

/-- A finite set is a partial transversal when its elements can be assigned
injectively to compatible indices in the presenting family. -/
def IsPartialTransversal {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) (I : Finset α) : Prop :=
  Nonempty (hallMatchingsOn (compatibleSlots A) I)

/-- The empty set is a partial transversal of every finite set system. -/
theorem partialTransversal_empty {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) :
    IsPartialTransversal A ∅ := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · intro x
    exact isEmptyElim x
  · intro x y _
    exact isEmptyElim x
  · intro x
    exact isEmptyElim x

/-- Restricting a partial transversal preserves its matching, hence preserves
independence. This is the hereditary matroid axiom for the presentation. -/
theorem partialTransversal_subset {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) {I J : Finset α} (hIJ : I ⊆ J)
    (hJ : IsPartialTransversal A J) : IsPartialTransversal A I := by
  obtain ⟨f⟩ := hJ
  exact ⟨hallMatchingsOn.restrict (compatibleSlots A) hIJ f⟩

/-- A partial transversal satisfies Hall's cardinal inequality for its full
set of elements. The subset form and the augmentation theorem will build on
this injection into the union of compatible slots. -/
theorem partialTransversal_card_le_slots {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) {I : Finset α} (hI : IsPartialTransversal A I) :
    I.card ≤ (I.biUnion (compatibleSlots A)).card := by
  obtain ⟨f⟩ := hI
  let g : {x // x ∈ I} → {i // i ∈ I.biUnion (compatibleSlots A)} := fun x =>
    ⟨f.val x, by
      rw [Finset.mem_biUnion]
      exact ⟨x, x.property, f.property.2 x⟩⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply f.property.1
    exact congrArg Subtype.val hxy
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g hg

/-- Every subset of a partial transversal satisfies Hall's cardinal
inequality. -/
theorem partialTransversal_hall {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) {I S : Finset α} (hSI : S ⊆ I)
    (hI : IsPartialTransversal A I) :
    S.card ≤ (S.biUnion (compatibleSlots A)).card :=
  partialTransversal_card_le_slots A (partialTransversal_subset A hSI hI)

/-- Hall's inequalities on every subset of `I` construct a partial
transversal of `I`. Together with `partialTransversal_hall`, this is the
finite Hall characterization used by the augmentation proof. -/
theorem hall_partialTransversal {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) (I : Finset α)
    (h : ∀ S : Finset α, S ⊆ I → S.card ≤ (S.biUnion (compatibleSlots A)).card) :
    IsPartialTransversal A I := by
  have hsubtype : ∀ S : Finset {x // x ∈ I},
      S.card ≤ (S.biUnion fun x => compatibleSlots A x).card := by
    intro S
    convert h (S.image Subtype.val) (by
      rintro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact y.property) using 1
    · simp only [Finset.card_image_of_injective _ Subtype.coe_injective]
    · rw [Finset.image_biUnion]
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun x : {x // x ∈ I} => compatibleSlots A x)).mp hsubtype
  exact ⟨⟨f, hf_inj, hf_mem⟩⟩

/-- Finite Hall characterization of partial transversals. -/
theorem partialTransversal_iff_hall {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) (I : Finset α) :
    IsPartialTransversal A I ↔
      ∀ S : Finset α, S ⊆ I → S.card ≤ (S.biUnion (compatibleSlots A)).card := by
  constructor
  · intro hI S hSI
    exact partialTransversal_hall A hSI hI
  · exact hall_partialTransversal A I

/-- If a finite set has no partial transversal, Hall's condition has a
concrete finite witness. This is the starting point for the tight-set argument
in the augmentation axiom. -/
theorem not_partialTransversal_exists_hall_violation {α : Type*} [DecidableEq α]
    {t : Nat} (A : Fin t → Finset α) (I : Finset α)
    (hI : ¬ IsPartialTransversal A I) :
    ∃ S : Finset α, S ⊆ I ∧ (S.biUnion (compatibleSlots A)).card < S.card := by
  rw [partialTransversal_iff_hall] at hI
  push Not at hI
  obtain ⟨S, hSI, hS⟩ := hI
  exact ⟨S, hSI, hS⟩

/-- A Hall witness for the failure of `insert e I` must contain the inserted
element when `I` is already a partial transversal. -/
theorem hall_violation_insert_mem {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) {I S : Finset α} {e : α}
    (hI : IsPartialTransversal A I) (hSsub : S ⊆ insert e I)
    (hS : (S.biUnion (compatibleSlots A)).card < S.card) :
    e ∈ S := by
  by_contra heS
  have hSI : S ⊆ I := by
    intro x hx
    rcases Finset.mem_insert.mp (hSsub hx) with hxe | hxI
    · subst x
      exact False.elim (heS hx)
    · exact hxI
  exact (Nat.not_lt_of_ge (partialTransversal_hall A hSI hI) hS).elim

/-- If adding `e` to a partial transversal fails, there is a tight subset of
the original transversal whose compatible slots already contain every slot
compatible with `e`. This is the tight-set certificate used in the standard
Hall proof of augmentation. -/
theorem exists_tight_witness_of_not_insert {α : Type*} [DecidableEq α]
    {t : Nat} (A : Fin t → Finset α) {I : Finset α} {e : α}
    (hI : IsPartialTransversal A I) (hnot : ¬ IsPartialTransversal A (insert e I)) :
    ∃ R : Finset α, R ⊆ I ∧ e ∉ R ∧
      (R.biUnion (compatibleSlots A)).card = R.card ∧
      compatibleSlots A e ⊆ R.biUnion (compatibleSlots A) := by
  obtain ⟨S, hSsub, hS⟩ :=
    not_partialTransversal_exists_hall_violation A (insert e I) hnot
  have heS : e ∈ S := hall_violation_insert_mem A hI hSsub hS
  let R := S.erase e
  have hRsub : R ⊆ I := by
    intro x hx
    rcases Finset.mem_insert.mp (hSsub (Finset.mem_of_mem_erase hx)) with hxe | hxI
    · subst x
      exact False.elim (Finset.ne_of_mem_erase hx rfl)
    · exact hxI
  have heR : e ∉ R := by
    simp [R]
  have hinsert : insert e R = S := by
    simpa [R] using Finset.insert_erase heS
  have hNsub : R.biUnion (compatibleSlots A) ⊆ S.biUnion (compatibleSlots A) :=
    Finset.biUnion_subset_biUnion_of_subset_left (compatibleSlots A)
      (Finset.erase_subset e S)
  have hRhall := partialTransversal_hall A hRsub hI
  have hScard : S.card = R.card + 1 := by
    rw [← hinsert]
    simp [heR]
  have hNSle : (S.biUnion (compatibleSlots A)).card ≤ R.card := by
    rw [hScard] at hS
    exact Nat.lt_succ_iff.mp hS
  have hRcard : (R.biUnion (compatibleSlots A)).card = R.card := by
    apply Nat.le_antisymm
    exact (Finset.card_le_card hNsub).trans hNSle
    exact hRhall
  have hNeq : R.biUnion (compatibleSlots A) = S.biUnion (compatibleSlots A) := by
    apply Finset.eq_of_subset_of_card_le hNsub
    calc
      (S.biUnion (compatibleSlots A)).card ≤ R.card := hNSle
      _ = (R.biUnion (compatibleSlots A)).card := hRcard.symm
  refine ⟨R, hRsub, heR, hRcard, ?_⟩
  rw [hNeq, ← hinsert]
  intro i hi
  rw [Finset.mem_biUnion]
  exact ⟨e, Finset.mem_insert_self e R, hi⟩

/-- The union of two Hall-tight subsets of a partial transversal is again
Hall-tight. This is the submodularity step in the augmentation argument. -/
theorem tight_union {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) {I R S : Finset α} (hI : IsPartialTransversal A I)
    (hRI : R ⊆ I) (hSI : S ⊆ I)
    (hR : (R.biUnion (compatibleSlots A)).card = R.card)
    (hS : (S.biUnion (compatibleSlots A)).card = S.card) :
    ((R ∪ S).biUnion (compatibleSlots A)).card = (R ∪ S).card := by
  have hUnion : (R ∪ S).biUnion (compatibleSlots A) =
      R.biUnion (compatibleSlots A) ∪ S.biUnion (compatibleSlots A) := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_union]
    constructor
    · rintro ⟨x, hx | hx, hi⟩
      · exact Or.inl ⟨x, hx, hi⟩
      · exact Or.inr ⟨x, hx, hi⟩
    · rintro (⟨x, hx, hi⟩ | ⟨x, hx, hi⟩)
      · exact ⟨x, Or.inl hx, hi⟩
      · exact ⟨x, Or.inr hx, hi⟩
  have hInterSub : (R ∩ S).biUnion (compatibleSlots A) ⊆
      R.biUnion (compatibleSlots A) ∩ S.biUnion (compatibleSlots A) := by
    intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨x, hx, hxi⟩ := hi
    have hx' := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨x, hx'.1, hxi⟩,
       Finset.mem_biUnion.mpr ⟨x, hx'.2, hxi⟩⟩
  have hSubmod :
      ((R ∪ S).biUnion (compatibleSlots A)).card +
        ((R ∩ S).biUnion (compatibleSlots A)).card ≤
      (R.biUnion (compatibleSlots A)).card + (S.biUnion (compatibleSlots A)).card := by
    rw [hUnion]
    calc
      (R.biUnion (compatibleSlots A) ∪ S.biUnion (compatibleSlots A)).card +
          ((R ∩ S).biUnion (compatibleSlots A)).card ≤
        (R.biUnion (compatibleSlots A) ∪ S.biUnion (compatibleSlots A)).card +
          (R.biUnion (compatibleSlots A) ∩ S.biUnion (compatibleSlots A)).card :=
        Nat.add_le_add_left (Finset.card_le_card hInterSub) _
      _ = (R.biUnion (compatibleSlots A)).card + (S.biUnion (compatibleSlots A)).card :=
        Finset.card_union_add_card_inter _ _
  have hUnionHall := partialTransversal_hall A (Finset.union_subset hRI hSI) hI
  have hInterSubI : R ∩ S ⊆ I := by
    intro x hx
    exact hRI (Finset.mem_inter.mp hx).1
  have hInterHall := partialTransversal_hall A hInterSubI hI
  have hCardRS : (R ∪ S).card + (R ∩ S).card = R.card + S.card :=
    Finset.card_union_add_card_inter R S
  omega

/-- A finite union of Hall-tight subsets of a partial transversal is
Hall-tight. -/
theorem tight_biUnion {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) {I : Finset α} (hI : IsPartialTransversal A I)
    (F : Finset (Finset α)) (hsub : ∀ R ∈ F, R ⊆ I)
    (htight : ∀ R ∈ F, (R.biUnion (compatibleSlots A)).card = R.card) :
    ((F.biUnion id).biUnion (compatibleSlots A)).card = (F.biUnion id).card := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert R F hRF ih =>
      have hRsub : R ⊆ I := hsub R (Finset.mem_insert_self R F)
      have hRtight : (R.biUnion (compatibleSlots A)).card = R.card :=
        htight R (Finset.mem_insert_self R F)
      have hFsub : F.biUnion id ⊆ I := by
        intro x hx
        rw [Finset.mem_biUnion] at hx
        obtain ⟨T, hTF, hxT⟩ := hx
        exact hsub T (Finset.mem_insert_of_mem hTF) hxT
      have hFtight : ((F.biUnion id).biUnion (compatibleSlots A)).card =
          (F.biUnion id).card := ih
        (fun T hTF => hsub T (Finset.mem_insert_of_mem hTF))
        (fun T hTF => htight T (Finset.mem_insert_of_mem hTF))
      simpa only [Finset.biUnion_insert, id_eq] using
        tight_union A hI hRsub hFsub hRtight hFtight

/-- A finite family of tight subsets of `I` that covers the compatible slots
of every element in `J \ I` forces `|J \ I| ≤ |I \ J|`. -/
theorem card_sdiff_le_of_tight_cover {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) {I J : Finset α}
    (hI : IsPartialTransversal A I) (hJ : IsPartialTransversal A J)
    (F : Finset (Finset α)) (hFsub : ∀ R ∈ F, R ⊆ I)
    (hFtight : ∀ R ∈ F, (R.biUnion (compatibleSlots A)).card = R.card)
    (hcover : ∀ e ∈ J \ I, compatibleSlots A e ⊆
      (F.biUnion id).biUnion (compatibleSlots A)) :
    (J \ I).card ≤ (I \ J).card := by
  let U := F.biUnion id
  have hUsub : U ⊆ I := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨R, hRF, hxR⟩ := hx
    exact hFsub R hRF hxR
  have hUtight : (U.biUnion (compatibleSlots A)).card = U.card := by
    simpa only [U] using tight_biUnion A hI F hFsub hFtight
  let P := (J \ I) ∪ (U ∩ J)
  have hPJ : P ⊆ J := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_sdiff.mp hx |>.1
    · exact Finset.mem_inter.mp hx |>.2
  have hNPsub : P.biUnion (compatibleSlots A) ⊆ U.biUnion (compatibleSlots A) := by
    intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨x, hxP, hxi⟩ := hi
    rcases Finset.mem_union.mp hxP with hx | hx
    · exact hcover x hx hxi
    · exact Finset.mem_biUnion.mpr ⟨x, (Finset.mem_inter.mp hx).1, hxi⟩
  have hPHall := partialTransversal_hall A hPJ hJ
  have hDisjoint : Disjoint (J \ I) (U ∩ J) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxJI hxUJ
    have hxI : x ∈ I := hUsub (Finset.mem_inter.mp hxUJ).1
    exact (Finset.mem_sdiff.mp hxJI).2 hxI
  have hPcard : P.card = (J \ I).card + (U ∩ J).card := by
    rw [Finset.card_union_of_disjoint hDisjoint]
  have hUdiff : (U \ J).card ≤ (I \ J).card := by
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hUsub (Finset.mem_sdiff.mp hx).1,
      (Finset.mem_sdiff.mp hx).2⟩
  have hP_le_U : P.card ≤ U.card := by
    calc
      P.card ≤ (P.biUnion (compatibleSlots A)).card := hPHall
      _ ≤ (U.biUnion (compatibleSlots A)).card := Finset.card_le_card hNPsub
      _ = U.card := hUtight
  have hUcard : (U \ J).card + (U ∩ J).card = U.card :=
    Finset.card_sdiff_add_card_inter U J
  omega

/-- The augmentation axiom for finite partial transversals. This is the
combinatorial core of Perfect's transversal-matroid theorem. -/
theorem partialTransversal_augmentation {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) {I J : Finset α}
    (hI : IsPartialTransversal A I) (hJ : IsPartialTransversal A J)
    (hcard : I.card < J.card) :
    ∃ e ∈ J \ I, IsPartialTransversal A (insert e I) := by
  classical
  by_contra hExists
  have hfail : ∀ e, e ∈ J \ I → ¬ IsPartialTransversal A (insert e I) := by
    intro e he hpartial
    exact hExists ⟨e, he, hpartial⟩
  let W : {e // e ∈ J \ I} → Finset α := fun e =>
    (exists_tight_witness_of_not_insert A hI (hfail e e.property)).choose
  have hW : ∀ e : {e // e ∈ J \ I}, W e ⊆ I ∧ e.val ∉ W e ∧
      ((W e).biUnion (compatibleSlots A)).card = (W e).card ∧
      compatibleSlots A e.val ⊆ (W e).biUnion (compatibleSlots A) := by
    intro e
    exact (exists_tight_witness_of_not_insert A hI (hfail e e.property)).choose_spec
  let F : Finset (Finset α) := Finset.univ.image W
  have hFsub : ∀ R ∈ F, R ⊆ I := by
    intro R hRF
    simp only [F, Finset.mem_image] at hRF
    obtain ⟨e, -, rfl⟩ := hRF
    exact (hW e).1
  have hFtight : ∀ R ∈ F, (R.biUnion (compatibleSlots A)).card = R.card := by
    intro R hRF
    simp only [F, Finset.mem_image] at hRF
    obtain ⟨e, -, rfl⟩ := hRF
    exact (hW e).2.2.1
  have hcover : ∀ e ∈ J \ I, compatibleSlots A e ⊆
      (F.biUnion id).biUnion (compatibleSlots A) := by
    intro e he
    let ee : {e // e ∈ J \ I} := ⟨e, he⟩
    have hWeeF : W ee ∈ F := by
      simp only [F, Finset.mem_image]
      exact ⟨ee, Finset.mem_univ _, rfl⟩
    have hWeeSub : W ee ⊆ F.biUnion id := by
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨W ee, hWeeF, hx⟩
    exact (hW ee).2.2.2.trans
      (Finset.biUnion_subset_biUnion_of_subset_left (compatibleSlots A) hWeeSub)
  have hle := card_sdiff_le_of_tight_cover A hI hJ F hFsub hFtight hcover
  have hlt : (I \ J).card < (J \ I).card :=
    Finset.card_sdiff_lt_card_sdiff_iff.mpr hcard
  exact (Nat.not_lt_of_ge hle hlt).elim

/-- The transversal matroid presented by the finite set system `A`. Elements
outside every member of `A` are loops, so the ground set is all of `α`. -/
noncomputable def transversalMatroid {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) : Matroid α :=
  (IndepMatroid.ofFinset Set.univ (IsPartialTransversal A)
    (partialTransversal_empty A)
    (fun I J hJ hIJ => partialTransversal_subset A hIJ hJ)
    (fun I J hI hJ hcard => by
      obtain ⟨e, heJI, hepartial⟩ := partialTransversal_augmentation A hI hJ hcard
      exact ⟨e, (Finset.mem_sdiff.mp heJI).1, (Finset.mem_sdiff.mp heJI).2, hepartial⟩)
    (by
      intro I hI x hx
      simp)).matroid

/-- Perfect's transversal-matroid theorem for the finite presentation `A`:
the independent finite sets of `transversalMatroid A` are exactly the partial
transversals of `A`. -/
theorem transversalMatroid_indep {α : Type*} [DecidableEq α] {t : Nat}
    (A : Fin t → Finset α) (I : Finset α) :
    (transversalMatroid A).Indep (I : Set α) ↔ IsPartialTransversal A I := by
  simp [transversalMatroid]

end TransversalMatroid

end Theorems
