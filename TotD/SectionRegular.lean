/-
SectionRegular.lean

Authors: Carles Marín, Claude (Anthropic) as AI assistant

The counting core of Cameron's synchronization hierarchy
(P. J. Cameron, "Synchronization", LTCC lecture notes, Lecture 3, 2010).

Setting: a finite group `G` acting on a finite set `Ω` (transitively where
stated); partitions of `Ω` are Mathlib `Finpartition (univ : Finset Ω)`.

Main definitions
* `IsSection S P`        : `S` contains exactly one point of every part of `P`
                           (stated as `#(S ∩ T) = 1` for every part `T`).
* `IsSectionRegular G P S` : `g • S` is a section of `P` for every `g : G`.

Main results (all sorry-free, axiom-audited at the bottom of the file)
* `card_smul_fiber_mul_card_eq_card_group` — transitive fibre count:
  `#{g | g • a = b} * #Ω = #G` (orbit–stabilizer + coset bijection).
* `sum_card_smul_inter_mul_card` — **Cameron Thm 10** (set version,
  multiplied out to stay in ℕ):
  `(∑ g : G, #((g • A) ∩ B)) * #Ω = #A * #B * #G`,
  by counting triples `(a, b, g)` with `a ∈ A`, `b ∈ B`, `g • a = b`.
* `card_mul_card_of_forall_card_smul_inter_eq` — **Cameron Thm 9** (set
  version): if `#((g • A) ∩ B) = l` for all `g` then `#A * #B = l * #Ω`.
* `IsSectionRegular.card_part_mul_card_section` — section-regular partitions
  are uniform: every part `T` satisfies `#T * #S = #Ω` (the `l = 1` case).
* `IsSectionRegular.card_part_eq_card_part` — hence all parts have equal size.
* `card_smul_inter_eq_of_forall_le` / `card_smul_inter_eq_of_forall_ge` —
  **Cameron Thm 8**, the two nontrivial implications: given
  `#A * #B = l * #Ω`, if all intersections are `≥ l` (resp. `≤ l`) then the
  average forces all of them to equal `l`.
-/
import Mathlib.Order.Partition.Finpartition
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

open Finset MulAction
open scoped Pointwise

variable {Ω : Type*} [DecidableEq Ω] {G : Type*} [Group G] [MulAction G Ω]

/-! ### Sections and section-regular partitions -/

section Defs

variable [Fintype Ω]

/-- Cameron: `S` is a *section* (transversal) of the partition `P` of `Ω` if it
contains exactly one point of every part of `P`. -/
def IsSection (S : Finset Ω) (P : Finpartition (univ : Finset Ω)) : Prop :=
  ∀ T ∈ P.parts, (S ∩ T).card = 1

/-- Cameron: `P` is *section-regular* for `G` with section `S` if `g • S` is a
section of `P` for every `g : G`. -/
def IsSectionRegular (G : Type*) [Group G] [MulAction G Ω]
    (P : Finpartition (univ : Finset Ω)) (S : Finset Ω) : Prop :=
  ∀ g : G, IsSection (g • S) P

/-- The section of a section-regular partition is itself a section
(take `g = 1`). -/
theorem IsSectionRegular.isSection {P : Finpartition (univ : Finset Ω)}
    {S : Finset Ω} (hreg : IsSectionRegular G P S) : IsSection S P := by
  have h := hreg (1 : G)
  rwa [one_smul] at h

end Defs

/-! ### The transitive fibre count -/

/-- For a transitive action of a finite group `G` on a finite set `Ω`, the
number of group elements sending `a` to `b` is `#G / #Ω`, stated multiplied
out: `#{g | g • a = b} * #Ω = #G`. The fibre over `b` of `g ↦ g • a` is a
left coset of the stabilizer of `a`; conclude by orbit–stabilizer. -/
theorem card_smul_fiber_mul_card_eq_card_group [Fintype G] [Fintype Ω]
    [IsPretransitive G Ω] (a b : Ω) :
    (univ.filter fun g : G => g • a = b).card * Fintype.card Ω
      = Fintype.card G := by
  obtain ⟨h, hh⟩ := exists_smul_eq G a b
  -- the fibre over `b` is in bijection with the stabilizer of `a`
  have e : {g : G // g • a = b} ≃ stabilizer G a :=
    { toFun := fun g => ⟨h⁻¹ * g.1, by
        rw [mem_stabilizer_iff, mul_smul, g.2, ← hh, inv_smul_smul]⟩
      invFun := fun s => ⟨h * s.1, by
        rw [mul_smul, mem_stabilizer_iff.mp s.2, hh]⟩
      left_inv := fun g => Subtype.ext (mul_inv_cancel_left h g.1)
      right_inv := fun s => Subtype.ext (inv_mul_cancel_left h s.1) }
  have h1 : (univ.filter fun g : G => g • a = b).card
      = Nat.card (stabilizer G a) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr e
  -- orbit–stabilizer theorem, `Nat.card` version
  have h2 : Nat.card (orbit G a) * Nat.card (stabilizer G a) = Nat.card G := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (orbitProdStabilizerEquivGroup G a)
  -- transitivity: the orbit is everything
  have h3 : Nat.card (orbit G a) = Fintype.card Ω := by
    rw [orbit_eq_univ, Nat.card_congr (Equiv.Set.univ Ω),
      Nat.card_eq_fintype_card]
  rw [h1, mul_comm, ← h3, h2, Nat.card_eq_fintype_card]

/-! ### The averaging lemma (Cameron Theorem 10) -/

/-- The translate-intersection count, pulled back to `A`:
`#((g • A) ∩ B) = #{a ∈ A | g • a ∈ B}`. -/
theorem card_smul_inter_eq_card_filter (g : G) (A B : Finset Ω) :
    ((g • A) ∩ B).card = (A.filter fun a => g • a ∈ B).card := by
  calc ((g • A) ∩ B).card
      = (g • (A ∩ g⁻¹ • B)).card := by rw [smul_finset_inter, smul_inv_smul]
    _ = (A ∩ g⁻¹ • B).card := card_smul_finset g _
    _ = (A.filter fun a => a ∈ g⁻¹ • B).card := by rw [filter_mem_eq_inter]
    _ = (A.filter fun a => g • a ∈ B).card :=
        congrArg Finset.card
          (filter_congr fun a _ => mem_inv_smul_finset_iff)

/-- **Cameron, Synchronization Lecture 3, Theorem 10** (set version,
multiplied out to stay in ℕ). For a transitive action of a finite group `G`
on a finite set `Ω` and any `A B : Finset Ω`:
`(∑ g : G, #((g • A) ∩ B)) * #Ω = #A * #B * #G`.
Both sides count the triples `(a, b, g)` with `a ∈ A`, `b ∈ B`, `g • a = b`,
times `#Ω`. -/
theorem sum_card_smul_inter_mul_card [Fintype G] [Fintype Ω]
    [IsPretransitive G Ω] (A B : Finset Ω) :
    (∑ g : G, ((g • A) ∩ B).card) * Fintype.card Ω
      = A.card * B.card * Fintype.card G := by
  -- triple count: reorganize the sum over `g` as a sum over `(a, b)`
  have key : ∑ g : G, ((g • A) ∩ B).card
      = ∑ a ∈ A, ∑ b ∈ B, (univ.filter fun g : G => g • a = b).card := by
    calc ∑ g : G, ((g • A) ∩ B).card
        = ∑ g : G, ∑ a ∈ A, ite (g • a ∈ B) 1 0 :=
          sum_congr rfl fun g _ => by
            rw [card_smul_inter_eq_card_filter, card_filter]
      _ = ∑ a ∈ A, ∑ g : G, ite (g • a ∈ B) 1 0 := sum_comm
      _ = ∑ a ∈ A, (univ.filter fun g : G => g • a ∈ B).card :=
          sum_congr rfl fun a _ => (card_filter _ _).symm
      _ = ∑ a ∈ A, ∑ b ∈ B, (univ.filter fun g : G => g • a = b).card := by
          refine sum_congr rfl fun a _ => ?_
          refine (card_eq_sum_card_fiberwise (f := fun g : G => g • a) (t := B)
            (fun g hg => (mem_filter.mp hg).2)).trans ?_
          refine sum_congr rfl fun b hb => congrArg Finset.card ?_
          ext g
          simp only [mem_filter, mem_univ, true_and]
          exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hb, h⟩⟩
  -- each `(a, b)` contributes `#G` after multiplying by `#Ω`
  have step : ∀ a ∈ A,
      (∑ b ∈ B, (univ.filter fun g : G => g • a = b).card) * Fintype.card Ω
        = B.card * Fintype.card G := by
    intro a _
    calc (∑ b ∈ B, (univ.filter fun g : G => g • a = b).card)
          * Fintype.card Ω
        = ∑ b ∈ B, (univ.filter fun g : G => g • a = b).card
            * Fintype.card Ω := sum_mul _ _ _
      _ = ∑ _b ∈ B, Fintype.card G :=
          sum_congr rfl fun b _ => card_smul_fiber_mul_card_eq_card_group a b
      _ = B.card * Fintype.card G := by rw [sum_const, smul_eq_mul]
  calc (∑ g : G, ((g • A) ∩ B).card) * Fintype.card Ω
      = ∑ a ∈ A, (∑ b ∈ B, (univ.filter fun g : G => g • a = b).card)
          * Fintype.card Ω := by rw [key, sum_mul]
    _ = ∑ _a ∈ A, B.card * Fintype.card G := sum_congr rfl step
    _ = A.card * (B.card * Fintype.card G) := by rw [sum_const, smul_eq_mul]
    _ = A.card * B.card * Fintype.card G := (mul_assoc _ _ _).symm

/-! ### Uniformity (Cameron Theorems 8 and 9) -/

/-- **Cameron Theorem 9** (set version): if all translate intersections have
the same size `l`, then `#A * #B = l * #Ω`. Immediate from the averaging
lemma, cancelling `#G > 0`. -/
theorem card_mul_card_of_forall_card_smul_inter_eq [Fintype G] [Fintype Ω]
    [IsPretransitive G Ω] {A B : Finset Ω} {l : ℕ}
    (h : ∀ g : G, ((g • A) ∩ B).card = l) :
    A.card * B.card = l * Fintype.card Ω := by
  have hG : 0 < Fintype.card G := Fintype.card_pos
  have havg := sum_card_smul_inter_mul_card (G := G) A B
  have hsum : ∑ g : G, ((g • A) ∩ B).card = Fintype.card G * l := by
    rw [sum_congr rfl fun g _ => h g, sum_const, smul_eq_mul, card_univ]
  rw [hsum] at havg
  refine Nat.eq_of_mul_eq_mul_left hG ?_
  calc Fintype.card G * (A.card * B.card)
      = A.card * B.card * Fintype.card G := by ring
    _ = Fintype.card G * l * Fintype.card Ω := havg.symm
    _ = Fintype.card G * (l * Fintype.card Ω) := by ring

/-- **Cameron Theorem 9**: section-regular partitions are uniform. If `P` is
section-regular for `G` with section `S`, every part `T` of `P` satisfies
`#T * #S = #Ω`. This is the `l = 1` case of the previous theorem: a section
meets every part, in every translate, in exactly one point. -/
theorem IsSectionRegular.card_part_mul_card_section [Fintype G] [Fintype Ω]
    [IsPretransitive G Ω] {P : Finpartition (univ : Finset Ω)} {S : Finset Ω}
    (hreg : IsSectionRegular G P S) {T : Finset Ω} (hT : T ∈ P.parts) :
    T.card * S.card = Fintype.card Ω := by
  have h := card_mul_card_of_forall_card_smul_inter_eq (G := G)
    (A := S) (B := T) (l := 1) (fun g => hreg g T hT)
  rw [one_mul] at h
  rw [mul_comm]
  exact h

/-- All parts of a section-regular partition have the same size
("section-regular partitions are uniform"). -/
theorem IsSectionRegular.card_part_eq_card_part [Fintype G] [Fintype Ω]
    [IsPretransitive G Ω] {P : Finpartition (univ : Finset Ω)} {S : Finset Ω}
    (hreg : IsSectionRegular G P S) {T₁ T₂ : Finset Ω}
    (h1 : T₁ ∈ P.parts) (h2 : T₂ ∈ P.parts) : T₁.card = T₂.card := by
  have e1 := hreg.card_part_mul_card_section h1
  have e2 := hreg.card_part_mul_card_section h2
  have hΩ : 0 < Fintype.card Ω := by
    obtain ⟨x, _⟩ := P.nonempty_of_mem_parts h1
    exact Fintype.card_pos_iff.mpr ⟨x⟩
  have hS : 0 < S.card := by
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · rw [h0, mul_zero] at e1
      omega
    · exact hpos
  exact Nat.eq_of_mul_eq_mul_right hS (e1.trans e2.symm)

/-- **Cameron Theorem 8**, "≥ forces =": if `#A * #B = l * #Ω` and every
translate intersection has size at least `l`, then every translate
intersection has size exactly `l` (the average equals `l`, so no term can
exceed it). -/
theorem card_smul_inter_eq_of_forall_le [Fintype G] [Fintype Ω] [Nonempty Ω]
    [IsPretransitive G Ω] {A B : Finset Ω} {l : ℕ}
    (hAB : A.card * B.card = l * Fintype.card Ω)
    (hle : ∀ g : G, l ≤ ((g • A) ∩ B).card) (g : G) :
    ((g • A) ∩ B).card = l := by
  have hΩ : 0 < Fintype.card Ω := Fintype.card_pos
  have havg := sum_card_smul_inter_mul_card (G := G) A B
  rw [hAB] at havg
  have hsum : ∑ g : G, ((g • A) ∩ B).card = ∑ _g : G, l := by
    refine Nat.eq_of_mul_eq_mul_right hΩ ?_
    rw [havg, sum_const, smul_eq_mul, card_univ]
    ring
  have hall := (sum_eq_sum_iff_of_le fun i (_ : i ∈ univ) => hle i).mp hsum.symm
  exact (hall g (mem_univ g)).symm

/-- **Cameron Theorem 8**, "≤ forces =": if `#A * #B = l * #Ω` and every
translate intersection has size at most `l`, then every translate
intersection has size exactly `l`. -/
theorem card_smul_inter_eq_of_forall_ge [Fintype G] [Fintype Ω] [Nonempty Ω]
    [IsPretransitive G Ω] {A B : Finset Ω} {l : ℕ}
    (hAB : A.card * B.card = l * Fintype.card Ω)
    (hge : ∀ g : G, ((g • A) ∩ B).card ≤ l) (g : G) :
    ((g • A) ∩ B).card = l := by
  have hΩ : 0 < Fintype.card Ω := Fintype.card_pos
  have havg := sum_card_smul_inter_mul_card (G := G) A B
  rw [hAB] at havg
  have hsum : ∑ g : G, ((g • A) ∩ B).card = ∑ _g : G, l := by
    refine Nat.eq_of_mul_eq_mul_right hΩ ?_
    rw [havg, sum_const, smul_eq_mul, card_univ]
    ring
  have hall := (sum_eq_sum_iff_of_le fun i (_ : i ∈ univ) => hge i).mp hsum
  exact hall g (mem_univ g)

/-! ### Axiom audit -/

#print axioms card_smul_fiber_mul_card_eq_card_group
#print axioms sum_card_smul_inter_mul_card
#print axioms card_mul_card_of_forall_card_smul_inter_eq
#print axioms IsSectionRegular.card_part_mul_card_section
#print axioms IsSectionRegular.card_part_eq_card_part
#print axioms card_smul_inter_eq_of_forall_le
#print axioms card_smul_inter_eq_of_forall_ge
