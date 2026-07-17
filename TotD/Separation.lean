/-
Authors: Carles Marín, Claude (Anthropic) as AI assistant.

P. M. Neumann's Separation Lemma, in two forms.

1. Finite/transitive version (Cameron, "Synchronization", Lecture 3, Thm 6b):
   if `G` acts pretransitively on `Ω` and `A B : Finset Ω` satisfy
   `A.card * B.card < Nat.card Ω`, then some `g : G` moves `A` entirely off `B`.
   Stated with `Nat.card`, so NO finiteness instance is needed on `G` or `Ω`
   (the cardinality hypothesis forces `Ω` finite and nonempty); a `Fintype.card`
   corollary is provided.

2. Infinite version (P. M. Neumann, 1974): if the orbit of every point of `A`
   is infinite (in particular if all `G`-orbits on `Ω` are infinite), then for
   finite `A B : Set Ω` some `g : G` satisfies `(g • A) ∩ B = ∅`.

Both are driven by ONE counting engine: the coset covering
`G = ⋃ (a,b) ∈ A × B, t(a,b) • stabilizer G a` obtained from the negation of the
conclusion, fed to B. H. Neumann's covering lemma
(`Subgroup.exists_index_le_card_of_leftCoset_cover`, Mathlib.GroupTheory.CosetCover).
Sorry-free; axioms: propext, Classical.choice, Quot.sound.
-/
import Mathlib.GroupTheory.CosetCover
import Mathlib.GroupTheory.Index
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic

open MulAction Pointwise

namespace TotD

variable (G : Type*) {Ω : Type*} [Group G] [MulAction G Ω]

/-- Shared counting engine: if every `g : G` sends some point of `A` into `B`, then the
sets `{g | g • a = b}` for `(a, b) ∈ A ×ˢ B` — each a left coset of `stabilizer G a`
when nonempty — cover `G`, so by B. H. Neumann's covering lemma some point `a ∈ A` has a
stabilizer of finite index, bounded by `A.card * B.card`. -/
private lemma exists_stabilizer_finiteIndex_of_forall_exists {A B : Finset Ω}
    (hcon : ∀ x : G, ∃ a ∈ A, x • a ∈ B) :
    ∃ p ∈ A ×ˢ B, (stabilizer G p.1).FiniteIndex ∧
      (stabilizer G p.1).index ≤ A.card * B.card := by
  -- choose a transporter `t p` with `t p • p.1 = p.2` whenever one exists
  have key : ∀ p : Ω × Ω, ∃ g : G, (∃ g' : G, g' • p.1 = p.2) → g • p.1 = p.2 := by
    intro p
    by_cases hex : ∃ g' : G, g' • p.1 = p.2
    · exact ⟨hex.choose, fun _ => hex.choose_spec⟩
    · exact ⟨1, fun h => absurd h hex⟩
  choose t ht using key
  -- the corresponding left cosets of the stabilizers cover G
  have hcovers : ⋃ p ∈ A ×ˢ B, t p • (stabilizer G p.1 : Set G) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨a, haA, haB⟩ := hcon x
    refine Set.mem_iUnion₂.mpr ⟨(a, x • a), Finset.mem_product.mpr ⟨haA, haB⟩, ?_⟩
    rw [mem_leftCoset_iff, SetLike.mem_coe, mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
    exact (ht (a, x • a) ⟨x, rfl⟩).symm
  obtain ⟨p, hp, hfi, hle⟩ := Subgroup.exists_index_le_card_of_leftCoset_cover hcovers
  exact ⟨p, hp, hfi, by rwa [Finset.card_product] at hle⟩

/-- **Separation lemma, finite/transitive version** (Cameron, "Synchronization",
Lecture 3, Theorem 6b). If `G` acts pretransitively on `Ω` and `A B : Finset Ω`
satisfy `A.card * B.card < Nat.card Ω`, then some `g : G` maps `A` off `B`.

No finiteness is assumed of `G` or `Ω`: the hypothesis forces `Ω` finite nonempty
(`Nat.card` of an infinite type is `0`), and the counting runs through subgroup
indices rather than `|G|`. -/
theorem separation_lemma_of_pretransitive [IsPretransitive G Ω] {A B : Finset Ω}
    (h : A.card * B.card < Nat.card Ω) :
    ∃ g : G, ∀ a ∈ A, g • a ∉ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨p, -, -, hle⟩ := exists_stabilizer_finiteIndex_of_forall_exists G hcon
  rw [index_stabilizer_of_transitive] at hle
  omega

/-- `Fintype.card` form of `separation_lemma_of_pretransitive`. -/
theorem separation_lemma_of_pretransitive' [Fintype Ω] [IsPretransitive G Ω]
    {A B : Finset Ω} (h : A.card * B.card < Fintype.card Ω) :
    ∃ g : G, ∀ a ∈ A, g • a ∉ B :=
  separation_lemma_of_pretransitive G (by rwa [Nat.card_eq_fintype_card])

/-- **P. M. Neumann's separation lemma** (1974), sharp hypothesis: if the orbit of
every point of `A` is infinite, then for finite `A B : Set Ω` some `g : G`
satisfies `(g • A) ∩ B = ∅`.

Proof: otherwise the sets `{g | g • a = b}`, `(a, b) ∈ A × B` — left cosets of the
stabilizers of points of `A` — cover `G`, so by B. H. Neumann's covering lemma some
`stabilizer G a` has finite index; but its index is `(orbit G a).ncard = 0`. -/
theorem neumann_separation_lemma {A B : Set Ω} (hA : A.Finite) (hB : B.Finite)
    (horb : ∀ a ∈ A, (orbit G a).Infinite) :
    ∃ g : G, (g • A) ∩ B = ∅ := by
  by_contra hcon
  push Not at hcon
  -- `push Not` turns `¬ (· = ∅)` directly into `Set.Nonempty`
  have hcon' : ∀ x : G, ∃ a ∈ hA.toFinset, x • a ∈ hB.toFinset := by
    intro x
    obtain ⟨y, hy1, hy2⟩ := hcon x
    obtain ⟨a, haA, rfl⟩ := Set.mem_smul_set.mp hy1
    exact ⟨a, hA.mem_toFinset.mpr haA, hB.mem_toFinset.mpr hy2⟩
  obtain ⟨p, hp, hfi, -⟩ := exists_stabilizer_finiteIndex_of_forall_exists G hcon'
  exact hfi.index_ne_zero <| (index_stabilizer G p.1).trans
    (horb p.1 (hA.mem_toFinset.mp (Finset.mem_product.mp hp).1)).ncard

/-- P. M. Neumann's separation lemma, classical statement: if all `G`-orbits on `Ω`
are infinite, then any two finite subsets of `Ω` can be separated by some `g : G`. -/
theorem neumann_separation_lemma' {A B : Set Ω} (hA : A.Finite) (hB : B.Finite)
    (horb : ∀ x : Ω, (orbit G x).Infinite) :
    ∃ g : G, (g • A) ∩ B = ∅ :=
  neumann_separation_lemma G hA hB fun a _ => horb a

end TotD

#print axioms TotD.separation_lemma_of_pretransitive
#print axioms TotD.separation_lemma_of_pretransitive'
#print axioms TotD.neumann_separation_lemma
#print axioms TotD.neumann_separation_lemma'
