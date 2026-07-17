/-
Dichotomy.lean

Authors: Carles Marín, Claude (Anthropic) as AI assistant

The separation dichotomy (SEED A of the TotD attack), scope-corrected after the
prior-art audit.

Setting: a finite group `G` acting on a set `Ω` (no transitivity assumed);
`A B : Finset Ω`.

Main results (all sorry-free, axiom-audited at the bottom of the file)
* `sum_card_smul_inter` — **the averaging identity**, the one counting engine of
  the file: `∑ g : G, #((g • A) ∩ B) = ∑ a ∈ A, #(B ∩ orbit a) * #(stab a)`.
  Dividing by `#G` this is `(1/#G) ∑_g #(gA ∩ B) = ∑_O #(A∩O) #(B∩O) / #O` over
  common orbits `O` — the triple-count of Barbieri–Bhattacharjee–Manna–Nagy,
  arXiv:2508.20731, Lemma 15 (there for `A = B`), stated multiplied out in ℕ.
* `separation_dichotomy` — **the dichotomy, orbit-local weak form**: if every
  orbit meeting BOTH `A` and `B` has size `≥ #A * #B`, then either some `g`
  separates `A` from `B`, or `#((g • A) ∩ B) = 1` for EVERY `g` and `A`, `B`
  lie in one single common orbit of size exactly `#A * #B`.
* `separation_of_forall_lt` — the strict form (orbit-local BBMN Theorem 2):
  common orbits of size `> #A * #B` force separation.
* `forall_card_smul_inter_eq_one_iff_factorization` — for the left-regular
  action of `G` on itself, the extremal branch is an **exact factorization**:
  `#((g • A) ∩ B) = 1` for all `g` ⟺ every `g` is uniquely `b * a⁻¹` with
  `(a, b) ∈ A × B`, i.e. `G = B · A⁻¹` with uniqueness.
* `forall_card_vadd_inter_eq_one_iff_tiling` — the `ZMod n` corollary: the
  extremal branch ⟺ every `x : ZMod n` is uniquely `b - a`, i.e.
  `B ⊕ (-A) = ℤ/n` is a **tiling** — the rhythmic-canon condition of
  Coven–Meyerowitz and Vuza. Extremal non-separating pairs ARE rhythmic canons.
* `tiling_witness_zmod12` / `separating_witness_zmod12` — `decide` sanity
  witnesses on `ℤ/12`: `{0,3,6,9} , {0,1,2}` is extremal (a canon),
  `{0,1,2,3} , {0,1,2}` separates.

Provenance (honesty floor). The transitive case of the dichotomy is KNOWN: it
is the definition of a *separating group* in Araújo–Cameron–Steinberg,
"Between primitive and 2-transitive" (arXiv:1511.03184), §5.2, and the `λ = 1`
case of Cameron's Theorem 8 ("Synchronization", LTCC Lecture 3). The strict
inequality is BBMN, Bull. Austral. Math. Soc. 14 (1976) 7–10, Theorem 2 (their
remark p. 8 gives the extremal example but no characterization). The diagonal
(`A = B`) regular extremal case is Barbieri et al. arXiv:2508.20731; the
loop-transversal view is ACS §6.4. New here: the orbit-local weak form (no
transitivity; the hypothesis only constrains orbits meeting both sets, and the
failure of separation forces `A ∪ B` into ONE such orbit), the two-set regular
factorization bridge, the `ℤ/n` tiling identification, and the first ITP
formalization of any of it.

Sorry-free; axioms: propext, Classical.choice, Quot.sound.
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

open Finset MulAction
open scoped Pointwise

namespace TotD

variable {Ω : Type*} [DecidableEq Ω] {G : Type*} [Group G] [MulAction G Ω]

/-! ### The counting engine: fibres and the averaging identity -/

/-- The transporter fibre `{g | g • a = b}` is a left coset of `stabilizer G a`
when `b` lies in the orbit of `a`, so it has `#(stabilizer G a)` elements.
(Non-transitive generalization of the fibre count in `SectionRegular.lean`.) -/
theorem card_smul_fiber_eq_card_stabilizer [Fintype G] {a b : Ω}
    (hab : b ∈ orbit G a) :
    (univ.filter fun g : G => g • a = b).card = Nat.card (stabilizer G a) := by
  obtain ⟨h, hh⟩ := mem_orbit_iff.mp hab
  have e : {g : G // g • a = b} ≃ stabilizer G a :=
    { toFun := fun g => ⟨h⁻¹ * g.1, by
        rw [mem_stabilizer_iff, mul_smul, g.2, ← hh, inv_smul_smul]⟩
      invFun := fun s => ⟨h * s.1, by
        rw [mul_smul, mem_stabilizer_iff.mp s.2, hh]⟩
      left_inv := fun g => Subtype.ext (mul_inv_cancel_left h g.1)
      right_inv := fun s => Subtype.ext (inv_mul_cancel_left h s.1) }
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr e

/-- The transporter fibre is empty when `b` is not in the orbit of `a`. -/
theorem card_smul_fiber_eq_zero [Fintype G] {a b : Ω} (hab : b ∉ orbit G a) :
    (univ.filter fun g : G => g • a = b).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g _ hg
  exact hab (mem_orbit_iff.mpr ⟨g, hg⟩)

/-- The translate-intersection count, pulled back to `A`
(same as in `SectionRegular.lean`; restated because these files are standalone). -/
private theorem card_smul_inter_eq_card_filter (g : G) (A B : Finset Ω) :
    ((g • A) ∩ B).card = (A.filter fun a => g • a ∈ B).card := by
  calc ((g • A) ∩ B).card
      = (g • (A ∩ g⁻¹ • B)).card := by rw [smul_finset_inter, smul_inv_smul]
    _ = (A ∩ g⁻¹ • B).card := card_smul_finset g _
    _ = (A.filter fun a => a ∈ g⁻¹ • B).card := by rw [filter_mem_eq_inter]
    _ = (A.filter fun a => g • a ∈ B).card :=
        congrArg Finset.card
          (filter_congr fun a _ => mem_inv_smul_finset_iff)

/-- Triple count: `∑ g #((g • A) ∩ B)` counts the triples `(a, b, g)` with
`a ∈ A`, `b ∈ B`, `g • a = b`. No transitivity is used. -/
private theorem sum_card_smul_inter_eq_sum_fiber [Fintype G] (A B : Finset Ω) :
    ∑ g : G, ((g • A) ∩ B).card
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
        rw [card_eq_sum_card_fiberwise (s := univ.filter fun g : G => g • a ∈ B)
          (f := fun g : G => g • a) (t := B)
          (fun g hg => (mem_filter.mp hg).2)]
        refine sum_congr rfl fun b hb => congrArg Finset.card ?_
        ext g
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hb, h⟩⟩

/-- Averaging identity, `Finset.filter` form (internal): the inner sum over `B`
collapses onto the part of `B` in the orbit of `a`, each point contributing one
stabilizer-sized fibre. -/
private theorem sum_card_smul_inter_filter [Fintype G] (A B : Finset Ω)
    [∀ a : Ω, DecidablePred (· ∈ orbit G a)] :
    ∑ g : G, ((g • A) ∩ B).card
      = ∑ a ∈ A,
          (B.filter fun b => b ∈ orbit G a).card * Nat.card (stabilizer G a) := by
  rw [sum_card_smul_inter_eq_sum_fiber]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_filter_add_sum_filter_not B (fun b => b ∈ orbit G a)
    (fun b => (univ.filter fun g : G => g • a = b).card)]
  have h1 : ∑ b ∈ B.filter (fun b => b ∈ orbit G a),
      (univ.filter fun g : G => g • a = b).card
      = (B.filter fun b => b ∈ orbit G a).card * Nat.card (stabilizer G a) := by
    calc ∑ b ∈ B.filter (fun b => b ∈ orbit G a),
        (univ.filter fun g : G => g • a = b).card
        = ∑ _b ∈ B.filter (fun b => b ∈ orbit G a), Nat.card (stabilizer G a) :=
          sum_congr rfl fun b hb =>
            card_smul_fiber_eq_card_stabilizer (mem_filter.mp hb).2
      _ = (B.filter fun b => b ∈ orbit G a).card * Nat.card (stabilizer G a) := by
          rw [sum_const, smul_eq_mul]
  have h2 : ∑ b ∈ B.filter (fun b => ¬b ∈ orbit G a),
      (univ.filter fun g : G => g • a = b).card = 0 :=
    Finset.sum_eq_zero fun b hb => card_smul_fiber_eq_zero (mem_filter.mp hb).2
  rw [h1, h2, add_zero]

/-- **The averaging identity** (the engine; cf. Barbieri–Bhattacharjee–Manna–Nagy,
arXiv:2508.20731, Lemma 15, there for `A = B`). For a finite group `G` acting on
`Ω` and `A B : Finset Ω`:
`∑ g : G, #((g • A) ∩ B) = ∑ a ∈ A, #(↑B ∩ orbit G a) * #(stabilizer G a)`.

Grouping the `a ∈ A` by orbit and dividing by `#G = #O * #(stab)`, this is the
usual form `(1/#G) ∑ g #(gA ∩ B) = ∑_O #(A ∩ O) * #(B ∩ O) / #O` over the
orbits `O` meeting both `A` and `B` — stated multiplied out to stay in ℕ. -/
theorem sum_card_smul_inter [Fintype G] (A B : Finset Ω) :
    ∑ g : G, ((g • A) ∩ B).card
      = ∑ a ∈ A, (↑B ∩ orbit G a).ncard * Nat.card (stabilizer G a) := by
  classical
  rw [sum_card_smul_inter_filter A B]
  refine sum_congr rfl fun a _ => ?_
  have hcoe : ((B.filter fun b => b ∈ orbit G a : Finset Ω) : Set Ω)
      = ↑B ∩ orbit G a := by
    ext b
    simp [Set.mem_inter_iff]
  rw [← Set.ncard_coe_finset, hcoe]

/-! ### The dichotomy, orbit-local weak form -/

/-- **The separation dichotomy, orbit-local weak form** (SEED A). Let a finite
group `G` act on `Ω`, and let `A B : Finset Ω` be nonempty. Suppose every orbit
meeting BOTH `A` and `B` has size at least `#A * #B`. Then either

* some `g : G` separates: `(g • A) ∩ B = ∅`; or
* the pair is **extremal**: `#((g • A) ∩ B) = 1` for EVERY `g`, and `A` and `B`
  lie in one single common orbit of size exactly `#A * #B`.

The transitive case (`Ω` a single orbit of size `#A * #B`) is known — it is the
definition of a *separating group* in Araújo–Cameron–Steinberg 2017 §5.2, and
the `λ = 1` case of Cameron's Theorem 8. The orbit-local form proved here
assumes nothing outside the common orbits: failure of separation *forces*
`A ∪ B` into one common orbit and pins its size. BBMN (Bull. Austral. Math.
Soc. 14 (1976) 7–10, Thm 2) is the strict-inequality corollary
`separation_of_forall_lt` below.

Proof: averaging. If no `g` separates, `∑ g #((g • A) ∩ B) ≥ #G`; the engine
plus `#(orbit) ≥ #A * #B` on common orbits bounds the same sum by `#G` from
above; equality analysis of the sandwich gives everything. -/
theorem separation_dichotomy [Fintype G] {A B : Finset Ω}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (horb : ∀ a ∈ A, ∀ b ∈ B, b ∈ orbit G a →
      A.card * B.card ≤ Nat.card (orbit G a)) :
    (∃ g : G, (g • A) ∩ B = ∅) ∨
      ((∀ g : G, ((g • A) ∩ B).card = 1) ∧
        ∃ x : Ω, ↑A ⊆ orbit G x ∧ ↑B ⊆ orbit G x ∧
          Nat.card (orbit G x) = A.card * B.card) := by
  classical
  by_cases hsep : ∃ g : G, (g • A) ∩ B = ∅
  · exact Or.inl hsep
  · right
    -- no separation: every translate meets `B`
    have hone : ∀ g : G, 1 ≤ ((g • A) ∩ B).card := by
      intro g
      refine Finset.card_pos.mpr ?_
      rcases Finset.eq_empty_or_nonempty ((g • A) ∩ B) with hemp | hne
      · exact absurd ⟨g, hemp⟩ hsep
      · exact hne
    have hApos : 0 < A.card := Finset.card_pos.mpr hA
    have hBpos : 0 < B.card := Finset.card_pos.mpr hB
    have hnpos : 0 < A.card * B.card := Nat.mul_pos hApos hBpos
    have hGpos : 0 < Fintype.card G := Fintype.card_pos
    -- orbit–stabilizer, multiplied out
    have horbstab : ∀ a : Ω,
        Nat.card (orbit G a) * Nat.card (stabilizer G a) = Fintype.card G := by
      intro a
      rw [← Nat.card_eq_fintype_card, ← Nat.card_prod]
      exact Nat.card_congr (orbitProdStabilizerEquivGroup G a)
    have hspos : ∀ a : Ω, 0 < Nat.card (stabilizer G a) := fun a => Nat.card_pos
    -- the averaging identity
    have havg := sum_card_smul_inter_filter (G := G) A B
    -- per-point bound, multiplied out: on common orbits `#(stab) * (#A * #B) ≤ #G`
    have hkey : ∀ a ∈ A,
        (B.filter fun b => b ∈ orbit G a).card * Nat.card (stabilizer G a)
            * (A.card * B.card)
          ≤ (B.filter fun b => b ∈ orbit G a).card * Fintype.card G := by
      intro a ha
      rcases Nat.eq_zero_or_pos (B.filter fun b => b ∈ orbit G a).card
        with h0 | hpos
      · rw [h0]; simp
      · obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
        obtain ⟨hbB, hborb⟩ := mem_filter.mp hb
        have hno := horb a ha b hbB hborb
        calc (B.filter fun b => b ∈ orbit G a).card * Nat.card (stabilizer G a)
              * (A.card * B.card)
            = (B.filter fun b => b ∈ orbit G a).card
                * (Nat.card (stabilizer G a) * (A.card * B.card)) := by ring
          _ ≤ (B.filter fun b => b ∈ orbit G a).card
                * (Nat.card (stabilizer G a) * Nat.card (orbit G a)) :=
              Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hno)
          _ = (B.filter fun b => b ∈ orbit G a).card * Fintype.card G := by
              rw [mul_comm (Nat.card (stabilizer G a)), horbstab a]
    -- the chain of sums
    have hup1 : ∑ a ∈ A, (B.filter fun b => b ∈ orbit G a).card
          * Nat.card (stabilizer G a) * (A.card * B.card)
        ≤ ∑ a ∈ A, (B.filter fun b => b ∈ orbit G a).card * Fintype.card G :=
      Finset.sum_le_sum hkey
    have hup2 : ∑ a ∈ A, (B.filter fun b => b ∈ orbit G a).card * Fintype.card G
        ≤ ∑ _a ∈ A, B.card * Fintype.card G :=
      Finset.sum_le_sum fun a _ =>
        Nat.mul_le_mul (Finset.card_filter_le _ _) le_rfl
    have hVeq : ∑ _a ∈ A, B.card * Fintype.card G
        = A.card * B.card * Fintype.card G := by
      rw [sum_const, smul_eq_mul]; ring
    -- no separation forces the average up
    have hlow : Fintype.card G ≤ ∑ g : G, ((g • A) ∩ B).card := by
      calc Fintype.card G = ∑ _g : G, 1 := by
            rw [sum_const, smul_eq_mul, mul_one, card_univ]
        _ ≤ ∑ g : G, ((g • A) ∩ B).card := Finset.sum_le_sum fun g _ => hone g
    -- the sandwich
    have htop : (∑ g : G, ((g • A) ∩ B).card) * (A.card * B.card)
        ≤ A.card * B.card * Fintype.card G := by
      rw [havg, Finset.sum_mul]
      exact (hup1.trans hup2).trans_eq hVeq
    have hbot : A.card * B.card * Fintype.card G
        ≤ (∑ g : G, ((g • A) ∩ B).card) * (A.card * B.card) := by
      calc A.card * B.card * Fintype.card G
          ≤ A.card * B.card * ∑ g : G, ((g • A) ∩ B).card :=
            Nat.mul_le_mul le_rfl hlow
        _ = (∑ g : G, ((g • A) ∩ B).card) * (A.card * B.card) := mul_comm _ _
    have hSeq : ∑ g : G, ((g • A) ∩ B).card = Fintype.card G := by
      have h := le_antisymm htop hbot
      have h' : (∑ g : G, ((g • A) ∩ B).card) * (A.card * B.card)
          = Fintype.card G * (A.card * B.card) := by rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_right hnpos h'
    -- variance zero: every translate hits exactly once
    have hallone : ∀ g : G, ((g • A) ∩ B).card = 1 := by
      have hsum : ∑ g : G, ((g • A) ∩ B).card = ∑ _g : G, 1 := by
        rw [hSeq, sum_const, smul_eq_mul, mul_one, card_univ]
      have hall :=
        (Finset.sum_eq_sum_iff_of_le fun g (_ : g ∈ univ) => hone g).mp hsum.symm
      exact fun g => (hall g (mem_univ g)).symm
    -- equalities inside the chain
    have hTeq : ∑ a ∈ A, (B.filter fun b => b ∈ orbit G a).card
          * Nat.card (stabilizer G a) * (A.card * B.card)
        = A.card * B.card * Fintype.card G := by
      rw [← Finset.sum_mul, ← havg, hSeq]; ring
    have hUeq : ∑ a ∈ A, (B.filter fun b => b ∈ orbit G a).card * Fintype.card G
        = A.card * B.card * Fintype.card G :=
      le_antisymm (hup2.trans_eq hVeq) (by rw [← hTeq]; exact hup1)
    -- every `a ∈ A` sees ALL of `B` inside its orbit …
    have hcB : ∀ a ∈ A, (B.filter fun b => b ∈ orbit G a).card = B.card := by
      have hsum2 :
          ∑ a ∈ A, (B.filter fun b => b ∈ orbit G a).card * Fintype.card G
          = ∑ _a ∈ A, B.card * Fintype.card G := hUeq.trans hVeq.symm
      have hall := (Finset.sum_eq_sum_iff_of_le fun a _ =>
        Nat.mul_le_mul (Finset.card_filter_le _ _) le_rfl).mp hsum2
      exact fun a ha => Nat.eq_of_mul_eq_mul_right hGpos (hall a ha)
    -- … and its orbit has size exactly `#A * #B`
    have horbn : ∀ a ∈ A, Nat.card (orbit G a) = A.card * B.card := by
      have hall := (Finset.sum_eq_sum_iff_of_le hkey).mp (hTeq.trans hUeq.symm)
      intro a ha
      have hc0 : 0 < (B.filter fun b => b ∈ orbit G a).card := by
        rw [hcB a ha]; exact hBpos
      have h := hall a ha
      rw [mul_assoc] at h
      have hsn := Nat.eq_of_mul_eq_mul_left hc0 h
      have h2 : Nat.card (orbit G a) * Nat.card (stabilizer G a)
          = A.card * B.card * Nat.card (stabilizer G a) := by
        rw [horbstab a, ← hsn]; ring
      exact Nat.eq_of_mul_eq_mul_right (hspos a) h2
    have hmem : ∀ a ∈ A, ∀ b ∈ B, b ∈ orbit G a := by
      intro a ha b hb
      have heq : B.filter (fun b => b ∈ orbit G a) = B :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (hcB a ha).ge
      rw [← heq] at hb
      exact (mem_filter.mp hb).2
    -- assemble: everything lives in the orbit of any `a₀ ∈ A`
    obtain ⟨a₀, ha₀⟩ := hA
    obtain ⟨b₀, hb₀⟩ := hB
    refine ⟨hallone, a₀, ?_, ?_, horbn a₀ ha₀⟩
    · intro a ha
      rw [Finset.mem_coe] at ha
      have h1 : orbit G b₀ = orbit G a := orbit_eq_iff.mpr (hmem a ha b₀ hb₀)
      have h2 : orbit G b₀ = orbit G a₀ := orbit_eq_iff.mpr (hmem a₀ ha₀ b₀ hb₀)
      rw [← h2, h1]
      exact mem_orbit_self a
    · intro b hb
      rw [Finset.mem_coe] at hb
      exact hmem a₀ ha₀ b hb

/-- **Orbit-local BBMN** (Bull. Austral. Math. Soc. 14 (1976) 7–10, Theorem 2,
sharpened to an orbit-local hypothesis): if every orbit meeting both `A` and
`B` has size STRICTLY greater than `#A * #B`, then some `g` separates. The
strict hypothesis kills the extremal branch of `separation_dichotomy`. -/
theorem separation_of_forall_lt [Fintype G] {A B : Finset Ω}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (horb : ∀ a ∈ A, ∀ b ∈ B, b ∈ orbit G a →
      A.card * B.card < Nat.card (orbit G a)) :
    ∃ g : G, (g • A) ∩ B = ∅ := by
  rcases separation_dichotomy hA hB
      (fun a ha b hb hab => (horb a ha b hb hab).le)
    with h | ⟨-, x, hAx, hBx, hcard⟩
  · exact h
  · obtain ⟨a₀, ha₀⟩ := hA
    obtain ⟨b₀, hb₀⟩ := hB
    have hax : a₀ ∈ orbit G x := hAx (Finset.mem_coe.mpr ha₀)
    have hbx : b₀ ∈ orbit G x := hBx (Finset.mem_coe.mpr hb₀)
    have hxa : orbit G a₀ = orbit G x := orbit_eq_iff.mpr hax
    have hb' : b₀ ∈ orbit G a₀ := by rw [hxa]; exact hbx
    have hlt := horb a₀ ha₀ b₀ hb₀ hb'
    rw [hxa, hcard] at hlt
    exact absurd hlt (lt_irrefl _)

/-! ### Extremal = exact factorization (the regular action) -/

section Regular

variable {G : Type*} [Group G] [DecidableEq G]

/-- For the left-regular action of `G` on itself, `(g • A) ∩ B` is in bijection
with the pairs `(a, b) ∈ A × B` such that `b * a⁻¹ = g` (send `b` to
`(g⁻¹ * b, b)`). -/
@[to_additive /-- For the regular action of an additive group `G` on itself,
`(g +ᵥ A) ∩ B` is in bijection with the pairs `(a, b) ∈ A × B` such that
`b + -a = g`. -/]
theorem card_smul_inter_regular (g : G) (A B : Finset G) :
    ((g • A) ∩ B).card = ((A ×ˢ B).filter fun p => p.2 * p.1⁻¹ = g).card := by
  refine Finset.card_nbij' (fun b => (g⁻¹ * b, b)) (fun p => p.2) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_coe, Finset.mem_inter] at hb
    obtain ⟨hbA, hbB⟩ := hb
    have haA : g⁻¹ * b ∈ A := by
      rw [← smul_eq_mul]
      exact Finset.inv_smul_mem_iff.mpr hbA
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨haA, hbB⟩, ?_⟩
    show b * (g⁻¹ * b)⁻¹ = g
    rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]
  · rintro ⟨p1, p2⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, hpg⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_inter]
    refine ⟨?_, hp2⟩
    have h : g • p1 = p2 := by
      rw [smul_eq_mul, ← hpg, inv_mul_cancel_right]
    rw [← h]
    exact (Finset.smul_mem_smul_finset_iff g).mpr hp1
  · intro b _
    rfl
  · rintro ⟨p1, p2⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨-, hpg⟩ := hp
    show (g⁻¹ * p2, p2) = (p1, p2)
    have h : g⁻¹ * p2 = p1 := by
      rw [← hpg, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    rw [h]

/-- A finset has exactly one element iff membership determines a unique
element. -/
private theorem card_eq_one_iff_existsUnique {α : Type*} {s : Finset α} :
    s.card = 1 ↔ ∃! a, a ∈ s := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨a, Finset.mem_singleton_self a, fun b hb => Finset.mem_singleton.mp hb⟩
  · rintro ⟨a, ha, hu⟩
    have hs : s = {a} := by
      ext b
      simp only [Finset.mem_singleton]
      exact ⟨fun hb => hu b hb, fun hb => hb ▸ ha⟩
    rw [hs, Finset.card_singleton]

/-- **Extremal = exact factorization** (regular action; cf.
Araújo–Cameron–Steinberg 2017 §6.4 for the loop-transversal view, and Barbieri
et al. arXiv:2508.20731 for the diagonal `A = B` case): for `G` acting on
itself by left multiplication and `A B : Finset G`, every translate of `A`
meets `B` exactly once iff every `g : G` has a UNIQUE expression `g = b * a⁻¹`
with `(a, b) ∈ A × B` — an exact factorization `G = B · A⁻¹`. These are
precisely the extremal non-separating pairs of `separation_dichotomy` on the
regular action (all orbits have size `#G = #A * #B`). -/
@[to_additive forall_card_vadd_inter_eq_one_iff_factorization
/-- **Extremal = exact factorization**, additive version: every
translate of `A` meets `B` exactly once iff every `g : G` has a unique
expression `g = b + -a` with `(a, b) ∈ A × B`. -/]
theorem forall_card_smul_inter_eq_one_iff_factorization (A B : Finset G) :
    (∀ g : G, ((g • A) ∩ B).card = 1) ↔
      ∀ g : G, ∃! p : G × G, p ∈ A ×ˢ B ∧ p.2 * p.1⁻¹ = g := by
  refine forall_congr' fun g => ?_
  rw [card_smul_inter_regular g A B, card_eq_one_iff_existsUnique]
  exact existsUnique_congr fun p => Finset.mem_filter

end Regular

/-! ### The `ℤ/n` bridge: extremal pairs are rhythmic canons -/

/-- **Extremal pairs over `ℤ/n` are exactly the rhythmic canons.** For
`A B : Finset (ZMod n)`, every translate of `A` meets `B` in exactly one point
iff the difference map `A × B → ZMod n`, `(a, b) ↦ b - a`, is a bijection —
i.e. `B ⊕ (-A) = ℤ/n` is a tiling of `ℤ/n` by translates. This is the
rhythmic-canon condition of Coven–Meyerowitz ("Tiling the integers with
translates of one finite set") and Vuza (for the aperiodic ones): the extremal
non-separating pairs of the separation dichotomy over `ℤ/n` ARE rhythmic
canons. The separation literature (BBMN 1976, ACS 2017) and the tiling
literature (Vuza, Coven–Meyerowitz, Amiot, Andreatta) never cite each other;
this statement is the bridge. -/
theorem forall_card_vadd_inter_eq_one_iff_tiling {n : ℕ}
    (A B : Finset (ZMod n)) :
    (∀ g : ZMod n, ((g +ᵥ A) ∩ B).card = 1) ↔
      ∀ x : ZMod n, ∃! p : ZMod n × ZMod n, p ∈ A ×ˢ B ∧ p.2 - p.1 = x := by
  simp only [sub_eq_add_neg]
  exact forall_card_vadd_inter_eq_one_iff_factorization A B

/-! ### Sanity witnesses on `ℤ/12` (`decide`) -/

/-- The diminished-seventh rhythm `{0,3,6,9}` against the chromatic cell
`{0,1,2}` in `ℤ/12`: `#A * #B = 12 = #(ℤ/12)`, and every translate meets in
exactly one point — the extremal branch of the dichotomy; by
`forall_card_vadd_inter_eq_one_iff_tiling`, a rhythmic canon. -/
theorem tiling_witness_zmod12 :
    ∀ g : ZMod 12,
      ((g +ᵥ ({0, 3, 6, 9} : Finset (ZMod 12))) ∩ {0, 1, 2}).card = 1 := by
  decide

/-- The chromatic cell `{0,1,2,3}` against `{0,1,2}` in `ℤ/12`: again
`#A * #B = 12 = #(ℤ/12)`, but this pair is NOT a tiling — and indeed it
separates (the other branch of the dichotomy). -/
theorem separating_witness_zmod12 :
    ∃ g : ZMod 12,
      (g +ᵥ ({0, 1, 2, 3} : Finset (ZMod 12))) ∩ {0, 1, 2} = ∅ := by
  decide

end TotD

/-! ### Axiom audit -/

#print axioms TotD.card_smul_fiber_eq_card_stabilizer
#print axioms TotD.card_smul_fiber_eq_zero
#print axioms TotD.sum_card_smul_inter
#print axioms TotD.separation_dichotomy
#print axioms TotD.separation_of_forall_lt
#print axioms TotD.card_smul_inter_regular
#print axioms TotD.card_vadd_inter_regular
#print axioms TotD.forall_card_smul_inter_eq_one_iff_factorization
#print axioms TotD.forall_card_vadd_inter_eq_one_iff_factorization
#print axioms TotD.forall_card_vadd_inter_eq_one_iff_tiling
#print axioms TotD.tiling_witness_zmod12
#print axioms TotD.separating_witness_zmod12
