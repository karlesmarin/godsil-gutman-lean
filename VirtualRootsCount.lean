/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

/-
# The exact virtual-root count (work in progress)

The capstone of the virtual-root development: the number of virtual roots of `p` in `(a,b]` equals the
Budan–Fourier sign-variation drop `V(a) − V(b)` (Coste). This fuses the two independent recursions of
the theory — the `ℛ_d` construction of `VirtualRoots` and the `fourierVar` of `BudanFourier`.

**Strategy (recursive bridge).** Both `fourierVar` and `vroots` recurse `p → p'`. The core is the
reformulation
  `fourierVar p x = #{ virtual roots of p strictly greater than x }`,
proved by induction down the derivative tower; the `(a,b]` count follows by subtraction
(`#(a,b] = N(a) − N(b)` with `N(x) = #{ρ > x}`). The induction step matches the leading sign-change of
`fourierVar` (p vs the p'-tower) against the extra virtual root the interlacing inserts above `x`.

**STATUS: scaffold, `sorry`-marked, under construction.** Kept in a separate file so
`VirtualRoots.lean` stays `sorry`-free.
-/
public import VirtualRoots
public import BudanFourier

open Polynomial

namespace VirtualRoots

/-- **Bracketing hypothesis.** `[lo,hi]` strictly contains every root of every member of the
derivative tower of `p`. Then (as the count needs) all virtual roots lie in `(lo,hi)`, `V(lo)` is the
degree, and `V(hi) = 0`. -/
public def Brackets (lo hi : ℝ) (p : Polynomial ℝ) : Prop :=
  ∀ q ∈ BudanFourier.fourierSeq p, ∀ z : ℝ, q.eval z = 0 → z ∈ Set.Ioo lo hi

/-- The derivative tower of `p` is `p` followed by the tower of `p'` (for `deg p ≥ 1`). The structural
recursion that lets `fourierVar` and `vroots` be compared one degree at a time. -/
theorem fourierSeq_cons {p : Polynomial ℝ} (hp : 0 < p.natDegree) :
    BudanFourier.fourierSeq p = p :: BudanFourier.fourierSeq (derivative p) := by
  have hm : (derivative p).natDegree + 1 = p.natDegree := by
    rw [natDegree_derivative_eq hp]; omega
  unfold BudanFourier.fourierSeq
  rw [List.range_succ_eq_map, List.map_cons, ← hm]
  simp only [Function.iterate_zero, id_eq]
  congr 1
  rw [List.map_map]
  refine List.map_congr_left (fun k _ => ?_)
  rw [Function.comp_apply, Function.iterate_succ_apply]

/-- **fourierVar recursion, root case.** Where `p` vanishes, its sign-variation count equals that of
`p'`: the leading zero is invisible. -/
theorem fourierVar_succ_root {p : Polynomial ℝ} (hp : 0 < p.natDegree) {x : ℝ}
    (hx : p.eval x = 0) :
    BudanFourier.fourierVar p x = BudanFourier.fourierVar (derivative p) x := by
  rw [BudanFourier.fourierVar_eq_signVarAt, BudanFourier.fourierVar_eq_signVarAt,
    Sturm.signVarAt_eq_signChanges, Sturm.signVarAt_eq_signChanges, fourierSeq_cons hp,
    List.map_cons, hx]
  simp

/-- **fourierVar recursion, non-root case.** Where `p(x) ≠ 0`, prepending its sign to the `p'`-tower
adds one variation iff that sign disagrees with the first surviving sign `d` of the `p'`-tower. -/
theorem fourierVar_succ_ne {p : Polynomial ℝ} (hp : 0 < p.natDegree) {x : ℝ}
    (hx : p.eval x ≠ 0) {d : SignType}
    (hd : (((BudanFourier.fourierSeq (derivative p)).map (fun q => SignType.sign (q.eval x))).filter
          (· ≠ 0)).head? = some d) :
    BudanFourier.fourierVar p x
      = BudanFourier.fourierVar (derivative p) x
        + (if SignType.sign (p.eval x) = d then 0 else 1) := by
  rw [BudanFourier.fourierVar_eq_signVarAt, BudanFourier.fourierVar_eq_signVarAt,
    Sturm.signVarAt_eq_signChanges, Sturm.signVarAt_eq_signChanges, fourierSeq_cons hp,
    List.map_cons]
  exact Sturm.signChanges_cons_of_ne_zero (by rw [ne_eq, sign_eq_zero_iff]; exact hx) hd

/-- **Count-above is monotone under a pointwise `≤`.** If `L[i] ≤ M[i]` entrywise, then at most as many
of `L` exceed `x` as of `M`. The signless engine of the vroots-side recursion. -/
theorem countP_gt_le_of_forall₂ (x : ℝ) {L M : List ℝ} (h : List.Forall₂ (· ≤ ·) L M) :
    L.countP (fun r => decide (x < r)) ≤ M.countP (fun r => decide (x < r)) := by
  induction h with
  | nil => simp
  | @cons a b L M hab _ ih =>
    rw [List.countP_cons, List.countP_cons]
    refine Nat.add_le_add ih ?_
    by_cases h1 : x < a
    · rw [if_pos (show decide (x < b) = true by simpa using lt_of_lt_of_le h1 hab)]
      split_ifs <;> omega
    · rw [if_neg (show ¬ decide (x < a) = true by simpa using h1)]
      exact Nat.zero_le _

/-- Bridge: the Multiset-card form of `N(x)` equals the `List.countP` form the engine uses. -/
theorem card_filter_gt_eq_countP (x : ℝ) (L : List ℝ) :
    ((L : Multiset ℝ).filter (fun r => x < r)).card = L.countP (fun r => decide (x < r)) := by
  rw [← Multiset.countP_eq_card_filter, Multiset.coe_countP]

/-- The derivative drops the degree by exactly one (characteristic zero), even at degree `0`. -/
theorem natDegree_derivative_eq' (p : Polynomial ℝ) :
    (derivative p).natDegree = p.natDegree - 1 := by
  rcases Nat.eq_zero_or_pos p.natDegree with h | h
  · have := Polynomial.natDegree_derivative_le p
    rw [h]; omega
  · exact natDegree_derivative_eq h

/-- **Lower bound of the vroots-side recursion.** `N_{p'}(x) ≤ N_p(x)`: each virtual root of `p'` above
`x` is matched by one of `p` above `x` (the right half of the interlacing). -/
theorem N_deriv_le_N {lo hi : ℝ} (hab : lo ≤ hi) (p : Polynomial ℝ) (x : ℝ) :
    ((vroots lo hi (derivative p) : Multiset ℝ).filter (fun r => x < r)).card
      ≤ ((vroots lo hi p : Multiset ℝ).filter (fun r => x < r)).card := by
  rw [card_filter_gt_eq_countP, card_filter_gt_eq_countP]
  have hforall : List.Forall₂ (· ≤ ·) (vroots lo hi (derivative p)) ((vroots lo hi p).tail) := by
    rw [List.forall₂_iff_get]
    refine ⟨?_, fun i h1 h2 => ?_⟩
    · rw [List.length_tail, vroots_length, vroots_length, natDegree_derivative_eq']
    · rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_tail]
      have hrp : i + 1 < (vroots lo hi p).length := by
        rw [List.length_tail] at h2; omega
      exact (vroots_interlacing lo hi hab p i h1 hrp).2
  calc (vroots lo hi (derivative p)).countP (fun r => decide (x < r))
      ≤ ((vroots lo hi p).tail).countP (fun r => decide (x < r)) :=
        countP_gt_le_of_forall₂ x hforall
    _ ≤ (vroots lo hi p).countP (fun r => decide (x < r)) :=
        (List.tail_sublist _).countP_le

/-- **Upper bound of the vroots-side recursion.** `N_p(x) ≤ N_{p'}(x) + 1`: dropping the top virtual
root of `p`, the rest are dominated by those of `p'` (the left half of the interlacing). -/
theorem N_le_N_deriv_succ {lo hi : ℝ} (hab : lo ≤ hi) (p : Polynomial ℝ) (x : ℝ) :
    ((vroots lo hi p : Multiset ℝ).filter (fun r => x < r)).card
      ≤ ((vroots lo hi (derivative p) : Multiset ℝ).filter (fun r => x < r)).card + 1 := by
  rw [card_filter_gt_eq_countP, card_filter_gt_eq_countP]
  have hforall : List.Forall₂ (· ≤ ·) ((vroots lo hi p).dropLast) (vroots lo hi (derivative p)) := by
    rw [List.forall₂_iff_get]
    refine ⟨?_, fun i h1 h2 => ?_⟩
    · rw [List.length_dropLast, vroots_length, vroots_length, natDegree_derivative_eq']
    · rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_dropLast]
      have hrp : i + 1 < (vroots lo hi p).length := by
        rw [List.length_dropLast] at h1; omega
      exact (vroots_interlacing lo hi hab p i h2 hrp).1
  have hdrop : (vroots lo hi p).countP (fun r => decide (x < r))
      ≤ (vroots lo hi p).dropLast.countP (fun r => decide (x < r)) + 1 := by
    have hle := (List.dropLast_sublist (vroots lo hi p)).le_countP (fun r => decide (x < r))
    rw [List.length_dropLast] at hle
    omega
  calc (vroots lo hi p).countP (fun r => decide (x < r))
      ≤ (vroots lo hi p).dropLast.countP (fun r => decide (x < r)) + 1 := hdrop
    _ ≤ (vroots lo hi (derivative p)).countP (fun r => decide (x < r)) + 1 :=
        Nat.add_le_add_right (countP_gt_le_of_forall₂ x hforall) 1

/-- **Core reformulation (WIP).** The Budan–Fourier count at `x` equals the number of virtual roots of
`p` strictly above `x`. Everything else is bookkeeping around this. -/
public theorem fourierVar_eq_card_vroots_gt {lo hi : ℝ} {p : Polynomial ℝ} (hp : p ≠ 0)
    (hbr : Brackets lo hi p) {x : ℝ} (hx : x ∈ Set.Ico lo hi) :
    BudanFourier.fourierVar p x
      = (((vroots lo hi p : Multiset ℝ)).filter (fun r => x < r)).card := by
  sorry

/-- **The exact virtual-root count (WIP).** The number of virtual roots in `(a,b]` equals the
Budan–Fourier drop `V(a) − V(b)`, turning the inequality of `BudanFourier.budan_fourier` into an
equality. -/
public theorem card_vroots_Ioc_eq_fourierVar {lo hi : ℝ} {p : Polynomial ℝ} (hp : p ≠ 0)
    (hbr : Brackets lo hi p) {a b : ℝ} (ha : a ∈ Set.Ico lo hi) (hb : b ∈ Set.Ico lo hi)
    (hab : a ≤ b) :
    (((vroots lo hi p : Multiset ℝ)).filter (fun r => a < r ∧ r ≤ b)).card
      = BudanFourier.fourierVar p a - BudanFourier.fourierVar p b := by
  have ka := fourierVar_eq_card_vroots_gt hp hbr ha
  have kb := fourierVar_eq_card_vroots_gt hp hbr hb
  set M := (vroots lo hi p : Multiset ℝ) with hM
  -- {a < r ≤ b} ⊎ {b < r} = {a < r}, as multisets (using a ≤ b)
  have hfilt : M.filter (fun r => a < r ∧ r ≤ b) + M.filter (fun r => b < r)
      = M.filter (fun r => a < r) := by
    rw [Multiset.filter_add_filter]
    have e1 : M.filter (fun r => (a < r ∧ r ≤ b) ∨ b < r) = M.filter (fun r => a < r) := by
      refine Multiset.filter_congr (fun r _ => ?_)
      constructor
      · rintro (⟨h, _⟩ | h)
        · exact h
        · exact lt_of_le_of_lt hab h
      · intro h
        rcases le_or_gt r b with hr | hr
        · exact Or.inl ⟨h, hr⟩
        · exact Or.inr hr
    have e2 : M.filter (fun r => (a < r ∧ r ≤ b) ∧ b < r) = 0 := by
      rw [Multiset.filter_eq_nil]
      rintro r _ ⟨⟨_, hrb⟩, hbr'⟩
      exact absurd hrb (not_le.mpr hbr')
    rw [e1, e2, add_zero]
  have hcard := congrArg Multiset.card hfilt
  rw [Multiset.card_add] at hcard
  rw [ka, kb]; omega

end VirtualRoots
