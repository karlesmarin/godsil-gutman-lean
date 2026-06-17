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

**STATUS: reduced to ONE crux.** The induction down the derivative tower (base case + plumbing) is
`sorry`-free; the whole capstone now rests on the single analytic lemma `count_step` (the δ=δ' bit:
the interlacing inserts a virtual root above `x` iff the leading Fourier sign flips). Kept in a
separate file so `VirtualRoots.lean` stays `sorry`-free.
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

/-- Prepending a sign can only add variations: `signChanges` is monotone under `cons`
(a leading nonzero sign adds `0` or `1`; a leading zero adds nothing). -/
theorem signChanges_le_cons (c : SignType) (s : List SignType) :
    Sturm.signChanges s ≤ Sturm.signChanges (c :: s) := by
  rcases hfilt : s.filter (· ≠ 0) with _ | ⟨a, f'⟩
  · have h0 : Sturm.signChanges s = 0 := by
      rw [← Sturm.signChanges_cons_zero s]
      exact Sturm.signChanges_cons_of_filter_nil hfilt
    rw [Sturm.signChanges_cons_of_filter_nil hfilt]; omega
  · rcases eq_or_ne c 0 with hc | hc
    · subst hc; simp
    · rw [Sturm.signChanges_cons_of_ne_zero hc
        (show (s.filter (· ≠ 0)).head? = some a by rw [hfilt]; rfl)]
      omega

/-- The derivative's Fourier count never exceeds `p`'s: the extra leading derivative `p` contributes
at most one new sign variation. The monotonicity that makes the count recursion telescope. -/
theorem fourierVar_deriv_le {p : Polynomial ℝ} (hp : 0 < p.natDegree) (x : ℝ) :
    BudanFourier.fourierVar (derivative p) x ≤ BudanFourier.fourierVar p x := by
  rw [BudanFourier.fourierVar_eq_signVarAt, BudanFourier.fourierVar_eq_signVarAt,
    Sturm.signVarAt_eq_signChanges, Sturm.signVarAt_eq_signChanges, fourierSeq_cons hp,
    List.map_cons]
  exact signChanges_le_cons _ _

/-! ### Toward `count_step`: foundational bricks

The crux needs that `p` is strictly monotone on each `p'`-cell, which needs `p'` to be sign-constant
there, which needs **Coste's Prop. 2.2**: every actual root of a polynomial is one of its virtual
roots. These bricks build toward it: `brackets_ne_zero`, `brackets_derivative` (the bracket hypothesis
descends the tower), and `exists_deriv_root_between` (Rolle: a root of `q'` between any two roots of
`q`). -/

/-- A bracketed polynomial is nonzero (`0` would force the right endpoint `hi` into the open interval
`(lo,hi)`). -/
theorem brackets_ne_zero {lo hi : ℝ} {q : Polynomial ℝ} (hbr : Brackets lo hi q) : q ≠ 0 := by
  intro h
  have hmem : q ∈ BudanFourier.fourierSeq q :=
    (BudanFourier.fourierSeq_mem q q).mpr ⟨0, Nat.zero_le _, by simp⟩
  have hz : q.eval hi = 0 := by rw [h]; simp
  exact lt_irrefl hi (hbr q hmem hi hz).2

/-- The bracket hypothesis descends to the derivative (its Fourier sequence is a tail of `q`'s, for
`deg q ≥ 1`). -/
theorem brackets_derivative {lo hi : ℝ} {q : Polynomial ℝ} (hq : 0 < q.natDegree)
    (hbr : Brackets lo hi q) : Brackets lo hi (derivative q) := fun r hr z hz =>
  hbr r (by rw [fourierSeq_cons hq]; exact List.mem_cons_of_mem _ hr) z hz

/-- **Rolle for the derivative tower.** Between any two roots of `q` there is a root of `q'`. -/
theorem exists_deriv_root_between {q : Polynomial ℝ} {z z' : ℝ} (hlt : z < z')
    (hz : q.eval z = 0) (hz' : q.eval z' = 0) :
    ∃ y ∈ Set.Ioo z z', (derivative q).eval y = 0 := by
  have hcont : ContinuousOn (fun x => q.eval x) (Set.Icc z z') := q.continuous.continuousOn
  obtain ⟨y, hy, hdy⟩ := exists_deriv_eq_zero hlt hcont (by simp [hz, hz'])
  exact ⟨y, hy, by rwa [Polynomial.deriv] at hdy⟩

/-- **THE crux (the one remaining analytic fact).** The increment in the count of virtual roots above
`x` going from `p'` to `p` equals the Fourier increment `V_p − V_{p'}`. Geometrically: the interlacing
inserts a virtual root of `p` above `x` **iff** the virtual root of `p` in `x`'s own `p'`-cell lies
above `x`, and that happens exactly when the leading sign of `p` at `x` produces a new Fourier
variation. Both recursions are pinned to `{0,1}` (the Fourier side by `fourierVar_deriv_le`, the count
side by `N_deriv_le_N`/`N_le_N_deriv_succ`); this lemma says the two bits agree. -/
theorem count_step {lo hi : ℝ} {p : Polynomial ℝ} (hp : 0 < p.natDegree)
    (hbr : Brackets lo hi p) {x : ℝ} (hx : x ∈ Set.Ico lo hi) :
    (((vroots lo hi p : Multiset ℝ)).filter (fun r => x < r)).card
      = (((vroots lo hi (derivative p) : Multiset ℝ)).filter (fun r => x < r)).card
        + (BudanFourier.fourierVar p x - BudanFourier.fourierVar (derivative p) x) := by
  sorry

/-- **Core reformulation.** The Budan–Fourier count at `x` equals the number of virtual roots of `p`
strictly above `x`. The whole development is now `sorry`-free except for the single crux `count_step`:
the induction down the derivative tower (base case + plumbing) is closed here. -/
public theorem fourierVar_eq_card_vroots_gt {lo hi : ℝ} {p : Polynomial ℝ} (hp : p ≠ 0)
    (hbr : Brackets lo hi p) {x : ℝ} (hx : x ∈ Set.Ico lo hi) :
    BudanFourier.fourierVar p x
      = (((vroots lo hi p : Multiset ℝ)).filter (fun r => x < r)).card := by
  suffices H : ∀ n, ∀ q : Polynomial ℝ, q.natDegree = n → q ≠ 0 → Brackets lo hi q →
      BudanFourier.fourierVar q x
        = (((vroots lo hi q : Multiset ℝ)).filter (fun r => x < r)).card from
    H p.natDegree p rfl hp hbr
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hn hp hbr
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · -- base case: `p` is a nonzero constant; both sides are `0`
      subst h0
      have hV : BudanFourier.fourierVar p x = 0 := by
        rw [BudanFourier.fourierVar_eq_signVarAt, Sturm.signVarAt_eq_signChanges]
        have hfs : BudanFourier.fourierSeq p = [p] := by
          rw [BudanFourier.fourierSeq, hn]; simp
        rw [hfs, List.map_cons, List.map_nil]
        exact Sturm.signChanges_cons_of_filter_nil (by simp)
      have hvr : vroots lo hi p = [] := by
        rw [← List.length_eq_zero_iff, vroots_length]; exact hn
      rw [hV, hvr]; simp
    · -- inductive step: peel one derivative
      have hdeg : 0 < p.natDegree := by rw [hn]; exact hpos
      have hp' : derivative p ≠ 0 := by
        intro h
        have hd := degree_derivative_eq p hdeg
        rw [h, degree_zero] at hd
        simp at hd
      have hbr' : Brackets lo hi (derivative p) := by
        intro q hq z hz
        exact hbr q (by rw [fourierSeq_cons hdeg]; exact List.mem_cons_of_mem _ hq) z hz
      have hdn : (derivative p).natDegree = n - 1 := by rw [natDegree_derivative_eq hdeg, hn]
      have ihv := ih (n - 1) (by omega) (derivative p) hdn hp' hbr'
      have hmono := fourierVar_deriv_le hdeg x
      rw [count_step hdeg hbr hx, ← ihv]
      omega

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
