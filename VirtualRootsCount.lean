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

/-- **A sorted list has no member strictly between two consecutive entries.** The combinatorial fact
that pins each `q'`-root (which Coste 2.2 places among the breakpoints) to a breakpoint, never strictly
inside a cell. -/
theorem not_mem_between {L : List ℝ} (hL : List.IsChain (· ≤ ·) L) {i : ℕ}
    (hi : i + 1 < L.length) {y : ℝ} (hy : y ∈ L)
    (h1 : L[i]'(Nat.lt_of_succ_lt hi) < y) (h2 : y < L[i + 1]'hi) : False := by
  have hpw := List.pairwise_iff_getElem.mp hL.pairwise
  obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.mp hy
  subst hjy
  rcases Nat.lt_trichotomy j i with h | h | h
  · exact absurd (hpw j i hj (Nat.lt_of_succ_lt hi) h) (not_le.mpr h1)
  · subst h; exact lt_irrefl _ h1
  · rcases Nat.lt_trichotomy j (i + 1) with h' | h' | h'
    · omega
    · subst h'; exact lt_irrefl _ h2
    · exact absurd (hpw (i + 1) j hi hj h') (not_le.mpr h2)

/-- **Cell location.** In a sorted list of length `≥ 2` spanning `z` (head `≤ z ≤` last), some
consecutive pair brackets `z`. Locates the cell of the breakpoint partition that contains a root. -/
theorem exists_bracket {z : ℝ} (L : List ℝ) (hchain : List.IsChain (· ≤ ·) L) (hne : L ≠ [])
    (hlo : L.head hne ≤ z) (hhi : z ≤ L.getLast hne) (hlen : 2 ≤ L.length) :
    ∃ i, ∃ (h : i + 1 < L.length), L[i]'(Nat.lt_of_succ_lt h) ≤ z ∧ z ≤ L[i + 1]'h := by
  induction L with
  | nil => exact absurd rfl hne
  | cons a L' ih =>
    cases L' with
    | nil => simp at hlen
    | cons b rest =>
      have hchain' : List.IsChain (· ≤ ·) (b :: rest) := (List.isChain_cons_cons.mp hchain).2
      by_cases hzb : z ≤ b
      · refine ⟨0, by simp, ?_, ?_⟩
        · simpa using hlo
        · simpa using hzb
      · have hzb' : b < z := not_le.mp hzb
        have hne' : (b :: rest) ≠ [] := by simp
        have hlast : (a :: b :: rest).getLast hne = (b :: rest).getLast hne' :=
          List.getLast_cons hne'
        have hlo' : (b :: rest).head hne' ≤ z := le_of_lt (by simpa using hzb')
        have hhi' : z ≤ (b :: rest).getLast hne' := by rw [← hlast]; exact hhi
        have hlen' : 2 ≤ (b :: rest).length := by
          cases rest with
          | nil =>
            simp only [List.getLast_singleton] at hhi'
            exact absurd hhi' hzb
          | cons _ _ => simp
        obtain ⟨i, hi, hia, hib⟩ := ih hchain' hne' hlo' hhi' hlen'
        refine ⟨i + 1, by simpa using hi, ?_, ?_⟩
        · simpa using hia
        · simpa using hib

/-- **Coste's Proposition 2.2.** Every actual root of `q` (under the bracket hypothesis) is one of its
virtual roots. The keystone: it makes the breakpoints capture all of `q'`'s roots, so `q'` is
sign-constant on each cell and `q` is monotone there. Proved by strong induction down the tower:
locate the root's cell (`exists_bracket`), capture it with `ℛ_d` (`R_eval_eq_zero_of_exists`), and rule
out a second root by Rolle (`exists_deriv_root_between` gives a `q'`-root in the open cell, which the
inductive hypothesis places among the breakpoints — impossible by `not_mem_between`). -/
theorem root_mem_vroots {lo hi : ℝ} (hab : lo ≤ hi) {q : Polynomial ℝ}
    (hbr : Brackets lo hi q) {z : ℝ} (hz : q.eval z = 0) : z ∈ vroots lo hi q := by
  suffices H : ∀ n, ∀ q : Polynomial ℝ, q.natDegree = n → Brackets lo hi q →
      ∀ z, q.eval z = 0 → z ∈ vroots lo hi q from H q.natDegree q rfl hbr z hz
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro q hn hbr z hz
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · -- degree `0`: a nonzero constant has no roots
      subst h0
      exfalso
      have hq0 := brackets_ne_zero hbr
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hn
      rw [← hc, eval_C] at hz
      rw [← hc, hz, map_zero] at hq0
      exact hq0 rfl
    · -- degree `≥ 1`: locate the cell, capture, and use Rolle for uniqueness
      have hdeg : 0 < q.natDegree := by rw [hn]; exact hpos
      have hd : q.natDegree ≠ 0 := by omega
      have hbr' : Brackets lo hi (derivative q) := brackets_derivative hdeg hbr
      have hdn : (derivative q).natDegree = n - 1 := by rw [natDegree_derivative_eq hdeg, hn]
      have hzin : z ∈ Set.Ioo lo hi :=
        hbr q ((BudanFourier.fourierSeq_mem q q).mpr ⟨0, Nat.zero_le _, by simp⟩) z hz
      set bps := lo :: (vroots lo hi (derivative q) ++ [hi]) with hbps
      have hchain : List.IsChain (· ≤ ·) bps := vroots_isChain lo hi hab (derivative q)
      have hbne : bps ≠ [] := by simp [hbps]
      have hlo : bps.head hbne ≤ z := by simp only [hbps]; simpa using le_of_lt hzin.1
      have hhi : z ≤ bps.getLast hbne := by
        simp only [hbps, List.getLast_cons (by simp : vroots lo hi (derivative q) ++ [hi] ≠ []),
          List.getLast_append_singleton]
        exact le_of_lt hzin.2
      have hvl : (vroots lo hi (derivative q)).length = n - 1 := by rw [vroots_length, hdn]
      have hblen : bps.length = (n - 1) + 2 := by
        rw [hbps]
        simp only [List.length_cons, List.length_append, List.length_nil, hvl]
      have hlen : 2 ≤ bps.length := by rw [hblen]; omega
      obtain ⟨i, hi1, hbiz, hzbi⟩ := exists_bracket bps hchain hbne hlo hhi hlen
      have hadj : bps[i]'(Nat.lt_of_succ_lt hi1) ≤ bps[i + 1]'hi1 := le_trans hbiz hzbi
      have hzmem : z ∈ Set.Icc (bps[i]'(Nat.lt_of_succ_lt hi1)) (bps[i + 1]'hi1) :=
        Set.mem_Icc.mpr ⟨hbiz, hzbi⟩
      have hwroot : q.eval (R q (bps[i]'(Nat.lt_of_succ_lt hi1)) (bps[i + 1]'hi1)) = 0 :=
        R_eval_eq_zero_of_exists hadj ⟨z, hzmem, hz⟩
      have hwmem := Set.mem_Icc.mp (R_mem (p := q) hadj)
      have hwz : R q (bps[i]'(Nat.lt_of_succ_lt hi1)) (bps[i + 1]'hi1) = z := by
        by_contra hne
        have hbridge : ∀ y, bps[i]'(Nat.lt_of_succ_lt hi1) < y → y < bps[i + 1]'hi1 →
            (derivative q).eval y = 0 → False := by
          intro y hy1 hy2 hyroot
          have hyv : y ∈ vroots lo hi (derivative q) :=
            ih (n - 1) (by omega) (derivative q) hdn hbr' y hyroot
          have hymem : y ∈ bps := by
            rw [hbps]; exact List.mem_cons_of_mem lo (List.mem_append_left _ hyv)
          exact not_mem_between hchain hi1 hymem hy1 hy2
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · obtain ⟨y, hy, hyroot⟩ := exists_deriv_root_between hlt hwroot hz
          exact hbridge y (lt_of_le_of_lt hwmem.1 hy.1) (lt_of_lt_of_le hy.2 hzbi) hyroot
        · obtain ⟨y, hy, hyroot⟩ := exists_deriv_root_between hlt hz hwroot
          exact hbridge y (lt_of_le_of_lt hbiz hy.1) (lt_of_lt_of_le hy.2 hwmem.2) hyroot
      have hivr : i < (vroots lo hi q).length := by
        rw [vroots_length, hn]; omega
      have hvrq : vroots lo hi q
          = List.zipWith (R q) bps bps.tail := by rw [vroots_eq_zipWith hd, ← hbps]
      have hidx : (vroots lo hi q)[i]'hivr
          = R q (bps[i]'(Nat.lt_of_succ_lt hi1)) (bps[i + 1]'hi1) := by
        simp only [hvrq, List.getElem_zipWith, List.getElem_tail]
      have : (vroots lo hi q)[i]'hivr = z := by rw [hidx, hwz]
      exact this ▸ List.getElem_mem hivr

/-! ### (a)+(b): `p` is strictly monotone on each `p'`-cell

Coste 2.2 makes `p'` root-free on each open cell; with the IVT that forces `p'` to keep a constant
sign there, hence (by the mean-value bedrock) `p` is strictly monotone across the closed cell — even
though `p'` may vanish at the breakpoint endpoints. -/

/-- **IVT sign-change.** A continuous polynomial with opposite signs at the ends of an interval has a
root strictly inside. -/
theorem exists_root_of_sign_change {q : Polynomial ℝ} {c d : ℝ} (hcd : c < d)
    (hsign : q.eval c * q.eval d < 0) : ∃ e ∈ Set.Ioo c d, q.eval e = 0 := by
  have hcont : ContinuousOn (fun x => q.eval x) (Set.Icc c d) := q.continuous.continuousOn
  rcases mul_neg_iff.mp hsign with ⟨hcp, hdn⟩ | ⟨hcn, hdp⟩
  · obtain ⟨e, he, hee⟩ := intermediate_value_Icc' hcd.le hcont (Set.mem_Icc.mpr ⟨hdn.le, hcp.le⟩)
    have hee' : q.eval e = 0 := hee
    refine ⟨e, ⟨lt_of_le_of_ne he.1 (fun h => ?_), lt_of_le_of_ne he.2 (fun h => ?_)⟩, hee'⟩
    · rw [h, hee'] at hcp; exact lt_irrefl 0 hcp
    · rw [← h, hee'] at hdn; exact lt_irrefl 0 hdn
  · obtain ⟨e, he, hee⟩ := intermediate_value_Icc hcd.le hcont (Set.mem_Icc.mpr ⟨hcn.le, hdp.le⟩)
    have hee' : q.eval e = 0 := hee
    refine ⟨e, ⟨lt_of_le_of_ne he.1 (fun h => ?_), lt_of_le_of_ne he.2 (fun h => ?_)⟩, hee'⟩
    · rw [h, hee'] at hcn; exact lt_irrefl 0 hcn
    · rw [← h, hee'] at hdp; exact lt_irrefl 0 hdp

/-- **(a)+(b): monotone on a root-free cell.** If `p'` has no root on the open interval `(a,b)`, then
`p` is strictly monotone (one way or the other) on the closed `[a,b]`. -/
theorem strictMonoOn_or_antiOn_of_no_deriv_root {p : Polynomial ℝ} {a b : ℝ} (hab : a < b)
    (hno : ∀ y ∈ Set.Ioo a b, (derivative p).eval y ≠ 0) :
    StrictMonoOn (fun x => p.eval x) (Set.Icc a b)
      ∨ StrictAntiOn (fun x => p.eval x) (Set.Icc a b) := by
  have hmid : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  -- a root-free `(a,b)` keeps `p'` of one sign: any sign disagreement gives a root by the IVT
  have hsame : ∀ y ∈ Set.Ioo a b, 0 < (derivative p).eval ((a + b) / 2) → 0 < (derivative p).eval y := by
    intro y hy hposm
    by_contra hy0
    have hy0 := not_lt.mp hy0
    have hyneg : (derivative p).eval y < 0 := lt_of_le_of_ne hy0 (hno y hy)
    rcases lt_trichotomy y ((a + b) / 2) with hlt | heq | hgt
    · obtain ⟨e, he, hee⟩ := exists_root_of_sign_change hlt (mul_neg_of_neg_of_pos hyneg hposm)
      exact hno e ⟨lt_trans hy.1 he.1, lt_trans he.2 hmid.2⟩ hee
    · rw [heq] at hyneg; exact absurd hposm (not_lt.mpr hyneg.le)
    · obtain ⟨e, he, hee⟩ := exists_root_of_sign_change hgt (mul_neg_of_pos_of_neg hposm hyneg)
      exact hno e ⟨lt_trans hmid.1 he.1, lt_trans he.2 hy.2⟩ hee
  have hsame' : ∀ y ∈ Set.Ioo a b, (derivative p).eval ((a + b) / 2) < 0 →
      (derivative p).eval y < 0 := by
    intro y hy hnegm
    by_contra hy0
    have hy0 := not_lt.mp hy0
    have hypos : 0 < (derivative p).eval y := lt_of_le_of_ne hy0 (Ne.symm (hno y hy))
    rcases lt_trichotomy y ((a + b) / 2) with hlt | heq | hgt
    · obtain ⟨e, he, hee⟩ := exists_root_of_sign_change hlt (mul_neg_of_pos_of_neg hypos hnegm)
      exact hno e ⟨lt_trans hy.1 he.1, lt_trans he.2 hmid.2⟩ hee
    · rw [heq] at hypos; exact absurd hnegm (not_lt.mpr hypos.le)
    · obtain ⟨e, he, hee⟩ := exists_root_of_sign_change hgt (mul_neg_of_neg_of_pos hnegm hypos)
      exact hno e ⟨lt_trans hmid.1 he.1, lt_trans he.2 hy.2⟩ hee
  rcases lt_trichotomy ((derivative p).eval ((a + b) / 2)) 0 with hm | hm | hm
  · right
    apply strictAntiOn_of_deriv_neg (convex_Icc a b) p.continuous.continuousOn
    intro y hy; rw [interior_Icc] at hy; rw [Polynomial.deriv]
    exact hsame' y hy hm
  · exact absurd hm (hno _ hmid)
  · left
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) p.continuous.continuousOn
    intro y hy; rw [interior_Icc] at hy; rw [Polynomial.deriv]
    exact hsame y hy hm

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
