/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

/-
# The Budan–Fourier theorem (real-root counting via the derivative tower)

Reverse-engine target (2026-06-15): confirmed ABSENT from Mathlib (Loogle `Budan` → unknown
identifier; Mathlib has `Polynomial.signVariations` for Descartes' rule of signs but not the
Budan–Fourier theorem). Formalized in Isabelle/HOL (Wenda Li, arXiv:1811.11093), so this is
**first in Lean**, not first in any ITP. Genuine Mathlib gap, our exact domain (real-root
counting), the natural companion of Sturm: the same sign-variation count, on the *derivative tower*
`p, p', p'', …, p^(deg p)` instead of the signed-remainder sequence.

## The theorem
For a nonzero real polynomial `p` and `a < b` with `p(a), p(b) ≠ 0`, the number of real roots of
`p` in `(a, b]` **counted with multiplicity** is at most the drop `V(a) − V(b)` in the sign
variations of the Fourier (derivative-tower) sequence, and differs from it by an even number:
* `#roots(a,b] ≤ V(a) − V(b)`        (Budan–Fourier inequality)
* `V(a) − V(b) − #roots(a,b]` is even (the parity refinement; Descartes' even-difference rule).

Descartes' rule of signs is the special case read off the coefficients (the `b → ∞` Fourier
sequence); Mathlib already has that count, so this completes the picture for a bounded interval.

**Complete and `sorry`-free** (depends only on `propext`, `Classical.choice`, `Quot.sound`). The
reusable sign-variation toolkit (zeros invisible, the `wallCount` parity engine, local sign
constancy) lives in `Sturm.lean` and is shared here; the local analysis at a critical point uses the
monotonicity bricks of this file plus the derivative-order characterization of root multiplicity.

## Reference route
Wikipedia "Budan's theorem"; Basu–Pollack–Roy, *Algorithms in Real Algebraic Geometry* (Ch. 2);
W. Li, *The Budan–Fourier theorem and counting real roots with multiplicity*, arXiv:1811.11093.
-/
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.List.Destutter
public import Mathlib.Data.Sign.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Algebra.Ring.Parity
public import Sturm

open Polynomial

namespace BudanFourier

/-- The **Fourier sequence** (derivative tower) of `p`: `p, p', p'', …, p^(deg p)`. -/
public noncomputable def fourierSeq (p : Polynomial ℝ) : List (Polynomial ℝ) :=
  (List.range (p.natDegree + 1)).map (fun k => (derivative^[k]) p)

/-- The Fourier sequence has `deg p + 1` entries. -/
public theorem fourierSeq_length (p : Polynomial ℝ) :
    (fourierSeq p).length = p.natDegree + 1 := by
  unfold fourierSeq; simp

/-- The Fourier sequence is never empty (it always contains at least `p`). -/
public theorem fourierSeq_ne_nil (p : Polynomial ℝ) : fourierSeq p ≠ [] := by
  have hlen : 0 < (fourierSeq p).length := by
    simpa [fourierSeq, List.length_map, List.length_range, Nat.succ_eq_add_one] using
      Nat.succ_pos p.natDegree
  exact List.ne_nil_of_length_pos hlen

/-- Membership in the Fourier sequence: its entries are exactly the iterated derivatives
`p^(k)` for `0 ≤ k ≤ deg p`. -/
public theorem fourierSeq_mem (p q : Polynomial ℝ) :
    q ∈ fourierSeq p ↔ ∃ k, k ≤ p.natDegree ∧ q = (derivative^[k]) p := by
  unfold fourierSeq
  constructor
  · intro h
    rcases List.mem_map.1 h with ⟨k, hk, rfl⟩
    exact ⟨k, Nat.le_of_lt_succ (List.mem_range.1 hk), rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact List.mem_map.2 ⟨k, List.mem_range.2 (Nat.lt_succ_of_le hk), rfl⟩

/-- **Fourier sign variations** of `p` at `x`: the number of sign changes in the derivative tower
evaluated at `x`, with zeros dropped. The eval-analogue, on the derivative tower, of the count used
for Sturm's theorem. -/
@[expose] public noncomputable def fourierVar (p : Polynomial ℝ) (x : ℝ) : ℕ :=
  ((((fourierSeq p).map (fun q => SignType.sign (q.eval x))).filter (· ≠ 0)).destutter (· ≠ ·)).length - 1

/-- **Bridge to the Sturm toolkit.** `fourierVar p x` is, definitionally, `Sturm.signVarAt` applied
to the derivative tower. This single `rfl` makes the entire sign-variation toolkit from `Sturm.lean`
(locally-constant on root-free intervals, `signChanges`/`wallCount` parity engine, interior
cancellation) act directly on the Fourier sequence. -/
public theorem fourierVar_eq_signVarAt (p : Polynomial ℝ) (x : ℝ) :
    fourierVar p x = Sturm.signVarAt (fourierSeq p) x := rfl

/-- **`fourierVar` is locally constant.** On a closed interval where no member of the derivative
tower vanishes, the Fourier sign-variation count does not change. Reused verbatim from the generic
`Sturm.signVarAt_eq_of_no_root`; this is the "nothing happens between critical points" half of the
global telescoping argument. -/
public theorem fourierVar_eq_of_no_root {p : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ q ∈ fourierSeq p, ∀ x ∈ Set.Icc a b, q.eval x ≠ 0) :
    fourierVar p a = fourierVar p b := by
  rw [fourierVar_eq_signVarAt, fourierVar_eq_signVarAt]
  exact Sturm.signVarAt_eq_of_no_root hab hne

/-- **Every member of the derivative tower is nonzero.** For `k ≤ deg p`, the `k`-th derivative
`p^(k)` has nonzero coefficient `(deg p).descFactorial k · leadingCoeff p` in degree `deg p − k`
(char 0), so it is nonzero. Unlike the Sturm chain this is the *only* nonvanishing we get — two
*consecutive* tower members can still share a root, which is exactly why the local analysis differs
from Sturm's coprime chain. -/
public theorem fourierSeq_mem_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∀ q ∈ fourierSeq p, q ≠ 0 := by
  intro q hq
  rw [fourierSeq_mem] at hq
  obtain ⟨k, hk, rfl⟩ := hq
  intro h0
  have hcoeff : (derivative^[k] p).coeff (p.natDegree - k) ≠ 0 := by
    rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, nsmul_eq_mul]
    apply mul_ne_zero
    · exact_mod_cast Nat.descFactorial_pos.mpr hk |>.ne'
    · rw [← leadingCoeff]; exact leadingCoeff_ne_zero.mpr hp
  rw [h0, coeff_zero] at hcoeff
  exact hcoeff rfl

/-- **The product of the derivative tower is nonzero** (the analogue of `Sturm.sturmSeq_prod_ne_zero`):
its roots are exactly the "critical points" where some `p^(k)` vanishes, the only places where
`fourierVar` can move. -/
public theorem fourierSeq_prod_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) :
    (fourierSeq p).prod ≠ 0 := by
  intro h
  rw [List.prod_eq_zero_iff] at h
  exact fourierSeq_mem_ne_zero hp 0 h rfl

/-- **Half-open root count splits additively** (with multiplicity). For `a ≤ d ≤ b`, the roots of a
multiset in `(a, b]` are those in `(a, d]` plus those in `(d, b]`. The multiplicity-aware companion
of Sturm's Finset `split`; needed because Budan–Fourier counts roots *with* multiplicity. -/
public theorem rootCount_split (M : Multiset ℝ) {a d b : ℝ} (had : a ≤ d) (hdb : d ≤ b) :
    (M.filter (fun x => a < x ∧ x ≤ b)).card
      = (M.filter (fun x => a < x ∧ x ≤ d)).card + (M.filter (fun x => d < x ∧ x ≤ b)).card := by
  rw [← Multiset.card_add]
  congr 1
  rw [Multiset.filter_add_filter]
  have h1 : M.filter (fun x => (a < x ∧ x ≤ d) ∧ (d < x ∧ x ≤ b)) = 0 := by
    rw [Multiset.filter_eq_nil]
    rintro x _ ⟨⟨_, hxd⟩, hdx, _⟩
    exact absurd hdx (not_lt.mpr hxd)
  have h2 : M.filter (fun x => (a < x ∧ x ≤ d) ∨ (d < x ∧ x ≤ b))
          = M.filter (fun x => a < x ∧ x ≤ b) := by
    apply Multiset.filter_congr
    intro x _
    constructor
    · rintro (⟨hax, hxd⟩ | ⟨hdx, hxb⟩)
      · exact ⟨hax, hxd.trans hdb⟩
      · exact ⟨had.trans_lt hdx, hxb⟩
    · rintro ⟨hax, hxb⟩
      rcases le_or_gt x d with h | h
      · exact Or.inl ⟨hax, h⟩
      · exact Or.inr ⟨h, hxb⟩
  rw [h1, h2, Multiset.add_zero]

/-! ## The recursive monotonicity bricks (foundation of the block analysis)

The derivative tower steps `p^(k+1) = (p^(k))′`. So if `p^(k)` vanishes at `c` and `p^(k+1)` keeps a
constant nonzero sign just off `c`, then `p^(k)` is strictly monotone there and its sign just off `c`
is determined: **same** sign as `p^(k+1)` on the right, **opposite** on the left. This one-step
recursion replaces the Taylor/`rootMultiplicity` bookkeeping entirely. -/

/-- **Sign just right of a root = sign of the derivative there.** If `q(c) = 0` and `q′` keeps the
constant nonzero sign `s` on `(c, z]`, then `sign (q z) = s`. -/
theorem sign_eval_right_of_deriv_sign {q : Polynomial ℝ} {c z : ℝ} {s : SignType}
    (hqc : q.eval c = 0) (hcz : c < z) (hs : s ≠ 0)
    (hsign : ∀ w ∈ Set.Ioc c z, SignType.sign ((derivative q).eval w) = s) :
    SignType.sign (q.eval z) = s := by
  have hcont : ContinuousOn (fun x => q.eval x) (Set.Icc c z) := q.continuous.continuousOn
  have hqz' : (derivative q).eval z ≠ 0 := by
    intro h; exact hs (by rw [← hsign z ⟨hcz, le_refl z⟩, h, sign_zero])
  rcases lt_or_gt_of_ne hqz' with hneg | hpos
  · have hsneg : s = -1 := by rw [← hsign z ⟨hcz, le_refl z⟩]; exact sign_neg hneg
    have hmono : StrictAntiOn (fun x => q.eval x) (Set.Icc c z) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc c z) hcont
      intro x hx
      rw [interior_Icc] at hx
      rw [Polynomial.deriv]
      have hxs := hsign x ⟨hx.1, hx.2.le⟩
      rw [hsneg] at hxs
      exact sign_eq_neg_one_iff.mp hxs
    have hlt : q.eval z < q.eval c := hmono ⟨le_refl c, hcz.le⟩ ⟨hcz.le, le_refl z⟩ hcz
    rw [hqc] at hlt; rw [hsneg]; exact sign_neg hlt
  · have hspos : s = 1 := by rw [← hsign z ⟨hcz, le_refl z⟩]; exact sign_pos hpos
    have hmono : StrictMonoOn (fun x => q.eval x) (Set.Icc c z) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc c z) hcont
      intro x hx
      rw [interior_Icc] at hx
      rw [Polynomial.deriv]
      have hxs := hsign x ⟨hx.1, hx.2.le⟩
      rw [hspos] at hxs
      exact sign_eq_one_iff.mp hxs
    have hlt : q.eval c < q.eval z := hmono ⟨le_refl c, hcz.le⟩ ⟨hcz.le, le_refl z⟩ hcz
    rw [hqc] at hlt; rw [hspos]; exact sign_pos hlt

/-- **Sign just left of a root = opposite sign of the derivative there.** If `q(c) = 0` and `q′`
keeps the constant nonzero sign `s` on `[z, c)`, then `sign (q z) = -s`. -/
theorem sign_eval_left_of_deriv_sign {q : Polynomial ℝ} {c z : ℝ} {s : SignType}
    (hqc : q.eval c = 0) (hzc : z < c) (hs : s ≠ 0)
    (hsign : ∀ w ∈ Set.Ico z c, SignType.sign ((derivative q).eval w) = s) :
    SignType.sign (q.eval z) = -s := by
  have hcont : ContinuousOn (fun x => q.eval x) (Set.Icc z c) := q.continuous.continuousOn
  have hqz' : (derivative q).eval z ≠ 0 := by
    intro h; exact hs (by rw [← hsign z ⟨le_refl z, hzc⟩, h, sign_zero])
  rcases lt_or_gt_of_ne hqz' with hneg | hpos
  · have hsneg : s = -1 := by rw [← hsign z ⟨le_refl z, hzc⟩]; exact sign_neg hneg
    have hmono : StrictAntiOn (fun x => q.eval x) (Set.Icc z c) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc z c) hcont
      intro x hx
      rw [interior_Icc] at hx
      rw [Polynomial.deriv]
      have hxs := hsign x ⟨hx.1.le, hx.2⟩
      rw [hsneg] at hxs
      exact sign_eq_neg_one_iff.mp hxs
    have hlt : q.eval c < q.eval z := hmono ⟨le_refl z, hzc.le⟩ ⟨hzc.le, le_refl c⟩ hzc
    rw [hqc] at hlt; rw [hsneg]
    rw [show -(-1 : SignType) = 1 by decide]; exact sign_pos hlt
  · have hspos : s = 1 := by rw [← hsign z ⟨le_refl z, hzc⟩]; exact sign_pos hpos
    have hmono : StrictMonoOn (fun x => q.eval x) (Set.Icc z c) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc z c) hcont
      intro x hx
      rw [interior_Icc] at hx
      rw [Polynomial.deriv]
      have hxs := hsign x ⟨hx.1.le, hx.2⟩
      rw [hspos] at hxs
      exact sign_eq_one_iff.mp hxs
    have hlt : q.eval z < q.eval c := hmono ⟨le_refl z, hzc.le⟩ ⟨hzc.le, le_refl c⟩ hzc
    rw [hqc] at hlt; rw [hspos, show -(1 : SignType) = -1 by decide]; exact sign_neg hlt

/-! ## Per-member off-`c` sign recursion (item 1: iterate the bricks up the block)

For each tower member, its sign just off `c` is fixed by whether it vanishes at `c`:
* **kept** (`q(c) ≠ 0`): the sign just off `c` equals `sign (q c)` (both sides), by local constancy;
* **vanishing** (`q(c) = 0`): on the **right** it copies the derivative's sign, on the **left** the
  opposite — one step of the brick recursion.
Iterated up a vanishing block, these give: right of `c` the block copies the first kept sign above
it (no new sign change), left of `c` it alternates. -/

/-- Kept member, right of `c`: constant sign. -/
theorem sign_eval_right_kept {q : Polynomial ℝ} {c b z : ℝ} (hqc : q.eval c ≠ 0)
    (hcz : c < z) (hzb : z ≤ b) (hqno : ∀ w ∈ Set.Ioc c b, q.eval w ≠ 0) :
    SignType.sign (q.eval z) = SignType.sign (q.eval c) := by
  rw [eq_comm]
  apply Sturm.sign_eval_eq_of_no_root hcz.le
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]; exact hqc
  · exact hqno x ⟨h, hx.2.trans hzb⟩

/-- Kept member, left of `c`: constant sign. -/
theorem sign_eval_left_kept {q : Polynomial ℝ} {a c z : ℝ} (hqc : q.eval c ≠ 0)
    (hzc : z < c) (haz : a ≤ z) (hqno : ∀ w ∈ Set.Ico a c, q.eval w ≠ 0) :
    SignType.sign (q.eval z) = SignType.sign (q.eval c) := by
  apply Sturm.sign_eval_eq_of_no_root hzc.le
  intro x hx
  rcases eq_or_lt_of_le hx.2 with h | h
  · rw [h]; exact hqc
  · exact hqno x ⟨haz.trans hx.1, h⟩

/-- Vanishing member, right of `c`: copies the derivative's sign. -/
theorem sign_eval_right_vanish {q : Polynomial ℝ} {c b z : ℝ} (hqc : q.eval c = 0)
    (hcz : c < z) (hzb : z ≤ b) (hq'no : ∀ w ∈ Set.Ioc c b, (derivative q).eval w ≠ 0) :
    SignType.sign (q.eval z) = SignType.sign ((derivative q).eval z) := by
  have hsign : ∀ w ∈ Set.Ioc c z, SignType.sign ((derivative q).eval w)
      = SignType.sign ((derivative q).eval z) := by
    intro w hw
    apply Sturm.sign_eval_eq_of_no_root hw.2
    intro x hx
    exact hq'no x ⟨lt_of_lt_of_le hw.1 hx.1, hx.2.trans hzb⟩
  have hs : SignType.sign ((derivative q).eval z) ≠ 0 := by
    rw [Ne, sign_eq_zero_iff]; exact hq'no z ⟨hcz, hzb⟩
  exact sign_eval_right_of_deriv_sign hqc hcz hs hsign

/-- Vanishing member, left of `c`: opposite of the derivative's sign. -/
theorem sign_eval_left_vanish {q : Polynomial ℝ} {a c z : ℝ} (hqc : q.eval c = 0)
    (hzc : z < c) (haz : a ≤ z) (hq'no : ∀ w ∈ Set.Ico a c, (derivative q).eval w ≠ 0) :
    SignType.sign (q.eval z) = - SignType.sign ((derivative q).eval z) := by
  have hsign : ∀ w ∈ Set.Ico z c, SignType.sign ((derivative q).eval w)
      = SignType.sign ((derivative q).eval z) := by
    intro w hw
    rw [eq_comm]
    apply Sturm.sign_eval_eq_of_no_root hw.1
    intro x hx
    exact hq'no x ⟨haz.trans hx.1, lt_of_le_of_lt hx.2 hw.2⟩
  have hs : SignType.sign ((derivative q).eval z) ≠ 0 := by
    rw [Ne, sign_eq_zero_iff]; exact hq'no z ⟨haz, hzc⟩
  exact sign_eval_left_of_deriv_sign hqc hzc hs hsign

/-! ## The pure sign-list combinatorics (items 2+3, decoupled from polynomials)

The two off-`c` sign sequences are abstracted as list functions of the at-`c` sign list `s` (entry
`0` = vanishing member, `±1` = kept). Building from the right with the item-1 recursions:
* `Rseq` (signs at `b`): a vanishing entry copies the value above it (`headD`);
* `Lseq` (signs at `a`): a vanishing entry negates the value above it.
The right side collapses (`signChanges (Rseq s) = signChanges s`, i.e. `V(b) = V(c)`); the left side
adds the leading-zero run plus an even surplus (the Budan–Fourier drop + parity). -/

/-- Signs just right of `c`: a vanishing member copies the sign above it. -/
def Rseq : List SignType → List SignType
  | [] => []
  | σ :: rest => if σ = 0 then ((Rseq rest).headD 0) :: Rseq rest else σ :: Rseq rest

/-- Signs just left of `c`: a vanishing member negates the sign above it. -/
def Lseq : List SignType → List SignType
  | [] => []
  | σ :: rest => if σ = 0 then (-(Lseq rest).headD 0) :: Lseq rest else σ :: Lseq rest

/-- **Right side collapses to the at-`c` count.** The vanishing members copy their kept successor, so
they destutter away: `signChanges (Rseq s) = signChanges s`. (Also: `Rseq s` is all-nonzero and shares
its leading surviving sign with `s`.) Needs the last entry nonzero (the leading coefficient never
vanishes). -/
theorem Rseq_spec : ∀ (s : List SignType), (∀ h : s ≠ [], s.getLast h ≠ 0) →
    (∀ y ∈ Rseq s, y ≠ 0) ∧ (Rseq s).head? = (s.filter (· ≠ 0)).head? ∧
    Sturm.signChanges (Rseq s) = Sturm.signChanges s := by
  intro s
  induction s with
  | nil => intro _; exact ⟨by simp [Rseq], by simp [Rseq], by simp [Rseq]⟩
  | cons σ rest ih =>
    intro hs
    have hs' : ∀ h : rest ≠ [], rest.getLast h ≠ 0 := fun h => by
      rw [← List.getLast_cons h]; exact hs (List.cons_ne_nil σ rest)
    obtain ⟨ihne, ihhead, ihsc⟩ := ih hs'
    by_cases hσ : σ = 0
    · subst hσ
      have hrest : rest ≠ [] := by
        rintro rfl; exact hs (by simp) (by simp)
      have hfe : rest.filter (· ≠ 0) ≠ [] := by
        intro h
        exact (hs' hrest) (by
          have := List.getLast_mem hrest
          by_contra hne
          exact (List.filter_eq_nil_iff.1 h) (rest.getLast hrest) this (by simpa using hne))
      obtain ⟨d, hd⟩ : ∃ d, (rest.filter (· ≠ 0)).head? = some d := by
        cases hh : (rest.filter (· ≠ 0)).head? with
        | none => exact absurd (List.head?_eq_none_iff.1 hh) hfe
        | some d => exact ⟨d, rfl⟩
      have hRhd : (Rseq rest).head? = some d := by rw [ihhead]; exact hd
      have hRne : Rseq rest ≠ [] := by intro h; rw [h] at hRhd; simp at hRhd
      obtain ⟨hh, tt, hcons⟩ := List.exists_cons_of_ne_nil hRne
      have hhd0 : (Rseq rest).headD 0 = hh := by rw [hcons]; rfl
      have hhne : hh ≠ 0 := ihne hh (by rw [hcons]; exact List.mem_cons_self ..)
      have hRdef : Rseq (0 :: rest) = hh :: Rseq rest := by
        simp only [Rseq, hhd0, if_true]
      have hfhd : ((Rseq rest).filter (· ≠ 0)).head? = some hh := by
        rw [List.filter_eq_self.2 (fun y hy => by simpa using ihne y hy), hcons, List.head?_cons]
      refine ⟨?_, ?_, ?_⟩
      · rw [hRdef]; intro y hy
        rcases List.mem_cons.1 hy with h | h
        · rw [h]; exact hhne
        · exact ihne y h
      · rw [hRdef, List.head?_cons, List.filter_cons_of_neg (by simp), ← ihhead, hcons]; rfl
      · rw [hRdef, Sturm.signChanges_cons_zero, Sturm.signChanges_cons_of_ne_zero hhne hfhd,
          if_pos rfl, Nat.add_zero, ihsc]
    · have hRdef : Rseq (σ :: rest) = σ :: Rseq rest := by simp only [Rseq, if_neg hσ]
      refine ⟨?_, ?_, ?_⟩
      · rw [hRdef]; intro y hy
        rcases List.mem_cons.1 hy with h | h
        · rw [h]; exact hσ
        · exact ihne y h
      · rw [hRdef, List.head?_cons, Sturm.filter_ne_zero_head?_cons hσ]
      · rw [hRdef]
        by_cases hfe : rest.filter (· ≠ 0) = []
        · have hRe : Rseq rest = [] := by
            rw [← List.head?_eq_none_iff]; rw [ihhead, hfe]; rfl
          rw [hRe, Sturm.signChanges_cons_of_filter_nil (by simp),
            Sturm.signChanges_cons_of_filter_nil hfe]
        · obtain ⟨d, hd⟩ : ∃ d, (rest.filter (· ≠ 0)).head? = some d := by
            cases hh : (rest.filter (· ≠ 0)).head? with
            | none => exact absurd (List.head?_eq_none_iff.1 hh) hfe
            | some d => exact ⟨d, rfl⟩
          have hdR : ((Rseq rest).filter (· ≠ 0)).head? = some d := by
            rw [List.filter_eq_self.2 (fun y hy => by simpa using ihne y hy), ihhead]; exact hd
          rw [Sturm.signChanges_cons_of_ne_zero hσ hdR, Sturm.signChanges_cons_of_ne_zero hσ hd, ihsc]

/-- `Rseq` preserves length. -/
theorem Rseq_length (s : List SignType) : (Rseq s).length = s.length := by
  induction s with
  | nil => rfl
  | cons σ rest ih => by_cases hσ : σ = 0 <;> simp [Rseq, hσ, ih]

/-- `Lseq` preserves length. -/
theorem Lseq_length (s : List SignType) : (Lseq s).length = s.length := by
  induction s with
  | nil => rfl
  | cons σ rest ih => by_cases hσ : σ = 0 <;> simp [Lseq, hσ, ih]

/-- **Left side adds the leading-zero run plus an even surplus.** The Budan–Fourier drop: the top
vanishing block alternates (contributing its length `= rootMult`), interior blocks contribute an even
amount. Carries the head sign-parity relation `Lhead = (-1)^{leadingZeros} · Rhead` as the induction
invariant. -/
theorem Lseq_spec : ∀ (s : List SignType), (∀ h : s ≠ [], s.getLast h ≠ 0) →
    (∀ y ∈ Lseq s, y ≠ 0) ∧
    (Lseq s).headD 0 = (-1 : SignType) ^ ((s.takeWhile (· = 0)).length) * (Rseq s).headD 0 ∧
    ∃ g, Sturm.signChanges (Lseq s)
       = Sturm.signChanges (Rseq s) + (s.takeWhile (· = 0)).length + 2 * g := by
  intro s
  induction s with
  | nil => intro _; exact ⟨by simp [Lseq], by simp [Lseq, Rseq], 0, by simp [Lseq, Rseq]⟩
  | cons σ rest ih =>
    intro hs
    have hs' : ∀ h : rest ≠ [], rest.getLast h ≠ 0 := fun h => by
      rw [← List.getLast_cons h]; exact hs (List.cons_ne_nil σ rest)
    obtain ⟨ihne, ihhead, g', ihsc⟩ := ih hs'
    obtain ⟨ihneR, _, _⟩ := Rseq_spec rest hs'
    by_cases hσ : σ = 0
    · subst hσ
      have hrest : rest ≠ [] := by rintro rfl; exact hs (by simp) (by simp)
      have hLne : Lseq rest ≠ [] := by
        rw [← List.length_pos_iff, Lseq_length]; exact List.length_pos_of_ne_nil hrest
      have hRne : Rseq rest ≠ [] := by
        rw [← List.length_pos_iff, Rseq_length]; exact List.length_pos_of_ne_nil hrest
      obtain ⟨L0, Lt, hLc⟩ := List.exists_cons_of_ne_nil hLne
      obtain ⟨R0, Rt, hRc⟩ := List.exists_cons_of_ne_nil hRne
      have hL0ne : L0 ≠ 0 := ihne L0 (hLc ▸ List.mem_cons_self ..)
      have hR0ne : R0 ≠ 0 := ihneR R0 (hRc ▸ List.mem_cons_self ..)
      have hLd0 : (Lseq rest).headD 0 = L0 := by rw [hLc]; rfl
      have hRd0 : (Rseq rest).headD 0 = R0 := by rw [hRc]; rfl
      have hrel : L0 = (-1 : SignType) ^ ((rest.takeWhile (· = 0)).length) * R0 := by
        rw [← hLd0, ← hRd0]; exact ihhead
      have hLdef : Lseq (0 :: rest) = (-L0) :: Lseq rest := by simp only [Lseq, hLd0, if_true]
      have hRdef : Rseq (0 :: rest) = R0 :: Rseq rest := by simp only [Rseq, hRd0, if_true]
      have htw : ((0 :: rest).takeWhile (· = 0)).length
          = (rest.takeWhile (· = 0)).length + 1 := by
        rw [List.takeWhile_cons_of_pos (by decide), List.length_cons]
      have hnegL0ne : -L0 ≠ 0 := fun h => hL0ne (SignType.neg_eq_zero_iff.mp h)
      have hnegself : -L0 ≠ L0 := fun h => hL0ne (SignType.neg_eq_self_iff.mp h)
      refine ⟨?_, ?_, ?_⟩
      · rw [hLdef]; intro y hy
        rcases List.mem_cons.1 hy with h | h
        · rw [h]; exact hnegL0ne
        · exact ihne y h
      · rw [hLdef, hRdef]
        show -L0 = (-1 : SignType) ^ (((0 :: rest).takeWhile (· = 0)).length) * R0
        rw [htw, pow_succ, hrel, mul_neg_one, neg_mul]
      · have hLfhd : ((Lseq rest).filter (· ≠ 0)).head? = some L0 := by
          rw [List.filter_eq_self.2 (fun y hy => by simpa using ihne y hy), hLc]; rfl
        have hRfhd : ((Rseq rest).filter (· ≠ 0)).head? = some R0 := by
          rw [List.filter_eq_self.2 (fun y hy => by simpa using ihneR y hy), hRc]; rfl
        refine ⟨g', ?_⟩
        rw [hLdef, hRdef, Sturm.signChanges_cons_of_ne_zero hnegL0ne hLfhd,
          Sturm.signChanges_cons_of_ne_zero hR0ne hRfhd, if_neg hnegself, if_pos rfl, htw, ihsc]
        omega
    · have hLdef : Lseq (σ :: rest) = σ :: Lseq rest := by simp only [Lseq, if_neg hσ]
      have hRdef : Rseq (σ :: rest) = σ :: Rseq rest := by simp only [Rseq, if_neg hσ]
      have htw0 : ((σ :: rest).takeWhile (· = 0)).length = 0 := by
        rw [List.takeWhile_cons_of_neg (by simpa using hσ)]; rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hLdef]; intro y hy
        rcases List.mem_cons.1 hy with h | h
        · rw [h]; exact hσ
        · exact ihne y h
      · rw [hLdef, hRdef]
        show σ = (-1 : SignType) ^ (((σ :: rest).takeWhile (· = 0)).length) * σ
        rw [htw0, pow_zero, one_mul]
      · by_cases hre : rest = []
        · subst hre
          refine ⟨0, ?_⟩
          rw [show Lseq [σ] = [σ] from by simp [Lseq, if_neg hσ],
            show Rseq [σ] = [σ] from by simp [Rseq, if_neg hσ], htw0]
          omega
        · have hLne : Lseq rest ≠ [] := by
            rw [← List.length_pos_iff, Lseq_length]; exact List.length_pos_of_ne_nil hre
          have hRne : Rseq rest ≠ [] := by
            rw [← List.length_pos_iff, Rseq_length]; exact List.length_pos_of_ne_nil hre
          obtain ⟨L0, Lt, hLc⟩ := List.exists_cons_of_ne_nil hLne
          obtain ⟨R0, Rt, hRc⟩ := List.exists_cons_of_ne_nil hRne
          have hL0ne : L0 ≠ 0 := ihne L0 (hLc ▸ List.mem_cons_self ..)
          have hR0ne : R0 ≠ 0 := ihneR R0 (hRc ▸ List.mem_cons_self ..)
          have hLd0 : (Lseq rest).headD 0 = L0 := by rw [hLc]; rfl
          have hRd0 : (Rseq rest).headD 0 = R0 := by rw [hRc]; rfl
          have hrel : L0 = (-1 : SignType) ^ ((rest.takeWhile (· = 0)).length) * R0 := by
            rw [← hLd0, ← hRd0]; exact ihhead
          have hLfhd : ((Lseq rest).filter (· ≠ 0)).head? = some L0 := by
            rw [List.filter_eq_self.2 (fun y hy => by simpa using ihne y hy), hLc]; rfl
          have hRfhd : ((Rseq rest).filter (· ≠ 0)).head? = some R0 := by
            rw [List.filter_eq_self.2 (fun y hy => by simpa using ihneR y hy), hRc]; rfl
          rw [hLdef, hRdef, Sturm.signChanges_cons_of_ne_zero hσ hLfhd,
            Sturm.signChanges_cons_of_ne_zero hσ hRfhd, htw0]
          rcases Nat.even_or_odd ((rest.takeWhile (· = 0)).length) with hev | hod
          · have hpow : (-1 : SignType) ^ ((rest.takeWhile (· = 0)).length) = 1 :=
              Even.neg_one_pow hev
            obtain ⟨m, hm⟩ := hev
            have hL0R0 : L0 = R0 := by rw [hrel, hpow, one_mul]
            refine ⟨m + g', ?_⟩
            rw [hL0R0]; omega
          · have hpow : (-1 : SignType) ^ ((rest.takeWhile (· = 0)).length) = -1 :=
              Odd.neg_one_pow hod
            obtain ⟨m, hm⟩ := hod
            have hL0R0 : L0 = -R0 := by rw [hrel, hpow, neg_one_mul]
            by_cases hσR : σ = R0
            · have hiL : ¬ (σ = L0) := by
                rw [hL0R0, hσR]; exact fun h => hR0ne (SignType.neg_eq_self_iff.mp h.symm)
              refine ⟨m + g' + 1, ?_⟩
              rw [if_neg hiL, if_pos hσR]; omega
            · have hiL : σ = L0 := by
                rw [hL0R0]; revert hσ hσR hR0ne
                rcases σ with _ | _ | _ <;> rcases R0 with _ | _ | _ <;> decide
              refine ⟨m + g', ?_⟩
              rw [if_pos hiL, if_neg hσR]; omega

/-! ## Plumbing: the polynomial tower realizes the abstract sign lists `Rseq`/`Lseq`

The two list lemmas `Rseq_spec`/`Lseq_spec` are stated about an abstract list of signs. Here we show
that, for the derivative tower, the sign pattern at `b` (right of the critical point `c`) *is* `Rseq`
of the pattern at `c`, and the pattern at `a` (left) *is* `Lseq` of it — the per-member recursion of
the monotonicity bricks, threaded up the tower via its derivative-chain structure. -/

/-- The top derivative `p^(deg p)` is a nonzero constant, so it never vanishes. -/
theorem iterate_derivative_natDegree_eval_ne {p : Polynomial ℝ} (hp : p ≠ 0) (x : ℝ) :
    ((derivative^[p.natDegree]) p).eval x ≠ 0 := by
  have hdeg : ((derivative^[p.natDegree]) p).natDegree = 0 :=
    Nat.le_zero.mp (by simpa using natDegree_iterate_derivative p p.natDegree)
  have hne : (derivative^[p.natDegree]) p ≠ 0 :=
    fourierSeq_mem_ne_zero hp _ (by rw [fourierSeq_mem]; exact ⟨p.natDegree, le_refl _, rfl⟩)
  rw [eq_C_of_natDegree_eq_zero hdeg, eval_C]
  intro h0
  exact hne (by rw [eq_C_of_natDegree_eq_zero hdeg]; simp [h0])

/-- The last member of the Fourier sequence is `p^(deg p)`. -/
theorem fourierSeq_getLast {p : Polynomial ℝ} (h : fourierSeq p ≠ []) :
    (fourierSeq p).getLast h = (derivative^[p.natDegree]) p := by
  have hrw : fourierSeq p
      = (List.range p.natDegree).map (fun k => (derivative^[k]) p)
        ++ [(derivative^[p.natDegree]) p] := by
    rw [fourierSeq, List.range_succ, List.map_append, List.map_singleton]
  simp only [hrw, List.getLast_append_singleton]

/-- The last member of the Fourier sequence never vanishes. -/
theorem fourierSeq_getLast_eval_ne {p : Polynomial ℝ} (hp : p ≠ 0) (x : ℝ)
    (h : fourierSeq p ≠ []) : ((fourierSeq p).getLast h).eval x ≠ 0 := by
  rw [fourierSeq_getLast h]; exact iterate_derivative_natDegree_eval_ne hp x

/-- The `i`-th member of the Fourier sequence is `p^(i)`. -/
theorem fourierSeq_getElem? (p : Polynomial ℝ) (i : ℕ) (hi : i < p.natDegree + 1) :
    (fourierSeq p)[i]? = some ((derivative^[i]) p) := by
  rw [fourierSeq, List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- The Fourier sequence is a derivative chain: each member is the derivative of the previous. -/
theorem fourierSeq_isChain (p : Polynomial ℝ) :
    List.IsChain (fun q q' => q' = derivative q) (fourierSeq p) := by
  rw [fourierSeq, List.isChain_map]
  refine (List.isChain_range_succ _ p.natDegree).mpr ?_
  intro m _
  exact Function.iterate_succ_apply' derivative m p

/-- **Right side = `Rseq`.** For a derivative chain `L` whose last member is nonzero at `c` and none
of whose members vanishes on `(c, b]`, the sign pattern at `b` equals `Rseq` of the pattern at `c`. -/
theorem signs_right_eq_Rseq {c b : ℝ} (hcb : c < b) :
    ∀ (L : List (Polynomial ℝ)),
      List.IsChain (fun q q' => q' = derivative q) L →
      (∀ h : L ≠ [], ((L.getLast h).eval c) ≠ 0) →
      (∀ q ∈ L, ∀ z ∈ Set.Ioc c b, q.eval z ≠ 0) →
      L.map (fun q => SignType.sign (q.eval b))
        = Rseq (L.map (fun q => SignType.sign (q.eval c))) := by
  intro L
  induction L with
  | nil => intro _ _ _; rfl
  | cons q rest ih =>
    intro hchain hlast hno
    have hchain_rest := (List.isChain_cons.mp hchain).2
    have hno_rest : ∀ q' ∈ rest, ∀ z ∈ Set.Ioc c b, q'.eval z ≠ 0 :=
      fun q' hq' => hno q' (List.mem_cons_of_mem q hq')
    have hlast_rest : ∀ h : rest ≠ [], ((rest.getLast h).eval c) ≠ 0 := by
      intro h; have := hlast (List.cons_ne_nil q rest); rwa [List.getLast_cons h] at this
    have hIH := ih hchain_rest hlast_rest hno_rest
    rw [List.map_cons, List.map_cons]
    by_cases hqc : SignType.sign (q.eval c) = 0
    · have hqc0 : q.eval c = 0 := by rwa [sign_eq_zero_iff] at hqc
      have hrest : rest ≠ [] := by
        rintro rfl; exact (hlast (List.cons_ne_nil q [])) (by simpa using hqc0)
      obtain ⟨r, rest', hrc⟩ := List.exists_cons_of_ne_nil hrest
      have hr : r = derivative q := (List.isChain_cons.mp hchain).1 r (by rw [hrc]; rfl)
      have hRdef : Rseq (SignType.sign (q.eval c)
            :: rest.map (fun q => SignType.sign (q.eval c)))
          = ((Rseq (rest.map (fun q => SignType.sign (q.eval c)))).headD 0)
            :: Rseq (rest.map (fun q => SignType.sign (q.eval c))) := by
        simp only [Rseq, if_pos hqc]
      rw [hRdef, ← hIH]
      congr 1
      rw [hrc, List.map_cons]
      show SignType.sign (q.eval b) = SignType.sign (r.eval b)
      rw [hr]
      exact sign_eval_right_vanish hqc0 hcb le_rfl
        (fun w hw => by rw [← hr]; exact hno_rest r (by rw [hrc]; exact List.mem_cons_self ..) w hw)
    · have hRdef : Rseq (SignType.sign (q.eval c)
            :: rest.map (fun q => SignType.sign (q.eval c)))
          = SignType.sign (q.eval c)
            :: Rseq (rest.map (fun q => SignType.sign (q.eval c))) := by
        simp only [Rseq, if_neg hqc]
      rw [hRdef, ← hIH]
      congr 1
      exact sign_eval_right_kept (by rwa [sign_eq_zero_iff] at hqc) hcb le_rfl
        (hno q (List.mem_cons_self ..))

/-- **Left side = `Lseq`.** Symmetric to `signs_right_eq_Rseq`: the sign pattern at `a` (left of `c`)
equals `Lseq` of the pattern at `c`. -/
theorem signs_left_eq_Lseq {a c : ℝ} (hac : a < c) :
    ∀ (L : List (Polynomial ℝ)),
      List.IsChain (fun q q' => q' = derivative q) L →
      (∀ h : L ≠ [], ((L.getLast h).eval c) ≠ 0) →
      (∀ q ∈ L, ∀ z ∈ Set.Ico a c, q.eval z ≠ 0) →
      L.map (fun q => SignType.sign (q.eval a))
        = Lseq (L.map (fun q => SignType.sign (q.eval c))) := by
  intro L
  induction L with
  | nil => intro _ _ _; rfl
  | cons q rest ih =>
    intro hchain hlast hno
    have hchain_rest := (List.isChain_cons.mp hchain).2
    have hno_rest : ∀ q' ∈ rest, ∀ z ∈ Set.Ico a c, q'.eval z ≠ 0 :=
      fun q' hq' => hno q' (List.mem_cons_of_mem q hq')
    have hlast_rest : ∀ h : rest ≠ [], ((rest.getLast h).eval c) ≠ 0 := by
      intro h; have := hlast (List.cons_ne_nil q rest); rwa [List.getLast_cons h] at this
    have hIH := ih hchain_rest hlast_rest hno_rest
    rw [List.map_cons, List.map_cons]
    by_cases hqc : SignType.sign (q.eval c) = 0
    · have hqc0 : q.eval c = 0 := by rwa [sign_eq_zero_iff] at hqc
      have hrest : rest ≠ [] := by
        rintro rfl; exact (hlast (List.cons_ne_nil q [])) (by simpa using hqc0)
      obtain ⟨r, rest', hrc⟩ := List.exists_cons_of_ne_nil hrest
      have hr : r = derivative q := (List.isChain_cons.mp hchain).1 r (by rw [hrc]; rfl)
      have hLdef : Lseq (SignType.sign (q.eval c)
            :: rest.map (fun q => SignType.sign (q.eval c)))
          = (-(Lseq (rest.map (fun q => SignType.sign (q.eval c)))).headD 0)
            :: Lseq (rest.map (fun q => SignType.sign (q.eval c))) := by
        simp only [Lseq, if_pos hqc]
      rw [hLdef, ← hIH]
      congr 1
      rw [hrc, List.map_cons]
      show SignType.sign (q.eval a) = -(SignType.sign (r.eval a))
      rw [hr]
      exact sign_eval_left_vanish hqc0 hac le_rfl
        (fun w hw => by rw [← hr]; exact hno_rest r (by rw [hrc]; exact List.mem_cons_self ..) w hw)
    · have hLdef : Lseq (SignType.sign (q.eval c)
            :: rest.map (fun q => SignType.sign (q.eval c)))
          = SignType.sign (q.eval c)
            :: Lseq (rest.map (fun q => SignType.sign (q.eval c))) := by
        simp only [Lseq, if_neg hqc]
      rw [hLdef, ← hIH]
      congr 1
      exact sign_eval_left_kept (by rwa [sign_eq_zero_iff] at hqc) hac le_rfl
        (hno q (List.mem_cons_self ..))

/-- **The leading-zero run of a sign list has the prescribed length.** If the first `r` entries are
`0` and entry `r` (when present) is nonzero, then `takeWhile (· = 0)` has length exactly `r`. -/
theorem takeWhile_eq_zero_length : ∀ (l : List SignType) (r : ℕ), r ≤ l.length →
    (∀ i, i < r → l[i]? = some 0) → (∀ x, l[r]? = some x → x ≠ 0) →
    (l.takeWhile (· = 0)).length = r := by
  intro l
  induction l with
  | nil => intro r hr _ _; simp only [List.length_nil, Nat.le_zero] at hr; rw [hr]; rfl
  | cons x xs ih =>
    intro r hr hlt hstop
    cases r with
    | zero =>
      have hx : x ≠ 0 := hstop x (by simp)
      rw [List.takeWhile_cons_of_neg (by simpa using hx)]
      rfl
    | succ r' =>
      have hx0 : x = 0 := by have := hlt 0 (Nat.succ_pos r'); simpa using this
      rw [List.takeWhile_cons_of_pos (by simp [hx0]), List.length_cons]
      have hr' : r' ≤ xs.length := by simp only [List.length_cons] at hr; omega
      have hlt' : ∀ i, i < r' → xs[i]? = some 0 := by
        intro i hi; have := hlt (i + 1) (by omega); simpa using this
      have hstop' : ∀ y, xs[r']? = some y → y ≠ 0 := by
        intro y hy; apply hstop y; simpa using hy
      rw [ih r' hr' hlt' hstop']

/-- **Local drop at a critical point — the analytic core.** The one piece with no
Sturm analogue: the derivative tower is *not* a coprime chain, so a whole block of consecutive
members `p^(i), …, p^(j)` may vanish at `c`. Stated in additive form `V(a) = V(b) + #roots(a,b] +
2e`, which packages BOTH the Budan–Fourier inequality `#roots ≤ V(a)−V(b)` and the even-difference
parity into a single existential that adds cleanly across the global induction (the locally-constant
case is `e = 0, #roots = 0`). Remaining work: Taylor/leading-term sign analysis of the vanishing
block left and right of `c`. -/
public theorem fourierVar_drop_at_critical_point {p : Polynomial ℝ} (hp : p ≠ 0)
    {a b c : ℝ} (hab : a ≤ b) (hc : c ∈ Set.Icc a b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0)
    (h_only : ∀ q ∈ fourierSeq p, ∀ z ∈ Set.Icc a b, q.eval z = 0 → z = c) :
    ∃ e, fourierVar p a = fourierVar p b
       + (p.roots.filter (fun x => a < x ∧ x ≤ b)).card + 2 * e := by
  obtain ⟨hca, hcb⟩ := hc
  have hpmem : p ∈ fourierSeq p := by
    rw [fourierSeq_mem]; exact ⟨0, Nat.zero_le _, by simp⟩
  set σ := (fourierSeq p).map (fun q => SignType.sign (q.eval c)) with hσdef
  -- σ's last entry is nonzero (the top derivative is a nonzero constant)
  have hσlast : ∀ h : σ ≠ [], σ.getLast h ≠ 0 := by
    intro h
    have hrw : σ = ((List.range p.natDegree).map (fun k => (derivative^[k]) p)).map
          (fun q => SignType.sign (q.eval c))
        ++ [SignType.sign (((derivative^[p.natDegree]) p).eval c)] := by
      rw [hσdef, fourierSeq, List.range_succ, List.map_append, List.map_singleton,
        List.map_append, List.map_singleton]
    simp only [hrw, List.getLast_append_singleton, ne_eq, sign_eq_zero_iff]
    exact iterate_derivative_natDegree_eval_ne hp c
  rw [fourierVar_eq_signVarAt, fourierVar_eq_signVarAt,
    Sturm.signVarAt_eq_signChanges, Sturm.signVarAt_eq_signChanges]
  obtain ⟨_, _, gL, hgL⟩ := Lseq_spec σ hσlast
  obtain ⟨_, _, hRsc⟩ := Rseq_spec σ hσlast
  -- the sign pattern at `b` reproduces `signChanges (Rseq σ)`
  have hRb : Sturm.signChanges ((fourierSeq p).map (fun q => SignType.sign (q.eval b)))
      = Sturm.signChanges (Rseq σ) := by
    rcases eq_or_lt_of_le hcb with hcbeq | hcblt
    · have hSb : (fourierSeq p).map (fun q => SignType.sign (q.eval b)) = σ := by
        rw [hσdef, hcbeq]
      rw [hSb, hRsc]
    · have hrt := signs_right_eq_Rseq hcblt (fourierSeq p) (fourierSeq_isChain p)
        (fun h => fourierSeq_getLast_eval_ne hp c h)
        (fun q hq z hz hqz =>
          (ne_of_lt hz.1) (h_only q hq z ⟨hca.trans hz.1.le, hz.2⟩ hqz).symm)
      rw [← hσdef] at hrt
      rw [hrt]
  rcases eq_or_lt_of_le hca with hcaeq | hcalt
  · -- `a = c`: no genuine left drop; no roots in `(a, b]`
    have hSa : (fourierSeq p).map (fun q => SignType.sign (q.eval a)) = σ := by
      rw [hσdef, hcaeq]
    have hroots0 : (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0 := by
      rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
      intro x hx
      rintro ⟨hax, hxb⟩
      have hxroot : p.eval x = 0 := (Polynomial.mem_roots'.mp hx).2
      have hxc : x = c := h_only p hpmem x ⟨hax.le, hxb⟩ hxroot
      have hxa : x = a := hxc.trans hcaeq.symm
      rw [hxa] at hax; exact lt_irrefl a hax
    refine ⟨0, ?_⟩
    rw [hSa, hroots0, hRb, hRsc]
    omega
  · -- `a < c`: the genuine drop, with `#roots = leading-zero run = rootMultiplicity`
    have hSa := signs_left_eq_Lseq hcalt (fourierSeq p) (fourierSeq_isChain p)
      (fun h => fourierSeq_getLast_eval_ne hp c h)
      (fun q hq z hz hqz =>
        (ne_of_lt hz.2) (h_only q hq z ⟨hz.1, (le_of_lt hz.2).trans hcb⟩ hqz))
    rw [← hσdef] at hSa
    set r := p.rootMultiplicity c with hrdef
    have hσlen : σ.length = p.natDegree + 1 := by
      rw [hσdef, List.length_map, fourierSeq_length]
    have hr_le : r ≤ p.natDegree := by
      have hdvd := p.pow_rootMultiplicity_dvd c
      have hle := Polynomial.natDegree_le_of_dvd hdvd hp
      simpa [natDegree_pow, Polynomial.natDegree_X_sub_C] using hle
    have hσget : ∀ i, i < p.natDegree + 1 →
        σ[i]? = some (SignType.sign (((derivative^[i]) p).eval c)) := by
      intro i hi
      rw [hσdef, List.getElem?_map, fourierSeq_getElem? p i hi, Option.map_some]
    -- the takeWhile-zero run has length `r = rootMultiplicity`
    have stepA : (σ.takeWhile (· = 0)).length = r := by
      apply takeWhile_eq_zero_length σ r (by rw [hσlen]; omega)
      · intro i hir
        rw [hσget i (by omega)]
        have hz : ((derivative^[i]) p).eval c = 0 :=
          isRoot_iterate_derivative_of_lt_rootMultiplicity hir
        rw [hz, sign_zero]
      · intro x hx
        rw [hσget r (by omega)] at hx
        have hxeq : x = SignType.sign (((derivative^[r]) p).eval c) := by
          injection hx with hx'; exact hx'.symm
        rw [hxeq]; simp only [ne_eq, sign_eq_zero_iff]
        intro h0
        have hroot_le : ∀ m ≤ r, ((derivative^[m]) p).IsRoot c := by
          intro m hm
          rcases lt_or_eq_of_le hm with hlt' | heq
          · exact isRoot_iterate_derivative_of_lt_rootMultiplicity hlt'
          · rw [heq]; exact h0
        have hfact : ((r.factorial : ℝ)) ∈ nonZeroDivisors ℝ := by
          rw [mem_nonZeroDivisors_iff_ne_zero]; exact_mod_cast Nat.factorial_ne_zero r
        have hlt'' : r < p.rootMultiplicity c :=
          (lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors hp hfact).mpr
            hroot_le
        exact absurd hlt'' (lt_irrefl r)
    -- `#roots(a,b] = rootMultiplicity c p` (every root in the interval equals `c`)
    have hB : (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = r := by
      have hfilter_eq : p.roots.filter (fun x => a < x ∧ x ≤ b)
          = p.roots.filter (fun x => c = x) := by
        apply Multiset.filter_congr
        intro x hx
        have hxroot : p.eval x = 0 := (Polynomial.mem_roots'.mp hx).2
        constructor
        · rintro ⟨hax, hxb⟩
          exact (h_only p hpmem x ⟨hax.le, hxb⟩ hxroot).symm
        · rintro rfl; exact ⟨hcalt, hcb⟩
      rw [hfilter_eq, ← Multiset.count_eq_card_filter_eq, Polynomial.count_roots]
    have hroots : (p.roots.filter (fun x => a < x ∧ x ≤ b)).card
        = (σ.takeWhile (· = 0)).length := by rw [hB]; exact stepA.symm
    refine ⟨gL, ?_⟩
    rw [hSa, hgL, hRb, hroots]

/-- **The Budan–Fourier theorem.** For nonzero `p` and `a < b` with neither endpoint a root, the
number of real roots of `p` in `(a, b]` counted with multiplicity is bounded by the drop in Fourier
sign variations, and has the same parity as that drop.

Proof (`sorry`-free): strong induction on the number of *distinct* critical points (roots of the
tower's product `Pc`) in `(a, b]`; peel the maximum one, split just below it, recurse left and apply
the local drop `fourierVar_drop_at_critical_point` on the right, combining the two additive
existentials. -/
public theorem budan_fourier (p : Polynomial ℝ) (hp : p ≠ 0) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (p.roots.filter (fun x => a < x ∧ x ≤ b)).card ≤ fourierVar p a - fourierVar p b ∧
    Even (fourierVar p a - fourierVar p b - (p.roots.filter (fun x => a < x ∧ x ≤ b)).card) := by
  set Pc := (fourierSeq p).prod with hPc
  have hPc0 : Pc ≠ 0 := fourierSeq_prod_ne_zero hp
  have hpmem : p ∈ fourierSeq p := by
    rw [fourierSeq_mem]; exact ⟨0, Nat.zero_le _, by simp⟩
  -- a root of any tower member is a root of the product (a "critical point")
  have hcrit : ∀ z, ∀ q ∈ fourierSeq p, q.eval z = 0 → Pc.eval z = 0 := by
    intro z q hq hqz
    have hev : ∀ (L : List (Polynomial ℝ)), L.prod.eval z = (L.map (fun r => r.eval z)).prod := by
      intro L
      induction L with
      | nil => simp
      | cons hd tl ih => rw [List.prod_cons, eval_mul, ih, List.map_cons, List.prod_cons]
    rw [hPc, hev]
    exact List.prod_eq_zero (List.mem_map.mpr ⟨q, hq, hqz⟩)
  -- Finset split of distinct critical points (the induction measure)
  have splitF : ∀ (Q : Polynomial ℝ) (a' d' b' : ℝ), a' ≤ d' → d' ≤ b' →
      (Q.roots.toFinset.filter (fun x => a' < x ∧ x ≤ b')).card
      = (Q.roots.toFinset.filter (fun x => a' < x ∧ x ≤ d')).card
      + (Q.roots.toFinset.filter (fun x => d' < x ∧ x ≤ b')).card := by
    intro Q a' d' b' had hdb
    have hdisj : Disjoint (Q.roots.toFinset.filter (fun x => a' < x ∧ x ≤ d'))
        (Q.roots.toFinset.filter (fun x => d' < x ∧ x ≤ b')) := by
      rw [Finset.disjoint_left]; rintro x hx1 hx2
      rw [Finset.mem_filter] at hx1 hx2
      exact absurd hx2.2.1 (not_lt.mpr hx1.2.2)
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hr, hax, hxb⟩
      by_cases hxd : x ≤ d'
      · exact Or.inl ⟨hr, hax, hxd⟩
      · exact Or.inr ⟨hr, not_le.mp hxd, hxb⟩
    · rintro (⟨hr, hax, hxd⟩ | ⟨hr, hdx, hxb⟩)
      · exact ⟨hr, hax, hxd.trans hdb⟩
      · exact ⟨hr, had.trans_lt hdx, hxb⟩
  -- main strong induction on the number of critical points in `(a, b]`
  suffices key : ∀ n, ∀ a b : ℝ, a ≤ b → p.eval a ≠ 0 → p.eval b ≠ 0 →
      (Pc.roots.toFinset.filter (fun x => a < x ∧ x ≤ b)).card = n →
      ∃ e, fourierVar p a = fourierVar p b
        + (p.roots.filter (fun x => a < x ∧ x ≤ b)).card + 2 * e by
    obtain ⟨e, he⟩ := key _ a b hab.le ha hb rfl
    exact ⟨by omega, e, by omega⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hab ha hb hcard
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- no critical point in `(a, b]`: the only possible tower root in `[a,b]` is the endpoint `a`
    subst hn0
    have hcset : Pc.roots.toFinset.filter (fun x => a < x ∧ x ≤ b) = ∅ :=
      Finset.card_eq_zero.mp hcard
    have h_only : ∀ q ∈ fourierSeq p, ∀ z ∈ Set.Icc a b, q.eval z = 0 → z = a := by
      intro q hq z hz hqz
      by_contra hza
      have haz : a < z := lt_of_le_of_ne hz.1 (Ne.symm hza)
      have hmem : z ∈ Pc.roots.toFinset.filter (fun x => a < x ∧ x ≤ b) := by
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots']
        exact ⟨⟨hPc0, hcrit z q hq hqz⟩, haz, hz.2⟩
      rw [hcset] at hmem; exact absurd hmem (Finset.notMem_empty z)
    exact fourierVar_drop_at_critical_point hp hab ⟨le_refl a, hab⟩ ha hb h_only
  · -- peel the maximum critical point `c`
    have hne : (Pc.roots.toFinset.filter (fun x => a < x ∧ x ≤ b)).Nonempty :=
      Finset.card_pos.mp (hcard ▸ hnpos)
    set c := (Pc.roots.toFinset.filter (fun x => a < x ∧ x ≤ b)).max' hne with hcdef
    have hc_mem := Finset.max'_mem _ hne
    rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots'] at hc_mem
    obtain ⟨⟨_, hcroot⟩, hac, hcb⟩ := hc_mem
    have hc_max : ∀ x ∈ Pc.roots.toFinset.filter (fun x => a < x ∧ x ≤ b), x ≤ c :=
      fun x hx => Finset.le_max' _ x hx
    obtain ⟨t, htc, hta, htB⟩ : ∃ t, t < c ∧ a ≤ t ∧
        (∀ x, Pc.eval x = 0 → a < x → x ≤ b → x < c → x ≤ t) := by
      set B := (Pc.roots.toFinset.filter (fun x => a < x ∧ x ≤ b)).filter (· < c) with hBdef
      rcases B.eq_empty_or_nonempty with hBe | hBne
      · refine ⟨a, hac, le_refl a, ?_⟩
        intro x hx0 hax hxb hxc
        exfalso
        have hxB : x ∈ B := by
          rw [hBdef, Finset.mem_filter, Finset.mem_filter, Multiset.mem_toFinset,
            Polynomial.mem_roots']
          exact ⟨⟨⟨hPc0, hx0⟩, hax, hxb⟩, hxc⟩
        rw [hBe] at hxB; exact absurd hxB (Finset.notMem_empty x)
      · refine ⟨B.max' hBne, ?_, ?_, ?_⟩
        · exact (Finset.mem_filter.mp (Finset.max'_mem B hBne)).2
        · exact ((Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.max'_mem B hBne)).1).2.1).le
        · intro x hx0 hax hxb hxc
          apply Finset.le_max'
          rw [hBdef, Finset.mem_filter, Finset.mem_filter, Multiset.mem_toFinset,
            Polynomial.mem_roots']
          exact ⟨⟨⟨hPc0, hx0⟩, hax, hxb⟩, hxc⟩
    set d := (t + c) / 2 with hddef
    have htd : t < d := by rw [hddef]; linarith
    have hdc : d < c := by rw [hddef]; linarith
    have had : a ≤ d := hta.trans htd.le
    have hdb : d ≤ b := hdc.le.trans hcb
    have hPcd : Pc.eval d ≠ 0 := by
      intro h0
      have hdt : d ≤ t := htB d h0 (lt_of_le_of_lt hta htd) (hdc.le.trans hcb) hdc
      linarith
    have hpd : p.eval d ≠ 0 := fun h => hPcd (hcrit d p hpmem h)
    -- in `(d, b]` the only critical point is `c`
    have hdb_eq_c : ∀ (Q : Polynomial ℝ), (∀ z, Q.eval z = 0 → Pc.eval z = 0) →
        ∀ x ∈ Q.roots.toFinset.filter (fun y => d < y ∧ y ≤ b), x = c := by
      intro Q hQ x hx
      rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots'] at hx
      obtain ⟨⟨_, hxroot⟩, hdx, hxb⟩ := hx
      have hx0 : Pc.eval x = 0 := hQ x hxroot
      have hax : a < x := lt_of_le_of_lt had hdx
      have hxc_le : x ≤ c := hc_max x (by
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots']
        exact ⟨⟨hPc0, hx0⟩, hax, hxb⟩)
      rcases lt_or_eq_of_le hxc_le with hlt | heq
      · exfalso; have := htB x hx0 hax hxb hlt; linarith
      · exact heq
    have hcset_db : (Pc.roots.toFinset.filter (fun x => d < x ∧ x ≤ b)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨c, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun x hx =>
        hdb_eq_c Pc (fun z hz => hz) x hx⟩⟩
      rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots']
      exact ⟨⟨hPc0, hcroot⟩, hdc, hcb⟩
    have h_only_db : ∀ q ∈ fourierSeq p, ∀ z ∈ Set.Icc d b, q.eval z = 0 → z = c := by
      intro q hq z hz hqz
      refine hdb_eq_c Pc (fun w hw => hw) z ?_
      rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots']
      refine ⟨⟨hPc0, hcrit z q hq hqz⟩, ?_, hz.2⟩
      rcases lt_or_eq_of_le hz.1 with h | h
      · exact h
      · exfalso; exact hPcd (by rw [h]; exact hcrit z q hq hqz)
    have hstep := fourierVar_drop_at_critical_point hp hdb ⟨hdc.le, hcb⟩ hpd hb h_only_db
    have hcard_ad : (Pc.roots.toFinset.filter (fun x => a < x ∧ x ≤ d)).card = n - 1 := by
      have hsp := splitF Pc a d b had hdb
      rw [hcard, hcset_db] at hsp
      omega
    have hrec := ih (n - 1) (by omega) a d had ha hpd hcard_ad
    obtain ⟨e1, he1⟩ := hrec
    obtain ⟨e2, he2⟩ := hstep
    have hpsplit := rootCount_split p.roots had hdb
    exact ⟨e1 + e2, by omega⟩

end BudanFourier
