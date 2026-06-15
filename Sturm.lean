/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

/-
# Sturm's theorem (real-root counting via the signed remainder sequence)

Reverse-engine target (2026-06-15): confirmed ABSENT from Mathlib (Lean 4 has `signVariations`
of coefficients / Descartes' rule of signs, but NOT the Sturm sequence nor Sturm's theorem).
Already formalized in Coq (Cohen), Isabelle/HOL (Li–Paulson, Sturm–Tarski) and HOL Light, so this
is **first in Lean**, not first in any ITP. Genuine Mathlib gap, our exact domain (real-root
counting), PR-able.

This file is **P0 of the plan**: the two missing definitions + the main statement (with `sorry`).
The real work (P1–P5: chain algebra, local constancy, root crossing, assembly) lands incrementally.

## Definitions
* `Sturm.sturmSeq p` — the signed remainder sequence `p, p', -(p % p'), …` of `p : ℝ[X]`.
* `Sturm.signVarAt L x` — number of sign changes in the list `L` **evaluated** at `x` (zeros
  dropped), the eval-analogue of `Polynomial.signVariations` (which is on coefficients).

## Main statement
* `Sturm.sturm` — for squarefree `p` and `a < b` neither a root of `p`,
  `signVarAt (sturmSeq p) a - signVarAt (sturmSeq p) b` equals the number of DISTINCT real roots
  of `p` in `(a, b]`.

## Reference route
Wikipedia "Sturm's theorem"; Cohen (Coq); Li & Paulson, Sturm–Tarski (Isabelle, Cauchy index);
Li, Budan–Fourier in Isabelle/HOL (arXiv:1811.11093); "Sturm's theorem with endpoints"
(arXiv:2208.07904).
-/
public import RealStable
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Data.List.Destutter
public import Mathlib.Data.Sign.Basic

open Polynomial

namespace Sturm

/-- The signed remainder chain starting from `(p, q)`: `p :: q :: -(p % q) :: …`, stopping when a
remainder hits `0`. Terminates because `(p % q).degree < q.degree`. -/
public noncomputable def sturmAux (p q : Polynomial ℝ) : List (Polynomial ℝ) :=
  haveI : Decidable (q = 0) := Classical.propDecidable _
  if hq : q = 0 then [p] else p :: sturmAux q (-(p % q))
termination_by q.degree
decreasing_by
  · rw [degree_neg]; exact degree_mod_lt p hq

/-- **Sturm sequence** of `p`: the signed remainder sequence of `p` and its derivative. -/
public noncomputable def sturmSeq (p : Polynomial ℝ) : List (Polynomial ℝ) :=
  sturmAux p (derivative p)

/-- Sign variations of a list of polynomials **evaluated** at `x`: count sign changes in
`L.map (eval x)`, ignoring zeros. Eval-analogue of `Polynomial.signVariations`. -/
public noncomputable def signVarAt (L : List (Polynomial ℝ)) (x : ℝ) : ℕ :=
  (((L.map (fun p => SignType.sign (p.eval x))).filter (· ≠ 0)).destutter (· ≠ ·)).length - 1

/-! ## P1 — chain algebra

The signed-remainder step `next = -(a % b)` obeys `a + next = b * (a / b)`. Evaluated at a root of
the middle member `b`, this forces `a(x) = -next(x)`: the predecessor and successor are antipodal
there. With consecutive members coprime (squarefree case), neither vanishes, so they have strictly
opposite signs — the engine that makes interior sign-variation changes cancel. -/

/-- **Signed-remainder step.** With `next = -(a % b)`, we have `a + next = b * (a / b)`. -/
public theorem add_neg_mod (a b : Polynomial ℝ) :
    a + (-(a % b)) = b * (a / b) := by
  linear_combination -EuclideanDomain.div_add_mod a b

/-- **Antipodal at a root of the middle member.** If `x` is a root of `b`, the predecessor `a` and
the successor `next = -(a % b)` take opposite values at `x`: `a(x) = -next(x)`. -/
public theorem eval_eq_neg_next_of_root {a b : Polynomial ℝ} {x : ℝ} (hx : b.IsRoot x) :
    a.eval x = -((-(a % b)).eval x) := by
  have h := congrArg (eval x) (add_neg_mod a b)
  simp only [eval_add, eval_mul] at h
  rw [IsRoot.def] at hx
  rw [hx, zero_mul] at h
  linarith

/-- **Coprimality is preserved by the signed-remainder step.** If `a, b` are coprime then so are
`b` and the successor `next = -(a % b)`. (Same ideal: `(a, b) = (b, a % b)`.) -/
public theorem isCoprime_step {a b : Polynomial ℝ} (h : IsCoprime a b) :
    IsCoprime b (-(a % b)) := by
  have key : a = a / b * b + a % b := by
    linear_combination -EuclideanDomain.div_add_mod a b
  have : IsCoprime b (a % b) := by
    have hb : IsCoprime b a := h.symm
    rw [key] at hb
    exact hb.of_mul_add_right_right
  exact this.neg_right

/-- **Squarefree ⟹ coprime to its derivative** (over `ℝ`, a perfect field). The whole Sturm chain
inherits its gcd from `gcd p p'`, which is a unit precisely when `p` is squarefree. -/
public theorem isCoprime_self_derivative {p : Polynomial ℝ} (hp : Squarefree p) :
    IsCoprime p (derivative p) :=
  (separable_def p).mp (PerfectField.separable_iff_squarefree.mpr hp)

/-- **Coprime polynomials share no real root** (Bézout: `u·a + v·b = 1` evaluated at a common root
gives `0 = 1`). -/
public theorem not_common_root {a b : Polynomial ℝ} (h : IsCoprime a b) {x : ℝ}
    (ha : a.IsRoot x) (hb : b.IsRoot x) : False := by
  obtain ⟨u, v, huv⟩ := h
  have hev := congrArg (eval x) huv
  simp only [eval_add, eval_mul, eval_one] at hev
  rw [IsRoot.def] at ha hb
  rw [ha, hb, mul_zero, mul_zero, add_zero] at hev
  exact zero_ne_one hev

/-! ## P2 — local constancy

On an interval where a polynomial has no root its evaluation keeps a constant sign (IVT: an opposite
sign at the endpoints would force a root in between). Hence on an interval free of roots of EVERY
chain member, the whole sign pattern — and therefore `signVarAt` — is constant. -/

/-- **Constant sign on a root-free interval.** If `q` has no root in `[a, b]`, then `q` takes the
same sign at `a` and `b`. -/
public theorem sign_eval_eq_of_no_root {q : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ x ∈ Set.Icc a b, q.eval x ≠ 0) :
    SignType.sign (q.eval a) = SignType.sign (q.eval b) := by
  have hcont : ContinuousOn (fun x => q.eval x) (Set.Icc a b) :=
    (Polynomial.continuous q).continuousOn
  have ha0 : q.eval a ≠ 0 := hne a (Set.left_mem_Icc.mpr hab)
  have hb0 : q.eval b ≠ 0 := hne b (Set.right_mem_Icc.mpr hab)
  rcases lt_or_gt_of_ne ha0 with ha | ha <;> rcases lt_or_gt_of_ne hb0 with hb | hb
  · rw [sign_neg ha, sign_neg hb]
  · -- q.eval a < 0 < q.eval b: IVT gives a root, contradiction
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hab hcont ⟨ha.le, hb.le⟩
    exact absurd hc0 (hne c hc)
  · -- q.eval b < 0 < q.eval a: IVT (decreasing) gives a root, contradiction
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hab hcont ⟨hb.le, ha.le⟩
    exact absurd hc0 (hne c hc)
  · rw [sign_pos ha, sign_pos hb]

/-- **`signVarAt` is constant on a root-free interval.** If no member of `L` has a root in `[a, b]`,
the sign variations of `L` agree at `a` and `b`. -/
public theorem signVarAt_eq_of_no_root {L : List (Polynomial ℝ)} {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ q ∈ L, ∀ x ∈ Set.Icc a b, q.eval x ≠ 0) :
    signVarAt L a = signVarAt L b := by
  have hmap : L.map (fun q => SignType.sign (q.eval a))
            = L.map (fun q => SignType.sign (q.eval b)) :=
    List.map_congr_left fun q hq => sign_eval_eq_of_no_root hab (hne q hq)
  unfold signVarAt
  rw [hmap]

/-! ## P3 — behaviour at a root of `p` (analytic core)

At a simple root `α` of `p` (so `p'(α) ≠ 0`), write `p = (X - α)·g`; then `g(α) = p'(α) ≠ 0`, and
near `α`, `sign(p(x)) = sign(x - α)·sign(p'(α))`: `p` flips sign, with orientation fixed by `p'`.
This is the analytic engine behind "the leading pair `(p, p')` loses exactly one sign variation as
`x` crosses `α`". The remaining combinatorial accounting (full V-drop over the list) is P3'/P5. -/

/-- At a root `α` of `p`, the cofactor `p /ₘ (X - α)` evaluates to `p'(α)`. -/
public theorem eval_divByMonic_eq_derivative_at_root {p : Polynomial ℝ} {α : ℝ}
    (hp0 : p.eval α = 0) :
    (p /ₘ (X - C α)).eval α = (derivative p).eval α := by
  set g := p /ₘ (X - C α) with hg
  have hfac : (X - C α) * g = p := mul_divByMonic_eq_iff_isRoot.2 hp0
  have hd : derivative p = g + (X - C α) * derivative g := by
    rw [← hfac, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  rw [hd]
  simp [eval_add, eval_mul, eval_sub, eval_X, eval_C]

/-- **Sign flip at a simple root.** Near a simple root `α` of `p`,
`sign(p(x)) = sign(x - α) · sign(p'(α))`. -/
public theorem eventually_sign_eval_simple_root {p : Polynomial ℝ} {α : ℝ}
    (hp0 : p.eval α = 0) (hp' : (derivative p).eval α ≠ 0) :
    ∀ᶠ x in nhds α, SignType.sign (p.eval x)
      = SignType.sign (x - α) * SignType.sign ((derivative p).eval α) := by
  set g := p /ₘ (X - C α) with hg
  have hfac : (X - C α) * g = p := mul_divByMonic_eq_iff_isRoot.2 hp0
  have hgα : g.eval α = (derivative p).eval α := eval_divByMonic_eq_derivative_at_root hp0
  have hgα0 : g.eval α ≠ 0 := by rw [hgα]; exact hp'
  have hgcont : ContinuousAt (fun x => g.eval x) α := (Polynomial.continuous g).continuousAt
  have hsign_g : ∀ᶠ x in nhds α, SignType.sign (g.eval x) = SignType.sign (g.eval α) := by
    rcases lt_or_gt_of_ne hgα0 with hneg | hpos
    · filter_upwards [hgcont.eventually_lt continuousAt_const hneg] with x hx
      rw [sign_neg hx, sign_neg hneg]
    · filter_upwards [continuousAt_const.eventually_lt hgcont hpos] with x hx
      rw [sign_pos hx, sign_pos hpos]
  filter_upwards [hsign_g] with x hx
  have hpx : p.eval x = (x - α) * g.eval x := by
    rw [← hfac]; simp [eval_mul, eval_sub, eval_X, eval_C]
  rw [hpx, sign_mul, hx, hgα]

/-! ## P3' — sign-variation combinatorics (toward the V-drop)

Factor `signVarAt` through a pure `signChanges : List SignType → ℕ` and prove the bookkeeping
facts the V-drop needs: zeros are invisible, and a three-term window with opposite nonzero ends
always shows exactly one variation regardless of its middle (the interior-root cancellation from
P1's antipodal property, in combinatorial form). -/

/-- Sign changes in a raw list of signs: drop the zeros, then count adjacent differences. -/
public def signChanges (s : List SignType) : ℕ :=
  ((s.filter (· ≠ 0)).destutter (· ≠ ·)).length - 1

/-- `signVarAt` is `signChanges` of the evaluated sign pattern. -/
public theorem signVarAt_eq_signChanges (L : List (Polynomial ℝ)) (x : ℝ) :
    signVarAt L x = signChanges (L.map fun p => SignType.sign (p.eval x)) := by
  unfold signVarAt signChanges
  rfl

/-- A leading zero is invisible to `signChanges`. -/
@[simp] public theorem signChanges_cons_zero (s : List SignType) :
    signChanges (0 :: s) = signChanges s := by
  unfold signChanges
  rw [List.filter_cons_of_neg (by decide)]

/-- **Interior cancellation, combinatorial form.** A three-term window whose ends are nonzero and
opposite shows exactly one sign change, whatever its middle term is. -/
public theorem signChanges_triple {a m b : SignType} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    signChanges [a, m, b] = 1 := by
  revert ha hb hab
  rcases a with _ | _ <;> rcases m with _ | _ <;> rcases b with _ | _ <;> decide

/-- If every entry of `s` is a zero, prepending anything gives no variations. -/
public theorem signChanges_cons_of_filter_nil {c : SignType} {s : List SignType}
    (hs : s.filter (· ≠ 0) = []) : signChanges (c :: s) = 0 := by
  unfold signChanges
  rcases eq_or_ne c 0 with hc | hc
  · rw [List.filter_cons_of_neg (by simp [hc]), hs]; simp
  · rw [List.filter_cons_of_pos (by simpa using hc), hs]; simp

/-- **Head recursion.** Prepending a nonzero sign `c` adds exactly one variation when `c` differs
from the first surviving (nonzero) sign `d` of `s`, and none when it agrees. This is the leading-pair
flip in combinatorial form. -/
public theorem signChanges_cons_of_ne_zero {c d : SignType} (hc : c ≠ 0) {s : List SignType}
    (hd : (s.filter (· ≠ 0)).head? = some d) :
    signChanges (c :: s) = signChanges s + (if c = d then 0 else 1) := by
  unfold signChanges
  rw [List.filter_cons_of_pos (by simpa using hc)]
  rcases hfilt : s.filter (· ≠ 0) with _ | ⟨a, f'⟩
  · rw [hfilt] at hd; simp at hd
  · rw [hfilt] at hd ⊢
    rw [List.head?_cons, Option.some.injEq] at hd
    rw [← hd, List.destutter_cons', List.destutter_cons']
    by_cases hcd : c = a
    · subst hcd
      rw [List.destutter'_cons_neg (h := by simp), if_pos rfl, Nat.add_zero]
    · rw [List.destutter'_cons_pos (h := hcd), List.length_cons, if_neg hcd]
      have h1 : (List.destutter' (· ≠ ·) a f').length ≠ 0 := by
        rw [Ne, List.length_eq_zero_iff]
        exact List.destutter'_ne_nil f' (· ≠ ·)
      omega

/-- The first surviving sign of `c :: t` is `c` when `c ≠ 0`. -/
public theorem filter_ne_zero_head?_cons {c : SignType} (hc : c ≠ 0) (t : List SignType) :
    ((c :: t).filter (· ≠ 0)).head? = some c := by
  rw [List.filter_cons_of_pos (by simpa using hc)]; rfl

/-- **Leading-pair drop.** If the head `c` flips relative to the first surviving sign `c'` of the
tail (`c ≠ c'`, both nonzero), the count is one more than with head `c'`. With `c = sign p(α⁻)` and
`c' = sign p'(α) = sign p(α⁺)`, this is the exact `-1` of the `(p, p')` pair across a root. -/
public theorem signChanges_head_drop {c c' : SignType} (hc : c ≠ 0) (hc' : c' ≠ 0) (hne : c ≠ c')
    {t : List SignType} (hd : (t.filter (· ≠ 0)).head? = some c') :
    signChanges (c :: t) = signChanges (c' :: t) + 1 := by
  rw [signChanges_cons_of_ne_zero hc hd, signChanges_cons_of_ne_zero hc' hd, if_neg hne, if_pos rfl]

/-- **Interior cancellation.** Deleting a middle entry that sits between two nonzero opposite signs
leaves the count unchanged — whatever the deleted sign is. This is why an interior chain member,
whose sign may change across `α`, does not move `V` (its neighbours are fixed and opposite). -/
public theorem signChanges_remove_middle {a b m : SignType} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    {rest : List SignType} :
    signChanges (a :: m :: b :: rest) = signChanges (a :: b :: rest) := by
  have hbhd : ((b :: rest).filter (· ≠ 0)).head? = some b := filter_ne_zero_head?_cons hb rest
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    have h0 : ((0 :: b :: rest).filter (· ≠ 0)).head? = some b := by
      rw [List.filter_cons_of_neg (by simp)]; exact hbhd
    rw [signChanges_cons_of_ne_zero ha h0, signChanges_cons_zero,
        signChanges_cons_of_ne_zero ha hbhd]
  · have hmhd : ((m :: b :: rest).filter (· ≠ 0)).head? = some m :=
      filter_ne_zero_head?_cons hm (b :: rest)
    rw [signChanges_cons_of_ne_zero ha hmhd, signChanges_cons_of_ne_zero hm hbhd,
        signChanges_cons_of_ne_zero ha hbhd]
    rcases a with _ | _ <;> rcases m with _ | _ <;> rcases b with _ | _ <;> simp_all

/-! ## P5 — structural facts about the Sturm sequence (toward assembly) -/

/-- The chain stops at a zero divisor: `sturmAux p 0 = [p]`. -/
@[simp] public theorem sturmAux_zero (p : Polynomial ℝ) : sturmAux p 0 = [p] := by
  rw [sturmAux]; simp

/-- One unfolding step of the chain when the divisor is nonzero. -/
public theorem sturmAux_cons {p q : Polynomial ℝ} (hq : q ≠ 0) :
    sturmAux p q = p :: sturmAux q (-(p % q)) := by
  rw [sturmAux]; rw [dif_neg hq]

/-- The Sturm sequence starts with `p`. -/
public theorem sturmSeq_head? (p : Polynomial ℝ) : (sturmSeq p).head? = some p := by
  unfold sturmSeq
  rcases eq_or_ne (derivative p) 0 with h | h
  · rw [h, sturmAux_zero]; rfl
  · rw [sturmAux_cons h]; rfl

/-- **Sturm's theorem.** For squarefree `p` and `a < b` with neither endpoint a root of `p`, the
drop in sign variations of the Sturm sequence equals the number of distinct real roots in `(a, b]`.
-/
public theorem sturm (p : Polynomial ℝ) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    signVarAt (sturmSeq p) a - signVarAt (sturmSeq p) b =
      (p.roots.toFinset.filter (fun x => a < x ∧ x ≤ b)).card := by
  sorry

end Sturm
