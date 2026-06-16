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

The full theorem is proven sorry-free (3 standard axioms): chain algebra, local constancy, root
crossing, the chain-walk flank-reduction, the single-critical-point quantum, and the global
critical-set induction. First Sturm's theorem in Lean.

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
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.RuleOfSigns
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
@[expose] public noncomputable def signVarAt (L : List (Polynomial ℝ)) (x : ℝ) : ℕ :=
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

/-- Every chain `sturmAux p q` starts with `p`. -/
public theorem sturmAux_head? (p q : Polynomial ℝ) : (sturmAux p q).head? = some p := by
  rcases eq_or_ne q 0 with h | h
  · rw [h, sturmAux_zero]; rfl
  · rw [sturmAux_cons h]; rfl

/-- The Sturm sequence starts with `p`. -/
public theorem sturmSeq_head? (p : Polynomial ℝ) : (sturmSeq p).head? = some p :=
  sturmAux_head? _ _

/-- Every member of a Sturm chain is nonzero, provided the dividend is. -/
public theorem sturmAux_mem_ne_zero : ∀ (p q : Polynomial ℝ), p ≠ 0 → ∀ r ∈ sturmAux p q, r ≠ 0 := by
  intro p q
  induction p, q using sturmAux.induct with
  | case1 p =>
    intro hp r hr
    rw [sturmAux_zero, List.mem_singleton] at hr
    subst hr; exact hp
  | case2 p q hq ih =>
    intro hp r hr
    rw [sturmAux_cons hq, List.mem_cons] at hr
    rcases hr with h | h
    · subst h; exact hp
    · exact ih hq r h

/-- The product of all Sturm-sequence members is nonzero (each member is nonzero in the domain
`ℝ[X]`). Its roots are exactly the critical points; this makes the critical set finite. -/
public theorem sturmSeq_prod_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) :
    (sturmSeq p).prod ≠ 0 := by
  rw [Ne, List.prod_eq_zero_iff]
  intro h0
  unfold sturmSeq at h0
  exact sturmAux_mem_ne_zero p (derivative p) hp 0 h0 rfl

/-- **Consecutive members of a signed-remainder chain are coprime** (with a coprime seed). Each step
preserves coprimality (`isCoprime_step`), so every adjacent pair `[x, m]` appearing in the chain is
coprime — the source of `hiso` (no two adjacent members vanish at a common point). -/
public theorem sturmAux_consecutive_coprime :
    ∀ (p q : Polynomial ℝ), IsCoprime p q →
      ∀ x m, [x, m] <:+: sturmAux p q → IsCoprime x m := by
  intro p q
  induction p, q using sturmAux.induct with
  | case1 p =>
    intro _ x m hinf
    rw [sturmAux_zero, List.infix_singleton_iff] at hinf
    rcases hinf with h | h <;> simp at h
  | case2 p q hq ih =>
    intro hcop x m hinf
    rw [sturmAux_cons hq] at hinf
    rcases List.infix_cons_iff.mp hinf with hpre | hsuf
    · obtain ⟨hx, hpre2⟩ := List.cons_prefix_cons.mp hpre
      obtain ⟨t, ht⟩ := hpre2
      have hhead : (sturmAux q (-(p % q))).head? = some m := by rw [← ht]; rfl
      have h2 := sturmAux_head? q (-(p % q))
      rw [hhead, Option.some_inj] at h2
      rw [hx, h2]; exact hcop
    · exact ih (isCoprime_step hcop) x m hsuf

/-- **The successor of a chain triple is the signed remainder.** For any three consecutive members
`[x, m, y]` of a signed-remainder chain, `y = -(x % m)` — the chain's defining relation, surfaced as
a fact about adjacent triples. Together with `eval_eq_neg_next_of_root` this gives the antipodal
flank behaviour at an interior root (the source of `hflank`). -/
public theorem sturmAux_consecutive_succ :
    ∀ (p q : Polynomial ℝ), ∀ x m y, [x, m, y] <:+: sturmAux p q → y = -(x % m) := by
  intro p q
  induction p, q using sturmAux.induct with
  | case1 p =>
    intro x m y hinf
    rw [sturmAux_zero, List.infix_singleton_iff] at hinf
    rcases hinf with h | h <;> simp at h
  | case2 p q hq ih =>
    intro x m y hinf
    rw [sturmAux_cons hq] at hinf
    rcases List.infix_cons_iff.mp hinf with hpre | hsuf
    · obtain ⟨hx, hpre2⟩ := List.cons_prefix_cons.mp hpre
      by_cases hq2 : (-(p % q)) = 0
      · rw [hq2, sturmAux_zero] at hpre2
        obtain ⟨_, hpre3⟩ := List.cons_prefix_cons.mp hpre2
        simp at hpre3
      · rw [sturmAux_cons hq2] at hpre2
        obtain ⟨hm, hpre3⟩ := List.cons_prefix_cons.mp hpre2
        obtain ⟨t, ht⟩ := hpre3
        have hhead : (sturmAux (-(p % q)) (-(q % -(p % q)))).head? = some y := by rw [← ht]; rfl
        have h2 := sturmAux_head? (-(p % q)) (-(q % -(p % q)))
        rw [hhead, Option.some_inj] at h2
        rw [hx, hm]; exact h2
    · exact ih x m y hsuf

/-- **The last member of a coprime-seeded chain is a unit.** The chain ends at the last nonzero
remainder — the gcd — which for a coprime seed is a unit (`IsCoprime p 0 ↔ IsUnit p` at the base).
Hence the final Sturm member is a nonzero constant, never vanishing (the source of `hlast`). -/
public theorem sturmAux_getLast_isUnit :
    ∀ (p q : Polynomial ℝ), IsCoprime p q → ∀ g, (sturmAux p q).getLast? = some g → IsUnit g := by
  intro p q
  induction p, q using sturmAux.induct with
  | case1 p =>
    intro hcop g hg
    rw [sturmAux_zero] at hg
    rw [List.getLast?_singleton, Option.some_inj] at hg
    rw [← hg]
    exact isCoprime_zero_right.mp hcop
  | case2 p q hq ih =>
    intro hcop g hg
    rw [sturmAux_cons hq] at hg
    obtain ⟨L', hL'⟩ : ∃ L', sturmAux q (-(p % q)) = q :: L' := by
      have hh := sturmAux_head? q (-(p % q))
      rcases h : sturmAux q (-(p % q)) with _ | ⟨c, r⟩
      · rw [h] at hh; simp at hh
      · rw [h, List.head?_cons, Option.some_inj] at hh; exact ⟨r, by rw [hh]⟩
    rw [hL', List.getLast?_cons_cons, ← hL'] at hg
    exact ih (isCoprime_step hcop) g hg

/-- **Root-crossing bridge.** If, between two points `x` and `y`, only the head polynomial `p`
changes sign (the rest of the list keeps its signs), `p` is nonzero at both, and the head sign at
`y` equals the first surviving sign of the tail, then `V` is exactly one larger at `x`. This lifts
the combinatorial `signChanges_head_drop` to the evaluated sign lists — the `-1` of `V` across a
simple root of `p`, in generic position. -/
public theorem signVarAt_cons_head_drop {p : Polynomial ℝ} {tail : List (Polynomial ℝ)} {x y : ℝ}
    (hpx0 : p.eval x ≠ 0) (hpy0 : p.eval y ≠ 0)
    (hne : SignType.sign (p.eval x) ≠ SignType.sign (p.eval y))
    (htail : tail.map (fun q => SignType.sign (q.eval x))
           = tail.map (fun q => SignType.sign (q.eval y)))
    (hfirst : ((tail.map (fun q => SignType.sign (q.eval y))).filter (· ≠ 0)).head?
                = some (SignType.sign (p.eval y))) :
    signVarAt (p :: tail) x = signVarAt (p :: tail) y + 1 := by
  simp only [signVarAt_eq_signChanges, List.map_cons]
  rw [htail]
  exact signChanges_head_drop
    (by rw [Ne, sign_eq_zero_iff]; exact hpx0)
    (by rw [Ne, sign_eq_zero_iff]; exact hpy0) hne hfirst

/-- Tail signs are unchanged on a root-free interval (the `htail` provider for the keystone). -/
public theorem map_sign_eq_of_no_root {L : List (Polynomial ℝ)} {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ q ∈ L, ∀ z ∈ Set.Icc a b, q.eval z ≠ 0) :
    L.map (fun q => SignType.sign (q.eval a)) = L.map (fun q => SignType.sign (q.eval b)) :=
  List.map_congr_left fun q hq => sign_eval_eq_of_no_root hab (hne q hq)

/-- The first surviving tail sign is the sign of the first (nonzero-valued) member (the `hfirst`
provider for the keystone). -/
public theorem filter_map_sign_head?_cons {q : Polynomial ℝ} {rest : List (Polynomial ℝ)} {y : ℝ}
    (hq : q.eval y ≠ 0) :
    (((q :: rest).map (fun r => SignType.sign (r.eval y))).filter (· ≠ 0)).head?
      = some (SignType.sign (q.eval y)) := by
  rw [List.map_cons, List.filter_cons_of_pos (by simp [sign_eq_zero_iff, hq])]; rfl

/-! ## Interior cancellation at arbitrary position (monolith engine) -/

/-- The first surviving sign of `pre ++ a :: X` does not depend on `X` (the inserted/changed entry
sits after the nonzero `a`, never becoming the first nonzero). -/
public theorem filter_append_cons_head?_eq {a : SignType} (ha : a ≠ 0) (pre X Y : List SignType) :
    ((pre ++ a :: X).filter (· ≠ 0)).head? = ((pre ++ a :: Y).filter (· ≠ 0)).head? := by
  rw [List.filter_append, List.filter_append,
      List.filter_cons_of_pos (by simpa using ha), List.filter_cons_of_pos (by simpa using ha)]
  rcases pre.filter (· ≠ 0) with _ | ⟨h, t⟩ <;> simp

/-- **Interior cancellation, any position.** Deleting a middle entry between two nonzero opposite
signs leaves the count unchanged, anywhere in the list (induction on the prefix). -/
public theorem signChanges_remove_middle_append {a b m : SignType}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (pre rest : List SignType) :
    signChanges (pre ++ a :: m :: b :: rest) = signChanges (pre ++ a :: b :: rest) := by
  induction pre with
  | nil => exact signChanges_remove_middle ha hb hab
  | cons c pre' ih =>
    rcases eq_or_ne c 0 with hc | hc
    · subst hc
      simp only [List.cons_append, signChanges_cons_zero]; exact ih
    · obtain ⟨d, hd⟩ : ∃ d, ((pre' ++ a :: m :: b :: rest).filter (· ≠ 0)).head? = some d := by
        rcases hq : ((pre' ++ a :: m :: b :: rest).filter (· ≠ 0)).head? with _ | d
        · exfalso
          have hmem : a ∈ (pre' ++ a :: m :: b :: rest).filter (· ≠ 0) :=
            List.mem_filter.mpr ⟨List.mem_append_right _ (List.mem_cons_self ..), by simpa using ha⟩
          rw [List.head?_eq_none_iff.mp hq] at hmem; simp at hmem
        · exact ⟨d, hq⟩
      have hd2 : ((pre' ++ a :: b :: rest).filter (· ≠ 0)).head? = some d := by
        rw [← filter_append_cons_head?_eq ha pre' (m :: b :: rest) (b :: rest)]; exact hd
      simp only [List.cons_append]
      rw [signChanges_cons_of_ne_zero hc hd, signChanges_cons_of_ne_zero hc hd2, ih]

/-! ## Interior-member crossing (piece ii): neighbours are nonzero and opposite -/

/-- **At a root of an interior chain member, its neighbours are nonzero and opposite.** If `a` and
`m` are coprime (consecutive Sturm members) and `m(c) = 0`, then `a(c)` and the successor
`(-(a % m))(c)` are both nonzero and carry opposite signs — exactly the configuration that makes
`signChanges_remove_middle` fire, so the interior root contributes `0` to the variation change. -/
public theorem sign_neighbours_opposite_at_interior_root {a m : Polynomial ℝ} {c : ℝ}
    (hco : IsCoprime a m) (hm : m.eval c = 0) :
    SignType.sign (a.eval c) ≠ 0 ∧
      SignType.sign (a.eval c) ≠ SignType.sign ((-(a % m)).eval c) := by
  have ha : a.eval c ≠ 0 := fun h => not_common_root hco h hm
  have hanti : a.eval c = -((-(a % m)).eval c) := eval_eq_neg_next_of_root hm
  have hNval : (-(a % m)).eval c = -(a.eval c) := by linarith [hanti]
  have hsa : SignType.sign (a.eval c) ≠ 0 := by rw [Ne, sign_eq_zero_iff]; exact ha
  refine ⟨hsa, ?_⟩
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hNpos : 0 < (-(a % m)).eval c := by rw [hNval]; linarith
    rw [sign_neg hneg, sign_pos hNpos]; decide
  · have hNneg : (-(a % m)).eval c < 0 := by rw [hNval]; linarith
    rw [sign_pos hpos, sign_neg hNneg]; decide

/-- **Surgery atom.** At a point `z` where the two flanking polynomials `pa`, `pb` take nonzero
opposite signs, the middle polynomial `pm` can be deleted from the list without changing `signVarAt`
— anywhere in the list. This is `signChanges_remove_middle_append` lifted to evaluated polynomial
lists; iterating it deletes every interior member that vanishes at a critical point. -/
public theorem signVarAt_remove_middle (pre rest : List (Polynomial ℝ)) (pa pm pb : Polynomial ℝ)
    {z : ℝ} (ha : SignType.sign (pa.eval z) ≠ 0) (hb : SignType.sign (pb.eval z) ≠ 0)
    (hab : SignType.sign (pa.eval z) ≠ SignType.sign (pb.eval z)) :
    signVarAt (pre ++ pa :: pm :: pb :: rest) z = signVarAt (pre ++ pa :: pb :: rest) z := by
  simp only [signVarAt_eq_signChanges, List.map_append, List.map_cons]
  exact signChanges_remove_middle_append ha hb hab _ _

/-- **Middle irrelevance.** Between two nonzero opposite signs, the middle entry's value does not
affect the count: changing it from `m` to `m'` is invisible (both reduce to the same list with the
middle deleted). This is the two-point form of interior cancellation — across a critical point an
interior member changes sign, but its fixed opposite neighbours absorb the change. -/
public theorem signChanges_middle_irrelevant {a b m m' : SignType}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (pre rest : List SignType) :
    signChanges (pre ++ a :: m :: b :: rest) = signChanges (pre ++ a :: m' :: b :: rest) := by
  rw [signChanges_remove_middle_append ha hb hab, signChanges_remove_middle_append ha hb hab]

/-- Middle irrelevance at the polynomial level (one interior member, at one point). -/
public theorem signVarAt_middle_irrelevant (pre rest : List (Polynomial ℝ)) (pa pm pm' pb : Polynomial ℝ)
    {z : ℝ} (ha : SignType.sign (pa.eval z) ≠ 0) (hb : SignType.sign (pb.eval z) ≠ 0)
    (hab : SignType.sign (pa.eval z) ≠ SignType.sign (pb.eval z)) :
    signVarAt (pre ++ pa :: pm :: pb :: rest) z = signVarAt (pre ++ pa :: pm' :: pb :: rest) z := by
  rw [signVarAt_remove_middle pre rest pa pm pb ha hb hab,
      signVarAt_remove_middle pre rest pa pm' pb ha hb hab]

/-! ## The crux: flank-reduction (the decoupled two-point comparison engine)

From the Socratic analysis of a critical point: deleting interior chain members that vanish there
(each flanked by nonzero opposite neighbours) preserves the sign-variation count. Encode "delete
flanked middles" as an inductive relation; it preserves `signChanges`. The Sturm chain then only has
to exhibit the reductions — the combinatorics is decoupled. -/

/-- `xs` reduces to `ys` by deleting middle entries flanked by nonzero opposite signs. -/
public inductive FlankReduce : List SignType → List SignType → Prop where
  | refl (l : List SignType) : FlankReduce l l
  | del (pre : List SignType) (a m b : SignType) (rest : List SignType)
      (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) {ys : List SignType} :
      FlankReduce (pre ++ a :: b :: rest) ys →
      FlankReduce (pre ++ a :: m :: b :: rest) ys

/-- **Flank-reduction preserves the count.** Each deletion is `signChanges_remove_middle_append`. -/
public theorem FlankReduce.signChanges_eq {xs ys : List SignType} (h : FlankReduce xs ys) :
    signChanges xs = signChanges ys := by
  induction h with
  | refl => rfl
  | del pre a m b rest ha hb hab _ ih =>
      rw [signChanges_remove_middle_append ha hb hab]; exact ih

/-- **Lift to evaluated polynomial lists.** If the sign patterns of two polynomial lists at `z` are
flank-related, their sign variations at `z` agree. This is where the decoupling pays off: the Sturm
chain only has to exhibit a `FlankReduce` between the `c⁻` and `c⁺` sign patterns. -/
public theorem signVarAt_eq_of_flankReduce {L₁ L₂ : List (Polynomial ℝ)} {z : ℝ}
    (h : FlankReduce (L₁.map fun q => SignType.sign (q.eval z))
                     (L₂.map fun q => SignType.sign (q.eval z))) :
    signVarAt L₁ z = signVarAt L₂ z := by
  rw [signVarAt_eq_signChanges, signVarAt_eq_signChanges]; exact h.signChanges_eq

/-- **Chain-level reduction step.** If at `z` the flanking polynomials `pa`, `pb` carry nonzero
opposite signs, a `FlankReduce` of the list with the middle `pm` deleted extends to one of the full
list. Iterating this (one per interior vanisher) exhibits the reduction of the chain's sign pattern.
The flank hypotheses come from `sign_neighbours_opposite_at_interior_root` (chain structure). -/
public theorem flankReduce_eval_step (pre rest : List (Polynomial ℝ)) (pa pm pb : Polynomial ℝ)
    {z : ℝ} (ha : SignType.sign (pa.eval z) ≠ 0) (hb : SignType.sign (pb.eval z) ≠ 0)
    (hab : SignType.sign (pa.eval z) ≠ SignType.sign (pb.eval z))
    {ys : List SignType}
    (hrest : FlankReduce ((pre ++ pa :: pb :: rest).map fun q => SignType.sign (q.eval z)) ys) :
    FlankReduce ((pre ++ pa :: pm :: pb :: rest).map fun q => SignType.sign (q.eval z)) ys := by
  simp only [List.map_append, List.map_cons] at hrest ⊢
  exact FlankReduce.del _ _ _ _ _ ha hb hab hrest

/-- **`FlankReduce` is closed under consing.** Prepending the same head to both sides preserves the
relation (every deletion's prefix just grows by one). Lets the chain-walk keep a fixed head while
reducing the tail. -/
public theorem FlankReduce.cons (s : SignType) {xs ys : List SignType} (h : FlankReduce xs ys) :
    FlankReduce (s :: xs) (s :: ys) := by
  induction h with
  | refl l => exact .refl _
  | del pre a m b rest ha hb hab _ ih =>
      have hstep := FlankReduce.del (s :: pre) a m b rest ha hb hab
        (by rw [List.cons_append]; exact ih)
      rw [List.cons_append] at hstep
      exact hstep

section ChainWalk
attribute [local instance] Classical.propDecidable

/-- **Chain-walk reduction (the decoupled wall).** Walking a polynomial chain `a :: tail`, every
*interior* member that vanishes at `c` — flanked (`hflank`) by neighbours of nonzero opposite sign
at the evaluation point `z` — is deleted: the sign pattern at `z` `FlankReduce`s to that of the chain
with those interior vanishers removed (the head is always kept). `hiso` records that no two
consecutive members both vanish at `c` (Sturm chains satisfy this by consecutive coprimality);
`hlast` records that the final member does not vanish at `c` (Sturm's last member is a nonzero
constant). With these, the chain's `c⁻`/`c⁺` sign patterns both reduce to the *same* kept chain. -/
public theorem flankReduce_chain_walk {c z : ℝ} :
    ∀ (a : Polynomial ℝ) (tail : List (Polynomial ℝ)),
    (∀ x m y, [x, m, y] <:+: (a :: tail) → m.eval c = 0 →
        SignType.sign (x.eval z) ≠ 0 ∧ SignType.sign (y.eval z) ≠ 0 ∧
        SignType.sign (x.eval z) ≠ SignType.sign (y.eval z)) →
    (∀ x y, [x, y] <:+: (a :: tail) → ¬ (x.eval c = 0 ∧ y.eval c = 0)) →
    (∀ q, (a :: tail).getLast? = some q → q.eval c ≠ 0) →
    FlankReduce ((a :: tail).map (fun q => SignType.sign (q.eval z)))
      ((a :: tail.filter (fun q => decide (q.eval c ≠ 0))).map
        (fun q => SignType.sign (q.eval z))) := by
  intro a tail
  induction tail generalizing a with
  | nil => intro _ _ _; simpa using FlankReduce.refl _
  | cons m rest ih =>
    intro hflank hiso hlast
    by_cases hm : m.eval c = 0
    · -- m vanishes: an interior vanisher (`rest ≠ []` since the last member never vanishes)
      have hrest_ne : rest ≠ [] := by
        rintro rfl
        exact hlast m (by simp) hm
      obtain ⟨b, rest', rfl⟩ := List.exists_cons_of_ne_nil hrest_ne
      -- `b` is the right neighbour of the vanisher `m`; by `hiso` it does not vanish at `c`
      have hbne : b.eval c ≠ 0 := by
        intro hb0
        exact hiso m b (by exact ⟨[a], rest', rfl⟩) ⟨hm, hb0⟩
      -- flank signs at `z` from `hflank` on the triple `[a, m, b]`
      obtain ⟨ha, hb, hab⟩ := hflank a m b ⟨[], rest', rfl⟩ hm
      -- the kept list drops `m`
      have hfilter : (m :: b :: rest').filter (fun q => decide (q.eval c ≠ 0))
          = (b :: rest').filter (fun q => decide (q.eval c ≠ 0)) := by
        simp [hm]
      rw [hfilter]
      -- hypotheses transfer to the reduced chain `a :: b :: rest'`
      have hflank' : ∀ x mm y, [x, mm, y] <:+: (a :: b :: rest') → mm.eval c = 0 →
          SignType.sign (x.eval z) ≠ 0 ∧ SignType.sign (y.eval z) ≠ 0 ∧
          SignType.sign (x.eval z) ≠ SignType.sign (y.eval z) := by
        intro x mm y hinf hmm0
        rcases List.infix_cons_iff.mp hinf with hpre | hsuf
        · -- prefix: x = a, mm = b — but `b` does not vanish, contradiction
          obtain ⟨rfl, hpre2⟩ := List.cons_prefix_cons.mp hpre
          obtain ⟨rfl, _⟩ := List.cons_prefix_cons.mp hpre2
          exact absurd hmm0 hbne
        · exact hflank x mm y (List.infix_cons_iff.mpr (Or.inr (List.infix_cons_iff.mpr (Or.inr hsuf)))) hmm0
      have hiso' : ∀ x y, [x, y] <:+: (a :: b :: rest') → ¬ (x.eval c = 0 ∧ y.eval c = 0) := by
        intro x y hinf
        rcases List.infix_cons_iff.mp hinf with hpre | hsuf
        · obtain ⟨rfl, hpre2⟩ := List.cons_prefix_cons.mp hpre
          obtain ⟨rfl, _⟩ := List.cons_prefix_cons.mp hpre2
          exact fun ⟨_, hb0⟩ => hbne hb0
        · exact hiso x y (List.infix_cons_iff.mpr (Or.inr (List.infix_cons_iff.mpr (Or.inr hsuf))))
      have hlast' : ∀ q, (a :: b :: rest').getLast? = some q → q.eval c ≠ 0 := by
        intro q hq
        apply hlast q
        rw [List.getLast?_cons_cons, List.getLast?_cons_cons]
        rw [List.getLast?_cons_cons] at hq
        exact hq
      exact flankReduce_eval_step [] rest' a m b ha hb hab (ih a hflank' hiso' hlast')
    · -- m does not vanish: kept; recurse on `(m, rest)` and re-cons `a`
      have hfilter : (m :: rest).filter (fun q => decide (q.eval c ≠ 0))
          = m :: rest.filter (fun q => decide (q.eval c ≠ 0)) := by
        simp [hm]
      rw [hfilter]
      have hflank' : ∀ x mm y, [x, mm, y] <:+: (m :: rest) → mm.eval c = 0 →
          SignType.sign (x.eval z) ≠ 0 ∧ SignType.sign (y.eval z) ≠ 0 ∧
          SignType.sign (x.eval z) ≠ SignType.sign (y.eval z) :=
        fun x mm y hinf => hflank x mm y (List.infix_cons_iff.mpr (Or.inr hinf))
      have hiso' : ∀ x y, [x, y] <:+: (m :: rest) → ¬ (x.eval c = 0 ∧ y.eval c = 0) :=
        fun x y hinf => hiso x y (List.infix_cons_iff.mpr (Or.inr hinf))
      have hlast' : ∀ q, (m :: rest).getLast? = some q → q.eval c ≠ 0 := by
        intro q hq
        apply hlast q
        rw [List.getLast?_cons_cons]
        exact hq
      simpa [List.map_cons] using FlankReduce.cons (SignType.sign (a.eval z)) (ih m hflank' hiso' hlast')

end ChainWalk

/-! ## Domain-wall view: `signChanges` as a local additive sum (BPR sign-variation theory in Lean)

Following classical real-algebraic-geometry sign-variation theory (Basu–Pollack–Roy; sign-change
decomposition formalized in Coq, "Theorem of three circles") — first in Lean. On a zero-free list,
`signChanges` equals the local count of adjacent disagreements (`wallCount`), an additive sum that
makes the two-point comparison decouple. -/

/-- The local count of adjacent disagreements (`±1` domain walls; no zeros dropped). -/
public def wallCount : List SignType → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a = b then 0 else 1) + wallCount (b :: t)

/-- On a **zero-free** list, `signChanges` is the local additive `wallCount` (head recursion). -/
public theorem signChanges_eq_wallCount_of_zero_free :
    ∀ f : List SignType, (0 : SignType) ∉ f → signChanges f = wallCount f
  | [], _ => by simp [signChanges, wallCount]
  | [a], _ => by rcases eq_or_ne a 0 with h | h <;> simp [signChanges, wallCount, h]
  | a :: b :: t, hf => by
      have ha : a ≠ 0 := fun h => hf (h ▸ List.mem_cons_self ..)
      have hb : b ≠ 0 := fun h => hf (h ▸ List.mem_cons_of_mem a (List.mem_cons_self ..))
      have hbt : (0 : SignType) ∉ (b :: t) := fun h => hf (List.mem_cons_of_mem a h)
      have ih := signChanges_eq_wallCount_of_zero_free (b :: t) hbt
      rw [signChanges_cons_of_ne_zero ha (filter_ne_zero_head?_cons hb t), wallCount, ih,
        Nat.add_comm]

/-- **The additive bridge.** `signChanges s = wallCount (nonzero filtrate of s)`. -/
public theorem signChanges_eq_wallCount (s : List SignType) :
    signChanges s = wallCount (s.filter (· ≠ 0)) := by
  have h1 : signChanges s = signChanges (s.filter (· ≠ 0)) := by
    unfold signChanges; rw [List.filter_filter]; simp
  rw [h1, signChanges_eq_wallCount_of_zero_free _ (by simp [List.mem_filter])]

/-- **The ℤ/2 layer of sign variation.** For a zero-free list, `(-1)^(wallCount)` telescopes to the
product of the endpoint signs: modulo 2, sign variation forgets everything but whether the ends
disagree. This is the engine behind Descartes' even-difference refinement and the transversality
(`sign p'`) at a simple root — the single-bit shadow of the count. -/
public theorem wallCount_neg_one_pow :
    ∀ (a : SignType) (l : List SignType), (0 : SignType) ∉ a :: l →
      (-1 : SignType) ^ wallCount (a :: l) = a * (a :: l).getLast (List.cons_ne_nil a l)
  | a, [], h => by
      have ha : a ≠ 0 := fun h0 => h (h0 ▸ List.mem_cons_self ..)
      have key : (1 : SignType) = a * a :=
        (by decide : ∀ a : SignType, a ≠ 0 → (1 : SignType) = a * a) a ha
      simpa [wallCount] using key
  | a, b :: l', h => by
      have ha : a ≠ 0 := fun h0 => h (h0 ▸ List.mem_cons_self ..)
      have hb : b ≠ 0 := fun h0 => h (h0 ▸ List.mem_cons_of_mem a (List.mem_cons_self ..))
      have hbl : (0 : SignType) ∉ b :: l' := fun h0 => h (List.mem_cons_of_mem a h0)
      have ih := wallCount_neg_one_pow b l' hbl
      have key : (-1 : SignType) ^ (if a = b then 0 else 1) * b = a :=
        (by decide : ∀ a b : SignType, a ≠ 0 → b ≠ 0 →
          (-1 : SignType) ^ (if a = b then 0 else 1) * b = a) a b ha hb
      rw [wallCount, pow_add, ih, List.getLast_cons (List.cons_ne_nil b l'), ← mul_assoc, key]

/-- **Parity, clean form.** A zero-free list has an even number of sign changes iff its endpoints
agree. The `±1` shadow: parity of sign variation = "do the ends match?". -/
public theorem wallCount_even_iff_endpoints {a : SignType} {l : List SignType}
    (h : (0 : SignType) ∉ a :: l) :
    Even (wallCount (a :: l)) ↔ a = (a :: l).getLast (List.cons_ne_nil a l) := by
  have hpow := wallCount_neg_one_pow a l h
  have ha : a ≠ 0 := fun h0 => h (h0 ▸ List.mem_cons_self ..)
  have hlast : (a :: l).getLast (List.cons_ne_nil a l) ≠ 0 :=
    fun h0 => h (h0 ▸ List.getLast_mem (List.cons_ne_nil a l))
  rw [← neg_one_pow_eq_one_iff_even (by decide : (-1 : SignType) ≠ 1), hpow]
  exact (by decide : ∀ a b : SignType, a ≠ 0 → b ≠ 0 → (a * b = 1 ↔ a = b)) _ _ ha hlast

/-! ## Continuity sub-thread: signs are locally constant near a nonzero point -/

/-- **Local sign constancy.** Near a point where `q` is nonzero, `q` keeps its sign (continuity). -/
public theorem eventually_sign_eval_eq {q : Polynomial ℝ} {c : ℝ} (hc : q.eval c ≠ 0) :
    ∀ᶠ z in nhds c, SignType.sign (q.eval z) = SignType.sign (q.eval c) := by
  have hcont : ContinuousAt (fun z => q.eval z) c := (Polynomial.continuous q).continuousAt
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · filter_upwards [hcont.eventually_lt continuousAt_const hneg] with z hz
    rw [sign_neg hz, sign_neg hneg]
  · filter_upwards [continuousAt_const.eventually_lt hcont hpos] with z hz
    rw [sign_pos hz, sign_pos hpos]

/-- **Flank-opposite persists near an interior root.** At a root `c` of an interior member `m`
(coprime to its predecessor `a`), the predecessor and successor `-(a % m)` keep nonzero opposite
signs at every nearby `z` — exactly the flank hypotheses `flankReduce_eval_step` needs at `c⁻` / `c⁺`
(not just at `c`). -/
public theorem eventually_flank_opposite_at_interior_root {a m : Polynomial ℝ} {c : ℝ}
    (hco : IsCoprime a m) (hm : m.eval c = 0) :
    ∀ᶠ z in nhds c, SignType.sign (a.eval z) ≠ 0 ∧
      SignType.sign (a.eval z) ≠ SignType.sign ((-(a % m)).eval z) := by
  obtain ⟨hsa, hne⟩ := sign_neighbours_opposite_at_interior_root hco hm
  have ha : a.eval c ≠ 0 := fun h => not_common_root hco h hm
  have hN : (-(a % m)).eval c ≠ 0 := by
    have := eval_eq_neg_next_of_root (a := a) hm
    intro h; rw [h, neg_zero] at this; exact ha this
  filter_upwards [eventually_sign_eval_eq ha, eventually_sign_eval_eq hN] with z hza hzN
  rw [hza, hzN]; exact ⟨hsa, hne⟩

/-! ## Local root-crossing (closing P3 for one simple root, generic position) -/

/-- Just to the right of a simple root, `p` carries the sign of `p'(α)`. -/
public theorem sign_eval_eq_sign_deriv_right {p : Polynomial ℝ} {α b : ℝ} (hroot : p.eval α = 0)
    (hp'0 : (derivative p).eval α ≠ 0) (hαb : α < b)
    (hp_only : ∀ z ∈ Set.Icc α b, p.eval z = 0 → z = α) :
    SignType.sign (p.eval b) = SignType.sign ((derivative p).eval α) := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff.mp (eventually_sign_eval_simple_root hroot hp'0)
  set δ := min (ε / 2) ((b - α) / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  set xR := α + δ with hxR
  have hxR_gt : α < xR := by rw [hxR]; linarith
  have hxR_lt : xR < b := by
    have : δ ≤ (b - α) / 2 := min_le_right _ _
    rw [hxR]; linarith
  have hdist : dist xR α < ε := by
    have hle : δ ≤ ε / 2 := min_le_left _ _
    rw [hxR, Real.dist_eq, add_sub_cancel_left, abs_of_pos hδpos]; linarith
  have hsxR : SignType.sign (p.eval xR) = SignType.sign ((derivative p).eval α) := by
    rw [hball hdist, hxR, add_sub_cancel_left, sign_pos hδpos, one_mul]
  have hno : ∀ z ∈ Set.Icc xR b, p.eval z ≠ 0 := by
    intro z hz hz0
    have hzα : z = α := hp_only z ⟨le_trans hxR_gt.le hz.1, hz.2⟩ hz0
    rw [hzα] at hz; exact absurd hz.1 (not_le.mpr hxR_gt)
  rw [← sign_eval_eq_of_no_root hxR_lt.le hno]; exact hsxR

/-- Just to the left of a simple root, `p` carries the opposite sign of `p'(α)`. -/
public theorem sign_eval_eq_neg_sign_deriv_left {p : Polynomial ℝ} {α a : ℝ} (hroot : p.eval α = 0)
    (hp'0 : (derivative p).eval α ≠ 0) (haα : a < α)
    (hp_only : ∀ z ∈ Set.Icc a α, p.eval z = 0 → z = α) :
    SignType.sign (p.eval a) = - SignType.sign ((derivative p).eval α) := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff.mp (eventually_sign_eval_simple_root hroot hp'0)
  set δ := min (ε / 2) ((α - a) / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  set xL := α - δ with hxL
  have hxL_lt : xL < α := by rw [hxL]; linarith
  have hxL_gt : a < xL := by
    have : δ ≤ (α - a) / 2 := min_le_right _ _
    rw [hxL]; linarith
  have hdist : dist xL α < ε := by
    have hle : δ ≤ ε / 2 := min_le_left _ _
    rw [hxL, Real.dist_eq]
    have : xL - α = -δ := by rw [hxL]; ring
    rw [this, abs_neg, abs_of_pos hδpos]; linarith
  have hsxL : SignType.sign (p.eval xL) = - SignType.sign ((derivative p).eval α) := by
    rw [hball hdist]
    have : xL - α < 0 := by rw [hxL]; linarith
    rw [sign_neg this, neg_one_mul]
  have hno : ∀ z ∈ Set.Icc a xL, p.eval z ≠ 0 := by
    intro z hz hz0
    have hzα : z = α := hp_only z ⟨hz.1, le_trans hz.2 hxL_lt.le⟩ hz0
    rw [hzα] at hz; exact absurd hz.2 (not_le.mpr hxL_lt)
  rw [sign_eval_eq_of_no_root hxL_gt.le hno]; exact hsxL

/-- **Local root-crossing.** Across a simple root `α` of `p` (generic position: `α` the only root
of `p` in `[a,α]` and `[α,b]`, and no Sturm-tail member vanishes in `[a,b]`), the sign variations of
the Sturm sequence drop by exactly one. -/
public theorem signVarAt_drop_at_simple_root {p : Polynomial ℝ} {α a b : ℝ}
    (hp'ne : derivative p ≠ 0) (hroot : p.eval α = 0) (hp'0 : (derivative p).eval α ≠ 0)
    (haα : a < α) (hαb : α < b)
    (hp_left : ∀ z ∈ Set.Icc a α, p.eval z = 0 → z = α)
    (hp_right : ∀ z ∈ Set.Icc α b, p.eval z = 0 → z = α)
    (htail : ∀ q ∈ (sturmSeq p).tail, ∀ z ∈ Set.Icc a b, q.eval z ≠ 0) :
    signVarAt (sturmSeq p) a = signVarAt (sturmSeq p) b + 1 := by
  have hab : a ≤ b := le_of_lt (lt_trans haα hαb)
  have hseq : sturmSeq p = p :: sturmAux (derivative p) (-(p % derivative p)) := by
    unfold sturmSeq; rw [sturmAux_cons hp'ne]
  rw [hseq, List.tail_cons] at htail
  set tail := sturmAux (derivative p) (-(p % derivative p)) with htaildef
  obtain ⟨rest, hrest⟩ : ∃ rest, tail = derivative p :: rest := by
    have hh : tail.head? = some (derivative p) := sturmAux_head? _ _
    rcases hc : tail with _ | ⟨c, r⟩
    · rw [hc] at hh; simp at hh
    · rw [hc, List.head?_cons, Option.some.injEq] at hh; exact ⟨r, by rw [hh]⟩
  have hp'mem : derivative p ∈ tail := by rw [hrest]; exact List.mem_cons_self ..
  have hp'b : (derivative p).eval b ≠ 0 := htail _ hp'mem b ⟨hab, le_refl b⟩
  have hpa : SignType.sign (p.eval a) = - SignType.sign ((derivative p).eval α) :=
    sign_eval_eq_neg_sign_deriv_left hroot hp'0 haα hp_left
  have hpb : SignType.sign (p.eval b) = SignType.sign ((derivative p).eval α) :=
    sign_eval_eq_sign_deriv_right hroot hp'0 hαb hp_right
  have hc'0 : SignType.sign ((derivative p).eval α) ≠ 0 := by
    rw [Ne, sign_eq_zero_iff]; exact hp'0
  have hne : SignType.sign (p.eval a) ≠ SignType.sign (p.eval b) := by
    rw [hpa, hpb]; exact (by decide : ∀ c : SignType, c ≠ 0 → -c ≠ c) _ hc'0
  have hp'b_eq : SignType.sign ((derivative p).eval b) = SignType.sign (p.eval b) := by
    rw [hpb]
    exact (sign_eval_eq_of_no_root hαb.le
      (fun z hz => htail _ hp'mem z ⟨le_trans haα.le hz.1, hz.2⟩)).symm
  have hfirst : ((tail.map (fun q => SignType.sign (q.eval b))).filter (· ≠ 0)).head?
      = some (SignType.sign (p.eval b)) := by
    rw [hrest, filter_map_sign_head?_cons hp'b, hp'b_eq]
  have htaileq : tail.map (fun q => SignType.sign (q.eval a))
      = tail.map (fun q => SignType.sign (q.eval b)) :=
    map_sign_eq_of_no_root hab htail
  have hpa0 : p.eval a ≠ 0 := by
    intro h; have := hp_left a ⟨le_refl a, haα.le⟩ h; linarith
  have hpb0 : p.eval b ≠ 0 := by
    intro h; have := hp_right b ⟨hαb.le, le_refl b⟩ h; linarith
  rw [hseq]
  exact signVarAt_cons_head_drop hpa0 hpb0 hne htaileq hfirst

/-! ## Single critical point: the decoupled crossing (chain-walk + head-drop) -/

section SingleCrit
attribute [local instance] Classical.propDecidable

/-- **Single-critical-point crossing.** If `c ∈ [a, b]` is the *only* point of `[a, b]` where any
member of the Sturm sequence of a squarefree `p` vanishes (with `p(a), p(b) ≠ 0`), then `V` drops by
`1` if `p(c) = 0` and is unchanged otherwise. Both endpoints' sign patterns `FlankReduce` (via
`flankReduce_chain_walk`) to the *same* chain with the interior `c`-vanishers removed; on that reduced
chain only the head `p` can cross, so the change collapses to a single head-drop. This is the per-point
quantum of Sturm's theorem — and it also covers the case `c = a`/`c = b` (a tail member vanishing at an
endpoint, which then necessarily has `p(c) ≠ 0`) and the degenerate no-critical case. -/
public theorem signVarAt_drop_at_critical_point {p : Polynomial ℝ} (hp : Squarefree p)
    {a b c : ℝ} (hab : a ≤ b) (hc : c ∈ Set.Icc a b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0)
    (h_only : ∀ q ∈ sturmSeq p, ∀ z ∈ Set.Icc a b, q.eval z = 0 → z = c) :
    signVarAt (sturmSeq p) a
      = signVarAt (sturmSeq p) b + (if p.eval c = 0 then 1 else 0) := by
  have hseed : IsCoprime p (derivative p) := isCoprime_self_derivative hp
  -- members nonvanishing at `c` are root-free on `[a,b]`, hence have constant sign there
  have hrootfree : ∀ q ∈ sturmSeq p, q.eval c ≠ 0 → ∀ z ∈ Set.Icc a b, q.eval z ≠ 0 := by
    intro q hq hqc z hz hz0
    exact hqc (h_only q hq z hz hz0 ▸ hz0)
  have hsignconst : ∀ q ∈ sturmSeq p, q.eval c ≠ 0 → ∀ z ∈ Set.Icc a b,
      SignType.sign (q.eval z) = SignType.sign (q.eval c) := by
    intro q hq hqc z hz
    have h1 : SignType.sign (q.eval a) = SignType.sign (q.eval z) :=
      sign_eval_eq_of_no_root hz.1 (fun w hw => hrootfree q hq hqc w ⟨hw.1, hw.2.trans hz.2⟩)
    have h2 : SignType.sign (q.eval a) = SignType.sign (q.eval c) :=
      sign_eval_eq_of_no_root hc.1 (fun w hw => hrootfree q hq hqc w ⟨hw.1, hw.2.trans hc.2⟩)
    rw [← h1, h2]
  -- the three `flankReduce_chain_walk` hypotheses, over `sturmSeq p`
  have hiso : ∀ x y, [x, y] <:+: sturmSeq p → ¬ (x.eval c = 0 ∧ y.eval c = 0) := by
    rintro x y hinf ⟨hx0, hy0⟩
    exact not_common_root (sturmAux_consecutive_coprime p (derivative p) hseed x y hinf) hx0 hy0
  have hlast : ∀ g, (sturmSeq p).getLast? = some g → g.eval c ≠ 0 := by
    intro g hg
    obtain ⟨r, hr, hCr⟩ := Polynomial.isUnit_iff.mp
      (sturmAux_getLast_isUnit p (derivative p) hseed g hg)
    rw [← hCr, eval_C]; exact hr.ne_zero
  have hflank : ∀ z ∈ Set.Icc a b, ∀ x m y, [x, m, y] <:+: sturmSeq p → m.eval c = 0 →
      SignType.sign (x.eval z) ≠ 0 ∧ SignType.sign (y.eval z) ≠ 0 ∧
      SignType.sign (x.eval z) ≠ SignType.sign (y.eval z) := by
    intro z hz x m y hinf hmc
    have hxm : [x, m] <:+: sturmSeq p := (show [x, m] <:+: [x, m, y] from ⟨[], [y], rfl⟩).trans hinf
    have hmy : [m, y] <:+: sturmSeq p := ((List.suffix_cons x [m, y]).isInfix).trans hinf
    have hcopxm : IsCoprime x m := sturmAux_consecutive_coprime p (derivative p) hseed x m hxm
    have hcopmy : IsCoprime m y := sturmAux_consecutive_coprime p (derivative p) hseed m y hmy
    have hxc : x.eval c ≠ 0 := fun h => not_common_root hcopxm h hmc
    have hyc : y.eval c ≠ 0 := fun h => not_common_root hcopmy hmc h
    have hsucc : y = -(x % m) := sturmAux_consecutive_succ p (derivative p) x m y hinf
    obtain ⟨hxc', hopp⟩ := sign_neighbours_opposite_at_interior_root hcopxm hmc
    have hoppy : SignType.sign (x.eval c) ≠ SignType.sign (y.eval c) := by rw [hsucc]; exact hopp
    have hxmem : x ∈ sturmSeq p := hxm.subset (by simp)
    have hymem : y ∈ sturmSeq p := hmy.subset (by simp)
    have hsx := hsignconst x hxmem hxc z hz
    have hsy := hsignconst y hymem hyc z hz
    refine ⟨?_, ?_, ?_⟩
    · rw [hsx]; exact hxc'
    · rw [hsy, Ne, sign_eq_zero_iff]; exact hyc
    · rw [hsx, hsy]; exact hoppy
  -- split off the head `p :: T`
  obtain ⟨T, hT⟩ : ∃ T, sturmSeq p = p :: T := by
    have hh := sturmSeq_head? p
    rcases h : sturmSeq p with _ | ⟨c0, r⟩
    · rw [h] at hh; simp at hh
    · rw [h, List.head?_cons, Option.some_inj] at hh; exact ⟨r, by rw [hh]⟩
  set KT := T.filter (fun q => decide (q.eval c ≠ 0)) with hKT
  -- both endpoints reduce to the same kept chain `p :: KT`
  have hfra : signVarAt (sturmSeq p) a = signVarAt (p :: KT) a := by
    rw [hT]
    exact signVarAt_eq_of_flankReduce
      (flankReduce_chain_walk p T
        (fun x m y hinf hmc => hflank a ⟨le_refl a, hab⟩ x m y (by rw [hT]; exact hinf) hmc)
        (fun x y hinf => hiso x y (by rw [hT]; exact hinf))
        (fun g hg => hlast g (by rw [hT]; exact hg)))
  have hfrb : signVarAt (sturmSeq p) b = signVarAt (p :: KT) b := by
    rw [hT]
    exact signVarAt_eq_of_flankReduce
      (flankReduce_chain_walk p T
        (fun x m y hinf hmc => hflank b ⟨hab, le_refl b⟩ x m y (by rw [hT]; exact hinf) hmc)
        (fun x y hinf => hiso x y (by rw [hT]; exact hinf))
        (fun g hg => hlast g (by rw [hT]; exact hg)))
  rw [hfra, hfrb]
  -- the kept tail is root-free on `[a,b]`
  have hKTsub : ∀ q ∈ KT, q ∈ sturmSeq p ∧ q.eval c ≠ 0 := by
    intro q hq
    rw [hKT, List.mem_filter] at hq
    exact ⟨by rw [hT]; exact List.mem_cons_of_mem p hq.1, of_decide_eq_true hq.2⟩
  have hKTrf : ∀ q ∈ KT, ∀ z ∈ Set.Icc a b, q.eval z ≠ 0 := by
    intro q hq z hz
    obtain ⟨hmem, hqc⟩ := hKTsub q hq
    exact hrootfree q hmem hqc z hz
  have hpmem : p ∈ sturmSeq p := by rw [hT]; exact List.mem_cons_self ..
  by_cases hpc : p.eval c = 0
  · rw [if_pos hpc]
    have hac : a < c := hc.1.lt_of_ne (fun h => ha (by rw [h]; exact hpc))
    have hcb : c < b := hc.2.lt_of_ne (fun h => hb (by rw [← h]; exact hpc))
    have hp'c : (derivative p).eval c ≠ 0 := fun h => not_common_root hseed hpc h
    have hp'ne : derivative p ≠ 0 := fun h => hp'c (by rw [h]; simp)
    have hpa0 : p.eval a ≠ 0 := ha
    have hpb0 : p.eval b ≠ 0 := hb
    have hpa_sign : SignType.sign (p.eval a) = - SignType.sign ((derivative p).eval c) :=
      sign_eval_eq_neg_sign_deriv_left hpc hp'c hac
        (fun z hz hz0 => h_only p hpmem z ⟨hz.1, hz.2.trans hcb.le⟩ hz0)
    have hpb_sign : SignType.sign (p.eval b) = SignType.sign ((derivative p).eval c) :=
      sign_eval_eq_sign_deriv_right hpc hp'c hcb
        (fun z hz hz0 => h_only p hpmem z ⟨hac.le.trans hz.1, hz.2⟩ hz0)
    have hne : SignType.sign (p.eval a) ≠ SignType.sign (p.eval b) := by
      rw [hpa_sign, hpb_sign]
      have hc'0 : SignType.sign ((derivative p).eval c) ≠ 0 := by rw [Ne, sign_eq_zero_iff]; exact hp'c
      exact (by decide : ∀ s : SignType, s ≠ 0 → -s ≠ s) _ hc'0
    -- `T = p' :: T'`, and `p'` is kept (does not vanish at `c`), so `KT = p' :: …`
    obtain ⟨T', hT'⟩ : ∃ T', T = derivative p :: T' := by
      have hsa : sturmSeq p = p :: sturmAux (derivative p) (-(p % derivative p)) := by
        unfold sturmSeq; rw [sturmAux_cons hp'ne]
      rw [hT] at hsa
      injection hsa with _ hTeq
      have hh := sturmAux_head? (derivative p) (-(p % derivative p))
      rw [← hTeq] at hh
      rcases h' : T with _ | ⟨w, r⟩
      · rw [h'] at hh; simp at hh
      · rw [h', List.head?_cons, Option.some_inj] at hh; exact ⟨r, by rw [hh]⟩
    have hp'mem : derivative p ∈ sturmSeq p := by
      rw [hT, hT']; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have hKThead : KT = derivative p :: T'.filter (fun q => decide (q.eval c ≠ 0)) := by
      rw [hKT, hT']; simp [hp'c]
    have hp'b0 : (derivative p).eval b ≠ 0 := hrootfree (derivative p) hp'mem hp'c b ⟨hab, le_refl b⟩
    have hfirst : ((KT.map (fun q => SignType.sign (q.eval b))).filter (· ≠ 0)).head?
        = some (SignType.sign (p.eval b)) := by
      rw [hKThead, filter_map_sign_head?_cons hp'b0]
      congr 1
      rw [hsignconst (derivative p) hp'mem hp'c b ⟨hab, le_refl b⟩, ← hpb_sign]
    have hKTtail : KT.map (fun q => SignType.sign (q.eval a))
        = KT.map (fun q => SignType.sign (q.eval b)) :=
      map_sign_eq_of_no_root hab hKTrf
    exact signVarAt_cons_head_drop hpa0 hpb0 hne hKTtail hfirst
  · rw [if_neg hpc]
    have hKrf : ∀ q ∈ (p :: KT), ∀ z ∈ Set.Icc a b, q.eval z ≠ 0 := by
      intro q hq z hz
      rcases List.mem_cons.mp hq with h | h
      · rw [h]; exact hrootfree p hpmem hpc z hz
      · exact hKTrf q h z hz
    have := signVarAt_eq_of_no_root hab hKrf
    omega

end SingleCrit

/-! ## Playground — what else falls out of the machinery -/

/-- **Bolzano, sign form.** A sign change of `p` between `a` and `b` forces a real root in `[a,b]`
(contrapositive of local constancy). -/
public theorem exists_root_of_sign_ne {p : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : SignType.sign (p.eval a) ≠ SignType.sign (p.eval b)) :
    ∃ x ∈ Set.Icc a b, p.eval x = 0 := by
  by_contra hcon
  exact h (sign_eval_eq_of_no_root hab (fun x hx hx0 => hcon ⟨x, hx, hx0⟩))

/-- **Bridge to Descartes' rule of signs.** Mathlib's `signVariations` (sign changes of the
coefficient list) is exactly our `signChanges` of the mapped coefficient signs — so the whole
`signChanges` toolkit (zeros invisible, interior cancellation, head recursion) transfers to it. -/
public theorem signVariations_eq_signChanges (P : Polynomial ℝ) :
    P.signVariations = signChanges (P.coeffList.map SignType.sign) := by
  unfold Polynomial.signVariations signChanges
  rfl

/-- A simple corollary of the bridge: the sign-variation count of the coefficients is invariant
under prepending a zero sign (the `signChanges` lemma, now visible for Descartes). -/
public theorem signChanges_coeff_cons_zero (P : Polynomial ℝ) :
    signChanges (0 :: P.coeffList.map SignType.sign) = P.signVariations := by
  rw [signChanges_cons_zero, signVariations_eq_signChanges]

/-- **Sturm's theorem.** For squarefree `p` and `a < b` with neither endpoint a root of `p`, the
drop in sign variations of the Sturm sequence equals the number of distinct real roots in `(a, b]`.
-/
public theorem sturm (p : Polynomial ℝ) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    signVarAt (sturmSeq p) a - signVarAt (sturmSeq p) b =
      (p.roots.toFinset.filter (fun x => a < x ∧ x ≤ b)).card := by
  have hp0 : p ≠ 0 := hp.ne_zero
  set Pc := (sturmSeq p).prod with hPc
  have hPc0 : Pc ≠ 0 := sturmSeq_prod_ne_zero hp0
  have hpmem : p ∈ sturmSeq p := by
    rcases h : sturmSeq p with _ | ⟨hd, tl⟩
    · have := sturmSeq_head? p; rw [h] at this; simp at this
    · have hh := sturmSeq_head? p
      rw [h, List.head?_cons, Option.some_inj] at hh
      rw [← hh]; exact List.mem_cons_self ..
  -- a root of any chain member is a root of the product (a "critical point")
  have hcrit : ∀ z, ∀ q ∈ sturmSeq p, q.eval z = 0 → Pc.eval z = 0 := by
    intro z q hq hqz
    have hev : ∀ (L : List (Polynomial ℝ)), L.prod.eval z = (L.map (fun r => r.eval z)).prod := by
      intro L
      induction L with
      | nil => simp
      | cons hd tl ih => rw [List.prod_cons, eval_mul, ih, List.map_cons, List.prod_cons]
    rw [hPc, hev]
    exact List.prod_eq_zero (List.mem_map.mpr ⟨q, hq, hqz⟩)
  -- every p-root is a critical point
  have pset_sub_cset : ∀ a' b' x, x ∈ p.roots.toFinset.filter (fun y => a' < y ∧ y ≤ b') →
      x ∈ Pc.roots.toFinset.filter (fun y => a' < y ∧ y ≤ b') := by
    intro a' b' x hx
    rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots'] at hx ⊢
    exact ⟨⟨hPc0, hcrit x p hpmem hx.1.2⟩, hx.2⟩
  -- half-open interval count splits at an interior point
  have split : ∀ (Q : Polynomial ℝ) (a' d' b' : ℝ), a' ≤ d' → d' ≤ b' →
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
      signVarAt (sturmSeq p) a = signVarAt (sturmSeq p) b
        + (p.roots.toFinset.filter (fun x => a < x ∧ x ≤ b)).card by
    have := key _ a b hab.le ha hb rfl
    omega
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hab ha hb hcard
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- no critical point in `(a, b]`: V is constant and there are no p-roots
    subst hn0
    have hcset : Pc.roots.toFinset.filter (fun x => a < x ∧ x ≤ b) = ∅ :=
      Finset.card_eq_zero.mp hcard
    have hpset0 : (p.roots.toFinset.filter (fun x => a < x ∧ x ≤ b)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      exact (Finset.eq_empty_iff_forall_notMem.mp hcset) x (pset_sub_cset a b x hx)
    rw [hpset0, Nat.add_zero]
    have h_only : ∀ q ∈ sturmSeq p, ∀ z ∈ Set.Icc a b, q.eval z = 0 → z = a := by
      intro q hq z hz hqz
      by_contra hza
      have haz : a < z := lt_of_le_of_ne hz.1 (Ne.symm hza)
      have hmem : z ∈ Pc.roots.toFinset.filter (fun x => a < x ∧ x ≤ b) := by
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots']
        exact ⟨⟨hPc0, hcrit z q hq hqz⟩, haz, hz.2⟩
      rw [hcset] at hmem; exact absurd hmem (Finset.notMem_empty z)
    have hpt := signVarAt_drop_at_critical_point hp hab ⟨le_refl a, hab⟩ ha hb h_only
    rw [if_neg ha] at hpt; exact hpt
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
    -- in `(d, b]` the only critical / only possible p-root is `c`
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
    have hpset_db : (p.roots.toFinset.filter (fun x => d < x ∧ x ≤ b)).card
        = (if p.eval c = 0 then 1 else 0) := by
      by_cases hpc : p.eval c = 0
      · rw [if_pos hpc, Finset.card_eq_one]
        refine ⟨c, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun x hx =>
          hdb_eq_c p (fun z hz => hcrit z p hpmem hz) x hx⟩⟩
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots']
        exact ⟨⟨hp0, hpc⟩, hdc, hcb⟩
      · rw [if_neg hpc, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro x hx
        have hxc := hdb_eq_c p (fun z hz => hcrit z p hpmem hz) x hx
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots'] at hx
        rw [hxc] at hx; exact hpc hx.1.2
    have h_only_db : ∀ q ∈ sturmSeq p, ∀ z ∈ Set.Icc d b, q.eval z = 0 → z = c := by
      intro q hq z hz hqz
      refine hdb_eq_c Pc (fun w hw => hw) z ?_
      rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots']
      refine ⟨⟨hPc0, hcrit z q hq hqz⟩, ?_, hz.2⟩
      rcases lt_or_eq_of_le hz.1 with h | h
      · exact h
      · exfalso; exact hPcd (by rw [h]; exact hcrit z q hq hqz)
    have hstep := signVarAt_drop_at_critical_point hp hdb ⟨hdc.le, hcb⟩ hpd hb h_only_db
    have hcard_ad : (Pc.roots.toFinset.filter (fun x => a < x ∧ x ≤ d)).card = n - 1 := by
      have hsp := split Pc a d b had hdb
      rw [hcard, hcset_db] at hsp
      omega
    have hrec := ih (n - 1) (by omega) a d had ha hpd hcard_ad
    have hpsplit := split p a d b had hdb
    rw [hrec, hstep, hpsplit, hpset_db]
    omega

end Sturm
