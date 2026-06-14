/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

/-
# Newton's inequalities (real-rooted ⟹ log-concave elementary symmetric means)

Reverse-engine target (2026-06-14): confirmed ABSENT from Mathlib (it has `Multiset.esymm` but not
the Newton inequalities). FOUNDATIONAL — the classical bridge "real-rooted ⟹ log-concave coefficients"
underlying matching-poly / Chow / Heilmann–Lieb log-concavity. Built on our `RealStable` (RealRooted).

Skeleton: statement + key lemmas. Proof strategy:
  (1) derivative of a real-rooted real polynomial is real-rooted (Rolle between consecutive roots);
  (2) base case: a real-rooted real quadratic has discriminant ≥ 0;
  (3) reduce index k by differentiating (n-2) times + reversal x↦1/x to a real-rooted quadratic.
-/
public import RealStable
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

open Polynomial MSS

namespace Newton

variable {p : Polynomial ℝ}

/-- **(1) Rolle stone.** The derivative of a real-rooted real polynomial is real-rooted. -/
public theorem RealRooted.derivative (hp : RealRooted p) :
    RealRooted (Polynomial.derivative p) := by
  rw [realRooted_iff_card_roots] at hp ⊢
  -- upper bound: #roots(p') ≤ deg(p');  Rolle bound: #roots(p) ≤ #roots(p') + 1;
  -- degree drop: deg(p') ≤ deg(p) - 1.  Squeeze with hp (#roots(p) = deg(p)) closes it.
  have hub : (Polynomial.derivative p).roots.card ≤ (Polynomial.derivative p).natDegree :=
    card_roots' _
  have hlb : p.roots.card ≤ (Polynomial.derivative p).roots.card + 1 :=
    card_roots_le_derivative p
  have hdle : (Polynomial.derivative p).natDegree ≤ p.natDegree - 1 :=
    natDegree_derivative_le p
  omega

/-- Real-rootedness is preserved by the **reversal** `x ↦ 1/x`, for nonzero constant term. -/
public theorem RealRooted.reverse (hp : RealRooted p) (_h0 : p.coeff 0 ≠ 0) :
    RealRooted p.reverse := by
  -- helper: the reverse of a product of monic linears is real-rooted (each reverse has degree ≤ 1)
  have key : ∀ s : Multiset ℝ,
      RealRooted ((s.map (fun r => X - C r)).prod).reverse := by
    intro s
    induction s using Multiset.induction with
    | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero]
      rw [← C_1, reverse_C]; exact realRooted_C 1
    | cons r t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain]
      refine RealRooted.mul ?_ ih
      have hd : ((X - C r : Polynomial ℝ).reverse).natDegree ≤ 1 :=
        le_trans (reverse_natDegree_le _) (by rw [natDegree_X_sub_C])
      exact Splits.of_natDegree_le_one hd
  -- p = C lc · ∏ (X - C r); reverse distributes, reverse (C lc) = C lc
  have hfact : C p.leadingCoeff * (p.roots.map (fun r => X - C r)).prod = p :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C (realRooted_iff_card_roots.mp hp)
  have hrev : p.reverse
      = C p.leadingCoeff * ((p.roots.map (fun r => X - C r)).prod).reverse := by
    conv_lhs => rw [← hfact]
    rw [reverse_mul_of_domain, reverse_C]
  rw [hrev]
  exact RealRooted.mul (realRooted_C _) (key p.roots)

/-- **(2) Base case.** A real-rooted real quadratic `a x² + b x + c` (a ≠ 0) has `b² - 4ac ≥ 0`. -/
public theorem realRooted_quadratic_discrim {a b c : ℝ} (ha : a ≠ 0)
    (h : RealRooted (C a * X ^ 2 + C b * X + C c)) :
    b ^ 2 - 4 * a * c ≥ 0 := by
  set q := C a * X ^ 2 + C b * X + C c with hq
  -- q has degree 2, hence is nonzero
  have hdeg : q.degree = 2 := degree_quadratic ha
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0, degree_zero] at hdeg; exact absurd hdeg (by decide)
  have hnat : q.natDegree = 2 := natDegree_eq_of_degree_eq_some hdeg
  -- real-rootedness ⟹ #roots = natDegree = 2 > 0, so a real root exists
  have hcard : q.roots.card = q.natDegree := realRooted_iff_card_roots.mp h
  rw [hnat] at hcard
  have hne : q.roots ≠ 0 := by
    intro h0; rw [h0, Multiset.card_zero] at hcard; exact absurd hcard (by decide)
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
  have hroot : q.IsRoot x := (mem_roots hq0).mp hx
  -- evaluate: a x² + b x + c = 0
  have he : a * x ^ 2 + b * x + c = 0 := by
    have h2 : q.eval x = 0 := hroot
    rw [hq] at h2
    simpa [eval_add, eval_mul, eval_pow, eval_C, eval_X] using h2
  -- b² − 4ac = (2ax+b)² − 4a·(a x²+b x+c) = (2ax+b)² ≥ 0
  have key : b ^ 2 - 4 * a * c
      = (2 * a * x + b) ^ 2 - 4 * a * (a * x ^ 2 + b * x + c) := by ring
  rw [he, mul_zero, sub_zero] at key
  rw [key]
  exact sq_nonneg _

/-- **Real-rootedness is preserved by iterated differentiation** (iterate Rolle). -/
public theorem RealRooted.iterate_derivative (hp : RealRooted p) (k : ℕ) :
    RealRooted (Polynomial.derivative^[k] p) := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact RealRooted.derivative ih

/-- **(2′) Base case, coefficient form.** A real-rooted polynomial of `natDegree ≤ 2` satisfies the
discriminant inequality on its low coefficients: `a₁² ≥ 4 a₂ a₀`. (For `natDegree < 2` the leading
`a₂ = 0` makes it `a₁² ≥ 0`.) This is the form the reduction below consumes. -/
public theorem realRooted_discrim_coeff {q : Polynomial ℝ} (hq : RealRooted q)
    (hdeg : q.natDegree ≤ 2) :
    q.coeff 1 ^ 2 ≥ 4 * q.coeff 2 * q.coeff 0 := by
  by_cases hc2 : q.coeff 2 = 0
  · rw [hc2]; simpa using sq_nonneg (q.coeff 1)
  · have h2 : q.natDegree = 2 := le_antisymm hdeg (le_natDegree_of_ne_zero hc2)
    have hq0 : q ≠ 0 := fun h => hc2 (by rw [h]; simp)
    have hcard : q.roots.card = 2 := by rw [realRooted_iff_card_roots.mp hq, h2]
    have hne : q.roots ≠ 0 := by
      intro h0; rw [h0, Multiset.card_zero] at hcard; exact absurd hcard (by decide)
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
    have hroot : q.IsRoot x := (mem_roots hq0).mp hx
    have he : q.coeff 0 + q.coeff 1 * x + q.coeff 2 * x ^ 2 = 0 := by
      have h3 : q.natDegree < 3 := by omega
      have hev : q.eval x = 0 := hroot
      rw [eval_eq_sum_range' h3] at hev
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, mul_one, pow_one,
        zero_add] at hev
      linarith [hev]
    have key : q.coeff 1 ^ 2 - 4 * q.coeff 2 * q.coeff 0
        = (2 * q.coeff 2 * x + q.coeff 1) ^ 2
          - 4 * q.coeff 2 * (q.coeff 0 + q.coeff 1 * x + q.coeff 2 * x ^ 2) := by ring
    rw [he, mul_zero, sub_zero] at key
    linarith [sq_nonneg (2 * q.coeff 2 * x + q.coeff 1), key]

/-- **(3) Newton's inequalities.** For a monic real-rooted polynomial of degree `n` with roots
multiset `s = p.roots`, for `1 ≤ k ≤ n-1`,
`e_k(s)² · C(n,k-1)·C(n,k+1) ≥ e_{k-1}(s)·e_{k+1}(s) · C(n,k)²`. -/
public theorem newton_inequality (hp : RealRooted p) (hmonic : p.Monic)
    {k : ℕ} (hk : 1 ≤ k) (hk2 : k + 1 ≤ p.natDegree) :
    (p.roots.esymm k) ^ 2 * ((p.natDegree.choose (k - 1) : ℝ) * (p.natDegree.choose (k + 1) : ℝ))
      ≥ (p.roots.esymm (k - 1)) * (p.roots.esymm (k + 1)) * ((p.natDegree.choose k : ℝ)) ^ 2 := by
  sorry

/-- **Corollary (log-concavity of normalized means).** `p_{k-1} · p_{k+1} ≤ p_k²`. -/
public theorem newton_logConcave (hp : RealRooted p) (hmonic : p.Monic)
    {k : ℕ} (hk : 1 ≤ k) (hk2 : k + 1 ≤ p.natDegree) :
    (p.roots.esymm (k - 1) / (p.natDegree.choose (k - 1) : ℝ)) *
      (p.roots.esymm (k + 1) / (p.natDegree.choose (k + 1) : ℝ))
      ≤ (p.roots.esymm k / (p.natDegree.choose k : ℝ)) ^ 2 := by
  sorry

end Newton
