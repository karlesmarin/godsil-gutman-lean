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
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

open Polynomial MSS

namespace Newton

variable {p : Polynomial ℝ}

/-- **(1) Rolle stone.** The derivative of a real-rooted real polynomial is real-rooted. -/
public theorem RealRooted.derivative (hp : RealRooted p) :
    RealRooted (Polynomial.derivative p) := by
  sorry

/-- Real-rootedness is preserved by the **reversal** `x ↦ 1/x`, for nonzero constant term. -/
public theorem RealRooted.reverse (hp : RealRooted p) (h0 : p.coeff 0 ≠ 0) :
    RealRooted p.reverse := by
  sorry

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
