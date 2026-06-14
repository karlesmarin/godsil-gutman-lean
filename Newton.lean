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
  sorry

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
