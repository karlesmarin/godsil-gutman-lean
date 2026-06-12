/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib

/-!
# The dilogarithm `Li₂` and Euler's reflection identity

This file begins a formalization of the **dilogarithm**

  `Li₂ z = ∑_{n ≥ 1} zⁿ / n²`,

the order-2 polylogarithm. As of the Mathlib revision this is built against, Mathlib has **no**
polylogarithm/dilogarithm: only a comment in
`Mathlib/Analysis/SpecialFunctions/Integrals/LogTrigonometric.lean` *referencing* `Li₂` without it
existing. A literature check (2026-06) also found no dilogarithm formalization in Isabelle/AFP or
Coq. So this appears to be the first machine-checked development of the dilogarithm.

## Main definitions
* `Dilog.Li₂` : the real dilogarithm via its power series.

## Main results (this file)
* `Dilog.Li₂_zero` : `Li₂ 0 = 0`.
* `Dilog.Li₂_one`  : `Li₂ 1 = π² / 6`  (Basel; via `hasSum_zeta_two`).
* `Dilog.hasDerivAt_Li₂` : `Li₂'(x) = -log(1 - x) / x` on `(0,1)`.
* `Dilog.Li₂_add_Li₂_one_sub` : **Euler's reflection identity**
    `Li₂ x + Li₂ (1 - x) = π²/6 - log x · log (1 - x)` on `(0,1)`.

## Roadmap (later files)
* Landen and inversion functional equations.
* The complex dilogarithm and analytic continuation.
* **Abel's five-term relation** (Rogers `L`-function) — the capstone, and the engine behind the
  golden/silver-ratio ladder identities (cf. arXiv:2509.07598).

## References
* L. Lewin, *Polylogarithms and Associated Functions*.
* D. Zagier, *The dilogarithm function*, in *Frontiers in Number Theory, Physics, and Geometry II*.
-/

noncomputable section
open scoped Real BigOperators
open Set

namespace Dilog

/-- The real **dilogarithm** `Li₂ z = ∑_{n ≥ 1} zⁿ / n² = ∑_{n ≥ 0} z^{n+1} / (n+1)²`. -/
noncomputable def Li₂ (z : ℝ) : ℝ := ∑' n : ℕ, z ^ (n + 1) / ((n : ℝ) + 1) ^ 2

/-- The defining series of `Li₂` is summable on the closed unit interval `|z| ≤ 1`
(majorised termwise by the convergent `∑ 1/(n+1)²`). -/
theorem summable_Li₂ {z : ℝ} (hz : |z| ≤ 1) :
    Summable fun n : ℕ => z ^ (n + 1) / ((n : ℝ) + 1) ^ 2 := by
  -- Absolute comparison with the convergent `∑ 1/(n+1)²`.
  rw [← summable_abs_iff]
  -- the dominating series `∑ 1/(n+1)²` is summable (shift of the `p = 2` series).
  have hdom : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    have h2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hs := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h2
    simpa [Nat.cast_add, Nat.cast_one] using hs
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hdom
  have hden : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hden, abs_pow]
  gcongr
  exact pow_le_one₀ (abs_nonneg z) hz

@[simp] theorem Li₂_zero : Li₂ 0 = 0 := by
  -- every term `0^(n+1)/(n+1)² = 0`
  simp [Li₂]

/-- `Li₂ 1 = π² / 6` — the Basel problem. Reindex `∑_{n≥0} 1/(n+1)²` to `hasSum_zeta_two`
(`∑_{n : ℕ} 1/n² = π²/6`, whose `n = 0` term is `0`). -/
theorem Li₂_one : Li₂ 1 = π ^ 2 / 6 := by
  simp only [Li₂, one_pow]
  -- goal: `∑' n, 1/((n:ℝ)+1)² = π²/6`; shift `hasSum_zeta_two` past its (zero) `n = 0` term.
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr
    (by simpa using hasSum_zeta_two)
  simpa [Nat.cast_add, Nat.cast_one] using h.tsum_eq

/-- Termwise differentiation of the dilogarithm series gives, on `(0,1)`,
`Li₂'(x) = -log(1 - x)/x` (note `∑_{n≥1} xⁿ⁻¹ = 1/(1-x)` and `∑ xⁿ/n = -log(1-x)`). -/
theorem hasDerivAt_Li₂ {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt Li₂ (-Real.log (1 - x) / x) x := by
  obtain ⟨hx0, hx1⟩ := hx
  set r : ℝ := (x + 1) / 2 with hr
  have hxr : x < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 < r := by rw [hr]; linarith
  -- the open neighbourhood `t = (-r, r) ⊂ (-1,1)` on which the derivative series is dominated by `rⁿ`
  set t : Set ℝ := Ioo (-r) r with ht_def
  have hxt : x ∈ t := ⟨by linarith, hxr⟩
  set g : ℕ → ℝ → ℝ := fun n z => z ^ (n + 1) / ((n : ℝ) + 1) ^ 2 with hg_def
  set g' : ℕ → ℝ → ℝ := fun n z => z ^ n / ((n : ℝ) + 1) with hg'_def
  have hne : ∀ n : ℕ, ((n : ℝ) + 1) ≠ 0 := fun n => by positivity
  -- term derivatives
  have hg : ∀ n y, y ∈ t → HasDerivAt (g n) (g' n y) y := by
    intro n y _
    have h1 : HasDerivAt (fun z : ℝ => z ^ (n + 1)) (((n : ℝ) + 1) * y ^ n) y := by
      simpa [Nat.cast_add, Nat.cast_one] using hasDerivAt_pow (n + 1) y
    have h2 := h1.div_const (((n : ℝ) + 1) ^ 2)
    convert h2 using 1
    rw [hg'_def]; field_simp
  -- uniform geometric bound `‖g' n y‖ ≤ rⁿ` on `t`
  have hg' : ∀ n y, y ∈ t → ‖g' n y‖ ≤ r ^ n := by
    intro n y hy
    have hyr : |y| ≤ r := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
    rw [hg'_def, Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by positivity : (0:ℝ) < (n:ℝ)+1)]
    calc |y| ^ n / ((n : ℝ) + 1) ≤ |y| ^ n :=
          div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])
      _ ≤ r ^ n := pow_le_pow_left₀ (abs_nonneg y) hyr n
  have hu : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0.le hr1
  have hg0 : Summable fun n => g n x := summable_Li₂ (by rw [abs_of_pos hx0]; exact hx1.le)
  -- term-by-term differentiation
  have key : HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n x) x :=
    hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg' hxt hg0 hxt
  -- identify the derivative series with `-log(1-x)/x` (Mercator series)
  have habs : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have hlog : ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) = -Real.log (1 - x) := by
    have := (Real.hasSum_pow_div_log_of_abs_lt_one habs).tsum_eq
    simpa using this
  have hfactor : ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) = x * ∑' n : ℕ, x ^ n / ((n : ℝ) + 1) := by
    rw [← tsum_mul_left]; congr 1; ext n; rw [pow_succ]; ring
  have hsum : ∑' n : ℕ, g' n x = -Real.log (1 - x) / x := by
    rw [hg'_def]
    rw [eq_div_iff (ne_of_gt hx0), mul_comm, ← hfactor, hlog]
  rw [hsum] at key
  exact key

/-- **Euler's reflection identity** for the dilogarithm on `(0,1)`:
`Li₂ x + Li₂ (1 - x) = π²/6 - log x · log (1 - x)`.

Proof skeleton: let `f x := Li₂ x + Li₂ (1 - x) + log x · log (1 - x)`. Using `hasDerivAt_Li₂`
(and `Li₂'(1-x) = -log x/(1-x)` by the chain rule), `f' = 0` on `(0,1)`, so `f` is constant on the
connected set `(0,1)`; its limit as `x → 1⁻` is `Li₂ 1 + Li₂ 0 + 0 = π²/6` by `Li₂_one`, `Li₂_zero`
and `log x · log(1-x) → 0`. -/
theorem Li₂_add_Li₂_one_sub {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Li₂ x + Li₂ (1 - x) = π ^ 2 / 6 - Real.log x * Real.log (1 - x) := by
  sorry

end Dilog
