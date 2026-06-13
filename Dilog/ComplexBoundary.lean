/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib
import Dilog.Basic
import Dilog.Clausen

/-!
# The complex dilogarithm on the closed unit disk, and its boundary

First brick of the *zero-localization* program (O'Sullivan, "Zeros of the dilogarithm",
arXiv:1507.07980), built on the real `Cl₂` / Bernoulli-parabola machinery of
`Dilog/Clausen.lean`.

* `Li₂c z = ∑_{n≥1} zⁿ/n²` — the complex dilogarithm, convergent on `‖z‖ ≤ 1`.
* Boundary decomposition (O'Sullivan (2.8)–(2.9)): on the unit circle
  `Re Li₂c(e^{iθ}) = π²/6 − πθ/2 + θ²/4` and `Im Li₂c(e^{iθ}) = Cl₂(θ)`.
* `Li₂c` has **no zero on the unit circle** for `θ ∈ (0, 2π)` — the principal-branch
  `A = B = 0` case of O'Sullivan's Theorem 1.1, the complex upgrade of the Clock paper's
  `zetaState_never_orthogonal`.
-/

open Complex
open scoped BigOperators Real

namespace Dilog

/-- The complex dilogarithm `∑_{n≥1} zⁿ/n²`, convergent on the closed unit disk. -/
noncomputable def Li₂c (z : ℂ) : ℂ := ∑' n : ℕ, z ^ (n + 1) / ((n : ℂ) + 1) ^ 2

/-- The defining series of `Li₂c` is absolutely summable on the closed unit disk. -/
theorem summable_Li₂c {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) ^ 2) := by
  apply Summable.of_norm_bounded (summable_pow_div_add (1 : ℂ) 2 1 (by norm_num))
  intro n
  have hz1 : ‖z‖ ^ (n + 1) ≤ 1 :=
    (pow_le_pow_left₀ (norm_nonneg z) hz (n + 1)).trans_eq (one_pow _)
  simp only [Nat.cast_one]
  rw [norm_div, norm_div, norm_one, norm_pow]
  gcongr

/-- `‖e^{iθ}‖ ≤ 1` (in fact `= 1`). -/
private lemma norm_exp_mul_I_le (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * I)‖ ≤ 1 := by
  rw [Complex.norm_exp]; simp [Complex.mul_I_re]

/-- The real part of the `n`-th boundary term is `cos((n+1)θ)/(n+1)²`. -/
private lemma Li₂c_term_re (θ : ℝ) (n : ℕ) :
    ((Complex.exp ((θ : ℂ) * I)) ^ (n + 1) / ((n : ℂ) + 1) ^ 2).re
      = Real.cos (((n : ℝ) + 1) * θ) / ((n : ℝ) + 1) ^ 2 := by
  rw [show ((n : ℂ) + 1) ^ 2 = ((((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) from by push_cast; ring,
    Complex.div_ofReal_re,
    show (Complex.exp ((θ : ℂ) * I)) ^ (n + 1)
        = Complex.exp ((Complex.ofReal (((n : ℝ) + 1) * θ)) * I) from by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

/-- The imaginary part of the `n`-th boundary term is `sin((n+1)θ)/(n+1)²`. -/
private lemma Li₂c_term_im (θ : ℝ) (n : ℕ) :
    ((Complex.exp ((θ : ℂ) * I)) ^ (n + 1) / ((n : ℂ) + 1) ^ 2).im
      = Real.sin (((n : ℝ) + 1) * θ) / ((n : ℝ) + 1) ^ 2 := by
  rw [show ((n : ℂ) + 1) ^ 2 = ((((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) from by push_cast; ring,
    Complex.div_ofReal_im,
    show (Complex.exp ((θ : ℂ) * I)) ^ (n + 1)
        = Complex.exp ((Complex.ofReal (((n : ℝ) + 1) * θ)) * I) from by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring,
    Complex.exp_ofReal_mul_I_im]

/-- The real part on the unit circle equals the Clock paper's `zetaStateRe`. -/
theorem Li₂c_exp_re_eq (θ : ℝ) : (Li₂c (Complex.exp ((θ : ℂ) * I))).re = zetaStateRe θ := by
  rw [Li₂c, re_tsum (summable_Li₂c (norm_exp_mul_I_le θ)), zetaStateRe]
  exact tsum_congr (Li₂c_term_re θ)

/-- The imaginary part on the unit circle equals `Cl₂` (O'Sullivan (2.9)). -/
theorem Li₂c_exp_im (θ : ℝ) : (Li₂c (Complex.exp ((θ : ℂ) * I))).im = Cl₂ θ := by
  rw [Li₂c, im_tsum (summable_Li₂c (norm_exp_mul_I_le θ)), Cl₂]
  exact tsum_congr fun n => Li₂c_term_im θ n

/-- The Bernoulli parabola, for the `(n+1)`-indexed sum (general `θ`); generalizes the
Clock paper's `zetaStateRe_pi` to all `θ ∈ [0, 2π]`. -/
theorem zetaStateRe_eq {θ : ℝ} (h0 : 0 ≤ θ) (h2π : θ ≤ 2 * π) :
    zetaStateRe θ = π ^ 2 / 6 - π * θ / 2 + θ ^ 2 / 4 := by
  have h := hasSum_cos_div_sq h0 h2π
  have hzero : ∑ i ∈ Finset.range 1, Real.cos ((i : ℝ) * θ) / (i : ℝ) ^ 2 = 0 := by simp
  have h' : HasSum (fun n : ℕ => Real.cos ((n : ℝ) * θ) / (n : ℝ) ^ 2)
      ((π ^ 2 / 6 - π * θ / 2 + θ ^ 2 / 4)
        + ∑ i ∈ Finset.range 1, Real.cos ((i : ℝ) * θ) / (i : ℝ) ^ 2) := by
    rw [hzero, add_zero]; exact h
  have hsh := (hasSum_nat_add_iff
    (f := fun n : ℕ => Real.cos ((n : ℝ) * θ) / (n : ℝ) ^ 2) 1).mpr h'
  rw [zetaStateRe, ← hsh.tsum_eq]
  refine tsum_congr fun n => ?_
  push_cast; ring_nf

/-- Real part on the unit circle: the Bernoulli parabola (O'Sullivan (2.8)). -/
theorem Li₂c_exp_re {θ : ℝ} (h0 : 0 ≤ θ) (h2π : θ ≤ 2 * π) :
    (Li₂c (Complex.exp ((θ : ℂ) * I))).re = π ^ 2 / 6 - π * θ / 2 + θ ^ 2 / 4 := by
  rw [Li₂c_exp_re_eq, zetaStateRe_eq h0 h2π]

/-- **No zero on the unit circle** for `θ ∈ (0, 2π)` (principal branch). Direct from the
Clock paper's `zetaState_never_orthogonal` via the boundary decomposition. -/
theorem Li₂c_exp_ne_zero {θ : ℝ} (h0 : 0 < θ) (h2π : θ < 2 * π) :
    Li₂c (Complex.exp ((θ : ℂ) * I)) ≠ 0 := by
  intro h
  refine zetaState_never_orthogonal h0 h2π ⟨?_, ?_⟩
  · rw [← Li₂c_exp_re_eq, h, Complex.zero_re]
  · rw [← Li₂c_exp_im, h, Complex.zero_im]

end Dilog
