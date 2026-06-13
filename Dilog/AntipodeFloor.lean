/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib

/-!
# The antipode floor for finite completely monotone states

A finite *completely monotone* state has populations `pₙ = ∑ⱼ wⱼ xⱼⁿ` with weights
`wⱼ ≥ 0` on bases `xⱼ ∈ [0,1)` — equivalently, its autocorrelation generating function is
the resolvent sum

  `Φ(z) = ∑ⱼ wⱼ xⱼ / (1 − xⱼ z)`   (`= ∑ₙ pₙ zⁿ⁻¹`).

On the unit circle the modulus of `Φ` is **bounded below by its value at the antipode**
`z = −1`:

  `‖Φ(z)‖ ≥ ∑ⱼ wⱼ xⱼ / (1 + xⱼ) = Φ(−1)`,   for `‖z‖ = 1`.

Since the full autocorrelation `W(z) = z·Φ(z)` has `‖W‖ = ‖Φ‖` on the circle, this says a
finite completely monotone quantum clock **never reaches an orthogonal state** — its
autocorrelation never drops below the floor, the *Euler-factor* value attained only at the
antipode. This is the coefficient-side companion, for the whole completely monotone family,
of the Clock paper's `zetaState_never_orthogonal` (the `s = 2` zeta state).

The mechanism is one clean per-mode inequality: for `x ∈ [0,1)` and `‖z‖ = 1`,

  `Re ( 1 / (1 − x z) ) = (1 − x·Re z) / ‖1 − x z‖²  ≥  1 / (1 + x)`,

because the difference is `x(1 + Re z)(1 − x) / ((1+x)‖1−xz‖²) ≥ 0`
(`Re z ≥ −1` on the circle). Summing with the weights and using `Re ≤ ‖·‖` closes it.

## Main result

* `Dilog.antipode_floor`

A literature check (2026-06) did not find this minimum-modulus statement named; the
ingredients (Herglotz positive real part + per-mode monotonicity) are classical, so it is
most plausibly folklore — recorded here as the first machine-checked form, companion to the
Eneström–Kakeya boundary theorem in `Dilog/Enestrom.lean`.
-/

open Finset Complex
open scoped BigOperators

namespace Dilog

/-- **The antipode floor for finite completely monotone states.** For nonnegative weights
`w` on bases `x ∈ [0,1)`, the resolvent generating function `∑ⱼ wⱼ xⱼ/(1 − xⱼ z)` has, on
the unit circle, modulus at least its antipodal value `∑ⱼ wⱼ xⱼ/(1 + xⱼ)`. -/
theorem antipode_floor {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ∑ i ∈ s, w i * x i / (1 + x i)
      ≤ ‖∑ i ∈ s, ((w i * x i : ℝ) : ℂ) / (1 - (x i : ℂ) * z)‖ := by
  -- `Re z ∈ [-1, 1]` and `normSq z = 1`.
  have habs : |z.re| ≤ 1 := by have h := Complex.abs_re_le_norm z; rwa [hz] at h
  have hre_lb : -1 ≤ z.re := (abs_le.mp habs).1
  have hnsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  set Φ : ℂ := ∑ i ∈ s, ((w i * x i : ℝ) : ℂ) / (1 - (x i : ℂ) * z) with hΦ
  -- Step A: the floor bounds the real part, mode by mode.
  have hfloor_le_re : ∑ i ∈ s, w i * x i / (1 + x i) ≤ Φ.re := by
    rw [hΦ, Complex.re_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hxi0 := hx0 i hi; have hxi1 := hx1 i hi; have hwi := hw i hi
    have h1px : (0 : ℝ) < 1 + x i := by linarith
    -- denominator is nonzero on the disc `x ∈ [0,1)`, `‖z‖ = 1`.
    have hzne : (1 - (x i : ℂ) * z) ≠ 0 := by
      intro h
      have hxz : (x i : ℂ) * z = 1 := by linear_combination -h
      have hnorm : ‖(x i : ℂ) * z‖ = 1 := by rw [hxz]; simp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxi0, hz, mul_one]
        at hnorm
      linarith
    have hD : (0 : ℝ) < Complex.normSq (1 - (x i : ℂ) * z) := Complex.normSq_pos.mpr hzne
    -- real and imaginary parts of `1 - xᵢ z`.
    have hre1 : (1 - (x i : ℂ) * z).re = 1 - x i * z.re := by
      rw [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul]
    have him1 : (1 - (x i : ℂ) * z).im = -(x i * z.im) := by
      rw [Complex.sub_im, Complex.one_im, Complex.im_ofReal_mul]; ring
    -- the squared modulus, simplified with `normSq z = 1`.
    have hDval : Complex.normSq (1 - (x i : ℂ) * z) = 1 - 2 * x i * z.re + x i ^ 2 := by
      rw [Complex.normSq_apply, hre1, him1]
      have hz1 : z.re * z.re + z.im * z.im = 1 := by rw [← Complex.normSq_apply]; exact hnsq
      linear_combination (x i) ^ 2 * hz1
    -- the real part of the `i`-th mode.
    have hterm : (((w i * x i : ℝ) : ℂ) / (1 - (x i : ℂ) * z)).re
        = w i * x i * (1 - x i * z.re) / Complex.normSq (1 - (x i : ℂ) * z) := by
      rw [div_eq_mul_inv, Complex.re_ofReal_mul, Complex.inv_re, hre1]; ring
    rw [hterm, hDval]
    have hDpos : (0 : ℝ) < 1 - 2 * x i * z.re + x i ^ 2 := by rw [← hDval]; exact hD
    rw [div_le_div_iff₀ h1px hDpos]
    -- `w x · ‖1−xz‖²  ≤  w x (1 − x·Re z) · (1 + x)`, since the gap is
    -- `w x² (1 + Re z)(1 − x) ≥ 0`.
    nlinarith [mul_nonneg (mul_nonneg hwi hxi0)
      (mul_nonneg (mul_nonneg hxi0 (show (0 : ℝ) ≤ 1 + z.re by linarith))
        (show (0 : ℝ) ≤ 1 - x i by linarith))]
  -- Step B: real part bounds modulus.
  exact le_trans hfloor_le_re (by simpa using RCLike.re_le_norm Φ)

end Dilog
