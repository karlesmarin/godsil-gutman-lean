/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib
import QSL.Basic

/-!
# A Mandelstam–Tamm-type speed limit (L¹ form)

The classical Mandelstam–Tamm bound (1945) reads `τ ≥ π/(2·ΔE)` where
`ΔE = (∑ pₙ(Eₙ−⟨E⟩)²)^(1/2)` is the energy standard deviation. This file proves the
**L¹ (mean-absolute-deviation) variant**, `ℏ = 1`:

  `τ ≥ 1 / D₁`,   `D₁ = ∑ pₙ·|Eₙ − ⟨E⟩|`,

by the phase-shift + mean-value argument: the centered autocorrelation
`g(t) = e^{i⟨E⟩t}·S(t) = ∑ pₙ·e^{−i(Eₙ−⟨E⟩)t}` travels from `g(0) = 1` to `g(τ) = 0`
with speed `‖g'‖ ≤ D₁` everywhere, so `1 ≤ D₁·τ`.

Since `D₁ ≤ ΔE` (Cauchy–Schwarz), this implies the textbook *weak* form `τ ≥ 1/ΔE`.
Note the comparison with the sharp constant: for heavy-tailed energy distributions
`D₁ ≪ ΔE`, and then `1/D₁` can exceed the sharp Mandelstam–Tamm bound `π/(2ΔE)` — the
two bounds are incomparable in general.

## Main result
* `QSL.mandelstam_tamm_L1` : `1 ≤ D₁·τ` for any orthogonalization time `τ ≥ 0`.

## Roadmap
* The sharp `τ ≥ π/(2·ΔE)` (geodesic/arccos comparison argument).
* The `ΔE` corollary via Cauchy–Schwarz on the spectral measure.
-/

noncomputable section
open scoped Real
open Set

namespace QSL

/-- **Mandelstam–Tamm-type speed limit, L¹ form** (`ℏ = 1`): if a normalized population
distribution `p` over energies `E` has mean absolute energy deviation
`D₁ = ∑ pₙ·|Eₙ − Ebar|` around any reference energy `Ebar`, and the autocorrelation
`S(τ) = ∑ pₙ·e^{−i·Eₙ·τ}` vanishes at some `τ ≥ 0`, then `1 ≤ D₁·τ`, i.e.
`τ ≥ 1/D₁`. With `Ebar = ⟨E⟩` and Cauchy–Schwarz this implies the textbook weak
Mandelstam–Tamm bound `τ ≥ 1/ΔE`. -/
theorem mandelstam_tamm_L1 {p E : ℕ → ℝ} {Ebar D1 τ : ℝ}
    (hp : ∀ n, 0 ≤ p n) (hτ : 0 ≤ τ)
    (hsum : HasSum p 1)
    (hdev : HasSum (fun n => p n * |E n - Ebar|) D1)
    (horth : HasSum
      (fun n => (p n : ℂ) * Complex.exp ((-(E n * τ) : ℝ) * Complex.I)) 0) :
    1 ≤ D1 * τ := by
  set d : ℕ → ℂ := fun n => -((E n - Ebar : ℝ) : ℂ) * Complex.I with hd
  set f : ℕ → ℝ → ℂ := fun n t => (p n : ℂ) * Complex.exp (d n * (t : ℂ)) with hf
  set f' : ℕ → ℝ → ℂ := fun n t => (p n : ℂ) * (Complex.exp (d n * (t : ℂ)) * d n) with hf'
  set u : ℕ → ℝ := fun n => p n * |E n - Ebar| with hu_def
  -- termwise derivative
  have hderiv : ∀ (n : ℕ) (t : ℝ), HasDerivAt (f n) (f' n t) t := by
    intro n t
    have h1 : HasDerivAt (fun s : ℝ => d n * (s : ℂ)) (d n) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (d n)
    exact h1.cexp.const_mul _
  -- the exponential has unit norm (purely imaginary exponent)
  have hexp_norm : ∀ (n : ℕ) (t : ℝ), ‖Complex.exp (d n * (t : ℂ))‖ = 1 := by
    intro n t
    have harg : d n * (t : ℂ) = ((-(E n - Ebar) * t : ℝ) : ℂ) * Complex.I := by
      rw [hd]; push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  -- norm of the term derivatives
  have hnorm : ∀ (n : ℕ) (t : ℝ), ‖f' n t‖ = u n := by
    intro n t
    rw [hf', hu_def]
    simp only
    rw [norm_mul, norm_mul, hexp_norm, one_mul, hd]
    simp only [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hp n)]
  have hu_sum : Summable u := hdev.summable
  have hf0 : Summable fun n => f n 0 := by
    have hfun : (fun n => f n 0) = fun n => (p n : ℂ) := by
      funext n
      rw [hf]
      simp
    rw [hfun]
    exact (Complex.hasSum_ofReal.mpr hsum).summable
  -- derivative of the summed centered autocorrelation
  have hg_deriv : ∀ t : ℝ, HasDerivAt (fun y : ℝ => ∑' n, f n y) (∑' n, f' n t) t := by
    intro t
    exact hasDerivAt_tsum_of_isPreconnected hu_sum isOpen_univ isPreconnected_univ
      (fun n x _ => hderiv n x) (fun n x _ => le_of_eq (hnorm n x)) (mem_univ (0 : ℝ))
      hf0 (mem_univ t)
  -- the speed bound `‖g'‖ ≤ D₁`
  have hgbound : ∀ t : ℝ, ‖∑' n, f' n t‖ ≤ D1 := by
    intro t
    have hfun : (fun n => ‖f' n t‖) = u := funext fun n => hnorm n t
    have hsn : Summable fun n => ‖f' n t‖ := by rw [hfun]; exact hu_sum
    calc ‖∑' n, f' n t‖ ≤ ∑' n, ‖f' n t‖ := norm_tsum_le_tsum_norm hsn
      _ = ∑' n, u n := tsum_congr fun n => hnorm n t
      _ = D1 := hdev.tsum_eq
  -- endpoint values
  have hG0 : (∑' n, f n 0) = 1 := by
    have hfun : (fun n => f n 0) = fun n => (p n : ℂ) := by
      funext n
      rw [hf]
      simp
    rw [hfun, (Complex.hasSum_ofReal.mpr hsum).tsum_eq]
    norm_num
  have hGτ : (∑' n, f n τ) = 0 := by
    set c : ℂ := Complex.exp ((Ebar * τ : ℝ) * Complex.I) with hc
    have h := horth.mul_left c
    have hfun : (fun n => c * ((p n : ℂ) * Complex.exp ((-(E n * τ) : ℝ) * Complex.I)))
        = fun n => f n τ := by
      funext n
      simp only [hf, hc]
      have harg : d n * (τ : ℂ)
          = ((-(E n * τ) : ℝ) : ℂ) * Complex.I + ((Ebar * τ : ℝ) : ℂ) * Complex.I := by
        rw [hd]; push_cast; ring
      rw [harg, Complex.exp_add]
      ring
    rw [hfun] at h
    rw [h.tsum_eq]
    simp
  -- mean value inequality on `[0, τ]`
  have hineq := (convex_Icc (0 : ℝ) τ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => ∑' n, f n t) (f' := fun t => ∑' n, f' n t)
    (fun x _ => (hg_deriv x).hasDerivWithinAt)
    (fun x _ => hgbound x) (left_mem_Icc.mpr hτ) (right_mem_Icc.mpr hτ)
  have hfinal : (1 : ℝ) ≤ D1 * |τ| := by
    have h1 : ‖(0 : ℂ) - 1‖ ≤ D1 * ‖τ - (0 : ℝ)‖ := by
      simpa [hG0, hGτ] using hineq
    simpa using h1
  rwa [abs_of_nonneg hτ] at hfinal

end QSL
