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

/-- The analytic core, complex form: `Li₂c'(z) = -log(1-z)/z` on the punctured open disk.
The complex companion of `Dilog.hasDerivAt_Li₂`, by the same term-by-term differentiation
under a geometric majorant on a ball, then the complex Mercator series. -/
theorem hasDerivAt_Li₂c {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasDerivAt Li₂c (-Complex.log (1 - z) / z) z := by
  set r : ℝ := (‖z‖ + 1) / 2 with hr
  have hzr : ‖z‖ < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 < r := by rw [hr]; positivity
  set t : Set ℂ := Metric.ball 0 r with ht_def
  have hzt : z ∈ t := by
    rw [ht_def, Metric.mem_ball, dist_zero_right]; exact hzr
  set g : ℕ → ℂ → ℂ := fun n w => w ^ (n + 1) / ((n : ℂ) + 1) ^ 2 with hg_def
  set g' : ℕ → ℂ → ℂ := fun n w => w ^ n / ((n : ℂ) + 1) with hg'_def
  have hne : ∀ n : ℕ, ((n : ℂ) + 1) ≠ 0 := fun n => Nat.cast_add_one_ne_zero n
  have hg : ∀ n w, w ∈ t → HasDerivAt (g n) (g' n w) w := by
    intro n w _
    have h1 : HasDerivAt (fun u : ℂ => u ^ (n + 1)) (((n : ℂ) + 1) * w ^ n) w := by
      simpa [Nat.cast_add, Nat.cast_one] using hasDerivAt_pow (n + 1) w
    have h2 := h1.div_const (((n : ℂ) + 1) ^ 2)
    convert h2 using 1
    rw [hg'_def, pow_two, mul_div_mul_left _ _ (hne n)]
  have hg' : ∀ n w, w ∈ t → ‖g' n w‖ ≤ r ^ n := by
    intro n w hw
    rw [ht_def, Metric.mem_ball, dist_zero_right] at hw
    rw [hg'_def, norm_div, norm_pow]
    have hd : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
      rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    rw [hd]
    calc ‖w‖ ^ n / ((n : ℝ) + 1) ≤ ‖w‖ ^ n :=
          div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])
      _ ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg w) hw.le n
  have hu : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0.le hr1
  have hg0 : Summable fun n => g n z := summable_Li₂c hz.le
  have key : HasDerivAt (fun w => ∑' n, g n w) (∑' n, g' n z) z :=
    hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball Metric.isPreconnected_ball
      hg hg' hzt hg0 hzt
  -- complex Mercator: `∑ zⁿ⁺¹/(n+1) = -log(1-z)`
  have hlog : ∑' n : ℕ, z ^ (n + 1) / ((n : ℂ) + 1) = -Complex.log (1 - z) := by
    have hz' : ‖(-z)‖ < 1 := by rwa [norm_neg]
    have H := Complex.hasSum_taylorSeries_log hz'
    have hfun : (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * (-z) ^ n / (n : ℂ))
        = fun n : ℕ => -(z ^ n / (n : ℂ)) := by
      funext n
      rw [neg_pow z n, ← mul_assoc, ← pow_add, show n + 1 + n = 2 * n + 1 by ring,
        pow_succ, pow_mul, neg_one_sq, one_pow]
      ring
    rw [hfun, show (1 : ℂ) + -z = 1 - z by ring] at H
    have H2 : HasSum (fun n : ℕ => z ^ n / (n : ℂ)) (-Complex.log (1 - z)) := by
      simpa using H.neg
    have Hshift := (hasSum_nat_add_iff (f := fun n : ℕ => z ^ n / (n : ℂ)) 1).mpr
      (show HasSum (fun n : ℕ => z ^ n / (n : ℂ))
          (-Complex.log (1 - z) + ∑ i ∈ Finset.range 1, z ^ i / (i : ℂ)) by simpa using H2)
    have Htarget : HasSum (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1)) (-Complex.log (1 - z)) := by
      have heq : (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1))
          = fun n : ℕ => z ^ (n + 1) / (((n + 1 : ℕ) : ℂ)) := by
        funext n; push_cast; ring
      rw [heq]; exact Hshift
    exact Htarget.tsum_eq
  have hfactor : ∑' n : ℕ, z ^ (n + 1) / ((n : ℂ) + 1)
      = z * ∑' n : ℕ, z ^ n / ((n : ℂ) + 1) := by
    rw [← tsum_mul_left]; congr 1; ext n; rw [pow_succ]; ring
  have hsum : ∑' n : ℕ, g' n z = -Complex.log (1 - z) / z := by
    rw [hg'_def, eq_div_iff hz0, mul_comm, ← hfactor, hlog]
  rw [hsum] at key
  exact key

/-- **No zero on the unit circle** for `θ ∈ (0, 2π)` (principal branch). Direct from the
Clock paper's `zetaState_never_orthogonal` via the boundary decomposition. -/
theorem Li₂c_exp_ne_zero {θ : ℝ} (h0 : 0 < θ) (h2π : θ < 2 * π) :
    Li₂c (Complex.exp ((θ : ℂ) * I)) ≠ 0 := by
  intro h
  refine zetaState_never_orthogonal h0 h2π ⟨?_, ?_⟩
  · rw [← Li₂c_exp_re_eq, h, Complex.zero_re]
  · rw [← Li₂c_exp_im, h, Complex.zero_im]

/-- The multivalued dilogarithm branch `φ_{A,B}(z) = Li₂(z) + 4π²A + 2πiB·log z`
(O'Sullivan, A,B ∈ ℤ). On the principal branch `A = B = 0`, `φ = Li₂c`. -/
noncomputable def phi (A B : ℤ) (z : ℂ) : ℂ :=
  Li₂c z + 4 * (π : ℂ) ^ 2 * (A : ℂ) + 2 * (π : ℂ) * I * (B : ℂ) * Complex.log z

/-- The derivative of `φ_{A,B}` on the punctured slit disk. -/
theorem hasDerivAt_phi (A B : ℤ) {z : ℂ} (hz : ‖z‖ < 1) (hslit : z ∈ Complex.slitPlane) :
    HasDerivAt (phi A B)
      (-Complex.log (1 - z) / z + 2 * (π : ℂ) * I * (B : ℂ) * z⁻¹) z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Complex.mem_slitPlane_iff] at hslit
  have h1 := hasDerivAt_Li₂c hz hz0
  have hc : HasDerivAt (fun _ : ℂ => 4 * (π : ℂ) ^ 2 * (A : ℂ)) 0 z := hasDerivAt_const z _
  have hlog := (Complex.hasDerivAt_log hslit).const_mul (2 * (π : ℂ) * I * (B : ℂ))
  have h := (h1.add hc).add hlog
  simpa [phi, add_zero] using h

/-- **O'Sullivan (2.1)**: `z·φ'_{A,B}(z) = -log(1-z) + 2πiB` on the punctured slit disk. -/
theorem z_mul_deriv_phi (B : ℤ) {z : ℂ} (hslit : z ∈ Complex.slitPlane) :
    z * (-Complex.log (1 - z) / z + 2 * (π : ℂ) * I * (B : ℂ) * z⁻¹)
      = -Complex.log (1 - z) + 2 * (π : ℂ) * I * (B : ℂ) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Complex.mem_slitPlane_iff] at hslit
  field_simp

/-- `Li₂c` is continuous on the closed unit disk (Weierstrass M-test). -/
theorem continuousOn_Li₂c : ContinuousOn Li₂c (Metric.closedBall 0 1) := by
  refine continuousOn_tsum (fun n => ?_) (summable_pow_div_add (1 : ℂ) 2 1 (by norm_num))
    (fun n z hz => ?_)
  · exact (by fun_prop : Continuous fun z : ℂ => z ^ (n + 1) / ((n : ℂ) + 1) ^ 2).continuousOn
  · rw [Metric.mem_closedBall, dist_zero_right] at hz
    simp only [Nat.cast_one]
    rw [norm_div, norm_div, norm_one, norm_pow]
    gcongr
    exact (pow_le_pow_left₀ (norm_nonneg z) hz (n + 1)).trans_eq (one_pow _)

/-! ## Phase 3: sign localization of the imaginary-part zero curve (O'Sullivan §5)

For `B ≥ 1`, the zero `w(A,B)` of `φ_{A,B}` lies on the curve `Im φ_{A,B} = 0`.
Along the ray `z = r·e^{iθ}` this imaginary part is
`I_θ(r) = Im Li₂(r e^{iθ}) + 2πB·log r` (O'Sullivan (5.2), since `Re log z = log r`).
At the unit circle `r = 1` it reduces to `Cl₂(θ)`; its sign (via our `Cl₂_pos`)
decides whether the zero sits inside (`Cl₂ > 0`) or outside the disk — the seed of
O'Sullivan's Proposition 5.3. -/

/-- The imaginary part of `φ_{0,B}` along the ray `r·e^{iθ}` (O'Sullivan (5.2)). -/
noncomputable def Iθ (B : ℤ) (θ r : ℝ) : ℝ :=
  (Li₂c ((r : ℂ) * Complex.exp ((θ : ℂ) * I))).im + 2 * π * (B : ℝ) * Real.log r

/-- **O'Sullivan §5, the key identity**: at the unit circle `I_θ(1) = Cl₂(θ)`. -/
theorem Iθ_one (B : ℤ) (θ : ℝ) : Iθ B θ 1 = Cl₂ θ := by
  simp only [Iθ, Real.log_one, mul_zero, add_zero, Complex.ofReal_one, one_mul]
  exact Li₂c_exp_im θ

/-- On the arc `θ ∈ (0,π)` the imaginary-part function is positive at the unit circle —
the sign that localizes the zero inside the disk (O'Sullivan Prop. 5.3). -/
theorem Iθ_one_pos (B : ℤ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) : 0 < Iθ B θ 1 := by
  rw [Iθ_one]; exact Cl₂_pos h0 hπ

end Dilog
