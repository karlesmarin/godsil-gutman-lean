/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib
import Dilog.Basic
import Dilog.FejerJackson

/-!
# The Clausen function `Cl₂` and Catalan's constant

The **Clausen function** `Cl₂(θ) = ∑_{n≥1} sin(nθ)/n²` is the imaginary part of the
dilogarithm on the unit circle, `Cl₂(θ) = Im Li₂(e^{iθ})`; equivalently
`Cl₂(θ) = −∫₀^θ log|2 sin(t/2)| dt` (Clausen, 1832). It is the crossroads where four of
our threads meet: boundary values of the complex dilogarithm; exact orthogonality
analysis of "zeta states" in quantum speed limits (the weight-2 autocorrelation
`S(t) = Li₂(e^{−it})/ζ(2)` has `Im S ∝ −Cl₂`); the dimer/lattice constant
`Cl₂(π/2) = G` (Catalan); and Fejér–Jackson-type positive trigonometric sums.

The companion real part is elementary — the **Bernoulli parabola**
`∑ cos(nθ)/n² = π²/6 − πθ/2 + θ²/4` on `[0, 2π]` — which we derive here from Mathlib's
Fourier expansion of Bernoulli polynomials (`hasSum_one_div_nat_pow_mul_cos`). The sine
series at even weight is *not* elementary: that is precisely why `Cl₂` is a genuinely
new special function, and why **Catalan's constant** `G = Cl₂(π/2) = ∑ (−1)^k/(2k+1)²`
(whose irrationality is a famous open problem) is defined here as well — a literature
check (2026-06) found neither the Clausen function nor Catalan's constant formalized in
any proof assistant.

## Main definitions
* `Dilog.Cl₂` : the Clausen function via its absolutely convergent series.
* `Dilog.catalanConst` : Catalan's constant `G = ∑ (−1)^k/(2k+1)²`.

## Main results
* `Dilog.Cl₂_zero`, `Dilog.Cl₂_pi` : `Cl₂(0) = Cl₂(π) = 0`.
* `Dilog.Cl₂_neg` : `Cl₂` is odd.
* `Dilog.Cl₂_pi_div_two` : `Cl₂(π/2) = G`.
* `Dilog.hasSum_cos_div_sq` : the Bernoulli parabola (= `Re Li₂` on the circle).

## Roadmap (later)
* Fejér–Jackson positivity `∑_{k≤N} sin(kθ)/k > 0` on `(0,π)` → `Cl₂ > 0` on `(0,π)`
  (by Abel summation), hence: weight-2 zeta states never reach an orthogonal state.
* `Cl₂'(θ) = −log(2 sin(θ/2))` and the duplication `Cl₂(2θ) = 2Cl₂(θ) − 2Cl₂(π−θ)`.
* The dimer entropy and hyperbolic volume connections.
-/

noncomputable section
open scoped Real
open Set

namespace Dilog

/-- The **Clausen function** `Cl₂(θ) = ∑_{n≥1} sin(nθ)/n²`, the imaginary part of the
dilogarithm on the unit circle. -/
def Cl₂ (θ : ℝ) : ℝ := ∑' n : ℕ, Real.sin ((n + 1) * θ) / ((n : ℝ) + 1) ^ 2

/-- The Clausen series converges absolutely (dominated by `∑ 1/(n+1)²`). -/
theorem summable_Cl₂ (θ : ℝ) :
    Summable fun n : ℕ => Real.sin ((n + 1) * θ) / ((n : ℝ) + 1) ^ 2 := by
  rw [← summable_abs_iff]
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    summable_one_div_add_one_sq
  have hden : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hden]
  gcongr
  · exact Real.abs_sin_le_one _

@[simp] theorem Cl₂_zero : Cl₂ 0 = 0 := by
  simp [Cl₂]

/-- `Cl₂(π) = 0` — every term `sin((n+1)π)` vanishes. -/
@[simp] theorem Cl₂_pi : Cl₂ π = 0 := by
  have h : ∀ n : ℕ, Real.sin ((n + 1) * π) / ((n : ℝ) + 1) ^ 2 = 0 := by
    intro n
    have hs : Real.sin (((n + 1 : ℕ) : ℝ) * π) = 0 := Real.sin_nat_mul_pi (n + 1)
    rw [show ((n : ℝ) + 1) * π = ((n + 1 : ℕ) : ℝ) * π by push_cast; ring] at *
    rw [hs, zero_div]
  simp only [Cl₂]
  rw [tsum_congr h]
  exact tsum_zero

/-- `Cl₂` is an odd function. -/
theorem Cl₂_neg (θ : ℝ) : Cl₂ (-θ) = -Cl₂ θ := by
  simp only [Cl₂]
  rw [← tsum_neg]
  exact tsum_congr fun n => by rw [mul_neg, Real.sin_neg, neg_div]

/-- **Catalan's constant** `G = ∑_{k≥0} (−1)^k/(2k+1)² = 0.9159…` — the value of the
Dirichlet beta function at `2`. Its irrationality is a famous open problem. -/
def catalanConst : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2

/-- The defining series of Catalan's constant converges absolutely. -/
theorem summable_catalanConst :
    Summable fun k : ℕ => (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2 := by
  rw [← summable_abs_iff]
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    summable_one_div_add_one_sq
  have hden : (0 : ℝ) < (2 * (n : ℝ) + 1) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hden, abs_pow, abs_neg, abs_one, one_pow]
  have h1 : ((n : ℝ) + 1) ^ 2 ≤ (2 * (n : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have h2 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
  exact one_div_le_one_div_of_le h2 h1

/-- **`Cl₂(π/2) = G`** — Catalan's constant is the Clausen function at the quarter
circle. (Even-indexed sines vanish, odd-indexed give the alternating series.) -/
theorem Cl₂_pi_div_two : Cl₂ (π / 2) = catalanConst := by
  set f : ℕ → ℝ := fun n => Real.sin ((n + 1) * (π / 2)) / ((n : ℝ) + 1) ^ 2 with hf
  -- odd-indexed terms vanish: `sin((2k+2)·π/2) = sin((k+1)π) = 0`
  have hodd : ∀ k : ℕ, f (2 * k + 1) = 0 := by
    intro k
    have harg : ((2 * k + 1 : ℕ) + 1 : ℝ) * (π / 2) = ((k + 1 : ℕ) : ℝ) * π := by
      push_cast; ring
    rw [hf]
    simp only
    rw [show (((2 * k + 1 : ℕ) : ℝ) + 1) * (π / 2) = ((k + 1 : ℕ) : ℝ) * π by push_cast; ring,
      Real.sin_nat_mul_pi, zero_div]
  -- even-indexed terms: `sin((2k+1)·π/2) = cos(kπ) = (−1)^k`
  have heven : ∀ k : ℕ, f (2 * k) = (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2 := by
    intro k
    have hsin : Real.sin ((2 * (k : ℝ) + 1) * (π / 2)) = (-1 : ℝ) ^ k := by
      rw [show (2 * (k : ℝ) + 1) * (π / 2) = (k : ℝ) * π + π / 2 by ring,
        Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
    rw [hf]
    simp only
    rw [show ((2 * k : ℕ) : ℝ) + 1 = 2 * (k : ℝ) + 1 by push_cast; ring, hsin]
  have hse : Summable fun k : ℕ => f (2 * k) := by
    rw [funext heven]
    exact summable_catalanConst
  have hso : Summable fun k : ℕ => f (2 * k + 1) := by
    rw [funext hodd]
    exact summable_zero
  have hsplit := tsum_even_add_odd hse hso
  have h1 : ∑' k : ℕ, f (2 * k) = catalanConst := by
    rw [funext heven]
    rfl
  have h2 : ∑' k : ℕ, f (2 * k + 1) = 0 := by
    rw [funext hodd]
    exact tsum_zero
  rw [Cl₂, ← hsplit, h1, h2, add_zero]

/-- **The Bernoulli parabola**: for `θ ∈ [0, 2π]`,
`∑_{n≥1} cos(nθ)/n² = π²/6 − πθ/2 + θ²/4` — the real part of `Li₂` on the unit circle
(the weight-2 Fourier expansion of the Bernoulli polynomial `B₂`). Note the `n = 0`
term of the ℕ-indexed sum is `0` by the `1/0 = 0` convention. -/
theorem hasSum_cos_div_sq {θ : ℝ} (h0 : 0 ≤ θ) (h2π : θ ≤ 2 * π) :
    HasSum (fun n : ℕ => Real.cos (n * θ) / (n : ℝ) ^ 2)
      (π ^ 2 / 6 - π * θ / 2 + θ ^ 2 / 4) := by
  have hπ := Real.pi_pos
  have hx : θ / (2 * π) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      linarith
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  have hfun : (fun n : ℕ => 1 / (n : ℝ) ^ (2 * 1) * Real.cos (2 * π * n * (θ / (2 * π))))
      = fun n : ℕ => Real.cos (n * θ) / (n : ℝ) ^ 2 := by
    funext n
    rw [show 2 * π * (n : ℝ) * (θ / (2 * π)) = (n : ℝ) * θ by field_simp]
    rw [pow_mul, pow_one]
    ring
  rw [hfun] at h
  convert h using 1
  -- evaluate the Bernoulli polynomial `B₂(x) = x² − x + 1/6` at `x = θ/(2π)`
  have hB : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2)).eval (θ / (2 * π))
      = (θ / (2 * π)) ^ 2 - θ / (2 * π) + 1 / 6 := by
    have hpoly : Polynomial.bernoulli 2
        = Polynomial.monomial 2 (1 : ℚ) + Polynomial.monomial 1 (-1)
          + Polynomial.monomial 0 (1 / 6) := by
      rw [Polynomial.bernoulli]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [bernoulli_zero, bernoulli_one, bernoulli_two]
    rw [hpoly]
    simp only [Polynomial.map_add, Polynomial.map_monomial, map_one, map_neg, map_div₀,
      map_ofNat, Polynomial.eval_add, Polynomial.eval_monomial]
    norm_num
    ring
  rw [hB]
  have hne : (2 * π : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-! ### Positivity of `Cl₂` on `(0, π)`

Abel rearrangement of the partial sums of the `Cl₂` series in terms of the
Fejér–Jackson sums, then `fejerSum_pos` makes every piece positive. The arrangement is
asymptotics-free: every partial sum is at least `sin θ / 2`. -/

/-- Abel summation identity: the `(N+1)`-term partial sum of the `Cl₂` series equals
`S_{N+1}/(N+1) + ∑_{k<N} S_{k+1}·(1/(k+1) − 1/(k+2))` in terms of the Fejér–Jackson
sums `S_M = fejerSum M`. -/
private lemma cl2_partial_abel (θ : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), Real.sin (((k : ℝ) + 1) * θ) / ((k : ℝ) + 1) ^ 2
      = fejerSum (N + 1) θ / ((N : ℝ) + 1)
        + ∑ k ∈ Finset.range N,
            fejerSum (k + 1) θ * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
  induction N with
  | zero =>
    simp [fejerSum]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hsplit : fejerSum (M + 2) θ
        = fejerSum (M + 1) θ + Real.sin (((M : ℝ) + 2) * θ) / ((M : ℝ) + 2) := by
      unfold fejerSum
      rw [Finset.sum_range_succ,
        show (((M + 1 : ℕ) : ℝ) + 1) = (M : ℝ) + 2 by push_cast; ring]
    have hc1 : (((M + 1 : ℕ) : ℝ) + 1) = (M : ℝ) + 2 := by push_cast; ring
    rw [hc1, hsplit]
    have h1 : ((M : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((M : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring

/-- **Positivity of the Clausen function** on `(0, π)`: `0 < Cl₂ θ` — in fact
`Cl₂ θ ≥ sin θ / 2`. Via Fejér–Jackson positivity and Abel summation; this is the
analytic heart of "weight-2 zeta states never reach an orthogonal state". -/
theorem Cl₂_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) : 0 < Cl₂ θ := by
  have hsin := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  -- every (N+1)-term partial sum is at least `sin θ / 2`
  have hpartial : ∀ N : ℕ,
      Real.sin θ / 2 ≤ ∑ k ∈ Finset.range (N + 1),
        Real.sin (((k : ℝ) + 1) * θ) / ((k : ℝ) + 1) ^ 2 := by
    intro N
    rw [cl2_partial_abel θ N]
    have hS : 0 < fejerSum (N + 1) θ / ((N : ℝ) + 1) := by
      have := fejerSum_pos (N + 1) (by omega) h0 hπ
      positivity
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      have h1 : fejerSum 1 θ = Real.sin θ := by
        simp [fejerSum]
      simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.cast_zero, zero_add]
      rw [h1] at hS ⊢
      linarith [hS]
    · -- the `k = 0` summand alone is `S₁·(1 − 1/2) = sin θ / 2`
      have h1 : fejerSum 1 θ * (1 / ((0 : ℕ) + 1 : ℝ) - 1 / ((0 : ℕ) + 2 : ℝ))
          = Real.sin θ / 2 := by
        simp [fejerSum]
        ring
      have hterms : ∀ k ∈ Finset.range N,
          0 ≤ fejerSum (k + 1) θ * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
        intro k _
        apply mul_nonneg (fejerSum_pos (k + 1) (by omega) h0 hπ).le
        have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hb : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        rw [sub_nonneg]
        apply one_div_le_one_div_of_le ha
        linarith
      have hsum_ge : Real.sin θ / 2
          ≤ ∑ k ∈ Finset.range N,
              fejerSum (k + 1) θ * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
        calc Real.sin θ / 2
            = fejerSum (0 + 1) θ * (1 / ((0 : ℕ) + 1 : ℝ) - 1 / ((0 : ℕ) + 2 : ℝ)) := by
              rw [← h1]
          _ ≤ _ := by
              apply Finset.single_le_sum hterms
              exact Finset.mem_range.mpr h
      linarith
  -- pass to the limit of partial sums
  have htend := ((summable_Cl₂ θ).hasSum).tendsto_sum_nat
  have hge : Real.sin θ / 2 ≤ Cl₂ θ := by
    apply ge_of_tendsto htend
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [add_comm 1 M]
    exact hpartial M
  linarith

end Dilog
