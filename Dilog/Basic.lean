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
* `Dilog.continuousOn_Li₂` : `Li₂` is continuous on `[-1, 1]` (Weierstrass M-test).
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
open scoped Real BigOperators Topology
open Set Filter

namespace Dilog

/-- The real **dilogarithm** `Li₂ z = ∑_{n ≥ 1} zⁿ / n² = ∑_{n ≥ 0} z^{n+1} / (n+1)²`. -/
noncomputable def Li₂ (z : ℝ) : ℝ := ∑' n : ℕ, z ^ (n + 1) / ((n : ℝ) + 1) ^ 2

/-- The dominating series `∑ 1/(n+1)²` converges (shift of the `p = 2` series). -/
theorem summable_one_div_add_one_sq : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
  have h2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h2
  simpa [Nat.cast_add, Nat.cast_one] using hs

/-- The defining series of `Li₂` is summable on the closed unit interval `|z| ≤ 1`
(majorised termwise by the convergent `∑ 1/(n+1)²`). -/
theorem summable_Li₂ {z : ℝ} (hz : |z| ≤ 1) :
    Summable fun n : ℕ => z ^ (n + 1) / ((n : ℝ) + 1) ^ 2 := by
  -- Absolute comparison with the convergent `∑ 1/(n+1)²`.
  rw [← summable_abs_iff]
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    summable_one_div_add_one_sq
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

/-- Termwise differentiation of the dilogarithm series gives, on `(-1,1) \ {0}`,
`Li₂'(x) = -log(1 - x)/x` (note `∑_{n≥1} xⁿ⁻¹ = 1/(1-x)` and `∑ xⁿ/n = -log(1-x)`).
At `x = 0` the derivative is `1`, but the quotient form requires `x ≠ 0`. -/
theorem hasDerivAt_Li₂ {x : ℝ} (habs : |x| < 1) (hx0 : x ≠ 0) :
    HasDerivAt Li₂ (-Real.log (1 - x) / x) x := by
  set r : ℝ := (|x| + 1) / 2 with hr
  have hxr : |x| < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 < r := by rw [hr]; positivity
  -- the open neighbourhood `t = (-r, r) ⊂ (-1,1)` on which the derivative series is dominated by `rⁿ`
  set t : Set ℝ := Ioo (-r) r with ht_def
  have hxt : x ∈ t := by
    have h := abs_lt.mp hxr
    exact ⟨h.1, h.2⟩
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
  have hg0 : Summable fun n => g n x := summable_Li₂ habs.le
  -- term-by-term differentiation
  have key : HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n x) x :=
    hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg' hxt hg0 hxt
  -- identify the derivative series with `-log(1-x)/x` (Mercator series)
  have hlog : ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) = -Real.log (1 - x) := by
    have := (Real.hasSum_pow_div_log_of_abs_lt_one habs).tsum_eq
    simpa using this
  have hfactor : ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) = x * ∑' n : ℕ, x ^ n / ((n : ℝ) + 1) := by
    rw [← tsum_mul_left]; congr 1; ext n; rw [pow_succ]; ring
  have hsum : ∑' n : ℕ, g' n x = -Real.log (1 - x) / x := by
    rw [hg'_def]
    rw [eq_div_iff hx0, mul_comm, ← hfactor, hlog]
  rw [hsum] at key
  exact key

/-- `Li₂` is continuous on `[-1, 1]` (Weierstrass M-test: the series is dominated by
`∑ 1/(n+1)²` uniformly on the closed interval). -/
theorem continuousOn_Li₂ : ContinuousOn Li₂ (Icc (-1 : ℝ) 1) := by
  have : ContinuousOn (fun z : ℝ => ∑' n : ℕ, z ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
      (Icc (-1 : ℝ) 1) := by
    refine continuousOn_tsum (fun i => ((continuous_pow (i + 1)).div_const _).continuousOn)
      summable_one_div_add_one_sq (fun n z hz => ?_)
    have hz1 : |z| ≤ 1 := abs_le.mpr ⟨hz.1, hz.2⟩
    have hden : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hden]
    gcongr
    exact pow_le_one₀ (abs_nonneg z) hz1
  exact this

/-- **Euler's reflection identity** for the dilogarithm on `(0,1)`:
`Li₂ x + Li₂ (1 - x) = π²/6 - log x · log (1 - x)`.

Proof: let `F y := Li₂ y + Li₂ (1 - y) + log y · log (1 - y)`. Using `hasDerivAt_Li₂`
(and `(Li₂ (1-·))' = log y/(1-y)` by the chain rule), `F' = 0` on `(0,1)`, so `F` is constant
there (`constant_of_has_deriv_right_zero` on subintervals). Its limit as `y → 0⁺` is
`Li₂ 0 + Li₂ 1 + 0 = π²/6` by continuity of `Li₂` on `[-1,1]` and
`log y · log(1-y) = (log(1-y)/y)·(y·log y) → (-1)·0 = 0`. -/
theorem Li₂_add_Li₂_one_sub {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Li₂ x + Li₂ (1 - x) = π ^ 2 / 6 - Real.log x * Real.log (1 - x) := by
  set F : ℝ → ℝ := fun y => Li₂ y + Li₂ (1 - y) + Real.log y * Real.log (1 - y) with hF
  -- Step 1: `F' = 0` on `(0,1)`.
  have hF' : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt F 0 y := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    have hy1' : (0 : ℝ) < 1 - y := by linarith
    have hinner : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    -- `Li₂ y`
    have h1 : HasDerivAt Li₂ (-Real.log (1 - y) / y) y :=
      hasDerivAt_Li₂ (by rw [abs_of_pos hy0]; exact hy1) (ne_of_gt hy0)
    -- `Li₂ (1 - y)` via the chain rule
    have h2base : HasDerivAt Li₂ (-Real.log (1 - (1 - y)) / (1 - y)) (1 - y) :=
      hasDerivAt_Li₂ (by rw [abs_of_pos hy1']; linarith) (ne_of_gt hy1')
    rw [show (1 : ℝ) - (1 - y) = y by ring] at h2base
    have h2 : HasDerivAt (fun z : ℝ => Li₂ (1 - z)) (Real.log y / (1 - y)) y := by
      have h := h2base.comp y hinner
      convert h using 1
      ring
    -- `log y · log (1 - y)` via the product + chain rules
    have h3a : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log (ne_of_gt hy0)
    have h3b : HasDerivAt (fun z : ℝ => Real.log (1 - z)) ((1 - y)⁻¹ * -1) y :=
      (Real.hasDerivAt_log (ne_of_gt hy1')).comp y hinner
    have h3 := h3a.mul h3b
    -- assemble and simplify the total derivative to `0`
    have htot := (h1.add h2).add h3
    rw [hF]
    convert htot using 1
    field_simp
    ring
  -- Step 2: `F` is constant on `(0,1)` (zero right-derivative on every subinterval).
  have hconst : ∀ y ∈ Ioo (0 : ℝ) 1, ∀ z ∈ Ioo (0 : ℝ) 1, y ≤ z → F z = F y := by
    intro y hy z hz hyz
    have hsub : Icc y z ⊆ Ioo (0 : ℝ) 1 :=
      fun t ht => ⟨lt_of_lt_of_le hy.1 ht.1, lt_of_le_of_lt ht.2 hz.2⟩
    have hcont : ContinuousOn F (Icc y z) :=
      fun t ht => ((hF' t (hsub ht)).continuousAt).continuousWithinAt
    have hderiv : ∀ t ∈ Ico y z, HasDerivWithinAt F 0 (Ici t) t :=
      fun t ht => (hF' t (hsub ⟨ht.1, ht.2.le⟩)).hasDerivWithinAt
    exact constant_of_has_deriv_right_zero hcont hderiv z ⟨hyz, le_refl z⟩
  -- Step 3: boundary limit — `F → π²/6` along `𝓝[>] 0`.
  have hIoo : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
    exact self_mem_nhdsWithin
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo (0 : ℝ) 1 := hIoo
  have hsub01 : Ioo (0 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 :=
    fun t ht => ⟨by linarith [ht.1], ht.2.le⟩
  -- (a) `Li₂ y → Li₂ 0 = 0`
  have hLi2a : Tendsto Li₂ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc (-1 : ℝ) 1] 0 := by
      rw [← nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
      exact nhdsWithin_mono 0 hsub01
    have h := (continuousOn_Li₂.continuousWithinAt (by norm_num)).mono_left hle
    simpa using h
  -- (b) `Li₂ (1 - y) → Li₂ 1`
  have hLi2b : Tendsto (fun y : ℝ => Li₂ (1 - y)) (𝓝[>] (0 : ℝ)) (𝓝 (Li₂ 1)) := by
    have hcw1 : ContinuousWithinAt Li₂ (Icc (-1 : ℝ) 1) 1 :=
      continuousOn_Li₂.continuousWithinAt (by norm_num)
    have hmap : Tendsto (fun y : ℝ => 1 - y) (𝓝[>] (0 : ℝ)) (𝓝[Icc (-1 : ℝ) 1] 1) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h : Tendsto (fun y : ℝ => 1 - y) (𝓝 0) (𝓝 (1 - 0)) :=
          (continuous_const.sub continuous_id).tendsto 0
        simpa using h.mono_left nhdsWithin_le_nhds
      · filter_upwards [hev] with y hy
        exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
    exact hcw1.tendsto.comp hmap
  -- (c) `log y · log (1 - y) → 0`, written as `(log(1-y)/y) · (y·log y)`
  have hT1 : Tendsto (fun y : ℝ => Real.log (1 - y) / y) (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
    have hinner0 : HasDerivAt (fun y : ℝ => 1 - y) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
    have houter : HasDerivAt Real.log ((1 : ℝ))⁻¹ (1 - (0 : ℝ)) := by
      rw [show (1 : ℝ) - 0 = 1 by norm_num]
      exact Real.hasDerivAt_log one_ne_zero
    have hd : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1) 0 := by
      have h := houter.comp (0 : ℝ) hinner0
      simpa using h
    have hslope := hasDerivAt_iff_tendsto_slope.mp hd
    have hmono : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_mono 0 (fun y hy => ne_of_gt hy)
    refine (hslope.mono_left hmono).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y _
    rw [slope_def_field]
    norm_num
  have hT2 : Tendsto (fun y : ℝ => y * Real.log y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := tendsto_log_mul_rpow_nhdsGT_zero (r := (1 : ℝ)) one_pos
    simp only [Real.rpow_one] at h
    exact h.congr fun y => mul_comm _ _
  have hT3 : Tendsto (fun y : ℝ => Real.log y * Real.log (1 - y)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hT1.mul hT2
    rw [show (-1 : ℝ) * 0 = 0 by ring] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    field_simp
  have hlim : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (π ^ 2 / 6)) := by
    rw [hF]
    have h := (hLi2a.add hLi2b).add hT3
    simpa [Li₂_one] using h
  -- Step 4: combine — `F` is eventually the constant `F x`, so `F x = π²/6`.
  have hFeq : ∀ᶠ y in 𝓝[>] (0 : ℝ), F y = F x := by
    filter_upwards [hev] with y hy
    rcases le_total y x with h | h
    · exact (hconst y hy x hx h).symm
    · exact hconst x hx y hy h
  have hclim : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F x)) :=
    Tendsto.congr' (by filter_upwards [hFeq] with y h; exact h.symm) tendsto_const_nhds
  have hFx : F x = π ^ 2 / 6 := tendsto_nhds_unique hclim hlim
  have hFx' : Li₂ x + Li₂ (1 - x) + Real.log x * Real.log (1 - x) = π ^ 2 / 6 := by
    simpa [hF] using hFx
  linarith

/-- **Landen's identity** for the dilogarithm on `(0, 1/2)`:
`Li₂ x + Li₂ (x/(x-1)) = -log²(1-x) / 2`.

For `x ∈ (0, 1/2)` the second argument `x/(x-1) ∈ (-1, 0)` stays inside the disc of
convergence of the defining power series; past `x = 1/2` the identity requires analytic
continuation, which the series definition does not provide.

Proof: same scheme as the reflection identity — the combination
`G y := Li₂ y + Li₂ (y/(y-1)) + log²(1-y)/2` has zero derivative on `(0, 1/2)` and tends
to `0` as `y → 0⁺`. -/
theorem Li₂_landen {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    Li₂ x + Li₂ (x / (x - 1)) = -Real.log (1 - x) ^ 2 / 2 := by
  set G : ℝ → ℝ := fun y => Li₂ y + Li₂ (y / (y - 1)) + Real.log (1 - y) ^ 2 / 2 with hG
  -- Step 1: `G' = 0` on `(0, 1/2)`.
  have hG' : ∀ y ∈ Ioo (0 : ℝ) (1 / 2), HasDerivAt G 0 y := by
    intro y hy
    obtain ⟨hy0, hy2⟩ := hy
    have hy1 : y < 1 := by linarith
    have hy0' : y ≠ 0 := ne_of_gt hy0
    have hy1' : (0 : ℝ) < 1 - y := by linarith
    have h1y' : (1 : ℝ) - y ≠ 0 := ne_of_gt hy1'
    have hym1 : y - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hy1)
    -- the inner map `u = y/(y-1)` and its bounds
    have hu : HasDerivAt (fun z : ℝ => z / (z - 1)) (-1 / (y - 1) ^ 2) y := by
      have h := (hasDerivAt_id y).div ((hasDerivAt_id y).sub_const 1) hym1
      convert h using 1
      simp only [id_eq]
      field_simp
      ring
    have huval : |y / (y - 1)| < 1 := by
      rw [abs_div, abs_of_pos hy0, abs_of_neg (show y - 1 < 0 by linarith),
        div_lt_one (by linarith : (0 : ℝ) < -(y - 1))]
      linarith
    have hune : y / (y - 1) ≠ 0 := div_ne_zero hy0' hym1
    -- `Li₂ y`
    have h1 : HasDerivAt Li₂ (-Real.log (1 - y) / y) y :=
      hasDerivAt_Li₂ (by rw [abs_of_pos hy0]; exact hy1) hy0'
    -- `Li₂ (y/(y-1))` via the chain rule; note `1 - y/(y-1) = (1-y)⁻¹`
    have h2base : HasDerivAt Li₂
        (-Real.log (1 - y / (y - 1)) / (y / (y - 1))) (y / (y - 1)) :=
      hasDerivAt_Li₂ huval hune
    have harg : (1 : ℝ) - y / (y - 1) = (1 - y)⁻¹ := by
      field_simp
      ring
    rw [harg, Real.log_inv] at h2base
    have h2 := h2base.comp y hu
    -- `log²(1-y)/2`
    have hlog' : HasDerivAt (fun z : ℝ => Real.log (1 - z)) ((1 - y)⁻¹ * -1) y :=
      (Real.hasDerivAt_log h1y').comp y (by simpa using (hasDerivAt_id y).const_sub 1)
    have h3 := (hlog'.pow 2).div_const 2
    have htot := (h1.add h2).add h3
    rw [hG]
    convert htot using 1
    field_simp
    ring
  -- Step 2: `G` is constant on `(0, 1/2)`.
  have hconst : ∀ y ∈ Ioo (0 : ℝ) (1 / 2), ∀ z ∈ Ioo (0 : ℝ) (1 / 2), y ≤ z → G z = G y := by
    intro y hy z hz hyz
    have hsub : Icc y z ⊆ Ioo (0 : ℝ) (1 / 2) :=
      fun t ht => ⟨lt_of_lt_of_le hy.1 ht.1, lt_of_le_of_lt ht.2 hz.2⟩
    have hcont : ContinuousOn G (Icc y z) :=
      fun t ht => ((hG' t (hsub ht)).continuousAt).continuousWithinAt
    have hderiv : ∀ t ∈ Ico y z, HasDerivWithinAt G 0 (Ici t) t :=
      fun t ht => (hG' t (hsub ⟨ht.1, ht.2.le⟩)).hasDerivWithinAt
    exact constant_of_has_deriv_right_zero hcont hderiv z ⟨hyz, le_refl z⟩
  -- Step 3: boundary limit — `G → 0` along `𝓝[>] 0`.
  have hIoo : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)]
    exact self_mem_nhdsWithin
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo (0 : ℝ) (1 / 2) := hIoo
  -- (a) `Li₂ y → 0`
  have hLi2a : Tendsto Li₂ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc (-1 : ℝ) 1] 0 := by
      rw [← nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
      exact nhdsWithin_mono 0 (fun t ht => ⟨by linarith [ht.1], ht.2.le⟩)
    have h := (continuousOn_Li₂.continuousWithinAt (by norm_num)).mono_left hle
    simpa using h
  -- (b) `Li₂ (y/(y-1)) → Li₂ 0 = 0`
  have hmap : Tendsto (fun y : ℝ => y / (y - 1)) (𝓝[>] (0 : ℝ)) (𝓝[Icc (-1 : ℝ) 1] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : ContinuousAt (fun y : ℝ => y / (y - 1)) 0 :=
        continuousAt_id.div (continuousAt_id.sub continuousAt_const) (by norm_num)
      have h : Tendsto (fun y : ℝ => y / (y - 1)) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) / (0 - 1))) :=
        hc.tendsto.mono_left nhdsWithin_le_nhds
      simpa using h
    · filter_upwards [hev] with y hy
      have hval : y / (y - 1) = -(y / (1 - y)) := by
        rw [show y - 1 = -(1 - y) by ring, div_neg]
      have hb : y / (1 - y) ≤ 1 := by
        rw [div_le_one (by linarith [hy.2])]
        linarith [hy.2]
      have hnn : 0 ≤ y / (1 - y) := div_nonneg hy.1.le (by linarith [hy.2])
      exact ⟨by rw [hval]; linarith, by rw [hval]; linarith⟩
  have hLi2b : Tendsto (fun y : ℝ => Li₂ (y / (y - 1))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (continuousOn_Li₂.continuousWithinAt
      (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)).tendsto.comp hmap
    simpa using h
  -- (c) `log²(1-y)/2 → 0` by continuity at `0`
  have hT3 : Tendsto (fun y : ℝ => Real.log (1 - y) ^ 2 / 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1c : ContinuousAt (fun y : ℝ => (1 : ℝ) - y) 0 :=
      continuousAt_const.sub continuousAt_id
    have h2c : ContinuousAt Real.log ((1 : ℝ) - 0) := by
      rw [show (1 : ℝ) - 0 = 1 by norm_num]
      exact Real.continuousAt_log one_ne_zero
    have hc : ContinuousAt (fun y : ℝ => Real.log (1 - y) ^ 2 / 2) 0 :=
      ((h2c.comp h1c).pow 2).div_const 2
    have h : Tendsto (fun y : ℝ => Real.log (1 - y) ^ 2 / 2) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.log (1 - 0) ^ 2 / 2)) := hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h
  have hlim : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [hG]
    have h := (hLi2a.add hLi2b).add hT3
    simpa using h
  -- Step 4: combine — `G` is eventually the constant `G x`, so `G x = 0`.
  have hGeq : ∀ᶠ y in 𝓝[>] (0 : ℝ), G y = G x := by
    filter_upwards [hev] with y hy
    rcases le_total y x with h | h
    · exact (hconst y hy x hx h).symm
    · exact hconst x hx y hy h
  have hclim : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (G x)) :=
    Tendsto.congr' (by filter_upwards [hGeq] with y h; exact h.symm) tendsto_const_nhds
  have hGx : G x = 0 := tendsto_nhds_unique hclim hlim
  have hGx' : Li₂ x + Li₂ (x / (x - 1)) + Real.log (1 - x) ^ 2 / 2 = 0 := by
    simpa [hG] using hGx
  linarith

end Dilog
