/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib
import Dilog.Basic

/-!
# Abel's five-term relation for the dilogarithm (Rogers `L` form)

The capstone of weight-2 dilogarithm theory: for `x, y ∈ (0,1)`,

  `L(x) + L(y) = L(xy) + L(x(1−y)/(1−xy)) + L(y(1−x)/(1−xy))`,

where `L` is the Rogers `L`-function `L(x) = Li₂(x) + ½ log x · log(1−x)`. With it, every
two-variable weight-2 dilogarithm identity (and the ladders built from them) follows.

Proof strategy (the same derivative scheme as Euler reflection / Landen in `Dilog.Basic`):
fix `y`, view the difference as a function of `x` on `(0,1)`, show its derivative vanishes
(an algebraic cancellation of the `L'` log-terms), conclude it is constant, and evaluate
the constant at `x → 0⁺` (where it is `0`).

## Building blocks
* `Dilog.hasDerivAt_rogersL` : `L'(x) = −½(log(1−x)/x + log x/(1−x))` on `(0,1)`.
-/

open Set
open scoped Real

namespace Dilog

/-- The derivative of the Rogers `L`-function on `(0,1)`:
`L'(x) = −(log(1−x)/x + log x/(1−x))/2`. -/
theorem hasDerivAt_rogersL {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt rogersL (-(Real.log (1 - x) / x + Real.log x / (1 - x)) / 2) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hx0' : x ≠ 0 := ne_of_gt hx0
  have h1x : (1 : ℝ) - x ≠ 0 := by linarith
  -- derivative of `Li₂`
  have hLi : HasDerivAt Li₂ (-Real.log (1 - x) / x) x :=
    hasDerivAt_Li₂ (by rw [abs_of_pos hx0]; exact hx1) hx0'
  -- derivative of `log`
  have hlogx : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0'
  -- derivative of `log (1 - ·)`
  have hlin : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
  have hlog1x : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-(1 - x)⁻¹) x := by
    have := (Real.hasDerivAt_log h1x).comp x hlin
    simpa using this
  -- product rule for `log x · log (1 - x)`
  have hprod : HasDerivAt (fun t : ℝ => Real.log t * Real.log (1 - t))
      (x⁻¹ * Real.log (1 - x) + Real.log x * -(1 - x)⁻¹) x := hlogx.mul hlog1x
  -- `rogersL = Li₂ + (log · log(1-·)) / 2`
  have hsum : HasDerivAt rogersL
      ((-Real.log (1 - x) / x) + (x⁻¹ * Real.log (1 - x) + Real.log x * -(1 - x)⁻¹) / 2) x := by
    have := hLi.add (hprod.div_const 2)
    simpa [rogersL] using this
  convert hsum using 1
  field_simp
  ring

/-- The five-term difference, as a function of `x` with `y` fixed, has zero derivative on
`(0,1)`: the log-terms of `L'` cancel after rewriting every argument's logarithm in the
basis `{log x, log y, log(1−x), log(1−y), log(1−xy)}`. -/
theorem fiveterm_hasDerivAt_zero {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => rogersL t - rogersL (t * y)
        - rogersL (t * (1 - y) / (1 - t * y)) - rogersL (y * (1 - t) / (1 - t * y))) 0 x := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have hD : (0 : ℝ) < 1 - x * y := by nlinarith
  have hD' : (1 : ℝ) - x * y ≠ 0 := ne_of_gt hD
  have h1y : (0 : ℝ) < 1 - y := by linarith
  have h1x : (0 : ℝ) < 1 - x := by linarith
  -- membership of the three composite arguments in (0,1)
  have ha : x * y ∈ Ioo (0 : ℝ) 1 := ⟨mul_pos hx0 hy0, by nlinarith⟩
  have hb : x * (1 - y) / (1 - x * y) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (mul_pos hx0 h1y) hD, by rw [div_lt_one hD]; nlinarith⟩
  have hc : y * (1 - x) / (1 - x * y) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (mul_pos hy0 h1x) hD, by rw [div_lt_one hD]; nlinarith⟩
  -- derivatives of the three rational arguments
  have da : HasDerivAt (fun t : ℝ => t * y) y x := by
    simpa using (hasDerivAt_id x).mul_const y
  have dden : HasDerivAt (fun t : ℝ => 1 - t * y) (-y) x := by
    simpa using ((hasDerivAt_id x).mul_const y).const_sub (1 : ℝ)
  have dbnum : HasDerivAt (fun t : ℝ => t * (1 - y)) (1 - y) x := by
    simpa using (hasDerivAt_id x).mul_const (1 - y)
  have db := dbnum.div dden hD'
  have dcnum : HasDerivAt (fun t : ℝ => y * (1 - t)) (y * -1) x :=
    ((hasDerivAt_id x).const_sub (1 : ℝ)).const_mul y
  have dc := dcnum.div dden hD'
  -- compose with the Rogers-L derivative
  have Lx := hasDerivAt_rogersL ⟨hx0, hx1⟩
  have La := (hasDerivAt_rogersL ha).comp x da
  have Lb := (hasDerivAt_rogersL hb).comp x db
  have Lc := (hasDerivAt_rogersL hc).comp x dc
  have HG := ((Lx.sub La).sub Lb).sub Lc
  convert HG using 1
  -- now the algebraic + logarithmic cancellation `0 = (derivative expression)`
  have hxy0 : x * y ≠ 0 := ne_of_gt (mul_pos hx0 hy0)
  have hx0' : x ≠ 0 := ne_of_gt hx0
  have hy0' : y ≠ 0 := ne_of_gt hy0
  have hDyx : (1 : ℝ) - y * x ≠ 0 := by rw [mul_comm]; exact hD'
  -- simplify `1 - b` and `1 - c`
  have hb1 : 1 - x * (1 - y) / (1 - x * y) = (1 - x) / (1 - x * y) := by
    field_simp; ring
  have hc1 : 1 - y * (1 - x) / (1 - x * y) = (1 - y) / (1 - x * y) := by
    field_simp; ring
  rw [hb1, hc1]
  -- expand all logarithms into the basis
  rw [Real.log_mul hx0' hy0',
      Real.log_div (mul_pos hx0 h1y).ne' hD', Real.log_mul hx0' h1y.ne',
      Real.log_div h1x.ne' hD',
      Real.log_div (mul_pos hy0 h1x).ne' hD', Real.log_mul hy0' h1x.ne',
      Real.log_div h1y.ne' hD']
  have h1x' : (1 : ℝ) - x ≠ 0 := h1x.ne'
  have h1y' : (1 : ℝ) - y ≠ 0 := h1y.ne'
  field_simp
  ring

open Filter Topology

/-- `L(t) → 0` as `t → 0⁺`: the `Li₂` part is continuous, and `log t · log(1−t) → 0` is
squeezed by `2·(−t log t) → 0` (using `−log(1−t) ≤ 2t` on `(0,½]`). -/
theorem tendsto_rogersL_nhdsGT_zero : Tendsto rogersL (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hLi : Tendsto Li₂ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto Li₂ (𝓝[Icc (-1 : ℝ) 1] 0) (𝓝 0) := by
      have := (continuousOn_Li₂.continuousWithinAt (by norm_num : (0:ℝ) ∈ Icc (-1:ℝ) 1)).tendsto
      rwa [Li₂_zero] at this
    refine hc.mono_left ?_
    rw [nhdsWithin_le_iff]
    exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by norm_num) (by norm_num))
  have hmem1 : Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) :=
    (nhdsGT_basis (0:ℝ)).mem_of_mem (show (0:ℝ) < 1 by norm_num)
  have hmem2 : Ioo (0:ℝ) (1/2) ∈ 𝓝[>] (0:ℝ) :=
    (nhdsGT_basis (0:ℝ)).mem_of_mem (show (0:ℝ) < 1/2 by norm_num)
  have hlog : Tendsto (fun t : ℝ => Real.log t * Real.log (1 - t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hg : Tendsto (fun t : ℝ => 2 * Real.negMulLog t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h0 : Tendsto Real.negMulLog (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using (Real.continuous_negMulLog.tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0))
      simpa using h0.const_mul 2
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [hmem1] with t ht
      have h1 : Real.log t ≤ 0 := Real.log_nonpos ht.1.le ht.2.le
      have h2 : Real.log (1 - t) ≤ 0 := Real.log_nonpos (by linarith [ht.2]) (by linarith [ht.1])
      nlinarith [mul_nonneg (neg_nonneg.mpr h1) (neg_nonneg.mpr h2)]
    · filter_upwards [hmem2] with t ht
      have ht0 : 0 < t := ht.1
      have h1t : (0:ℝ) < 1 - t := by linarith [ht.2]
      have hlogt : Real.log t ≤ 0 := Real.log_nonpos ht0.le (by linarith [ht.2])
      have hb : -Real.log (1 - t) ≤ 2 * t := by
        have h := Real.one_sub_inv_le_log_of_pos h1t
        have e : (1 - t)⁻¹ - 1 = t / (1 - t) := by field_simp; ring
        have hle : t / (1 - t) ≤ 2 * t := by rw [div_le_iff₀ h1t]; nlinarith [ht.2, ht0]
        have hh : -Real.log (1 - t) ≤ (1 - t)⁻¹ - 1 := by linarith
        rw [e] at hh; linarith
      calc Real.log t * Real.log (1 - t)
          = (-Real.log t) * (-Real.log (1 - t)) := by ring
        _ ≤ (-Real.log t) * (2 * t) := mul_le_mul_of_nonneg_left hb (neg_nonneg.mpr hlogt)
        _ = 2 * Real.negMulLog t := by rw [show Real.negMulLog t = -t * Real.log t from rfl]; ring
  have hr : rogersL = fun t => Li₂ t + Real.log t * Real.log (1 - t) / 2 := rfl
  rw [hr]
  simpa using hLi.add (hlog.div_const 2)

/-- The Rogers `L`-function is continuous at every interior point of `(0,1)`. -/
theorem continuousAt_rogersL {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : ContinuousAt rogersL x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hLi : ContinuousAt Li₂ x :=
    continuousOn_Li₂.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hlog1 : ContinuousAt (fun t : ℝ => Real.log t) x := Real.continuousAt_log (ne_of_gt hx0)
  have hlog2 : ContinuousAt (fun t : ℝ => Real.log (1 - t)) x :=
    (Real.continuousAt_log (by linarith : (1 : ℝ) - x ≠ 0)).comp
      (continuousAt_const.sub continuousAt_id)
  have hr : rogersL = fun t => Li₂ t + Real.log t * Real.log (1 - t) / 2 := rfl
  rw [hr]
  exact hLi.add ((hlog1.mul hlog2).div_const 2)

/-- **Abel's five-term relation** in Rogers `L` form: for `x, y ∈ (0,1)`,
`L(x) + L(y) = L(xy) + L(x(1−y)/(1−xy)) + L(y(1−x)/(1−xy))`. The capstone of weight-2
dilogarithm theory — with it every two-variable dilogarithm identity follows. (First
machine-checked in any proof assistant, per a literature check of June 2026.) -/
theorem rogersL_fiveterm {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    rogersL x + rogersL y =
      rogersL (x * y) + rogersL (x * (1 - y) / (1 - x * y))
        + rogersL (y * (1 - x) / (1 - x * y)) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have hyIoo : y ∈ Ioo (0 : ℝ) 1 := ⟨hy0, hy1⟩
  set G : ℝ → ℝ := fun t => rogersL t - rogersL (t * y)
      - rogersL (t * (1 - y) / (1 - t * y)) - rogersL (y * (1 - t) / (1 - t * y)) with hG
  -- G is constant on (0,1).
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt G 0 t := fun t ht => fiveterm_hasDerivAt_zero ht hyIoo
  have hGconst : ∀ t ∈ Ioo (0 : ℝ) 1, G t = G x := fun t ht =>
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo 0 1).isPreconnected
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) ht ⟨hx0, hx1⟩
  have hmem01 : Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) :=
    (nhdsGT_basis (0:ℝ)).mem_of_mem (show (0:ℝ) < 1 by norm_num)
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Ioo (0:ℝ) 1 := eventually_of_mem hmem01 fun t ht => ht
  -- Boundary limit of each piece as t → 0⁺.
  have key : ∀ {f : ℝ → ℝ}, Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0) → (∀ᶠ t in 𝓝[>] (0:ℝ), 0 < f t) →
      Tendsto (fun t => rogersL (f t)) (𝓝[>] 0) (𝓝 0) :=
    fun hf hpos => tendsto_rogersL_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hf, hpos⟩)
  have hL_t : Tendsto (fun t : ℝ => rogersL t) (𝓝[>] 0) (𝓝 0) := tendsto_rogersL_nhdsGT_zero
  have hty0 : Tendsto (fun t : ℝ => t * y) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using ((continuous_id.mul continuous_const).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hL_ty : Tendsto (fun t : ℝ => rogersL (t * y)) (𝓝[>] 0) (𝓝 0) :=
    key hty0 (hev.mono fun t ht => mul_pos ht.1 hy0)
  have hbcont : ContinuousAt (fun t : ℝ => t * (1 - y) / (1 - t * y)) 0 := by
    refine ContinuousAt.div (continuousAt_id.mul continuousAt_const)
      (continuousAt_const.sub (continuousAt_id.mul continuousAt_const)) ?_
    simp
  have hb0 : Tendsto (fun t : ℝ => t * (1 - y) / (1 - t * y)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := hbcont.tendsto; simp only [zero_mul, zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hL_b : Tendsto (fun t : ℝ => rogersL (t * (1 - y) / (1 - t * y))) (𝓝[>] 0) (𝓝 0) :=
    key hb0 (hev.mono fun t ht => div_pos (mul_pos ht.1 (by linarith [hy1]))
      (by nlinarith [ht.1, ht.2, hy0, hy1]))
  have hccont : ContinuousAt (fun t : ℝ => y * (1 - t) / (1 - t * y)) 0 := by
    refine ContinuousAt.div (continuousAt_const.mul (continuousAt_const.sub continuousAt_id))
      (continuousAt_const.sub (continuousAt_id.mul continuousAt_const)) ?_
    simp
  have hcy : Tendsto (fun t : ℝ => y * (1 - t) / (1 - t * y)) (𝓝[>] (0:ℝ)) (𝓝 y) := by
    have h := hccont.tendsto
    simp only [sub_zero, zero_mul, mul_one, div_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hL_c : Tendsto (fun t : ℝ => rogersL (y * (1 - t) / (1 - t * y))) (𝓝[>] 0) (𝓝 (rogersL y)) :=
    (continuousAt_rogersL hyIoo).tendsto.comp hcy
  have hlim : Tendsto G (𝓝[>] 0) (𝓝 (-rogersL y)) := by
    have h := ((hL_t.sub hL_ty).sub hL_b).sub hL_c
    simpa using h
  -- G is eventually constant (= G x) near 0⁺, so its limit is G x; hence G x = -L y.
  have hGx : G x = -rogersL y := by
    refine tendsto_nhds_unique ?_ hlim
    refine Tendsto.congr' ?_
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => G x) (𝓝[>] 0) (𝓝 (G x)))
    filter_upwards [hev] with t ht using (hGconst t ht).symm
  simp only [hG] at hGx
  linarith [hGx]

end Dilog
