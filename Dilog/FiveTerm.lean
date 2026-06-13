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

end Dilog
