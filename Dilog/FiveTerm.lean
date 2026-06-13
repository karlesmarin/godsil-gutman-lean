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

end Dilog
