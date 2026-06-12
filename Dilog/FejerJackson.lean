/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib

/-!
# The Fejér–Jackson inequality

The **Fejér–Jackson inequality** (Fejér 1910, Jackson 1911): every partial sum of the
sine series `∑_{k=1}^{M} sin(kθ)/k` is strictly positive on `(0, π)`. A literature
check (2026-06) found no formalization in any proof assistant.

The proof is the classical interior-minimum induction:
* the derivative is the shifted Dirichlet kernel, handled **multiplicatively** (no
  division): `2 sin(θ/2) · ∑_{k=1}^M cos(kθ) = sin((M+½)θ) − sin(θ/2)` by telescoping
  the product-to-sum identity;
* at an interior local minimum the derivative vanishes, so
  `sin((M+½)θ₀) = sin(θ₀/2)`; factoring the difference gives
  `sin(Mθ₀/2)·cos((M+1)θ₀/2) = 0`, whose two branches force `sin(Mθ₀) = 0` or
  `sin(Mθ₀) = sin θ₀ > 0` — either way the **last term is nonnegative**, so the
  minimum value is at least the previous partial sum, positive by induction;
* the boundary values are `0`, so no interior point can be ≤ 0.

This is the engine behind `Cl₂ > 0` on `(0, π)` (by Abel summation, later file), and
hence behind "weight-2 zeta states never reach an orthogonal state" (QSL connection).

## Main result
* `Dilog.fejerSum_pos` : `0 < ∑_{k=1}^{M} sin(kθ)/k` for `M ≥ 1`, `θ ∈ (0, π)`.
-/

noncomputable section
open scoped Real
open Set Finset

namespace Dilog

/-- The Fejér–Jackson partial sum `∑_{k=1}^{M} sin(kθ)/k` (indexed `k ∈ range M` with
summand `sin((k+1)θ)/(k+1)`). -/
def fejerSum (M : ℕ) (θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range M, Real.sin (((k : ℝ) + 1) * θ) / ((k : ℝ) + 1)

@[simp] lemma fejerSum_zero_arg (M : ℕ) : fejerSum M 0 = 0 := by
  simp [fejerSum]

@[simp] lemma fejerSum_pi (M : ℕ) : fejerSum M π = 0 := by
  unfold fejerSum
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [show ((k : ℝ) + 1) * π = ((k + 1 : ℕ) : ℝ) * π by push_cast; ring,
    Real.sin_nat_mul_pi, zero_div]

lemma continuous_fejerSum (M : ℕ) : Continuous (fejerSum M) := by
  unfold fejerSum
  fun_prop

/-- Termwise differentiation: `fejerSum M` has derivative the shifted Dirichlet kernel
`∑_{k=1}^M cos(kθ)`. -/
lemma hasDerivAt_fejerSum (M : ℕ) (θ : ℝ) :
    HasDerivAt (fejerSum M) (∑ k ∈ Finset.range M, Real.cos (((k : ℝ) + 1) * θ)) θ := by
  unfold fejerSum
  apply HasDerivAt.fun_sum
  intro k _
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => ((k : ℝ) + 1) * x) ((k : ℝ) + 1) θ := by
    simpa using (hasDerivAt_id θ).const_mul ((k : ℝ) + 1)
  have h2 := (Real.hasDerivAt_sin (((k : ℝ) + 1) * θ)).comp θ h1
  have h3 := h2.div_const ((k : ℝ) + 1)
  convert h3 using 1
  field_simp

/-- The multiplicative (division-free) Dirichlet kernel identity:
`2 sin(θ/2) · ∑_{k=1}^M cos(kθ) = sin((M+½)θ) − sin(θ/2)`, by telescoping. -/
lemma dirichlet_telescope (M : ℕ) (θ : ℝ) :
    2 * Real.sin (θ / 2) * ∑ k ∈ Finset.range M, Real.cos (((k : ℝ) + 1) * θ)
      = Real.sin (((M : ℝ) + 1 / 2) * θ) - Real.sin (θ / 2) := by
  set f : ℕ → ℝ := fun k => Real.sin (((k : ℝ) + 1 / 2) * θ) with hf
  have hterm : ∀ k : ℕ, f (k + 1) - f k = 2 * Real.sin (θ / 2) * Real.cos (((k : ℝ) + 1) * θ) := by
    intro k
    rw [hf]
    simp only
    rw [show (((k + 1 : ℕ) : ℝ) + 1 / 2) * θ = ((k : ℝ) + 1 + 1 / 2) * θ by push_cast; ring]
    rw [Real.sin_sub_sin,
      show (((k : ℝ) + 1 + 1 / 2) * θ - ((k : ℝ) + 1 / 2) * θ) / 2 = θ / 2 by ring,
      show (((k : ℝ) + 1 + 1 / 2) * θ + ((k : ℝ) + 1 / 2) * θ) / 2 = ((k : ℝ) + 1) * θ by ring]
  calc 2 * Real.sin (θ / 2) * ∑ k ∈ Finset.range M, Real.cos (((k : ℝ) + 1) * θ)
      = ∑ k ∈ Finset.range M, (f (k + 1) - f k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => (hterm k).symm
    _ = f M - f 0 := Finset.sum_range_sub f M
    _ = Real.sin (((M : ℝ) + 1 / 2) * θ) - Real.sin (θ / 2) := by
        rw [hf]
        simp only [Nat.cast_zero, zero_add]
        rw [show (1 / 2 : ℝ) * θ = θ / 2 by ring]

/-- **The critical-point dichotomy**: at an interior local minimum of `fejerSum M`,
the "last term" sine `sin(Mθ₀)` is nonnegative — the two branches of the equality
`sin((M+½)θ₀) = sin(θ₀/2)` give `sin(Mθ₀) = 0` or `sin(Mθ₀) = sin θ₀ > 0`. -/
lemma sin_last_nonneg_at_localMin {M : ℕ} {θ₀ : ℝ} (h0 : 0 < θ₀) (hπ : θ₀ < π)
    (hmin : IsLocalMin (fejerSum M) θ₀) : 0 ≤ Real.sin ((M : ℝ) * θ₀) := by
  have hcrit : ∑ k ∈ Finset.range M, Real.cos (((k : ℝ) + 1) * θ₀) = 0 :=
    hmin.hasDerivAt_eq_zero (hasDerivAt_fejerSum M θ₀)
  have htel := dirichlet_telescope M θ₀
  rw [hcrit, mul_zero] at htel
  -- `sin((M+½)θ₀) = sin(θ₀/2)`; factor the difference
  have hfact : Real.sin ((M : ℝ) * θ₀ / 2) * Real.cos (((M : ℝ) + 1) * θ₀ / 2) = 0 := by
    have h := Real.sin_sub_sin (((M : ℝ) + 1 / 2) * θ₀) (θ₀ / 2)
    rw [show (((M : ℝ) + 1 / 2) * θ₀ - θ₀ / 2) / 2 = (M : ℝ) * θ₀ / 2 by ring,
      show (((M : ℝ) + 1 / 2) * θ₀ + θ₀ / 2) / 2 = ((M : ℝ) + 1) * θ₀ / 2 by ring] at h
    nlinarith [h, htel]
  rcases mul_eq_zero.mp hfact with hs | hc
  · -- branch 1: `Mθ₀ = 2mπ`, so `sin(Mθ₀) = 0`
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hs
    have harg : (M : ℝ) * θ₀ = ((2 * m : ℤ) : ℝ) * π := by push_cast at hm ⊢; linarith
    rw [harg, Real.sin_int_mul_pi]
  · -- branch 2: `(M+1)θ₀ = (2m+1)π`, so `sin(Mθ₀) = sin θ₀ > 0`
    obtain ⟨m, hm⟩ := Real.cos_eq_zero_iff.mp hc
    have harg : (M : ℝ) * θ₀ = ((2 * m + 1 : ℤ) : ℝ) * π - θ₀ := by
      push_cast at hm ⊢
      linarith
    rw [harg, Real.sin_int_mul_pi_sub]
    have hodd : Odd (2 * m + 1 : ℤ) := ⟨m, by ring⟩
    rw [hodd.neg_one_zpow]
    simpa using (Real.sin_pos_of_pos_of_lt_pi h0 hπ).le

/-- **The Fejér–Jackson inequality** (Fejér 1910, Jackson 1911): every partial sum
`∑_{k=1}^{M} sin(kθ)/k` with `M ≥ 1` is strictly positive on `(0, π)`. -/
theorem fejerSum_pos : ∀ M : ℕ, 1 ≤ M → ∀ {θ : ℝ}, 0 < θ → θ < π → 0 < fejerSum M θ := by
  intro M
  induction M with
  | zero => exact fun h => absurd h (by norm_num)
  | succ N ih =>
    intro _ θ h0 hπ
    rcases Nat.eq_zero_or_pos N with hN | hN
    · -- base case `M = 1`: the sum is `sin θ`
      subst hN
      have := Real.sin_pos_of_pos_of_lt_pi h0 hπ
      simpa [fejerSum] using this
    · -- inductive step
      -- any interior local minimum of `fejerSum (N+1)` has positive value
      have key : ∀ x, 0 < x → x < π → IsLocalMin (fejerSum (N + 1)) x →
          0 < fejerSum (N + 1) x := by
        intro x hx1 hx2 hmin
        have hlast := sin_last_nonneg_at_localMin (M := N + 1) hx1 hx2 hmin
        have hsplit : fejerSum (N + 1) x
            = fejerSum N x + Real.sin (((N : ℝ) + 1) * x) / ((N : ℝ) + 1) := by
          unfold fejerSum
          rw [Finset.sum_range_succ]
        rw [hsplit]
        have h1 := ih hN hx1 hx2
        have h2 : 0 ≤ Real.sin (((N : ℝ) + 1) * x) / ((N : ℝ) + 1) := by
          apply div_nonneg _ (by positivity)
          rwa [show (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 by push_cast; ring] at hlast
        linarith
      -- compactness + boundary analysis
      by_contra hcon
      push_neg at hcon
      obtain ⟨θs, hθs, hminOn⟩ := isCompact_Icc.exists_isMinOn
        (Set.nonempty_Icc.mpr Real.pi_pos.le) (continuous_fejerSum (N + 1)).continuousOn
      have hθmem : θ ∈ Icc (0 : ℝ) π := ⟨h0.le, hπ.le⟩
      have hval : fejerSum (N + 1) θs ≤ fejerSum (N + 1) θ := hminOn hθmem
      by_cases hin : 0 < θs ∧ θs < π
      · have hloc : IsLocalMin (fejerSum (N + 1)) θs :=
          hminOn.isLocalMin (Icc_mem_nhds hin.1 hin.2)
        have := key θs hin.1 hin.2 hloc
        linarith
      · -- the minimizer is a boundary point, where the sum vanishes
        have hzero : fejerSum (N + 1) θs = 0 := by
          rcases hθs with ⟨hl, hr⟩
          rcases eq_or_lt_of_le hl with h | h
          · rw [← h]
            exact fejerSum_zero_arg _
          · have hπs : θs = π := by
              by_contra hne
              exact hin ⟨h, lt_of_le_of_ne hr hne⟩
            rw [hπs]
            exact fejerSum_pi _
        have hθ0 : fejerSum (N + 1) θ = 0 := le_antisymm hcon (hzero ▸ hval)
        have hminθ : IsMinOn (fejerSum (N + 1)) (Icc 0 π) θ := by
          apply isMinOn_iff.mpr
          intro y hy
          calc fejerSum (N + 1) θ = 0 := hθ0
            _ = fejerSum (N + 1) θs := hzero.symm
            _ ≤ fejerSum (N + 1) y := hminOn hy
        have hloc : IsLocalMin (fejerSum (N + 1)) θ := hminθ.isLocalMin (Icc_mem_nhds h0 hπ)
        have := key θ h0 hπ hloc
        linarith

end Dilog
