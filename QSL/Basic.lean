/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib

/-!
# The Margolus–Levitin quantum speed limit

This file formalizes the **Margolus–Levitin theorem** (Margolus & Levitin, *The maximum
speed of dynamical evolution*, Physica D 120 (1998) 188–195; arXiv:quant-ph/9710043):
a quantum state with mean energy `⟨E⟩` above the ground state needs time at least
`τ ≥ π·ℏ/(2⟨E⟩)` to evolve into an orthogonal state. Units: `ℏ = 1`.

We state the theorem in its honest mathematical form: about the autocorrelation function
`S(τ) = ∑ pₙ e^(−i·Eₙ·τ)` of a discrete nonnegative spectral measure (`pₙ = |cₙ|²` are the
populations of the energy eigenstates, `Eₙ ≥ 0` the energies above the ground state).
Orthogonality `S(τ) = 0` is split into its real and imaginary parts, so the whole
development is real — no complex numbers needed.

A literature check (2026-06) found no quantum-speed-limit theorem in any proof assistant
(Mathlib has no `quantum` declarations at all; the Coq/Isabelle quantum libraries cover
circuits, not dynamical bounds). This appears to be the first.

## Main results
* `QSL.one_sub_le_cos` : the Margolus–Levitin cosine inequality
    `1 − (2/π)(x + sin x) ≤ cos x` for `x ≥ 0` (equality at `x = 0` and `x = π`).
* `QSL.margolus_levitin` : the speed limit `π ≤ 2·⟨E⟩·τ` for any orthogonalization time
    `τ ≥ 0`, i.e. `τ ≥ π/(2⟨E⟩)`.

## Roadmap (later files)
* The Mandelstam–Tamm bound `τ ≥ π/(2·ΔE)` (1945).
* Sharpness: the state `(|0⟩+|2E⟩)/√2` attains the bound.
* The arbitrary-fidelity generalization (Giovannetti–Lloyd–Maccone 2003 conjecture,
  proven 2023).
-/

noncomputable section
open scoped Real
open Set

namespace QSL

/-! ### The cosine inequality

`h(x) = cos x − 1 + (2/π)(x + sin x) ≥ 0` for `x ≥ 0`. The proof splits at
`x₀ = 2·arctan(2/π)`: `h` increases on `[0, x₀]`, decreases on `[x₀, π]`, with
`h(0) = h(π) = 0`; for `x ≥ π` the linear term alone dominates since `x + sin x` is
monotone. -/

private lemma monotone_add_sin : Monotone fun y : ℝ => y + Real.sin y := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y + Real.sin y) (1 + Real.cos y) y :=
    fun y => (hasDerivAt_id y).add (Real.hasDerivAt_sin y)
  apply monotone_of_deriv_nonneg
  · exact fun y => (hd y).differentiableAt
  · intro y
    rw [(hd y).deriv]
    nlinarith [Real.neg_one_le_cos y]

/-- The auxiliary function of the Margolus–Levitin proof. -/
private def mlAux (y : ℝ) : ℝ := Real.cos y - 1 + 2 / π * (y + Real.sin y)

private lemma mlAux_zero : mlAux 0 = 0 := by
  simp [mlAux]

private lemma mlAux_pi : mlAux π = 0 := by
  have hne : π ≠ 0 := ne_of_gt Real.pi_pos
  simp only [mlAux, Real.cos_pi, Real.sin_pi, add_zero]
  field_simp
  norm_num

private lemma hasDerivAt_mlAux (y : ℝ) :
    HasDerivAt mlAux (-Real.sin y + 2 / π * (1 + Real.cos y)) y := by
  have h1 := (Real.hasDerivAt_cos y).sub_const 1
  have h2 := ((hasDerivAt_id y).add (Real.hasDerivAt_sin y)).const_mul (2 / π)
  exact h1.add h2

/-- Half-angle form of the derivative sign: `mlAux' y = 2·cos(y/2)·((2/π)·cos(y/2) − sin(y/2))`. -/
private lemma mlAux_deriv_eq (y : ℝ) :
    -Real.sin y + 2 / π * (1 + Real.cos y)
      = 2 * Real.cos (y / 2) * (2 / π * Real.cos (y / 2) - Real.sin (y / 2)) := by
  have hs : Real.sin y = 2 * Real.sin (y / 2) * Real.cos (y / 2) := by
    rw [← Real.sin_two_mul]
    congr 1
    ring
  have hc : Real.cos y = 2 * Real.cos (y / 2) ^ 2 - 1 := by
    have h := Real.cos_sq (y / 2)
    rw [show (2 : ℝ) * (y / 2) = y by ring] at h
    linarith
  rw [hs, hc]
  ring

private lemma cos_half_pos {y : ℝ} (h0 : 0 ≤ y) (hπ : y < π) : 0 < Real.cos (y / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> [linarith [Real.pi_pos]; linarith]

/-- On `(0, x₀)` with `x₀ = 2·arctan(2/π)` the derivative is nonnegative. -/
private lemma mlAux_deriv_nonneg {y : ℝ} (h0 : 0 ≤ y)
    (hy : y ≤ 2 * Real.arctan (2 / π)) (hyπ : y < π) :
    0 ≤ -Real.sin y + 2 / π * (1 + Real.cos y) := by
  rw [mlAux_deriv_eq]
  have hc := cos_half_pos h0 hyπ
  have htan : Real.tan (y / 2) ≤ 2 / π := by
    have harc : y / 2 ≤ Real.arctan (2 / π) := by linarith
    have hmem1 : y / 2 ∈ Ioo (-(π / 2)) (π / 2) := by
      constructor
      · linarith [Real.pi_pos]
      · exact lt_of_le_of_lt harc (Real.arctan_mem_Ioo _).2
    have h := Real.strictMonoOn_tan.monotoneOn hmem1 (Real.arctan_mem_Ioo _) harc
    rwa [Real.tan_arctan] at h
  have hsin : Real.sin (y / 2) ≤ 2 / π * Real.cos (y / 2) := by
    have h := mul_le_mul_of_nonneg_right htan hc.le
    rwa [Real.tan_mul_cos (ne_of_gt hc)] at h
  nlinarith [hc]

/-- On `(x₀, π)` the derivative is nonpositive. -/
private lemma mlAux_deriv_nonpos {y : ℝ} (h0 : 0 ≤ y)
    (hy : 2 * Real.arctan (2 / π) ≤ y) (hyπ : y < π) :
    -Real.sin y + 2 / π * (1 + Real.cos y) ≤ 0 := by
  rw [mlAux_deriv_eq]
  have hc := cos_half_pos h0 hyπ
  have htan : 2 / π ≤ Real.tan (y / 2) := by
    have harc : Real.arctan (2 / π) ≤ y / 2 := by linarith
    have hmem2 : y / 2 ∈ Ioo (-(π / 2)) (π / 2) := by
      constructor
      · linarith [Real.pi_pos]
      · linarith
    have h := Real.strictMonoOn_tan.monotoneOn (Real.arctan_mem_Ioo _) hmem2 harc
    rwa [Real.tan_arctan] at h
  have hsin : 2 / π * Real.cos (y / 2) ≤ Real.sin (y / 2) := by
    have h := mul_le_mul_of_nonneg_right htan hc.le
    rwa [Real.tan_mul_cos (ne_of_gt hc)] at h
  nlinarith [hc]

private lemma arctan_two_div_pi_pos : 0 < Real.arctan (2 / π) :=
  Real.arctan_pos.mpr (by positivity)

private lemma two_arctan_lt_pi : 2 * Real.arctan (2 / π) < π := by
  have h := (Real.arctan_mem_Ioo (2 / π)).2
  linarith

/-- **The Margolus–Levitin cosine inequality**: `1 − (2/π)(x + sin x) ≤ cos x` for `x ≥ 0`,
with equality at `x = 0` and `x = π`. -/
theorem one_sub_le_cos {x : ℝ} (hx : 0 ≤ x) :
    1 - 2 / π * (x + Real.sin x) ≤ Real.cos x := by
  have hπ := Real.pi_pos
  have hgoal : 0 ≤ mlAux x → 1 - 2 / π * (x + Real.sin x) ≤ Real.cos x := by
    intro h
    simp only [mlAux] at h
    linarith
  apply hgoal
  rcases le_or_gt π x with hxπ | hxπ
  · -- tail: `x + sin x ≥ π`, so the linear term alone gives `mlAux ≥ cos x + 1 ≥ 0`
    have hmono : π + Real.sin π ≤ x + Real.sin x := monotone_add_sin hxπ
    rw [Real.sin_pi, add_zero] at hmono
    have h2 : (2 : ℝ) ≤ 2 / π * (x + Real.sin x) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hπ]
      nlinarith
    have := Real.neg_one_le_cos x
    unfold mlAux
    linarith
  · -- core `[0, π]`: increase to `x₀ = 2·arctan(2/π)`, then decrease to `π`
    set x₀ : ℝ := 2 * Real.arctan (2 / π) with hx₀
    have hx₀pos : 0 < x₀ := by
      have := arctan_two_div_pi_pos
      rw [hx₀]; linarith
    have hx₀π : x₀ < π := two_arctan_lt_pi
    have hcont : Continuous mlAux := by
      unfold mlAux
      fun_prop
    rcases le_or_gt x x₀ with hcase | hcase
    · -- `mlAux` is monotone on `[0, x₀]` and `mlAux 0 = 0`
      have hmono : MonotoneOn mlAux (Icc 0 x₀) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x₀) hcont.continuousOn
        · intro y _
          exact (hasDerivAt_mlAux y).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [interior_Icc] at hy
          rw [(hasDerivAt_mlAux y).deriv]
          exact mlAux_deriv_nonneg hy.1.le hy.2.le (lt_trans hy.2 hx₀π)
      have h := hmono ⟨le_refl 0, hx₀pos.le⟩ ⟨hx, hcase⟩ hx
      rwa [mlAux_zero] at h
    · -- `mlAux` is antitone on `[x₀, π]` and `mlAux π = 0`
      have hanti : AntitoneOn mlAux (Icc x₀ π) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc x₀ π) hcont.continuousOn
        · intro y _
          exact (hasDerivAt_mlAux y).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [interior_Icc] at hy
          rw [(hasDerivAt_mlAux y).deriv]
          exact mlAux_deriv_nonpos (le_trans hx₀pos.le hy.1.le) hy.1.le hy.2
      have h := hanti ⟨hcase.le, hxπ.le⟩ ⟨hx₀π.le, le_refl π⟩ hxπ.le
      rwa [mlAux_pi] at h

/-! ### The Margolus–Levitin theorem -/

/-- **The Margolus–Levitin theorem** (1998), `ℏ = 1`: if a normalized population
distribution `p` over nonnegative energies `E` has mean energy `⟨E⟩` and its
autocorrelation `S(τ) = ∑ pₙ·e^(−i·Eₙ·τ)` vanishes at some time `τ ≥ 0`
(given here by its real and imaginary parts separately), then `π ≤ 2·⟨E⟩·τ`,
i.e. the orthogonalization time obeys `τ ≥ π/(2⟨E⟩)`.

This bounds the maximum number of distinct (mutually orthogonal) states any isolated
physical system can pass through per unit time by `2⟨E⟩/π` — the "clock speed of the
universe" given an energy budget. -/
theorem margolus_levitin {p E : ℕ → ℝ} {Ebar τ : ℝ}
    (hp : ∀ n, 0 ≤ p n) (hE : ∀ n, 0 ≤ E n) (hτ : 0 ≤ τ)
    (hsum : HasSum p 1)
    (hmean : HasSum (fun n => p n * E n) Ebar)
    (hRe : HasSum (fun n => p n * Real.cos (E n * τ)) 0)
    (hIm : HasSum (fun n => p n * Real.sin (E n * τ)) 0) :
    π ≤ 2 * Ebar * τ := by
  have hπ := Real.pi_pos
  -- termwise application of the cosine inequality, weighted by `p n ≥ 0`
  have hterm : ∀ n, p n * (1 - 2 / π * (E n * τ + Real.sin (E n * τ)))
      ≤ p n * Real.cos (E n * τ) := fun n =>
    mul_le_mul_of_nonneg_left (one_sub_le_cos (mul_nonneg (hE n) hτ)) (hp n)
  -- the left-hand series sums to `1 − (2/π)·(⟨E⟩τ + 0)`
  have h1 : HasSum (fun n => p n * E n * τ) (Ebar * τ) := hmean.mul_right τ
  have h2 : HasSum (fun n => p n * E n * τ + p n * Real.sin (E n * τ)) (Ebar * τ + 0) :=
    h1.add hIm
  have h3 := h2.mul_left (2 / π)
  have h4 := hsum.sub h3
  have hfun : (fun n => p n - 2 / π * (p n * E n * τ + p n * Real.sin (E n * τ)))
      = fun n => p n * (1 - 2 / π * (E n * τ + Real.sin (E n * τ))) := by
    funext n
    ring
  rw [hfun] at h4
  -- compare the two convergent series
  have hkey : 1 - 2 / π * (Ebar * τ + 0) ≤ 0 := hasSum_le hterm h4 hRe
  -- clear the `2/π` factor
  have h5 : π * (1 - 2 / π * (Ebar * τ + 0)) = π - 2 * Ebar * τ := by
    field_simp
    ring
  nlinarith [mul_le_mul_of_nonneg_left hkey hπ.le]

end QSL
