/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

/-
# Descartes' rule of signs, through the Budan–Fourier engine

The Budan–Fourier sign-variation count of the derivative tower, read at `x = 0`, is exactly the
coefficient sign-variation count of Descartes' rule. Concretely
`fourierVar p 0 = Polynomial.signVariations p`, the function Mathlib uses for Descartes' rule of
signs. So Descartes' count is not a separate object: it is the engine's `V(0)`, the tower's signs at
`0` being the coefficient signs (`p^{(k)}(0) = k!\,a_k`). The single fact that makes the two match is
that `signChanges` is reversal-invariant: the tower lists the signs low-to-high, Mathlib's `coeffList`
high-to-low.
-/
public import BudanFourier
public import Mathlib.Algebra.Polynomial.RuleOfSigns

open Polynomial

namespace BudanFourier

/-! ### `signChanges` is reversal-invariant -/

/-- `filter (· ≠ 0)` commutes with `reverse`. -/
theorem filter_ne_zero_reverse (s : List SignType) :
    s.reverse.filter (· ≠ 0) = (s.filter (· ≠ 0)).reverse := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    rw [List.reverse_cons, List.filter_append, ih]
    by_cases h : a = 0 <;> simp [List.filter_cons, h]

/-- The number of maximal `≠`-runs is the same forwards and backwards: `destutter (· ≠ ·)` returns a
maximal `≠`-chain sublist, and reversal bijects chain sublists. -/
theorem destutter_ne_length_reverse (L : List SignType) :
    (L.reverse.destutter (· ≠ ·)).length = (L.destutter (· ≠ ·)).length := by
  have aux : ∀ M : List SignType,
      (M.destutter (· ≠ ·)).length ≤ (M.reverse.destutter (· ≠ ·)).length := by
    intro M
    have hchain : (M.destutter (· ≠ ·)).IsChain (· ≠ ·) := List.isChain_destutter (· ≠ ·) M
    have hsub : List.Sublist (M.destutter (· ≠ ·)) M := List.destutter_sublist (· ≠ ·) M
    have hsubr : List.Sublist ((M.destutter (· ≠ ·)).reverse) M.reverse := hsub.reverse
    have hchainr : ((M.destutter (· ≠ ·)).reverse).IsChain (· ≠ ·) :=
      List.isChain_reverse.mpr (hchain.imp (fun _ _ h => Ne.symm h))
    have hle := List.IsChain.length_le_length_destutter_ne hsubr hchainr
    rwa [List.length_reverse] at hle
  have h1 := aux L
  have h2 := aux L.reverse
  rw [List.reverse_reverse] at h2
  omega

/-- `signChanges` does not depend on the orientation of the list. -/
theorem signChanges_reverse (s : List SignType) :
    Sturm.signChanges s.reverse = Sturm.signChanges s := by
  unfold Sturm.signChanges
  rw [filter_ne_zero_reverse]
  congr 1
  exact destutter_ne_length_reverse (s.filter (· ≠ 0))

/-! ### The tower at `0` reads the coefficient signs -/

/-- `sign (p^{(k)}(0)) = sign (a_k)`, since `p^{(k)}(0) = k!\,a_k` and `k! > 0`. -/
theorem sign_iterate_derivative_eval_zero (p : Polynomial ℝ) (k : ℕ) :
    SignType.sign (((derivative^[k]) p).eval 0) = SignType.sign (p.coeff k) := by
  have he : ((derivative^[k]) p).eval 0 = (k.factorial : ℝ) * p.coeff k := by
    rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
    simp [Nat.descFactorial_self, nsmul_eq_mul]
  rw [he, sign_mul, show SignType.sign ((k.factorial : ℝ)) = 1 from
    sign_pos (by exact_mod_cast Nat.factorial_pos k), one_mul]

/-- The tower's signs at `0`, as a list, are the coefficient signs `[sign a_0, …, sign a_n]`. -/
theorem fourierSeq_eval_zero_signs (p : Polynomial ℝ) :
    (fourierSeq p).map (fun q => SignType.sign (q.eval 0))
      = (List.range (p.natDegree + 1)).map (fun k => SignType.sign (p.coeff k)) := by
  rw [fourierSeq, List.map_map]
  exact List.map_congr_left (fun k _ => sign_iterate_derivative_eval_zero p k)

/-- Mathlib's coefficient sign list is the reverse of the tower's sign list (high-to-low vs
low-to-high). -/
theorem coeffList_signs_eq_reverse (p : Polynomial ℝ) (hp : p ≠ 0) :
    (coeffList p).map SignType.sign
      = ((fourierSeq p).map (fun q => SignType.sign (q.eval 0))).reverse := by
  rw [fourierSeq_eval_zero_signs, coeffList, withBotSucc_degree_eq_natDegree_add_one hp]
  simp only [List.map_reverse, List.map_map, Function.comp_def]

/-! ### Descartes' count is the engine's `V(0)` -/

/-- **Descartes through the engine.** The Budan–Fourier sign-variation count of `p` at `0` equals the
coefficient sign-variation count `Polynomial.signVariations p` of Descartes' rule of signs. -/
public theorem fourierVar_zero_eq_signVariations (p : Polynomial ℝ) (hp : p ≠ 0) :
    fourierVar p 0 = Polynomial.signVariations p := by
  rw [fourierVar_eq_signVarAt, Sturm.signVarAt_eq_signChanges]
  have : Polynomial.signVariations p
      = Sturm.signChanges ((coeffList p).map SignType.sign) := rfl
  rw [this, coeffList_signs_eq_reverse p hp, signChanges_reverse]

end BudanFourier

