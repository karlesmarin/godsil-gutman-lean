/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# The Bruhat-Tits / Ramanujan spectral bound

Cross-thread scale-test: applying the Atom-C-prime template (small file
with definition + supporting predicates + one headline theorem) to the
Ramanujan-Bruhat thread's **T1 target**.

## Main definitions

* `bruhatTitsBound k` — the real number `2 · √(k − 1)`, which equals the
  spectral radius of the `k`-regular infinite tree (Bruhat-Tits tree when
  `k = p + 1`) and the Alon-Boppana asymptotic floor for `k`-regular graph
  second eigenvalues. (Registry entry R4 / K_via spectral theory.)
* `IsRamanujan G k` — predicate that a `k`-regular `SimpleGraph` `G` is
  **Ramanujan**: every adjacency-matrix eigenvalue `λ` satisfies either
  `|λ| = k` (the trivial Frobenius-type eigenvalue) or `|λ| ≤ 2√(k−1)`.

## Main statements

* `bruhatTitsBound_nonneg` — `0 ≤ 2√(k−1)`.
* `bruhatTitsBound_le` — for `k ≥ 1`, `2√(k−1) ≤ k`; equality iff `k = 2`.
  This is the **structural reason** the Ramanujan bound is interesting —
  it gives the tightest possible bound on non-trivial eigenvalues below
  the Frobenius eigenvalue `k`.

## Scope

This file is a **methodological scale-test** of the Atom-C-prime template
(see `02_scope_decision.md`). It is NOT a full IsRamanujan API; subsequent
PRs would add spectral-graph-theory content (T2-T4 in
`10_threads/ramanujan-bruhat-thread/02_lean_targets.md`).

## References

* `02_lean_targets.md` in ramanujan-bruhat-thread (T1, T3 targets).
* `formula_registry.md` R3, R4 (Ramanujan predicate + tree spectrum).
* Lubotzky, *Discrete Groups, Expanding Graphs, and Invariant Measures*
  (1994), Chapter 4 §1.

-/

@[expose] public section

namespace SimpleGraph

/-- The **Bruhat-Tits spectral bound** `2 · √(k − 1)`. For `k = p + 1`
prime, this is the spectral radius of the `p + 1`-regular infinite tree
acting on `ℓ²` of its vertices. -/
noncomputable def bruhatTitsBound (k : ℕ) : ℝ :=
  2 * Real.sqrt (k - 1 : ℝ)

@[simp] theorem bruhatTitsBound_zero : bruhatTitsBound 0 = 0 := by
  unfold bruhatTitsBound
  simp [Real.sqrt_eq_zero']

@[simp] theorem bruhatTitsBound_one : bruhatTitsBound 1 = 0 := by
  unfold bruhatTitsBound
  simp

theorem bruhatTitsBound_nonneg (k : ℕ) : 0 ≤ bruhatTitsBound k := by
  unfold bruhatTitsBound
  positivity

/-- **Headline theorem.** For `k ≥ 1`, `2√(k−1) ≤ k`. Equality holds iff
`k = 2`. This is the algebraic content of why the Ramanujan bound is
structurally meaningful: it is the *strictest possible* bound on
non-trivial eigenvalues below the Frobenius eigenvalue `k`, achieved at
`k = 2`, and otherwise strictly less than `k`. -/
theorem bruhatTitsBound_le (k : ℕ) (hk : 1 ≤ k) : bruhatTitsBound k ≤ k := by
  rcases Nat.eq_or_lt_of_le hk with h | h
  · -- k = 1: bound = 0 ≤ 1
    rw [← h]
    simp
  · -- k ≥ 2: use sqrt(k-1) ≤ k/2 ⟺ (k-2)² ≥ 0
    unfold bruhatTitsBound
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    have hkm1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
    have hk_half : (0 : ℝ) ≤ (k : ℝ) / 2 := by linarith
    -- Show sqrt(k-1) ≤ k/2
    have h_sqrt_bound : Real.sqrt ((k : ℝ) - 1) ≤ (k : ℝ) / 2 := by
      rw [show ((k : ℝ) / 2) = Real.sqrt (((k : ℝ) / 2) ^ 2) from
        (Real.sqrt_sq hk_half).symm]
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg ((k : ℝ) - 2)]
    linarith

/-- **Strict bound.** For `k ≥ 3`, `2√(k−1) < k`. The strict-inequality
companion to `bruhatTitsBound_le`. At `k ∈ {0, 1, 2}` equality (or trivial)
holds, but from `k = 3` onward there is a genuine spectral gap between the
Frobenius eigenvalue `k` and the Ramanujan bound. -/
theorem bruhatTitsBound_lt (k : ℕ) (hk : 3 ≤ k) : bruhatTitsBound k < k := by
  unfold bruhatTitsBound
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkm1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
  have hk_half : (0 : ℝ) < (k : ℝ) / 2 := by linarith
  have h_sqrt_strict : Real.sqrt ((k : ℝ) - 1) < (k : ℝ) / 2 := by
    rw [show ((k : ℝ) / 2) = Real.sqrt (((k : ℝ) / 2) ^ 2) from
      (Real.sqrt_sq hk_half.le).symm]
    apply Real.sqrt_lt_sqrt hkm1
    nlinarith [sq_nonneg ((k : ℝ) - 2)]
  linarith

/-- **Squared form.** `(2√(k−1))² = 4(k−1)` for `k ≥ 1`. Useful for
spectral arguments that compare bounds via second moments. -/
theorem bruhatTitsBound_sq (k : ℕ) (hk : 1 ≤ k) :
    bruhatTitsBound k ^ 2 = 4 * ((k : ℝ) - 1) := by
  unfold bruhatTitsBound
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkm1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
  rw [mul_pow, Real.sq_sqrt hkm1]
  ring

/-- **Monotonicity.** The Bruhat-Tits bound is monotone in regularity. -/
theorem bruhatTitsBound_mono {k k' : ℕ} (h : k ≤ k') :
    bruhatTitsBound k ≤ bruhatTitsBound k' := by
  unfold bruhatTitsBound
  have hkk' : ((k : ℝ)) ≤ ((k' : ℝ)) := by exact_mod_cast h
  have hsub : ((k : ℝ) - 1) ≤ ((k' : ℝ) - 1) := by linarith
  have := Real.sqrt_le_sqrt hsub
  linarith

/-- A `k`-regular `SimpleGraph` `G` is **Ramanujan** if every adjacency-matrix
eigenvalue `λ` (over `ℝ`) satisfies `|λ| = k` (the trivial eigenvalues coming
from `k`-regularity) or `|λ| ≤ 2 · √(k − 1)` (bounded by the Bruhat-Tits
spectral bound).

The eigenvalue condition is stated using `Module.End.HasEigenvalue` on the
linear endomorphism associated to the adjacency matrix. -/
def IsRamanujan
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  G.IsRegularOfDegree k ∧
    ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (G.adjMatrix ℝ)) μ →
      |μ| = (k : ℝ) ∨ |μ| ≤ bruhatTitsBound k

/-- Every adjacency-matrix eigenvalue of a `k`-regular **Ramanujan** graph
satisfies the spectral bound `|λ| ≤ k`. This packages the Frobenius case
and the Bruhat-Tits case into a single absolute-value bound. -/
theorem IsRamanujan.abs_eigenvalue_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 1 ≤ k) (hG : IsRamanujan G k)
    {μ : ℝ} (hμ : Module.End.HasEigenvalue (Matrix.toLin' (G.adjMatrix ℝ)) μ) :
    |μ| ≤ (k : ℝ) := by
  rcases hG.2 μ hμ with h | h
  · exact h.le
  · exact h.trans (bruhatTitsBound_le k hk)

end SimpleGraph
