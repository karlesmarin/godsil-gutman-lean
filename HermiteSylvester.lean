/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

/-
# Hermite–Sylvester real-root counting (P0 scaffold)

The Galois cross of the spectral program: the **signature** of the Hermite quadratic form (the Hankel
matrix of power sums of the roots) equals the number of REAL roots; its rank equals the number of
distinct roots. This is a second, quadratic-form-theoretic way to count the real spectrum — the
formal-verification bedrock under SDP/PSD certification (PSD-ness = signature ≥ 0).

Connection to our work: the entries `N_k = Σ rootⱼ^k` are power sums = `tr(M^k)` for the
multiplication operator — the trace counting we already formalized (matching↔Ihara; LDPC gap law).

P0: definitions (power sums, Hermite/Hankel matrix) + symmetry (sorry-free); the signature/rank
theorems are the next build (Vandermonde diagonalization `H = Σ_r v_r v_rᵀ`).

Reference route: Basu–Pollack–Roy (Hermite's theorem); Mathlib has `Algebra.traceForm` + quadratic
form signature (Sylvester's law) but not this bridge — first in Lean.
-/
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Data.Matrix.Basic

open Polynomial Matrix

namespace HermiteSylvester

/-- The `k`-th power sum of the complex roots of a real polynomial: `N_k = Σ_r r^k`. -/
public noncomputable def powerSum (p : Polynomial ℝ) (k : ℕ) : ℂ :=
  ((p.map (algebraMap ℝ ℂ)).roots.map (· ^ k)).sum

/-- The **Hermite (Hankel) matrix** of `p`: `H i j = N_{i+j}`. Its signature counts real roots, its
rank counts distinct roots (Hermite's theorem; to be proved via the Vandermonde decomposition). -/
public noncomputable def hermiteMatrix (p : Polynomial ℝ) :
    Matrix (Fin p.natDegree) (Fin p.natDegree) ℂ :=
  fun i j => powerSum p ((i : ℕ) + (j : ℕ))

/-- The Hermite matrix is symmetric (`N_{i+j} = N_{j+i}`). -/
public theorem hermiteMatrix_transpose (p : Polynomial ℝ) :
    (hermiteMatrix p)ᵀ = hermiteMatrix p := by
  ext i j
  rw [Matrix.transpose_apply, hermiteMatrix, hermiteMatrix, Nat.add_comm]

end HermiteSylvester
