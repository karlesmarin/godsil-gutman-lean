/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Ihara.Bass
import MathlibPR.MatrixWalkCount

/-!
# The Ihara `N_k` counts: `tr(Bᵏ) = number of closed non-backtracking walks`

The Hashimoto operator `B = G.hashimoto` is the `0-1` adjacency matrix of the *non-backtracking
relation* on darts (`d ⇝ e` iff `d.snd = e.fst` and `e ≠ d.symm`). Hence the directed-graph
walk-count `relMatrix_pow_apply` specialises to the Ihara counts: the trace of `Bᵏ` is the number of
closed, non-backtracking, tailless walks of length `k` (rooted at a dart), the combinatorial meaning
of the `N_k` whose generating function is computed in `Ihara/TraceFormula.lean`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **non-backtracking relation** on darts: `d ⇝ e` iff the head of `d` is the tail of `e` and
`e` is not the reverse of `d`. The Hashimoto operator is its `0-1` adjacency matrix. -/
def nbRel (d e : G.Dart) : Prop := d.snd = e.fst ∧ e ≠ d.symm

instance : DecidableRel G.nbRel :=
  fun d e => inferInstanceAs (Decidable (d.snd = e.fst ∧ e ≠ d.symm))

omit [Fintype V] [DecidableRel G.Adj] in
/-- The Hashimoto operator over a commutative ring `R` is the `Nat.cast` image of the `0-1`
adjacency matrix of the non-backtracking relation. -/
theorem hashimoto_eq_map_relMatrix (R : Type*) [CommRing R] :
    G.hashimoto R = (relMatrix G.nbRel).map (Nat.castRingHom R) := by
  ext d e
  simp only [Matrix.map_apply, hashimoto_apply, relMatrix, nbRel]
  split_ifs <;> simp

/-- **The Ihara `N_k` count.** The trace of `Bᵏ` is the natural number of closed non-backtracking
walks of length `k` (summed over the basepoint dart), cast into `R`. This is the combinatorial
identity behind the `N_k = tr(Bᵏ)` generating function of `ihara_Nk_isolated` /
`ihara_Nk_explicit`. -/
theorem trace_hashimoto_pow (R : Type*) [CommRing R] (k : ℕ) :
    ((G.hashimoto R) ^ k).trace
      = ((∑ e : G.Dart, (relWalks G.nbRel k e e).card : ℕ) : R) := by
  have hpow : (G.hashimoto R) ^ k = ((relMatrix G.nbRel) ^ k).map (Nat.castRingHom R) := by
    rw [hashimoto_eq_map_relMatrix G R, ← RingHom.mapMatrix_apply (Nat.castRingHom R), ← map_pow,
      RingHom.mapMatrix_apply]
  have htr : ((relMatrix G.nbRel) ^ k).trace = ∑ e : G.Dart, (relWalks G.nbRel k e e).card := by
    simp only [Matrix.trace, Matrix.diag_apply, relMatrix_pow_apply]
  rw [hpow, ← AddMonoidHom.map_trace, htr]
  simp

end SimpleGraph
