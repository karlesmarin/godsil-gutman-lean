/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-!
# The graph trace formula — Part III (the matching ↔ Ihara bridge)

This file begins Part III: the bridge uniting the two sides formalized earlier, the matching
polynomial (the **tree / Plancherel** side, in `MSS`) and the Hashimoto non-backtracking operator
(the **cycle / π₁** side, in `Ihara/Bass.lean`). The bridge is a sharp trace-formula gap law.

## The locked statement (numerically verified, NOT yet proved in Lean)

With `A` the adjacency matrix, `B` the Hashimoto operator (`Ihara/Bass.lean`), and
`p_k = Σ θᵢᵏ` the power sums of the matching-polynomial roots (Godsil's *tree-like walk* count),
define `gap_k := tr(Aᵏ) − p_k`. Then, for a finite graph of girth `g`:

  `gap_k = tr(Bᵏ)`  for all `1 ≤ k ≤ g+1`,  and this is SHARP (it fails at `k = g+2`);

  the first nonzero value is at `k = g`:  `tr(B^g) = 2·g·(#shortest cycles)`.

Independently re-verified (Python, `research/_tmp/traceformula_lock.py`) on
`K₃, C₅, K₄, K_{3,3}, Q₃, Petersen` — all six match, sharp at `g+2`, first gaps
`120, 72, 48, 24` (Petersen, K₃₃, Q₃, K₄) confirmed. This is CLASSICAL mathematics (Godsil's
moment theorem + the non-backtracking trace); the contribution is the *formalization* — the first
ITP record of the bridge, joining the two existing Lean files. No new theorem is claimed.

## Roadmap (the three pieces)

1. `tr(Aᵏ) = #closed walks of length k` — **this file** (free from
   `adjMatrix_pow_apply_eq_card_walk`).
2. `N_k = tr(Bᵏ) = #closed non-backtracking walks` — needs a non-backtracking-walk count
   (Mathlib lacks it); `B` is in `Ihara/Bass.lean`.
3. **`p_k = Σ θᵢᵏ = #closed tree-like walks` — Godsil's moment theorem. THE HARD BRICK**
   (Mathlib has no tree-like walks); plus the girth-threshold argument tying 1–3 together.

This file lands piece 1.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Piece 1 of the trace formula.** The trace of the `k`-th power of the adjacency matrix counts
the closed walks of length `k`: `tr(Aᵏ) = Σ_v #{closed walks of length k at v}`. -/
theorem trace_adjMatrix_pow (k : ℕ) :
    (G.adjMatrix ℕ ^ k).trace = ∑ v : V, #(G.finsetWalkLength k v v) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_congr rfl fun v _ => by
    rw [adjMatrix_pow_apply_eq_card_walk, Nat.cast_id, card_set_walk_length_eq]

end SimpleGraph
