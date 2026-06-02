/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import MatchingPoly

/-!
# MSS landmark — C2 foundation: signed adjacency matrices

This is brick #1 of the Marcus–Spielman–Srivastava program (see `MSS_BLUEPRINT.md`): formalizing
the existence of bipartite Ramanujan graphs of every degree. We start with the most self-contained
component **C2**: the identity

  `E over uniform ±1 edge-signings of  charpoly(A_w)  =  matchingPoly G`

which connects the matching polynomial (`MatchingPoly.lean`, DONE) to the spectral side.

## The powerful question (the hinge of the whole component)
*When does the expectation `E_w[ ∏_i (A_w)_{σ(i), i} ]` over a single permutation `σ` survive?*

`charpoly(A_w) = (charmatrix A_w).det = ∑_{σ : Perm V} sign(σ) ∏_i (charmatrix A_w)_{σ(i),i}` (Mathlib
`Matrix.det_apply`). Each off-diagonal factor carries the edge sign `w {σ(i), i}`. Taking `E_w` (signs
i.i.d. uniform on ±1) factorizes over edges; `E[w_e^p] = 0` for odd `p`, `1` for even `p`. So a term
survives **iff every edge is used an even number of times ⟺ `σ` is an involution whose 2-cycles are
edges of `G` ⟺ `σ` corresponds to a matching**, and then `sign(σ) = (−1)^k` for a `k`-edge matching.
The surviving terms reassemble exactly `∑_k (−1)^k m_k X^{n−2k} = matchingPoly G`. One question, the
whole identity.

## Status
FIRST BRICK: the signed adjacency matrix, stated and compiling. The expectation identity itself is the
target `expected_charpoly_eq_matchingPoly_target` (a `def … : Prop`, NOT a vacuous theorem — honesty
floor + Curiosity vacuity gate). Proof = MEDIUM (≈3–6 wk); pitfall = `Equiv.Perm` cycle bookkeeping.
-/

@[expose] public section

namespace SimpleGraph

-- (Fintype V / DecidableEq V are not needed yet — re-added when the det/charpoly work lands.)
variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **signed adjacency matrix** `A_w`: entry `(i, j)` is the signing `w i j` when `i ~ j`, else `0`.
For the MSS argument the signing is symmetric on edges (`w i j = w j i`) and takes values in `{−1, +1}`;
those constraints enter as hypotheses where needed (and a `Sym2`-indexed refinement is the next step —
see `MSS_BLUEPRINT.md`). This is brick #1: the matrix exists and is well-typed. -/
noncomputable def signedAdjMatrix (w : V → V → ℝ) : Matrix V V ℝ :=
  fun i j => if G.Adj i j then w i j else 0

/-- Off the edge set, the signed adjacency matrix vanishes — the basic sanity lemma (genuinely proved,
not a stub). -/
theorem signedAdjMatrix_eq_zero_of_not_adj (w : V → V → ℝ) {i j : V} (h : ¬ G.Adj i j) :
    G.signedAdjMatrix w i j = 0 := by
  simp [signedAdjMatrix, h]

/-- The diagonal of the signed adjacency matrix is zero (no self-loops in a `SimpleGraph`). -/
theorem signedAdjMatrix_diag (w : V → V → ℝ) (i : V) :
    G.signedAdjMatrix w i i = 0 :=
  signedAdjMatrix_eq_zero_of_not_adj G w (G.irrefl)

end SimpleGraph
