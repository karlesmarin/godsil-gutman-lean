import Lean.Elab.Tactic.Omega

/-!
Author: Carles Marín

# A near-Turán arithmetic kernel for Erdős problem 617

Program: the machine-checked arithmetic endgame of a proposed reduction for
the 5-colour `K_26` instance of Erdős--Gyárfás balanced colouring problem
(Erdős problem 617).
Purpose: verify the exact defect counts once the finite graph-theoretic
reduction has supplied a `6+5+5+5+5` block partition.
Input: a 60-edge colour class and the number `q` of complement edges internal
to those blocks; the structural reduction gives `q = 4` or `q = 5`.
Output: the block template has 55 edges, the local six-set cap forces defect
at least 13, and `q ∈ {4,5}` forces defect exactly 13 or 15.
Verification status: every theorem in this file is `sorry`-free and checked by
the Lean 4 kernel. The preceding graph-structural reduction, which invokes
Füredi's exact stability theorem, is intentionally not postulated here.

Mathematical contract.  A `6+5+5+5+5` union-of-cliques template has
`binom(6,2) + 4*binom(5,2) = 55` edges. If `q` of these internal pairs are
absent from a 60-edge colour graph, there are `5+q` crossing colour edges and
the symmetric-difference defect is `q+(5+q)`. A locally balanced colouring
has at most 11 edges on every six-set, giving at most 51 internal edges and
therefore defect at least 13.
-/

namespace Erdos617

/-- The `6+5+5+5+5` union-of-cliques template has 55 internal pairs. -/
theorem cliqueTemplateEdges : 55 = 15 + 4 * 10 := by
  omega

/-- With at most 55 internal template pairs, `q` missing internal colour
pairs force exactly `5+q` crossing colour edges in a 60-edge colour class. -/
theorem crossingEdgesOfInternalComplement (q : Nat) (hq : q ≤ 55) :
    60 - (55 - q) = 5 + q := by
  omega

/-- The finite arithmetic conclusion of the near-Turán reduction. -/
theorem defectOfQFourOrFive (q : Nat) (hq : q = 4 ∨ q = 5) :
    q + (60 - (55 - q)) = 13 ∨ q + (60 - (55 - q)) = 15 := by
  rcases hq with rfl | rfl <;> omega

/-- The weaker universal local-cap conclusion for every 60-edge class:
at most 51 internal colour edges force at least 13 defect entries. -/
theorem localCapDefectLowerBound (internalColourEdges : Nat)
    (hInternal : internalColourEdges ≤ 51) :
    13 ≤ 115 - 2 * internalColourEdges := by
  omega

end Erdos617
