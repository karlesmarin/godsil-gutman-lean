import Erdos617

/-!
Author: Carles Marín

# Trust report for the Erdős 617 near-Turán arithmetic kernel

Program: query Lean's axiom printer for every public theorem in `Erdos617`.
Purpose: make the trusted footprint of the currently formalised arithmetic
layer visible to readers and downstream users.
Input: the compiled `Erdos617` module.
Output: Lean's own `#print axioms` reports.
Verification status: diagnostic commands only; Lean produces each report.
-/

#print axioms Erdos617.cliqueTemplateEdges
#print axioms Erdos617.crossingEdgesOfInternalComplement
#print axioms Erdos617.defectOfQFourOrFive
#print axioms Erdos617.localCapDefectLowerBound
