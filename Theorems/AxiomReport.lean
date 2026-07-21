import Theorems.TransversalMatroid
import Theorems.TransversalObstruction

/-!
Author: Carles Marín

Program: trust-report query for the transversal-matroid formalization.
Purpose: ask Lean to list the axioms used by the headline theorems.
Input: the compiled `Theorems.TransversalMatroid` and
  `Theorems.TransversalObstruction` modules.
Output: Lean's `#print axioms` report for `transversalMatroid_indep`,
  `partialTransversal_augmentation` and `insert_iff_not_subset_maxTight`
  and `mem_closure_iff_subset_maxTight`.
Verification status: diagnostic command; Lean itself produces the report.
-/

#print axioms Theorems.TransversalMatroid.partialTransversal_augmentation
#print axioms Theorems.TransversalMatroid.transversalMatroid_indep
#print axioms Theorems.TransversalMatroid.tight_union_and_inter
#print axioms Theorems.TransversalMatroid.maxTight_isTight
#print axioms Theorems.TransversalMatroid.insert_iff_not_subset_maxTight
#print axioms Theorems.TransversalMatroid.mem_closure_iff_subset_maxTight
