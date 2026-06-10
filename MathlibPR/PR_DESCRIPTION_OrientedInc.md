# feat(Combinatorics/SimpleGraph): oriented incidence matrix and the Laplacian factorization

> Branch: `oriented-inc-pr` on `karlesmarin/mathlib4` (base `7e31c21f9f`, v4.30.0-rc2 era master).
> One new file + one `Mathlib.lean` line; 152 lines; compiles clean, zero warnings.
> Independent of the `cauchy-binet-pr` branch (same base, no shared files beyond `Mathlib.lean`).

## Summary

Adds the **oriented incidence matrix** of a simple graph and the standard **Gram factorization
of the graph Laplacian**:

- **`SimpleGraph.orientedIncMatrix R : Matrix α (Sym2 α) R`** — in the column of an edge
  `e = s(u, w)` with `u < w`: `+1` at row `w` (the larger endpoint), `-1` at row `u`, `0`
  elsewhere; columns of non-edges are zero. Orientation induced by a `LinearOrder` on the
  vertex type.
- **`SimpleGraph.orientedIncMatrix_mul_transpose`** — `N * Nᵀ = G.lapMatrix R` (= `D − A`).
- Supporting API mirroring `incMatrix`: `orientedIncMatrix_apply`,
  `orientedIncMatrix_of_notMem_incidenceSet`, `orientedIncMatrix_mul_self`
  (the square of an entry is the unoriented `incMatrix` entry), and the two sign lemmas
  `orientedIncMatrix_apply_mul_apply_of_adj` (product of the two endpoint entries = `-1`),
  `orientedIncMatrix_apply_add_apply_of_adj` (their sum = `0`), plus
  `orientedIncMatrix_apply_mul_apply_of_ne` (vanishing away from the common edge).

## Why

Mathlib has the unoriented `G.incMatrix`, whose Gram matrix is the **signless** Laplacian
`D + A` (`incMatrix_mul_transpose_diag` ff.), and it has `G.lapMatrix = D − A` with its kernel
theory — but no object connecting the two. The oriented incidence matrix is that object, and
`N Nᵀ = D − A` is the factorization behind: positive semidefiniteness of the Laplacian as a
Gram fact, Kirchhoff/matrix-tree determinant arguments (via Cauchy–Binet on the reduced
factorization), and total unimodularity of incidence matrices.

## Design notes

- The fixed smaller→larger orientation is harmless: any orientation gives the same Gram matrix
  (each edge contributes `(±1)²` on the diagonal and `(+1)(−1)` off it). This is stated in the
  module docstring; no orientation-genericity machinery is introduced.
- The headline proof is entrywise: the diagonal reduces to `sum_incMatrix_apply` (= degree)
  through `orientedIncMatrix_mul_self`; an off-diagonal `(u, w)` entry is supported on the
  single column `s(u, w)`, handled by `Finset.sum_eq_single` and the sign lemmas.
- `[Ring R]` for the API section (signs need negation); the definition itself only needs
  `[Zero R] [One R] [Neg R]`.

## Files / placement

- `Mathlib/Combinatorics/SimpleGraph/OrientedIncMatrix.lean` (new)
- `Mathlib.lean` (+1 import line)

## Verification

- `lake env lean` on the file: clean, zero warnings.
- `#print axioms SimpleGraph.orientedIncMatrix_mul_transpose` → 3 standard axioms.
- The factorization and the downstream matrix-tree chain were validated numerically in exact
  arithmetic (SageMath) before formalization.
  Downstream context: DOI [10.5281/zenodo.20629746](https://doi.org/10.5281/zenodo.20629746).
