# feat(LinearAlgebra/Matrix): the Cauchy–Binet formula

> Branch: `cauchy-binet-pr` on `karlesmarin/mathlib4` (base `7e31c21f9f`, v4.30.0-rc2 era master).
> One new file + one `Mathlib.lean` line; 194 lines; compiles clean, zero warnings.

## Summary

Adds the classical **Cauchy–Binet formula**, currently absent from Mathlib:

- **`Matrix.det_mul_cauchyBinet`** — for `A : Matrix m n R`, `B : Matrix n m R` over a
  `CommRing`,
  `det (A * B) = ∑ S : {s : Finset n // s.card = card m}, det A_S * det B_S`,
  where `A_S`/`B_S` are the maximal minors with columns/rows `S` taken in increasing order
  (`Finset.orderEmbOfFin`, rows/cols of the square minors indexed via `Fintype.equivFin m`).
- **`Matrix.det_mul_eq_sum_det_submatrix_mul_prod`** — the Leibniz-type expansion of
  `det (A * B)` over *all* index functions `g : m → n` (the formula before grouping by image),
  of independent use.

Degenerate cases are automatic: `card m > card n` makes the sum empty (and the determinant `0`);
`m ≃ n` recovers `det_mul`.

## Why

Cauchy–Binet is the standard bridge between Gram matrices and sums of squared minors
(`det (N Nᵀ) = ∑_S (det N_S)²`), used e.g. by every determinantal proof of the matrix-tree
theorem, by total-unimodularity arguments, and by Lindström–Gessel–Viennot-style reasoning.
Mathlib has `det_mul` and `Matrix.TotallyUnimodular`, but no Cauchy–Binet; no open PR mentions
it (GitHub search, 2026-06-10).

## Design notes

- **Proof shape.** Expand `det (A * B)` over all `g : m → n`
  (`det_mul_eq_sum_det_submatrix_mul_prod`); non-injective `g` vanish (repeated column);
  injective `g` biject with pairs (image subset, column relabelling) via `Finset.sum_bij`.
  The key step (`private fiberSum`): for a fixed column indexing, summing the plain
  `B`-products against the sign carried by the `A`-minor *reassembles* `det B_S` by the Leibniz
  formula read backwards — no explicit sign bookkeeping survives to the main proof.
- The `LinearOrder n` hypothesis is used only to *name* the sorted minors
  (`orderEmbOfFin`); the auxiliary lemmas (`cbPerm`, `cbPerm_spec`,
  `image_comp_orderEmbOfFin`, `card_image_univ`) are `private`.
- Over any `CommRing`; no field hypothesis.

## Prior art (stated for the reviewers)

An independent Lean 4 formalization of Cauchy–Binet exists in the
[facebookresearch/faabian `algebraic-combinatorics`](https://github.com/faabian/algebraic-combinatorics)
project (Grinberg-textbook formalization; blueprint §5.2), outside Mathlib, with a different
architecture (explicit permutation extraction/reconstruction). That project states no
upstreaming plans. This PR's proof is independent and was written against Mathlib's `Matrix`
API directly.

## Files / placement

- `Mathlib/LinearAlgebra/Matrix/Determinant/CauchyBinet.lean` (new)
- `Mathlib.lean` (+1 import line)

## Verification

- `lake env lean` on the file: clean, zero warnings.
- `#print axioms Matrix.det_mul_cauchyBinet` → `propext, Classical.choice, Quot.sound`.
- Statement validated numerically in exact arithmetic (SageMath) on a `2×3 · 3×2` pair and,
  via its downstream use (matrix-tree), on 40 random graphs × all `(n−1)`-subsets.
  Downstream context: DOI [10.5281/zenodo.20629746](https://doi.org/10.5281/zenodo.20629746).
