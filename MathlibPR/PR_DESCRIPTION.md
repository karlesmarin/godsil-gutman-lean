# feat(LinearAlgebra/Matrix): Jacobi's formula and Newton's identity for matrix traces

## Summary

Adds two classical, elementary facts about square matrices over a commutative ring that were
missing from Mathlib:

- **`Matrix.derivative_det`** — Jacobi's formula `(det M)′ = tr(adjugate M · M′)` for a matrix `M`
  of polynomials (`Polynomial.derivative`). Mathlib previously had only the *analytic* derivative of
  `det` (between normed spaces); this is the purely algebraic version over an arbitrary `CommRing`.
- **`Matrix.charpolyRev_logDeriv`** — Newton's identity for matrix traces:
  `(charpolyRev M)′ = - charpolyRev M · ∑ₖ tr(Mᵏ⁺¹) Xᵏ` in `R⟦X⟧`. Equivalently
  `∑_{k≥1} tr(Mᵏ) Xᵏ = -X · (charpolyRev M)′ / charpolyRev M`. Eigenvalue-free, over any `CommRing`.

Supporting public API (the **resolvent series** `∑ₖ Mᵏ Xᵏ`):
`Matrix.resolventSeries`, `coeff_resolventSeries`, `trace_resolventSeries`,
`resolventSeries_fixedPoint`, `one_sub_smul_mul_resolventSeries`,
`smul_resolventSeries_eq_adjugate`, `trace_resolventSeries_mul`.

## Why

- Mathlib's Newton identities (`RingTheory/MvPolynomial/Symmetric/NewtonIdentities`) only cover the
  abstract symmetric polynomials. The **matrix-trace form** — the bridge from
  `tr(Mᵏ)` to the characteristic-polynomial coefficients — was absent; only the linear coefficient
  existed, as `Matrix.coeff_charpolyRev_eq_neg_trace`. `charpolyRev_logDeriv` is the all-orders
  statement and specialises to that lemma at the `X¹` coefficient.
- Jacobi's formula is foundational infrastructure: the derivative of a characteristic polynomial,
  Faddeev–LeVerrier, perturbation of eigenvalues, the Ihara/graph zeta `N_k` counts, etc.

## Design notes

- The proof of Newton's identity is **eigenvalue-free**: no splitting field, no algebraic closure.
  It factors through the resolvent series `(1 - X·M)⁻¹ = ∑ₖ Mᵏ Xᵏ` and `adjugate F = det F · F⁻¹`
  in `Matrix n n R⟦X⟧`, then transports the polynomial Jacobi identity along the coercion
  `R[X] → R⟦X⟧`.
- Jacobi's formula is proved by the column-wise Leibniz rule (`derivative_det_eq_sum_updateCol`,
  kept `private`) and Cramer's rule (`cramer_eq_adjugate_mulVec`).

## Files

- `Mathlib/LinearAlgebra/Matrix/Charpoly/JacobiNewton.lean` (new).

Sorry-free; axioms = `[propext, Classical.choice, Quot.sound]`. Compiles clean against current
Mathlib with zero linter warnings.
