/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Ihara.PowerSumGenfun

/-!
# Power-sum generating function = reversed logarithmic derivative — Stone 4, claims B/C

`PowerSumGenfun.lean` (Stone 4 core, claim A) showed the power-sum generating function is the
multiset-sum of per-root geometric series:

  `Σ_k p_k Xᵏ  =  Σ_{θ∈s} geomSeries θ`,   `geomSeries θ = (1 - θX)⁻¹`.

The moment-theorem assembly needs to push this one step further, to the **reversed logarithmic
derivative** of the matching polynomial (Stone 4, claims B/C of `verify_stone4.py`):

  `Σ_k p_k zᵏ  =  n - z·q'/q  =  reverse_n[z·μ'] / reverse_n[μ]`,   `q = reverse μ`.

The graph side delivers exactly `↑reverse(μ'(G)) / ↑reverse(μ(G))` (vertex-deletion law
`Σ_v μ(G−v) = μ'` welded through `godsil_resolvent_charpoly_form` + the Stone-3 resolvent diagonal),
so the matching side must be shown equal to it.

## The derivative-free route

Rather than formalise a `PowerSeries` formal derivative and a logarithmic-derivative-of-a-product
lemma, observe that the numerator `reverse_n[z·μ'] = reverse_{n-1}[μ']` is, by the classical
product rule for a polynomial split into linear factors

  `μ' = Σ_{θ∈roots} ∏_{φ ≠ θ} (X - φ)`,

the reverse of `Σ_{θ} ∏_{φ∈s.erase θ} (1 - φ·X)`. That sum is produced **without any derivative** by
the geometric-series cancellation `geomSeries θ · (1 - θX) = 1`:

  `(Σ_{θ∈s} geomSeries θ) · ∏_{θ∈s} (1 - θX)  =  Σ_{θ∈s} ∏_{φ∈s.erase θ} (1 - φX)`.   (★)

This file lands `(★)` — `geomSeries_sum_mul_prod` — the self-contained, graph-free, derivative-free
core of claims B/C, over any commutative ring. The remaining links to the polynomial world,

* **(B2)** `Σ_{θ∈roots} ∏_{φ∈s.erase θ} (X - φ) = derivative μ` (Mathlib product rule), and
* **(B3)** the `reverse` / `Polynomial.coeToPowerSeries` coercion identifying `∏(1 - C φ·X)` with
  `↑reverse(∏(X - φ))` and the erase-sum with `↑reverse(μ')`,

are the documented remaining sub-brick.

## Numerical anchor

`verify_stone4.py` (Sage, exact `QQbar`): `Σ_k p_k zᵏ = reverse_n[z·μ']/reverse_n[μ]` exact across
`μ(K4)`, `μ(P4)`, `x³-2x`, `(x-1)(x-2)(x+3)`, `x²-x-1`.
-/

open PowerSeries

namespace PowerSeries

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- **(★) The geometric-series / reversed-product cancellation — Stone 4, claim B core.**
Multiplying the multiset-sum of per-root geometric series `Σ_{θ∈s} geomSeries θ` by the reversed
factor product `∏_{θ∈s} (1 - θX)` collapses, root by root, to the sum of the "leave-one-out"
products:

  `(Σ_{θ∈s} geomSeries θ) · ∏_{θ∈s} (1 - θX)  =  Σ_{θ∈s} ∏_{φ∈s.erase θ} (1 - φX)`.

The whole product `∏_{θ}(1 - θX)` factors as `(1 - θX) · ∏_{erase θ}` (`Multiset.prod_map_erase`),
and `geomSeries θ · (1 - θX) = 1` (`geomSeries_mul_one_sub`) cancels the singled-out factor, leaving
`∏_{erase θ}`. No formal derivative is needed: the right-hand side is precisely `reverse_{n-1}[μ']`
(the reverse of `μ' = Σ_θ ∏_{φ≠θ}(X - φ)`), the numerator of the reversed logarithmic derivative. -/
theorem geomSeries_sum_mul_prod (s : Multiset R) :
    (s.map geomSeries).sum * (s.map (fun a => 1 - C a * X)).prod
      = (s.map fun a => ((s.erase a).map fun b => 1 - C b * X).prod).sum := by
  rw [← Multiset.sum_map_mul_right]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun a ha => ?_)
  rw [← Multiset.prod_map_erase (f := fun b => 1 - C b * X) ha, ← mul_assoc,
    geomSeries_mul_one_sub, one_mul]

end PowerSeries
