/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib.RingTheory.PowerSeries.WellKnown
import Ihara.TreeLikeWalks

/-!
# Power-sum generating function — Godsil moment theorem, Stone 4 (core)

The matching side of the moment theorem `matchingPowerSum G k = treeLikeWalkCount G k` needs the
**power-sum generating function** of the roots of the matching polynomial. This file lands the
self-contained, graph-free core of that step, as a formal-power-series identity over any commutative
ring: the generating function `Σ_k p_k Xᵏ` of the power sums `p_k = Σ_{θ∈s} θᵏ` of a multiset `s`
is the sum, over the multiset, of the per-root **geometric series** `Σ_k θᵏ Xᵏ = (1 - θX)⁻¹`:

  `mk (fun k => (s.map (·ᵏ)).sum)  =  Σ_{θ∈s} (1 - θ·X)⁻¹`.

Both pieces are proved sorry-free:
* `geomSeries_mul_one_sub` : `geomSeries a · (1 - C a · X) = 1` — each per-root series inverts
  `1 - aX` (the `a = 1` case is Mathlib's `mk_one_mul_one_sub_eq_one`; we transport it along the
  `rescale a` ring homomorphism, `X ↦ aX`).
* `powerSum_genfun` : the generating-function identity above, by a coefficient-wise swap of the
  multiset sum past the `coeff` linear map.

This is the de-risked target of `research/godsil-numeric/verify_stone4.py` (claim A; claims B/C —
the further reduction to the reversed logarithmic derivative `n - X·q'/q`, `q = reverse μ` — are the
remaining Stone-4 sub-brick, tied to `godsil_resolvent_charpoly_form` on the trace side).

## Numerical anchor (Sage, exact `QQbar`)

`Σ_k p_k zᵏ = n - z·q'/q = reverse_n[z·μ']/reverse_n[μ]` holds exactly across `μ(K4)`, `μ(P4)`,
`x³-2x`, `(x-1)(x-2)(x+3)`, `x²-x-1` (an earlier `CDF` "FAIL" on the last-but-one was a
floating-point artefact at `(-3)¹²`, not a real discrepancy — exact `QQbar` confirms the identity).
-/

open PowerSeries

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The **per-root geometric series** `Σ_k aᵏ Xᵏ ∈ R⟦X⟧`, the formal inverse of `1 - aX`. -/
noncomputable def geomSeries (a : R) : R⟦X⟧ := mk fun k => a ^ k

@[simp] theorem coeff_geomSeries (a : R) (n : ℕ) : coeff n (geomSeries a) = a ^ n :=
  coeff_mk n _

/-- `geomSeries a` is the formal inverse of `1 - aX`: `(Σ_k aᵏ Xᵏ)·(1 - aX) = 1`. Transport of the
unit `a = 1` case (`mk_one_mul_one_sub_eq_one`, the geometric series `(Σ Xᵏ)(1-X)=1`) along the
`rescale a` ring homomorphism `X ↦ aX`. -/
theorem geomSeries_mul_one_sub (a : R) : geomSeries a * (1 - C a * X) = 1 := by
  have key : geomSeries a = rescale a (mk 1) := by
    rw [geomSeries, rescale_mk]; simp
  have hsub : (1 : R⟦X⟧) - C a * X = rescale a (1 - X) := by
    rw [map_sub, map_one, rescale_X]
  rw [key, hsub, ← map_mul, mk_one_mul_one_sub_eq_one R, map_one]

/-- **Power-sum generating function (Stone 4 core).** For a multiset `s : Multiset R`, the
generating function of the power sums `p_k = Σ_{θ∈s} θᵏ` is the multiset-sum of the per-root
geometric series:

  `mk (fun k => (s.map (·ᵏ)).sum)  =  Σ_{θ∈s} geomSeries θ`.

Proof: take the coefficient of `Xⁿ` on both sides. On the left, `coeff_mk` gives `(s.map (·ⁿ)).sum`;
on the right, `coeff n` is additive (`map_multiset_sum`) and `coeff n (geomSeries θ) = θⁿ`, so both
sides are `Σ_{θ∈s} θⁿ`. -/
theorem powerSum_genfun (s : Multiset R) :
    (mk fun k => (s.map (· ^ k)).sum : R⟦X⟧) = (s.map geomSeries).sum := by
  ext n
  rw [coeff_mk, map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun a _ => ?_)
  simp [Function.comp]

end PowerSeries

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- **The matching-side generating function.** Specialising `powerSum_genfun` to the multiset of
complex roots of the matching polynomial: the generating function of `matchingPowerSum G` (Godsil's
`p_k = Σᵢ θᵢᵏ`) is the sum over those roots of the per-root geometric series. This is the matching
side of the moment-theorem bridge in formal-power-series form; the trace side is
`treeLikeWalkCount_eq_sum_pathTree_adjMatrix_pow` welded through `godsil_resolvent_charpoly_form`. -/
theorem matchingPowerSum_genfun :
    (PowerSeries.mk fun k => G.matchingPowerSum k : ℂ⟦X⟧)
      = (((G.matchingPoly.map (algebraMap ℝ ℂ)).roots).map PowerSeries.geomSeries).sum := by
  simpa only [matchingPowerSum] using
    PowerSeries.powerSum_genfun (G.matchingPoly.map (algebraMap ℝ ℂ)).roots

end SimpleGraph
