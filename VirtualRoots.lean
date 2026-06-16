/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

/-
# Virtual roots of a real polynomial (foundations)

Reverse-engine target (2026-06-16): the *virtual roots* of González-Vega–Lombardi–Mahé and
Coste–Lajous–Lombardi–Roy (J. Pure Appl. Algebra 130 (1998) 49–65; M. Coste, *Generalized
Budan–Fourier theorem and virtual roots*). Confirmed ABSENT from every interactive theorem prover we
could search (Lean/Mathlib, Coq `mathcomp-real-closed` — which has only actual roots + the Thom
encoding —, and the Isabelle AFP — which has the Budan–Fourier *inequality* with multiplicity but not
the virtual roots). This file is the first ITP development of virtual roots, to the best of our
knowledge; the mathematics is Coste's, the formalization is the contribution.

## The object
For a monic real polynomial `P` of degree `d`, the `d` virtual roots
`ρ_{d,1}(P) ≤ … ≤ ρ_{d,d}(P)` are continuous, semialgebraic substitutes for the (possibly missing)
real roots, built recursively from the virtual roots of `P'`:
`ρ_{d,j}(P) = ℛ_d(ρ_{d-1,j-1}(P'/d), ρ_{d-1,j}(P'/d), P)`, where `ℛ_d(a,b,P)` is the point of `[a,b]`
minimising `|P|` on an interval where `P'` keeps a constant sign (the unique root there if one exists,
else the nearer endpoint). They satisfy a Rolle-type interlacing
`ρ_{d,r}(P) ≤ ρ_{d-1,r}(P') ≤ ρ_{d,r+1}(P)`, and the count of virtual roots in `(a,b]` equals the
Budan–Fourier drop `V(a) − V(b)` (`fourierVar`, from `BudanFourier.lean`) — turning that inequality
into an equality.

## Status (milestone 1, in progress)
This file lays the **analytic bedrock** on which `ℛ_d` rests, sorry-free: where the derivative keeps a
constant nonzero sign, the polynomial is strictly monotone (so `|P|` has a single well of a minimum),
and a continuous function attains its minimum on the compact interval. The recursive `ρ`, the
interlacing, and the exact Budan–Fourier count are the next milestones; their statements are recorded
below as the roadmap.
-/
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.Compact
-- (`BudanFourier` will be imported at the exact-count milestone, for `fourierVar`.)

open Polynomial

namespace VirtualRoots

/-! ## The monotonicity bedrock of `ℛ_d`

On an interval where `P'` keeps a constant nonzero sign, `P` is strictly monotone. This is exactly the
hypothesis under which `ℛ_d(a,b,P)` is defined, and it is what makes the minimiser of `|P|` on `[a,b]`
unique: either the single root (if `P` changes sign across the interval) or the endpoint nearer to
zero. The two bricks below are the analytic foundation; they reuse the mean-value engine already used
in `BudanFourier.lean` for the sign analysis. -/

/-- Where the derivative is positive on `[a,b]`, `P` is strictly increasing there. -/
public theorem eval_strictMonoOn_of_derivative_pos {p : Polynomial ℝ} {a b : ℝ}
    (h : ∀ x ∈ Set.Icc a b, 0 < (derivative p).eval x) :
    StrictMonoOn (fun x => p.eval x) (Set.Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) p.continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [Polynomial.deriv]
  exact h x ⟨hx.1.le, hx.2.le⟩

/-- Where the derivative is negative on `[a,b]`, `P` is strictly decreasing there. -/
public theorem eval_strictAntiOn_of_derivative_neg {p : Polynomial ℝ} {a b : ℝ}
    (h : ∀ x ∈ Set.Icc a b, (derivative p).eval x < 0) :
    StrictAntiOn (fun x => p.eval x) (Set.Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b) p.continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [Polynomial.deriv]
  exact h x ⟨hx.1.le, hx.2.le⟩

/-- **`|P|` attains a minimum on a nonempty closed interval.** The existence half of `ℛ_d`: a
continuous function on the compact `[a,b]` reaches its infimum. (Uniqueness of the minimiser comes
from strict monotonicity above, when `P'` keeps a constant sign.) -/
public theorem exists_isMinOn_abs_eval {p : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b) :
    ∃ z ∈ Set.Icc a b, IsMinOn (fun x => |p.eval x|) (Set.Icc a b) z := by
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hcont : ContinuousOn (fun x => |p.eval x|) (Set.Icc a b) :=
    (p.continuous.abs).continuousOn
  obtain ⟨z, hz, hmin⟩ := hcompact.exists_isMinOn hne hcont
  exact ⟨z, hz, hmin⟩

/-! ## Roadmap (next milestones)

The remaining development, to be built on the bedrock above:

* `R d a b P` — the choice `ℛ_d`: on `[a,b]` with `(derivative P)` of constant sign, the unique
  minimiser of `|P|` (root if `P` changes sign, else the nearer endpoint). Existence is
  `exists_isMinOn_abs_eval`; uniqueness is `eval_strictMonoOn_of_derivative_pos` /
  `eval_strictAntiOn_of_derivative_neg`. Extend to semi-infinite intervals via `cauchy bound`.
* `virtualRoot d j P` — the recursive `ρ_{d,j}` (`j ≤ 0 ↦ -∞`, `j > d ↦ +∞`, base `ρ_{1,1}(X-a)=a`).
* `virtualRoot_interlacing` — `ρ_{d,r}(P) ≤ ρ_{d-1,r}(P') ≤ ρ_{d,r+1}(P)` (Coste, Prop. 2.3): the
  Rolle interlacing, and the bridge to the interlacing line (Newton, Heilmann–Lieb).
* `isRoot_iff_eq_virtualRoot` — every actual root of `P` is some `ρ_{d,j}(P)` (Coste, Prop. 2.2).
* `card_virtualRoot_eq_fourierVar` — the exact Budan–Fourier count: the number of virtual roots in
  `(a,b]` (with multiplicity) equals `fourierVar P a - fourierVar P b`, turning the inequality of
  `BudanFourier.budan_fourier` into an equality. This is where `fourierVar`, `Rseq`/`Lseq` and the
  monotonicity of `fourierVar` feed in.
-/

end VirtualRoots
