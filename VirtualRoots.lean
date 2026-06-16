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
public import Mathlib.Topology.Order.IntermediateValue
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

/-! ## The choice operator `ℛ_d` (milestone 1, brick 2)

`R p a b` is Coste's `ℛ_d(a,b,P)`: a point of `[a,b]` minimising `|P|`. On an interval where `P'`
keeps a constant sign (so `P` is strictly monotone, by the bedrock above) this minimiser is unique,
and equals the unique root of `P` there when one exists, otherwise the nearer endpoint. We define it
by choosing a minimiser (which exists by `exists_isMinOn_abs_eval`) and prove the two properties that
matter downstream: it **lands in `[a,b]`** (the engine of the Rolle interlacing) and it **is a root of
`P` whenever `P` has one in `[a,b]`** (so virtual roots extend actual roots, Coste's Prop. 2.2). -/

/-- **The choice operator `ℛ_d(a,b,P)`**: a minimiser of `|P|` on `[a,b]` (junk value `a` if `b<a`). -/
public noncomputable def R (p : Polynomial ℝ) (a b : ℝ) : ℝ :=
  if hab : a ≤ b then (exists_isMinOn_abs_eval (p := p) hab).choose else a

/-- `ℛ_d(a,b,P)` lands in `[a,b]`. This single fact yields the Rolle interlacing of virtual roots,
since `ρ_{d,j}(P) = ℛ_d(ρ_{d-1,j-1}(P'),ρ_{d-1,j}(P'),P)` then lies between consecutive virtual roots
of `P'`. -/
public theorem R_mem {p : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b) : R p a b ∈ Set.Icc a b := by
  rw [R, dif_pos hab]
  exact (exists_isMinOn_abs_eval (p := p) hab).choose_spec.1

/-- `ℛ_d(a,b,P)` minimises `|P|` on `[a,b]`. -/
public theorem R_isMinOn {p : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b) :
    IsMinOn (fun x => |p.eval x|) (Set.Icc a b) (R p a b) := by
  rw [R, dif_pos hab]
  exact (exists_isMinOn_abs_eval (p := p) hab).choose_spec.2

/-- **`ℛ_d` captures actual roots.** If `P` vanishes somewhere in `[a,b]`, then `ℛ_d(a,b,P)` is a root
of `P`: the minimum of `|P|` is then `0`, so the minimiser is a zero. (No monotonicity needed; this is
the half of Coste's Prop. 2.2 saying virtual roots extend the actual ones.) -/
public theorem R_eval_eq_zero_of_exists {p : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∃ z ∈ Set.Icc a b, p.eval z = 0) : p.eval (R p a b) = 0 := by
  obtain ⟨z, hz, hpz⟩ := h
  have hle : |p.eval (R p a b)| ≤ |p.eval z| := (isMinOn_iff.mp (R_isMinOn (p := p) hab)) z hz
  rw [hpz, abs_zero] at hle
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

/-! ## The root case of `ℛ_d` (milestone 1, brick 3a)

When `P` changes sign across the interval, `ℛ_d(a,b,P)` is an actual root of `P`. This is the case
that makes a virtual root coincide with a real root, and it is what the recursive `ρ` produces on each
`P'`-monotone interval on which `P` crosses zero. It follows from the intermediate value theorem
(existence of a root) and `R_eval_eq_zero_of_exists`. -/

/-- If `P(a) ≤ 0 ≤ P(b)` on `[a,b]`, then `ℛ_d(a,b,P)` is a root of `P`. -/
public theorem R_eval_eq_zero_of_le_zero_le {p : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (ha : p.eval a ≤ 0) (hb : 0 ≤ p.eval b) : p.eval (R p a b) = 0 := by
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
  obtain ⟨c, hc, hpc⟩ := intermediate_value_Icc hab hcont ⟨ha, hb⟩
  exact R_eval_eq_zero_of_exists hab ⟨c, hc, hpc⟩

/-- If `P(b) ≤ 0 ≤ P(a)` on `[a,b]`, then `ℛ_d(a,b,P)` is a root of `P`. -/
public theorem R_eval_eq_zero_of_ge_zero_ge {p : Polynomial ℝ} {a b : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ p.eval a) (hb : p.eval b ≤ 0) : p.eval (R p a b) = 0 := by
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
  obtain ⟨c, hc, hpc⟩ := intermediate_value_Icc' hab hcont ⟨hb, ha⟩
  exact R_eval_eq_zero_of_exists hab ⟨c, hc, hpc⟩

/-! ## The recursive virtual roots (milestone 1, brick 3b)

On a bracketing interval `[lo,hi]` that contains all roots of the whole derivative tower (take
`lo = -M`, `hi = M` with `M` a Cauchy bound `Polynomial.cauchyBound`, design (B)), the `d` virtual
roots of `P` are built from the `d-1` virtual roots of `P'`: the breakpoints
`lo, ρ_{d-1,1}(P'), …, ρ_{d-1,d-1}(P'), hi` cut `[lo,hi]` into `d` intervals, on each of which `P'`
keeps a constant sign, and `ρ_{d,j}(P)` is `ℛ_d` applied to the `j`-th. Working on the finite `[lo,hi]`
keeps everything over `ℝ` and reuses `R`/`R_mem`/`R_eval_*` verbatim. -/

/-- **The recursive virtual roots** of `p` on the bracketing interval `[lo,hi]`, built from the virtual
roots of `derivative p` by `ℛ_d` on each `P'`-monotone subinterval. A degree-`0` polynomial has none;
well-founded on `natDegree` (`natDegree_derivative_lt`). -/
public noncomputable def vroots (lo hi : ℝ) (p : Polynomial ℝ) : List ℝ :=
  if h : p.natDegree = 0 then []
  else
    let bps := lo :: (vroots lo hi (derivative p) ++ [hi])
    List.zipWith (R p) bps bps.tail
  termination_by p.natDegree
  decreasing_by exact natDegree_derivative_lt h

/-- Exact derivative degree in characteristic zero: `deg(P') = deg P − 1` for `deg P ≥ 1`. -/
public theorem natDegree_derivative_eq {p : Polynomial ℝ} (hp : 0 < p.natDegree) :
    (derivative p).natDegree = p.natDegree - 1 :=
  natDegree_eq_of_degree_eq_some (degree_derivative_eq p hp)

/-- **`vroots` has the right length**: a degree-`d` polynomial has exactly `d` virtual roots. -/
public theorem vroots_length (lo hi : ℝ) (p : Polynomial ℝ) :
    (vroots lo hi p).length = p.natDegree := by
  induction p using vroots.induct (lo := lo) (hi := hi) with
  | case1 p h => rw [vroots, dif_pos h, h]; rfl
  | case2 p h ih =>
    rw [vroots, dif_neg h]
    simp only [List.tail_cons, List.length_zipWith, List.length_cons, List.length_append,
      List.length_singleton, List.length_nil]
    rw [ih, natDegree_derivative_eq (Nat.pos_of_ne_zero h)]
    omega

/-- **Virtual roots come out sorted (combinatorial core of the interlacing).** If the breakpoints are
sorted, the `ℛ_d`-values between consecutive ones are sorted too: each `R p bps[j] bps[j+1]` lies in
`[bps[j], bps[j+1]]` (by `R_mem`), and consecutive values are separated by the shared breakpoint
`bps[j+1]` — exactly the Rolle interlacing `ρ_{d,j} ≤ bps[j+1] ≤ ρ_{d,j+1}`. -/
public theorem isChain_zipWith_R (p : Polynomial ℝ) : ∀ (bps : List ℝ),
    List.IsChain (· ≤ ·) bps → List.IsChain (· ≤ ·) (List.zipWith (R p) bps bps.tail)
  | [], _ => by simp
  | [_], _ => by simp
  | x :: y :: l, h => by
    obtain ⟨hxy, hrest⟩ := List.isChain_cons_cons.mp h
    have ih := isChain_zipWith_R p (y :: l) hrest
    cases l with
    | nil => simp
    | cons z l' =>
      obtain ⟨hyz, _⟩ := List.isChain_cons_cons.mp hrest
      have hbound : R p x y ≤ R p y z :=
        le_trans (Set.mem_Icc.mp (R_mem hxy)).2 (Set.mem_Icc.mp (R_mem hyz)).1
      have hgoal : List.zipWith (R p) (x :: y :: z :: l') (x :: y :: z :: l').tail
          = R p x y :: R p y z :: List.zipWith (R p) (z :: l') (z :: l').tail := by
        simp [List.zipWith_cons_cons]
      rw [hgoal, List.isChain_cons_cons]
      refine ⟨hbound, ?_⟩
      simpa [List.zipWith_cons_cons] using ih

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
