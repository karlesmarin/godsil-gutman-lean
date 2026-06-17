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

## Status
The structural theory of the `ℛ_d` virtual roots is complete and sorry-free: existence and the count
(`= degree`), sortedness, containment in `[lo,hi]`, the localization of each root between its
breakpoints, and the Rolle interlacing `ρ_{d,r}(P) ≤ ρ_{d-1,r}(P') ≤ ρ_{d,r+1}(P)` (Coste, Prop. 2.3).
The exact Budan–Fourier count (number of virtual roots in `(a,b]` `= V(a) - V(b)`), which fuses this
construction with the `fourierVar` of `BudanFourier.lean`, is the natural sequel and is left as future
work; see the closing note.
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

/-- **The `vroots` recursion, exposed.** For `deg p ≥ 1`, the virtual roots are `ℛ_d` applied to
consecutive breakpoints `lo :: (vroots p' ++ [hi])`. Stated so other modules can unfold the (non-
`@[expose]`) `vroots` definition through a lemma. -/
public theorem vroots_eq_zipWith {lo hi : ℝ} {p : Polynomial ℝ} (hd : p.natDegree ≠ 0) :
    vroots lo hi p
      = List.zipWith (R p) (lo :: (vroots lo hi (derivative p) ++ [hi]))
          (lo :: (vroots lo hi (derivative p) ++ [hi])).tail := by
  rw [vroots, dif_neg hd]

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

/-! ## The breakpoints invariant (milestone 1, brick 4: the interlacing)

The recursion that builds `vroots` is driven by one invariant: the augmented list
`lo :: (vroots lo hi p ++ [hi])` — the breakpoints that cut `[lo,hi]` for the polynomial *one degree
up* — is sorted, and every virtual root lands in `[lo,hi]`. The two facts are mutually dependent (a
breakpoint list is sorted only if its members lie in range, and an `ℛ_d`-value lies in range only
between sorted breakpoints), so they are proved together by one induction down the derivative tower.
The chain half is the Rolle interlacing `ρ_{d,r}(P) ≤ ρ_{d-1,r}(P') ≤ ρ_{d,r+1}(P)` in list form. -/

/-- Every `ℛ_d`-value between consecutive breakpoints lands in `[lo,hi]`, provided the breakpoints are
sorted and themselves lie in `[lo,hi]`. The membership engine, by the same structural recursion as
`isChain_zipWith_R`. -/
private theorem zipWith_R_mem_Icc (p : Polynomial ℝ) {lo hi : ℝ} : ∀ (bps : List ℝ),
    List.IsChain (· ≤ ·) bps → (∀ w ∈ bps, w ∈ Set.Icc lo hi) →
    ∀ x ∈ List.zipWith (R p) bps bps.tail, x ∈ Set.Icc lo hi
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | x :: y :: l, h, hmem => by
    obtain ⟨hxy, hrest⟩ := List.isChain_cons_cons.mp h
    have hzip : List.zipWith (R p) (x :: y :: l) (x :: y :: l).tail
        = R p x y :: List.zipWith (R p) (y :: l) (y :: l).tail := by
      simp [List.zipWith_cons_cons]
    rw [hzip]
    intro z hz
    rw [List.mem_cons] at hz
    rcases hz with rfl | hz
    · have hx := Set.mem_Icc.mp (hmem x (by simp))
      have hy := Set.mem_Icc.mp (hmem y (by simp))
      have hr := Set.mem_Icc.mp (R_mem (p := p) hxy)
      exact Set.mem_Icc.mpr ⟨le_trans hx.1 hr.1, le_trans hr.2 hy.2⟩
    · exact zipWith_R_mem_Icc p (y :: l) hrest
        (fun w hw => hmem w (List.mem_cons_of_mem x hw)) z hz

/-- **The breakpoints invariant.** For `lo ≤ hi`, the augmented breakpoint list
`lo :: (vroots lo hi p ++ [hi])` is sorted, and every virtual root of `p` lies in `[lo,hi]`. Proved by
one induction down the tower: the breakpoints for `p` are exactly this list for `derivative p`. -/
public theorem vroots_chain_mem (lo hi : ℝ) (hab : lo ≤ hi) (p : Polynomial ℝ) :
    List.IsChain (· ≤ ·) (lo :: (vroots lo hi p ++ [hi]))
      ∧ (∀ x ∈ vroots lo hi p, x ∈ Set.Icc lo hi) := by
  induction p using vroots.induct (lo := lo) (hi := hi) with
  | case1 p h =>
    refine ⟨?_, ?_⟩
    · rw [vroots, dif_pos h]
      simp only [List.nil_append]
      exact List.isChain_cons_cons.mpr ⟨hab, List.isChain_singleton hi⟩
    · rw [vroots, dif_pos h]; simp
  | case2 p h ih =>
    obtain ⟨ihchain, ihmem⟩ := ih
    have hbmem : ∀ w ∈ lo :: (vroots lo hi (derivative p) ++ [hi]), w ∈ Set.Icc lo hi := by
      intro w hw
      rw [List.mem_cons, List.mem_append, List.mem_singleton] at hw
      rcases hw with rfl | (hw | rfl)
      · exact Set.mem_Icc.mpr ⟨le_rfl, hab⟩
      · exact ihmem w hw
      · exact Set.mem_Icc.mpr ⟨hab, le_rfl⟩
    have hmem : ∀ x ∈ vroots lo hi p, x ∈ Set.Icc lo hi := by
      rw [vroots, dif_neg h]; exact zipWith_R_mem_Icc p _ ihchain hbmem
    have hchainV : List.IsChain (· ≤ ·) (vroots lo hi p) := by
      rw [vroots, dif_neg h]; exact isChain_zipWith_R p _ ihchain
    refine ⟨?_, hmem⟩
    have happend : List.IsChain (· ≤ ·) (vroots lo hi p ++ [hi]) := by
      refine hchainV.append (List.isChain_singleton hi) ?_
      intro a ha b hb
      have hain : a ∈ vroots lo hi p := List.mem_of_mem_getLast? ha
      rw [List.head?_cons, Option.mem_some_iff] at hb
      subst hb
      exact (Set.mem_Icc.mp (hmem a hain)).2
    refine happend.cons ?_
    intro y hy
    have hyin : y ∈ vroots lo hi p ++ [hi] := List.mem_of_mem_head? hy
    rw [List.mem_append, List.mem_singleton] at hyin
    rcases hyin with hyin | rfl
    · exact (Set.mem_Icc.mp (hmem y hyin)).1
    · exact hab

/-- **The virtual roots come out sorted on `[lo,hi]`** (Rolle interlacing, list form): the breakpoint
list `lo :: (vroots lo hi p ++ [hi])` for the next degree up is a chain. -/
public theorem vroots_isChain (lo hi : ℝ) (hab : lo ≤ hi) (p : Polynomial ℝ) :
    List.IsChain (· ≤ ·) (lo :: (vroots lo hi p ++ [hi])) :=
  (vroots_chain_mem lo hi hab p).1

/-- **Every virtual root lies in the bracketing interval** `[lo,hi]`. -/
public theorem vroots_subset_Icc (lo hi : ℝ) (hab : lo ≤ hi) (p : Polynomial ℝ) :
    ∀ x ∈ vroots lo hi p, x ∈ Set.Icc lo hi :=
  (vroots_chain_mem lo hi hab p).2

/-! ## The index-form interlacing (milestone 1, brick 5: Coste Prop. 2.3)

The sorted invariant says the virtual roots are ordered; the sharper statement is *where* each one
sits. With `bps = lo :: (vroots lo hi P' ++ [hi])` the breakpoints cutting `[lo,hi]` for `P`, the
`r`-th virtual root of `P` lands in `[bps[r], bps[r+1]]` — that is `ℛ_d` landing in its own interval,
read index by index. Since the interior breakpoints `bps[r+1]` are exactly the virtual roots of `P'`,
this is the Rolle interlacing `ρ_{d,r}(P) ≤ ρ_{d-1,r}(P') ≤ ρ_{d,r+1}(P)`. -/

/-- **Each virtual root lies between its two breakpoints** (Coste's localization of `ρ_{d,r}`): for
`bps = lo :: (vroots lo hi P' ++ [hi])`, one has `bps[r] ≤ (vroots lo hi P)[r] ≤ bps[r+1]`. -/
public theorem vroots_getElem_mem (lo hi : ℝ) (hab : lo ≤ hi) (p : Polynomial ℝ)
    (r : ℕ) (hr : r < (vroots lo hi p).length)
    (hb : r + 1 < (lo :: (vroots lo hi (derivative p) ++ [hi])).length) :
    (lo :: (vroots lo hi (derivative p) ++ [hi]))[r]'(Nat.lt_of_succ_lt hb) ≤ (vroots lo hi p)[r]
      ∧ (vroots lo hi p)[r] ≤ (lo :: (vroots lo hi (derivative p) ++ [hi]))[r + 1]'hb := by
  have hd : p.natDegree ≠ 0 := by
    intro h0; rw [vroots_length, h0] at hr; exact absurd hr (Nat.not_lt_zero r)
  have hvr : vroots lo hi p
      = List.zipWith (R p) (lo :: (vroots lo hi (derivative p) ++ [hi]))
          (lo :: (vroots lo hi (derivative p) ++ [hi])).tail := by
    rw [vroots, dif_neg hd]
  have hchain : List.IsChain (· ≤ ·) (lo :: (vroots lo hi (derivative p) ++ [hi])) :=
    vroots_isChain lo hi hab (derivative p)
  set bps := lo :: (vroots lo hi (derivative p) ++ [hi]) with hbps
  have hadj : bps[r]'(Nat.lt_of_succ_lt hb) ≤ bps[r + 1]'hb := hchain.getElem r hb
  have hzip : (vroots lo hi p)[r] = R p (bps[r]'(Nat.lt_of_succ_lt hb)) (bps[r + 1]'hb) := by
    simp only [hvr, List.getElem_zipWith, List.getElem_tail]
  have hmem := Set.mem_Icc.mp (R_mem (p := p) hadj)
  rw [← hzip] at hmem
  exact hmem

/-- **The Rolle interlacing of virtual roots** (Coste, Prop. 2.3), in list/index form:
`ρ_{d,r}(P) ≤ ρ_{d-1,r}(P') ≤ ρ_{d,r+1}(P)`. Each virtual root of `P'` is wedged between two
consecutive virtual roots of `P`, because the `P'`-roots are exactly the interior breakpoints that
`ℛ_d` interpolates. -/
public theorem vroots_interlacing (lo hi : ℝ) (hab : lo ≤ hi) (p : Polynomial ℝ)
    (r : ℕ) (hr' : r < (vroots lo hi (derivative p)).length)
    (hrp : r + 1 < (vroots lo hi p).length) :
    (vroots lo hi p)[r]'(Nat.lt_of_succ_lt hrp) ≤ (vroots lo hi (derivative p))[r]'hr'
      ∧ (vroots lo hi (derivative p))[r]'hr' ≤ (vroots lo hi p)[r + 1]'hrp := by
  have hlenbps : (lo :: (vroots lo hi (derivative p) ++ [hi])).length
      = (vroots lo hi (derivative p)).length + 2 := by
    simp [List.length_append]
  have hb : r + 1 < (lo :: (vroots lo hi (derivative p) ++ [hi])).length := by
    rw [hlenbps]; omega
  have hb2 : r + 1 + 1 < (lo :: (vroots lo hi (derivative p) ++ [hi])).length := by
    rw [hlenbps]; omega
  have hL := vroots_getElem_mem lo hi hab p r (Nat.lt_of_succ_lt hrp) hb
  have hR := vroots_getElem_mem lo hi hab p (r + 1) hrp hb2
  have hbeq : (lo :: (vroots lo hi (derivative p) ++ [hi]))[r + 1]'hb
      = (vroots lo hi (derivative p))[r]'hr' := by
    simp [List.getElem_append]
    exact dif_pos hr'
  refine ⟨?_, ?_⟩
  · rw [← hbeq]; exact hL.2
  · rw [← hbeq]; exact hR.1

/-! ## What is established here, and what comes next

**Established (sorry-free, this file):** the virtual roots of a real polynomial as the recursive
`ℛ_d`-construction of Coste, with their structural theory.
* `R` (`ℛ_d`) and its bedrock: `exists_isMinOn_abs_eval`, `R_mem`, `R_isMinOn`,
  `R_eval_eq_zero_of_exists`, `R_eval_eq_zero_of_le_zero_le` / `_ge_zero_ge` — the minimiser exists,
  lands in `[a,b]`, and is an actual root of `P` whenever `P` has one there (Coste Prop. 2.2, cell form).
* `vroots` and `vroots_length` — a degree-`d` polynomial has **exactly `d`** virtual roots
  (the fundamental count: real roots are `≤ d`, virtual roots are always `d`).
* `vroots_isChain`, `vroots_subset_Icc` — the `d` virtual roots are sorted and lie in `[lo,hi]`.
* `vroots_getElem_mem`, `vroots_interlacing` — each lands between its two breakpoints, giving the
  **Rolle interlacing** `ρ_{d,r}(P) ≤ ρ_{d-1,r}(P') ≤ ρ_{d,r+1}(P)` (Coste, Prop. 2.3).

**Next (future work, the BudanFourier bridge):** `card_virtualRoot_eq_fourierVar` — the exact count,
that the number of virtual roots in `(a,b]` equals `fourierVar P a - fourierVar P b`, turning the
inequality of `BudanFourier.budan_fourier` into an equality. This fuses two independent recursive
constructions (the `ℛ_d` minimiser here and the sign-variation `fourierVar` of `BudanFourier.lean`)
and is a development in its own right; it is the natural sequel to this file. -/

end VirtualRoots
