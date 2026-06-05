/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import MatchingPoly
public import RealStable

/-!
# Heilmann–Lieb via the Herglotz / `u = 1/R` route (pivot, 2026-06-03)

This file pursues Heilmann–Lieb — `μ(G)` is real-rooted, roots in `[−2√(Δ−1), 2√(Δ−1)]` —
**without** the path tree, deliberately avoiding the `whnf`/`isDefEq` performance wall that blocks
the path-tree divisibility route (`MSS/Divisibility.lean`: the doubly-deleted `Σ`-of-paths transport
`matchingPoly_pathTree_deleteRoot_child_target`). Everything here lives in `ℝ[X]` — polynomials and
the real-stability muscle of `RealStable.lean` — so there are no complex graph types to blow up.

## The `u = 1/R` motivation (why this route exists)

For the **ratio / Green's function** `R(G,a) := μ(G∖a)/μ(G)`, the matching recurrence
`μ(G) = x·μ(G−a) − ∑_{b∼a} μ(G−a−b)` divided by `μ(G−a)` gives the continued-fraction recurrence
`1/R_a = x − ∑_{b∼a} R_b^{(G−a)}`. On the `(q+1)`-regular tree this is self-consistent and solves
`q R² − x R + 1 = 0`, whose branch `R = 1/u` ties the **Ihara non-backtracking variable** `u`
(Joukowski `x = u + q/u`, i.e. `x = qR + 1/R`) to the **matching Green's function** `R` by the
reciprocal duality `u = 1/R`. The band `2√q` (`q = Δ−1`) is the Joukowski image of `|u| = √q`, i.e.
exactly the branch cut of `R`. So:

* `μ` **real-rooted** ⟺ `R` is a (real) **Stieltjes/Herglotz** function — its poles (= roots of `μ`)
  are real and interlace its zeros (= roots of `μ(G∖a)`). The *real-algebraic shadow* of "Herglotz"
  is **interlacing**, which `RealStable` already speaks (`Interlace`, `realRooted_of_alternating`,
  `comb_alternates_of_alternates`).
* the **root bound** `|x| ≤ 2√(Δ−1)` is the location of `R`'s branch cut — proved separately from the
  recurrence staying inside the band.

## Route: interlacing induction on the matching recurrence

Inductive invariant `HLInterlace G` (on `|V|`, true matching polynomial):
`μ(G)` is real-rooted **and** for every vertex `a`, `μ(G−a)` interlaces `μ(G)`.

Inductive step from `μ(G) = x·μ(G−a) − ∑_{b∼a} μ(G−a−b)`:
1. IH on `G−a`: `μ(G−a)` real-rooted, and each `μ(G−a−b)` interlaces `μ(G−a)`.
2. `∑_{b∼a} μ(G−a−b)` interlaces `μ(G−a)` — a positive sum of interlacers (`RealStable` cone, e.g.
   `Interlace.comb`).
3. **Engine lemma** (`hl_interlacing_recurrence`, the one missing stone): if `p` is real-rooted and `q`
   interlaces `p` (with `deg q = deg p − 1`, positive leading coeff), then `x·p − q` is real-rooted and
   `p` interlaces `x·p − q`. This is Hermite–Biehler; it reduces to `realRooted_of_alternating` +
   `comb_alternates_of_alternates` once `f_alternates_at_g_roots` (the remaining `RealStable` stub) is
   supplied.

The fixed-`n` convention (`deleteIncidenceSet` pads `μ(G∖a) = x·μ_true(G−a)`) means the clean
interlacing is on the **true** (variable-degree) matching polynomial; the recurrence
`matchingPoly_recurrence` (`X²`-padded) recovers it after cancelling `X²`. Reconciling the two
conventions is part of building `HLInterlace`.

## What is already in hand (sorry-free, elsewhere)

* `matchingPoly_recurrence` — the deletion recurrence (engine), `MatchingPoly.lean`.
* `MatchingPoly.matchingPoly_bot_realRooted` — base case `μ(⊥) = Xⁿ` real-rooted.
* `RealStable`: `RealRooted` closure, `Interlace`/`Interlaces` + `comb`, `realRooted_of_alternating`,
  `comb_alternates_of_alternates`, `BoundedBy`/`maxRoot` (for the band).
* `IharaZeta` (same repo): the `u` side and the band `2√(Δ−1)` (`isRamanujan_iff_critical_circle`).
-/

@[expose] public section

namespace SimpleGraph

open MSS Polynomial

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The interlacing invariant of the Heilmann–Lieb induction (TARGET).** `μ(G)` is real-rooted
and every vertex-deletion `μ(G∖a)` interlaces it. Proven by strong induction on `|V|` (or edge
count) via `matchingPoly_recurrence` + `hl_interlacing_recurrence`; base case
`matchingPoly_bot_realRooted`. -/
def HLInterlace_target (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  MSS.RealRooted G.matchingPoly ∧
    ∀ a : V, MSS.Interlace (G.deleteIncidenceSet a).matchingPoly G.matchingPoly

/-- **Heilmann–Lieb, real-rootedness half (TARGET).** `μ(G)` is real-rooted, for every graph `G`.
Follows from `HLInterlace_target` (its first component). The Herglotz/`u = 1/R` route: the matching
Green's function `R = μ(G∖a)/μ(G)` is Stieltjes ⟺ this interlacing holds. -/
def matchingPoly_realRooted_target (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  MSS.RealRooted G.matchingPoly

/-- **The interlacing-recurrence engine (TARGET — assembly; all atoms now PROVEN).** Hermite–Biehler
shape: if `p` is real-rooted and `q` interlaces `p`, then `X·p − q` is real-rooted and `p` interlaces
it. Every building block exists in `RealStable` (committed); only the index/parity *assembly* remains:

  1. `p` real-rooted ⟹ `p` splits; take its `m` (simple, for the interlacing case) roots sorted
     `s₁<…<sₘ`.
  2. Build the `m+2`-point sequence `x₀ < s₁ < … < sₘ < x_{m+1}` with the outer points from
     `exists_lt_roots_negOnePow_eval_pos` / `exists_gt_roots_eval_pos` (the `±∞` end gaps).
  3. `X·p − q` alternates at the `sⱼ`: there it equals `−q` (`eval_X_mul_sub_at_isRoot`), and `q`
     alternates at `p`'s roots (the geometric content of `q` interlaces `p`); the squared signs give
     alternation (`eval_X_mul_sub_mul_at_isRoots`).
  4. Splice the two end points with the correct parity (their signs are fixed by the `±∞` atoms;
     `deg (X·p − q) = m+1` so the leading sign matches), giving alternation at all `m+2` points.
  5. `realRooted_of_alternating` (or `realRooted_of_root_per_gap`) ⟹ `RealRooted (X·p − q)`.

The remaining work is the `Fin (m+2)` bookkeeping + the endpoint parity — the single delicate
synthesis on the Herglotz route to `matchingPoly_realRooted_target`. -/
def hl_interlacing_recurrence_target (p q : Polynomial ℝ) : Prop :=
  MSS.RealRooted p → MSS.Interlace q p →
    MSS.RealRooted (Polynomial.X * p - q) ∧ MSS.Interlace p (Polynomial.X * p - q)

/-- **Heilmann–Lieb root bound (TARGET).** For maximum degree `Δ`, every root of `μ(G)` lies in
`[−2√(Δ−1), 2√(Δ−1)]` — the Joukowski image of `|u| = √(Δ−1)`, i.e. the branch cut of the
matching Green's function `R`. The `2√(Δ−1)` is the same band as `IharaZeta`'s Ramanujan threshold
(`u = 1/R`). -/
def matchingPoly_bounded_target (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (hΔ : ∀ v, G.degree v ≤ Δ) : Prop :=
  MSS.BoundedBy G.matchingPoly (2 * Real.sqrt (Δ - 1))

/-! ### Geometric route (skips the HKO bridge) -/

/-- **Geometric interlacing — the HL-route invariant.** `q` interlaces `p` *geometrically*: it
takes strictly opposite signs across any two *adjacent* roots of `p` (roots with no root of `p`
strictly between). Carrying THIS through the matching induction — instead of the algebraic
`MSS.Interlace` — keeps the whole proof geometric, so the HKO bridge (`hko_geometric_to_algebraic`)
is never needed (insight 2026-06-03). The recurrence step consumes exactly the `RealStable` atoms
(`realRooted_of_root_per_gap`, `eval_X_mul_sub_at_isRoot`, the `±∞` end-gap atoms,
`exists_strictMono_roots`). -/
def GeomInterlaced (q p : Polynomial ℝ) : Prop :=
  ∀ s t : ℝ, p.IsRoot s → p.IsRoot t → s < t →
    (∀ z, s < z → z < t → ¬ p.IsRoot z) → q.eval s * q.eval t < 0

/-- **Signed geometric interlacing — the additive, phase-locked refinement.** At every root `s`
of `p`, `q(s)` carries the *fixed* sign of `(-1)^{#roots of `p` strictly above `s`}`. Unlike
`GeomInterlaced` (sign-agnostic per gap, so not closed under `+`), the phase is pinned, so a *sum*
of signed interlacers is one (`SignedGeomInterlaced.add`/`.sum`) — exactly what the matching
recurrence's `q = Σ_{b∼a} μ(G⟦≠a,≠b⟧)` needs. It implies `GeomInterlaced` when `p` has simple
roots (`geomInterlaced`), feeding `hl_geom_recurrence`. The phase matches a real-rooted positive-
leading interlacer's actual sign, so it is what the induction can establish from below. -/
def SignedGeomInterlaced (q p : Polynomial ℝ) : Prop :=
  ∀ s : ℝ, p.IsRoot s → 0 < q.eval s * (-1 : ℝ) ^ (p.roots.filter (fun x => s < x)).card

/-- A sum of two signed interlacers is a signed interlacer (the phase is pinned). -/
theorem SignedGeomInterlaced.add {q₁ q₂ p : Polynomial ℝ}
    (h₁ : SignedGeomInterlaced q₁ p) (h₂ : SignedGeomInterlaced q₂ p) :
    SignedGeomInterlaced (q₁ + q₂) p := by
  intro s hs
  have e₁ := h₁ s hs; have e₂ := h₂ s hs
  rw [Polynomial.eval_add, add_mul]; linarith

/-- A nonempty finite sum of signed interlacers is a signed interlacer. -/
theorem SignedGeomInterlaced.sum {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    {q : ι → Polynomial ℝ} {p : Polynomial ℝ}
    (h : ∀ i ∈ s, SignedGeomInterlaced (q i) p) :
    SignedGeomInterlaced (∑ i ∈ s, q i) p := by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a (by simp)
  | cons a s ha hne ih =>
      rw [Finset.sum_cons]
      exact (h a (Finset.mem_cons_self a s)).add
        (ih (fun i hi => h i (Finset.mem_cons.mpr (Or.inr hi))))

/-- A signed interlacer is nonzero (it has a strict sign at each root of `p`, provided `p` has one). -/
theorem SignedGeomInterlaced.ne_zero {q p : Polynomial ℝ} {s : ℝ} (hs : p.IsRoot s)
    (h : SignedGeomInterlaced q p) : q ≠ 0 := by
  intro h0
  have := h s hs
  rw [h0, Polynomial.eval_zero, zero_mul] at this
  exact lt_irrefl _ this

/-- **Signed ⟹ geometric** (for simple-rooted `p`). Across adjacent roots `s < t` the phase flips
exactly once (one fewer root lies above `t` than above `s`, and `t` is simple), so `q(s)·q(t) < 0`. -/
theorem SignedGeomInterlaced.geomInterlaced {q p : Polynomial ℝ} (hp0 : p ≠ 0)
    (hsimple : ∀ r, p.IsRoot r → p.rootMultiplicity r = 1)
    (h : SignedGeomInterlaced q p) : GeomInterlaced q p := by
  intro s t hs ht hst hno
  have e₁ := h s hs
  have e₂ := h t ht
  -- The roots above `s` are the roots above `t` plus the single root `t`.
  have hone : (p.roots.filter (fun x => s < x ∧ x ≤ t)).card = 1 := by
    rw [Multiset.card_eq_one]
    refine ⟨t, ?_⟩
    ext x
    rw [Multiset.count_filter, Multiset.count_singleton]
    by_cases hx : x = t
    · rw [hx, if_pos ⟨hst, le_refl t⟩, if_pos rfl, Polynomial.count_roots, hsimple t ht]
    · rw [if_neg hx]
      by_cases hpx : s < x ∧ x ≤ t
      · rw [if_pos hpx]
        by_contra hc
        have hxroot : p.IsRoot x := by
          rw [← Polynomial.mem_roots hp0]; exact Multiset.count_pos.mp (Nat.pos_of_ne_zero hc)
        exact hno x hpx.1 (lt_of_le_of_ne hpx.2 hx) hxroot
      · rw [if_neg hpx]
  have hsplit : (p.roots.filter (fun x => s < x)).card
      = (p.roots.filter (fun x => t < x)).card + 1 := by
    rw [← hone, ← Multiset.card_add]
    congr 1
    ext x
    simp only [Multiset.count_add, Multiset.count_filter]
    by_cases hsx : s < x
    · by_cases htx : t < x
      · rw [if_pos hsx, if_pos htx,
          if_neg (by rintro ⟨_, hle⟩; exact absurd htx (not_lt.mpr hle)), add_zero]
      · rw [if_pos hsx, if_neg htx, if_pos ⟨hsx, not_lt.mp htx⟩, zero_add]
    · rw [if_neg hsx, if_neg (fun htx => hsx (lt_trans hst htx)),
        if_neg (fun h => hsx h.1), add_zero]
  rw [hsplit, pow_succ] at e₁
  set c : ℝ := (-1 : ℝ) ^ (p.roots.filter (fun x => t < x)).card with hc
  have hc2 : c * c = 1 := by rw [hc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  nlinarith [e₁, e₂, hc2]

/-- **Internal-gap root of the recurrence (HKO-free, no `Fin`).** Between two *adjacent* roots
`s<t` of `p` (no root of `p` strictly between), the recurrence combination `X·p − q` has a root.
Proof: `(X·p−q)(s)·(X·p−q)(t) = q(s)·q(t) < 0` (the hinge `eval_X_mul_sub_mul_at_isRoots` plus
`GeomInterlaced`), so the intermediate-value theorem `exists_isRoot_of_eval_mul_neg` gives a root
in `(s,t)`. This is the inner half of the input to `realRooted_of_root_per_gap`. -/
theorem exists_root_X_mul_sub_between_adjacent {p q : Polynomial ℝ} {s t : ℝ}
    (hs : p.IsRoot s) (ht : p.IsRoot t) (hst : s < t)
    (hno : ∀ z, s < z → z < t → ¬ p.IsRoot z) (hgi : GeomInterlaced q p) :
    ∃ r, s < r ∧ r < t ∧ (Polynomial.X * p - q).IsRoot r := by
  have hsign : (Polynomial.X * p - q).eval s * (Polynomial.X * p - q).eval t < 0 := by
    rw [MSS.eval_X_mul_sub_mul_at_isRoots p q hs ht]; exact hgi s t hs ht hst hno
  obtain ⟨r, ⟨hr1, hr2⟩, hr3⟩ := MSS.exists_isRoot_of_eval_mul_neg _ hst hsign
  exact ⟨r, hr1, hr2, hr3⟩

/-- **The recurrence step, assembled.** Given `p`'s roots as a full increasing family
`s : Fin m → ℝ` (`m ≥ 1`), two outer points `xL < s_i < xR`, `q` geometrically interlacing `p`,
and a root of `X·p − q` in each end gap `(xL, s_0)` and `(s_{m-1}, xR)` (phrased index-free via
`∀ i, r < s i` / `∀ i, s i < r`), the recurrence combination `X·p − q` is real-rooted. The inner
gaps get their roots from `exists_root_X_mul_sub_between_adjacent`; the sequence is
`strictMono_extend`; the conclusion is `realRooted_of_root_per_gap`. This is the full
Hermite–Biehler assembly, with only the two end-gap roots left as hypotheses (the endpoint
parity, derivable from leading-coeff/degree data). -/
theorem realRooted_X_mul_sub {p q : Polynomial ℝ} (hgi : GeomInterlaced q p)
    (hf : Polynomial.X * p - q ≠ 0) (m : ℕ) (hm : 0 < m)
    (hdeg : (Polynomial.X * p - q).natDegree ≤ m + 1)
    (s : Fin m → ℝ) (hsm : StrictMono s) (hsroot : ∀ i, p.IsRoot (s i))
    (hsurj : ∀ x, p.IsRoot x → ∃ i, s i = x)
    (xL xR : ℝ) (hL : ∀ i, xL < s i) (hR : ∀ i, s i < xR) (hLR : xL < xR)
    (hLend : ∃ r, xL < r ∧ (∀ i, r < s i) ∧ (Polynomial.X * p - q).IsRoot r)
    (hRend : ∃ r, (∀ i, s i < r) ∧ r < xR ∧ (Polynomial.X * p - q).IsRoot r) :
    MSS.RealRooted (Polynomial.X * p - q) := by
  refine MSS.realRooted_of_root_per_gap _ hf (m + 1) hdeg
    (Fin.cons xL (Fin.snoc s xR)) (MSS.strictMono_extend s hsm xL xR hL hR hLR) (fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · -- gap 0 = (xL, s_0)
    obtain ⟨r, hr1, hr2, hr3⟩ := hLend
    refine ⟨r, ?_, ?_, hr3⟩
    · rw [Fin.castSucc_zero, Fin.cons_zero]; exact hr1
    · rw [Fin.cons_succ, show (0 : Fin (m + 1)) = Fin.castSucc (⟨0, hm⟩ : Fin m) from by ext; simp,
        Fin.snoc_castSucc]
      exact hr2 _
  · -- gap (j+1)
    rw [Fin.castSucc_fin_succ, Fin.cons_succ, Fin.cons_succ, Fin.snoc_castSucc]
    by_cases hj : Fin.succ j = Fin.last m
    · -- right end gap (s_j, xR)
      rw [hj, Fin.snoc_last]
      obtain ⟨r, hr1, hr2, hr3⟩ := hRend
      exact ⟨r, hr1 j, hr2, hr3⟩
    · -- inner gap (s_j, s_k), k = j+1
      obtain ⟨k, hk⟩ := Fin.eq_castSucc_of_ne_last hj
      rw [← hk, Fin.snoc_castSucc]
      have hv : (k : ℕ) = (j : ℕ) + 1 := by have := congrArg Fin.val hk; simpa using this
      refine exists_root_X_mul_sub_between_adjacent (hsroot j) (hsroot k)
        (hsm (by simp [Fin.lt_def, hv])) (fun z hz1 hz2 hzr => ?_) hgi
      obtain ⟨l, rfl⟩ := hsurj z hzr
      have h1 : j < l := hsm.lt_iff_lt.mp hz1
      have h2 : l < k := hsm.lt_iff_lt.mp hz2
      simp only [Fin.lt_def] at h1 h2; omega

/-- **q's roots are confined to `p`'s interior.** With `q` geometrically interlacing `p` (roots
`s : Fin (k+1)`, surjective) and `deg q ≤ k`, every root of `q` is `< s_{last}` and `> s_0`. Proof:
`q` has a root in each of the `k` gaps (alternation + IVT), and `isRoot_eq_gap_root` makes those
all of `q`'s roots, each strictly inside `(s_0, s_{last})`. -/
theorem q_isRoot_lt_last {p q : Polynomial ℝ} (hgi : GeomInterlaced q p) (hq0 : q ≠ 0)
    (k : ℕ) (hqdeg : q.natDegree ≤ k) (s : Fin (k + 1) → ℝ) (hsm : StrictMono s)
    (hsroot : ∀ i, p.IsRoot (s i)) (hsurj : ∀ x, p.IsRoot x → ∃ i, s i = x)
    {z : ℝ} (hz : q.IsRoot z) : z < s (Fin.last k) := by
  have hadj : ∀ i : Fin k, ∀ w, s i.castSucc < w → w < s i.succ → ¬ p.IsRoot w := by
    intro i w hw1 hw2 hwr
    obtain ⟨l, rfl⟩ := hsurj w hwr
    have h1 : i.castSucc < l := hsm.lt_iff_lt.mp hw1
    have h2 : l < i.succ := hsm.lt_iff_lt.mp hw2
    simp only [Fin.lt_def, Fin.coe_castSucc, Fin.val_succ] at h1 h2; omega
  have hgap : ∀ i : Fin k, ∃ r, s i.castSucc < r ∧ r < s i.succ ∧ q.IsRoot r := by
    intro i
    have hlt : s i.castSucc < s i.succ := hsm (by simp [Fin.lt_def])
    obtain ⟨r, ⟨hr1, hr2⟩, hr3⟩ := MSS.exists_isRoot_of_eval_mul_neg q hlt
      (hgi _ _ (hsroot _) (hsroot _) hlt (hadj i))
    exact ⟨r, hr1, hr2, hr3⟩
  choose r hr1 hr2 hr3 using hgap
  obtain ⟨i, rfl⟩ := MSS.isRoot_eq_gap_root hq0 hqdeg hsm hr1 hr2 hr3 hz
  exact lt_of_lt_of_le (hr2 i) (hsm.monotone (Fin.le_last _))

/-- **Right end-gap root.** `X·p − q` has a root above all of `p`'s roots: `q(s_{last})>0` (since
all `q`-roots are `< s_{last}`, by `q_isRoot_lt_last`), so `(X·p−q)(s_{last})=−q(s_{last})<0`, while
`X·p − q` is eventually positive (positive leading coeff); IVT gives the root. -/
theorem exists_right_end_root {p q : Polynomial ℝ} (hgi : GeomInterlaced q p) (hq0 : q ≠ 0)
    (k : ℕ) (hqdeg : q.natDegree ≤ k) (s : Fin (k + 1) → ℝ) (hsm : StrictMono s)
    (hsroot : ∀ i, p.IsRoot (s i)) (hsurj : ∀ x, p.IsRoot x → ∃ i, s i = x)
    (hqlc : 0 ≤ q.leadingCoeff) (hXpq0 : Polynomial.X * p - q ≠ 0)
    (hXpqlc : 0 ≤ (Polynomial.X * p - q).leadingCoeff) :
    ∃ r, (∀ i, s i < r) ∧ (Polynomial.X * p - q).IsRoot r := by
  have hqpos : 0 < q.eval (s (Fin.last k)) :=
    zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
      (fun y hy => q_isRoot_lt_last hgi hq0 k hqdeg s hsm hsroot hsurj hy) hqlc
  have hsneg : (Polynomial.X * p - q).eval (s (Fin.last k)) < 0 := by
    rw [MSS.eval_X_mul_sub_at_isRoot p q (hsroot _)]; linarith
  obtain ⟨b₀, hb₀⟩ := MSS.exists_gt_forall_isRoot _ hXpq0
  have hbpos : 0 < (Polynomial.X * p - q).eval (max b₀ (s (Fin.last k)) + 1) :=
    zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
      (fun y hy => lt_of_lt_of_le (hb₀ y hy) (le_trans (le_max_left _ _) (by linarith))) hXpqlc
  have hslt : s (Fin.last k) < max b₀ (s (Fin.last k)) + 1 :=
    lt_of_le_of_lt (le_max_right _ _) (by linarith)
  obtain ⟨r, ⟨hr1, _⟩, hr3⟩ := MSS.exists_isRoot_of_eval_mul_neg _ hslt
    (mul_neg_of_neg_of_pos hsneg hbpos)
  exact ⟨r, fun i => lt_of_le_of_lt (hsm.monotone (Fin.le_last i)) hr1, hr3⟩

/-- **q's roots exceed `s_0`** (mirror of `q_isRoot_lt_last`). -/
theorem q_isRoot_gt_head {p q : Polynomial ℝ} (hgi : GeomInterlaced q p) (hq0 : q ≠ 0)
    (k : ℕ) (hqdeg : q.natDegree ≤ k) (s : Fin (k + 1) → ℝ) (hsm : StrictMono s)
    (hsroot : ∀ i, p.IsRoot (s i)) (hsurj : ∀ x, p.IsRoot x → ∃ i, s i = x)
    {z : ℝ} (hz : q.IsRoot z) : s 0 < z := by
  have hadj : ∀ i : Fin k, ∀ w, s i.castSucc < w → w < s i.succ → ¬ p.IsRoot w := by
    intro i w hw1 hw2 hwr
    obtain ⟨l, rfl⟩ := hsurj w hwr
    have h1 : i.castSucc < l := hsm.lt_iff_lt.mp hw1
    have h2 : l < i.succ := hsm.lt_iff_lt.mp hw2
    simp only [Fin.lt_def, Fin.coe_castSucc, Fin.val_succ] at h1 h2; omega
  have hgap : ∀ i : Fin k, ∃ r, s i.castSucc < r ∧ r < s i.succ ∧ q.IsRoot r := by
    intro i
    have hlt : s i.castSucc < s i.succ := hsm (by simp [Fin.lt_def])
    obtain ⟨r, ⟨hr1, hr2⟩, hr3⟩ := MSS.exists_isRoot_of_eval_mul_neg q hlt
      (hgi _ _ (hsroot _) (hsroot _) hlt (hadj i))
    exact ⟨r, hr1, hr2, hr3⟩
  choose r hr1 hr2 hr3 using hgap
  obtain ⟨i, rfl⟩ := MSS.isRoot_eq_gap_root hq0 hqdeg hsm hr1 hr2 hr3 hz
  exact lt_of_le_of_lt (hsm.monotone (Fin.zero_le _)) (hr1 i)

/-- **Left end-gap root.** `X·p − q` has a root below all of `p`'s roots. Here the signs carry a
parity: with `deg q + 1 = deg p` the degrees `deg(X·p−q)=deg p+1` and `deg q` have equal parity,
so the `(−1)^{deg}` factors of the eventual signs of `X·p−q` (below all its roots) and of `q` (at
`s_0`, since all `q`-roots exceed `s_0`) cancel, giving opposite signs of `X·p − q` at the two ends
of the gap; IVT gives the root. -/
theorem exists_left_end_root {p q : Polynomial ℝ} (hgi : GeomInterlaced q p) (hp0 : p ≠ 0)
    (hq0 : q ≠ 0) (k : ℕ) (hqdeg : q.natDegree ≤ k) (s : Fin (k + 1) → ℝ) (hsm : StrictMono s)
    (hsroot : ∀ i, p.IsRoot (s i)) (hsurj : ∀ x, p.IsRoot x → ∃ i, s i = x)
    (hqlc : 0 ≤ q.leadingCoeff) (hXpq0 : Polynomial.X * p - q ≠ 0)
    (hXpqlc : 0 ≤ (Polynomial.X * p - q).leadingCoeff)
    (hpar : q.natDegree + 1 = p.natDegree) :
    ∃ r, (∀ i, r < s i) ∧ (Polynomial.X * p - q).IsRoot r := by
  have hdeg : (Polynomial.X * p - q).natDegree = p.natDegree + 1 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      (by rw [Polynomial.natDegree_X_mul hp0]; omega), Polynomial.natDegree_X_mul hp0, add_comm]
  have hqsign := zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg (P := q) (x := s 0)
    (fun y hy => q_isRoot_gt_head hgi hq0 k hqdeg s hsm hsroot hsurj hy) hqlc
  obtain ⟨a₀, ha₀⟩ := MSS.exists_lt_forall_isRoot _ hXpq0
  have ha_root : ∀ y, (Polynomial.X * p - q).IsRoot y → min a₀ (s 0) - 1 < y := fun y hy =>
    lt_trans (by have := min_le_left a₀ (s 0); linarith) (ha₀ y hy)
  have hfsign := zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
    (P := Polynomial.X * p - q) (x := min a₀ (s 0) - 1) ha_root hXpqlc
  -- the two (-1)^deg factors cancel: deg(X*p-q)+deg q is even
  have hone : (Int.negOnePow ((Polynomial.X * p - q).natDegree) : ℝ)
      * (Int.negOnePow q.natDegree : ℝ) = 1 := by
    have he : Even (((Polynomial.X * p - q).natDegree : ℤ) + q.natDegree) := by
      rw [hdeg]; refine ⟨q.natDegree + 1, ?_⟩; push_cast; omega
    rw [← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add, Int.negOnePow_even _ he, Units.val_one,
      Int.cast_one]
  -- product of the two end values is negative
  have hprod : (Polynomial.X * p - q).eval (min a₀ (s 0) - 1)
      * (Polynomial.X * p - q).eval (s 0) < 0 := by
    rw [MSS.eval_X_mul_sub_at_isRoot p q (hsroot 0)]
    have hmul := mul_pos hfsign hqsign
    have heq : (Int.negOnePow ((Polynomial.X * p - q).natDegree) : ℝ)
          * (Polynomial.X * p - q).eval (min a₀ (s 0) - 1)
          * ((Int.negOnePow q.natDegree : ℝ) * q.eval (s 0))
        = ((Int.negOnePow ((Polynomial.X * p - q).natDegree) : ℝ) * (Int.negOnePow q.natDegree : ℝ))
          * ((Polynomial.X * p - q).eval (min a₀ (s 0) - 1) * q.eval (s 0)) := by ring
    rw [heq, hone, one_mul] at hmul
    nlinarith [hmul]
  have ha_s0 : min a₀ (s 0) - 1 < s 0 := by have := min_le_right a₀ (s 0); linarith
  obtain ⟨r, ⟨_, hr2⟩, hr3⟩ := MSS.exists_isRoot_of_eval_mul_neg _ ha_s0 hprod
  exact ⟨r, fun i => lt_of_lt_of_le hr2 (hsm.monotone (Fin.zero_le i)), hr3⟩

/-- **★ The geometric Hermite–Biehler recurrence step — PROVEN.** Given `p`'s roots as a full
increasing family `s : Fin (k+1)`, `q` geometrically interlacing `p` with `deg q + 1 = deg p` and
nonnegative leading coefficients, the recurrence combination `X·p − q` is real-rooted. Assembles
the two end-gap roots (`exists_left_end_root`/`exists_right_end_root`) with the inner-gap engine
(`realRooted_X_mul_sub`). This is `hl_geom_recurrence_target` discharged (HKO-free). -/
theorem hl_geom_recurrence {p q : Polynomial ℝ} (hgi : GeomInterlaced q p) (hp0 : p ≠ 0)
    (hq0 : q ≠ 0) (k : ℕ) (s : Fin (k + 1) → ℝ) (hsm : StrictMono s)
    (hsroot : ∀ i, p.IsRoot (s i)) (hsurj : ∀ x, p.IsRoot x → ∃ i, s i = x)
    (hpdeg : p.natDegree = k + 1) (hqdeg : q.natDegree ≤ k) (hpar : q.natDegree + 1 = p.natDegree)
    (hplc : 0 ≤ p.leadingCoeff) (hqlc : 0 ≤ q.leadingCoeff) :
    MSS.RealRooted (Polynomial.X * p - q) := by
  have hlt : q.natDegree < (Polynomial.X * p).natDegree := by
    rw [Polynomial.natDegree_X_mul hp0]; omega
  have hXpq0 : Polynomial.X * p - q ≠ 0 := fun h => by
    rw [sub_eq_zero] at h; rw [h] at hlt; exact lt_irrefl _ hlt
  have hdeg : (Polynomial.X * p - q).natDegree = k + 2 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_mul hp0]; omega
  have hXpqlc : 0 ≤ (Polynomial.X * p - q).leadingCoeff := by
    have hcoeff : (Polynomial.X * p - q).coeff (k + 2) = p.leadingCoeff := by
      rw [Polynomial.coeff_sub,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < k + 2), sub_zero,
        Polynomial.coeff_X_mul, Polynomial.leadingCoeff, hpdeg]
    rw [Polynomial.leadingCoeff, hdeg, hcoeff]; exact hplc
  obtain ⟨rL, hrL1, hrL2⟩ := exists_left_end_root hgi hp0 hq0 k hqdeg s hsm hsroot hsurj hqlc
    hXpq0 hXpqlc hpar
  obtain ⟨rR, hrR1, hrR2⟩ := exists_right_end_root hgi hq0 k hqdeg s hsm hsroot hsurj hqlc
    hXpq0 hXpqlc
  refine realRooted_X_mul_sub hgi hXpq0 (k + 1) (Nat.succ_pos k) (by rw [hdeg]) s hsm hsroot hsurj
    (rL - 1) (rR + 1) (fun i => by have := hrL1 i; linarith) (fun i => by have := hrR1 i; linarith)
    (by have := hrL1 0; have := hrR1 0; linarith)
    ⟨rL, by linarith [hrL1 0], hrL1, hrL2⟩ ⟨rR, hrR1, by linarith [hrR1 0], hrR2⟩

/-- **Per-gap root of `X·p − q` (the extracted body of `realRooted_X_mul_sub`).** Each of the
`m+1` gaps of the sequence `xL < s₀ < … < s_{m-1} < xR` contains a root of `X·p − q`: the two end
gaps from `hLend`/`hRend`, the inner gaps from `exists_root_X_mul_sub_between_adjacent`. Factored
out so both `realRooted_X_mul_sub` (real-rootedness) and `rootFamily_X_mul_sub` (the simple root
family + interlacing) can consume it. -/
theorem exists_root_per_gap_X_mul_sub {p q : Polynomial ℝ} (hgi : GeomInterlaced q p)
    (m : ℕ) (hm : 0 < m)
    (s : Fin m → ℝ) (hsm : StrictMono s) (hsroot : ∀ i, p.IsRoot (s i))
    (hsurj : ∀ x, p.IsRoot x → ∃ i, s i = x) (xL xR : ℝ)
    (hLend : ∃ r, xL < r ∧ (∀ i, r < s i) ∧ (Polynomial.X * p - q).IsRoot r)
    (hRend : ∃ r, (∀ i, s i < r) ∧ r < xR ∧ (Polynomial.X * p - q).IsRoot r) :
    ∀ i : Fin (m + 1), ∃ r,
      (Fin.cons xL (Fin.snoc s xR) : Fin (m + 2) → ℝ) i.castSucc < r ∧
      r < (Fin.cons xL (Fin.snoc s xR) : Fin (m + 2) → ℝ) i.succ ∧
      (Polynomial.X * p - q).IsRoot r := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · -- gap 0 = (xL, s_0)
    obtain ⟨r, hr1, hr2, hr3⟩ := hLend
    refine ⟨r, ?_, ?_, hr3⟩
    · rw [Fin.castSucc_zero, Fin.cons_zero]; exact hr1
    · rw [Fin.cons_succ, show (0 : Fin (m + 1)) = Fin.castSucc (⟨0, hm⟩ : Fin m) from by ext; simp,
        Fin.snoc_castSucc]
      exact hr2 _
  · -- gap (j+1)
    rw [Fin.castSucc_fin_succ, Fin.cons_succ, Fin.cons_succ, Fin.snoc_castSucc]
    by_cases hj : Fin.succ j = Fin.last m
    · -- right end gap (s_j, xR)
      rw [hj, Fin.snoc_last]
      obtain ⟨r, hr1, hr2, hr3⟩ := hRend
      exact ⟨r, hr1 j, hr2, hr3⟩
    · -- inner gap (s_j, s_k), k = j+1
      obtain ⟨k, hk⟩ := Fin.eq_castSucc_of_ne_last hj
      rw [← hk, Fin.snoc_castSucc]
      have hv : (k : ℕ) = (j : ℕ) + 1 := by have := congrArg Fin.val hk; simpa using this
      refine exists_root_X_mul_sub_between_adjacent (hsroot j) (hsroot k)
        (hsm (by simp [Fin.lt_def, hv])) (fun z hz1 hz2 hzr => ?_) hgi
      obtain ⟨l, rfl⟩ := hsurj z hzr
      have h1 : j < l := hsm.lt_iff_lt.mp hz1
      have h2 : l < k := hsm.lt_iff_lt.mp hz2
      simp only [Fin.lt_def] at h1 h2; omega

/-- **The `X·p − q` root family — `m+1` simple roots, strictly interleaving `p`'s `m` roots.**
From `exists_root_per_gap_X_mul_sub` upgraded by `unique_simple_root_per_gap`: each gap yields a
unique simple root `r i`, the family is strictly increasing, and `p`'s root `s j` sits strictly
between `r jᶜ` and `r jˢ` (`r jᶜ < s j < r jˢ`). Plus surjectivity onto the roots of `X·p − q`.
This is the geometric scaffold PIECE 2 needs to read off both simple-rootedness and interlacing
of the recurrence result. -/
theorem rootFamily_X_mul_sub {p q : Polynomial ℝ} (hgi : GeomInterlaced q p)
    (hf : Polynomial.X * p - q ≠ 0) (m : ℕ) (hm : 0 < m)
    (hdeg : (Polynomial.X * p - q).natDegree ≤ m + 1)
    (s : Fin m → ℝ) (hsm : StrictMono s) (hsroot : ∀ i, p.IsRoot (s i))
    (hsurj : ∀ x, p.IsRoot x → ∃ i, s i = x)
    (xL xR : ℝ) (hL : ∀ i, xL < s i) (hR : ∀ i, s i < xR) (hLR : xL < xR)
    (hLend : ∃ r, xL < r ∧ (∀ i, r < s i) ∧ (Polynomial.X * p - q).IsRoot r)
    (hRend : ∃ r, (∀ i, s i < r) ∧ r < xR ∧ (Polynomial.X * p - q).IsRoot r) :
    ∃ r : Fin (m + 1) → ℝ, StrictMono r ∧ (∀ i, (Polynomial.X * p - q).IsRoot (r i)) ∧
      (∀ i, (Polynomial.X * p - q).rootMultiplicity (r i) = 1) ∧
      (∀ j : Fin m, r j.castSucc < s j ∧ s j < r j.succ) ∧
      (∀ x, (Polynomial.X * p - q).IsRoot x → ∃ i, r i = x) := by
  set z : Fin (m + 2) → ℝ := Fin.cons xL (Fin.snoc s xR) with hz
  have hzmono : StrictMono z := MSS.strictMono_extend s hsm xL xR hL hR hLR
  have hgap := exists_root_per_gap_X_mul_sub hgi m hm s hsm hsroot hsurj xL xR hLend hRend
  have hus := MSS.unique_simple_root_per_gap _ hf (m + 1) hdeg z hzmono hgap
  choose r hr1 hr2 hr3 hrsimple _huniq using hus
  -- strict monotonicity: the gap-roots land in disjoint increasing gaps
  have hsuccle : ∀ {i j : Fin (m + 1)}, i < j → z i.succ ≤ z j.castSucc := fun {i j} hij =>
    hzmono.monotone (by
      have : i.val < j.val := hij
      rw [Fin.le_def, Fin.val_succ, Fin.coe_castSucc]; omega)
  have hrmono : StrictMono r := fun i j hij => ((hr2 i).trans_le (hsuccle hij)).trans (hr1 j)
  refine ⟨r, hrmono, hr3, hrsimple, fun j => ?_, fun x hx => ?_⟩
  · -- interleaving: r jᶜ < s j < r jˢ ; both bounds via z (jᶜ).succ = s j
    have hzj : z (Fin.castSucc j).succ = s j := by rw [hz, Fin.cons_succ, Fin.snoc_castSucc]
    refine ⟨?_, ?_⟩
    · have := hr2 j.castSucc; rwa [hzj] at this
    · have := hr1 j.succ
      rwa [← Fin.succ_castSucc, hzj] at this
  · -- surjectivity onto roots of X·p−q
    obtain ⟨i, hi⟩ := MSS.isRoot_eq_gap_root hf hdeg hzmono hr1 hr2 hr3 hx
    exact ⟨i, hi.symm⟩

/-- **Sign of a product `∏(x − aᵢ)`.** Over a root-free point `x` (no `aᵢ = x`), the product
`∏_{a∈M}(x − a)` carries the sign `(−1)^{#{a : x < a}}` — one sign flip per factor with `a > x`.
The combinatorial seed of the "sign of a real-rooted polynomial" formula. -/
theorem prod_map_sub_negOnePow_pos (M : Multiset ℝ) (x : ℝ) (hx : ∀ a ∈ M, a ≠ x) :
    0 < (-1 : ℝ) ^ (M.filter (fun a => x < a)).card * (M.map (fun a => x - a)).prod := by
  induction M using Multiset.induction with
  | empty => simp
  | cons a M ih =>
      have ih' := ih (fun b hb => hx b (Multiset.mem_cons_of_mem hb))
      have ha : a ≠ x := hx a (Multiset.mem_cons_self a M)
      rw [Multiset.map_cons, Multiset.prod_cons]
      by_cases hlt : x < a
      · rw [Multiset.filter_cons_of_pos _ hlt, Multiset.card_cons, pow_succ]
        have key : (-1 : ℝ) ^ (M.filter (fun a => x < a)).card * (-1) *
              ((x - a) * (M.map (fun a => x - a)).prod)
            = ((-1 : ℝ) ^ (M.filter (fun a => x < a)).card * (M.map (fun a => x - a)).prod)
              * (a - x) := by ring
        rw [key]; exact mul_pos ih' (by linarith)
      · rw [Multiset.filter_cons_of_neg _ hlt]
        have hax : a < x := lt_of_le_of_ne (not_lt.mp hlt) ha
        have key : (-1 : ℝ) ^ (M.filter (fun a => x < a)).card *
              ((x - a) * (M.map (fun a => x - a)).prod)
            = ((-1 : ℝ) ^ (M.filter (fun a => x < a)).card * (M.map (fun a => x - a)).prod)
              * (x - a) := by ring
        rw [key]; exact mul_pos ih' (by linarith)

/-- **Sign of a real-rooted polynomial between its roots.** For a real-rooted `p` with positive
leading coefficient and `x` not a root, `p(x)·(−1)^{#{roots > x}} > 0`: the sign of `p(x)` is
`(−1)^{number of roots above x}` (times the positive leading sign). Factor `p = lc·∏(X − rᵢ)` (it
splits) and apply `prod_map_sub_negOnePow_pos`. This is the absolute-sign input the signed
interlacing phase needs. -/
theorem eval_negOnePow_card_above_pos {p : Polynomial ℝ} (hp : MSS.RealRooted p)
    (hlc : 0 < p.leadingCoeff) {x : ℝ} (hx : ¬ p.IsRoot x) :
    0 < p.eval x * (-1 : ℝ) ^ (p.roots.filter (fun a => x < a)).card := by
  have hp0 : p ≠ 0 := fun h => by rw [h, Polynomial.leadingCoeff_zero] at hlc; exact lt_irrefl _ hlc
  have hroots_ne : ∀ a ∈ p.roots, a ≠ x := fun a ha hax =>
    hx (hax ▸ Polynomial.isRoot_of_mem_roots ha)
  have hsign := prod_map_sub_negOnePow_pos p.roots x hroots_ne
  have heval : p.eval x = p.leadingCoeff * (p.roots.map (fun a => x - a)).prod := by
    conv_lhs => rw [Polynomial.eq_prod_roots_of_splits_id hp]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod ?_
    exact Multiset.map_congr rfl (fun a _ => by simp)
  rw [heval]
  have key : p.leadingCoeff * (p.roots.map (fun a => x - a)).prod *
        (-1 : ℝ) ^ (p.roots.filter (fun a => x < a)).card
      = p.leadingCoeff * ((-1 : ℝ) ^ (p.roots.filter (fun a => x < a)).card *
        (p.roots.map (fun a => x - a)).prod) := by ring
  rw [key]; exact mul_pos hlc hsign

/-- **The roots of a real-rooted, simple-rooted polynomial are its root family.** If `t : Fin n`
is strictly monotone, lands on roots, is surjective onto them, each simple, and `g` has `n` roots,
then `g.roots = (Finset.univ.val).map t` as a multiset. Lets root-count filters be computed over
`Fin n`. -/
theorem roots_eq_univ_map {g : Polynomial ℝ} (hg0 : g ≠ 0) {n : ℕ} (t : Fin n → ℝ)
    (htm : StrictMono t) (htroot : ∀ i, g.IsRoot (t i))
    (htsurj : ∀ x, g.IsRoot x → ∃ i, t i = x)
    (htsimple : ∀ i, g.rootMultiplicity (t i) = 1) (hcard : g.roots.card = n) :
    g.roots = (Finset.univ.val.map t) := by
  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  · rw [Multiset.le_iff_count]
    intro a
    rcases eq_or_ne (Multiset.count a (Finset.univ.val.map t)) 0 with h0 | h0
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp (Nat.pos_of_ne_zero h0))
      have hnodup : (Finset.univ.val.map t).Nodup := Finset.univ.nodup.map htm.injective
      have hle1 := Multiset.nodup_iff_count_le_one.mp hnodup (t i)
      have hge1 : 1 ≤ Multiset.count (t i) g.roots := by
        rw [Polynomial.count_roots, htsimple i]
      exact le_trans hle1 hge1
  · rw [hcard, Multiset.card_map]; simp

/-- **PIECE 2 — `p` geometrically interlaces `X·p − q`.** Between two adjacent roots `u < v` of
`X·p − q` sits exactly one root `s j` of `p`, simple, so `p` changes sign once across `(u,v)`:
`p(u)·p(v) < 0`. Uses the `rootFamily_X_mul_sub` scaffold (adjacent `X·p−q`-roots are consecutive
`r i, r (i+1)`, with `s i` interleaved) + `factor_of_unique_simple_root_on_Icc` +
`eval_mul_neg_of_factor`. Combined with `hl_geom_recurrence`'s real-rootedness this discharges the
full `hl_geom_recurrence_target`. -/
theorem geomInterlaced_X_mul_sub {p q : Polynomial ℝ} (hgi : GeomInterlaced q p) (hp0 : p ≠ 0)
    (hpsimple : ∀ r, p.IsRoot r → p.rootMultiplicity r = 1)
    (hf : Polynomial.X * p - q ≠ 0) (m : ℕ) (hm : 0 < m)
    (hdeg : (Polynomial.X * p - q).natDegree ≤ m + 1)
    (s : Fin m → ℝ) (hsm : StrictMono s) (hsroot : ∀ i, p.IsRoot (s i))
    (hsurj : ∀ x, p.IsRoot x → ∃ i, s i = x)
    (xL xR : ℝ) (hL : ∀ i, xL < s i) (hR : ∀ i, s i < xR) (hLR : xL < xR)
    (hLend : ∃ r, xL < r ∧ (∀ i, r < s i) ∧ (Polynomial.X * p - q).IsRoot r)
    (hRend : ∃ r, (∀ i, s i < r) ∧ r < xR ∧ (Polynomial.X * p - q).IsRoot r) :
    GeomInterlaced p (Polynomial.X * p - q) := by
  obtain ⟨r, hrm, hrroot, _hrsimple, hrint, hrsurj⟩ :=
    rootFamily_X_mul_sub hgi hf m hm hdeg s hsm hsroot hsurj xL xR hL hR hLR hLend hRend
  intro u v hu hv huv hno
  obtain ⟨i, rfl⟩ := hrsurj u hu
  obtain ⟨i', rfl⟩ := hrsurj v hv
  have hii' : i < i' := hrm.lt_iff_lt.mp huv
  -- adjacency ⟹ consecutive: i'.val = i.val + 1
  have hconsec : (i' : ℕ) = (i : ℕ) + 1 := by
    by_contra hne
    have hlt : (i : ℕ) + 1 < (i' : ℕ) := by
      have : (i : ℕ) < i' := hii'; omega
    have hw : (⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 1)) ∈ Set.Ioo (i : Fin (m + 1)) i' := by
      constructor <;> simp [Fin.lt_def] <;> omega
    exact hno (r ⟨(i : ℕ) + 1, by omega⟩) (hrm hw.1) (hrm hw.2) (hrroot _)
  -- the interleaved p-root: j with value i, so r jᶜ = r i = u, r jˢ = r i' = v
  have him : (i : ℕ) < m := by have := i'.isLt; omega
  set j : Fin m := ⟨(i : ℕ), him⟩ with hj
  have hjv : (j : ℕ) = (i : ℕ) := by rw [hj]
  have hjc : j.castSucc = i := by ext; simp [hj]
  have hjs : j.succ = i' := by ext; simp [hj, Fin.val_succ, hconsec]
  obtain ⟨hlo, hhi⟩ := hrint j
  rw [hjc] at hlo; rw [hjs] at hhi
  -- s j is the unique p-root in [r i, r i']
  have huniq : ∀ w ∈ Set.Icc (r i) (r i'), p.IsRoot w → w = s j := by
    intro w hw hwr
    obtain ⟨l, rfl⟩ := hsurj w hwr
    rcases lt_trichotomy l j with hlj | rfl | hlj
    · -- s l < r i (= lower endpoint): contradiction with r i ≤ s l
      exfalso
      have : (l : ℕ) + 1 ≤ (i : ℕ) := by
        have hlt : (l : ℕ) < (j : ℕ) := hlj; omega
      have hle : r l.succ ≤ r i := hrm.monotone (by rw [Fin.le_def, Fin.val_succ]; omega)
      have := (hrint l).2  -- s l < r l.succ
      have hlo' : r i ≤ s l := hw.1
      linarith
    · rfl
    · -- s l > r i': contradiction
      exfalso
      have hil : (i : ℕ) + 1 ≤ (l : ℕ) := by have hlt : (j : ℕ) < (l : ℕ) := hlj; omega
      have hle : r i' ≤ r l.castSucc :=
        hrm.monotone (by rw [Fin.le_def, Fin.coe_castSucc]; omega)
      have := (hrint l).1  -- r l.castSucc < s l
      have hhi' : s l ≤ r i' := hw.2
      linarith
  -- factor p at the simple root s j and flip the sign across it
  obtain ⟨p', hpfac, hp'no⟩ :=
    MSS.factor_of_unique_simple_root_on_Icc p hp0 (hsroot j) (hpsimple _ (hsroot j)) huniq
  have := MSS.eval_mul_neg_of_factor p' hlo hhi hp'no
  rw [← hpfac] at this
  exact this

/-- **PIECE 2, SIGNED — `p` signed-geometrically interlaces `X·p − q`.** Strengthens
`geomInterlaced_X_mul_sub` to the *phase-pinned* predicate `SignedGeomInterlaced p (X·p − q)`,
which (unlike the unsigned one) is closed under `+` — exactly what the `|V|`-induction needs for
`q = Σ_{b∼a} μ(G⟦≠a,≠b⟧)`. At an `f`-root `r i` the phase `(−1)^{#f-roots above r i}` equals
`(−1)^{#p-roots above r i}` (both count `m − i`, via the strict interleaving `r jᶜ < s j < r jˢ`),
and `eval_negOnePow_card_above_pos` gives `0 < p(r i)·(−1)^{#p-roots above}`. Needs `p` monic-ish
(`0 < leadingCoeff`) + real-rooted with `m` roots. -/
theorem signedGeomInterlaced_X_mul_sub {p q : Polynomial ℝ} (hgi : GeomInterlaced q p) (hp0 : p ≠ 0)
    (hpsimple : ∀ r, p.IsRoot r → p.rootMultiplicity r = 1) (hplc : 0 < p.leadingCoeff)
    (hprr : MSS.RealRooted p) (hf : Polynomial.X * p - q ≠ 0) (m : ℕ) (hm : 0 < m)
    (hpdeg : p.natDegree = m) (hdeg : (Polynomial.X * p - q).natDegree ≤ m + 1)
    (s : Fin m → ℝ) (hsm : StrictMono s) (hsroot : ∀ i, p.IsRoot (s i))
    (hsurj : ∀ x, p.IsRoot x → ∃ i, s i = x)
    (xL xR : ℝ) (hL : ∀ i, xL < s i) (hR : ∀ i, s i < xR) (hLR : xL < xR)
    (hLend : ∃ r, xL < r ∧ (∀ i, r < s i) ∧ (Polynomial.X * p - q).IsRoot r)
    (hRend : ∃ r, (∀ i, s i < r) ∧ r < xR ∧ (Polynomial.X * p - q).IsRoot r) :
    SignedGeomInterlaced p (Polynomial.X * p - q) := by
  obtain ⟨r, hrm, hrroot, hrsimple, hrint, hrsurj⟩ :=
    rootFamily_X_mul_sub hgi hf m hm hdeg s hsm hsroot hsurj xL xR hL hR hLR hLend hRend
  -- root multisets as the families
  have hps : p.roots.card = m := by rw [MSS.realRooted_iff_card_roots.mp hprr, hpdeg]
  have hpmap : p.roots = Finset.univ.val.map s :=
    roots_eq_univ_map hp0 s hsm hsroot hsurj (fun i => hpsimple (s i) (hsroot i)) hps
  have hfcard : (Polynomial.X * p - q).roots.card = m + 1 := by
    refine le_antisymm (le_trans (Polynomial.card_roots' _) hdeg) ?_
    have hinj : (Finset.univ.image r).card = m + 1 := by
      rw [Finset.card_image_of_injective _ hrm.injective, Finset.card_univ, Fintype.card_fin]
    have hsub : Finset.univ.image r ⊆ (Polynomial.X * p - q).roots.toFinset := fun a ha => by
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp ha
      exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hf, hrroot l⟩)
    rw [← hinj]
    exact le_trans (Finset.card_le_card hsub) (Multiset.toFinset_card_le _)
  have hfmap : (Polynomial.X * p - q).roots = Finset.univ.val.map r :=
    roots_eq_univ_map hf r hrm hrroot hrsurj hrsimple hfcard
  intro w hw
  obtain ⟨i, rfl⟩ := hrsurj w hw
  -- r i is not a root of p (strictly between p's roots)
  have hwnp : ¬ p.IsRoot (r i) := by
    intro hpr
    obtain ⟨j, hj⟩ := hsurj (r i) hpr
    have h1 := (hrint j).1; have h2 := (hrint j).2
    rw [hj] at h1 h2
    have hlt1 : j.castSucc < i := hrm.lt_iff_lt.mp h1
    have hlt2 : i < j.succ := hrm.lt_iff_lt.mp h2
    simp only [Fin.lt_def, Fin.coe_castSucc, Fin.val_succ] at hlt1 hlt2; omega
  -- the two "roots above r i" counts agree
  have hpredr : ∀ l : Fin (m + 1), (r i < r l) ↔ (i < l) := fun l => hrm.lt_iff_lt
  have hpreds : ∀ j : Fin m, (r i < s j) ↔ ((i : ℕ) ≤ (j : ℕ)) := by
    intro j
    constructor
    · intro hlt
      by_contra hc
      push_neg at hc  -- j.val < i.val
      have h2 := (hrint j).2  -- s j < r j.succ
      have hle : r j.succ ≤ r i := hrm.monotone (by rw [Fin.le_def, Fin.val_succ]; omega)
      linarith
    · intro hle
      have h1 := (hrint j).1  -- r j.castSucc < s j
      have hle' : r i ≤ r j.castSucc := hrm.monotone (by rw [Fin.le_def, Fin.coe_castSucc]; omega)
      linarith
  -- count over the families: (map t univ).filter (r i < ·) has card = #{l | r i < t l}
  have key : ∀ {n : ℕ} (t : Fin n → ℝ),
      ((Finset.univ.val.map t).filter (fun a => r i < a)).card
      = (Finset.univ.filter (fun l => r i < t l)).card := by
    intro n t
    rw [Multiset.filter_map, Multiset.card_map]; rfl
  have hcardeq : ((Polynomial.X * p - q).roots.filter (fun a => r i < a)).card
               = (p.roots.filter (fun a => r i < a)).card := by
    rw [hfmap, hpmap, key r, key s]
    -- predicate conversion + bijection l ↦ l-1 between {l : Fin(m+1) | i<l} and {j : Fin m | i≤j}
    rw [Finset.filter_congr (fun l _ => hpredr l), Finset.filter_congr (fun j _ => hpreds j)]
    refine Finset.card_nbij' (fun l => (⟨(l : ℕ) - 1, by have := l.isLt; have := hm; omega⟩ : Fin m))
      (fun j => (⟨(j : ℕ) + 1, by have := j.isLt; omega⟩ : Fin (m + 1))) ?_ ?_ ?_ ?_
    · intro l hl
      rw [Finset.mem_coe, Finset.mem_filter] at hl
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hil : (i : ℕ) < (l : ℕ) := hl.2
      show (i : ℕ) ≤ (l : ℕ) - 1
      omega
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_filter] at hj
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hij : (i : ℕ) ≤ (j : ℕ) := hj.2
      show (i : ℕ) < (j : ℕ) + 1
      omega
    · intro l hl
      rw [Finset.mem_coe, Finset.mem_filter] at hl
      have hil : (i : ℕ) < (l : ℕ) := hl.2
      apply Fin.ext
      show ((l : ℕ) - 1) + 1 = (l : ℕ)
      omega
    · intro j hj
      apply Fin.ext
      show ((j : ℕ) + 1) - 1 = (j : ℕ)
      omega
  rw [hcardeq]
  exact eval_negOnePow_card_above_pos hprr hplc hwnp

/-- **★ The full geometric Hermite–Biehler step — the inductive payload (PIECE 2 + recurrence).**
Given `p` real-rooted with simple roots and `q` geometrically interlacing `p` (matching-recurrence
degree/leading data), `X·p − q` is (1) real-rooted, (2) geometrically interlaced *by* `p`, and (3)
all its roots are simple. This is exactly the triple the `|V|`-induction carries
(`HLGeom_target`-style invariant): real-rootedness propagates, `p = μ(G∖a)` interlaces `μ(G)`, and
`μ(G)` stays simple-rooted. Assembles `hl_geom_recurrence` (real) + `geomInterlaced_X_mul_sub`
(interlacing) + `rootFamily_X_mul_sub` (simple), sharing the end-gap roots. -/
theorem hl_geom_recurrence_full {p q : Polynomial ℝ} (hgi : GeomInterlaced q p) (hp0 : p ≠ 0)
    (hpsimple : ∀ r, p.IsRoot r → p.rootMultiplicity r = 1) (hq0 : q ≠ 0)
    (k : ℕ) (s : Fin (k + 1) → ℝ) (hsm : StrictMono s)
    (hsroot : ∀ i, p.IsRoot (s i)) (hsurj : ∀ x, p.IsRoot x → ∃ i, s i = x)
    (hpdeg : p.natDegree = k + 1) (hqdeg : q.natDegree ≤ k) (hpar : q.natDegree + 1 = p.natDegree)
    (hplc : 0 ≤ p.leadingCoeff) (hqlc : 0 ≤ q.leadingCoeff) :
    MSS.RealRooted (Polynomial.X * p - q) ∧ GeomInterlaced p (Polynomial.X * p - q) ∧
      (∀ w, (Polynomial.X * p - q).IsRoot w →
        (Polynomial.X * p - q).rootMultiplicity w = 1) := by
  have hlt : q.natDegree < (Polynomial.X * p).natDegree := by
    rw [Polynomial.natDegree_X_mul hp0]; omega
  have hXpq0 : Polynomial.X * p - q ≠ 0 := fun h => by
    rw [sub_eq_zero] at h; rw [h] at hlt; exact lt_irrefl _ hlt
  have hdeg : (Polynomial.X * p - q).natDegree = k + 2 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_mul hp0]; omega
  have hXpqlc : 0 ≤ (Polynomial.X * p - q).leadingCoeff := by
    have hcoeff : (Polynomial.X * p - q).coeff (k + 2) = p.leadingCoeff := by
      rw [Polynomial.coeff_sub,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < k + 2), sub_zero,
        Polynomial.coeff_X_mul, Polynomial.leadingCoeff, hpdeg]
    rw [Polynomial.leadingCoeff, hdeg, hcoeff]; exact hplc
  obtain ⟨rL, hrL1, hrL2⟩ := exists_left_end_root hgi hp0 hq0 k hqdeg s hsm hsroot hsurj hqlc
    hXpq0 hXpqlc hpar
  obtain ⟨rR, hrR1, hrR2⟩ := exists_right_end_root hgi hq0 k hqdeg s hsm hsroot hsurj hqlc
    hXpq0 hXpqlc
  refine ⟨hl_geom_recurrence hgi hp0 hq0 k s hsm hsroot hsurj hpdeg hqdeg hpar hplc hqlc, ?_, ?_⟩
  · exact geomInterlaced_X_mul_sub hgi hp0 hpsimple hXpq0 (k + 1) (Nat.succ_pos k) (by rw [hdeg])
      s hsm hsroot hsurj (rL - 1) (rR + 1)
      (fun i => by have := hrL1 i; linarith) (fun i => by have := hrR1 i; linarith)
      (by have := hrL1 0; have := hrR1 0; linarith)
      ⟨rL, by linarith [hrL1 0], hrL1, hrL2⟩ ⟨rR, hrR1, by linarith [hrR1 0], hrR2⟩
  · obtain ⟨r, _, _, hrsimple, _, hrsurj⟩ :=
      rootFamily_X_mul_sub hgi hXpq0 (k + 1) (Nat.succ_pos k) (by rw [hdeg])
        s hsm hsroot hsurj (rL - 1) (rR + 1)
        (fun i => by have := hrL1 i; linarith) (fun i => by have := hrR1 i; linarith)
        (by have := hrL1 0; have := hrR1 0; linarith)
        ⟨rL, by linarith [hrL1 0], hrL1, hrL2⟩ ⟨rR, hrR1, by linarith [hrR1 0], hrR2⟩
    intro w hw
    obtain ⟨i, rfl⟩ := hrsurj w hw
    exact hrsimple i

/-- **HL geometric invariant (TARGET).** `μ(G)` real-rooted with simple roots, and every
`μ(G∖a)` interlaces it geometrically. The induction carries THIS — no algebraic `Interlace`,
no HKO. -/
def HLGeom_target (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  MSS.RealRooted G.matchingPoly ∧
    (∀ r, G.matchingPoly.IsRoot r → G.matchingPoly.rootMultiplicity r = 1) ∧
    ∀ a : V, GeomInterlaced (G.deleteIncidenceSet a).matchingPoly G.matchingPoly

/-- **HL geometric recurrence step (TARGET — the one remaining synthesis, HKO-free).** If `p` is
real-rooted with simple roots and `q` interlaces `p` geometrically (with the matching recurrence's
leading-coeff / degree conditions), then `X·p − q` is real-rooted with simple roots and `p`
interlaces `X·p − q` geometrically. Plan: build the `m+2`-point sequence (p's roots via
`exists_strictMono_roots` + the `±∞` end-gap atoms), get alternation of `X·p − q` from
`eval_X_mul_sub_at_isRoot` (`= −q` at p's roots) + `GeomInterlaced`, then `realRooted_of_root_per_gap`.
The only `Fin`/parity bookkeeping left on the geometric route. -/
def hl_geom_recurrence_target (p q : Polynomial ℝ) : Prop :=
  MSS.RealRooted p → (∀ r, p.IsRoot r → p.rootMultiplicity r = 1) →
    GeomInterlaced q p → 0 < p.leadingCoeff → q.natDegree ≤ p.natDegree →
    MSS.RealRooted (Polynomial.X * p - q) ∧ GeomInterlaced p (Polynomial.X * p - q)

/-- **Base case — re-export.** `μ(⊥)` is real-rooted, anchoring the interlacing induction. -/
theorem matchingPoly_bot_realRooted' :
    MSS.RealRooted ((⊥ : SimpleGraph V).matchingPoly) :=
  matchingPoly_bot_realRooted

end SimpleGraph
