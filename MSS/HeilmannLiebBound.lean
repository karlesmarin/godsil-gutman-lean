/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import RealStable
public import RamanujanBound
public import MatchingPoly
public import MSS.ForestRealRooted
public import MSS.ForestComponents
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Heilmann–Lieb root bound — the Ramanujan band `[−2√(Δ−1), 2√(Δ−1)]`

This file assembles the second half of Heilmann–Lieb: for a finite graph `G` of maximum degree `Δ`,
every root of `μ(G)` lies in `[−2√(Δ−1), 2√(Δ−1)] = [−bruhatTitsBound Δ, bruhatTitsBound Δ]`
(`MSS.BoundedBy G.matchingPoly (bruhatTitsBound Δ)`). The real-rootedness half (`matchingPoly_realRooted`,
T6) is already sorry-free; this file adds the magnitude bound.

## Decomposition (route via the path tree + a weighted Gershgorin / Collatz–Wielandt argument)

1. **Matrix bound (`collatzWielandt`, PROVEN)** — graph-free. For a matrix `A` with nonnegative
   entries and a strictly positive test vector `w` with weighted row sums `∑ⱼ Aᵢⱼ wⱼ ≤ B wᵢ`, every
   real eigenvalue (root of `A.charpoly`) satisfies `|μ| ≤ B`. Proof: the weighted eigenvector /
   argmax-coordinate argument (`Matrix.exists_mulVec_eq_zero_iff` for the eigenvector,
   `Finset.exists_max_image` for the coordinate maximising `|vⱼ|/wⱼ`).

2. **Forest eigenvalue bound (`forest_bounded_target`)** — for a forest `F` with `deg ≤ Δ`,
   `BoundedBy F.matchingPoly (bruhatTitsBound Δ)`. Since `μ(F) = charpoly(A_F)` (T2,
   `matchingPoly_forest_eq_charpoly`) and `A_F` is symmetric (`isSymm_adjMatrix`), apply (1) with the
   **local test weights** `w_child = w_parent / √(d_parent − 1)` (root weight `1`). The weighted row
   sum at a non-root vertex `v` telescopes to `√(d_parent − 1) + √(d_v − 1) ≤ 2√(Δ − 1)` (in a tree
   every neighbour of `v` is at distance `±1` from the root, exactly one being the parent); at the
   root it is `d_root / √(d_root − 1) ≤ 2√(Δ − 1)`.

3. **Transfer (`connected_matchingPoly_bounded`, PROVEN below modulo 1–2 + the path-tree degree
   bound)** — `μ(G) ∣ μ(T(G,u))` (brick (e)) and `T(G,u)` is a forest with `deg ≤ Δ`, so the band of
   `μ(T)` transfers to `μ(G)` via `BoundedBy.of_dvd`.

Item (1) is now PROVEN (`collatzWielandt`, sorry-free); (2) and the path-tree degree bound remain
honest `Prop` targets (not vacuous theorems), as does the transfer (whnf wall, see (3)).
-/

@[expose] public section

namespace SimpleGraph

open Polynomial Matrix MSS

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **(1) Weighted Gershgorin / Collatz–Wielandt (PROVEN, graph-free).** A nonnegative matrix with a
strictly positive test vector `w` whose weighted row sums satisfy `∑ⱼ Aᵢⱼ wⱼ ≤ B wᵢ` has every real
eigenvalue (root of `A.charpoly`) bounded by `B` in absolute value.

Proof = the weighted eigenvector argument (Collatz–Wielandt): a charpoly root yields an eigenvector
`v ≠ 0` (`Matrix.exists_mulVec_eq_zero_iff` via `eval_charpoly`); pick the coordinate `k` maximising
`|vⱼ|/wⱼ`; then `|μ|·|v_k| = |∑ⱼ A_kⱼ vⱼ| ≤ ∑ⱼ A_kⱼ wⱼ (|vⱼ|/wⱼ) ≤ (∑ⱼ A_kⱼ wⱼ)(|v_k|/w_k) ≤
B w_k (|v_k|/w_k) = B|v_k|`, and `|v_k| > 0`. -/
theorem collatzWielandt {W : Type*} [Fintype W] [DecidableEq W]
    (A : Matrix W W ℝ) (w : W → ℝ) (B : ℝ)
    (hw : ∀ i, 0 < w i) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j * w j ≤ B * w i)
    (μ : ℝ) (hμ : A.charpoly.IsRoot μ) : |μ| ≤ B := by
  -- (a) eigenvector from the charpoly root
  have hdet : (Matrix.scalar W μ - A).det = 0 := by
    have h := Matrix.eval_charpoly A μ; rw [← h]; exact hμ
  obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hsc : (Matrix.scalar W μ) *ᵥ v = μ • v := by
    ext i; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply]
  have hAv : A *ᵥ v = μ • v := by
    have hsub : (Matrix.scalar W μ) *ᵥ v - A *ᵥ v = 0 := by
      rw [← Matrix.sub_mulVec]; exact hMv
    rw [hsc] at hsub; exact (sub_eq_zero.mp hsub).symm
  have heig : ∀ i, ∑ j, A i j * v j = μ * v i := by
    intro i
    have hi := congrFun hAv i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    exact hi
  -- (b) argmax coordinate
  have hne : Nonempty W := by
    obtain ⟨i, _⟩ := Function.ne_iff.mp hv0; exact ⟨i⟩
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image Finset.univ (fun i => |v i| / w i) Finset.univ_nonempty
  have hvk : v k ≠ 0 := by
    intro hk0; apply hv0; funext i
    have hle := hk i (Finset.mem_univ i)
    rw [hk0, abs_zero, zero_div] at hle
    have h0 : |v i| / w i = 0 := le_antisymm hle (div_nonneg (abs_nonneg _) (hw i).le)
    rw [div_eq_zero_iff, or_iff_left (hw i).ne'] at h0
    simpa using abs_eq_zero.mp h0
  have habsvk : 0 < |v k| := abs_pos.mpr hvk
  -- (c) the weighted Collatz–Wielandt chain
  have key : |μ| * |v k| ≤ B * |v k| := by
    calc |μ| * |v k| = |μ * v k| := (abs_mul μ (v k)).symm
      _ = |∑ j, A k j * v j| := by rw [← heig k]
      _ ≤ ∑ j, |A k j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, A k j * |v j| := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [abs_mul, abs_of_nonneg (hA k j)]
      _ ≤ ∑ j, A k j * (w j * (|v k| / w k)) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (hA k j)
          have hwj : w j ≠ 0 := (hw j).ne'
          have heqj : w j * (|v j| / w j) = |v j| := by field_simp
          calc |v j| = w j * (|v j| / w j) := heqj.symm
            _ ≤ w j * (|v k| / w k) :=
                mul_le_mul_of_nonneg_left (hk j (Finset.mem_univ j)) (hw j).le
      _ = (∑ j, A k j * w j) * (|v k| / w k) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ (B * w k) * (|v k| / w k) :=
          mul_le_mul_of_nonneg_right (hrow k) (div_nonneg (abs_nonneg _) (hw k).le)
      _ = B * |v k| := by
          have hwk : w k ≠ 0 := (hw k).ne'
          rw [mul_assoc]; congr 1; field_simp
  exact le_of_mul_le_mul_right key habsvk

/-- **(2a) Forest bound from a test weight (PROVEN, glue).** Reduces the forest band bound to
exhibiting a strictly positive weight `w` with `∑ᵤ A_vu wᵤ ≤ (bruhatTitsBound Δ)·w_v` for all `v`:
`μ(F) = charpoly(A_F)` (T4) is real-rooted, and `collatzWielandt` bounds its roots by `bruhatTitsBound
Δ`. The adjacency matrix is nonnegative (`adjMatrix_apply`). -/
theorem forest_bounded_of_weight {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj] (hF : F.IsAcyclic) (Δ : ℕ)
    (w : W → ℝ) (hw : ∀ v, 0 < w v)
    (hrow : ∀ v, ∑ u, (F.adjMatrix ℝ) v u * w u ≤ bruhatTitsBound Δ * w v) :
    BoundedBy F.matchingPoly (bruhatTitsBound Δ) := by
  refine ⟨F.matchingPoly_forest_realRooted hF, fun x hx => ?_⟩
  rw [F.matchingPoly_forest_eq_charpoly hF] at hx
  refine collatzWielandt (F.adjMatrix ℝ) w (bruhatTitsBound Δ) hw (fun i j => ?_) hrow x hx
  rw [adjMatrix_apply]; split <;> norm_num

/-- **(2b-arith) The row-sum bound, pure arithmetic (PROVEN).** With depth `δ`, base `s = √(Δ−1)`
and weight `wᵤ = s^(−δ u)`, given that every summand index `u ∈ N` is at depth `d±1`
(`hpm`), at most one is closer (`hpar`), and `|N| ≤ Δ`, the weighted neighbour sum is `≤ 2s · s^(−d)
= bruhatTitsBound Δ · w_v`. Closer terms equal `s^(−d)·s`, farther terms `s^(−d)·s⁻¹`; the count
inequality `a·(Δ−1) + b ≤ 2(Δ−1)` (`a ≤ 1`, `a+b ≤ Δ`, `Δ ≥ 2`, i.e. `(Δ−2)(1−a) ≥ 0`) closes it. -/
theorem rowsum_arith {W : Type*} [DecidableEq W]
    (N : Finset W) (δ : W → ℕ) (d : ℕ) (s : ℝ) (Δ : ℕ)
    (hs : 0 < s) (hs2 : s ^ 2 = (Δ : ℝ) - 1) (hΔ : 2 ≤ Δ)
    (hcard : N.card ≤ Δ)
    (hpm : ∀ u ∈ N, δ u = d + 1 ∨ δ u + 1 = d)
    (hpar : (N.filter (fun u => δ u + 1 = d)).card ≤ 1) :
    ∑ u ∈ N, s ^ (-(δ u : ℤ)) ≤ (2 * s) * s ^ (-(d : ℤ)) := by
  classical
  have hsne : s ≠ 0 := hs.ne'
  have hΔr : (2 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hPval : ∀ u ∈ N.filter (fun u => δ u + 1 = d),
      s ^ (-(δ u : ℤ)) = s ^ (-(d : ℤ)) * s := by
    intro u hu; obtain ⟨_, hud⟩ := Finset.mem_filter.mp hu
    have hd : (δ u : ℤ) = (d : ℤ) - 1 := by omega
    rw [hd, show -((d : ℤ) - 1) = -(d : ℤ) + 1 from by ring, zpow_add₀ hsne, zpow_one]
  have hQval : ∀ u ∈ N.filter (fun u => ¬ (δ u + 1 = d)),
      s ^ (-(δ u : ℤ)) = s ^ (-(d : ℤ)) * s⁻¹ := by
    intro u hu; obtain ⟨huN, hud⟩ := Finset.mem_filter.mp hu
    have hdu : δ u = d + 1 := by
      rcases hpm u huN with h | h
      · exact h
      · exact absurd h hud
    have hd : (δ u : ℤ) = (d : ℤ) + 1 := by rw [hdu]; push_cast; ring
    rw [hd, show -((d : ℤ) + 1) = -(d : ℤ) - 1 from by ring, zpow_sub₀ hsne, zpow_one,
      div_eq_mul_inv]
  have hsplit : (∑ u ∈ N.filter (fun u => δ u + 1 = d), s ^ (-(δ u : ℤ)))
      + (∑ u ∈ N.filter (fun u => ¬ (δ u + 1 = d)), s ^ (-(δ u : ℤ)))
      = ∑ u ∈ N, s ^ (-(δ u : ℤ)) :=
    Finset.sum_filter_add_sum_filter_not N _ _
  have hPsum : (∑ u ∈ N.filter (fun u => δ u + 1 = d), s ^ (-(δ u : ℤ)))
      = ((N.filter (fun u => δ u + 1 = d)).card : ℝ) * (s ^ (-(d : ℤ)) * s) := by
    rw [Finset.sum_congr rfl hPval, Finset.sum_const, nsmul_eq_mul]
  have hQsum : (∑ u ∈ N.filter (fun u => ¬ (δ u + 1 = d)), s ^ (-(δ u : ℤ)))
      = ((N.filter (fun u => ¬ (δ u + 1 = d))).card : ℝ) * (s ^ (-(d : ℤ)) * s⁻¹) := by
    rw [Finset.sum_congr rfl hQval, Finset.sum_const, nsmul_eq_mul]
  set a : ℝ := ((N.filter (fun u => δ u + 1 = d)).card : ℝ) with ha_def
  set b : ℝ := ((N.filter (fun u => ¬ (δ u + 1 = d))).card : ℝ) with hb_def
  have ha1 : a ≤ 1 := by rw [ha_def]; exact_mod_cast hpar
  have hab : a + b ≤ (Δ : ℝ) := by
    have hsum := Finset.filter_card_add_filter_neg_card_eq_card
      (s := N) (p := fun u => δ u + 1 = d)
    rw [ha_def, hb_def, ← Nat.cast_add, hsum]; exact_mod_cast hcard
  have hc : (0 : ℝ) < s ^ (-(d : ℤ)) := zpow_pos hs _
  have key : a * s + b * s⁻¹ ≤ 2 * s := by
    rw [← sub_nonneg]
    have heq : 2 * s - (a * s + b * s⁻¹) = (2 * s ^ 2 - a * s ^ 2 - b) * s⁻¹ := by
      field_simp; ring
    rw [heq]
    refine mul_nonneg ?_ (le_of_lt (inv_pos.mpr hs))
    rw [hs2]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (Δ : ℝ) - 2) (by linarith : (0 : ℝ) ≤ 1 - a), hab]
  calc ∑ u ∈ N, s ^ (-(δ u : ℤ))
      = (∑ u ∈ N.filter (fun u => δ u + 1 = d), s ^ (-(δ u : ℤ)))
        + (∑ u ∈ N.filter (fun u => ¬ (δ u + 1 = d)), s ^ (-(δ u : ℤ))) := hsplit.symm
    _ = a * (s ^ (-(d : ℤ)) * s) + b * (s ^ (-(d : ℤ)) * s⁻¹) := by rw [hPsum, hQsum]
    _ = s ^ (-(d : ℤ)) * (a * s + b * s⁻¹) := by ring
    _ ≤ s ^ (-(d : ℤ)) * (2 * s) := mul_le_mul_of_nonneg_left key (le_of_lt hc)
    _ = 2 * s * s ^ (-(d : ℤ)) := by ring

/-- **(2b-tree, Fact 1 — PROVEN) Adjacent vertices differ in root-distance by exactly 1.** For an
acyclic `F`, a root `ρ`, an edge `u ∼ v` with `u` reachable from `ρ`: `dist ρ u = dist ρ v + 1` or
`dist ρ u + 1 = dist ρ v`. The `≤ 1` bounds are `dist_le` on the shortest path concatenated with the
edge; the `≠` is bipartiteness (`IsAcyclic.isBipartite`): a `Bool`-colouring `c` has
`Even (dist ρ ·) ↔ (c ρ ↔ c ·)` (`even_length_iff_congr` on shortest paths), and `c u ≠ c v`
(`Coloring.valid`), so equal distances would force equal parities, contradiction. -/
theorem forest_adj_dist_pm_one {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj] (hF : F.IsAcyclic) (ρ : W) {u v : W}
    (huv : F.Adj u v) (hu : F.Reachable ρ u) :
    F.dist ρ u = F.dist ρ v + 1 ∨ F.dist ρ u + 1 = F.dist ρ v := by
  classical
  have hv : F.Reachable ρ v := hu.trans huv.reachable
  obtain ⟨c0⟩ := IsAcyclic.isBipartite hF
  have c : F.Coloring Bool := Coloring.mk (finTwoEquiv ∘ c0)
    (fun {a b} hab h => c0.valid hab (finTwoEquiv.injective h))
  have hne : F.dist ρ u ≠ F.dist ρ v := by
    intro heq
    obtain ⟨pu, hpu⟩ := hu.exists_walk_length_eq_dist
    obtain ⟨pv, hpv⟩ := hv.exists_walk_length_eq_dist
    have eu := Coloring.even_length_iff_congr c pu
    have ev := Coloring.even_length_iff_congr c pv
    rw [hpu, heq] at eu
    rw [hpv] at ev
    have hiff : (c ρ ↔ c u) ↔ (c ρ ↔ c v) := eu.symm.trans ev
    have hcuv := c.valid huv
    revert hcuv hiff
    cases c ρ <;> cases c u <;> cases c v <;> simp_all
  have hle1 : F.dist ρ u ≤ F.dist ρ v + 1 := by
    obtain ⟨pv, hpv⟩ := hv.exists_walk_length_eq_dist
    calc F.dist ρ u ≤ (pv.concat huv.symm).length := SimpleGraph.dist_le _
      _ = F.dist ρ v + 1 := by rw [Walk.length_concat, hpv]
  have hle2 : F.dist ρ v ≤ F.dist ρ u + 1 := by
    obtain ⟨pu, hpu⟩ := hu.exists_walk_length_eq_dist
    calc F.dist ρ v ≤ (pu.concat huv).length := SimpleGraph.dist_le _
      _ = F.dist ρ u + 1 := by rw [Walk.length_concat, hpu]
  omega

/-- A shortest walk is a path: there is a `p : Walk ρ x` with `p.IsPath` and `p.length = dist ρ x`
(`bypass` of any minimal-length walk). -/
theorem exists_isPath_length_eq_dist {W : Type*} [DecidableEq W] (F : SimpleGraph W)
    {ρ x : W} (hr : F.Reachable ρ x) :
    ∃ p : F.Walk ρ x, p.IsPath ∧ p.length = F.dist ρ x := by
  obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
  exact ⟨w.bypass, w.bypass_isPath,
    le_antisymm ((w.length_bypass_le).trans hw.le) (SimpleGraph.dist_le _)⟩

/-- **(2b-tree, Fact 2 — PROVEN) At most one neighbour is one step closer to the root.** For an
acyclic `F` and any `ρ, v`, at most one neighbour `u` of `v` has `dist ρ u + 1 = dist ρ v`. Two such
`u₁, u₂` give two shortest paths `ρ → v` ending in the edges `s(v,u₁)`, `s(v,u₂)`; by `path_unique`
these paths coincide, and `IsPath.eq_penultimate_of_mem_edges` makes both `u₁` and `u₂` the (unique)
penultimate vertex, so `u₁ = u₂`. -/
theorem forest_le_one_parent {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj] (hF : F.IsAcyclic) (ρ v : W) :
    ((F.neighborFinset v).filter (fun u => F.dist ρ u + 1 = F.dist ρ v)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro u1 h1 u2 h2
  rw [Finset.mem_filter, mem_neighborFinset] at h1 h2
  obtain ⟨ha1, hd1⟩ := h1
  obtain ⟨ha2, hd2⟩ := h2
  have hvr : F.Reachable ρ v := Reachable.of_dist_ne_zero (by omega : F.dist ρ v ≠ 0)
  have hu1r : F.Reachable ρ u1 := hvr.trans ha1.reachable
  have hu2r : F.Reachable ρ u2 := hvr.trans ha2.reachable
  obtain ⟨p1, hp1, hl1⟩ := F.exists_isPath_length_eq_dist hu1r
  obtain ⟨p2, hp2, hl2⟩ := F.exists_isPath_length_eq_dist hu2r
  have hv1 : v ∉ p1.support := by
    intro hmem
    have h := SimpleGraph.dist_le (p1.takeUntil v hmem)
    have h' := p1.length_takeUntil_le hmem
    omega
  have hv2 : v ∉ p2.support := by
    intro hmem
    have h := SimpleGraph.dist_le (p2.takeUntil v hmem)
    have h' := p2.length_takeUntil_le hmem
    omega
  have hP1 : (p1.concat ha1.symm).IsPath := hp1.concat hv1 ha1.symm
  have hP2 : (p2.concat ha2.symm).IsPath := hp2.concat hv2 ha2.symm
  have hPeq : (⟨p1.concat ha1.symm, hP1⟩ : F.Path ρ v) = ⟨p2.concat ha2.symm, hP2⟩ :=
    hF.path_unique _ _
  have hwalk : p1.concat ha1.symm = p2.concat ha2.symm := by
    simpa using congrArg Subtype.val hPeq
  have he1 : s(v, u1) ∈ (p1.concat ha1.symm).edges := by
    rw [Walk.edges_concat]; simp [Sym2.eq_swap]
  have he2 : s(v, u2) ∈ (p2.concat ha2.symm).edges := by
    rw [Walk.edges_concat]; simp [Sym2.eq_swap]
  have hu1pen : u1 = (p1.concat ha1.symm).penultimate := hP1.eq_penultimate_of_mem_edges he1
  have hu2pen : u2 = (p2.concat ha2.symm).penultimate := hP2.eq_penultimate_of_mem_edges he2
  rw [hu1pen, hu2pen, hwalk]

/-- **(2) Forest adjacency eigenvalue bound (TARGET).** Type-polymorphic so it applies to the path
tree `T(G,u)` (whose vertex type differs from `V`). Reduced by `forest_bounded_of_weight` to
constructing a test weight + proving the row-sum bound.

**Hypothesis `2 ≤ Δ` is necessary**: for `Δ = 1`, `bruhatTitsBound 1 = 0`, but a single edge `K₂`
(maximum degree `1`) has `μ = X² − 1` with roots `±1`, so the band `[0,0]` is violated. Heilmann–Lieb
`2√(Δ−1)` holds for `Δ ≥ 2` (for `Δ ≤ 1` the graph is a matching, roots in `{−1,0,1}`). -/
def forest_bounded_target : Prop :=
  ∀ {W : Type*} [Fintype W] [DecidableEq W] (F : SimpleGraph W) [DecidableRel F.Adj] (Δ : ℕ),
    2 ≤ Δ → F.IsAcyclic → (∀ v, F.degree v ≤ Δ) → BoundedBy F.matchingPoly (bruhatTitsBound Δ)

/-- **(2b) The test weight (Route B, depth form).** Root each component at `(connectedComponentMk v).out`,
`depth v := dist(root v, v)`, and `w v := (√(Δ−1))^(−depth v)` (strictly positive for `Δ ≥ 2`). The
row-sum bound reduces to two tree-distance facts (the genuine remaining combinatorics):

* **`forest_dist_pm_one_target`** — every neighbour `u ∼ v` satisfies `depth u = depth v ± 1` (adjacent
  vertices differ in root-distance by `≤ 1` always, and `≠ 0` since an equal-distance neighbour would
  close an odd cycle in a forest);
* **`forest_le_one_parent_target`** — at most one neighbour of `v` has `depth = depth v − 1` (two such
  would give two distinct shortest `root→v` paths, i.e. a cycle).

Given these, `∑_{u∼v} wᵤ = w_v · (a·√(Δ−1) + b/√(Δ−1))` with `a ≤ 1` closer neighbours and
`b = deg v − a ≤ Δ − a`; then `a·(Δ−1) + b ≤ 2(Δ−1)` (using `a ≤ 1`, `deg v ≤ Δ`), i.e.
`∑_{u∼v} wᵤ ≤ bruhatTitsBound Δ · w_v`. -/
def forest_dist_pm_one_target {W : Type*} (F : SimpleGraph W) (r : W → W) : Prop :=
  ∀ ⦃u v⦄, F.Adj u v → F.dist (r v) u = F.dist (r v) v + 1 ∨ F.dist (r v) u + 1 = F.dist (r v) v

/-- See `forest_dist_pm_one_target`: at most one neighbour of `v` is strictly closer to the root. -/
def forest_le_one_parent_target {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj] (r : W → W) : Prop :=
  ∀ v, ((F.neighborFinset v).filter (fun u => F.dist (r v) u + 1 = F.dist (r v) v)).card ≤ 1

/-- **(2) Forest adjacency eigenvalue bound — PROVEN (`forest_bounded_target`).** Assembles all of
(2): root each component at `(connectedComponentMk v).out`, weight `w v = (√(Δ−1))^(−dist(r v, v))`
(positive since `Δ ≥ 2`), convert the adjacency row sum to a neighbour sum, rewrite each neighbour's
weight using `r u = r v` (`connectedComponentMk_eq_of_adj`), and apply `rowsum_arith` fed by Fact 1
(`forest_adj_dist_pm_one`) and Fact 2 (`forest_le_one_parent`); close with `forest_bounded_of_weight`
(which routes through `collatzWielandt` + `matchingPoly_forest_eq_charpoly`). -/
theorem forest_bounded_proof : forest_bounded_target := by
  intro W _ _ F _ Δ hΔ hF hdeg
  classical
  have hΔr : (2 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  set s : ℝ := Real.sqrt ((Δ : ℝ) - 1) with hs_def
  have hs : 0 < s := by rw [hs_def, Real.sqrt_pos]; linarith
  have hs2 : s ^ 2 = (Δ : ℝ) - 1 := by rw [hs_def, Real.sq_sqrt (by linarith)]
  set r : W → W := fun v => (F.connectedComponentMk v).out with hr_def
  have hr_adj : ∀ {a b : W}, F.Adj a b → r a = r b := by
    intro a b hab
    simp only [hr_def]
    exact congrArg (·.out) (ConnectedComponent.connectedComponentMk_eq_of_adj hab)
  have hrv : ∀ v, F.Reachable (r v) v := by
    intro v
    simp only [hr_def]
    exact ConnectedComponent.exact (F.connectedComponentMk v).out_eq
  refine forest_bounded_of_weight F hF Δ (fun v => s ^ (-(F.dist (r v) v : ℤ)))
    (fun v => zpow_pos hs _) ?_
  intro v
  have hconv : ∑ u, (F.adjMatrix ℝ) v u * s ^ (-(F.dist (r u) u : ℤ))
      = ∑ u ∈ F.neighborFinset v, s ^ (-(F.dist (r v) u : ℤ)) := by
    rw [neighborFinset_eq_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [adjMatrix_apply]
    by_cases h : F.Adj v u
    · rw [if_pos h, if_pos h, one_mul, hr_adj h.symm]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [hconv, show bruhatTitsBound Δ = 2 * s from by rw [bruhatTitsBound, ← hs_def]]
  exact rowsum_arith (F.neighborFinset v) (fun u => F.dist (r v) u) (F.dist (r v) v) s Δ
    hs hs2 hΔ (by rw [card_neighborFinset_eq_degree]; exact hdeg v)
    (fun u hmem => by
      rw [mem_neighborFinset] at hmem
      exact forest_adj_dist_pm_one F hF (r v) hmem.symm ((hrv v).trans hmem.reachable))
    (forest_le_one_parent F hF (r v) v)

/-- **(4) Path-tree degree bound — PROVEN.** `deg_{T(G,u)}(p) ≤ deg_G(p.endpoint) ≤ Δ`. The map
`b ↦ b.endpoint` injects the path-tree neighbours of `p` into the `G`-neighbours of `p`'s endpoint:
every neighbour `b` (a child `Grows p b` or the parent `Grows b p`) has `b.1 ∈ N_G(p.1)`; and it is
injective — two children with the same endpoint have the same (forced) walk, the parent is unique
(`Grows.parent_unique`), and a child and the parent cannot share an endpoint (the child's endpoint is
off `p`'s support, the parent's is on it). -/
theorem pathTree_degree_le (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (p : G.PathFrom u) :
    (G.pathTree u).degree p ≤ Δ := by
  classical
  rw [← card_neighborFinset_eq_degree]
  refine le_trans (Finset.card_le_card_of_injOn (fun b => b.1) ?_ ?_)
    (le_of_eq_of_le (card_neighborFinset_eq_degree G p.1) (hdeg p.1))
  · intro b hb
    rw [Finset.mem_coe, mem_neighborFinset, pathTree_adj] at hb
    rw [Finset.mem_coe, mem_neighborFinset]
    rcases hb with ⟨he, _⟩ | ⟨he, _⟩
    · exact he
    · exact he.symm
  · have child_notin : ∀ {c : G.PathFrom u}, Grows p c → c.1 ∉ p.2.1.support := by
      rintro c ⟨he, hcw⟩
      exact ((Walk.concat_isPath_iff he).mp (hcw ▸ c.2.2)).2
    have parent_in : ∀ {c : G.PathFrom u}, Grows c p → c.1 ∈ p.2.1.support := by
      rintro c ⟨he, hpw⟩
      rw [hpw, Walk.support_concat]
      exact List.mem_append_left _ c.2.1.end_mem_support
    intro b hb b' hb' hbb
    dsimp only at hbb
    rw [Finset.mem_coe, mem_neighborFinset, pathTree_adj] at hb hb'
    rcases hb with hcb | hpb <;> rcases hb' with hcb' | hpb'
    · obtain ⟨bv, bp⟩ := b
      obtain ⟨b'v, b'p⟩ := b'
      obtain ⟨he, hbw⟩ := hcb
      obtain ⟨he', hb'w⟩ := hcb'
      subst hbb
      congr 1
      exact Subtype.ext (by rw [hbw, hb'w])
    · exact absurd (show b.1 ∈ p.2.1.support from by rw [hbb]; exact parent_in hpb')
        (child_notin hcb)
    · exact absurd (show b'.1 ∈ p.2.1.support from by rw [← hbb]; exact parent_in hpb)
        (child_notin hcb')
    · exact Grows.parent_unique hpb hpb'

/-- **Path-tree degree bound (TARGET, kept for reference).** Superseded by `pathTree_degree_le`. -/
def pathTree_degree_le_target (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) : Prop :=
  ∀ u : V, ∀ p : G.PathFrom u, (G.pathTree u).degree p ≤ Δ

/-- **(3) Transfer — connected case (PROVEN).** `μ(G)` divides `μ(T(G,u))` (brick (e)), and the path
tree `T(G,u)` is a forest of maximum degree `≤ Δ` (`pathTree_degree_le`, `pathTree_isAcyclic`), so its
matching polynomial is in the Ramanujan band (`forest_bounded_proof`); `BoundedBy.of_dvd` transfers
the band to `μ(G)`. The `matchingPoly_inst_irrel` rewrite aligns the `Σ`-paths `Fintype`/`DecidableRel`
instances (the brick-(e) `whnf` wall). -/
theorem connected_matchingPoly_bounded
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (hG : G.Connected) :
    BoundedBy G.matchingPoly (bruhatTitsBound Δ) := by
  obtain ⟨u⟩ := hG.nonempty
  have hdvd := connected_matchingPoly_dvd_pathTree G hG u
  have hF := forest_bounded_proof (G.pathTree u) Δ hΔ (pathTree_isAcyclic G u)
    (pathTree_degree_le G hdeg u)
  rw [matchingPoly_inst_irrel _ _ (G.pathTree u) _ _] at hF
  exact hF.of_dvd (matchingPoly_monic (G.pathTree u)).ne_zero hdvd

/-- **Heilmann–Lieb root bound — general case (PROVEN).** For ANY finite graph `G` with `2 ≤ Δ` and
maximum degree `≤ Δ`, every root of `μ(G)` lies in the Ramanujan band `[−2√(Δ−1), 2√(Δ−1)]`. Reduces
to the connected case over components: `μ(G) = ∏_C μ(G[C.supp])`, each induced component is connected
(`maximal_connected_induce_supp`) with degree `≤ Δ` (its `G`-neighbours stay in the component, so
`degree_induce_of_neighborSet_subset` gives equality), and `BoundedBy` multiplies. -/
theorem matchingPoly_bounded (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (hdeg : ∀ v, G.degree v ≤ Δ) : BoundedBy G.matchingPoly (bruhatTitsBound Δ) := by
  classical
  rw [matchingPoly_eq_prod_components]
  refine BoundedBy.prod (fun C _ => ?_)
  refine connected_matchingPoly_bounded (G.induce (C.supp : Set V)) Δ hΔ (fun v => ?_)
    C.maximal_connected_induce_supp.1
  have hsub : G.neighborSet (↑v) ⊆ (C.supp : Set V) := by
    intro w hw
    rw [SimpleGraph.mem_neighborSet] at hw
    rw [ConnectedComponent.mem_supp_iff, ← ConnectedComponent.connectedComponentMk_eq_of_adj hw,
        ← ConnectedComponent.mem_supp_iff]
    exact v.2
  rw [degree_induce_of_neighborSet_subset hsub]
  exact hdeg ↑v

end SimpleGraph
