/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import MatchingPoly

/-!
# Godsil's moment theorem — combinatorial core (Part III, brick 3, analytic heart)

Toward Godsil's moment theorem `p_k = Σ θᵢᵏ = #closed tree-like walks` (the matching side of the
trace-formula bridge, see `Ihara/TreeLikeWalks.lean`). The route is the log-derivative identity
`μ'(G)/μ(G) = Σ_v μ(G−v)/μ(G)`, whose algebraic shadow is the **vertex-deletion derivative law**
`Σ_v μ(G−v) = X·μ'(G)`. Its combinatorial heart is the double-count

  `Σ_v m_k(G−v) = (n − 2k)·m_k(G)`,

proved here: summing "`k`-matchings avoiding `v`" over `v` counts each `k`-matching once per
uncovered vertex, and a `k`-matching covers exactly `2k` vertices.
-/

open Finset Polynomial

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **A `k`-matching covers exactly `2k` vertices**, hence leaves `n − 2k` uncovered:
`#{ v : ∀ e ∈ s, v ∉ e } = n − 2k`. -/
theorem card_uncovered_of_mem_matchingsOfCard {k : ℕ} {s : Finset (Sym2 V)}
    (hs : s ∈ G.matchingsOfCard k) :
    #(univ.filter fun w : V => ∀ e ∈ s, w ∉ e) = Fintype.card V - 2 * k := by
  obtain ⟨hsub, hcard, hmatch⟩ := mem_matchingsOfCard.mp hs
  -- edges of the matching are pairwise vertex-disjoint
  have hdisj : ∀ e ∈ s, ∀ f ∈ s, e ≠ f → Disjoint e.toFinset f.toFinset := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro w hwe hwf
    exact hmatch e he f hf hef w (Sym2.mem_toFinset.mp hwe) (Sym2.mem_toFinset.mp hwf)
  -- the covered set is the disjoint union of the edges' endpoint-pairs, of size `2k`
  have hcov : #(s.biUnion fun e => e.toFinset) = 2 * k := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun e he =>
      Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeFinset (hsub he))),
      Finset.sum_const, hcard, smul_eq_mul, Nat.mul_comm]
  -- the uncovered set is the complement of the covered set
  have hueq : (univ.filter fun w : V => ∀ e ∈ s, w ∉ e)
      = univ \ (s.biUnion fun e => e.toFinset) := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_biUnion, not_exists, not_and,
      Sym2.mem_toFinset]
  rw [hueq, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, hcov]

/-- **The vertex-deletion double-count** `Σ_v m_k(G−v) = (n − 2k)·m_k(G)`: summing, over all
vertices `v`, the `k`-matchings of `G−v` (= the `k`-matchings of `G` avoiding `v`) tallies each
`k`-matching once for each of its `n − 2k` uncovered vertices. This is the combinatorial heart of
Godsil's moment theorem. -/
theorem sum_matchingNumber_deleteIncidenceSet (k : ℕ) :
    ∑ v : V, (G.deleteIncidenceSet v).matchingNumber k
      = (Fintype.card V - 2 * k) * G.matchingNumber k := by
  have key : ∀ s ∈ G.matchingsOfCard k,
      (∑ _v : V, if (∀ e ∈ s, _v ∉ e) then (1 : ℕ) else 0) = Fintype.card V - 2 * k := by
    intro s hs
    rw [← Finset.card_filter]
    exact card_uncovered_of_mem_matchingsOfCard G hs
  calc ∑ v : V, (G.deleteIncidenceSet v).matchingNumber k
      = ∑ v : V, ∑ s ∈ G.matchingsOfCard k, if (∀ e ∈ s, v ∉ e) then (1 : ℕ) else 0 := by
        simp only [matchingNumber_deleteIncidenceSet, Finset.card_filter]
    _ = ∑ s ∈ G.matchingsOfCard k, ∑ v : V, if (∀ e ∈ s, v ∉ e) then (1 : ℕ) else 0 :=
        Finset.sum_comm
    _ = ∑ _s ∈ G.matchingsOfCard k, (Fintype.card V - 2 * k) := Finset.sum_congr rfl key
    _ = (Fintype.card V - 2 * k) * G.matchingNumber k := by
        rw [Finset.sum_const, matchingNumber, smul_eq_mul, Nat.mul_comm]

/-- `X · d/dX (Xᵐ) = C(m) · Xᵐ` — handles the `m = 0` boundary cleanly (both sides `0`). -/
theorem X_mul_derivative_X_pow (m : ℕ) :
    (X : ℝ[X]) * derivative (X ^ m) = C (m : ℝ) * X ^ m := by
  rcases m with _ | m
  · simp
  · rw [derivative_X_pow, Nat.add_sub_cancel]; ring

/-- **The vertex-deletion derivative law** `Σ_v μ(G−v) = X·μ'(G)` (fixed-`n` incidence-deletion form:
`G.deleteIncidenceSet v` isolates `v`, so `μ(G.deleteIncidenceSet v)` plays the role of `X·μ(G−v)`).
The matching-polynomial mirror of `char'(A) = Σ_v char(A_v̂)`, and the log-derivative
`μ'/μ = Σ_v μ(G−v)/μ(G)` opening Godsil's tree-like-walk generating function. Termwise from the
double-count `sum_matchingNumber_deleteIncidenceSet`. -/
theorem sum_matchingPoly_deleteIncidenceSet :
    ∑ v : V, (G.deleteIncidenceSet v).matchingPoly = X * derivative G.matchingPoly := by
  simp only [matchingPoly]
  rw [Finset.sum_comm, derivative_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hAB : (∑ v : V, (-1 : ℝ) ^ k * ((G.deleteIncidenceSet v).matchingNumber k : ℝ))
      = (-1 : ℝ) ^ k * (G.matchingNumber k : ℝ) * ((Fintype.card V - 2 * k : ℕ) : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum, sum_matchingNumber_deleteIncidenceSet]
    push_cast; ring
  rw [← Finset.sum_mul, derivative_C_mul, mul_left_comm, X_mul_derivative_X_pow, ← map_sum, hAB,
    map_mul]
  ring

end SimpleGraph
