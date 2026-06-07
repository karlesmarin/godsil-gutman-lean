/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.ZMod.Basic

/-!
# Walk counting for a finite digraph (the power of a `0-1` matrix)

For a decidable relation `r` on a finite type `V` (a finite directed graph) we count directed walks
by powers of its `0-1` adjacency matrix. This is the directed-graph analogue of
`SimpleGraph.adjMatrix_pow_apply_eq_card_walk`, which Mathlib only provides for *undirected* simple
graphs.

## Main definitions

* `relMatrix r` — the `ℕ`-valued `0-1` adjacency matrix of `r`.
* `relWalks r k i j` — the finset of length-`k` directed `r`-walks from `i` to `j`, as vertex lists.

## Main results

* `relMatrix_pow_apply` — `((relMatrix r) ^ k) i j = (relWalks r k i j).card`.
-/

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (r : V → V → Prop) [DecidableRel r]

/-- The `ℕ`-valued `0-1` adjacency matrix of a decidable relation `r`. -/
def relMatrix : Matrix V V ℕ := fun i j => if r i j then 1 else 0

/-- The finset of length-`k` directed `r`-walks from `i` to `j`, encoded as the list of visited
vertices `[i, …, j]`. -/
def relWalks : ℕ → V → V → Finset (List V)
  | 0, i, j => if i = j then {[i]} else ∅
  | k + 1, i, j =>
    Finset.univ.biUnion fun l =>
      if r i l then (relWalks k l j).map ⟨List.cons i, fun _ _ => by simp⟩ else ∅

section PowSum
variable {R : Type*} [CommSemiring R]

/-- The `(i, j)` entry of `Mᵏ` as a sum, over length-`k` vertex walks `i → j` (encoded as
`Fin (k+1) → V` tuples with fixed endpoints), of the product of the edge weights. -/
theorem pow_apply_eq_sum (M : Matrix V V R) (k : ℕ) (i j : V) :
    (M ^ k) i j = ∑ p : Fin (k + 1) → V,
      if p 0 = i ∧ p (Fin.last k) = j then ∏ t : Fin k, M (p t.castSucc) (p t.succ) else 0 := by
  induction k generalizing i with
  | zero =>
    rw [pow_zero, Matrix.one_apply, Finset.sum_eq_single (fun _ => i)]
    · simp [Fin.last_zero]
    · intro p _ hp
      have hpi : p 0 ≠ i := fun h => hp (funext fun a => by rw [Fin.eq_zero a]; exact h)
      simp [Fin.last_zero, hpi]
    · intro h; exact absurd (Finset.mem_univ _) h
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    have hL : ∀ p : Fin (k + 1) → V,
        (∑ l : V, if p 0 = l ∧ p (Fin.last k) = j then M i l * ∏ t : Fin k,
            M (p t.castSucc) (p t.succ) else 0)
          = if p (Fin.last k) = j then M i (p 0) * ∏ t : Fin k, M (p t.castSucc) (p t.succ)
            else 0 := by
      intro p
      by_cases hj : p (Fin.last k) = j
      · simp only [hj, and_true]
        rw [Finset.sum_ite_eq]
        simp
      · simp [hj]
    rw [Finset.sum_congr rfl fun p _ => hL p,
      ← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 2) => V)), Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Fin.consEquiv_apply, Fin.cons_zero, ← Fin.succ_last, Fin.cons_succ,
      Fin.prod_univ_succ, Fin.castSucc_zero, Fin.succ_castSucc, Fin.cons_zero, Fin.cons_succ]
    by_cases hQ : p (Fin.last k) = j
    · simp only [hQ, and_true]
      rw [Finset.sum_ite_eq']
      simp
    · simp [hQ]

/-- **The trace of `Mᵏ` counts closed walks.** It is the sum, over closed length-`k` walks (tuples
`p : Fin (k+1) → V` with `p 0 = p (last)`), of the product of the edge weights. -/
theorem trace_pow_eq_sum_closed (M : Matrix V V R) (k : ℕ) :
    (M ^ k).trace = ∑ p : Fin (k + 1) → V,
      if p 0 = p (Fin.last k) then ∏ t : Fin k, M (p t.castSucc) (p t.succ) else 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, pow_apply_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : p 0 = p (Fin.last k)
  · rw [if_pos h, Finset.sum_eq_single (p 0)]
    · simp [h.symm]
    · intro a _ ha; rw [if_neg]; rintro ⟨h1, -⟩; exact ha h1.symm
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun a _ => if_neg ?_
    rintro ⟨h1, h2⟩; exact h (h1.trans h2.symm)

/-! ## Rotation invariance — toward closed geodesics -/

/-- The **cyclic product** of edge weights along a closed walk `w : ZMod n → V`,
`∏ₜ M (w t) (w (t+1))` with the index addition taken cyclically in `ZMod n`. -/
def cyclicProd {n : ℕ} [NeZero n] (M : Matrix V V R) (w : ZMod n → V) : R :=
  ∏ t : ZMod n, M (w t) (w (t + 1))

/-- **Rotation invariance.** The cyclic product is unchanged when the basepoint of the closed walk
is rotated by `c`. This is what makes the weight a class function on rotation orbits — the structure
that groups closed non-backtracking walks into (prime) geodesics. -/
theorem cyclicProd_comp_addRight {n : ℕ} [NeZero n] (M : Matrix V V R) (w : ZMod n → V)
    (c : ZMod n) : cyclicProd M (w ∘ Equiv.addRight c) = cyclicProd M w := by
  simp only [cyclicProd, Function.comp_apply]
  rw [← Equiv.prod_comp (Equiv.addRight c) fun t => M (w t) (w (t + 1))]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp [add_right_comm]

end PowSum

variable {r}

/-- Every walk in `relWalks r k i j` starts at `i`. -/
theorem head?_of_mem_relWalks {k : ℕ} {i j : V} {w : List V} (hw : w ∈ relWalks r k i j) :
    w.head? = some i := by
  cases k with
  | zero =>
    rw [relWalks] at hw
    split_ifs at hw with h
    · simp only [Finset.mem_singleton] at hw; subst hw; rfl
    · simp at hw
  | succ k =>
    rw [relWalks, Finset.mem_biUnion] at hw
    obtain ⟨l, -, hl⟩ := hw
    split_ifs at hl with h
    · rw [Finset.mem_map] at hl
      obtain ⟨p, -, rfl⟩ := hl
      rfl
    · simp at hl

/-- **Powers of the `0-1` adjacency matrix count directed walks.** -/
theorem relMatrix_pow_apply (k : ℕ) (i j : V) :
    ((relMatrix r) ^ k) i j = (relWalks r k i j).card := by
  induction k generalizing i with
  | zero =>
    rw [pow_zero, Matrix.one_apply, relWalks]
    split_ifs with h <;> simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, relWalks]
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [relMatrix]
      split_ifs with h
      · rw [Finset.card_map, ih, one_mul]
      · rw [zero_mul, Finset.card_empty]
    · intro l _ l' _ hll
      simp only [Finset.disjoint_left]
      intro w hw hw'
      apply hll
      split_ifs at hw hw' with h h'
      · rw [Finset.mem_map] at hw hw'
        obtain ⟨p, hp, rfl⟩ := hw
        obtain ⟨p', hp', hpp'⟩ := hw'
        simp only [Function.Embedding.coeFn_mk, List.cons.injEq] at hpp'
        have := head?_of_mem_relWalks hp
        have := head?_of_mem_relWalks (hpp'.2 ▸ hp')
        simp_all
      · simp at hw'
      · simp at hw
      · simp at hw
