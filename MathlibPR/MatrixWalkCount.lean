/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators

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
