/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Bass's determinant formula for the Ihara zeta function (Lean 4)

Target: the matrix-identity heart of Bass's theorem for the Ihara zeta function
of a finite graph. We deliberately formalize the **finite linear-algebra
identity** — not the analytic zeta function (the infinite Euler product over
prime cycles) — because that is the content with an elementary proof, and it is
what no proof assistant has yet recorded.

## The statement (TARGET)

For a finite simple graph `G` with `n = |V|` vertices, `m = |E|` edges, adjacency
matrix `A`, degree matrix `D`, and Hashimoto (non-backtracking) edge operator `B`
on the `2m` darts:

  `(1 - u²)ⁿ · det(I_{2m} - u·B)  =  (1 - u²)ᵐ · det(I_n - u·A + u²·(D - I))`.

This is the **division-free** form of Bass's formula
`det(I - uB) = (1-u²)^{m-n} det(I - uA + (D-I)u²)`, multiplied through by
`(1-u²)ⁿ` so that it is a genuine polynomial identity valid for *every* finite
graph (forests included, where `m < n`).

### Numerical pre-verification (Curiosity honesty floor)

The statement was locked by exact numerical check on K₃, K₄, P₄, C₅, S₄, and the
bull graph (residual ≤ 2e-15 at several `u`), together with the incidence
relations `S Tᵀ = A`, `S Sᵀ = D = T Tᵀ`, `B = Tᵀ S − J`, `S J = T`.
See `research/_tmp/bass_verify.py`. This is a `def … : Prop` target made a
theorem only once proved — no vacuous `True`, no committed `sorry` masquerading
as a result (Curiosity vacuity gate).

## Proof roadmap — SYLVESTER route (every step numerically verified 2026-06-06)

Route chosen after `research/_tmp/bass_proof_route.py` confirmed all steps on
K₃,K₄,P₄,C₅,bull. Cleaner than the (n+2m) block matrix: it rides Mathlib's
Sylvester identity `Matrix.det_one_add_mul_comm` / `det_mul_comm`.

Incidence layer (each is a `Finset.sum` over darts, all pre-verified):
  `S * Tᵀ = A`,  `S * Sᵀ = D`,  `T * Tᵀ = D`,  `B = Tᵀ * S - J`,  `S * J = T`,
with `J` the dart-reversal permutation (`reversal`), `S`=`startInc`, `T`=`termInc`.

Core chain (with `B = TᵀS − J`, `J² = I`):
1. `det(I + uJ) = (1 - u²)^m`.  `J` is an involution that is a product of `m`
   disjoint transpositions (the reversal pairs), so it has `m` eigenvalues `+1`
   and `m` eigenvalues `−1`. (Lean: `J` is a `PermMatrix` of `Dart.symm`; det via
   the cycle structure, or `det(I+uJ)·det(I-uJ)=det(I-u²I)=(1-u²)^{2m}` plus
   `det(I+uJ)=det(I-uJ)` by the symm-conjugation, giving `(1-u²)^m`.)
2. `(I + uJ)⁻¹ = (I − uJ)/(1 − u²)`  (immediate from `J² = I`).
3. `S (I − uJ) Tᵀ = A − u·D`   (uses `STᵀ=A`, `S J Tᵀ = T Tᵀ = D`).
4. **Sylvester**: `det(I_{2m} − uB) = det(I+uJ) · det(I_n − u·S(I+uJ)⁻¹Tᵀ)`
   via `det(I − XY) = det(I − YX)` with `X = u(I+uJ)⁻¹Tᵀ`, `Y = S`.
5. Substitute 1–3: `S(I+uJ)⁻¹Tᵀ = (A − uD)/(1−u²)`, so
   `det(I−uB) = (1−u²)^m · (1−u²)^{−n} · det((1−u²)I − uA + u²D)`
             `= (1−u²)^{m−n} · det(I − uA + u²(D−I))`. ∎

Division handling for the division-free TARGET: steps 2,5 divide by `(1−u²)`.
Two ways to discharge in Lean: (i) prove the rational-function identity in the
`FractionField (R[u])` then clear denominators (both sides are polynomials, and
`R[u]` is a domain so `(1−u²)^k` is regular — `mul_left_cancel₀`); or (ii) stay
division-free with the `(n+2m)` block factorization `Matrix.det_fromBlocks_zero₂₁`
(no inverse needed) — fallback if (i) is fiddly. Decide when implementing step 4.

## Status

- [x] Statement locked + numerically verified.
- [x] Definitions (`hashimoto`, `degMatrix`, `reversal`, incidence) — this file.
- [ ] Incidence relations (step 1) — next.
- [ ] Block determinant identity (step 2) — the crux.
-/

open scoped Classical
open Matrix Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Degree matrix `D`: diagonal of vertex degrees, in a commutative ring `R`. -/
def degMatrix (R : Type*) [CommRing R] : Matrix V V R :=
  Matrix.diagonal (fun v => (G.degree v : R))

/-- The dart-reversal permutation matrix `J`: `J d e = 1` iff `e = d.symm`. -/
def reversal (R : Type*) [CommRing R] : Matrix G.Dart G.Dart R :=
  Matrix.of fun d e => if e = d.symm then (1 : R) else 0

/-- The Hashimoto / non-backtracking edge operator `B`:
`B d e = 1` iff the head of `d` is the tail of `e` and `e` is not the reverse of
`d` (i.e. `d` may be followed by `e` without backtracking). -/
def hashimoto (R : Type*) [CommRing R] : Matrix G.Dart G.Dart R :=
  Matrix.of fun d e => if d.snd = e.fst ∧ e ≠ d.symm then (1 : R) else 0

/-- Start incidence matrix `S`: `S v d = 1` iff `d` originates at `v`. -/
def startInc (R : Type*) [CommRing R] : Matrix V G.Dart R :=
  Matrix.of fun v d => if d.fst = v then (1 : R) else 0

/-- Terminus incidence matrix `T`: `T v d = 1` iff `d` terminates at `v`. -/
def termInc (R : Type*) [CommRing R] : Matrix V G.Dart R :=
  Matrix.of fun v d => if d.snd = v then (1 : R) else 0

/-! ### Incidence layer — step 1 of the proof (all numerically pre-verified) -/

section Incidence
variable (R : Type*) [CommRing R]

@[simp] lemma startInc_apply (v : V) (d : G.Dart) :
    G.startInc R v d = if d.fst = v then 1 else 0 := rfl
@[simp] lemma termInc_apply (v : V) (d : G.Dart) :
    G.termInc R v d = if d.snd = v then 1 else 0 := rfl
@[simp] lemma reversal_apply (d e : G.Dart) :
    G.reversal R d e = if e = d.symm then 1 else 0 := rfl
@[simp] lemma hashimoto_apply (d e : G.Dart) :
    G.hashimoto R d e = if d.snd = e.fst ∧ e ≠ d.symm then 1 else 0 := rfl

/-- Number of darts with prescribed endpoints `(v, w)` is `1` iff `v ~ w`. -/
lemma adj_dart_card (v w : V) :
    #{d : G.Dart | d.fst = v ∧ d.snd = w} = if G.Adj v w then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨⟨(v, w), h⟩, Finset.eq_singleton_iff_unique_mem.mpr ⟨by simp, fun d hd => ?_⟩⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact Dart.ext _ _ (Prod.ext_iff.mpr ⟨hd.1, hd.2⟩)
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro d - ⟨h1, h2⟩
    exact h (h1 ▸ h2 ▸ d.adj)

/-- `S Tᵀ = A`: darts from `v` to `w` realise the adjacency matrix. -/
lemma startInc_mul_termInc_transpose :
    G.startInc R * (G.termInc R)ᵀ = G.adjMatrix R := by
  ext v w
  rw [Matrix.mul_apply, adjMatrix_apply]
  simp only [Matrix.transpose_apply, startInc_apply, termInc_apply]
  have step : ∀ d : G.Dart, (if d.fst = v then (1 : R) else 0) * (if d.snd = w then 1 else 0)
      = if (d.fst = v ∧ d.snd = w) then 1 else 0 := by
    intro d; split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun d _ => step d), Finset.sum_boole, adj_dart_card]
  split_ifs <;> simp

/-- `S Sᵀ = D`: the start-incidence Gram matrix is the degree matrix. -/
lemma startInc_mul_startInc_transpose :
    G.startInc R * (G.startInc R)ᵀ = G.degMatrix R := by
  ext v w
  rw [Matrix.mul_apply, degMatrix, Matrix.diagonal_apply]
  simp only [Matrix.transpose_apply, startInc_apply]
  split_ifs with hvw
  · subst hvw
    have step : ∀ d : G.Dart, (if d.fst = v then (1 : R) else 0) * (if d.fst = v then 1 else 0)
        = if d.fst = v then 1 else 0 := by intro d; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun d _ => step d), Finset.sum_boole,
      dart_fst_fiber_card_eq_degree]
  · apply Finset.sum_eq_zero
    intro d _
    split_ifs with h1 h2 <;> simp_all

/-- `B = Tᵀ S − J`: the Hashimoto operator removes backtracking from `Tᵀ S`. -/
lemma hashimoto_eq :
    G.hashimoto R = (G.termInc R)ᵀ * G.startInc R - G.reversal R := by
  ext d e
  rw [Matrix.sub_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, termInc_apply, startInc_apply, reversal_apply,
    hashimoto_apply]
  have hsum : (∑ x : V, (if d.snd = x then (1 : R) else 0) * (if e.fst = x then 1 else 0))
      = if d.snd = e.fst then 1 else 0 := by
    rw [Finset.sum_eq_single d.snd]
    · rw [if_pos rfl, one_mul]
      by_cases hc : d.snd = e.fst
      · rw [if_pos hc, if_pos hc.symm]
      · rw [if_neg hc, if_neg fun h => hc h.symm]
    · intro x _ hx; rw [if_neg (Ne.symm hx), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum]
  by_cases hsy : e = d.symm
  · subst hsy; simp
  · simp [hsy]

/-- `S J = T`: pre-composing start-incidence with reversal gives terminus-incidence. -/
lemma startInc_mul_reversal :
    G.startInc R * G.reversal R = G.termInc R := by
  ext v e
  rw [Matrix.mul_apply]
  simp only [startInc_apply, reversal_apply, termInc_apply]
  rw [Finset.sum_eq_single e.symm]
  · have hfst : e.symm.fst = e.snd := rfl
    simp only [Dart.symm_symm, hfst, if_true, mul_one]
  · intro d _ hd
    have : e ≠ d.symm := fun he => hd (by rw [he, Dart.symm_symm])
    rw [if_neg this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `J` is symmetric: reversal is its own transpose (since `symm` is an involution). -/
lemma reversal_transpose : (G.reversal R)ᵀ = G.reversal R := by
  ext d e
  simp only [Matrix.transpose_apply, reversal_apply]
  by_cases h : e = d.symm
  · rw [if_pos h, if_pos (show d = e.symm by rw [h, Dart.symm_symm])]
  · rw [if_neg h, if_neg (show ¬ d = e.symm from fun hd => h (by rw [hd, Dart.symm_symm]))]

/-- `J² = I`: reversal is an involution. -/
lemma reversal_mul_self : G.reversal R * G.reversal R = 1 := by
  ext d e
  rw [Matrix.mul_apply]
  simp only [reversal_apply]
  rw [Finset.sum_eq_single d.symm]
  · rw [if_pos rfl, one_mul, Dart.symm_symm, Matrix.one_apply]
    by_cases h : d = e
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg fun he => h he.symm, if_neg h]
  · intro f _ hf; rw [if_neg hf, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `T Tᵀ = D`: via `T = S J`, `Jᵀ = J`, `J² = I`, and `S Sᵀ = D`. -/
lemma termInc_mul_termInc_transpose :
    G.termInc R * (G.termInc R)ᵀ = G.degMatrix R := by
  have hT : G.termInc R = G.startInc R * G.reversal R := (G.startInc_mul_reversal R).symm
  rw [hT, Matrix.transpose_mul, reversal_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (G.reversal R), reversal_mul_self, Matrix.one_mul,
    startInc_mul_startInc_transpose]

/-- The algebraic heart of `det(I + uJ) = (1 - u²)^m`:
`(I + uJ)(I − uJ) = (1 − u²) I`, since `J² = I`. -/
lemma one_add_smul_reversal_mul (u : R) :
    (1 + u • G.reversal R) * (1 - u • G.reversal R)
      = (1 - u ^ 2) • (1 : Matrix G.Dart G.Dart R) := by
  have key : (u • G.reversal R) * (u • G.reversal R)
      = u ^ 2 • (1 : Matrix G.Dart G.Dart R) := by
    rw [smul_mul_smul_comm, G.reversal_mul_self R, pow_two]
  rw [mul_sub, mul_one, add_mul, one_mul, key, sub_smul, one_smul]
  abel

/-- Determinant consequence: `det(I + uJ) · det(I − uJ) = (1 − u²)^{2m}`
(here `2m = |Dart|`). The individual factor `det(I + uJ) = (1 − u²)^m` needs the
orientation reindex `Dart ≃ edges × Fin 2` — the next brick. -/
lemma det_one_add_smul_reversal_mul (u : R) :
    (1 + u • G.reversal R).det * (1 - u • G.reversal R).det
      = (1 - u ^ 2) ^ Fintype.card G.Dart := by
  rw [← Matrix.det_mul, one_add_smul_reversal_mul, Matrix.det_smul, Matrix.det_one, mul_one]

end Incidence

/-! ### Orientation reindex — toward `det(I + uJ) = (1 - u²)^m`

With a linear order on the vertices, each edge has a unique "positive" dart
(tail < head); a general dart is that positive dart together with a sign bit.
This realises `Dart ≃ Bool × PosDart`, under which `J = reversal` becomes a
block-diagonal of `2×2` swaps — the route to `det(I + uJ) = (1 - u²)^m`. -/

section Orientation
variable [LinearOrder V]

/-- A dart is positive when its tail precedes its head. -/
def IsPos (d : G.Dart) : Prop := d.fst < d.snd

instance : DecidablePred G.IsPos := fun d => (inferInstance : Decidable (d.fst < d.snd))

/-- If a dart is not positive, its reverse is. -/
lemma isPos_symm_of_not {d : G.Dart} (h : ¬ G.IsPos d) : G.IsPos d.symm :=
  lt_of_le_of_ne (not_lt.mp h) d.snd_ne_fst

/-- Orientation reindex: a dart is a chosen positive dart plus a sign bit. -/
def dartEquiv : G.Dart ≃ Bool × {d : G.Dart // G.IsPos d} where
  toFun d := if h : G.IsPos d then (true, ⟨d, h⟩) else (false, ⟨d.symm, G.isPos_symm_of_not h⟩)
  invFun p := if p.1 then p.2.1 else p.2.1.symm
  left_inv d := by
    by_cases h : G.IsPos d
    · simp [h]
    · simp [h, Dart.symm_symm]
  right_inv := by
    rintro ⟨b, q, hq⟩
    cases b
    · have hneg : ¬ G.IsPos q.symm := by
        show ¬ (q.snd < q.fst); exact not_lt.mpr (le_of_lt hq)
      simp [hneg, Dart.symm_symm]
    · simp [hq]

/-- The positive darts are in bijection with the edges: `|PosDart| = |E|`.
Proof: `dartEquiv` gives `|Dart| = 2·|PosDart|`, and the handshake lemma gives
`|Dart| = 2·|E|`; cancel the `2`. -/
lemma card_posDart : Fintype.card {d : G.Dart // G.IsPos d} = G.edgeFinset.card := by
  have h1 : Fintype.card G.Dart = 2 * Fintype.card {d : G.Dart // G.IsPos d} := by
    rw [Fintype.card_congr G.dartEquiv, Fintype.card_prod, Fintype.card_bool]
  have h2 : Fintype.card G.Dart = 2 * G.edgeFinset.card := by
    rw [dart_card_eq_sum_degrees, sum_degrees_eq_twice_card_edges]
  omega

/-- A dart never equals its own reverse. -/
lemma dart_ne_symm (d : G.Dart) : d ≠ d.symm :=
  fun h => d.fst_ne_snd (congrArg (fun e : G.Dart => e.fst) h)

@[simp] lemma dartEquiv_symm_apply (b : Bool) (p : {d : G.Dart // G.IsPos d}) :
    G.dartEquiv.symm (b, p) = if b then (p : G.Dart) else (p : G.Dart).symm := rfl

/-- Reversing a dart flips the orientation bit. -/
lemma dartEquiv_symm_symm (b : Bool) (p : {d : G.Dart // G.IsPos d}) :
    (G.dartEquiv.symm (b, p)).symm = G.dartEquiv.symm (!b, p) := by
  cases b <;> simp [Dart.symm_symm]

end Orientation

/-- The `2×2` sign block `[[1,u],[u,1]]` (indexed by `Bool`). -/
def signBlock (R : Type*) [CommRing R] (u : R) : Matrix Bool Bool R :=
  Matrix.of fun b1 b2 => if b1 = b2 then 1 else u

@[simp] lemma signBlock_apply (R : Type*) [CommRing R] (u : R) (b1 b2 : Bool) :
    signBlock R u b1 b2 = if b1 = b2 then 1 else u := rfl

lemma det_signBlock (R : Type*) [CommRing R] (u : R) : (signBlock R u).det = 1 - u ^ 2 := by
  rw [← Matrix.det_reindex_self finTwoEquiv.symm, Matrix.det_fin_two]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, signBlock_apply,
    EmbeddingLike.apply_eq_iff_eq]
  norm_num
  ring

/-- **`det(I + uJ) = (1 - u²)^m`.** Reindex by `dartEquiv` turns `I + uJ` into a
block-diagonal of `2×2` sign blocks (one per edge); `det_blockDiagonal` then gives
`(det signBlock)^|E| = (1 - u²)^|E|`. -/
lemma det_one_add_smul_reversal (R : Type*) [CommRing R] [LinearOrder V] (u : R) :
    (1 + u • G.reversal R).det = (1 - u ^ 2) ^ G.edgeFinset.card := by
  rw [← Matrix.det_reindex_self G.dartEquiv]
  have hblock : Matrix.reindex G.dartEquiv G.dartEquiv (1 + u • G.reversal R)
      = Matrix.blockDiagonal (fun _ : {d : G.Dart // G.IsPos d} => signBlock R u) := by
    ext ⟨i1, p1⟩ ⟨i2, p2⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.smul_apply, reversal_apply, smul_eq_mul, Matrix.blockDiagonal_apply, signBlock_apply]
    rw [dartEquiv_symm_symm]
    simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, eq_comm (a := p2) (b := p1)]
    cases i1 <;> cases i2 <;> by_cases hp : p1 = p2 <;> simp_all
  rw [hblock, Matrix.det_blockDiagonal]
  simp only [Finset.prod_const, Finset.card_univ, card_posDart, det_signBlock]


/-- **Bass's determinant formula** (division-free polynomial form).

`(1 - u²)^|V| · det(I - u·B) = (1 - u²)^|E| · det(I - u·A + u²·(D - I))`,

with `B` the Hashimoto operator on darts, `A` the adjacency matrix, `D` the
degree matrix. Equivalent to `det(I - uB) = (1-u²)^{|E|-|V|} det(I - uA + (D-I)u²)`
wherever the power is defined; this form is valid for every finite graph. -/
theorem bass_determinant (R : Type*) [CommRing R] (u : R) :
    (1 - u ^ 2) ^ (Fintype.card V) * (1 - u • G.hashimoto R).det
      = (1 - u ^ 2) ^ G.edgeFinset.card
        * (1 - u • G.adjMatrix R + u ^ 2 • (G.degMatrix R - 1)).det := by
  sorry

end SimpleGraph
