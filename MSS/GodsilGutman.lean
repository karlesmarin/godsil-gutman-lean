/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import MSS.ExpectedCharpoly
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# MSS C2 — proving the Godsil–Gutman identity (in progress)

Target: `expected_charpoly_eq_matchingPoly_target` (see `MSS/ExpectedCharpoly.lean`). This file BEGINS
the proof. It is honest WIP: the genuinely-proved building blocks below are sorry-free; the hard
combinatorial core (the permutation-expansion + expectation argument) is documented as the plan and is
NOT yet a theorem (no `sorry` is committed — we add lemmas only once they are actually proved).

## Proof plan (the spine)
1. `charpoly(A_cfg) = (charmatrix A_cfg).det = ∑_{σ : Perm V} sign(σ) ∏_i (charmatrix A_cfg)_{σ i, i}`
   (`Matrix.det_apply`).
2. Sum over `cfg`, swap the two finite sums: `∑_cfg ∑_σ = ∑_σ sign(σ) ∑_cfg ∏_i (…)`.
3. The inner `∑_cfg ∏_i (…)` factorizes over edges; each edge's ±1 sign averages to `0`
   (`sum_signOf_eq_zero` below). A term survives ⟺ every edge appears an even number of times ⟺ `σ`
   is an involution whose 2-cycles are edges of `G` ⟺ `σ` ↔ a `k`-edge matching, with `sign(σ)=(−1)^k`.
4. The surviving terms reassemble `∑_k (−1)^k m_k X^{n−2k} = matchingPoly G`.

## Proved here (sorry-free building blocks)
`signingMatrix_apply` (unfold), `signingMatrix_symm` (symmetry ⟹ the matrix is Hermitian, giving real
eigenvalues — needed downstream), `signingMatrix_diag` (zero diagonal), `sum_signOf_eq_zero`
(the ±1 expectation seed — step 3's engine).
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Unfolding lemma for the signing matrix. -/
theorem signingMatrix_apply (cfg : Sym2 V → Bool) (i j : V) :
    G.signingMatrix cfg i j = if G.Adj i j then (if cfg s(i, j) then (1 : ℝ) else -1) else 0 :=
  rfl

/-- The signing matrix is **symmetric** — both the support (`G.Adj`) and the sign (`Sym2` is
unordered) are symmetric. Hence `A_cfg` is Hermitian over `ℝ`, so it has real eigenvalues (the input
the spectral/Ramanujan side needs). -/
theorem signingMatrix_symm (cfg : Sym2 V → Bool) (i j : V) :
    G.signingMatrix cfg i j = G.signingMatrix cfg j i := by
  rw [signingMatrix_apply, signingMatrix_apply]
  by_cases h : G.Adj i j
  · rw [if_pos h, if_pos h.symm, Sym2.eq_swap]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

/-- The diagonal of the signing matrix is zero (no self-loops). -/
theorem signingMatrix_diag (cfg : Sym2 V → Bool) (i : V) :
    G.signingMatrix cfg i i = 0 :=
  G.signedAdjMatrix_diag _ i

/-- **The expectation seed.** A single ±1 edge-sign averages to `0`: `∑_{b} (±1) = 0`. This is the
engine of step 3 — it is why every term whose product contains an odd power of some edge-sign dies. -/
theorem sum_signOf_eq_zero :
    (∑ b : Bool, (if b then (1 : ℝ) else -1)) = 0 := by
  rw [Fintype.sum_bool]; norm_num

/-! ## Steps 1–2: expand `charpoly` over permutations and read off the entries -/

/-- **Step 2 (fixed point).** On the diagonal the char-matrix entry of the signing matrix is just `X`
(the signing matrix has zero diagonal). So a fixed point of `σ` contributes a factor `X`. -/
theorem charmatrix_signingMatrix_diag (cfg : Sym2 V → Bool) (i : V) :
    (G.signingMatrix cfg).charmatrix i i = Polynomial.X := by
  rw [Matrix.charmatrix_apply_eq, G.signingMatrix_diag cfg i, Polynomial.C_0, sub_zero]

/-- **Step 2 (off-diagonal).** Off the diagonal the char-matrix entry is `−C` of the signed adjacency
entry. So a point in `σ.support` contributes `−C (A_cfg)_{σ i, i}`. -/
theorem charmatrix_signingMatrix_offdiag (cfg : Sym2 V → Bool) {i j : V} (h : i ≠ j) :
    (G.signingMatrix cfg).charmatrix i j = - Polynomial.C (G.signingMatrix cfg i j) := by
  rw [Matrix.charmatrix_apply_ne _ _ _ h]

/-- **Step 1.** The characteristic polynomial of the signing matrix, expanded over permutations via
`Matrix.det_apply` (`charpoly = (charmatrix).det`). The summand factorizes (step 2) into
`X^{#fixed} · ∏_{support} (−C …)`. -/
theorem charpoly_signingMatrix_eq_sum (cfg : Sym2 V → Bool) :
    (G.signingMatrix cfg).charpoly
      = ∑ σ : Equiv.Perm V,
          ((Equiv.Perm.sign σ : ℤ) : Polynomial ℝ) * ∏ i, (G.signingMatrix cfg).charmatrix (σ i) i := by
  show (G.signingMatrix cfg).charmatrix.det = _
  rw [Matrix.det_apply']

/-! ## Step 3: split each permutation's product into `X^{#fixed} · ∏_{support}(−C …)` -/

/-- **Step 2/3 (per factor).** Each factor of the permutation product is `X` on a fixed point and
`−C (A_cfg)_{σ i, i}` on the support. -/
theorem charmatrix_signingMatrix_factor (cfg : Sym2 V → Bool) (σ : Equiv.Perm V) (i : V) :
    (G.signingMatrix cfg).charmatrix (σ i) i
      = if σ i = i then Polynomial.X else - Polynomial.C (G.signingMatrix cfg (σ i) i) := by
  by_cases h : σ i = i
  · rw [if_pos h, h, charmatrix_signingMatrix_diag]
  · rw [if_neg h, charmatrix_signingMatrix_offdiag G cfg h]

/-- **Step 3 (product split).** The permutation product factorizes into `X` over the fixed points
times `−C(A_cfg)_{σ i, i}` over the support: `∏_i = X^{#fixed} · ∏_{i ∈ supp σ} (−C …)`. -/
theorem prod_charmatrix_split (cfg : Sym2 V → Bool) (σ : Equiv.Perm V) :
    (∏ i, (G.signingMatrix cfg).charmatrix (σ i) i)
      = Polynomial.X ^ (Finset.univ.filter (fun i => σ i = i)).card
        * ∏ i ∈ σ.support, (- Polynomial.C (G.signingMatrix cfg (σ i) i)) := by
  have key : (∏ i, (G.signingMatrix cfg).charmatrix (σ i) i)
      = ∏ i, (if σ i = i then Polynomial.X
                else - Polynomial.C (G.signingMatrix cfg (σ i) i)) :=
    Finset.prod_congr rfl (fun i _ => charmatrix_signingMatrix_factor G cfg σ i)
  have hsupp : (Finset.univ.filter (fun i => ¬ σ i = i)) = σ.support := by
    ext i; simp [Equiv.Perm.mem_support]
  rw [key, Finset.prod_ite, Finset.prod_const, hsupp]

/-! ## Step 4 (first cut): only permutations whose support pairs are all edges survive -/

/-- **Step 4 (non-edge kills it).** If some support pair `(σ i, i)` is NOT an edge of `G`, the support
product is `0`. So in `∑_σ`, only permutations whose every support pair `(σ j, j)` is a `G`-edge can
contribute — the first restriction toward "only edge-involutions (matchings) survive". -/
theorem prod_support_eq_zero_of_not_adj (cfg : Sym2 V → Bool) (σ : Equiv.Perm V) {i : V}
    (hi : i ∈ σ.support) (hni : ¬ G.Adj (σ i) i) :
    (∏ j ∈ σ.support, (- Polynomial.C (G.signingMatrix cfg (σ j) j))) = 0 := by
  refine Finset.prod_eq_zero hi ?_
  rw [signingMatrix_apply, if_neg hni, Polynomial.C_0, neg_zero]

/-! ## Step 5 (sign): an involution with `k` transpositions has sign `(−1)^k` -/

/-- **Step 5 (the sign).** For an involution `σ` (`σ² = 1`), `sign σ = (−1)^{#support / 2}`. Since an
edge-involution with `k` 2-cycles has `#support = 2k`, this is the `(−1)^k` weight that matches the
matching polynomial's sign — obtained WITHOUT any `cycleType` multiset bookkeeping
(`sign_of_pow_two_eq_one` + `card_fixedPoints`). -/
theorem sign_involution (σ : Equiv.Perm V) (hσ : σ ^ 2 = 1) :
    Equiv.Perm.sign σ = (-1) ^ (σ.support.card / 2) := by
  rw [Equiv.Perm.sign_of_pow_two_eq_one hσ]
  congr 1
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType]
  have := Finset.card_le_univ σ.support
  omega

/-! ## Assembly: swap the sums and isolate the inner config-sum `S(σ)` -/

/-- **Assembly step.** Combining the permutation expansion (step 1) with the product split (step 3) and
swapping `∑_cfg`/`∑_σ`, the summed characteristic polynomial is a sum over permutations of
`sign σ • (X^{#fixed} · S(σ))`, where `S(σ) = ∑_cfg ∏_{support} (−C …)` is the inner config-sum to be
analyzed next (it vanishes unless `σ` is an edge-involution). -/
theorem sum_charpoly_eq :
    (∑ cfg : Sym2 V → Bool, (G.signingMatrix cfg).charpoly)
      = ∑ σ : Equiv.Perm V, ((Equiv.Perm.sign σ : ℤ) : Polynomial ℝ) *
          (Polynomial.X ^ (Finset.univ.filter (fun i => σ i = i)).card
            * ∑ cfg : Sym2 V → Bool,
                ∏ i ∈ σ.support, (- Polynomial.C (G.signingMatrix cfg (σ i) i))) := by
  simp only [charpoly_signingMatrix_eq_sum, prod_charmatrix_split]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [Finset.mul_sum]

/-! ## Analysis of `S(σ)`: vanishes unless every support pair is an edge -/

/-- **`S(σ)` analysis, first cut.** If `σ` moves some vertex `i` to a non-neighbour (`(σ i, i)` not an
edge), then the inner config-sum `S(σ)` is `0`: every single configuration's support product already
vanishes (`prod_support_eq_zero_of_not_adj`), so the sum over configurations is `0`. Concept: a signed
walk that steps along a non-edge carries weight `0`, regardless of the signing. -/
theorem innerSum_eq_zero_of_not_adj (σ : Equiv.Perm V) {i : V}
    (hi : i ∈ σ.support) (hni : ¬ G.Adj (σ i) i) :
    (∑ cfg : Sym2 V → Bool,
        ∏ j ∈ σ.support, (- Polynomial.C (G.signingMatrix cfg (σ j) j))) = 0 :=
  Finset.sum_eq_zero (fun cfg _ => prod_support_eq_zero_of_not_adj G cfg σ hi hni)

/-- **`S(σ)` reduces to a real-valued sum.** Since `C` (the constant-polynomial embedding `ℝ →+* ℝ[X]`)
is a ring hom, the whole `ℝ[X]`-valued inner sum `S(σ)` is `C` of a purely **real** quantity
`T'(σ) = ∑_cfg ∏_{support} (−A_cfg)_{σi,i}`. This is the key reduction: the hard combinatorics (edge
factorization, odd-multiplicity-vanishes) now happens in `ℝ`, where `Finset.prod_univ_sum` applies
cleanly — no `ℝ[X]` machinery in the way. Concept: the polynomial structure was inert; the content is
the real expectation of signed-edge-weight products. -/
theorem innerSum_eq_C (σ : Equiv.Perm V) :
    (∑ cfg : Sym2 V → Bool, ∏ i ∈ σ.support, (- Polynomial.C (G.signingMatrix cfg (σ i) i)))
      = Polynomial.C (∑ cfg : Sym2 V → Bool,
          ∏ i ∈ σ.support, (- G.signingMatrix cfg (σ i) i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun cfg _ => ?_)
  rw [map_prod]
  exact Finset.prod_congr rfl (fun i _ => (map_neg Polynomial.C _).symm)

/-! ## Engine of the edge factorization: the per-edge ±1 power-sum (odd ↦ 0, even ↦ 2)

When `T'(σ)` is factorized over edges via `Finset.prod_univ_sum`, each edge `e` contributes the Bool-sum
`∑_{b} (signOf b)^{mult(e)}`, where `mult(e)` is how many support vertices map to `e`. These two lemmas
give its value: **0 if the edge's multiplicity is odd, 2 if even**. An odd multiplicity anywhere zeroes
the whole product — this is precisely "every edge must be used an even number of times ⟺ `σ² = 1`". -/

/-- Odd multiplicity ⟹ the per-edge ±1 power-sum vanishes (`1^k + (−1)^k = 0` for odd `k`). The general
form of `sum_signOf_eq_zero` (the `k = 1` case). -/
theorem sum_signOf_pow_eq_zero_of_odd {k : ℕ} (hk : Odd k) :
    (∑ b : Bool, (if b then (1 : ℝ) else -1) ^ k) = 0 := by
  rw [Fintype.sum_bool]; simp [hk.neg_one_pow]

/-- Even multiplicity ⟹ the per-edge ±1 power-sum is `2` (`1^k + (−1)^k = 2` for even `k`). The
surviving edges each contribute a factor `2`, giving the overall `2^{#edges}` normalization. -/
theorem sum_signOf_pow_eq_two_of_even {k : ℕ} (hk : Even k) :
    (∑ b : Bool, (if b then (1 : ℝ) else -1) ^ k) = 2 := by
  rw [Fintype.sum_bool]; norm_num [hk.neg_one_pow]

/-! ## Fiberwise edge-factorization of the inner config-sum `T'(σ)`

The structural heart of step 3. Group the support product by the edge `s(σ i, i)` that each support
vertex sits on (`Finset.prod_fiberwise`), then push `∑_cfg` through `∏_e` (`Fintype.prod_sum`): the
inner real config-sum `T'(σ)` becomes a product over **edges** of a per-edge `Bool`-sum. This is what
lets the "odd-multiplicity edge ⟹ 0" engine (`sum_signOf_pow_eq_zero_of_odd`) act edge by edge — each
factor is a `∑_b` over a fiber whose size is exactly that edge's multiplicity. -/
theorem innerSum_factor_edges (σ : Equiv.Perm V) :
    (∑ cfg : Sym2 V → Bool, ∏ i ∈ σ.support, (- G.signingMatrix cfg (σ i) i))
      = ∏ e : Sym2 V, ∑ b : Bool,
          ∏ i ∈ σ.support with s(σ i, i) = e,
            (- (if G.Adj (σ i) i then (if b then (1 : ℝ) else -1) else 0)) := by
  rw [Fintype.prod_sum (fun (e : Sym2 V) (b : Bool) =>
        ∏ i ∈ σ.support with s(σ i, i) = e,
          (- (if G.Adj (σ i) i then (if b then (1 : ℝ) else -1) else 0)))]
  refine Finset.sum_congr rfl (fun cfg _ => ?_)
  rw [← Finset.prod_fiberwise σ.support (fun i => s(σ i, i))
        (fun i => - G.signingMatrix cfg (σ i) i)]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Finset.mem_filter] at hi
  rw [G.signingMatrix_apply cfg (σ i) i, hi.2]

/-! ## Per-edge collapse: each surviving edge contributes `∑_b (−signOf b)^{mult}` -/

/-- The `−signOf` power-sum, **odd** case — the engine lemma in the *sign that actually appears* in
`innerSum_factor_edges`. Same value as `sum_signOf_pow_eq_zero_of_odd`: the extra negation is absorbed
by `b ↦ ¬b` (`−(if true … )=−1`, `−(if false …)=1`). -/
theorem sum_negSignOf_pow_eq_zero_of_odd {m : ℕ} (hm : Odd m) :
    (∑ b : Bool, (- (if b then (1 : ℝ) else -1)) ^ m) = 0 := by
  rw [Fintype.sum_bool]; simp [hm.neg_one_pow]

/-- The `−signOf` power-sum, **even** case: value `2`. -/
theorem sum_negSignOf_pow_eq_two_of_even {m : ℕ} (hm : Even m) :
    (∑ b : Bool, (- (if b then (1 : ℝ) else -1)) ^ m) = 2 := by
  rw [Fintype.sum_bool]; norm_num [hm.neg_one_pow]

/-- **Fiber collapse.** On an edge `e` all of whose support-fiber pairs `(σ i, i)` are genuine
`G`-edges, the inner fiber product collapses to a single power: every factor equals `−signOf b`, so the
product is `(−signOf b)^{mult}`, where `mult` is the fiber cardinality — exactly the multiplicity of
`e` in `σ`'s support walk. Feeding this into `sum_negSignOf_pow_eq_*` is what makes an odd-multiplicity
edge zero the whole term. -/
theorem fiber_prod_eq_pow (σ : Equiv.Perm V) (e : Sym2 V) (b : Bool)
    (he : ∀ i ∈ σ.support.filter (fun i => s(σ i, i) = e), G.Adj (σ i) i) :
    (∏ i ∈ σ.support with s(σ i, i) = e,
        (- (if G.Adj (σ i) i then (if b then (1 : ℝ) else -1) else 0)))
      = (- (if b then (1 : ℝ) else -1)) ^ (σ.support.filter (fun i => s(σ i, i) = e)).card := by
  have h : (∏ i ∈ σ.support with s(σ i, i) = e,
        (- (if G.Adj (σ i) i then (if b then (1 : ℝ) else -1) else 0)))
      = ∏ i ∈ σ.support with s(σ i, i) = e, (- (if b then (1 : ℝ) else -1)) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [if_pos (he i hi)]
  rw [h, Finset.prod_const]

/-! ## The hard characterization: an odd edge-multiplicity exists ⟺ `σ` is not an involution

`mult_σ(s(a,b)) = [σ a = b] + [σ b = a] ∈ {0,1,2}`. It is **odd** (`=1`) exactly when `σ` sends `a ↦ b`
but not `b ↦ a`, i.e. `a` lies on a cycle of length `≥ 3`. Hence *some* pair has odd multiplicity ⟺
`σ² ≠ 1`. This lemma is the permutation-theoretic crux of the `⟹` direction: it produces the witnessing
ordered edge `a ↦ b ↦ (≠a)`. -/
theorem exists_of_sq_ne_one (σ : Equiv.Perm V) (hσ : σ ^ 2 ≠ 1) :
    ∃ a b, a ≠ b ∧ σ a = b ∧ σ b ≠ a := by
  have hx : ∃ x, σ (σ x) ≠ x := by
    by_contra h
    push_neg at h
    refine hσ (Equiv.ext fun x => ?_)
    rw [pow_two, Equiv.Perm.mul_apply, h x, Equiv.Perm.one_apply]
  obtain ⟨x, hx⟩ := hx
  exact ⟨x, σ x, fun h => hx (by simp [← h]), rfl, hx⟩

/-- **The witness edge carries multiplicity 1.** For the ordered edge `a ↦ b` with `σ b ≠ a` (the
output of `exists_of_sq_ne_one`), the support-fiber over the unordered pair `s(a, b)` is exactly
`{a}`: only `a` satisfies `s(σ i, i) = s(a, b)` (since `b` would need `σ b = a`). So this edge's
multiplicity is `1` — odd — which is what makes its per-edge `Bool`-sum vanish. -/
theorem fiber_witness (σ : Equiv.Perm V) {a b : V} (hab : a ≠ b)
    (ha : σ a = b) (hb : σ b ≠ a) :
    σ.support.filter (fun i => s(σ i, i) = s(a, b)) = {a} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_filter, Equiv.Perm.mem_support]
    refine ⟨?_, ?_⟩
    · rw [ha]; exact fun h => hab h.symm
    · rw [ha]; exact Sym2.eq_swap
  · intro i hi
    rw [Finset.mem_filter, Equiv.Perm.mem_support, Sym2.eq_iff] at hi
    obtain ⟨_, ⟨h1, h2⟩ | ⟨_, h2⟩⟩ := hi
    · exact absurd (h2 ▸ h1) hb
    · exact h2

/-- **The hard direction's payoff: non-involutions contribute `0`.** If `σ² ≠ 1`, the inner config-sum
`T'(σ)` vanishes. Proof: the witness edge `s(a, c)` (with `σ a = c`, `σ c ≠ a`) has fiber `{a}`
(`fiber_witness`), so its per-edge factor is the single Bool-sum `∑_b −(if Adj then signOf b else 0)`,
which is `0` (an odd, =1, multiplicity); one zero factor zeroes the whole edge-product
(`innerSum_factor_edges`). This is precisely why only involutions (matchings) survive in `∑_σ`. -/
theorem innerSum_factor_zero_of_sq_ne_one (σ : Equiv.Perm V) (hσ : σ ^ 2 ≠ 1) :
    (∑ cfg : Sym2 V → Bool, ∏ i ∈ σ.support, (- G.signingMatrix cfg (σ i) i)) = 0 := by
  rw [innerSum_factor_edges]
  obtain ⟨a, c, hac, ha, hc⟩ := exists_of_sq_ne_one σ hσ
  refine Finset.prod_eq_zero (Finset.mem_univ s(a, c)) ?_
  rw [fiber_witness σ hac ha hc]
  simp only [Finset.prod_singleton, ha]
  rw [Fintype.sum_bool]
  by_cases hadj : G.Adj c a <;> simp [hadj]

/-! ## The surviving value: edge-involutions give product `1` for every signing -/

/-- **Edge-involutions give product `1` for every signing.** If `σ² = 1` and every support pair is a
`G`-edge, then for *every* configuration `cfg` the support product is `1`. Pair each support vertex
`a` with `σ a` (an involution on the support, `Finset.prod_involution`): the two factors of a 2-cycle
are the *same* `±1` (by symmetry of the signing matrix), so their product is `(±1)² = 1`. Hence
`T'(σ) = ∑_cfg 1 = #configs` for an edge-involution — the value that, weighted by `sign = (−1)^k` and
`X^{n−2k}`, reassembles the matching polynomial. -/
theorem prod_eq_one_of_involution (cfg : Sym2 V → Bool) (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hedge : ∀ i ∈ σ.support, G.Adj (σ i) i) :
    (∏ i ∈ σ.support, (- G.signingMatrix cfg (σ i) i)) = 1 := by
  refine Finset.prod_involution (fun a _ => σ a) ?_
    (fun a ha _ => Equiv.Perm.mem_support.mp ha)
    (fun a ha => Equiv.Perm.apply_mem_support.mpr ha) ?_
  · intro a ha
    show (- G.signingMatrix cfg (σ a) a) * (- G.signingMatrix cfg (σ (σ a)) (σ a)) = 1
    have h2 : σ (σ a) = a := by
      rw [← Equiv.Perm.mul_apply, ← pow_two, hσ, Equiv.Perm.one_apply]
    rw [h2, G.signingMatrix_symm cfg a (σ a), G.signingMatrix_apply cfg (σ a) a,
      if_pos (hedge a ha)]
    obtain h | h := Bool.eq_false_or_eq_true (cfg s(σ a, a)) <;> rw [h] <;> norm_num
  · intro a ha
    show σ (σ a) = a
    rw [← Equiv.Perm.mul_apply, ← pow_two, hσ, Equiv.Perm.one_apply]

/-- **The surviving value.** For an edge-involution (`σ² = 1`, every support pair a `G`-edge) the inner
config-sum `T'(σ)` equals `#configs`: the integrand is `1` for every signing (`prod_eq_one_of_involution`),
so the sum is just the number of configurations. This is the constant that, summed against
`sign(σ)·X^{#fix(σ)}` over the matchings, yields `#configs • matchingPoly`. -/
theorem innerSum_eq_card_of_involution (σ : Equiv.Perm V)
    (hσ : σ ^ 2 = 1) (hedge : ∀ i ∈ σ.support, G.Adj (σ i) i) :
    (∑ cfg : Sym2 V → Bool, ∏ i ∈ σ.support, (- G.signingMatrix cfg (σ i) i))
      = (Fintype.card (Sym2 V → Bool) : ℝ) := by
  rw [Finset.sum_congr rfl (fun cfg _ => G.prod_eq_one_of_involution cfg σ hσ hedge),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-! ## Assembly: the per-permutation trichotomy and the edge-involution predicate -/

/-- **Non-edge support ⟹ `T'(σ) = 0`** (real level). If some support pair `(σ i, i)` is not a `G`-edge,
every configuration's support product already contains a `0` factor, so `T'(σ) = 0`. Completes the
trichotomy with `innerSum_factor_zero_of_sq_ne_one` (non-involution) and
`innerSum_eq_card_of_involution` (edge-involution): only **edge-involutions** survive. -/
theorem innerSum_zero_of_not_adj (σ : Equiv.Perm V) {i : V}
    (hi : i ∈ σ.support) (hni : ¬ G.Adj (σ i) i) :
    (∑ cfg : Sym2 V → Bool, ∏ j ∈ σ.support, (- G.signingMatrix cfg (σ j) j)) = 0 := by
  refine Finset.sum_eq_zero (fun cfg _ => Finset.prod_eq_zero hi ?_)
  rw [G.signingMatrix_apply cfg (σ i) i, if_neg hni, neg_zero]

/-- **`σ` is an edge-involution**: an involution (`σ² = 1`) all of whose 2-cycles are `G`-edges. These
are exactly the permutations that survive `∑_cfg charpoly`, and they biject with the matchings of `G`
(a `k`-transposition edge-involution ↔ a `k`-edge matching). -/
def IsEdgeInvolution (σ : Equiv.Perm V) : Prop :=
  σ ^ 2 = 1 ∧ ∀ i ∈ σ.support, G.Adj (σ i) i

instance (σ : Equiv.Perm V) : Decidable (G.IsEdgeInvolution σ) := by
  unfold IsEdgeInvolution; infer_instance

/-- **The trichotomy, collapsed.** `T'(σ)` is `#configs` on edge-involutions and `0` on everything
else. This is the per-permutation input to the final assembly: `∑_cfg charpoly = ∑_σ sign·X^{#fix}·C(T'(σ))`
then collapses to a sum over edge-involutions only. -/
theorem innerSum_eq_ite (σ : Equiv.Perm V) :
    (∑ cfg : Sym2 V → Bool, ∏ i ∈ σ.support, (- G.signingMatrix cfg (σ i) i))
      = if G.IsEdgeInvolution σ then (Fintype.card (Sym2 V → Bool) : ℝ) else 0 := by
  by_cases h : G.IsEdgeInvolution σ
  · rw [if_pos h, G.innerSum_eq_card_of_involution σ h.1 h.2]
  · rw [if_neg h]
    simp only [IsEdgeInvolution, not_and_or] at h
    rcases h with h1 | h2
    · exact G.innerSum_factor_zero_of_sq_ne_one σ h1
    · push_neg at h2
      obtain ⟨i, hi, hni⟩ := h2
      exact G.innerSum_zero_of_not_adj σ hi hni

/-! ## The bijection, inverse map: a matching `M` induces an involution `σ_M`

The hard half of the matching ↔ edge-involution bijection. Given a matching `M` (pairwise
vertex-disjoint edges), the map `partner M` sends each matched vertex to the other endpoint of its
(unique) edge and fixes everything else; it is an involution, hence a permutation `permOfMatching`. -/

/-- `Sym2.Mem.other'` depends only on the element and the edge, not on the membership proof: equal
edges give equal partners. -/
theorem other'_congr {v : V} {z z' : Sym2 V} (p : v ∈ z) (q : v ∈ z') (hzz : z = z') :
    Sym2.Mem.other' p = Sym2.Mem.other' q := by subst hzz; rfl

/-- In a matching, the edge containing a given vertex is unique. -/
theorem matching_unique_edge {M : Finset (Sym2 V)} (hM : IsMatchingSet M) {v : V}
    {e f : Sym2 V} (he : e ∈ M) (hf : f ∈ M) (hve : v ∈ e) (hvf : v ∈ f) : e = f := by
  by_contra hne
  exact hM e he f hf hne v hve hvf

/-- The partner of `v` under matching `M`: the other endpoint of `v`'s edge if matched, else `v`. -/
noncomputable def partner (M : Finset (Sym2 V)) (v : V) : V :=
  if h : ∃ e ∈ M, v ∈ e then Sym2.Mem.other' h.choose_spec.2 else v

/-- Value of `partner` at a matched vertex: the other endpoint of its edge (well-defined by
uniqueness of the matching edge). -/
theorem partner_matched {M : Finset (Sym2 V)} (hM : IsMatchingSet M) {v : V} {e : Sym2 V}
    (heM : e ∈ M) (hve : v ∈ e) : partner M v = Sym2.Mem.other' hve := by
  have h : ∃ f ∈ M, v ∈ f := ⟨e, heM, hve⟩
  rw [partner, dif_pos h]
  exact other'_congr h.choose_spec.2 hve
    (matching_unique_edge hM h.choose_spec.1 heM h.choose_spec.2 hve)

theorem partner_unmatched {M : Finset (Sym2 V)} {v : V} (h : ¬ ∃ e ∈ M, v ∈ e) :
    partner M v = v := by rw [partner, dif_neg h]

/-- `partner M` is an involution: matched vertices swap within their edge (`Sym2.other_invol'`),
unmatched vertices are fixed. -/
theorem partner_involutive {M : Finset (Sym2 V)} (hM : IsMatchingSet M) :
    Function.Involutive (partner M) := by
  intro v
  by_cases h : ∃ e ∈ M, v ∈ e
  · obtain ⟨e, heM, hve⟩ := h
    rw [partner_matched hM heM hve]
    have hwe : Sym2.Mem.other' hve ∈ e := Sym2.other_mem' hve
    rw [partner_matched hM heM hwe]
    exact Sym2.other_invol' hve hwe
  · rw [partner_unmatched h, partner_unmatched h]

/-- The involution permutation induced by a matching. -/
noncomputable def permOfMatching {M : Finset (Sym2 V)} (hM : IsMatchingSet M) : Equiv.Perm V :=
  (partner_involutive hM).toPerm

@[simp] theorem permOfMatching_apply {M : Finset (Sym2 V)} (hM : IsMatchingSet M) (v : V) :
    permOfMatching hM v = partner M v := rfl

/-- `permOfMatching` is an involution. -/
theorem permOfMatching_sq {M : Finset (Sym2 V)} (hM : IsMatchingSet M) :
    permOfMatching hM ^ 2 = 1 := by
  ext v
  rw [Equiv.Perm.one_apply, pow_two, Equiv.Perm.mul_apply]
  simp only [permOfMatching_apply]
  exact partner_involutive hM v

/-- When a matching's edges are edges of `G`, the induced involution is an **edge-involution**: every
moved vertex is sent along a `G`-edge (the matching edge it lies on). -/
theorem permOfMatching_isEdgeInvolution {M : Finset (Sym2 V)} (hM : IsMatchingSet M)
    (hMG : M ⊆ G.edgeFinset) : G.IsEdgeInvolution (permOfMatching hM) := by
  refine ⟨permOfMatching_sq hM, fun v hv => ?_⟩
  rw [Equiv.Perm.mem_support, permOfMatching_apply] at hv
  by_cases h : ∃ e ∈ M, v ∈ e
  · obtain ⟨e, heM, hve⟩ := h
    rw [permOfMatching_apply, partner_matched hM heM hve]
    have hee : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp (hMG heM)
    rw [← Sym2.other_spec' hve, SimpleGraph.mem_edgeSet] at hee
    exact hee.symm
  · exact absurd (partner_unmatched h) hv

/-! ## The bijection, forward map: an edge-involution `σ` induces a matching `M(σ)` -/

/-- For an involution, a 2-cycle's edge is determined by **any** of its vertices: if `v` lies on the
edge `s(a, σ a)`, then that edge is `s(v, σ v)`. (Either `v = a`, or `v = σ a` and then `σ v = a`.) -/
theorem edge_eq_of_mem {σ : Equiv.Perm V} (hσ : σ ^ 2 = 1) {a v : V}
    (hv : v ∈ s(a, σ a)) : s(a, σ a) = s(v, σ v) := by
  rw [Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · rfl
  · have h2 : σ (σ a) = a := by
      rw [← Equiv.Perm.mul_apply, ← pow_two, hσ, Equiv.Perm.one_apply]
    rw [h2, Sym2.eq_swap]

/-- The matching induced by an edge-involution: the set of its 2-cycle edges `{s(a, σ a) : a ∈ supp}`. -/
noncomputable def matchingOfPerm (σ : Equiv.Perm V) : Finset (Sym2 V) :=
  σ.support.image (fun a => s(a, σ a))

/-- `M(σ)`'s edges are edges of `G` (each 2-cycle pair is a `G`-edge). -/
theorem matchingOfPerm_subset {σ : Equiv.Perm V} (h : G.IsEdgeInvolution σ) :
    matchingOfPerm σ ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact (h.2 a ha).symm

/-- `M(σ)` is a matching: its edges are pairwise vertex-disjoint, because for an involution any vertex
determines its 2-cycle edge (`edge_eq_of_mem`). -/
theorem matchingOfPerm_isMatching {σ : Equiv.Perm V} (h : G.IsEdgeInvolution σ) :
    IsMatchingSet (matchingOfPerm σ) := by
  intro e he f hf hef v hve hvf
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
  exact hef ((edge_eq_of_mem h.1 hve).trans (edge_eq_of_mem h.1 hvf).symm)

/-! ## The bijection is mutually inverse -/

/-- **Left inverse:** recovering the edge-involution from its matching gives `σ` back. For each `v`:
if `v` is moved, its `M(σ)`-edge is `s(v, σ v)` so its partner is `σ v`; if `v` is fixed, it is
unmatched, so its partner is `v = σ v`. -/
theorem permOfMatching_matchingOfPerm {σ : Equiv.Perm V} (h : G.IsEdgeInvolution σ) :
    permOfMatching (G.matchingOfPerm_isMatching h) = σ := by
  ext v
  rw [permOfMatching_apply]
  by_cases hv : v ∈ σ.support
  · have hve : v ∈ s(v, σ v) := by rw [Sym2.mem_iff]; exact Or.inl rfl
    have heM : s(v, σ v) ∈ matchingOfPerm σ := Finset.mem_image.mpr ⟨v, hv, rfl⟩
    rw [partner_matched (G.matchingOfPerm_isMatching h) heM hve]
    exact Sym2.congr_right.mp (Sym2.other_spec' hve)
  · have hnm : ¬ ∃ e ∈ matchingOfPerm σ, v ∈ e := by
      rintro ⟨e, he, hve⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      rw [Sym2.mem_iff] at hve
      rcases hve with rfl | rfl
      · exact hv ha
      · exact hv (Equiv.Perm.apply_mem_support.mpr ha)
    have hfix : σ v = v := by
      by_contra hc; exact hv (Equiv.Perm.mem_support.mpr hc)
    rw [partner_unmatched hnm, hfix]

/-- `other'` of a vertex on a non-diagonal edge differs from that vertex. -/
theorem other'_ne {a : V} {z : Sym2 V} (hd : ¬ z.IsDiag) (h : a ∈ z) :
    Sym2.Mem.other' h ≠ a := by rw [← Sym2.other_eq_other']; exact Sym2.other_ne hd h

/-- **Right inverse:** the matching of the involution of a matching `M` (with `M ⊆ G.edgeFinset`) is
`M`. `⊆`: each 2-cycle edge `s(a, partner a)` reconstructs the matching edge through `a`. `⊇`: each
`e ∈ M` is a `G`-edge (non-diagonal), so any vertex `a ∈ e` is moved (its partner is the other,
distinct, endpoint), and `s(a, partner a) = e`. -/
theorem matchingOfPerm_permOfMatching {M : Finset (Sym2 V)} (hM : IsMatchingSet M)
    (hMG : M ⊆ G.edgeFinset) : matchingOfPerm (permOfMatching hM) = M := by
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    rw [Equiv.Perm.mem_support, permOfMatching_apply] at ha
    have hmatched : ∃ f ∈ M, a ∈ f := by
      by_contra hc; exact ha (partner_unmatched hc)
    obtain ⟨f, hfM, haf⟩ := hmatched
    rw [permOfMatching_apply, partner_matched hM hfM haf, Sym2.other_spec' haf]
    exact hfM
  · intro e he
    obtain ⟨a, ha⟩ : ∃ a, a ∈ e := Sym2.inductionOn e fun x y => ⟨x, Sym2.mem_mk_left x y⟩
    have hnd : ¬ e.IsDiag :=
      G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hMG he))
    have hpartner : partner M a = Sym2.Mem.other' ha := partner_matched hM he ha
    have hasupp : a ∈ (permOfMatching hM).support := by
      rw [Equiv.Perm.mem_support, permOfMatching_apply, hpartner]
      exact other'_ne hnd ha
    refine Finset.mem_image.mpr ⟨a, hasupp, ?_⟩
    show s(a, permOfMatching hM a) = e
    rw [permOfMatching_apply, hpartner]
    exact Sym2.other_spec' ha

/-! ## Card relation: `support.card = 2 · |matching|` -/

/-- Each edge of `M(σ)` has exactly **two** support preimages under `a ↦ s(a, σ a)`: the two
endpoints `{b, σ b}` of its 2-cycle. -/
theorem fiber_card_two {σ : Equiv.Perm V} (h : G.IsEdgeInvolution σ) {e : Sym2 V}
    (he : e ∈ σ.support.image (fun a => s(a, σ a))) :
    (σ.support.filter (fun a => s(a, σ a) = e)).card = 2 := by
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
  have hne : σ b ≠ b := Equiv.Perm.mem_support.mp hb
  have h2 : σ (σ b) = b := by
    rw [← Equiv.Perm.mul_apply, ← pow_two, h.1, Equiv.Perm.one_apply]
  have hset : σ.support.filter (fun a => s(a, σ a) = s(b, σ b)) = {b, σ b} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, heq⟩
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨hb, rfl⟩
      · exact ⟨Equiv.Perm.apply_mem_support.mpr hb, by rw [h2, Sym2.eq_swap]⟩
  rw [hset, Finset.card_pair hne.symm]

/-- **The 2-to-1 count.** For an edge-involution, the support has twice as many vertices as `M(σ)`
has edges: `supp.card = 2 · |M(σ)|`. (Each matching edge is covered by its two endpoints.) -/
theorem support_card_eq {σ : Equiv.Perm V} (h : G.IsEdgeInvolution σ) :
    σ.support.card = 2 * (matchingOfPerm σ).card := by
  show σ.support.card = 2 * (σ.support.image (fun a => s(a, σ a))).card
  rw [Finset.card_eq_sum_card_image (fun a => s(a, σ a)) σ.support,
    Finset.sum_congr rfl (fun e he => G.fiber_card_two h he), Finset.sum_const, smul_eq_mul,
    mul_comm]

/-! ## Final assembly -/

/-- **Step 1: collapse to a sum over edge-involutions.** Combining the permutation expansion
(`sum_charpoly_eq`), the `C`-reduction (`innerSum_eq_C`) and the trichotomy (`innerSum_eq_ite`),
`∑_cfg charpoly` becomes a sum over the **edge-involutions** only, each contributing
`sign(σ)·X^{#fix}·C(#configs)`. -/
theorem charpoly_sum_eq_filter :
    (∑ cfg : Sym2 V → Bool, (G.signingMatrix cfg).charpoly)
      = ∑ σ ∈ Finset.univ.filter G.IsEdgeInvolution,
          ((Equiv.Perm.sign σ : ℤ) : Polynomial ℝ)
            * Polynomial.X ^ (Finset.univ.filter (fun i => σ i = i)).card
            * Polynomial.C (Fintype.card (Sym2 V → Bool) : ℝ) := by
  rw [sum_charpoly_eq, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [innerSum_eq_C, G.innerSum_eq_ite σ]
  by_cases hP : G.IsEdgeInvolution σ
  · rw [if_pos hP, if_pos hP, mul_assoc]
  · rw [if_neg hP, if_neg hP, Polynomial.C_0, mul_zero, mul_zero]

/-- Casting `(-1 : ℤˣ)^k` through `ℤ` into `ℝ[X]` gives `(-1)^k` (the `Units.val_pow` rewrite is a
no-op `rfl`, so we go by induction on the exponent). -/
theorem intCast_units_neg_one_pow (k : ℕ) :
    ((((-1 : ℤˣ) ^ k : ℤ)) : Polynomial ℝ) = (-1) ^ k := by
  induction k with
  | zero => simp
  | succ n ih => rw [pow_succ, Int.cast_mul, ih, pow_succ]; simp

/-- **Step A: per-term rewrite.** For an edge-involution `σ`, its contribution `sign(σ)·X^{#fix}`
equals `C((−1)^{|M(σ)|})·X^{n−2|M(σ)|}` — the term of the matching polynomial indexed by the matching
`M(σ)`. Uses `sign_involution` (=(−1)^{supp/2}), `support_card_eq` (supp=2|M|) and `#fix = n−supp`. -/
theorem edgeInv_term {σ : Equiv.Perm V} (h : G.IsEdgeInvolution σ) :
    ((Equiv.Perm.sign σ : ℤ) : Polynomial ℝ)
        * Polynomial.X ^ (Finset.univ.filter (fun i => σ i = i)).card
      = Polynomial.C ((-1 : ℝ) ^ (matchingOfPerm σ).card)
        * Polynomial.X ^ (Fintype.card V - 2 * (matchingOfPerm σ).card) := by
  have hM : σ.support.card / 2 = (matchingOfPerm σ).card := by
    rw [G.support_card_eq h]; omega
  have hfix : (Finset.univ.filter (fun i => σ i = i)) = σ.supportᶜ := by
    ext i; simp [Equiv.Perm.mem_support]
  rw [sign_involution σ h.1, hM, hfix, Finset.card_compl, G.support_card_eq h]
  congr 1
  rw [map_pow, map_neg, map_one]
  exact intCast_units_neg_one_pow _

/-- A matching of an edge-involution has at most `n/2` edges (its `2|M|` matched vertices fit in `V`). -/
theorem matchingOfPerm_card_le {σ : Equiv.Perm V} (h : G.IsEdgeInvolution σ) :
    (matchingOfPerm σ).card ≤ Fintype.card V / 2 := by
  have h1 := G.support_card_eq h
  have h2 := Finset.card_le_univ σ.support
  omega

/-- `M(σ)` is a `|M(σ)|`-edge matching of `G`. -/
theorem matchingOfPerm_mem {σ : Equiv.Perm V} (h : G.IsEdgeInvolution σ) :
    matchingOfPerm σ ∈ G.matchingsOfCard (matchingOfPerm σ).card := by
  rw [mem_matchingsOfCard]
  exact ⟨G.matchingOfPerm_subset h, rfl, G.matchingOfPerm_isMatching h⟩

open scoped Classical in
/-- **Step B: reindex** the edge-involution sum to a sum over all matchings of `G`, via the bijection
`σ ↦ M(σ)` / `M ↦ σ_M`. -/
theorem sum_filter_eq_sum_matchings :
    (∑ σ ∈ Finset.univ.filter G.IsEdgeInvolution,
        Polynomial.C ((-1 : ℝ) ^ (matchingOfPerm σ).card)
          * Polynomial.X ^ (Fintype.card V - 2 * (matchingOfPerm σ).card))
      = ∑ M ∈ (G.edgeFinset.powerset).filter IsMatchingSet,
          Polynomial.C ((-1 : ℝ) ^ M.card) * Polynomial.X ^ (Fintype.card V - 2 * M.card) := by
  refine Finset.sum_bij' (fun σ _ => matchingOfPerm σ)
    (fun M hM => permOfMatching (Finset.mem_filter.mp hM).2) ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [Finset.mem_filter, Finset.mem_powerset]
    have h := (Finset.mem_filter.mp hσ).2
    exact ⟨G.matchingOfPerm_subset h, G.matchingOfPerm_isMatching h⟩
  · intro M hM
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      G.permOfMatching_isEdgeInvolution _ (Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1)⟩
  · intro σ hσ
    exact G.permOfMatching_matchingOfPerm (Finset.mem_filter.mp hσ).2
  · intro M hM
    exact G.matchingOfPerm_permOfMatching _ (Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1)
  · intro σ _
    rfl

open scoped Classical in
/-- **Step C: group by edge-count.** The sum over all matchings, grouped by cardinality `k`, gives the
matching polynomial (each size-`k` class contributes `m_k` copies of `C((−1)^k)·X^{n−2k}`). -/
theorem sum_matchings_eq_matchingPoly :
    (∑ M ∈ (G.edgeFinset.powerset).filter IsMatchingSet,
        Polynomial.C ((-1 : ℝ) ^ M.card) * Polynomial.X ^ (Fintype.card V - 2 * M.card))
      = G.matchingPoly := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (Fintype.card V / 2 + 1))
        (g := fun M => M.card)]
  · unfold matchingPoly
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hset : ((G.edgeFinset.powerset).filter IsMatchingSet).filter (fun M => M.card = k)
        = G.matchingsOfCard k := by
      rw [Finset.filter_filter, matchingsOfCard, Finset.powersetCard_eq_filter, Finset.filter_filter]
      exact Finset.filter_congr (fun M _ => by rw [and_comm])
    rw [hset, Finset.sum_congr rfl (fun M hM => by rw [(mem_matchingsOfCard.mp hM).2.1]),
      Finset.sum_const, ← smul_mul_assoc, nsmul_eq_mul, ← Polynomial.C_eq_natCast, ← map_mul]
    congr 2
    unfold matchingNumber
    ring
  · intro M hM
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1
    have hei := G.permOfMatching_isEdgeInvolution (Finset.mem_filter.mp hM).2 hsub
    have hround := G.matchingOfPerm_permOfMatching (Finset.mem_filter.mp hM).2 hsub
    have := G.matchingOfPerm_card_le hei
    rwa [hround] at this

/-! ## The Godsil–Gutman identity (C2, complete) -/

/-- **Godsil–Gutman (Component C2).** The sum over all `±1` edge-signings of the characteristic
polynomial of the signed adjacency matrix equals `#configs • matchingPoly G`. Equivalently, the
*expected* characteristic polynomial of a uniformly random signing is the matching polynomial. This is
the bridge from the spectral side to the combinatorial side of the Marcus–Spielman–Srivastava program.

Assembles: `charpoly_sum_eq_filter` (only edge-involutions survive) ∘ `edgeInv_term` (each contributes a
matching-polynomial term) ∘ `sum_filter_eq_sum_matchings` (bijection) ∘ `sum_matchings_eq_matchingPoly`
(group by edge-count). -/
theorem godsil_gutman : G.expected_charpoly_eq_matchingPoly_target := by
  rw [expected_charpoly_eq_matchingPoly_target, charpoly_sum_eq_filter, ← Finset.sum_mul,
    Finset.sum_congr rfl (fun σ hσ => G.edgeInv_term (Finset.mem_filter.mp hσ).2),
    G.sum_filter_eq_sum_matchings, G.sum_matchings_eq_matchingPoly,
    Polynomial.C_eq_natCast, nsmul_eq_mul, mul_comm]

/-! ## The parity-closed-walk kernel (moment-level companion of Godsil–Gutman)

The algebraic heart of the identity `P_d = 2^{−|E|} ∑_π trace(A_π^d)` (Chen–van Dam–Bu 2023): a walk's
signed weight, averaged over all `±1` signings, vanishes unless the walk is **parity-closed** (every
edge used an even number of times). It is exactly our sign-killing engine `sum_signOf_pow_*` summed over
edges via `Fintype.prod_sum`. Here `t e` is the edge-multiplicity of a walk; the product over signings
of `signOf(cfg e)^{t e}` is `2^{#pairs}` if all multiplicities are even, else `0`. -/
theorem sum_signOf_prod_pow (t : Sym2 V → ℕ) :
    (∑ cfg : Sym2 V → Bool, ∏ e : Sym2 V, (if cfg e then (1 : ℝ) else -1) ^ (t e))
      = if (∀ e : Sym2 V, Even (t e)) then (2 : ℝ) ^ Fintype.card (Sym2 V) else 0 := by
  rw [← Fintype.prod_sum (fun (e : Sym2 V) (b : Bool) => (if b then (1 : ℝ) else -1) ^ (t e))]
  by_cases h : ∀ e : Sym2 V, Even (t e)
  · rw [if_pos h, Finset.prod_congr rfl (fun e _ => sum_signOf_pow_eq_two_of_even (h e)),
      Finset.prod_const, Finset.card_univ]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨e, he⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ e)
      (sum_signOf_pow_eq_zero_of_odd ((Nat.even_or_odd (t e)).resolve_left he))

/-! ## The unifying principle: averaging over signings is the `ℤ/2` parity projection

Both formalized results in this file are instances of one fact — **averaging over all `±1` signings
projects onto the parity-even part**. Concretely (`sum_signOf_prod_pow`), `∑_cfg ∏_e signOf(cfg e)^{t e}`
is `2^{#pairs}` when every multiplicity `t e` is even, and `0` otherwise. The "survives ⟺ even" gate
(`signAvg_ne_zero_iff`) is the common heart of the two levels:

* **Godsil–Gutman** (`godsil_gutman`, characteristic-polynomial level): a permutation `σ` contributes to
  `∑_cfg charpoly(A_cfg)` exactly when its support multiplicities are all even — i.e. `σ² = 1`, an
  involution, i.e. a matching. (Elementary-symmetric functions of the eigenvalues.)
* **Parity-closed walks** (Chen–van Dam–Bu 2023, moment level): a closed walk contributes to
  `∑_cfg trace(A_cfg^d)` exactly when every edge is used an even number of times — a parity-closed walk.
  (Power sums of the eigenvalues.)

Elementary-symmetric (charpoly) and power-sum (moments) are two readings of the **same** `ℤ/2`-Fourier
projection `∑_{s ∈ {±1}} s^k = 2·[k \text{ even}]`. -/

/-- **The parity gate.** A sign-monomial survives the signing-average iff its multiplicity vector is
even — the single principle underlying both `godsil_gutman` (where "even everywhere" = `σ²=1`, a
matching) and the parity-closed-walk identity (where it = the walk is parity-closed). -/
theorem signAvg_ne_zero_iff (t : Sym2 V → ℕ) :
    (∑ cfg : Sym2 V → Bool, ∏ e : Sym2 V, (if cfg e then (1 : ℝ) else -1) ^ (t e)) ≠ 0
      ↔ ∀ e : Sym2 V, Even (t e) := by
  rw [sum_signOf_prod_pow]
  by_cases h : ∀ e : Sym2 V, Even (t e)
  · rw [if_pos h]; exact iff_of_true (pow_ne_zero _ two_ne_zero) h
  · rw [if_neg h]; exact iff_of_false (by simp) h

end SimpleGraph
