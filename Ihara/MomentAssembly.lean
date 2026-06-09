/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Ihara.MomentBridge
import Ihara.GodsilMoment
import Ihara.PowerSumLogDeriv
import Ihara.ResolventDiag

/-!
# Godsil moment theorem — final assembly (weld)

This file welds the matching side and the trace side of Godsil's moment theorem
`matchingPowerSum G k = treeLikeWalkCount G k` into a single power-series identity.

## The chain

Trace side (per path tree `T_v = pathTree v`, root `r`):
* Stone 1 `treeLikeWalkCount_eq_sum_pathTree_adjMatrix_pow`: `tlwc G k = Σ_v [A(T_v)ᵏ]_{r r}`.
* Stone 3 `resolventGenfun_diag_mul_coe_charpolyRev`: `(Σ_k [A(T_v)ᵏ]_{rr} Xᵏ)·↑charpolyRev(A T_v) =
  ↑charpolyRev(A(T_v)∖r)` (submatrix form).
* **Reconciliation (this file):** `charpolyRev(A(T_v)∖r) = charpolyRev(A((T_v).deleteIncidenceSet r))`
  — the isolated-root path tree. Because `A(deleteIncidenceSet r)` has a zero row/column at `r`, the
  matrix `1 - X·A(delInc r)` has row `r` equal to `eᵣ`, so its determinant collapses to the `{≠r}`
  minor (`det_eq_det_submatrix_ne_of_row_eq_single`, the block-triangular lemma below), which is the
  same minor `Stone 3` produces; the `{≠r}` blocks of `A(delInc r)` and `A(T_v)` agree.
* Forest bridge `matchingPoly_pathTree_eq_charpoly` + `godsil_resolvent_charpoly_form`: turn the
  per-tree `charpolyRev` ratio into the **graph** ratio `↑reverse μ(G−v)/↑reverse μ(G)`.

Matching side: `matchingPowerSum_genfun` + `geomSeries_sum_mul_prod` (★) + `derivative_prod_X_sub_C`
(B2) + `reverse_prod_X_sub_C` (B3) + splitting `μ_ℂ = ∏(X-θ)`.

Both meet at `mk(·)·↑reverse μ = ↑reverse(X·μ')` (vertex-deletion `Σ_v μ(G.deleteIncidenceSet v) =
X·μ'`), and `↑reverse μ` is a unit (constant term = leading coeff of the monic `μ` = 1), so the two
generating functions coincide and the coefficients give the moment theorem.

This file proceeds milestone by milestone; see the section markers.
-/

open Matrix PowerSeries

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- **(GL) Determinant collapses to a principal minor when a row is a basis vector.** If row `i` of
`B` is `eᵢ = Pi.single i 1`, then `det B = det (B∖i)` (the `{j ≠ i}` principal minor). Block-triangular
reindex `n ≃ {·=i} ⊕ {·≠i}` (`Equiv.sumCompl`): row `i` being `eᵢ` kills the top-right block, so
`det_fromBlocks_zero₁₂` factors the determinant as `(1×1 block = 1) · det(B∖i)`. This is the
matrix-with-an-isolated-index determinant, the abstraction of `adjugate_diag_eq_det_submatrix_ne`. -/
theorem det_eq_det_submatrix_ne_of_row_eq_single (B : Matrix n n R) (i : n)
    (hrow : B i = Pi.single i (1 : R)) :
    det B = det (B.submatrix (Subtype.val : {j // j ≠ i} → n) (Subtype.val : {j // j ≠ i} → n)) := by
  classical
  haveI : Unique {a : n // a = i} := ⟨⟨⟨i, rfl⟩⟩, fun y => Subtype.ext y.2⟩
  rw [← det_submatrix_equiv_self (Equiv.sumCompl (· = i)) B,
    ← fromBlocks_toBlocks (B.submatrix (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i)))]
  have h12 : (B.submatrix (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i))).toBlocks₁₂ = 0 := by
    ext s t
    simp only [toBlocks₁₂, of_apply, submatrix_apply, Equiv.sumCompl_apply_inl,
      Equiv.sumCompl_apply_inr, zero_apply]
    rw [show ((s : {a // a = i}) : n) = i from s.2, hrow, Pi.single_apply, if_neg t.2]
  have h11 : (B.submatrix (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i))).toBlocks₁₁.det = 1 := by
    rw [det_unique]
    simp only [toBlocks₁₁, of_apply, submatrix_apply, Equiv.sumCompl_apply_inl]
    rw [show ((default : {a // a = i}) : n) = i from (default : {a // a = i}).2, hrow,
      Pi.single_eq_same]
  have h22 : (B.submatrix (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i))).toBlocks₂₂
      = B.submatrix (Subtype.val : {j // j ≠ i} → n) (Subtype.val : {j // j ≠ i} → n) := by
    ext s t
    simp only [toBlocks₂₂, of_apply, submatrix_apply, Equiv.sumCompl_apply_inr]
  rw [h12, det_fromBlocks_zero₁₂, h11, h22, one_mul]

end Matrix

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- **Reflection of a sum at a fixed length = sum of reverses, when all degrees agree.** If every
`p i` (`i ∈ s`) has `natDegree = N`, then `Σ reverse (p i) = reflect N (Σ p i)`. Each
`reverse (p i) = reflect (natDegree (p i)) (p i) = reflect N (p i)`, and `reflect N` is additive
(`reflect_add`), so it commutes with the finite sum. This packages the degree-bookkeeping that lets
the per-vertex/per-root reversed pieces of the moment theorem be summed under a single reflection. -/
theorem sum_reverse_eq_reflect_sum {ι : Type*} (s : Finset ι) (p : ι → R[X]) (N : ℕ)
    (hp : ∀ i ∈ s, (p i).natDegree = N) :
    ∑ i ∈ s, (p i).reverse = reflect N (∑ i ∈ s, p i) := by
  let φ : R[X] →+ R[X] := ⟨⟨reflect N, reflect_zero⟩, fun a b => reflect_add a b N⟩
  rw [show reflect N (∑ i ∈ s, p i) = ∑ i ∈ s, reflect N (p i) from map_sum φ p s]
  exact Finset.sum_congr rfl fun i hi => by
    rw [show (p i).reverse = reflect (p i).natDegree (p i) from rfl, hp i hi]

/-- Multiset form of `sum_reverse_eq_reflect_sum`: if every polynomial in `m` has `natDegree = N`,
then `(m.map reverse).sum = reflect N m.sum`. Same proof (`reflect_add` additivity, `reverse =
reflect natDegree`), over a multiset rather than a `Finset`. -/
theorem sum_map_reverse_eq_reflect_sum (m : Multiset R[X]) (N : ℕ)
    (hp : ∀ p ∈ m, p.natDegree = N) :
    (m.map reverse).sum = reflect N m.sum := by
  let φ : R[X] →+ R[X] := ⟨⟨reflect N, reflect_zero⟩, fun a b => reflect_add a b N⟩
  rw [show reflect N m.sum = (m.map (reflect N)).sum from map_multiset_sum φ m]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp' => by
    rw [show p.reverse = reflect p.natDegree p from rfl, hp p hp'])

/-- **(PB) Matching-side polynomial identity.** For a monic split `p` over `ℂ`, the sum over its
roots of the "leave-one-out" reversed-factor products equals the reflected `X·p'`:

  `Σ_{θ∈roots} ∏_{φ∈roots.erase θ}(1 - φX) = reflect_n(X · p')`,   `n = natDegree p`.

This is the polynomial heart of the matching side of the moment theorem. `p` splits as `∏(X-θ)`
(`Splits.eq_prod_roots_of_monic`), so `p' = Σ_θ ∏_{erase}(X-φ)` (`derivative_prod_X_sub_C`, B2), and
`X·p' = Σ_θ X·∏_{erase}`; each `X·∏_{erase}` has `natDegree = n` (`natDegree_X_mul` + the
product-of-`(n-1)`-monic-linears degree), so the reflected sum splits termwise
(`sum_map_reverse_eq_reflect_sum`) into `Σ_θ reverse(X·∏_{erase}) = Σ_θ ∏_{erase}(1-φX)` via
`reverse_X_mul` + `reverse_prod_X_sub_C`. -/
theorem reflect_X_mul_derivative_eq_sum_prod (p : ℂ[X]) (hm : p.Monic) :
    (p.roots.map fun a => ((p.roots.erase a).map fun b => (1 : ℂ[X]) - C b * X).prod).sum
      = (X * derivative p).reflect p.natDegree := by
  have hp : Splits p := IsAlgClosed.splits p
  have hcard : p.roots.card = p.natDegree := splits_iff_card_roots.mp hp
  have hsplit : p = (p.roots.map fun a => X - C a).prod := hp.eq_prod_roots_of_monic hm
  have hder : derivative p
      = (p.roots.map fun a => ((p.roots.erase a).map fun b => X - C b).prod).sum := by
    conv_lhs => rw [hsplit]
    exact derivative_prod_X_sub_C _
  have hnd : ∀ q ∈ p.roots.map fun a => X * ((p.roots.erase a).map fun b => X - C b).prod,
      q.natDegree = p.natDegree := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hq
    have hne : ((p.roots.erase a).map fun b => X - C b).prod ≠ 0 :=
      (monic_multiset_prod_of_monic _ _ fun b _ => monic_X_sub_C b).ne_zero
    rw [natDegree_X_mul hne, natDegree_multiset_prod_X_sub_C_eq_card,
      Multiset.card_erase_add_one ha, hcard]
  rw [hder, ← Multiset.sum_map_mul_left,
    ← sum_map_reverse_eq_reflect_sum _ p.natDegree hnd, Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun a _ => by
    simp only [Function.comp_apply, reverse_X_mul, reverse_prod_X_sub_C])

/-- **(M5-core) Matching generating function times the reversed polynomial.** For a monic `p` over
`ℂ`, the generating function of the power sums of its roots, times `↑reverse p`, is `↑reflect_n(X·p')`:

  `mk (Σ_θ θᵏ) · ↑reverse p = ↑reflect_n(X · p')`,   `n = natDegree p`.

`mk (Σ_θ θᵏ) = Σ_θ geomSeries θ` (`powerSum_genfun`); `↑reverse p = ∏_θ (1 - θX)` in `ℂ⟦X⟧`
(splitting + `reverse_prod_X_sub_C` + the coercion of a polynomial product); so by
`geomSeries_sum_mul_prod` (★) the product collapses to `Σ_θ ∏_{erase}(1 - φX)`, which is `↑` of the
polynomial identity `reflect_X_mul_derivative_eq_sum_prod` (PB). -/
theorem mk_powerSum_mul_reverse (p : ℂ[X]) (hm : p.Monic) :
    (PowerSeries.mk fun k => (p.roots.map (· ^ k)).sum) * (p.reverse : ℂ⟦X⟧)
      = ((X * derivative p).reflect p.natDegree : ℂ⟦X⟧) := by
  have hsplit : p = (p.roots.map fun a => X - C a).prod :=
    (IsAlgClosed.splits p).eq_prod_roots_of_monic hm
  have hcoe : ∀ m : Multiset ℂ,
      (m.map fun a => 1 - PowerSeries.C a * PowerSeries.X).prod
        = (((m.map fun a => 1 - C a * X).prod : ℂ[X]) : ℂ⟦X⟧) := fun m => by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => by
      simp [Polynomial.coeToPowerSeries.ringHom_apply])
  have hrev : (p.reverse : ℂ⟦X⟧)
      = (p.roots.map fun a => 1 - PowerSeries.C a * PowerSeries.X).prod := by
    rw [hcoe, ← reverse_prod_X_sub_C, ← hsplit]
  have hbcoe : (p.roots.map fun a =>
        ((p.roots.erase a).map fun b => 1 - PowerSeries.C b * PowerSeries.X).prod).sum
      = (((p.roots.map fun a =>
          ((p.roots.erase a).map fun b => 1 - C b * X).prod).sum : ℂ[X]) : ℂ⟦X⟧) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun a _ => ?_)
    rw [Function.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, ← hcoe]
  rw [PowerSeries.powerSum_genfun, hrev, PowerSeries.geomSeries_sum_mul_prod, hbcoe,
    reflect_X_mul_derivative_eq_sum_prod p hm]

end Polynomial

namespace SimpleGraph

open Matrix PowerSeries

variable {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]

omit [Fintype V] in
/-- The `r`-th **row** of the adjacency matrix of `G.deleteIncidenceSet r` is zero: deleting all
edges incident to `r` makes `r` isolated, so `r` is adjacent to nothing. -/
theorem adjMatrix_deleteIncidenceSet_self (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (r : V) :
    ((G.deleteIncidenceSet r).adjMatrix R) r = 0 := by
  funext j
  simp [adjMatrix_apply, deleteIncidenceSet_adj]

omit [Fintype V] in
/-- The `{≠r}` **principal submatrix** is unaffected by deleting the edges at `r`: an entry between
two vertices `≠ r` is an edge of `G.deleteIncidenceSet r` iff it is an edge of `G`. -/
theorem adjMatrix_submatrix_deleteIncidenceSet (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (r : V) :
    ((G.deleteIncidenceSet r).adjMatrix R).submatrix
        (Subtype.val : {j // j ≠ r} → V) (Subtype.val : {j // j ≠ r} → V)
      = (G.adjMatrix R).submatrix
        (Subtype.val : {j // j ≠ r} → V) (Subtype.val : {j // j ≠ r} → V) := by
  ext s t
  simp only [submatrix_apply, adjMatrix_apply, deleteIncidenceSet_adj, s.2, t.2, ne_eq,
    not_false_eq_true, and_true]

/-- **(M1) `charpolyRev` reconciliation: deleting all edges at the root = deleting the root index.**
`↑charpolyRev(A(G.deleteIncidenceSet r)) = ↑charpolyRev(A(G)∖r)` in `R⟦X⟧`. `A(G.deleteIncidenceSet r)`
has a zero row at `r`, so `1 - X·A(deleteIncidenceSet r)` has row `r` equal to `eᵣ`; its determinant
collapses to the `{≠r}` minor (`det_eq_det_submatrix_ne_of_row_eq_single`), whose blocks agree with
`A(G)∖r` (`adjMatrix_submatrix_deleteIncidenceSet`). This bridges the **submatrix** form of Stone 3
(`resolventGenfun_diag_mul_coe_charpolyRev`) to the **isolated-root** path tree of
`godsil_resolvent_charpoly_form`. -/
theorem coe_charpolyRev_adjMatrix_deleteIncidenceSet (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (r : V) :
    (charpolyRev ((G.deleteIncidenceSet r).adjMatrix R) : R⟦X⟧)
      = (charpolyRev ((G.adjMatrix R).submatrix
          (Subtype.val : {j // j ≠ r} → V) (Subtype.val : {j // j ≠ r} → V)) : R⟦X⟧) := by
  rw [coe_charpolyRev_eq_det, coe_charpolyRev_eq_det]
  have hrow : (1 - (X : R⟦X⟧) • ((G.deleteIncidenceSet r).adjMatrix R).map
      (C : R →+* R⟦X⟧)) r = Pi.single r 1 := by
    funext j
    simp only [sub_apply, smul_apply, map_apply, smul_eq_mul, one_apply,
      congrFun (adjMatrix_deleteIncidenceSet_self (R := R) G r) j, Pi.zero_apply, map_zero,
      mul_zero, sub_zero, Pi.single_apply, eq_comm (a := r)]
  rw [det_eq_det_submatrix_ne_of_row_eq_single _ r hrow, one_sub_X_smul_submatrix_ne,
    adjMatrix_submatrix_deleteIncidenceSet]

/-- **(M3) Per-vertex resolvent identity.** The root–root resolvent of the path tree `T_v`, times the
reversed matching polynomial of `G`, equals the reversed matching polynomial of `G` with all edges at
`v` deleted:

  `(Σ_k [A(T_v)ᵏ]_{rr} Xᵏ) · ↑reverse μ(G) = ↑reverse μ(G.deleteIncidenceSet v)`.

Assembled from Stone 3 (`resolventGenfun_diag_mul_coe_charpolyRev`, submatrix form) reconciled to the
isolated-root tree (M1, `coe_charpolyRev_adjMatrix_deleteIncidenceSet`), the **reversed** Godsil
identity (`godsil_resolvent_charpoly_form` under `reverse_mul_of_domain` over the domain `ℝ[X]`, with
`reverse_charpoly` swapping `reverse ∘ charpoly = charpolyRev`), and cancellation of the unit factor
`↑charpolyRev(A T_v)` (nonzero: `charpoly` is monic, `reverse` preserves nonzero). This is the trace
side reduced to the **same** reversed matching polynomials the matching side speaks. -/
theorem resolventGenfun_pathTree_mul_reverse_matchingPoly
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ((G.pathTree v).adjMatrix ℝ).resolventGenfun (pathTreeRoot G v) (pathTreeRoot G v)
        * (G.matchingPoly.reverse : ℝ⟦X⟧)
      = ((G.deleteIncidenceSet v).matchingPoly.reverse : ℝ⟦X⟧) := by
  have hres : ((G.pathTree v).adjMatrix ℝ).resolventGenfun (pathTreeRoot G v) (pathTreeRoot G v)
        * (((G.pathTree v).adjMatrix ℝ).charpolyRev : ℝ⟦X⟧)
      = ((((G.pathTree v).deleteIncidenceSet (pathTreeRoot G v)).adjMatrix ℝ).charpolyRev : ℝ⟦X⟧) := by
    rw [resolventGenfun_diag_mul_coe_charpolyRev,
      ← coe_charpolyRev_adjMatrix_deleteIncidenceSet (R := ℝ) (G.pathTree v) (pathTreeRoot G v)]
  have hGRrev : (((G.pathTree v).deleteIncidenceSet (pathTreeRoot G v)).adjMatrix ℝ).charpolyRev
        * G.matchingPoly.reverse
      = ((G.pathTree v).adjMatrix ℝ).charpolyRev * (G.deleteIncidenceSet v).matchingPoly.reverse := by
    rw [← reverse_charpoly, ← reverse_charpoly, ← Polynomial.reverse_mul_of_domain,
      ← Polynomial.reverse_mul_of_domain, godsil_resolvent_charpoly_form]
  have hcT : (((G.pathTree v).adjMatrix ℝ).charpolyRev : ℝ⟦X⟧) ≠ 0 := by
    rw [Ne, Polynomial.coe_eq_zero_iff, ← reverse_charpoly, Polynomial.reverse_eq_zero]
    exact ((G.pathTree v).adjMatrix ℝ).charpoly_monic.ne_zero
  apply mul_left_cancel₀ hcT
  rw [mul_comm (((G.pathTree v).adjMatrix ℝ).charpolyRev : ℝ⟦X⟧)
        (((G.pathTree v).adjMatrix ℝ).resolventGenfun (pathTreeRoot G v) (pathTreeRoot G v)
          * (G.matchingPoly.reverse : ℝ⟦X⟧)),
    mul_right_comm, hres, ← Polynomial.coe_mul, hGRrev, Polynomial.coe_mul]

/-- The `ℕ`-valued and `ℝ`-valued adjacency-matrix powers agree under the cast `ℕ → ℝ`: the
adjacency matrix over `ℝ` is the entrywise cast of the one over `ℕ` (`adjMatrix_apply` + `apply_ite`),
and casting commutes with matrix powers (`Matrix.map_pow`). -/
theorem adjMatrix_pow_apply_cast (H : _root_.SimpleGraph V) [DecidableRel H.Adj] (k : ℕ) (i j : V) :
    (((H.adjMatrix ℕ) ^ k) i j : ℝ) = ((H.adjMatrix ℝ) ^ k) i j := by
  have hmap : (H.adjMatrix ℕ).map (Nat.castRingHom ℝ) = H.adjMatrix ℝ := by
    ext a b
    simp [adjMatrix_apply]
  rw [← hmap, ← Matrix.map_pow, Matrix.map_apply, Nat.coe_castRingHom]

/-- **(M4a) Trace generating function as a sum of path-tree resolvents.** The generating function of
the tree-like-walk counts is the sum over vertices of the root–root resolvent of each path tree:
`mk (tlwc G ·) = Σ_v resolventGenfun(A T_v)_{rr}` (over `ℝ`). Stone 1
(`treeLikeWalkCount_eq_sum_pathTree_adjMatrix_pow`) coefficientwise, with the `ℕ→ℝ` cast. -/
theorem mk_treeLikeWalkCount_eq_sum_resolventGenfun (G : _root_.SimpleGraph V)
    [DecidableRel G.Adj] :
    (PowerSeries.mk fun k => (G.treeLikeWalkCount k : ℝ))
      = ∑ v : V, ((G.pathTree v).adjMatrix ℝ).resolventGenfun (pathTreeRoot G v)
          (pathTreeRoot G v) := by
  ext k
  simp only [PowerSeries.coeff_mk, map_sum, resolventGenfun_apply]
  rw [treeLikeWalkCount_eq_sum_pathTree_adjMatrix_pow, Nat.cast_sum]
  exact Finset.sum_congr rfl fun v _ => adjMatrix_pow_apply_cast (G.pathTree v) k _ _

/-- **(M4) Trace side reduced to the reflected derivative.** The tree-like-walk generating function,
times `↑reverse μ(G)`, equals `↑reflect_n(X·μ'(G))` (`n = card V`):

  `mk (tlwc G ·) · ↑reverse μ(G) = ↑reflect_n(X · μ'(G))`.

Sum the per-vertex resolvent identity (M3) over `v` (`Finset.sum_mul`), push the coercion through the
sum, collapse `Σ_v reverse μ(G.deleteIncidenceSet v) = reflect_n(Σ_v μ(G.deleteIncidenceSet v))`
(`sum_reverse_eq_reflect_sum`, every `μ(G−v)` has `natDegree = n`), and apply the vertex-deletion law
`Σ_v μ(G.deleteIncidenceSet v) = X·μ'`. The whole trace side now lives in the reflected matching
polynomials — the exact object the matching side produces. -/
theorem mk_treeLikeWalkCount_mul_reverse_eq (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    (PowerSeries.mk fun k => (G.treeLikeWalkCount k : ℝ)) * (G.matchingPoly.reverse : ℝ⟦X⟧)
      = ((Polynomial.X * Polynomial.derivative G.matchingPoly).reflect (Fintype.card V) : ℝ⟦X⟧) := by
  have hpoly : (∑ v : V, (G.deleteIncidenceSet v).matchingPoly.reverse)
      = (Polynomial.X * Polynomial.derivative G.matchingPoly).reflect (Fintype.card V) := by
    rw [Polynomial.sum_reverse_eq_reflect_sum Finset.univ
        (fun v => (G.deleteIncidenceSet v).matchingPoly) (Fintype.card V)
        (fun v _ => matchingPoly_natDegree _),
      sum_matchingPoly_deleteIncidenceSet]
  rw [mk_treeLikeWalkCount_eq_sum_resolventGenfun, Finset.sum_mul,
    Finset.sum_congr rfl (fun v _ => resolventGenfun_pathTree_mul_reverse_matchingPoly G v),
    ← hpoly]
  exact (map_sum Polynomial.coeToPowerSeries.ringHom
    (fun v => (G.deleteIncidenceSet v).matchingPoly.reverse) Finset.univ).symm

/-- **(M5) Matching side reduced to the reflected derivative.** Specialise `mk_powerSum_mul_reverse`
to `μ_ℂ = μ(G).map(ℝ→ℂ)` (monic, `natDegree = card V`):

  `mk (matchingPowerSum G ·) · ↑reverse μ_ℂ = ↑reflect_n(X · μ_ℂ')`,   `n = card V`.

The matching generating function now lives in the same reflected matching polynomials as the trace
side (M4), the two halves ready to be welded after the `ℝ→ℂ` bridge. -/
theorem mk_matchingPowerSum_mul_reverse_eq (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    (PowerSeries.mk fun k => G.matchingPowerSum k)
        * ((G.matchingPoly.map (algebraMap ℝ ℂ)).reverse : ℂ⟦X⟧)
      = ((Polynomial.X * Polynomial.derivative (G.matchingPoly.map (algebraMap ℝ ℂ))).reflect
          (Fintype.card V) : ℂ⟦X⟧) := by
  have hmonic : (G.matchingPoly.map (algebraMap ℝ ℂ)).Monic := (matchingPoly_monic G).map _
  have hcardV : (G.matchingPoly.map (algebraMap ℝ ℂ)).natDegree = Fintype.card V := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective, matchingPoly_natDegree]
  simp only [matchingPowerSum]
  rw [← hcardV, Polynomial.mk_powerSum_mul_reverse _ hmonic]

end SimpleGraph
