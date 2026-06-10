import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card

/-!
# Cauchy–Binet formula  (sorry-free)

`det (A * B)` for a non-square pair `A : m×n`, `B : n×m` equals the sum over `m`-element subsets
`S ⊆ n` of the product of the two maximal minors selected by `S`.  Absent from Mathlib; entry point
for the Kirchhoff matrix-tree theorem (see `CAUCHY_BINET_PLAN.md`).

Indexing: an `m`-subset `S` of `n` (a `{s : Finset n // s.card = Fintype.card m}`) gives an order
embedding `S.orderEmbOfFin : Fin (card m) ↪o n`; reindex rows of `A` (resp. cols of `B`) through
`Fintype.equivFin m` to get square `Fin (card m) × Fin (card m)` minors.

## Proof architecture
* `det_mul_eq_sum_submatrix` (**Lemma A**): the determinant-of-product expanded over *all*
  functions `g : m → n`, each weighting the column-minor `det (A.submatrix id g)` by `∏ i, B (g i) i`.
* `fiber_sum`: for a fixed column indexing `φ`, summing the Lemma-A summand over all relabellings
  `π : Perm (Fin (card m))` rebuilds the product of the two minors (the `B`-determinant emerges from
  summing the plain `B`-product against the sign carried by the `A`-minor).
* `det_mul_cauchyBinet`: the main theorem regroups Lemma A — non-injective `g` give a repeated-column
  minor (det 0); injective `g` biject with `Σ S, Perm (Fin (card m))` via `cbPerm` / `image_Phi`,
  and `fiber_sum` collapses each fiber.  Depends only on `propext, Classical.choice, Quot.sound`.
-/

open Matrix Finset Equiv

namespace Matrix

/-- **Lemma A** — determinant of a product expanded over all index functions `g : m → n`.
Each `g` contributes the `m×m` column-minor `A.submatrix id g` weighted by `∏ i, B (g i) i`.
This is Cauchy–Binet *before* grouping the `g`'s by their image. -/
theorem det_mul_eq_sum_submatrix {R : Type*} [CommRing R]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ g : m → n, (A.submatrix id g).det * ∏ i, B (g i) i := by
  conv_lhs => rw [det_apply']
  simp_rw [mul_apply, Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [det_apply', Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id_eq, Finset.prod_mul_distrib]
  ring

/-- **Fiber sum** — for a fixed indexing `φ : Fin (card m) → n` of `m` columns, summing the
Lemma-A summand over all relabellings `π` of those columns rebuilds the product of the two minors.
The `A`-minor carries `sign π` (a column permutation of a determinant); summing the plain `B`-product
against that sign reconstructs the `B`-determinant.  Holds for *any* `φ` (no order/injectivity needed). -/
theorem fiber_sum {R : Type*} [CommRing R]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (A : Matrix m n R) (B : Matrix n m R) (φ : Fin (Fintype.card m) → n) :
    ∑ π : Equiv.Perm (Fin (Fintype.card m)),
        (A.submatrix id fun j => φ (π (Fintype.equivFin m j))).det
          * ∏ i, B (φ (π (Fintype.equivFin m i))) i
      = (A.submatrix (Fintype.equivFin m).symm φ).det
          * (B.submatrix φ (Fintype.equivFin m).symm).det := by
  set e := Fintype.equivFin m with he
  have hA : ∀ π : Equiv.Perm (Fin (Fintype.card m)),
      (A.submatrix id fun j => φ (π (e j))).det
        = ((Equiv.Perm.sign π : ℤ) : R) * (A.submatrix e.symm φ).det := by
    intro π
    have e1 : (A.submatrix id fun j => φ (π (e j)))
        = ((A.submatrix e.symm φ).submatrix id ⇑π).submatrix ⇑e ⇑e := by
      ext i j; simp [submatrix_apply]
    rw [e1, Matrix.det_submatrix_equiv_self e, det_permute']
  have hB : ∀ π : Equiv.Perm (Fin (Fintype.card m)),
      (∏ i, B (φ (π (e i))) i) = ∏ a, B (φ (π a)) (e.symm a) :=
    fun π => Fintype.prod_equiv e _ _ fun i => by simp
  simp_rw [hA, hB]
  rw [det_apply' (B.submatrix φ e.symm), Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp only [submatrix_apply]
  ring

section Regroup
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [LinearOrder n]

omit [DecidableEq m] [Fintype n] in
/-- For injective `g : m → n`, the cardinality of its image is `Fintype.card m`. -/
theorem card_image_eq {g : m → n} (hg : Function.Injective g) :
    (Finset.image g Finset.univ).card = Fintype.card m := by
  rw [Finset.card_image_of_injective _ hg, Finset.card_univ]

/-- The permutation of `Fin (card m)` recovered from an injective `g : m → n`: it relabels the
sorted image `S = image g` so that `S.orderEmbOfFin ∘ cbPerm ∘ equivFin = g` (`cbPerm_spec`). -/
noncomputable def cbPerm {g : m → n} (hg : Function.Injective g) :
    Equiv.Perm (Fin (Fintype.card m)) :=
  Equiv.ofBijective
    (fun a => ((Finset.image g Finset.univ).orderIsoOfFin (card_image_eq hg)).symm
      ⟨g ((Fintype.equivFin m).symm a), Finset.mem_image_of_mem g (Finset.mem_univ _)⟩)
    (Function.Injective.bijective_of_finite (by
      intro a b hab
      have h3 := ((Finset.image g Finset.univ).orderIsoOfFin (card_image_eq hg)).symm.injective hab
      exact (Fintype.equivFin m).symm.injective (hg (Subtype.ext_iff.mp h3))))

omit [DecidableEq m] [Fintype n] in
/-- Defining property of `cbPerm`: composing the sorted-image embedding with `cbPerm` and the
canonical relabelling `equivFin` recovers `g`. -/
theorem cbPerm_spec {g : m → n} (hg : Function.Injective g) (j : m) :
    (Finset.image g Finset.univ).orderEmbOfFin (card_image_eq hg) (cbPerm hg (Fintype.equivFin m j))
      = g j := by
  rw [← Finset.coe_orderIsoOfFin_apply]
  simp only [cbPerm, Equiv.ofBijective_apply, Equiv.symm_apply_apply,
    OrderIso.apply_symm_apply]

omit [DecidableEq m] [Fintype n] in
/-- The image of `m` under `S.orderEmbOfFin ∘ π ∘ equivFin` is all of `S` (the relabelling `π`
and `equivFin` are bijections, so the sorted embedding still sweeps out its whole range `S`). -/
theorem image_Phi (S : Finset n) (hS : S.card = Fintype.card m)
    (π : Equiv.Perm (Fin (Fintype.card m))) :
    Finset.image (fun j => S.orderEmbOfFin hS (π (Fintype.equivFin m j))) Finset.univ = S := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩; exact S.orderEmbOfFin_mem hS _
  · intro hx
    have hx' : x ∈ Finset.image (S.orderEmbOfFin hS) Finset.univ := by
      rw [Finset.image_orderEmbOfFin_univ]; exact hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx'
    obtain ⟨a, ha⟩ := hx'
    exact ⟨(Fintype.equivFin m).symm (π.symm a), by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact ha⟩

/-- **Cauchy–Binet formula.** `det (A * B)` is the sum, over `m`-element subsets `S` of the column
index `n`, of the product of the two maximal minors picked out by `S`.  Sorry-free. -/
theorem det_mul_cauchyBinet {R : Type*} [CommRing R] (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det =
      ∑ S : {s : Finset n // s.card = Fintype.card m},
        (A.submatrix (Fintype.equivFin m).symm (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) (Fintype.equivFin m).symm).det := by
  classical
  rw [det_mul_eq_sum_submatrix]
  simp_rw [← fiber_sum A B]
  rw [Finset.sum_sigma']
  -- vanishing of the non-injective summands
  have hvanish : ∀ g : m → n, ¬ Function.Injective g →
      (A.submatrix id g).det * ∏ i, B (g i) i = 0 := by
    intro g hg
    rw [Function.not_injective_iff] at hg
    obtain ⟨a, b, hgab, hab⟩ := hg
    rw [det_zero_of_column_eq hab fun x => by simp [submatrix_apply, hgab], zero_mul]
  rw [← Finset.sum_subset (Finset.filter_subset (fun g => Function.Injective g) Finset.univ)
    (fun g _ hgf => hvanish g fun hinj => hgf (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinj⟩))]
  symm
  refine Finset.sum_bij (fun p _ => fun j => p.1.1.orderEmbOfFin p.1.2 (p.2 (Fintype.equivFin m j)))
    ?hi ?inj ?surj ?h
  case hi =>
    intro p _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun a b hab => ?_⟩
    exact (Fintype.equivFin m).injective (p.2.injective ((p.1.1.orderEmbOfFin p.1.2).injective hab))
  case inj =>
    rintro ⟨⟨S1, hS1⟩, π1⟩ _ ⟨⟨S2, hS2⟩, π2⟩ _ heq
    dsimp only at heq
    have hSeq : S1 = S2 := by
      rw [← image_Phi S1 hS1 π1, ← image_Phi S2 hS2 π2, heq]
    subst hSeq
    have hπ : π1 = π2 := by
      refine Equiv.ext fun a => ?_
      have h3 := congrFun heq ((Fintype.equivFin m).symm a)
      simp only [Equiv.apply_symm_apply] at h3
      exact (S1.orderEmbOfFin hS1).injective h3
    rw [hπ]
  case surj =>
    intro g hg
    rw [Finset.mem_filter] at hg
    refine ⟨⟨⟨Finset.image g Finset.univ, card_image_eq hg.2⟩, cbPerm hg.2⟩,
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    funext j
    exact cbPerm_spec hg.2 j
  case h =>
    intro p _
    rfl

end Regroup

end Matrix
