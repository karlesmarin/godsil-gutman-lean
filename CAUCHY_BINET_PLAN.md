# Cauchy–Binet → Matrix-Tree in Lean — plan (updated 2026-06-10)

## Why: novel, timeless, our edge (det machinery). A merged Mathlib PR = real standing.

## GATE result (re-confirmed 2026-06-10, Mathlib v4.30)
- **Cauchy–Binet: ABSENT from Mathlib** (re-grepped `Mathlib/LinearAlgebra`). → PR-able.
- **Matrix-tree (Kirchhoff): ABSENT.** Builds on Cauchy–Binet.
- Building blocks PRESENT: `Matrix.det_apply'`, `Fintype.prod_sum`, `Matrix.det_submatrix_equiv_self`,
  `Matrix.det_permute'`, `Matrix.det_zero_of_column_eq`, `Finset.orderEmbOfFin`,
  `Matrix.TotallyUnimodular`, `SimpleGraph.lapMatrix`.

## Statement (validated in Sage, 2×3·3×2 exact match)
For `A : m×n`, `B : n×m`, `m ≤ n`:
```
det (A * B) = ∑ S : {s : Finset n // s.card = card m},
                det (A.submatrix e.symm S.orderEmbOfFin) * det (B.submatrix S.orderEmbOfFin e.symm)
```
`e := Fintype.equivFin m`. Sorted-subset indexing on both minors ⇒ NO loose sign (Sage-confirmed).

## Progress
### ✅ Lemma A — `det_mul_eq_sum_submatrix` (PROVEN, sorry-free, compiles 7s)
```
det (A * B) = ∑ g : m → n, det (A.submatrix id g) * ∏ i, B (g i) i
```
The analytic core. Proof: `det_apply'` → `mul_apply` → `Fintype.prod_sum` (expand ∏∑ over
functions `g`) → `sum_comm` → per-`g` recognise the inner `∑_σ sign σ ∏ A (σ i) (g i)` as
`det (A.submatrix id g)` via `det_apply'` again; `prod_mul_distrib` + `ring`.

### ⏳ Remaining — the combinatorial regrouping (sorry)
Math FULLY derived + de-risked 2026-06-10 (below). Only the Lean fiber bijection is left.

**Fiber computation (DONE on paper).** Fix `S` (card k = card m), `φ_S := S.orderEmbOfFin`,
`g := φ_S ∘ π ∘ e` for `π : Perm (Fin k)`:
1. `det (A.submatrix id g) = sign π · det (A.submatrix e.symm φ_S)`.
   Key collapse: `A.submatrix id g = (A.submatrix e.symm φ_S).submatrix e (e.trans π)`; the two-equiv
   determinant twist `τ = e.symm.trans (e.trans π) = π` (since `e.symm.trans e = refl`), so
   `det_submatrix_equiv_self e` + `det_permute' π` give exactly `sign π · minorA(S)`.
2. `∑_π sign π · ∏_{i:m} B (g i) i`: reindex the product by `a = e i` ⇒ `∏_{a:Fin k} B (φ_S (π a)) (e.symm a)`,
   so `∑_π sign π · ∏_a B (φ_S (π a)) (e.symm a) = det (B.submatrix φ_S e.symm) = minorB(S)`.
   **The B-determinant emerges from summing the plain product over π weighted by the A-minor's sign.**
3. ⟹ `∑_{π : Perm (Fin k)} F (φ_S ∘ π ∘ e) = minorA(S) · minorB(S)`, where `F g := det(A.sub id g)·∏B`.

**The only Lean gap** = the global reindexing
```
∑ g : m → n, F g
  = ∑ g (injective), F g                       -- non-injective: A.submatrix id g has 2 equal cols,
                                                --   det = 0  (Matrix.det_zero_of_column_eq)
  = ∑ S, ∑ π : Perm (Fin k), F (φ_S ∘ π ∘ e)    -- bijection {g injective} ≃ Σ S, Perm (Fin k)
  = ∑ S, minorA(S) · minorB(S)                  -- step 3 above
```
Bijection maps: forward `(S, π) ↦ (fun j => φ_S (π (e j)))`; backward `g ↦ (image g, the perm)`.
~150 lines (`Finset.sum_bij'` or an explicit `Equiv`). Fiddly bits: `card (image g) = k` for injective
`g`, and inverting `orderEmbOfFin` to recover `π`. Cheap compiles (7s warm) ⇒ tractable in a focused pass.

## Target 2 — Matrix-Tree (Kirchhoff), after CB
- `lapMatrix = B Bᵀ` for oriented incidence `B`; reduced Laplacian `L₀`, `det L₀ = #spanning trees`.
- Cauchy–Binet on `L₀ = B₀ B₀ᵀ` ⇒ `det L₀ = ∑_S det(B₀_{·,S})²`; `det(B₀_{·,S}) ∈ {0,±1}`
  (`TotallyUnimodular`), `= ±1` iff `S` is a spanning tree ⇒ count.

## Status: Lemma A banked sorry-free. Regrouping = math done, Lean bijection pending (next focused pass).
