# Cauchy–Binet → Matrix-Tree in Lean — plan (scoped 2026-06-09)

## Why: novel, timeless, our edge (det machinery). A merged Mathlib PR = real standing.

## GATE result
- **Cauchy–Binet: ABSENT from Mathlib** (confirmed). → PR-able, fundamental, many downstream uses.
- **Matrix-tree (Kirchhoff): ABSENT.** Builds on Cauchy–Binet.
- Building blocks PRESENT: `Matrix.det_mul`, `Finset.powersetCard`, **`Matrix.TotallyUnimodular`**
  (incidence det-submatrix ∈ {0,±1} — big bonus for matrix-tree), `SimpleGraph.lapMatrix`
  (posSemidef, kernel=components), `SimpleGraph.incMatrix`.

## Target 1 — Cauchy–Binet
For `A : Matrix m n R`, `B : Matrix n m R`, `[Fintype m] [Fintype n] [DecidableEq n]`, `m ≤ n`
(`Fintype.card m ≤ Fintype.card n`):
```
det (A * B) = ∑ S ∈ (Finset.univ : Finset n).powersetCard (Fintype.card m),
                det (A.submatrix id (S-embedding)) * det (B.submatrix (S-embedding) id)
```
(handle S→Fin m via `S.orderIsoOfFin` / an equiv `Fin m ≃ ↥S`.)

### Proof steps
1. `det (A*B) = ∑_σ sgn σ ∏_i ∑_k A i k * B k (σ i)`  [Matrix.det_apply, Matrix.mul_apply]
2. expand ∏ over `∑_k` → `∑ (φ : m → n) ∏_i A i (φ i) * B (φ i) (σ i)`  [Finset.prod_sum]
3. swap order: `∑_φ (∏_i A i (φ i)) * (∑_σ sgn σ ∏_i B (φ i) (σ i))`
   inner sum `= det (B.submatrix φ id)`.
4. φ non-injective ⇒ det = 0 (two equal rows). Keep injective φ.
5. group injective φ by image set S (card m): each S contributes `det(A_{·,S}) det(B_{S,·})`
   via factoring φ = (sorted S) ∘ (perm), sgn bookkeeping.

Likely 100–200 lines. Mirrors the det expansions already done in `Ihara/MomentAssembly.lean` and
`Ihara/AdjugateDiagMinor.lean`.

## Target 2 — Matrix-Tree (Kirchhoff), after CB
- `lapMatrix = B Bᵀ` for oriented incidence `B` (degree − adjacency). [need oriented incidence]
- reduced Laplacian `L₀` (delete one row/col), `det L₀ = #spanning trees`.
- Cauchy–Binet on `L₀ = B₀ B₀ᵀ` ⇒ `det L₀ = ∑_S det(B₀_{·,S})²`, sum over edge-sets S of size n−1.
- `det(B₀_{·,S}) ∈ {0,±1}` (TotallyUnimodular), `= ±1` iff S is a spanning tree ⇒ count.

## Status: plan only. Execution = fresh focused session (iterative compile). Statement + strategy ready.
