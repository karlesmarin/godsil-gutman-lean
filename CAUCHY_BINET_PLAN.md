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

## ⚠️ NOVELTY (wheel-checked 2026-06-10, post-proof)
- **NOT first Cauchy–Binet in Lean**: `facebookresearch/algebraic-combinatorics` (faabian fork,
  Grinberg-book formalization) has `CauchyBinet.cauchyBinet` complete (blueprint sect. 5.2 ✓).
  Different architecture (extractAlpha/extractBeta/constructSigma vs our cbPerm/fiber_sum).
- **Mathlib: still ABSENT; zero PRs ever mention Cauchy–Binet** (GitHub API search, total=0).
  Their project states no upstreaming plans. → our independent proof = the Mathlib-PR candidate.
  Honest claim: *first in Mathlib-scope, independent proof* — NOT "first in Lean".
- **Matrix-tree (Target 2): not found in ANY ITP** (Lean ecosystem, Isabelle AFP, Coq/Rocq,
  coq100 list; also absent from the faabian project). Strong-novelty target.

## ✅✅ STATUS: Cauchy–Binet PROVEN sorry-free 2026-06-10 (`det_mul_cauchyBinet`)
Whole `Ihara/CauchyBinet.lean` compiles clean (zero warnings); `#print axioms` = `propext,
Classical.choice, Quot.sound` (the 3 Mathlib-standard axioms). Pieces: `det_mul_eq_sum_submatrix`
(Lemma A) · `fiber_sum` · `card_image_eq` · `cbPerm` + `cbPerm_spec` · `image_Phi` · main.
The bijection went `Σ S, Perm (Fin k) → {g injective}` (`Finset.sum_bij`), so the only nontrivial
obligations were `inj` (via `image_Phi` + `orderEmbOfFin` injectivity, NO cbPerm reconstruction) and
`surj` (= `cbPerm_spec`).  **Next: Target 2 (Kirchhoff matrix-tree) + Mathlib PR packaging.**

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

## Target 2 — Matrix-Tree (Kirchhoff)

### ✅ Stone 1 (2026-06-10, `Ihara/OrientedIncidence.lean`, sorry-free, commit be19e30)
`SimpleGraph.orientedIncMatrix` (V × Sym2 V; +1 at sup endpoint, −1 at inf, orientation from
`LinearOrder V`) + `orientedIncMatrix_mul_transpose : N·Nᵀ = lapMatrix`. Mathlib has only the
UNORIENTED `incMatrix` (Gram = D+A) — the oriented def + D−A factorization are new; PR-able alone.

### ✅ Stone 2 (2026-06-10, `Ihara/MatrixTree.lean`, sorry-free, commit e64c3f9)
`reducedIncMatrix`/`reducedLapMatrix` (delete root `v₀`), `reducedLapMatrix_eq_mul_transpose`
(via `submatrix_mul` with bijective middle id), and **`det_reducedLapMatrix_eq_sum_sq`**:
`det L₀ = ∑_{S : (card V −1)-subsets of Sym2 V} det(N₀_S)²` (CB + `det_transpose`).
`LinearOrder (Sym2 V)` provided as a scoped instance, lex on `(inf, sup)` via `LinearOrder.lift'`.

### ✅✅ Stone 3 DONE 2026-06-10 (`Ihara/SpanningTreeMinor.lean`, commit e9e2fa1, sorry-free)
`sq_det_minor_eq_ite : det(N₀_S)² = if ↑S ⊆ G.edgeSet ∧ (fromEdgeSet ↑S).Connected then 1 else 0`
(+ the 3 case theorems). All axioms = 3 std, zero warnings. **Verification battery**: minor
expression syntactically identical to Stone 2 summand; Sage end-to-end 40 random graphs × ALL
(n−1)-subsets with the FAITHFUL model (zero columns at non-edges — the first sloppy model was
caught by the test, good): per-S det² == ite AND ∑ == det L₀ == #spanning trees. Loops s(v,v)
handled by case (a). Lean lessons: `set H` + hypotheses mentioning H ⇒ dependent-motive rewrite
failure (drop the `set`); beta-redex blocks `rw` (use `show`/explicit `have` types); `Fintype.sum_equiv`
+ `Finset.sum_subtype` + `sum_erase_add` for subtype↔univ sum transport.

### Original Stone 3 design (implemented as above): `det(N₀_S) = ±1` iff spanning tree, else `0`
**Design (Sage-validated 2026-06-10: 200 random trees + 158 non-tree (n−1)-edge graphs, all pass):**
- **(a) `S ⊄ edgeSet`** → zero column → `det_eq_zero_of_column_eq_zero`. Easy.
- **(b) `S ⊆ edges`, `|S| = n−1`, not a tree** → some connected component `C` of `(V,S)` misses
  `v₀`; the rows of `C` sum to 0 (every `S`-edge inside `C` hits +1 and −1; no edge leaves `C`)
  ⇒ det 0. Lean route: nontrivial `vecMul` kernel ⇒ det 0 (over a Field, or ℤ→ℚ cast).
- **(c) spanning tree** → TRIANGULARITY, no induction: each `u ≠ v₀` has a unique **parent edge**
  (first edge of the unique path `u → v₀`; `IsTree.existsUnique_path`); vertex↦parent-edge is a
  bijection `{v // v ≠ v₀} ≃ S`; recolumn the minor by it. Order rows by lex `(dist · v₀, ·)`
  (`LinearOrder.lift'`, injective 2nd component). Entry `(u, parentEdge w) ≠ 0` ⇒ `u ∈ e_w` ⇒
  `w = u` (diag, entry ±1) or `u = parent w` (`dist u < dist w`) ⇒ **lower-triangular** ⇒
  `Matrix.det_of_upperTriangular`-family gives `det = ∏ diag = ±1`. Needed sub-lemmas:
  parent well-defined + `dist (parent u) = dist u − 1` (tree paths are geodesics), bijectivity,
  entry analysis. Realistic ~300–500 lines + walk-API study. **Fresh-session grind.**
- Sign bookkeeping NOT needed (only `det² = 1` feeds Stone 4).

### ✅✅✅ Stone 4 DONE 2026-06-10 — KIRCHHOFF CLOSED (`Ihara/Kirchhoff.lean`, commit d30de99)
`det_reducedLapMatrix_eq_card_spanningTrees` sorry-free: over any integral domain,
det L₀ = #{(card V −1)-subsets S : ↑S ⊆ G.edgeSet ∧ (fromEdgeSet ↑S).IsTree}. Assembly =
Stone-2 sum + Stone-3 ite per S + `Finset.sum_boole`; connected↔tree via
`isTree_iff_connected_and_card` (helpers `card_ne_root_add_one`, `connected_fromEdgeSet_iff_isTree`).
Axioms = 3 std, zero warnings, full library build green (3074 jobs).

## ARC COMPLETE 2026-06-10 (one session): Cauchy–Binet → N·Nᵀ=L → reduced CB → dichotomy → Kirchhoff.
First ITP formalization of matrix-tree found in NO other proof assistant (wheel-checked).
**Next: paper (Paper-V, godsil series style) + Mathlib-PR packaging decision + push branch.**

## Status: Lemma A banked sorry-free. Regrouping = math done, Lean bijection pending (next focused pass).
