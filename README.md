# The Path-Tree Program — Godsil–Gutman & Heilmann–Lieb in Lean 4

A machine-checked formalization, in **Lean 4 / Mathlib**, of classical results
about the **matching polynomial** of a graph and the road between them, in a series of
papers:

- **Paper I — *Random Signs into Matchings*** ([`godsil-gutman-lean.pdf`](godsil-gutman-lean.pdf)):
  the **Godsil–Gutman identity** — the average characteristic polynomial of a
  uniformly random `±1` signing of a graph is its **matching polynomial** — plus
  the first formalization of the matching polynomial and its deletion recurrence in
  any proof assistant, and the Bilu–Linial 2-lift decomposition.
- **Paper II — *Unfolding a Graph into a Tree*** ([`heilmann-lieb-lean.pdf`](heilmann-lieb-lean.pdf)):
  the **Heilmann–Lieb theorem** — `μ_G` is real-rooted, and for maximum degree
  `Δ ≥ 2` all its roots lie in the Ramanujan band `[−2√(Δ−1), 2√(Δ−1)]` — proved
  via Godsil's path tree, the divisibility `μ_G ∣ μ_{T(G,u)}`, the forest identity,
  and a weighted Gershgorin / Collatz–Wielandt argument.
- **Paper III — *Walks that Forget the Cycles*** ([`path-tree-walks-lean.pdf`](path-tree-walks-lean.pdf)):
  the **bijection** between the **tree-like walks** of a graph and the walks on Godsil's
  path tree (`card_treeLike_eq_pathTreeWalks`) — the *combinatorial half* of Godsil's
  **moment theorem** `p_k = Σ_i θ_i^k = treeLikeWalkCount` — together with the spectral
  form `treeLikeWalkCount = Σ_v [A(T(G,v))^k]_root` and the forest bridge `μ(T)=charpoly`.
  The same path tree of Paper II, taught to count walks. The spectral half was **mapped, not built**
  there — now built in Paper IV; `sorry`-free, three standard axioms.
- **Paper IV — *When Walks Become a Spectrum*** ([`moment-theorem-lean.pdf`](moment-theorem-lean.pdf)):
  the **spectral half** that closes Godsil's **moment theorem**
  `p_k = Σ_i θ_i^k = treeLikeWalkCount` (`matchingPowerSum_eq_treeLikeWalkCount`). Each path tree's
  root–root resolvent is folded through Paper II's `godsil_identity` into reversed matching
  polynomials; both the walk-count and the root-power-sum generating functions are forced to the same
  `reflect_n(X·μ')`, then a unit is cancelled. Needs **no** univariate Newton — a geometric-series /
  reversed-product cancellation replaces it. With the Bass companion, both sides of the finite
  matching/Ihara trace formula now stand `sorry`-free in one library. DOI
  [10.5281/zenodo.20613247](https://doi.org/10.5281/zenodo.20613247). EN + ES.
- **Paper V — *Counting Trees Without Listing Them*** ([`matrix-tree-lean.pdf`](matrix-tree-lean.pdf)):
  **Kirchhoff's matrix-tree theorem** `det L_0 = #spanning trees`
  (`det_reducedLapMatrix_eq_card_spanningTrees`), over any integral domain, assembled from a
  self-contained **Cauchy--Binet** (`det_mul_cauchyBinet`), the **oriented incidence matrix** and
  its Gram factorization `N*Nᵀ = D − A` (`orientedIncMatrix_mul_transpose`), the reduced
  sum-of-squared-minors expansion, and a spanning-tree **minor dichotomy** proved by sorting
  (parent edges + a distance key make the minor triangular) instead of leaf-deletion induction.
  To the best of our knowledge the **first machine-checked matrix-tree theorem in any proof
  assistant**. DOI [10.5281/zenodo.20629746](https://doi.org/10.5281/zenodo.20629746). EN + ES.
- **Paper VI — *The Walks That Remember the Cycles*** ([`gap-window-lean.pdf`](gap-window-lean.pdf)):
  the **sharp trace-formula gap law** `tr(Aᵏ) − p_k = tr(Bᵏ)` on the window `1 ≤ k ≤ g+1`
  (`trace_sub_matchingPowerSum_eq_trace_hashimoto`) — the first machine-checked **bridge** between
  the matching polynomial and the non-backtracking spectrum, fusing the tree side (Parts III–IV)
  and the Ihara/Bass companion in one file. Below the girth both sides vanish; at `k ∈ {g, g+1}`
  both count the `k`-cycles `2k·c_k`; sharp at `k = g+2`. `sorry`-free, three standard axioms.
  DOI [10.5281/zenodo.20648489](https://doi.org/10.5281/zenodo.20648489). EN + ES.
- **Applied companion — *Certified Short-Cycle Counts for the IEEE 802.11n (WiFi) LDPC Codes***
  ([`ldpc-census.pdf`](ldpc-census.pdf)): the gap law applied as a **certified census** of the
  shortest cycles of the four deployed WiFi LDPC codes (`n = 648`), cross-checked by three
  mutually independent routes (NB-trace, gap law, enumeration). EN + ES. *(Zenodo / TechRxiv
  forthcoming.)*

A companion strand formalizes the **Ihara side** of spectral graph theory:

- **Bass's determinant formula** ([`Ihara/Bass.lean`](Ihara/Bass.lean)): the
  **Ihara–Bass identity** `(1−u²)^|V| · det(I − uB) = (1−u²)^|E| · det(I − uA + u²(D−I))`,
  relating the non-backtracking (Hashimoto) operator `B` of a graph to its adjacency
  and degree matrices — the reciprocal of the Ihara zeta function. To our knowledge
  the **first machine-checked proof of Bass's formula in any proof assistant**. Proved
  over a field (the standard setting) via the orientation reindex
  `Dart ≃ Bool × {positive darts}`, `det(I + uJ) = (1−u²)^|E|`, and a Sylvester
  (Weinstein–Aronszajn) step. This is the natural counterpart to the matching
  polynomial: matching poly = the "tree/Plancherel" side, Ihara–Bass = the
  "cycle/π₁" side of the graph trace formula.

- **Jacobi's formula and Newton's identity** ([`Ihara/TraceFormula.lean`](Ihara/TraceFormula.lean)):
  `(det M)′ = tr(adj M · M′)` and the matricial Newton identity (`charpolyRev` log-derivative) —
  the resolvent / trace-generating-function machinery that maps `tr(Bᵏ)` to closed
  non-backtracking walk counts, used by Part VI. DOI
  [10.5281/zenodo.20578470](https://doi.org/10.5281/zenodo.20578470).

Each paper has an English and a Spanish edition (`*-es.pdf`). All headline theorems
are **`sorry`-free**: `#print axioms` reports only `propext`, `Classical.choice`,
`Quot.sound`.

> *Honesty note.* This is a formalization of classical mathematics; it proves no
> new theorem and claims none. The "first formalization" claim is supported by a
> search of the Lean/Mathlib, Isabelle/AFP and Coq/mathcomp ecosystems, not by an
> exhaustive byte-level audit.

## What is formalized

All theorems below are `sorry`-free (axioms: `propext`, `Classical.choice`,
`Quot.sound`).

### Paper I — Godsil–Gutman

| Lean name | Statement | File |
|---|---|---|
| `godsil_gutman` | `∑_cfg det(xI − A_cfg) = #cfg · μ_G` | `MSS/GodsilGutman.lean` |
| `matchingPoly` (+ infra) | `μ_G = ∑_k (−1)^k m_k x^{n−2k}` — first in any prover | `MatchingPoly.lean` |
| `matchingNumber_recurrence` | `m_{k+1}(G) = m_{k+1}(G−v) + ∑_{u∼v} m_k(G−v−u)` | `MatchingPoly.lean` |
| `charpoly_twoLift` | Bilu–Linial 2-lift charpoly factorization | `MSS/TwoLift.lean` |

### Paper II — Heilmann–Lieb (the path-tree route)

| Lean name | Statement | File |
|---|---|---|
| `matchingPoly_realRooted` | `μ_G` is real-rooted, every finite `G` | `MSS/ForestRealRooted.lean` |
| `matchingPoly_bounded` | roots of `μ_G` in `[−2√(Δ−1), 2√(Δ−1)]` (`2 ≤ Δ`, `deg ≤ Δ`) | `MSS/HeilmannLiebBound.lean` |
| `connected_matchingPoly_dvd_pathTree` | `μ_G ∣ μ_{T(G,u)}` (Godsil divisibility) | `MSS/ForestComponents.lean` |
| `matchingPoly_forest_eq_charpoly` | `μ_F = charpoly(A_F)` on a forest | `MSS/ForestRealRooted.lean` |
| `pathTree_isAcyclic` | the path tree `T(G,u)` is a forest | `MSS/PathTree.lean` |
| `collatzWielandt` | weighted Gershgorin eigenvalue bound | `MSS/HeilmannLiebBound.lean` |
| `forest_bounded_proof` | forest matching roots in the band | `MSS/HeilmannLiebBound.lean` |
| `forest_adj_dist_pm_one`, `forest_le_one_parent` | the two tree-distance facts | `MSS/HeilmannLiebBound.lean` |

The **full Heilmann–Lieb theorem** (both halves) is now machine-checked; what
Paper I listed as "future, mapped" is done. Still future: the
interlacing-families existence step and the signing/2-lift correspondence that
would yield a formalized proof that Ramanujan graphs exist (Paper II, Q1).

### Paper III — the path tree counts walks

The combinatorial half of Godsil's **moment theorem** `p_k = Σ_i θ_i^k = treeLikeWalkCount`.

| Lean name | Statement | File |
|---|---|---|
| `card_treeLike_eq_pathTreeWalks` | `#{tree-like walks of G at v} = #{walks at root of T(G,v)}` (the bijection) | `Ihara/MomentBridge.lean` |
| `treeLikeWalkCount_eq_sum_pathTree_adjMatrix_pow` | `treeLikeWalkCount G k = ∑_v [A(T(G,v))^k]_root` | `Ihara/MomentBridge.lean` |
| `matchingPoly_pathTree_eq_charpoly` | `μ(T(G,v)) = charpoly(A(T(G,v)))` (forest) | `Ihara/MomentBridge.lean` |
| `pathTreeProj_walk_injective`, `exists_root_lift` | the bijection's injective + surjective halves | `Ihara/MomentBridge.lean` |
| `liftSeq_map_invariant` | the `liftSeq`↔path-tree-vertex invariant | `Ihara/MomentBridge.lean` |
| `Walk.isTreeLike_of_acyclic` | acyclic edge-support ⇒ tree-like (path-tree definition) | `Ihara/PathTree.lean` |

The **spectral half** is **built** in Paper IV (below); the matrix-resolvent infrastructure
lives in `Ihara/TraceFormula.lean` and the Jacobi–Newton companion.

### Paper IV — the moment theorem (spectral half)

Closes Godsil's **moment theorem** `p_k = Σ_i θ_i^k = treeLikeWalkCount`.

| Lean name | Statement | File |
|---|---|---|
| `matchingPowerSum_eq_treeLikeWalkCount` | `p_k = Σ_i θ_i^k = treeLikeWalkCount` (the moment theorem) | `Ihara/MomentAssembly.lean` |
| `mk_matchingPowerSum_mul_reverse_eq` | the power-sum generating function forced to `reflect_n(X·μ′)` | `Ihara/MomentAssembly.lean` |
| `mk_treeLikeWalkCount_mul_reverse_eq` | the walk-count generating function forced to the same | `Ihara/MomentAssembly.lean` |
| `resolventGenfun_pathTree_mul_reverse_matchingPoly` | each path tree's root resolvent folded through `godsil_identity` | `Ihara/MomentAssembly.lean` |
| `matchingPowerSum_genfun` | generating function of the matching-root power sums | `Ihara/PowerSumGenfun.lean` |

No univariate Newton step: a geometric-series / reversed-product cancellation replaces it.

### Paper V — Kirchhoff's matrix-tree theorem

| Lean name | Statement | File |
|---|---|---|
| `det_reducedLapMatrix_eq_card_spanningTrees` | `det L₀ = #spanning trees`, over any integral domain | `Ihara/Kirchhoff.lean` |
| `det_mul_cauchyBinet` | the Cauchy–Binet formula (self-contained) | `Ihara/CauchyBinet.lean` |
| `orientedIncMatrix_mul_transpose` | `N·Nᵀ = D − A` (oriented-incidence Gram factorization) | `Ihara/OrientedIncidence.lean` |
| `reducedLapMatrix_eq_mul_transpose` | `L₀ = N₀ · N₀ᵀ` | `Ihara/MatrixTree.lean` |
| `det_reducedLapMatrix_eq_sum_sq` | reduced sum-of-squared-minors expansion | `Ihara/MatrixTree.lean` |

### Paper VI — the trace-formula gap law

`tr Aᵏ − p_k = tr Bᵏ` on the sharp window `1 ≤ k ≤ g+1`; both sides count `2k·c_k` at
`k ∈ {g, g+1}`; sharp at `k = g+2`. Fuses the tree side (Parts III–IV) and the Ihara/Bass
companion in one file.

| Lean name | Statement | File |
|---|---|---|
| `trace_sub_matchingPowerSum_eq_trace_hashimoto` | `tr Aᵏ − p_k = tr Bᵏ` on the window (over `ℂ`) | `Ihara/GapWindow.lean` |
| `treeLikeGap_eq_trace_hashimoto` | the capstone over `ℤ` (`treeLikeGap k = tr Bᵏ`) | `Ihara/GapWindow.lean` |
| `isCycle_of_nbChain_window` | window rigidity: a closed NB walk on the window is a cycle | `Ihara/GapWindow.lean` |
| `isCycle_or_isTreeLike_window` | the window dichotomy (cycle or tree-like) | `Ihara/GapWindow.lean` |
| `sum_card_not_treeLike_eq_sum_card_relWalks` | the bijection of censuses | `Ihara/GapWindow.lean` |
| `eq_of_darts_eq` | a walk is determined by its darts | `Ihara/GapWindow.lean` |
| `even_countP_edges_iff'` | closed-walk incidence parity, no trail hypothesis | `Ihara/GapWindow.lean` |
| `exists_isCycle_of_nbChain_of_not_nodup` | cycle extraction from a non-backtracking chain (Stone A) | `Ihara/NbVanishing.lean` |
| `trace_hashimoto_pow_eq_zero_of_lt_egirth` | `tr Bᵏ = 0` for `k < g` | `Ihara/NbVanishing.lean` |

### The Ihara side — Bass's determinant formula

`sorry`-free over a field (`#print axioms` = `propext`, `Classical.choice`,
`Quot.sound`).

| Lean name | Statement | File |
|---|---|---|
| `bass_determinant` | `(1−u²)^\|V\| · det(I − uB) = (1−u²)^\|E\| · det(I − uA + u²(D−I))` | `Ihara/Bass.lean` |
| `det_one_add_smul_reversal` | `det(I + uJ) = (1−u²)^\|E\|` (J = dart reversal) | `Ihara/Bass.lean` |
| `dartEquiv` | orientation reindex `Dart ≃ Bool × {positive darts}` | `Ihara/Bass.lean` |
| `hashimoto_eq` | `B = Tᵀ S − J` (non-backtracking operator) | `Ihara/Bass.lean` |
| `card_posDart` | `\|{positive darts}\| = \|E\|` | `Ihara/Bass.lean` |

`B` is Hashimoto's non-backtracking edge operator on the `2\|E\|` darts; `A`, `D`
the adjacency and degree matrices; `J` the reversal involution. The field
hypothesis is the standard Bass setting (the Sylvester step inverts `I + uJ`,
a unit exactly when `1 − u² ≠ 0`); the degenerate value `u² = 1` is handled by
the no-edge / empty-graph cases. Full `CommRing` generality would follow by a
universal-coefficient transfer, not pursued here.

This is the **Ihara/π₁ side** complementing the matching polynomial (the
tree/Plancherel side). With both endpoints in Lean, **Part VI** fuses them into the
trace-formula gap law.

### The Ihara side — Jacobi's formula and Newton's identity

The resolvent / trace-generating-function machinery that maps `tr(Bᵏ)` to closed
non-backtracking walk counts (used by Part VI).

| Lean name | Statement | File |
|---|---|---|
| `charpolyRev_logDeriv` | Newton's identity, matricial: the `charpolyRev` log-derivative as `Σ_k tr(Mᵏ) Xᵏ` | `Ihara/TraceFormula.lean` |
| `smul_resolventSeries_eq_adjugate` | Jacobi's-formula resolvent: `X·(I−XM)⁻¹` equals the adjugate series | `Ihara/TraceFormula.lean` |
| `trace_resolventSeries` | `tr((I−XM)⁻¹) = Σ_k tr(Mᵏ) Xᵏ` (trace generating function) | `Ihara/TraceFormula.lean` |
| `coe_charpolyRev_eq_det` | `charpolyRev M = det(I − X·M)` | `Ihara/ResolventDiag.lean` |
| `adjugate_diag_eq_det_submatrix_ne` | adjugate diagonal entry = principal minor | `Ihara/AdjugateDiagMinor.lean` |

## Repository layout

```
RealStable.lean             RealRooted / BoundedBy predicates + closure algebra
MatchingPoly.lean           matching polynomial μ_G, matching number, deletion recurrence
RamanujanBound.lean         the band edge 2√(k−1) (bruhatTitsBound) and its algebra
MSS/Basic.lean              signed adjacency matrix
MSS/ExpectedCharpoly.lean   the average (expected) characteristic polynomial
MSS/GodsilGutman.lean       the Godsil–Gutman identity + the ℤ/2 engine
MSS/TwoLift.lean            Bilu–Linial 2-lift spectral decomposition
MSS/MatchingSum.lean        matching-sum / permutation-expansion machinery
MSS/PathTree.lean           Godsil's path tree + acyclicity
MSS/Divisibility.lean       μ_G ∣ μ_{T(G,u)} (the divisibility brick)
MSS/ForestComponents.lean   connected divisibility + component decomposition
MSS/ForestRealRooted.lean   forest identity, T5/T6 real-rootedness
MSS/HeilmannLieb.lean       interlacing/geometric real-stability engine
MSS/HeilmannLiebBound.lean  the Ramanujan bound (Collatz–Wielandt + tree facts)
Ihara/Bass.lean             Bass's determinant formula for the Ihara zeta (Ihara side)
Ihara/PathTree.lean         path-tree-faithful tree-like predicate (liftSeq) + acyclic ⇒ tree-like
Ihara/TreeLikeWalks.lean    treeLikeWalkCount, the trace-formula gap, matchingPowerSum
Ihara/MomentBridge.lean     Paper III: the bijection tree-like walks ↔ path-tree walks

godsil-gutman-lean{,-es}.{tex,pdf}   Paper I (EN / ES)
heilmann-lieb-lean{,-es}.{tex,pdf}   Paper II (EN / ES)
path-tree-walks-lean{,-es}.{tex,pdf} Paper III (EN / ES)
references.bib                        bibliography
figures/                              figure scripts + PDFs + tables.tex (per paper)
```

## Building

Requires [`elan`](https://github.com/leanprover/elan). The toolchain is pinned in
`lean-toolchain` (`leanprover/lean4:v4.30.0-rc2`); Mathlib is pinned in
`lakefile.lean`.

```bash
lake exe cache get      # prebuilt Mathlib oleans (recommended)
lake build              # RealStable, MatchingPoly, RamanujanBound, MSS/*
```

Axiom footprint of the headline theorems:

```lean
import MSS.GodsilGutman
import MSS.HeilmannLiebBound
open SimpleGraph
#print axioms SimpleGraph.MSS.godsil_gutman          -- Paper I
#print axioms SimpleGraph.matchingPoly_realRooted     -- Paper II
#print axioms SimpleGraph.matchingPoly_bounded        -- Paper II
import Ihara.Bass
#print axioms SimpleGraph.bass_determinant            -- Ihara side
-- each: propext, Classical.choice, Quot.sound
```

## Figures and numerical cross-checks

Paper I figures: `figures/fig{1_godsil_gutman,2_ramanujan_bound,3_zmod2_principle,4_path_tree}.py`.
Paper II figures and SageMath cross-checks:
`figures/{hl_figures.py,hl_figures2.py,wallA_mss.py,wallA_squared.py}`.

## Citing

```bibtex
@misc{Marin2026GodsilGutmanLean,
  author = {Mar\'in, Carles},
  title  = {Random Signs into Matchings: A Godsil--Gutman Identity, Formalized in Lean 4},
  year   = {2026}, doi = {10.5281/zenodo.20517350},
  note   = {\url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
@misc{Marin2026HeilmannLiebLean,
  author = {Mar\'in, Carles},
  title  = {Unfolding a Graph into a Tree: A Machine-Checked Proof of the Heilmann--Lieb Theorem in Lean 4},
  year   = {2026}, doi = {10.5281/zenodo.20561832},
  note   = {\url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
@misc{Marin2026IharaBassLean,
  author = {Mar\'in, Carles},
  title  = {Folding Edges into Vertices: A Machine-Checked Proof of Bass's Determinant Formula for the Ihara Zeta Function in Lean 4},
  year   = {2026}, doi = {10.5281/zenodo.20573120},
  note   = {\url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
@misc{Marin2026PathTreeWalksLean,
  author = {Mar\'in, Carles},
  title  = {Walks that Forget the Cycles: A Machine-Checked Bijection between Tree-Like Walks and Godsil's Path Tree in Lean 4},
  year   = {2026}, doi = {10.5281/zenodo.20600326},
  note   = {\url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
@misc{Marin2026MomentTheoremLean,
  author = {Mar\'in, Carles},
  title  = {When Walks Become a Spectrum: A Machine-Checked Proof of Godsil's Moment Theorem in Lean 4},
  year   = {2026}, doi = {10.5281/zenodo.20613247},
  note   = {\url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
@misc{Marin2026MatrixTreeLean,
  author = {Mar\'in, Carles},
  title  = {Counting Trees Without Listing Them: A Machine-Checked Proof of Kirchhoff's Matrix-Tree Theorem in Lean 4},
  year   = {2026}, doi = {10.5281/zenodo.20629746},
  note   = {\url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
@misc{Marin2026JacobiNewtonLean,
  author = {Mar\'in, Carles},
  title  = {What a Determinant's Derivative Knows: Jacobi's Formula and Newton's Identity for Matrix Traces in Lean 4},
  year   = {2026}, doi = {10.5281/zenodo.20578470},
  note   = {\url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
@misc{Marin2026GapWindowLean,
  author = {Mar\'in, Carles},
  title  = {The Walks That Remember the Cycles: A Machine-Checked Sharp Gap Law between the Matching Polynomial and the Non-Backtracking Spectrum in Lean 4},
  year   = {2026}, doi = {10.5281/zenodo.20648489},
  note   = {Part VI. \url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
```

The papers are archived on Zenodo:
Part I [10.5281/zenodo.20517350](https://doi.org/10.5281/zenodo.20517350),
Part II [10.5281/zenodo.20561832](https://doi.org/10.5281/zenodo.20561832),
Ihara/Bass [10.5281/zenodo.20573120](https://doi.org/10.5281/zenodo.20573120),
Part III [10.5281/zenodo.20600326](https://doi.org/10.5281/zenodo.20600326),
Part IV [10.5281/zenodo.20613247](https://doi.org/10.5281/zenodo.20613247),
Part V [10.5281/zenodo.20629746](https://doi.org/10.5281/zenodo.20629746),
Jacobi–Newton [10.5281/zenodo.20578470](https://doi.org/10.5281/zenodo.20578470),
Part VI [10.5281/zenodo.20648489](https://doi.org/10.5281/zenodo.20648489).

## Author and license

**Carles Marín** (independent researcher, `karlesmarin@gmail.com`). The Lean
formalization was carried out with Claude (Anthropic) as an AI research instrument
under a build-as-oracle loop: the assistant proposed definitions and proofs, the
Lean kernel verified or rejected each, and all design decisions, mathematics and
claims are the author's responsibility. The kernel has the last word.

Licensed under the **Apache License 2.0** — see [`LICENSE`](LICENSE).
