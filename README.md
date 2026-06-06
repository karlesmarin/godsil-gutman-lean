# The Path-Tree Program — Godsil–Gutman & Heilmann–Lieb in Lean 4

A machine-checked formalization, in **Lean 4 / Mathlib**, of two classical results
about the **matching polynomial** of a graph and the road between them, in two
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
tree/Plancherel side). With both endpoints now in Lean, a future Part II can
formalize the **graph trace formula** that fuses them.

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

godsil-gutman-lean{,-es}.{tex,pdf}   Paper I (EN / ES)
heilmann-lieb-lean{,-es}.{tex,pdf}   Paper II (EN / ES)
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
```

The papers are archived on Zenodo:
Part I [10.5281/zenodo.20517350](https://doi.org/10.5281/zenodo.20517350),
Part II [10.5281/zenodo.20561832](https://doi.org/10.5281/zenodo.20561832),
Ihara/Bass [10.5281/zenodo.20573120](https://doi.org/10.5281/zenodo.20573120).

## Author and license

**Carles Marín** (independent researcher, `karlesmarin@gmail.com`). The Lean
formalization was carried out with Claude (Anthropic) as an AI research instrument
under a build-as-oracle loop: the assistant proposed definitions and proofs, the
Lean kernel verified or rejected each, and all design decisions, mathematics and
claims are the author's responsibility. The kernel has the last word.

Licensed under the **Apache License 2.0** — see [`LICENSE`](LICENSE).
