# Random Signs into Matchings — Godsil–Gutman in Lean 4

A machine-checked formalization, in **Lean 4 / Mathlib**, of the **Godsil–Gutman
identity**: the average characteristic polynomial of a uniformly random `±1`
signing of a graph is its **matching polynomial**. Along the way it provides the
first formalization of the matching polynomial and its deletion recurrence in any
proof assistant, isolates the `ℤ/2` sign-averaging fact that makes the proof
work, and formalizes the Bilu–Linial 2-lift spectral decomposition that bridges
the result to Ramanujan graphs.

The accompanying paper is **[`godsil-gutman-lean.pdf`](godsil-gutman-lean.pdf)**
(source `godsil-gutman-lean.tex`).

> This is a *pearl*, not a landmark. The headline theorems are `sorry`-free; the
> deep half of the Marcus–Spielman–Srivastava program (Heilmann–Lieb
> real-rootedness, interlacing families) is **mapped, not formalized** — see
> *Scope* below.

## What is formalized

All theorems below are `sorry`-free. `#print axioms` reports only the three
standard Mathlib axioms: `propext`, `Classical.choice`, `Quot.sound`.

| Lean name | Statement | File |
|---|---|---|
| `godsil_gutman` | `∑_cfg det(xI − A_cfg) = #cfg · μ_G` (average charpoly = matching polynomial) | `MSS/GodsilGutman.lean` |
| `matchingPoly` (+ infra) | `μ_G = ∑_k (−1)^k m_k x^{n−2k}` — first in any prover | `MatchingPoly.lean` |
| `matchingNumber_recurrence` | `m_{k+1}(G) = m_{k+1}(G−v) + ∑_{u∼v} m_k(G−v−u)` | `MatchingPoly.lean` |
| `charpoly_twoLift` | `det(xI − [[B,C],[C,B]]) = det(xI−(B+C))·det(xI−(B−C))` (Bilu–Linial) | `MSS/TwoLift.lean` |
| `signAvg_ne_zero_iff` | a sign-monomial survives the `±1` average ⟺ every multiplicity is even | `MSS/GodsilGutman.lean` |
| `sum_signOf_prod_pow` | the `ℤ/2` parity-projection kernel (moment level) | `MSS/GodsilGutman.lean` |

## Scope (done vs. future)

**Done (and checked):** Godsil–Gutman; the matching polynomial and its deletion
recurrence; the `ℤ/2` sign-averaging engine and its two consumers
(characteristic-polynomial level = Godsil–Gutman, moment level =
parity-closed-walk kernel of Chen–van Dam–Bu); the Bilu–Linial 2-lift charpoly
factorization.

**Future (mapped, not formalized):** Heilmann–Lieb — `roots(μ_G) ⊆
[−2√(Δ−1), 2√(Δ−1)]` — via Godsil's path-tree; and the interlacing-families step.
The paper (§"The next stone") documents the proposed path-tree route in detail.
`RealStable.lean` contains exploratory real-rootedness infrastructure toward that
step; it is `sorry`-free but the Heilmann–Lieb *bound* itself is not yet a theorem.

## Repository layout

```
MatchingPoly.lean        matching polynomial μ_G, matching number, deletion recurrence
RealStable.lean          RealRooted predicate + closure algebra + Interlaces (toward Heilmann–Lieb)
MSS/Basic.lean           signed adjacency matrix
MSS/ExpectedCharpoly.lean   the average (expected) characteristic polynomial
MSS/GodsilGutman.lean    the Godsil–Gutman identity + the ℤ/2 engine
MSS/TwoLift.lean         Bilu–Linial 2-lift spectral decomposition (pure-matrix form)

godsil-gutman-lean.tex   the paper (source)
godsil-gutman-lean.pdf   the paper (compiled)
references.bib           bibliography
figures/                 figure scripts (matplotlib/sympy/networkx) + PDFs/PNGs + tables.tex
```

## Building the Lean code

Requires [`elan`](https://github.com/leanprover/elan) (Lean toolchain manager).
The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.30.0-rc2`) and
Mathlib is pinned in `lakefile.lean` to a specific revision.

```bash
lake exe cache get      # download prebuilt Mathlib oleans (recommended)
lake build              # build RealStable, MatchingPoly, and MSS/*
```

To inspect the axiom footprint of the headline theorem:

```lean
import MSS.GodsilGutman
#print axioms SimpleGraph.MSS.godsil_gutman
-- propext, Classical.choice, Quot.sound
```

## Reproducing the figures and tables

```bash
cd figures
python fig1_godsil_gutman.py     # Godsil–Gutman on K3
python fig2_ramanujan_bound.py   # Heilmann–Lieb Ramanujan band
python fig3_zmod2_principle.py   # the ℤ/2 engine dependency
python fig4_path_tree.py         # Godsil's path-tree (the proposed next step)
```

Each writes a `.pdf` and a 300-dpi `.png`. Requires `matplotlib`, `sympy`,
`networkx`. The numerical cross-checks in the paper's Table 2 are exact (SymPy).
`figures/README.md` documents the honesty notes baked into each asset.

## Citing

If you use this development, please cite the paper (preprint, June 2026):

```bibtex
@misc{Marin2026GodsilGutmanLean,
  author = {Mar\'in, Carles},
  title  = {Random Signs into Matchings: A Godsil--Gutman Identity, Formalized in Lean 4},
  year   = {2026},
  doi    = {10.5281/zenodo.20517350},
  note   = {Lean 4 formalization (English + Spanish editions), \url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
```

Archived on Zenodo: [10.5281/zenodo.20517350](https://doi.org/10.5281/zenodo.20517350).
The paper is included in English (`godsil-gutman-lean.pdf`) and Spanish
(`godsil-gutman-lean-es.pdf`).

## Author and license

**Carles Marín** (independent researcher, `karlesmarin@gmail.com`).

The Lean formalization was carried out with Claude (Anthropic) as an AI research
instrument; all design decisions, mathematics, and claims are the author's
responsibility. A build-as-oracle loop verified or rejected each lemma against
the Lean kernel, which has the last word.

Licensed under the **Apache License 2.0** — see [`LICENSE`](LICENSE).
