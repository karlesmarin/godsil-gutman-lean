# Zenodo metadata draft — Part VI (theory paper)

Upload: `gap-window-lean.pdf` (EN, primary) + `gap-window-lean-es.pdf` (ES mirror).
Optional: a source zip of `Ihara/*.lean` + `research/_tmp/{traceformula_lock,gaplaw_sweep}.py`
(or rely on the GitHub related-identifier below).

---

**Resource type:** Publication → Preprint

**Title:**
The Walks That Remember the Cycles: a machine-checked sharp gap law between the matching
polynomial and the non-backtracking spectrum in Lean 4 (Part VI)

**Creators:**
- Carles Marin — ORCID 0009-0007-5637-9688 — Affiliation: Independent researcher

**Publication date:** 2026-06-11  (set to actual upload date)

**Language:** English (eng)  [ES mirror included as a second file]

**Version:** v1

**License:** Creative Commons Attribution 4.0 International (CC-BY-4.0)

**Description:**
A machine-checked, sorry-free proof, in Lean 4 over Mathlib, of the sharp trace-formula gap
law for a finite simple graph of girth g: for every 1 <= k <= g+1,

    tr(A^k) - p_k = tr(B^k),

where A is the adjacency matrix, B the Hashimoto non-backtracking operator, and p_k the power
sums of the roots of the matching polynomial. Below the girth both sides vanish; at
k in {g, g+1} both count the rooted traversals of the k-cycles, 2k*c_k; and the window is
sharp -- the law fails at k = g+2 on every graph tested, including all 12064 connected cyclic
graphs on 4 to 8 vertices. The contribution is the formalization: to the best of the author's
knowledge the first machine-checked bridge between the matching polynomial and the
non-backtracking spectrum in any proof assistant. The headline theorem depends only on the
three standard axioms (propext, Classical.choice, Quot.sound).

This is Part VI of the godsil-gutman-lean series. A companion applied paper applies the law,
as a certified census of short cycles, to the LDPC codes of the IEEE 802.11n (WiFi) standard.

Formalized with AI assistance (Claude, Anthropic); the mathematics and all claims are the
author's responsibility.

**Keywords:**
Lean 4; Mathlib; formal verification; interactive theorem proving; machine-checked proof;
matching polynomial; non-backtracking operator; Hashimoto matrix; Ihara zeta function;
trace formula; graph girth; closed walks; Godsil; algebraic graph theory

**Related/alternate identifiers:**
| Relation | Identifier | Resource type |
|---|---|---|
| isContinuationOf | 10.5281/zenodo.20629746  (Part V, Kirchhoff matrix-tree) | Publication |
| references | 10.5281/zenodo.20517350  (Part I, Godsil-Gutman / Ramanujan band) | Publication |
| references | 10.5281/zenodo.20573120  (Part III, Bass determinant formula) | Publication |
| references | 10.5281/zenodo.20578470  (Jacobi-Newton matrix traces) | Publication |
| references | 10.5281/zenodo.20613246  (Part IV, Godsil moment theorem) | Publication |
| references | 10.5281/zenodo.20561832  (Part II, Heilmann-Lieb / Unfolding a graph into a tree) | Publication |
| isSupplementedBy | https://github.com/karlesmarin/godsil-gutman-lean | Software |

(After the applied paper gets its own DOI, add: isReferencedBy -> <applied DOI>.)

**Notes:**
All theorems machine-checked sorry-free in Lean 4 over Mathlib (toolchain v4.30.0-rc2);
`#print axioms` on every load-bearing result reports only propext, Classical.choice,
Quot.sound. Build and check: `lake build Ihara`. Sharpness locked numerically on all 12064
connected cyclic graphs (4 <= n <= 8) and re-checked on six named graphs in exact arithmetic.

---

## Pre-upload checks
- Part II DOI resolved: 10.5281/zenodo.20561832 (verified 2026-06-11). All six prior series
  DOIs confirmed live. Paper bibliography titles corrected to match the published records
  (Parts I and II had drifted titles; III/IV/V had abbreviated subtitles).
- Part IV uses the concept DOI 10.5281/zenodo.20613246 (resolves to latest, v2 = 20617199).
- Community: add to a series/relevant Zenodo community if you maintain one.
