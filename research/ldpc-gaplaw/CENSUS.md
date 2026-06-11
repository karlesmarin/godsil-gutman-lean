# Short-cycle census of deployed LDPC codes via the trace-formula gap law

**Date**: 2026-06-11 · **Pipeline**: `census_pilot2.py` (Sage, `sage_pacemaker` container)
**Theory**: Part III matching↔Ihara bridge, `godsil-gutman-lean` (`Ihara/TraceFormula.lean`,
`Ihara/NbVanishing.lean`)

## Claim being applied

For a finite graph of girth `g`, the trace-formula gap law:

```
gap_k := tr(A^k) − p_k = tr(B^k)        for 1 ≤ k ≤ g+1   (sharp at g+2)
```

with `A` = adjacency, `B` = Hashimoto non-backtracking operator, `p_k` = power sums of
matching-polynomial roots. At `k = g` this counts the shortest cycles:
`c_g = (tr(A^g) − p_g)/(2g) = tr(B^g)/(2g)`.

**Certification status (honest):**
- `k < g` (both sides vanish): **PROVEN in Lean, sorry-free** — `Ihara/NbVanishing.lean`,
  commit `4fc9d2e` (Stone A). Axioms: the 3 standard.
- `k = g` (the census case): numerically locked on **all 12 064 connected cyclic graphs
  with 4–8 vertices** (`research/_tmp/gaplaw_sweep.py`: 0 violations, sharpness universal)
  — Stone B, formalization in progress. When Stone B lands the census below becomes
  theorem-backed end to end.

## The census — IEEE 802.11n (WiFi) LDPC codes, n = 648, z = 27

Tanner graphs from the standard's parity-check matrices (alist files derived from
IEEE 802.11n via `jeroenoverman/ECC-LDPC-application`). Three mutually independent routes:

- **R1** non-backtracking trace: `c_g = tr(B^g)/(2g)` (scipy sparse, no densification)
- **R2** gap law: `c_g = (tr(A^g) − p_g)/(2g)`, `p_4 = 2m₁²−4m₂`,
  `p_6 = 2m₁³−6m₁m₂+6m₃` (`m₃` by exact bipartite edge-deletion recursion)
- **R3** brute-force enumeration: codegree pairs (g=4) / VF2 subgraph search (g=6)

| Code (rate) | Tanner \|V\| | \|E\| | girth | **c_g (R1 = R2 = R3)** | Stone A zeros | time |
|---|---|---|---|---|---|---|
| 1/2 | 972 | 2376 | 6 | **3 942** hexagons | OK | 25 s |
| 2/3 | 864 | 2376 | 6 | **8 046** hexagons | OK | 26 s |
| 3/4 | 810 | 2376 | 4 | **54** squares | OK | 3 s |
| 5/6 | 756 | 2376 | 6 | **32 346** hexagons | OK | 45 s |

**All four codes: the three routes agree exactly.** The Lean-certified below-girth
zeros (`tr(B^k) = 0` for `k < g`) hold on all four deployed graphs, as the theorem demands.

## Engineering story the census tells

Short cycles in a Tanner graph degrade belief-propagation decoding (locally correlated
messages = the "rumor circling back" effect). The census quantifies the design trade-off
across rates at fixed n = 648:

- rate 1/2 → girth 6 with the fewest hexagons (3 942): the cleanest graph.
- rate 2/3 → still girth 6, hexagons double (8 046).
- rate 3/4 → girth COLLAPSES to 4 (54 squares — the most damaging cycles present).
- rate 5/6 → girth 6 recovered, but at the price of 32 346 hexagons: the designers
  traded the (worse) 4-cycles away for a large 6-cycle population.

## Honest scope

- Counting short cycles of LDPC codes is a solved engineering problem (Blake–Lin spectral
  counting; Karimi–Banihashemi message-passing and QC-aware methods — these count further,
  up to 2g−2, and faster on QC structure). We do NOT claim algorithmic novelty.
- The contribution is the **certification layer**: the counting identity backed by a
  machine-checked theorem (Stone A today; Stone B = the census case, in progress), absent
  from the literature (searched 2026-06-11: no Lean/Coq/ITP work on cycle counting for
  coding theory).
- Matrix provenance is third-party (standard-derived alists); structure cross-checked
  (QC z=27 block structure, degree profiles). A standards-grade census would re-derive
  H from IEEE 802.11n Annex F directly.

## Next steps

1. **Stone B** (k = g window) in Lean → census becomes fully theorem-backed.
2. **5G NR** (3GPP TS 38.212, BG1/BG2 with real lifting sizes) — the headline census.
3. Window extension k ≤ 2g−2 with correction terms (Blake–Lin genre) as new ITP targets.
