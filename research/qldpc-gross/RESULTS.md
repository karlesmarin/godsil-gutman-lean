# Certified short-cycle census of a quantum LDPC code — proof of concept

**Date**: 2026-06-11 · **Pipeline**: `census_gross.py` (Sage) · **Theory**: Part VI gap law.

## The result

Applying the Part VI trace-formula gap law (the unchanged WiFi-census machinery) to the
**IBM "gross code" `[[144,12,12]]`** bivariate bicycle qLDPC (Bravyi et al., Nature 2024):
`l=12, m=6`, `A = x^3+y+y^2`, `B = y^3+x+x^2`, `HX = [A|B]`.

| Quantity | Value |
|---|---|
| Tanner graph of `HX` | `\|V\|=216`, `\|E\|=432`, `(6,3)`-biregular |
| girth `g` | **6** |
| `c_6` (shortest cycles), R1 = R2 = R3 | **144** |
| Stone A (`tr B^k=0`, `k<g`), Lean-certified | holds |

Three mutually independent routes agree: R1 non-backtracking trace `tr(B^6)/12`,
R2 gap law `(tr A^6 - p_6)/12`, R3 VF2 enumeration. `c_6 = 144 = ` the number of data qubits
(`12 x 12`) — likely an artifact of the code's `Z_12 x Z_6` Cayley symmetry.

## Novelty wheel-check (2026-06-11, honest)

- **The number `c_6=144` is not novel**: it is an exact computation any cycle-counting tool
  could produce. No source was found that states it, but that is not a contribution.
- **Short-cycle counting for qLDPC is occupied** (QC-aware enumeration up to `2g-2`,
  e.g. arXiv:2310.12556; girth analysis of quantum QC-LDPC). Faster than us; not our edge.
- **A certified / machine-checked short-cycle census for qLDPC was NOT found** — searches over
  Lean/Coq/formal-methods + qLDPC returned nothing. Lean-QEC (arXiv:2605.16523) certifies
  code *distance*, explicitly not girth/cycles/BP. The certified niche appears open.
  (Best-of-knowledge; a deeper wheel-check of the Error Correction Zoo and recent venues is
  still advisable before any "first" claim.)

## The deeper thread (higher ceiling than a certified count)

A 2025 result (arXiv:2511.13560) shows the **gross code's Tanner graph is a double cover** of
a smaller graph. Graph **covers are exactly the home of the Ihara zeta function** (Stark-Terras,
*Zeta functions of finite graphs and coverings*, 1996 — already cited in Part VI). The
non-backtracking operator `B` and the Ihara zeta we formalized are the natural language for
covers. So the promising direction is not "count cycles, certified" but **the covering
structure of bivariate bicycle codes through the certified Ihara/non-backtracking machinery**:
relating `tr B^k` of a BB code to that of its base graph via the covering, with the gap law
giving the short-cycle profile of the whole tower at once. This ties our formalized theory to
the *construction* of the codes, not just their measurement.

## Honest scope

- We reach the **shortest cycles** (girth-length), the entry-level BP diagnostic — **not**
  trapping/absorbing sets (the error-floor structures), which are harder and more valuable.
- This is the cheap level: identity certified in Lean (general) + per-code numbers in Sage,
  3-route cross-checked. The Lean-QEC standard is **per-code kernel-checked**; reaching it for
  a small BB code (feeding the exact Tanner graph into a Lean `gap law` evaluation) is the
  open level (a), and likely infeasible at `[[144,12,12]]` size without a reduction.

## Next steps

1. Extend the census across the BB family ([[72,12,6]], [[90,8,10]], [[288,12,18]]) — needs the
   exact polynomials from Bravyi et al. Table 3.
2. Develop the covering-graph / Ihara-zeta-of-covers thread (the real novelty candidate).
3. Attempt a Lean kernel-checked count for a small BB code (level (a)).
4. Deeper wheel-check before any publication / "first" claim.
