# Part II skeleton — "The Clock That Never Ticks: the coefficient side"

*Planning skeleton, 2026-06-13. Sequel to "The Clock That Never Ticks"
(Zenodo 10.5281/zenodo.20675270, Part I). Honest genre: formalization + synthesis +
observation — NO new mathematics. Same tier as Part I and the godsil series.*

## Working title (pick one)
- **"The Clock That Never Ticks, Part II: The Coefficient Side"**
- alt: "When a Quantum Clock Ticks — Eneström–Kakeya, the antipode floor, and the
  dilogarithm as Szegő's critical weight"

## The arc (why a sequel, not overlap)

Part I closed on two unanswered things, *quoted from its own text*:
- **Open road #4:** "Eneström–Kakeya, both as a formalization target and as the
  dictionary of Remark 7."
- **Question Q5:** "What is the correct functional of the spectral measure that *does*
  decide τ⊥ — and is the Eneström–Kakeya dictionary its shadow on monotone states?"

Part II answers both, machine-checked, and finds the organizing principle behind them
(Berg's Pick-function hierarchy) plus one clean observation (the dilogarithm is Szegő's
critical polylog weight). Part I was the **analytic / boundary-value** side (the
dilogarithm on the circle); Part II is the **coefficient / spectral-measure** side.

## The one-paragraph thesis

A quantum clock with populations `pₙ` on equally spaced levels orthogonalizes iff its
autocorrelation `S(t)=∑pₙe^{-int}` vanishes, i.e. iff the generating function `∑pₙzⁿ` has a
zero on `|z|=1`. The *coefficient structure* of `(pₙ)` decides this, in a clean hierarchy:
monotone (Eneström–Kakeya: zeros only on/outside the circle, on the circle only at roots
of unity) ⊃ completely monotone (an antipode floor: the modulus never drops below its
value at `z=−1`, so the clock never ticks). The floor `∑pₙ(−1)ⁿ` is the functional Q5
asked for. Read on the unit circle, a completely monotone clock *is* an OPUC measure whose
moments are its populations; the dilogarithm `s=2` clock is the **critical** polylog weight
— the largest `s` for which the Carathéodory function `1+(2/ζ(s))Li_s` has a positive
boundary measure — with Verblunsky coefficients `αₙ ~ (−1)ⁿ/n` forced by the density's
double zero at the antipode.

## Section skeleton (with Lean anchors + honest novelty tag)

### §0 Introduction — the clock, and what Part I left open
Recall `S(t)`, ticking = unit-circle zero. Quote road #4 + Q5. State the plan: the
coefficient side. *[narrative]*

### §1 The coefficient dictionary: monotone populations ↔ zeros
- Eneström–Kakeya, interior: no zero in `|z|<1`. `Dilog.enestrom_kakeya`.
- **Boundary refinement** (the new formalized content): a unit-circle zero ⟹ root of
  unity; decrements concentrate on an arithmetic progression. `Dilog.enestrom_kakeya_boundary`.
- Strict decrease ⟹ no zero on closed disc. `Dilog.enestrom_kakeya_strict`.
- Clock reading: `Dilog.monotoneState_never_orthogonal`.
- The dichotomy worked example: ML-sharp `½(1+z)` (ticks at `z=−1`) vs the zeta state
  (decrements at every index, never ticks).
*Novelty: E-K is 1893; the four theorems are (per June-2026 checks) the first ITP
formalization of E-K and its boundary case. First-ITP, not new math.*

### §2 The completely monotone floor — answering Q5
- `pₙ=∫₀¹ xⁿ dμ`, generating function `Φ(z)=∫ x/(1−xz)dμ` = Cauchy–Stieltjes /
  Carathéodory (Re Φ > 0).
- **Antipode floor:** `‖Φ(z)‖ ≥ Φ(−1) = ∑ⱼwⱼxⱼ/(1+xⱼ)` on `|z|=1`. `Dilog.antipode_floor`
  (finite form; proof at full Cauchy–Stieltjes generality).
- This is the Q5 functional: for CM states `τ⊥=∞`, floor `= |∑pₙ(−1)ⁿ|`. CM ⊂ monotone,
  gets the stronger conclusion — the E-K dictionary *is* its shadow (answer to Q5's second
  half).
- Corollary: zeta states, floor `η(s)/ζ(s)=1−2^{1−s}` (Euler factor at 2); `s=2` recovers
  Part I's Theorem.
*Novelty: classical (Herglotz + per-mode monotonicity), most plausibly folklore;
not found stated (Berg arXiv:1401.8052 has the Pick framework but not this min-modulus
statement). First-ITP form. Cite Berg, Carathéodory.*

### §3 The hierarchy behind it (Berg's Pick characterization)
- Berg: generating functions of moment sequences ↔ Pick functions positive on `(−∞,1)`.
- The ladder: monotone (E-K) → completely monotone (antipode floor) → convex-density
  moments (`(1−z)F₁'` Pick) → concave-density moments (`F₁'` Pick). Each rung a sharper
  statement about where/how `S(t)` dips.
- We formalize the first two rungs; the convex/concave rungs are flagged as open roads.
*Novelty: the organizing principle is Berg (classical); the QSL reading of the ladder is
the synthesis. No new math.*

### §4 Observation — the dilogarithm as Szegő's critical weight
- On the circle a CM clock is an **OPUC measure** with **moments = populations**:
  `c_k = pₖ = 1/(ζ(s)k^s)`.
- `s≤2 ⟺ 1+(2/ζ(s))Li_s` Carathéodory ⟺ Verblunsky `αₙ∈𝔻` (numerically: sharp blow-up of
  `max|αₙ|` past `s=2`).
- At the critical `s=2` (Bernoulli-parabola density `3(1−θ/π)²`, double zero at θ=π):
  `αₙ ~ (−1)ⁿ/n` — *forced* by Baxter's theorem (weight not strictly positive ⟹ Verblunsky
  not ℓ¹) and the Fisher–Hartwig / algebraic-singularity asymptotics
  (Martínez-Finkelshtein–McLaughlin–Saff). `α₀ = 1/ζ(2)=6/π²` exactly.
- The dilogarithm is the boundary of the polylog–OPUC family.
*Novelty: HONEST — all explained by mature OPUC theory (Simon's two volumes; Baxter;
Fisher–Hartwig). The specific polylog/zeta weight not found named, but a routine instance.
Recorded as an **observation/connection** in Part I's own "we record it as an observation"
style. NOT a theorem of ours. Cite Simon, Baxter, MFM-S.*

### §5 The boundary of the contribution (honest, à la Part I)
All mathematics classical: Eneström 1893, Kakeya 1912, Herglotz, Carathéodory, Berg 2014,
Szegő/Verblunsky/Baxter, Fisher–Hartwig. We claim no new theorem. Contributions:
(i) first-ITP formalization of E-K + boundary + the antipode floor (all sorry-free, 3 std
axioms); (ii) answering Part I's road #4 and Q5; (iii) the Berg-ladder organization and the
OPUC observation, recorded as synthesis. AI-assisted, kernel-checked, `#print axioms`.

### §6 Open roads
1. The convex/concave-density rungs of the Berg ladder, formalized.
2. The genuinely two-variable weight-4 object `J(a)=∫₀¹ln²(1+at)ln(1−t)dt/t` (from the
   gemini moment tower, H4): standalone reducibility = a symbol / `{2,2}`-coproduct
   question (Duhr); a tooling target.
3. A closed form (or sharp asymptotic constant) for the `s=2` Verblunsky `αₙ`.
4. The moment-tower keeper `∫₀^∞ xᵐg_a = m![ζ(m+2)−Li_{m+2}(−a)]` and its self-inverse-region
   geometry — an appendix or a note.
5. Sharp Mandelstam–Tamm / arbitrary-fidelity ML (carried over from Part I).

### Questions to take with you (one per section, none rhetorical)
- Q1 (dictionary). Is "root location of positive-coefficient series ↔ orthogonalizability"
  a genuine equivalence at every monotonicity level, or does it break above some rung?
- Q2 (floor). Is `Φ(−1)` the *unique* spectral functional deciding `τ⊥` on CM states, or
  one of a family?
- Q3 (hierarchy). What does each Berg rung *say* physically about the autocorrelation —
  is there a clock-interpretation of convex vs concave spectral density?
- Q4 (OPUC). The dilogarithm is the critical polylog weight. Critical *for what*, in
  dynamical terms — what changes in the clock exactly at `s=2`?
- Q5 (carryover). The two-variable `J(a)`: classical or genuinely Duhr-irreducible?

### Appendices
- Reproduce (clone, `lake build Dilog`, figure scripts).
- Lean inventory table (Enestrom.lean, AntipodeFloor.lean + the Part-I Dilog/QSL files
  this builds on).

## Decisions to make with Carles before writing prose
1. Scope: §1–§4 + boundary + roads, or trim §4 (OPUC) to a remark?
2. EN+ES both (Part I had both)?
3. Venue: Zenodo as a Part II (concept-DOI sibling of Part I), per the series pattern.
4. Figures: the dichotomy plot (ML-sharp vs zeta), the Berg ladder schematic, the
   `max|αₙ|` blow-up at `s=2`, the Verblunsky `(−1)ⁿ/n` decay.

## Honest one-line summary
A sequel that answers its predecessor's own open questions with two first-in-ITP
formalizations (Eneström–Kakeya + the antipode floor) and assembles a classical but
(as far as we found) unstated dictionary — monotonicity of populations ↔ orthogonalization
of the clock — with the dilogarithm sitting at the Szegő-critical point. Synthesis and
formalization, not discovery.
