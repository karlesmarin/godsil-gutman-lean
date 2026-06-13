# The antipode floor for completely monotone states

*Research note, 2026-06-13. Spun out of "The Clock That Never Ticks" (Zenodo
10.5281/zenodo.20675270). Generalizes that paper's Theorem 4 (the weight-2 zeta state)
to the whole completely-monotone family, with a short proof.*

## Statement

> **Theorem (antipode floor).** Let `(pₙ)_{n≥1}` be a completely monotone sequence,
> i.e. `pₙ = ∫₀¹ xⁿ dα(x)` for a positive measure α on `[0,1)` with `Σ pₙ < ∞`.
> Then its generating function `W(z) = Σ_{n≥1} pₙ zⁿ` satisfies
>
>   `min_{|z|=1} |W(z)| = |W(−1)| = |Σ_{n≥1} (−1)ⁿ pₙ|`,
>
> attained at `z = −1`.

## Proof (four steps)

1. **Factor out the zero.** `W(0)=0`, so `W(z) = z·Φ(z)` with
   `Φ(z) = Σ_{n≥1} pₙ z^{n−1} = ∫₀¹ x/(1−xz) dα(x)`. On `|z|=1`, `|W| = |Φ|`.

2. **Φ has positive real part.** For `z = e^{iθ}`,
   `Re Φ(e^{iθ}) = ∫₀¹ rₓ(θ) dα(x)`, where
   `rₓ(θ) = x(1 − x cosθ)/(1 − 2x cosθ + x²) > 0` for `x ∈ [0,1)`.
   (So Φ is, up to normalization, a Carathéodory/Herglotz function.)

3. **Each mode's real part is monotone in cosθ.** Writing `c = cosθ`,
   `d rₓ/dc = x²(1 − x²)/(1 − 2xc + x²)² > 0`.
   Hence `rₓ` is minimized at `c = −1` (θ = π), with `rₓ(π) = x/(1+x)`. Therefore
   `Re Φ(θ) ≥ ∫₀¹ x/(1+x) dα = Φ(−1)` for every θ.

4. **Close with `|·| ≥ Re`.** `|Φ(θ)| ≥ Re Φ(θ) ≥ Φ(−1) = |Φ(−1)|`, the last equality
   because `Φ(−1)` is real and positive. Equality holds at θ = π. ∎

## Why the non-completely-monotone cases escape

The proof uses positivity of α in step 2. Sequences that are positive and (even
strictly) decreasing but **not** completely monotone — e.g. the constant `(1,1,1,…)`
(an Eneström–Kakeya equality case, with a genuine zero at a cube root of unity), or a
decrement-spiked profile like `(1, .99, .98, .01)` — fail exactly there: their
generating functions vanish, or are minimized, at roots of unity other than `−1`. So
the dichotomy is clean:

* **completely monotone** → minimum modulus at the antipode `z = −1`, equal to the
  alternating sum; the state **never orthogonalizes**.
* **Eneström–Kakeya equality** (decrements concentrated on an arithmetic progression of
  order `d > 2`) → a zero at a `d`-th root of unity; the state **does** orthogonalize.

## Corollary — the weight-`s` zeta states

For `pₙ = 1/(nˢ ζ(s))` (completely monotone for every `s > 1`):

   `min_{|z|=1} |W(z)| = η(s)/ζ(s) = 1 − 2^{1−s}`,

attained at `z = −1` (i.e. θ = π in time). The floor is the **Euler factor at the prime
2** stripped from ζ. For `s = 2` this is `1/2` — recovering Theorem 4 of *The Clock That
Never Ticks*. So **no weight-`s` zeta state ever orthogonalizes** (resolving the H1
question), and the published `s = 2` result is one member of a one-parameter family.

A separate, finer fact (verified numerically, not used above): the Carathéodory function
`F_s(z) = 1 + (2/ζ(s)) Li_s(z)` is a genuine positive-measure (OPUC) Carathéodory
function **iff `s ≤ 2`**, with `Re F_s(−1) = 2^{2−s} − 1`; at the critical weight `s = 2`
the spectral density is the Bernoulli parabola `3(1 − θ/π)²`, vanishing to second order
at θ = π. The dilogarithm is the boundary of the polylog-OPUC family.

## Status / honesty

* **Proof:** elementary; verified numerically — `min|W| = |alternating sum|` on eight
  exact (non-truncated) completely-monotone families, and step 3's `min Re Φ = Φ(−1)`
  at θ = π.
* **Literature:** searched the completely-monotone / Hausdorff-moment, Markov/Cauchy-
  transform, Nevanlinna, Kaluza, absolutely-monotonic, and Herglotz/Carathéodory
  literatures (June 2026) and did **not** find this minimum-modulus statement named. The
  ingredients (Herglotz positive real part + an elementary per-mode monotonicity) are
  entirely classical, so it is most plausibly **folklore or a known exercise**; no strong
  novelty is claimed. The contribution, if any, is the clean assembly and its tie to the
  quantum-speed-limit reading.
* **Formalization:** the four steps are Mathlib-shaped (positivity of an integral, one
  derivative sign, `Complex.re_le_abs`). The obstacle is the completely-monotone ⟺
  Hausdorff-moment representation, which Mathlib does not appear to carry; a scoped Lean
  target is the polylog specialization, where `Φ` can be handled without the general
  moment theorem.

## Earlier mistakes recorded (so they are not repeated)

* "Positive + monotone ⇒ minimum at `−1`" is **false** (constant and spiked
  counterexamples). The right hypothesis is complete monotonicity.
* A first "phase-coherence" intuition for the mechanism was **backwards**: at the
  antipode each mode is at its individual modulus *minimum* (not a coherence maximum);
  the correct mechanism is the monotonicity of `Re Φ` in `cosθ`.
