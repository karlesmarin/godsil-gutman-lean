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
  DOI [10.5281/zenodo.20648488](https://doi.org/10.5281/zenodo.20648488) (concept, latest version). EN + ES.
- **Applied companion — *Certified Short-Cycle Counts for the IEEE 802.11n (WiFi) LDPC Codes***
  ([`ldpc-census.pdf`](ldpc-census.pdf)): the gap law applied as a **certified census** of the
  shortest cycles of the four deployed WiFi LDPC codes (`n = 648`), cross-checked by three
  mutually independent routes (NB-trace, gap law, enumeration). EN + ES.
  DOI [10.5281/zenodo.20649056](https://doi.org/10.5281/zenodo.20649056).

> **From theory to technology.** Papers I–VI are pure formalized mathematics: a
> machine-checked trace-formula gap law, proved `sorry`-free in Lean 4. The **applied
> companion is the technological payoff of that theory** — the point where the abstract
> identity `tr Aᵏ − p_k = tr Bᵏ` becomes a concrete engineering tool. At `k = g` the law is a
> formula for the number of shortest cycles, `c_g = (tr A^g − p_g)/2g = tr B^g/2g`; short
> cycles in a Tanner graph are what degrade the belief-propagation decoder of an LDPC code.
> So the same theorem that is a line of Lean becomes a **certified diagnostic of the LDPC
> codes a WiFi chip actually runs** (IEEE 802.11n, n = 648): a short-cycle census whose
> defining identity carries a machine-checked proof, cross-checked three independent ways.
> The mathematics did not change on the way out; it acquired a use. The same pipeline targets
> 5G NR and quantum LDPC codes next.

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

A second, **independent strand** (different subject area, same repository) formalizes the
**real dilogarithm and quantum speed limits**:

- **The Clock That Never Ticks** ([`clock-never-ticks.pdf`](clock-never-ticks.pdf)):
  a `sorry`-free development (∼1 500 lines) that fills a hole in Mathlib — the dilogarithm
  `Li₂` the library cites but does not define — and follows it to a quantum-mechanics
  ending. To the best of our knowledge the first formalization in any proof assistant of:
  the real dilogarithm with Euler's reflection, Landen's transformation and the duplication
  formula; the golden-ratio ladder `Li₂(1/φ²) = π²/15 − ln²φ` (from a 3×3 linear system, no
  five-term relation) and the Lee–Yang effective central charge `c_eff = 2/5`; the Clausen
  function `Cl₂` and Catalan's constant `G = Cl₂(π/2)`; the Fejér–Jackson inequality; the
  bound `Cl₂(θ) ≥ sin(θ)/2`; and the Margolus–Levitin and (an `L¹` form of the)
  Mandelstam–Tamm quantum speed limits. They assemble into the title theorem: the weight-2
  zeta state (populations `∝ 1/n²` on equally spaced levels) has infinite mean energy and
  infinite variance — both textbook speed limits say nothing — yet never reaches an
  orthogonal state, because its autocorrelation is `(6/π²)·Li₂(e^{−iθ})` and the dilogarithm
  has no zero on the unit circle. EN + ES. DOI
  [10.5281/zenodo.20675270](https://doi.org/10.5281/zenodo.20675270) (concept, latest version).
  A follow-on development (`Dilog/ComplexBoundary.lean`) extends this to the **complex**
  dilogarithm and begins the machine-checked **localization of its zeros** (O'Sullivan,
  arXiv:1507.07980) — the same `Cl₂ > 0` that powers the clock now places the dilogarithm's
  zeros inside the unit circle.

- **The Pentagon, Machine-Checked** ([`five-term-lean.pdf`](five-term-lean.pdf)): the sequel
  to *The Clock That Never Ticks*. A `sorry`-free proof (`Dilog/FiveTerm.lean`, 243 lines on
  the dilogarithm built there) of **Abel's five-term relation**
  `L(x) + L(y) = L(xy) + L(x(1−y)/(1−xy)) + L(y(1−x)/(1−xy))` for the Rogers `L`-function —
  the generator of the whole weight-2 theory: by Wojtkowiak and de Jeu every rational
  functional equation of `Li₂` follows from it, and it is the defining relation of the Bloch
  group and the pentagon of cluster algebras and of the quantum dilogarithm. The Clock paper
  climbed the golden ladder *without* it; this closes that thread. The proof is the classical
  one made rigorous: vanishing derivative (nine logs collapse to a basis of five) → constant
  → boundary value. EN + ES. DOI
  [10.5281/zenodo.20682715](https://doi.org/10.5281/zenodo.20682715) (concept, latest version).

A third strand formalizes the **real-rooted ⇒ log-concave** bridge that underlies the
matching polynomial (Paper II) and much of modern combinatorics:

- **The Inward Bow of a Real-Rooted Polynomial** ([`newton-inequalities-lean.pdf`](newton-inequalities-lean.pdf)):
  **Newton's inequalities** (1707) — if a real polynomial of degree `n` has all real roots, its
  elementary symmetric functions obey `e_k² · C(n,k−1)C(n,k+1) ≥ e_{k−1}e_{k+1} · C(n,k)²`, i.e.
  the normalized means `p_k = e_k/C(n,k)` are **log-concave**. The classical differentiate–reverse
  reduction made fully rigorous: real-rootedness survives differentiation (Rolle) and reversal
  (`x ↦ 1/x`), so a few derivatives and one reversal collapse each index to a real-rooted
  **quadratic**, whose discriminant `b²−4ac ≥ 0` *is* the inequality once positive factorials are
  cleared. To our knowledge the **first machine-checked Newton's inequalities in any proof
  assistant** (`Newton.lean`); the symmetric-function form is checked for monic polynomials (no
  loss; the coefficient form needs no normalization). EN + ES. DOI
  [10.5281/zenodo.20693064](https://doi.org/10.5281/zenodo.20693064).
- **The Staircase of Signs** ([`sturm-lean.pdf`](sturm-lean.pdf)): **Sturm's theorem** (1829) — for
  a squarefree `p` with `p(a), p(b) ≠ 0`, the number of *distinct* real roots in `(a, b]` is
  `V(a) − V(b)`, the drop in sign variations of the **Sturm sequence** `p, p′, −(p mod p′), …`. No
  root is ever located; two integers are subtracted. The per-point quantum (`ΔV ∈ {0,1}`) is
  decoupled from the chain's algebra by an inductive **flank-reduction** relation (`FlankReduce`),
  then summed over the finite critical set. To our knowledge the **first Sturm's theorem in Lean**
  (not first in any system — prior work in Coq, Isabelle/HOL and HOL Light) (`Sturm.lean`,
  `sorry`-free, three standard axioms). By-product: the sign-variation count here is, by `rfl`,
  Mathlib's Descartes `signVariations`. EN + ES. DOI
  [10.5281/zenodo.20707348](https://doi.org/10.5281/zenodo.20707348).

- **Counting with the Derivative Tower** ([`budan-fourier-lean.pdf`](budan-fourier-lean.pdf)): the
  **Budan–Fourier theorem** — for `p(a), p(b) ≠ 0`, the number of real roots in `(a, b]` *with
  multiplicity* is at most `V(a) − V(b)`, the drop in sign variations of the **derivative tower**
  `p, p′, p″, …`, and the difference is **even**. The same engine as Sturm, but its local analysis
  must resolve a whole **vanishing block** of the tower at once (the tower is not a coprime/Sturm
  chain at a multiple root), handled by the `Rseq`/`Lseq` block law. The `b → ∞` shadow is Descartes'
  rule, reached via `fourierVar p 0 = Polynomial.signVariations p` (`Descartes.lean`). To our
  knowledge the **first Budan–Fourier theorem in Lean** (not first in any system — prior Isabelle/HOL
  by W. Li) (`BudanFourier.lean`, `sorry`-free, three standard axioms). EN + ES. DOI
  [10.5281/zenodo.20736143](https://doi.org/10.5281/zenodo.20736143).

- **Roots That Are Always There** ([`virtual-roots-lean.pdf`](virtual-roots-lean.pdf)): the **virtual
  roots** of a real polynomial (González-Vega–Lombardi–Mahé; Coste) — a degree-`d` polynomial always
  has exactly `d` virtual roots `ρ_{d,1} ≤ … ≤ ρ_{d,d}`, continuous semialgebraic substitutes that
  coincide with the real roots when these exist and otherwise sit where the polynomial comes closest to
  vanishing. The `ℛ_d` construction, count `= deg`, sortedness, the **Rolle interlacing**
  `ρ_{d,r}(p) ≤ ρ_{d−1,r}(p′) ≤ ρ_{d,r+1}(p)`, and the **exact Budan–Fourier count**
  `#{virtual roots in (a,b]} = V(a) − V(b)` (`card_vroots_Ioc_eq_fourierVar`) that turns the
  Budan–Fourier *inequality* into an *equality*. To our knowledge the **first virtual roots — and this
  exact count — in any interactive theorem prover** (`VirtualRoots.lean`, `VirtualRootsCount.lean`,
  `sorry`-free, three standard axioms). EN + ES. DOI
  [10.5281/zenodo.20736336](https://doi.org/10.5281/zenodo.20736336).
- **One Engine, Three Counts** ([`sign-variation-lean.pdf`](sign-variation-lean.pdf)): a synthesis
  note — Descartes, Sturm and Budan–Fourier run through **one** sign-variation engine and **one**
  local-drop law `V(c⁻) = V(c⁺) + μ_c + 2e`; it locates the exact axiom where the derivative tower
  leaves the Sturm-chain world (the tower is not a Sturm chain at a multiple root) and ties the
  engine's `V(0)` to Mathlib's Descartes count via `fourierVar p 0 = Polynomial.signVariations p`
  (`Descartes.lean`). A companion note to the Budan–Fourier paper. EN + ES. DOI *(on publication)*.

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

### The dilogarithm and quantum speed limits — *The Clock That Never Ticks*

An independent strand (`Dilog/`, `QSL/`), `sorry`-free (axioms: `propext`,
`Classical.choice`, `Quot.sound`).

| Lean name | Statement | File |
|---|---|---|
| `Li2_add_Li2_one_sub` | Euler reflection `Li₂(x)+Li₂(1−x) = π²/6 − ln x·ln(1−x)` | `Dilog/Basic.lean` |
| `Li2_landen`, `Li2_sq`, `Li2_one_half` | Landen transformation, duplication, `Li₂(½)` | `Dilog/Basic.lean` |
| `rogersL_inv_goldenRatio_sq`, `rogersL_gold_sum` | golden ladder + Rogers `L`, Lee–Yang `c_eff = 2/5` | `Dilog/Basic.lean` |
| `catalanConst`, `Cl₂_pi_div_two` | Clausen function `Cl₂`, Catalan's constant `G = Cl₂(π/2)` | `Dilog/Clausen.lean` |
| `Cl₂_pos` | `Cl₂(θ) ≥ sin(θ)/2 > 0` on `(0,π)` (asymptotics-free Abel) | `Dilog/Clausen.lean` |
| `zetaState_never_orthogonal` | the weight-2 zeta state never reaches orthogonality | `Dilog/Clausen.lean` |
| `fejerSum_pos` | Fejér–Jackson `Σ_{k=1}^M sin(kθ)/k > 0` on `(0,π)` | `Dilog/FejerJackson.lean` |
| `margolus_levitin` | `π ≤ 2⟨E⟩τ` at orthogonality — first QSL in any prover | `QSL/Basic.lean` |
| `mandelstam_tamm_L1` | `1 ≤ D₁τ` (`L¹` Mandelstam–Tamm) | `QSL/MandelstamTamm.lean` |

### Complex dilogarithm and zero localization (`Dilog/ComplexBoundary.lean`)

A development towards machine-checked **localization of the zeros of the dilogarithm**
(O'Sullivan, *Zeros of the dilogarithm*, arXiv:1507.07980), built on the real `Cl₂` /
Bernoulli-parabola machinery above. To the best of our knowledge (search of the
Lean/Mathlib, Isabelle/AFP and Coq ecosystems, June 2026) the complex dilogarithm and its
zeros are absent from every proof assistant. `sorry`-free; three standard axioms.

| Lean name | Statement | Phase |
|---|---|---|
| `Li₂c` | the complex dilogarithm `∑ zⁿ/n²`, summable on the closed unit disk | 1 |
| `Li₂c_exp_re`, `Li₂c_exp_im` | boundary decomposition: `Re Li₂c(e^{iθ}) = π²/6−πθ/2+θ²/4`, `Im = Cl₂ θ` | 1 |
| `Li₂c_exp_ne_zero` | no zero on the unit circle for `θ ∈ (0,2π)` (principal branch) | 1 |
| `hasDerivAt_Li₂c` | the analytic core `Li₂c'(z) = −log(1−z)/z` | 2 |
| `phi`, `hasDerivAt_phi`, `z_mul_deriv_phi` | multivalued `φ_{A,B}` + O'Sullivan (2.1) `z·φ' = −log(1−z)+2πiB` | 2 |
| `continuousOn_Li₂c` | continuity of `Li₂c` on the closed disk (M-test) | 3 |
| `Iθ_one`, `exists_Iθ_zero_lt_one` | `I_θ(1) = Cl₂(θ)`; the imaginary-part zero curve lies **inside** the disk for `θ ∈ (0,π)`, `B ≥ 1` (core of O'Sullivan Prop. 5.3) | 3 |

The full existence/uniqueness of the zero (O'Sullivan Thm 1.1, via the argument principle
or Newton's method) is future work.

### Abel's five-term relation — *The Pentagon, Machine-Checked*

The weight-2 capstone (`Dilog/FiveTerm.lean`), built on the dilogarithm above: the
**generator** from which every rational functional equation of `Li₂` follows (Wojtkowiak, de
Jeu). To the best of our knowledge the first machine-checked five-term relation in any proof
assistant. `sorry`-free; three standard axioms. Sequel to *The Clock That Never Ticks*, which
climbed the golden ladder without it.

| Lean name | Statement | Role |
|---|---|---|
| `rogersL_fiveterm` | `L(x)+L(y) = L(xy) + L(x(1−y)/(1−xy)) + L(y(1−x)/(1−xy))` on `(0,1)²` | the five-term relation |
| `fiveterm_hasDerivAt_zero` | the five-term difference has identically zero derivative (nine logs collapse to a basis of five) | core |
| `hasDerivAt_rogersL` | `L'(x) = −½·(ln(1−x)/x + ln x/(1−x))` | reusable block |
| `tendsto_rogersL_nhdsGT_zero` | `L(t) → 0` as `t → 0⁺` (the `−t·ln t` squeeze) | reusable block |
| `continuousAt_rogersL` | `L` continuous on `(0,1)` | reusable block |

Two hand-checkable instances: `(x,y)=(½,½)` gives `L(¼)+2L(⅓) = π²/6`; `(x,y)=(1/φ,1/φ)`
collapses all three arguments to `1/φ²`, giving `2L(1/φ) = 3L(1/φ²) = π²/5`.

### Newton's inequalities — *The Inward Bow of a Real-Rooted Polynomial*

The classical **real-rooted ⇒ log-concave** bridge (`Newton.lean`), the engine Paper II uses
informally, now certified. `sorry`-free; three standard axioms.

| Lean name | Statement | File |
|---|---|---|
| `newton_inequality` | `e_k² C(n,k−1)C(n,k+1) ≥ e_{k−1}e_{k+1} C(n,k)²` (monic, real-rooted) | `Newton.lean` |
| `newton_logConcave` | `p_{k−1}p_{k+1} ≤ p_k²` — log-concavity of the normalized means | `Newton.lean` |
| `newton_inequality_coeff` | coefficient form `a_i² C(n,i−1)C(n,i+1) ≥ a_{i−1}a_{i+1} C(n,i)²` (no monic) | `Newton.lean` |
| `realRooted_discrim_coeff` | real-rooted, `deg ≤ 2 ⇒ a_1² ≥ 4 a_2 a_0` (the base case) | `Newton.lean` |
| `RealRooted.derivative`, `.iterate_derivative` | real-rootedness under `D` and `Dᵏ` (Rolle) | `Newton.lean` |
| `RealRooted.reverse` | real-rootedness under reversal `x ↦ 1/x` | `Newton.lean` |

Worked instance: for `(x−1)(x−2)(x−4)` (so `e = (1,7,14,8)`), `k=1` reads `147 ≥ 126` and `k=2`
reads `588 ≥ 504`; `(x−1)⁴` saturates every inequality, and `x²+1` (complex roots) fails it.

### Sturm's theorem — *The Staircase of Signs*

Counting the real roots of a polynomial in an interval **without finding a single one** (`Sturm.lean`):
the drop in sign variations of the Sturm sequence equals the root count. To our knowledge the
**first Sturm's theorem in Lean** (not first in any system). `sorry`-free; three standard axioms.

| Lean name | Statement | File |
|---|---|---|
| `Sturm.sturm` | `V(a) − V(b) = #{distinct real roots of p in (a,b]}` (squarefree, `p(a),p(b) ≠ 0`) | `Sturm.lean` |
| `sturmSeq` | the negated signed-remainder sequence `p, p′, −(p mod p′), …` | `Sturm.lean` |
| `signVarAt` | sign changes of the list evaluated at `x` (zeros dropped) | `Sturm.lean` |
| `signVarAt_drop_at_critical_point` | per-point quantum: `ΔV ∈ {0,1}` at an isolated critical point | `Sturm.lean` |
| `flankReduce_chain_walk` | the chain reduces to its non-vanishers (the coupled-recursion wall) | `Sturm.lean` |
| `FlankReduce.signChanges_eq` | flank-reduction preserves the sign-change count | `Sturm.lean` |
| `sign_neighbours_opposite_at_interior_root` | antipodal neighbours at a zero of an interior member | `Sturm.lean` |
| `signVariations_eq_signChanges` | `=` Descartes' `signVariations` (by `rfl`) | `Sturm.lean` |

Worked instance: for `x³−x` (chain `x³−x, 3x²−1, (2/3)x, 1`), `V(−2)=3` and `V(2)=0`, so there are
`3` roots in `(−2,2]` — read off the signs, no root computed.

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
# core
RealStable.lean              RealRooted / BoundedBy predicates + closure algebra
MatchingPoly.lean            matching polynomial μ_G, matching number, deletion recurrence
RamanujanBound.lean          the band edge 2√(k−1) (bruhatTitsBound) and its algebra
Newton.lean                  Newton's inequalities: real-rooted ⇒ log-concave (esymm + coeff form)
Sturm.lean                   Sturm's theorem: real-root counting via the signed remainder sequence + sign variation

# MSS/ — Papers I–II
MSS/Basic.lean               signed adjacency matrix
MSS/ExpectedCharpoly.lean    the average (expected) characteristic polynomial
MSS/GodsilGutman.lean        the Godsil–Gutman identity + the ℤ/2 engine            (Paper I)
MSS/TwoLift.lean             Bilu–Linial 2-lift spectral decomposition             (Paper I)
MSS/MatchingSum.lean         matching-sum / permutation-expansion machinery
MSS/PathTree.lean            Godsil's path tree + acyclicity                       (Paper II)
MSS/Divisibility.lean        μ_G ∣ μ_{T(G,u)} (the divisibility brick)             (Paper II)
MSS/ForestComponents.lean    connected divisibility + component decomposition      (Paper II)
MSS/ForestRealRooted.lean    forest identity, T5/T6 real-rootedness                (Paper II)
MSS/HeilmannLieb.lean        interlacing/geometric real-stability engine           (Paper II)
MSS/HeilmannLiebBound.lean   the Ramanujan bound (Collatz–Wielandt + tree facts)   (Paper II)

# Ihara/ — Papers III–VI and the Ihara companions
Ihara/PathTree.lean          path-tree-faithful tree-like predicate (liftSeq)      (Paper III)
Ihara/MomentBridge.lean      the bijection tree-like walks ↔ path-tree walks       (Paper III)
Ihara/TreeLikeWalks.lean     treeLikeWalkCount, below-girth lifting, matchingPowerSum (III–VI)
Ihara/GodsilMoment.lean      matching-number deletion + derivative identities      (Paper IV)
Ihara/MomentAssembly.lean    the moment theorem p_k = treeLikeWalkCount            (Paper IV)
Ihara/PowerSumGenfun.lean    power-sum generating function of the matching roots   (Paper IV)
Ihara/ResolventGenfun.lean   resolvent generating function over R⟦X⟧              (Papers IV, JN)
Ihara/CauchyBinet.lean       the Cauchy–Binet formula                              (Paper V)
Ihara/OrientedIncidence.lean oriented incidence matrix, N·Nᵀ = D − A              (Paper V)
Ihara/MatrixTree.lean        reduced Laplacian = N₀·N₀ᵀ, sum-of-squared-minors     (Paper V)
Ihara/SpanningTreeMinor.lean spanning-tree minor dichotomy (sort, not leaf-delete) (Paper V)
Ihara/Kirchhoff.lean         det L₀ = #spanning trees (Kirchhoff)                  (Paper V)
Ihara/NbVanishing.lean       Stone A: tr Bᵏ = 0 below the girth                    (Paper VI)
Ihara/GapWindow.lean         the sharp gap law tr Aᵏ − p_k = tr Bᵏ (capstone)      (Paper VI)
Ihara/NbWalkCount.lean       tr(Bᵏ) counts closed non-backtracking dart walks
Ihara/Bass.lean              Bass's determinant formula for the Ihara zeta         (Ihara–Bass companion)
Ihara/TraceFormula.lean      resolvent series, Jacobi adjugate, charpolyRev_logDeriv (Jacobi–Newton companion)
Ihara/PowerSumLogDeriv.lean  Newton log-derivative (geom-series / reversed product)  (Jacobi–Newton companion)
Ihara/ResolventDiag.lean     diagonal resolvent, charpolyRev = det(I − X·M)          (Jacobi–Newton companion)
Ihara/AdjugateDiagMinor.lean adjugate diagonal entry = principal minor              (Jacobi–Newton companion)

# Dilog/, QSL/ — the dilogarithm + quantum speed limits (independent strand)
Dilog/Basic.lean             Li₂: series, derivative, reflection, Landen, duplication, golden ladder, Rogers L
Dilog/Clausen.lean           Clausen Cl₂, Catalan's constant, Bernoulli parabola, Cl₂≥sinθ/2, zeta-state theorem
Dilog/ComplexBoundary.lean   complex Li₂c, boundary decomposition, derivative, φ_{A,B}, zero-curve localization
Dilog/FejerJackson.lean      the Fejér–Jackson inequality
QSL/Basic.lean               Margolus–Levitin quantum speed limit (+ the cosine inequality)
QSL/MandelstamTamm.lean      Mandelstam–Tamm, L¹ form

# papers — each with an -es Spanish edition and a compiled .pdf
godsil-gutman-lean.tex       Paper I    — Random Signs into Matchings
heilmann-lieb-lean.tex       Paper II   — Unfolding a Graph into a Tree
path-tree-walks-lean.tex     Paper III  — Walks that Forget the Cycles
moment-theorem-lean.tex      Paper IV   — When Walks Become a Spectrum
matrix-tree-lean.tex         Paper V    — Counting Trees Without Listing Them
gap-window-lean.tex          Paper VI   — The Walks That Remember the Cycles
ihara-bass-lean.tex          companion  — Folding Edges into Vertices (Bass)
jacobi-newton-lean.tex       companion  — What a Determinant's Derivative Knows
ldpc-census.tex              applied    — Certified Short-Cycle Counts for IEEE 802.11n LDPC
clock-never-ticks.tex        strand     — The Clock That Never Ticks (dilogarithm → QSL)
five-term-lean.tex           strand     — The Pentagon, Machine-Checked (Abel's five-term)
newton-inequalities-lean.tex strand     — The Inward Bow of a Real-Rooted Polynomial (Newton)
sturm-lean.tex               strand     — The Staircase of Signs (Sturm's theorem)
references.bib               bibliography
figures/                     figure scripts + PDFs + per-paper tables.tex
research/                    numerical locks, sweeps, the LDPC census pipeline
```

## Building

Requires [`elan`](https://github.com/leanprover/elan). The toolchain is pinned in
`lean-toolchain` (`leanprover/lean4:v4.30.0-rc2`); Mathlib is pinned in
`lakefile.lean`.

```bash
lake exe cache get      # prebuilt Mathlib oleans (recommended)
lake build              # core, MSS/* (Papers I–II)
lake build Ihara        # Ihara/* (Papers III–VI and the companions)
lake build Dilog QSL    # dilogarithm + quantum speed limits (independent strand)
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
  year   = {2026}, doi = {10.5281/zenodo.20648488},
  note   = {Part VI (concept DOI, latest version). \url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
@misc{Marin2026LDPCCensus,
  author = {Mar\'in, Carles},
  title  = {Certified Short-Cycle Counts for the IEEE 802.11n (WiFi) LDPC Codes},
  year   = {2026}, doi = {10.5281/zenodo.20649056},
  note   = {Applied companion. \url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
@misc{Marin2026ClockNeverTicks,
  author = {Mar\'in, Carles},
  title  = {The Clock That Never Ticks: A Machine-Checked Path from the Dilogarithm to Quantum Speed Limits in Lean 4},
  year   = {2026}, doi = {10.5281/zenodo.20675270},
  note   = {Independent strand (concept DOI, latest version). \url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
@misc{Marin2026FiveTermLean,
  author = {Mar\'in, Carles},
  title  = {The Pentagon, Machine-Checked: Abel's Five-Term Relation for the Dilogarithm in Lean 4},
  year   = {2026}, doi = {10.5281/zenodo.20682715},
  note   = {Sequel to The Clock That Never Ticks (concept DOI, latest version). \url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
@misc{Marin2026NewtonInequalitiesLean,
  author = {Mar\'in, Carles},
  title  = {The Inward Bow of a Real-Rooted Polynomial: Newton's Inequalities, Machine-Checked in Lean 4},
  year   = {2026}, doi = {10.5281/zenodo.20693064},
  note   = {Real-rooted $\Rightarrow$ log-concave; first in any prover. \url{https://github.com/karlesmarin/godsil-gutman-lean}}
}
@misc{Marin2026SturmLean,
  author = {Mar\'in, Carles},
  title  = {The Staircase of Signs: Sturm's Root-Counting Theorem, Machine-Checked in Lean 4},
  year   = {2026}, doi = {10.5281/zenodo.20707348},
  note   = {Real-root counting via the signed remainder sequence; first in Lean. \url{https://github.com/karlesmarin/godsil-gutman-lean}}
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
Part VI [10.5281/zenodo.20648488](https://doi.org/10.5281/zenodo.20648488),
Applied census [10.5281/zenodo.20649056](https://doi.org/10.5281/zenodo.20649056).
Clock paper (dilogarithm + QSL strand) [10.5281/zenodo.20675270](https://doi.org/10.5281/zenodo.20675270),
Pentagon / five-term [10.5281/zenodo.20682715](https://doi.org/10.5281/zenodo.20682715),
Newton's inequalities [10.5281/zenodo.20693064](https://doi.org/10.5281/zenodo.20693064),
Sturm's theorem [10.5281/zenodo.20707348](https://doi.org/10.5281/zenodo.20707348).

## Author and license

**Carles Marín** (independent researcher, `karlesmarin@gmail.com`). The Lean
formalization was carried out with Claude (Anthropic) as an AI research instrument
under a build-as-oracle loop: the assistant proposed definitions and proofs, the
Lean kernel verified or rejected each, and all design decisions, mathematics and
claims are the author's responsibility. The kernel has the last word.

Licensed under the **Apache License 2.0** — see [`LICENSE`](LICENSE).
