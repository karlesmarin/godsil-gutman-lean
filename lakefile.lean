import Lake
open Lake DSL

package «godsil_gutman_lean» where
  -- mathlib-style settings
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Pinned to the exact Mathlib revision the development was built against
-- (Lean toolchain: see `lean-toolchain`). Run `lake exe cache get` before `lake build`.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "701fb6e9c3b9285968b375d19886bfc5ca134840"

@[default_target]
lean_lib «Sturm» where
  -- Sturm's theorem (real-root counting via the signed-remainder chain). First in Lean.
  -- Exposes the reusable sign-variation toolkit (signVarAt, signChanges, wallCount) that the
  -- Budan–Fourier development imports and reuses on the derivative tower.

@[default_target]
lean_lib «RealStable» where
  -- RealRooted predicate + closure algebra + Interlaces (pencil form).
  -- Foundation toward Heilmann–Lieb (real-rootedness), used by MatchingPoly.

@[default_target]
lean_lib «MatchingPoly» where
  -- The matching polynomial μ_G, matching number, and the deletion recurrence.
  -- First such infrastructure in any proof assistant.

@[default_target]
lean_lib «RamanujanBound» where
  -- The Bruhat–Tits / Ramanujan band edge 2·√(k−1) and its algebra (Paper II).

@[default_target]
lean_lib «Ihara» where
  -- Bass's determinant formula for the Ihara zeta function (matrix-identity core).
  -- The "Ihara side"; a future Part II bridges this to the matching polynomial (MSS).
  globs := #[.submodules `Ihara]

@[default_target]
lean_lib «MathlibPR» where
  -- Mathlib-PR staging: graph-free general results (Jacobi's formula, Newton's identity for
  -- matrix traces, directed-graph walk counting) extracted for upstreaming.
  globs := #[.submodules `MathlibPR]

@[default_target]
lean_lib «Dilog» where
  -- The dilogarithm Li₂ + Euler's reflection identity (first ITP of the dilogarithm; catalog +
  -- literature checked clean 2026-06). Roadmap: Landen/inversion → Abel's five-term relation.
  globs := #[.submodules `Dilog]

@[default_target]
lean_lib «QSL» where
  -- Quantum speed limits: the Margolus–Levitin cosine inequality and theorem
  -- (τ⊥ ≥ π/(2⟨E⟩), ℏ=1). Literature-checked 2026-06: no QSL in any ITP; Mathlib has
  -- zero `quantum` declarations. Roadmap: Mandelstam–Tamm; arbitrary-fidelity ML (2023).
  globs := #[.submodules `QSL]

@[default_target]
lean_lib «MSS» where
  -- Paper I: signed adjacency (Basic), expected characteristic polynomial
  -- (ExpectedCharpoly), the Godsil–Gutman identity (GodsilGutman), the 2-lift (TwoLift).
  -- Paper II: the path tree (PathTree), divisibility (Divisibility), the forest
  -- identity and real-rootedness (MatchingSum, ForestComponents, ForestRealRooted),
  -- and the Heilmann–Lieb root bound (HeilmannLieb, HeilmannLiebBound).
  globs := #[.submodules `MSS]
