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
lean_lib «RealStable» where
  -- RealRooted predicate + closure algebra + Interlaces (pencil form).
  -- Foundation toward Heilmann–Lieb (real-rootedness), used by MatchingPoly.

@[default_target]
lean_lib «MatchingPoly» where
  -- The matching polynomial μ_G, matching number, and the deletion recurrence.
  -- First such infrastructure in any proof assistant.

@[default_target]
lean_lib «MSS» where
  -- Signed adjacency (Basic), expected characteristic polynomial (ExpectedCharpoly),
  -- the Godsil–Gutman identity (GodsilGutman), and the Bilu–Linial 2-lift (TwoLift).
  globs := #[.submodules `MSS]
