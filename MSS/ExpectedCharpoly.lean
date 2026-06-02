/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import MSS.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Data.Sym.Sym2

/-!
# MSS C2 — the Godsil–Gutman identity (target stated)

Component C2 of the MSS program (`MSS_BLUEPRINT.md`): the **expected characteristic polynomial of a
uniformly random ±1 edge-signing equals the matching polynomial** (Godsil–Gutman 1981). This is the
bridge from the combinatorial side (`matchingPoly`, DONE) to the spectral side.

A *signing* is a `cfg : Sym2 V → Bool`; on edge `s(i, j)` it picks the sign `+1` (`true`) or `−1`
(`false`). Because `Sym2` is unordered, the resulting matrix is automatically symmetric on edges.
Summing the characteristic polynomial over **all** `2^{|Sym2 V|}` configurations (the bits on
non-edges are irrelevant — `signedAdjMatrix` is `0` there — so they only rescale by a common factor),
the Godsil–Gutman theorem says the total equals `(#configs) • matchingPoly G`:

  `∑_{cfg} charpoly(A_cfg) = (card of configs) • matchingPoly G`        (no division needed).

**The hinge (proved next):** `charpoly = det(X·I − A) = ∑_{σ : Perm V} sign(σ) ∏_i (…)_{σ i, i}`
(`Matrix.det_apply`); the uniform ±1 expectation of `∏ edge-signs` vanishes unless every edge is used
an even number of times ⟺ `σ` is an involution made of edges ⟺ `σ` ↔ a matching, with `sign(σ)=(−1)^k`.

Status: **TARGET STATED** as a `def … : Prop` (honesty floor — NOT a proved theorem; not vacuous).
Proof = MEDIUM (`Equiv.Perm` cycle bookkeeping). The signing matrix and the statement compile.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The signed adjacency matrix induced by a `Bool`-configuration on edges: `true ↦ +1`, `false ↦ −1`
(off the edge set it is `0`, via `signedAdjMatrix`). Symmetric because `s(i, j) = s(j, i)` in `Sym2`. -/
noncomputable def signingMatrix (cfg : Sym2 V → Bool) : Matrix V V ℝ :=
  G.signedAdjMatrix (fun i j => if cfg s(i, j) then (1 : ℝ) else -1)

/-- **C2 target (Godsil–Gutman), stated — not yet proved.** The characteristic polynomials of all
`±1` edge-signings sum to `(#configs) • matchingPoly G`. Equivalent to "the *average* charpoly is the
matching polynomial". A `def … : Prop`: a precise target, never a vacuous `∨ True` theorem. -/
def expected_charpoly_eq_matchingPoly_target : Prop :=
  (∑ cfg : Sym2 V → Bool, (G.signingMatrix cfg).charpoly)
    = (Fintype.card (Sym2 V → Bool)) • G.matchingPoly

end SimpleGraph
