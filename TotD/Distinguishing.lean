/-
Authors: Carles Marín, Claude (Anthropic) as AI assistant.

Distinguishing numbers of group actions, and the Fano exception
`D(GL(3,2) ↷ F₂³ \ {0}) = 4`, machine-checked.

A coloring `c : X → Fin k` of a `G`-set `X` is *distinguishing* if the identity is the
only element of `G` preserving it; the *distinguishing number* `D(G ↷ X)` is the least
such `k` (Albertson–Collins, EJC 3 (1996) R18, for graphs; Tymoczko, EJC 11 (2004) R63,
for group actions). Melody Chan (EJC 13 (2006) R70, arXiv:math/0601359) computed the
distinguishing numbers of many linear actions and asked (Question 4) for
`D(GL_n(K) ↷ K^n)` in the remaining cases `|K| ≤ n + 1`. The answer is
Klavžar–Wong–Zhu, J. Algebra 303 (2006) 626–641, Theorem 3.1: `D = 2` always, except
`GL(2,2)`, `GL(2,3)`, `GL(4,2)` (where `D = 3`) and the single maximum `GL(3,2)`
(where `D = 4`). Devillers–Morgan–Harper (arXiv:1808.08705) re-derive this via
semiprimitive groups — note their introduction's summary sentence omits the `(3,2)`
`D = 4` case, contradicting their own Table 2; we follow KWZ and our own exhaustive
computation (GAP + Python cross-check, `chan_q4_log.txt`, 2026-07-17).

This file contributes, to our knowledge, the FIRST formalization of distinguishing
numbers in any interactive theorem prover (literature gate cleared 2026-07-17):

* `TotD.IsDistinguishing`, `TotD.distinguishingNumber` — the general definitions for a
  `MulAction` of a group, with basic API: monotonicity in `k`
  (`IsDistinguishing.mono`), `D ≤ |X|` for faithful actions
  (`distinguishingNumber_le_card`), and the IBIS bridge `D ≤ b + 1` for a base of
  size `b` (`distinguishingNumber_le_card_base_add_one`, bridge B3 of the TotD plan).
* The exceptional case, fully kernel-checked with plain `decide` (no `native_decide`
  anywhere): `fanoGroup` is the collineation group of the Fano plane, i.e. the
  stabilizer in `Equiv.Perm (Fin 7)` of the 7 lines — this is
  `GL(3,2) ≅ PSL(2,7)` of order 168 (classical Fano count, GAP-cross-checked; not proved in Lean — see the
  in-file note) acting on the 7 nonzero vectors of `F₂³`
  (point `i` ↔ binary digits of `i + 1`).
  - `fano_not_isDistinguishing_two`, `fano_not_isDistinguishing_three`: no 2- or
    3-coloring is distinguishing. Engine: a greedy list of 21 involutions
    (transvections) such that every one of the `3^7 = 2187` colorings is preserved by
    at least one of them (`fanoWitnesses_cover`, a single `decide`).
  - `fanoColoring_isDistinguishing`: the explicit coloring `(0,0,0,0,1,2,3)` IS
    distinguishing — proved structurally from the line geometry (unique colors pin
    points 4, 5, 6; lines `{2,4,5}`, `{0,5,6}`, `{1,4,6}` then pin 2, 0, 1;
    injectivity pins 3), no big enumeration needed.
  - `fano_distinguishingNumber : distinguishingNumber ↥fanoGroup (Fin 7) = 4`.

Honesty: the VALUES are known mathematics (KWZ 2006); ours is the formalization.
Documented frontier (not attempted): `D(GL(4,2) ↷ F₂⁴ \ {0}) = 3` — the lower bound
`D ≥ 3` needs all `2^15 = 32768` subsets checked against `|GL(4,2)| = 20160` elements,
too heavy for plain kernel `decide` without a cleverer certificate (e.g. a per-subset
witness table or a conjugacy-class union bound); left as a future brick.

Sorry-free. Axioms per theorem printed at the end of the file.
-/
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Group.Submonoid.MulAction
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.VecNotation

open MulAction Pointwise

-- The Fano decide bricks (`fanoWitnesses_spec`, `fanoWitnesses_cover`) exhaust
-- thousands of colorings / nested-`Finset` membership checks in the kernel; raise the
-- elaboration recursion limit so `decide` can unfold them.
set_option maxRecDepth 10000

namespace TotD

/-! ### Distinguishing colorings and the distinguishing number, in general -/

/-- A coloring `c : X → Fin k` is *distinguishing* for the action of `G` on `X` if the
only `g : G` preserving the coloring is the identity (Albertson–Collins 1996;
Tymoczko 2004 for arbitrary group actions). -/
def IsDistinguishing (G : Type*) {X : Type*} [Group G] [MulAction G X] {k : ℕ}
    (c : X → Fin k) : Prop :=
  ∀ g : G, (∀ x : X, c (g • x) = c x) → g = 1

/-- The *distinguishing number* `D(G ↷ X)`: the least number of colors admitting a
distinguishing coloring (`sInf`, so `0` if no coloring distinguishes — e.g. an
unfaithful action of a nontrivial group on a finite set). -/
noncomputable def distinguishingNumber (G X : Type*) [Group G] [MulAction G X] : ℕ :=
  sInf {k : ℕ | ∃ c : X → Fin k, IsDistinguishing G c}

variable {G X : Type*} [Group G] [MulAction G X]

/-- Monotonicity: a distinguishing `k`-coloring yields a distinguishing `m`-coloring
for any `m ≥ k` (recolor through the inclusion `Fin k ↪ Fin m`). -/
theorem IsDistinguishing.mono {k m : ℕ} (hkm : k ≤ m) {c : X → Fin k}
    (hc : IsDistinguishing G c) :
    IsDistinguishing G fun x : X => (⟨(c x).1, (c x).2.trans_le hkm⟩ : Fin m) :=
  fun g hg => hc g fun x => by
    have h := congrArg Fin.val (hg x)
    exact Fin.ext h

/-- Existence form of monotonicity: the set of color counts admitting a distinguishing
coloring is upward closed. -/
theorem exists_isDistinguishing_mono {k m : ℕ} (hkm : k ≤ m)
    (h : ∃ c : X → Fin k, IsDistinguishing G c) :
    ∃ c : X → Fin m, IsDistinguishing G c :=
  let ⟨_, hc⟩ := h
  ⟨_, hc.mono hkm⟩

/-- A distinguishing `k`-coloring bounds the distinguishing number: `D ≤ k`. -/
theorem distinguishingNumber_le {k : ℕ} {c : X → Fin k} (hc : IsDistinguishing G c) :
    distinguishingNumber G X ≤ k :=
  Nat.sInf_le ⟨c, hc⟩

/-- Lower bound: if some coloring distinguishes (so the defining set is nonempty) but
no `k`-coloring does, then `k < D`. -/
theorem lt_distinguishingNumber {k m : ℕ} {c : X → Fin m} (hc : IsDistinguishing G c)
    (hnone : ∀ c' : X → Fin k, ¬IsDistinguishing G c') :
    k < distinguishingNumber G X := by
  rcases Nat.lt_or_ge k (distinguishingNumber G X) with hlt | hge
  · exact hlt
  · have hmem := Nat.sInf_mem
      (s := {n : ℕ | ∃ c' : X → Fin n, IsDistinguishing G c'}) ⟨m, c, hc⟩
    obtain ⟨c₁, hc₁⟩ := exists_isDistinguishing_mono hge hmem
    exact absurd hc₁ (hnone c₁)

/-- A faithful action on a finite set is distinguished by the all-distinct coloring:
`D ≤ |X|`. -/
theorem distinguishingNumber_le_card [Fintype X] [FaithfulSMul G X] :
    distinguishingNumber G X ≤ Fintype.card X :=
  distinguishingNumber_le (c := fun x => Fintype.equivFin X x) fun g hg =>
    eq_of_smul_eq_smul (α := X) fun x => by
      rw [one_smul]
      exact (Fintype.equivFin X).injective (hg x)

/-- **Bridge B3 (IBIS ↔ distinguishing)**: a base of size `b` — a finite set whose
pointwise stabilizer is trivial — gives `D ≤ b + 1`: color the base points with `b`
distinct nonzero colors and everything else with `0`. -/
theorem distinguishingNumber_le_card_base_add_one [DecidableEq X] (S : Finset X)
    (hS : ∀ g : G, (∀ x ∈ S, g • x = x) → g = 1) :
    distinguishingNumber G X ≤ S.card + 1 := by
  have key : IsDistinguishing G fun x : X =>
      if h : x ∈ S then (S.equivFin ⟨x, h⟩).succ else (0 : Fin (S.card + 1)) := by
    intro g hg
    refine hS g fun x hx => ?_
    have hgx : (if h : g • x ∈ S then (S.equivFin ⟨g • x, h⟩).succ
        else (0 : Fin (S.card + 1))) =
        (if h : x ∈ S then (S.equivFin ⟨x, h⟩).succ else (0 : Fin (S.card + 1))) := hg x
    rw [dif_pos hx] at hgx
    by_cases hmem : g • x ∈ S
    · rw [dif_pos hmem] at hgx
      have : (⟨g • x, hmem⟩ : S) = ⟨x, hx⟩ :=
        S.equivFin.injective (Fin.ext (Nat.succ.inj (congrArg Fin.val hgx)))
      exact congrArg Subtype.val this
    · rw [dif_neg hmem] at hgx
      exact absurd hgx.symm (Fin.succ_ne_zero _)
  exact distinguishingNumber_le key

/-! ### The Fano exception: `D(GL(3,2) ↷ F₂³ \ {0}) = 4`

Points `0, …, 6 : Fin 7` stand for the nonzero vectors of `F₂³`: point `i` is the
vector whose binary digits are those of `i + 1` (so `0 ↔ (1,0,0)`, `1 ↔ (0,1,0)`,
`2 ↔ (1,1,0)`, `3 ↔ (0,0,1)`, `4 ↔ (1,0,1)`, `5 ↔ (0,1,1)`, `6 ↔ (1,1,1)`).
A triple is a line of the Fano plane iff the corresponding vectors sum to zero, and a
permutation of the points is induced by a (unique) element of `GL(3,2)` iff it maps
lines to lines. -/

/-- The 7 lines of the Fano plane on `Fin 7` (triples whose vectors XOR to zero). -/
def fanoLines : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

/-- The collineation group of the Fano plane: the stabilizer in `Equiv.Perm (Fin 7)`
of the line set. Abstractly `GL(3,2) ≅ PSL(2,7)`, of order 168, in its natural action
on the nonzero vectors of `F₂³`. -/
def fanoGroup : Subgroup (Equiv.Perm (Fin 7)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 7)) fanoLines

instance : DecidablePred (· ∈ fanoGroup) := fun g =>
  decidable_of_iff (g • fanoLines = fanoLines) MulAction.mem_stabilizer_iff.symm

-- The collineation group of the Fano plane has order 168 (`= |GL(3,2)| = |PSL(2,7)|`),
-- the classical count of Fano structures on 7 points, cross-checked in GAP
-- (`chan_q4_log.txt`). We do not prove the cardinality in Lean: `decide` on the subtype
-- fintype of `Equiv.Perm (Fin 7)` (5040 elements, each a nested-`Finset` membership test)
-- blows up the kernel (>19 GB), and the `D = 4` result below does not depend on it.

/-- Build an involutive permutation of `Fin 7` from its vector of images. -/
private def involPerm (v : Fin 7 → Fin 7) (h : ∀ x, v (v x) = x) : Equiv.Perm (Fin 7) :=
  ⟨v, v, h, h⟩

/-- 21 involutions of `fanoGroup` (the transvections of `GL(3,2)`), listed in greedy
cover order: every 3-coloring of the 7 points is preserved by at least one of them
(`fanoWitnesses_cover`). Generated and cross-checked against GAP
(`chan_q4_log.txt`). -/
def fanoWitnesses : List (Equiv.Perm (Fin 7)) :=
  [involPerm ![0, 1, 2, 4, 3, 6, 5] (by decide),
   involPerm ![0, 3, 4, 1, 2, 5, 6] (by decide),
   involPerm ![0, 5, 6, 3, 4, 1, 2] (by decide),
   involPerm ![2, 1, 0, 3, 6, 5, 4] (by decide),
   involPerm ![1, 0, 2, 3, 5, 4, 6] (by decide),
   involPerm ![3, 1, 5, 0, 4, 2, 6] (by decide),
   involPerm ![0, 4, 3, 2, 1, 5, 6] (by decide),
   involPerm ![3, 6, 2, 0, 4, 5, 1] (by decide),
   involPerm ![0, 2, 1, 3, 4, 6, 5] (by decide),
   involPerm ![0, 1, 2, 5, 6, 3, 4] (by decide),
   involPerm ![0, 1, 2, 6, 5, 4, 3] (by decide),
   involPerm ![0, 2, 1, 4, 3, 5, 6] (by decide),
   involPerm ![0, 6, 5, 3, 4, 2, 1] (by decide),
   involPerm ![1, 0, 2, 6, 4, 5, 3] (by decide),
   involPerm ![2, 1, 0, 5, 4, 3, 6] (by decide),
   involPerm ![4, 1, 6, 3, 0, 5, 2] (by decide),
   involPerm ![4, 5, 2, 3, 0, 1, 6] (by decide),
   involPerm ![5, 1, 3, 2, 4, 0, 6] (by decide),
   involPerm ![5, 4, 2, 3, 1, 0, 6] (by decide),
   involPerm ![6, 1, 4, 3, 2, 5, 0] (by decide),
   involPerm ![6, 3, 2, 1, 4, 5, 0] (by decide)]

/-- Every witness is a nontrivial element of the collineation group. Kernel `decide`
(the `p ∈ fanoGroup` checks are nested-`Finset` line-set equalities, too heavy for the
heartbeat-bounded elaborator; only 21 items, so the kernel handles them quickly). -/
theorem fanoWitnesses_spec :
    ∀ p ∈ fanoWitnesses, p ∈ fanoGroup ∧ ∃ x : Fin 7, p x ≠ x := by decide +kernel

private theorem dec7 (y : Fin 7) :
    y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 := by
  revert y; decide

private theorem vec_apply {α : Type*} (c : Fin 7 → α) (x : Fin 7) :
    ![c 0, c 1, c 2, c 3, c 4, c 5, c 6] x = c x := by
  rcases dec7 x with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **Kernel-checked cover**: each of the `3^7 = 2187` colorings of the Fano points is
preserved by at least one of the 21 witnesses. This is the entire exhaustive content
of "no 3-coloring distinguishes", packed into one plain `decide`. -/
theorem fanoWitnesses_cover : ∀ a b c d e f g : Fin 3,
    ∃ p ∈ fanoWitnesses, ∀ x : Fin 7,
      ![a, b, c, d, e, f, g] (p x) = ![a, b, c, d, e, f, g] x := by decide +kernel

/-- No 3-coloring of the Fano points is distinguishing (KWZ 2006 for `GL(3,2)`;
independently exhausted by our GAP/Python cross-check: 0 of 2187). -/
theorem fano_not_isDistinguishing_three (c : Fin 7 → Fin 3) :
    ¬IsDistinguishing ↥fanoGroup c := by
  intro hc
  obtain ⟨p, hp, hpres⟩ := fanoWitnesses_cover (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6)
  obtain ⟨hmem, x, hx⟩ := fanoWitnesses_spec p hp
  have h1 : (⟨p, hmem⟩ : ↥fanoGroup) = 1 :=
    hc ⟨p, hmem⟩ fun y => (vec_apply c (p y)).symm.trans ((hpres y).trans (vec_apply c y))
  exact hx (congrArg (fun q : Equiv.Perm (Fin 7) => q x) (congrArg Subtype.val h1))

/-- No 2-coloring of the Fano points is distinguishing (so `D ≥ 3`; in fact `D = 4`). -/
theorem fano_not_isDistinguishing_two (c : Fin 7 → Fin 2) :
    ¬IsDistinguishing ↥fanoGroup c := fun hc =>
  fano_not_isDistinguishing_three _ (hc.mono (by decide))

/-- The witness 4-coloring from our GAP cross-check: points `0,1,2,3` share color `0`,
points `4,5,6` get the unique colors `1,2,3`. In vector terms the color classes are
`{(1,0,0), (0,1,0), (1,1,0), (0,0,1)}`, `{(1,0,1)}`, `{(0,1,1)}`, `{(1,1,1)}`. -/
def fanoColoring : Fin 7 → Fin 4 := ![0, 0, 0, 0, 1, 2, 3]

/-- The coloring `(0,0,0,0,1,2,3)` is distinguishing. Structural proof from the line
geometry: the unique colors pin `4, 5, 6`; the lines `{2,4,5}`, `{0,5,6}`, `{1,4,6}`
are the unique lines through their two pinned points, so `2, 0, 1` are pinned;
injectivity pins `3`. -/
theorem fanoColoring_isDistinguishing : IsDistinguishing ↥fanoGroup fanoColoring := by
  rintro ⟨g, hg⟩ hfix
  have hfix' : ∀ x : Fin 7, fanoColoring (g x) = fanoColoring x := hfix
  -- the unique colors 1, 2, 3 pin the points 4, 5, 6
  have h4 : g 4 = 4 :=
    (by decide : ∀ y : Fin 7, fanoColoring y = 1 → y = 4) _ ((hfix' 4).trans (by decide))
  have h5 : g 5 = 5 :=
    (by decide : ∀ y : Fin 7, fanoColoring y = 2 → y = 5) _ ((hfix' 5).trans (by decide))
  have h6 : g 6 = 6 :=
    (by decide : ∀ y : Fin 7, fanoColoring y = 3 → y = 6) _ ((hfix' 6).trans (by decide))
  -- g maps lines to lines
  have hstab : g • fanoLines = fanoLines := MulAction.mem_stabilizer_iff.mp hg
  have hline : ∀ L ∈ fanoLines, g • L ∈ fanoLines := fun L hL => by
    rw [← hstab]; exact Finset.smul_mem_smul_finset hL
  have happ : ∀ (L : Finset (Fin 7)) (y : Fin 7), y ∈ L → g y ∈ g • L := fun L y hy => by
    have := Finset.smul_mem_smul_finset (a := g) hy
    rwa [Equiv.Perm.smul_def] at this
  -- the line {2,4,5} is the unique line through 4 and 5, so 2 is pinned
  have h2 : g 2 = 2 := by
    have hM : g • ({2, 4, 5} : Finset (Fin 7)) ∈ fanoLines := hline _ (by decide)
    have m4 : (4 : Fin 7) ∈ g • ({2, 4, 5} : Finset (Fin 7)) := by
      have h := happ ({2, 4, 5} : Finset (Fin 7)) 4 (by decide); rwa [h4] at h
    have m5 : (5 : Fin 7) ∈ g • ({2, 4, 5} : Finset (Fin 7)) := by
      have h := happ ({2, 4, 5} : Finset (Fin 7)) 5 (by decide); rwa [h5] at h
    have hM245 : g • ({2, 4, 5} : Finset (Fin 7)) = {2, 4, 5} :=
      (by decide : ∀ M ∈ fanoLines, (4 : Fin 7) ∈ M → (5 : Fin 7) ∈ M → M = {2, 4, 5})
        _ hM m4 m5
    have m2 : g 2 ∈ ({2, 4, 5} : Finset (Fin 7)) := by
      have h := happ ({2, 4, 5} : Finset (Fin 7)) 2 (by decide); rwa [hM245] at h
    rcases (by decide : ∀ y : Fin 7, y ∈ ({2, 4, 5} : Finset (Fin 7)) →
        y = 2 ∨ y = 4 ∨ y = 5) _ m2 with h | h | h
    · exact h
    · exact absurd (g.injective (h.trans h4.symm)) (by decide)
    · exact absurd (g.injective (h.trans h5.symm)) (by decide)
  -- the line {0,5,6} is the unique line through 5 and 6, so 0 is pinned
  have h0 : g 0 = 0 := by
    have hM : g • ({0, 5, 6} : Finset (Fin 7)) ∈ fanoLines := hline _ (by decide)
    have m5 : (5 : Fin 7) ∈ g • ({0, 5, 6} : Finset (Fin 7)) := by
      have h := happ ({0, 5, 6} : Finset (Fin 7)) 5 (by decide); rwa [h5] at h
    have m6 : (6 : Fin 7) ∈ g • ({0, 5, 6} : Finset (Fin 7)) := by
      have h := happ ({0, 5, 6} : Finset (Fin 7)) 6 (by decide); rwa [h6] at h
    have hM056 : g • ({0, 5, 6} : Finset (Fin 7)) = {0, 5, 6} :=
      (by decide : ∀ M ∈ fanoLines, (5 : Fin 7) ∈ M → (6 : Fin 7) ∈ M → M = {0, 5, 6})
        _ hM m5 m6
    have m0 : g 0 ∈ ({0, 5, 6} : Finset (Fin 7)) := by
      have h := happ ({0, 5, 6} : Finset (Fin 7)) 0 (by decide); rwa [hM056] at h
    rcases (by decide : ∀ y : Fin 7, y ∈ ({0, 5, 6} : Finset (Fin 7)) →
        y = 0 ∨ y = 5 ∨ y = 6) _ m0 with h | h | h
    · exact h
    · exact absurd (g.injective (h.trans h5.symm)) (by decide)
    · exact absurd (g.injective (h.trans h6.symm)) (by decide)
  -- the line {1,4,6} is the unique line through 4 and 6, so 1 is pinned
  have h1 : g 1 = 1 := by
    have hM : g • ({1, 4, 6} : Finset (Fin 7)) ∈ fanoLines := hline _ (by decide)
    have m4 : (4 : Fin 7) ∈ g • ({1, 4, 6} : Finset (Fin 7)) := by
      have h := happ ({1, 4, 6} : Finset (Fin 7)) 4 (by decide); rwa [h4] at h
    have m6 : (6 : Fin 7) ∈ g • ({1, 4, 6} : Finset (Fin 7)) := by
      have h := happ ({1, 4, 6} : Finset (Fin 7)) 6 (by decide); rwa [h6] at h
    have hM146 : g • ({1, 4, 6} : Finset (Fin 7)) = {1, 4, 6} :=
      (by decide : ∀ M ∈ fanoLines, (4 : Fin 7) ∈ M → (6 : Fin 7) ∈ M → M = {1, 4, 6})
        _ hM m4 m6
    have m1 : g 1 ∈ ({1, 4, 6} : Finset (Fin 7)) := by
      have h := happ ({1, 4, 6} : Finset (Fin 7)) 1 (by decide); rwa [hM146] at h
    rcases (by decide : ∀ y : Fin 7, y ∈ ({1, 4, 6} : Finset (Fin 7)) →
        y = 1 ∨ y = 4 ∨ y = 6) _ m1 with h | h | h
    · exact h
    · exact absurd (g.injective (h.trans h4.symm)) (by decide)
    · exact absurd (g.injective (h.trans h6.symm)) (by decide)
  -- injectivity pins the last point 3
  have h3 : g 3 = 3 := by
    rcases dec7 (g 3) with h | h | h | h | h | h | h
    · exact absurd (g.injective (h.trans h0.symm)) (by decide)
    · exact absurd (g.injective (h.trans h1.symm)) (by decide)
    · exact absurd (g.injective (h.trans h2.symm)) (by decide)
    · exact h
    · exact absurd (g.injective (h.trans h4.symm)) (by decide)
    · exact absurd (g.injective (h.trans h5.symm)) (by decide)
    · exact absurd (g.injective (h.trans h6.symm)) (by decide)
  refine Subtype.ext (Equiv.ext fun x => ?_)
  rcases dec7 x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5, h6]

/-- **The Fano exception, machine-checked** (Klavžar–Wong–Zhu, J. Algebra 303 (2006),
Thm 3.1, the unique `D = 4` case; answers part of Chan's Question 4):
the distinguishing number of `GL(3,2) ≅ PSL(2,7)` acting on the 7 nonzero vectors of
`F₂³` — equivalently, of the collineation group of the Fano plane acting on its
points — is exactly 4. -/
theorem fano_distinguishingNumber : distinguishingNumber ↥fanoGroup (Fin 7) = 4 :=
  le_antisymm (distinguishingNumber_le fanoColoring_isDistinguishing)
    (lt_distinguishingNumber fanoColoring_isDistinguishing fano_not_isDistinguishing_three)

end TotD

#print axioms TotD.IsDistinguishing.mono
#print axioms TotD.distinguishingNumber_le
#print axioms TotD.lt_distinguishingNumber
#print axioms TotD.distinguishingNumber_le_card
#print axioms TotD.distinguishingNumber_le_card_base_add_one
#print axioms TotD.fanoWitnesses_spec
#print axioms TotD.fanoWitnesses_cover
#print axioms TotD.fano_not_isDistinguishing_three
#print axioms TotD.fano_not_isDistinguishing_two
#print axioms TotD.fanoColoring_isDistinguishing
#print axioms TotD.fano_distinguishingNumber
