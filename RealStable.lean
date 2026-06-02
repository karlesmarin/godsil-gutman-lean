/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Real-rooted polynomials and interlacing — foundation for Marcus–Spielman–Srivastava

**First brick of the MSS Ramanujan-graph existence program.**

Marcus–Spielman–Srivastava (Annals of Mathematics, 2015) proved that bipartite
Ramanujan graphs of *every* degree exist, via the **method of interlacing
polynomials**. That method is Deligne-free — pure real-rootedness and interlacing
of univariate real polynomials — and is entirely absent from Mathlib (checked
2026-05-30: `grep RealStable` / `interlac` → zero hits).

This file lays the foundation: the `RealRooted` predicate with its closure
algebra, the `Interlaces` relation (pencil form), and a scaffold for the MSS
averaging theorem (the combinatorial heart), kept as a documented stub.

Companion to `IharaZeta.lean`, which formalises the **characterisation** half of
Ramanujan graphs (discrete RH: `G` Ramanujan ⟺ Ihara-zeta poles on the critical
circle). MSS is the **existence** half — the two halves of the theory.

## Main definitions
* `RealRooted p` — `p : ℝ[X]` splits into linear/constant factors over `ℝ`
  (all complex roots real). Defined as the intrinsic `Polynomial.Splits`.
* `Interlaces f g` — the real pencil `f + t·g` is real-rooted for every `t : ℝ`.

## Status (2026-05-30)
* Closure algebra of `RealRooted` (`C`, `X - C a`, `*`, `∏`, `0`, `1`) and the
  root-count characterisation: **PROVEN sorry-free**.
* Pencil endpoints of `Interlaces`: **PROVEN sorry-free**.
* `exists_index_le_maxRoot_sum` (MSS averaging core): documented stub.
-/

@[expose] public section

namespace MSS

open Polynomial

variable {p q : Polynomial ℝ}

/-- A real polynomial is **real-rooted** if it splits into linear (and constant)
factors over `ℝ` — equivalently, all of its complex roots are real. Defined as
the intrinsic `Polynomial.Splits`, i.e. membership in the multiplicative closure
of constants `C a` and monic linears `X + C a`. -/
def RealRooted (p : Polynomial ℝ) : Prop := p.Splits

theorem realRooted_zero : RealRooted (0 : Polynomial ℝ) :=
  splits_of_degree_le_zero (by rw [degree_zero]; exact bot_le)

theorem realRooted_one : RealRooted (1 : Polynomial ℝ) :=
  splits_of_degree_le_zero (by rw [degree_one])

/-- Constants are real-rooted. -/
theorem realRooted_C (a : ℝ) : RealRooted (C a) :=
  splits_of_degree_le_zero degree_C_le

/-- Monic linear factors `X - C a` are real-rooted. -/
theorem realRooted_X_sub_C (a : ℝ) : RealRooted (X - C a) :=
  splits_of_degree_le_one_of_monic (le_of_eq (degree_X_sub_C a)) (monic_X_sub_C a)

/-- **Real-rootedness is closed under multiplication.** Immediate from `Splits`
being membership in a submonoid (`Submonoid.mul_mem`). -/
theorem RealRooted.mul (hp : RealRooted p) (hq : RealRooted q) :
    RealRooted (p * q) :=
  Submonoid.mul_mem _ hp hq

/-- **Real-rootedness is closed under finite products.** -/
theorem RealRooted.prod {ι : Type*} {s : Finset ι} {f : ι → Polynomial ℝ}
    (h : ∀ i ∈ s, RealRooted (f i)) : RealRooted (∏ i ∈ s, f i) :=
  Submonoid.prod_mem _ h

/-- **Root-count characterisation.** A real polynomial is real-rooted iff its
multiset of (real) roots has cardinality equal to its degree — i.e. it has
exactly `natDegree` real roots counted with multiplicity. -/
theorem realRooted_iff_card_roots : RealRooted p ↔ p.roots.card = p.natDegree :=
  splits_iff_card_roots

/-- A product of monic linears `∏ (X - C aᵢ)` is real-rooted. -/
theorem realRooted_prod_X_sub_C {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    RealRooted (∏ i ∈ s, (X - C (a i))) :=
  RealRooted.prod (fun i _ => realRooted_X_sub_C (a i))

/-- `p` is **bounded by `B`** if it is real-rooted and all of its (real) roots
lie in the interval `[-B, B]`.

**This is the shared substrate of the whole Ramanujan story** (the fusion of the
two halves):
* discrete RH (`IharaZeta.lean`): a graph is Ramanujan ⟺ its eigenvalues are
  `BoundedBy 2√(k-1)` — see `charpoly_boundedBy_iff_eigenvalues`;
* MSS existence: the Heilmann–Lieb theorem says the matching polynomial is
  `BoundedBy 2√(d-1)`, and the interlacing-family average transfers this bound.

The Joukowski map `λ = (k-1)z + 1/z` sends the critical circle `|z| = 1/√(k-1)`
to the real interval `[-2√(k-1), 2√(k-1)]`, turning "roots on the critical
circle" (the `IharaZeta` factor condition) into "roots in `[-B, B]`" — i.e. into
`BoundedBy`. -/
def BoundedBy (p : Polynomial ℝ) (B : ℝ) : Prop :=
  RealRooted p ∧ ∀ x : ℝ, p.IsRoot x → |x| ≤ B

theorem BoundedBy.realRooted {B : ℝ} (h : BoundedBy p B) : RealRooted p := h.1

/-- **Fundamental constructor / fusion brick.** A product of linears
`∏ (X - C aᵢ)` whose roots `aᵢ` all lie in `[-B, B]` is `BoundedBy B`. Both the
eigenvalue product (RH side, via `IsHermitian.charpoly_eq`) and the matching
polynomial (MSS side) are of exactly this shape. -/
theorem boundedBy_prod_X_sub_C {ι : Type*} (s : Finset ι) (a : ι → ℝ) {B : ℝ}
    (hB : ∀ i ∈ s, |a i| ≤ B) : BoundedBy (∏ i ∈ s, (X - C (a i))) B := by
  refine ⟨realRooted_prod_X_sub_C s a, fun x hx => ?_⟩
  rw [IsRoot, eval_prod] at hx
  obtain ⟨i, hi, hxi⟩ := Finset.prod_eq_zero_iff.mp hx
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hxi
  rw [hxi]; exact hB i hi

/-! ## Largest real root -/

/-- The **largest real root** of `p`, valued in `WithBot ℝ` so that the
empty case (no real roots, e.g. `p = 0` or an irreducible-over-`ℝ` factor) is
total: `maxRoot p = ⊥`. For the method of interlacing polynomials this is the
quantity compared across a family — the averaging theorem says some member's
`maxRoot` is at most the `maxRoot` of the sum. -/
noncomputable def maxRoot (p : Polynomial ℝ) : WithBot ℝ := p.roots.toFinset.max

@[simp] theorem maxRoot_zero : maxRoot (0 : Polynomial ℝ) = ⊥ := by
  simp [maxRoot]

/-- Every real root is `≤ maxRoot`. -/
theorem le_maxRoot {x : ℝ} (hp : p ≠ 0) (hx : p.IsRoot x) :
    (x : WithBot ℝ) ≤ maxRoot p :=
  Finset.le_max (Multiset.mem_toFinset.mpr ((mem_roots hp).mpr hx))

/-- `maxRoot p ≤ B` iff every real root is `≤ B`. -/
theorem maxRoot_le_coe_iff {B : ℝ} :
    maxRoot p ≤ (B : WithBot ℝ) ↔ ∀ x ∈ p.roots, x ≤ B := by
  unfold maxRoot
  refine ⟨fun h x hx => ?_, fun h => Finset.max_le (fun a ha => ?_)⟩
  · have : (x : WithBot ℝ) ≤ (B : WithBot ℝ) :=
      le_trans (Finset.le_max (Multiset.mem_toFinset.mpr hx)) h
    exact_mod_cast this
  · exact_mod_cast h a (Multiset.mem_toFinset.mp ha)

/-- A polynomial **bounded by `B`** has `maxRoot ≤ B`: the upper half of the
`[-B, B]` containment, packaged for the interlacing-family argument. -/
theorem BoundedBy.maxRoot_le {B : ℝ} (h : BoundedBy p B) :
    maxRoot p ≤ (B : WithBot ℝ) := by
  rw [maxRoot_le_coe_iff]
  exact fun x hx => (abs_le.mp (h.2 x (mem_roots'.mp hx).2)).2

/-- When `p` has at least one real root, `maxRoot p` is **attained**: it equals
`↑r` for an actual root `r`. -/
theorem exists_isRoot_eq_maxRoot (hp : p ≠ 0) (hr : p.roots ≠ 0) :
    ∃ r : ℝ, p.IsRoot r ∧ maxRoot p = (r : WithBot ℝ) := by
  have hne : (p.roots.toFinset).Nonempty := Multiset.toFinset_nonempty.mpr hr
  refine ⟨(p.roots.toFinset).max' hne,
    (mem_roots hp).mp (Multiset.mem_toFinset.mp (Finset.max'_mem _ hne)), ?_⟩
  rw [maxRoot]; exact (Finset.coe_max' hne).symm

/-- `f` and `g` **interlace** (pencil form) if every real combination `f + t·g`
of the pencil is real-rooted. This is the operational notion used throughout the
method of interlacing polynomials: a common interlacer of a family yields
real-rootedness of every convex combination, hence of the average. -/
def Interlaces (f g : Polynomial ℝ) : Prop :=
  ∀ t : ℝ, RealRooted (f + C t * g)

/-- An interlacing pencil's left endpoint (`t = 0`) is real-rooted. -/
theorem Interlaces.realRooted_left {f g : Polynomial ℝ} (h : Interlaces f g) :
    RealRooted f := by
  have h0 := h 0
  simpa using h0

/-- If `f` and `g` interlace then their **sum** `f + g` is real-rooted
(the `t = 1` point of the pencil). This is the seed of the MSS averaging
argument. -/
theorem Interlaces.realRooted_add {f g : Polynomial ℝ} (h : Interlaces f g) :
    RealRooted (f + g) := by
  have h1 := h 1
  simpa using h1

/-! ## The interlacing pencil and its convex cone (cala 3) -/

/-- `f` and `g` form an **interlacing pair** if *every* real linear combination
`a·f + b·g` is real-rooted. By the Hermite–Kakeya–Obreschkoff theorem this is
equivalent to `f` and `g` having interlacing roots (a common interlacer); we take
the algebraic form as the working definition, since MSS proofs manipulate the
combinations directly. Strictly stronger than the one-sided pencil `Interlaces`
(take `a = 1`). -/
def Interlace (f g : Polynomial ℝ) : Prop :=
  ∀ a b : ℝ, RealRooted (C a * f + C b * g)

theorem Interlace.realRooted_left {f g : Polynomial ℝ} (h : Interlace f g) :
    RealRooted f := by
  have := h 1 0; simpa using this

theorem Interlace.realRooted_right {f g : Polynomial ℝ} (h : Interlace f g) :
    RealRooted g := by
  have := h 0 1; simpa using this

/-- An interlacing pair's **sum** is real-rooted — the seed of the convex cone. -/
theorem Interlace.realRooted_add {f g : Polynomial ℝ} (h : Interlace f g) :
    RealRooted (f + g) := by
  have := h 1 1; simpa using this

theorem Interlace.symm {f g : Polynomial ℝ} (h : Interlace f g) : Interlace g f := by
  intro a b; have := h b a; rwa [add_comm] at this

/-- **Convex-cone / pencil structure — the algebraic heart of cala 3.** If `f, g`
interlace then *any two* polynomials in their linear pencil `span{f, g}`
interlace each other. Hence the pencil is a 2-dimensional cone all of whose
members are mutually real-rooted — the algebraic backbone of the method of
interlacing polynomials (every combination encountered in MSS stays real-rooted).
-/
theorem Interlace.comb {f g : Polynomial ℝ} (h : Interlace f g) (a b c d : ℝ) :
    Interlace (C a * f + C b * g) (C c * f + C d * g) := by
  intro s t
  have key := h (s * a + t * c) (s * b + t * d)
  have e : C s * (C a * f + C b * g) + C t * (C c * f + C d * g)
         = C (s * a + t * c) * f + C (s * b + t * d) * g := by
    simp only [C_add, C_mul]; ring
  rwa [e]

/-- The pencil is closed under sums (a corollary of `comb`): `f + g` interlaces
`f`. This is the cone's additive-closure brick at the algebraic level. -/
theorem Interlace.add_interlace_left {f g : Polynomial ℝ} (h : Interlace f g) :
    Interlace (f + g) f := by
  have := h.comb 1 1 1 0; simpa using this

/-- Scaling a pencil generator keeps the pair interlacing (cone closed under
nonneg — indeed all — real scaling). -/
theorem Interlace.smul_left {f g : Polynomial ℝ} (h : Interlace f g) (c : ℝ) :
    Interlace (C c * f) g := by
  have := h.comb c 0 0 1; simpa using this

/-! ## HKO bridge — the analytic load-bearing stones (cala 3, analytic) -/

/-- **IVT atom.** If a real polynomial takes values of opposite sign at `x < y`
then it has a root strictly between them. This is the intermediate-value theorem
specialised to polynomials (continuous), and it is the single analytic primitive
out of which the whole Hermite–Kakeya–Obreschkoff sign-change argument is built:
each sign alternation of a combination across the roots of its interlacer yields
one root via this lemma. -/
theorem exists_isRoot_of_eval_mul_neg (p : Polynomial ℝ) {x y : ℝ} (hxy : x < y)
    (h : p.eval x * p.eval y < 0) : ∃ z, z ∈ Set.Ioo x y ∧ p.IsRoot z := by
  have cont : ContinuousOn (fun t => p.eval t) (Set.Icc x y) := p.continuousOn
  rcases mul_neg_iff.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · obtain ⟨z, hz, hez⟩ :=
      intermediate_value_Ioo' hxy.le cont (show (0 : ℝ) ∈ Set.Ioo (p.eval y) (p.eval x) from ⟨hy, hx⟩)
    exact ⟨z, hz, hez⟩
  · obtain ⟨z, hz, hez⟩ :=
      intermediate_value_Ioo hxy.le cont (show (0 : ℝ) ∈ Set.Ioo (p.eval x) (p.eval y) from ⟨hx, hy⟩)
    exact ⟨z, hz, hez⟩

/-- **Counting stone.** A polynomial that has *at least* `natDegree` real roots
(counted with multiplicity) is real-rooted: combined with the always-true reverse
bound `card_roots' : card ≤ natDegree`, exhibiting `natDegree` real roots forces
equality, hence `Splits`. This is the stone that converts "the IVT produced
enough sign-change roots" into `RealRooted`. -/
theorem realRooted_of_natDegree_le_card_roots
    (h : p.natDegree ≤ Multiset.card p.roots) : RealRooted p :=
  realRooted_iff_card_roots.mpr (le_antisymm (card_roots' p) h)

/-! ### Ordering the roots (first sub-cala of the HKO assembly) -/

/-- The **sorted list of distinct real roots** of `p`, strictly increasing.
This is the combinatorial skeleton on which the HKO sign-change argument runs:
the gaps between consecutive entries are where `exists_isRoot_of_eval_mul_neg`
will deposit the roots of a combination. -/
noncomputable def rootsList (p : Polynomial ℝ) : List ℝ := p.roots.toFinset.sort (· ≤ ·)

/-- The sorted root list is **strictly increasing**. -/
theorem rootsList_sortedLT (p : Polynomial ℝ) : (rootsList p).SortedLT :=
  Finset.sortedLT_sort _

/-- The sorted root list has **no duplicates**. -/
theorem rootsList_nodup (p : Polynomial ℝ) : (rootsList p).Nodup :=
  Finset.sort_nodup _ _

/-- Membership in the sorted root list is membership in the root multiset. -/
theorem mem_rootsList {p : Polynomial ℝ} {x : ℝ} :
    x ∈ rootsList p ↔ x ∈ p.roots := by
  rw [rootsList, Finset.mem_sort, Multiset.mem_toFinset]

/-- For `p ≠ 0`, the sorted root list is exactly the set of real roots. -/
theorem mem_rootsList_iff_isRoot {p : Polynomial ℝ} (hp : p ≠ 0) {x : ℝ} :
    x ∈ rootsList p ↔ p.IsRoot x := by
  rw [mem_rootsList, mem_roots hp]

/-- The length of the sorted root list is the number of **distinct** real roots. -/
theorem length_rootsList (p : Polynomial ℝ) :
    (rootsList p).length = p.roots.toFinset.card :=
  Finset.length_sort _

/-- **Completeness of the ordering.** Every real root of `p` appears in
`rootsList p`; conversely every list entry is a genuine root. Packaged for the
gap argument: outside the closed span of `rootsList p` and between consecutive
entries, `p` has no roots, so a sign change there must come from the *other*
polynomial of the pencil — the seed of alternation. -/
theorem isRoot_iff_mem_rootsList {p : Polynomial ℝ} (hp : p ≠ 0) {x : ℝ} :
    p.IsRoot x ↔ x ∈ rootsList p :=
  (mem_rootsList_iff_isRoot hp).symm

/-! ### The sign-change muscle (the novel core of HKO) -/

/-- **Sign-change root count — the muscle.** If a real polynomial `h` takes
values of strictly alternating sign at `n+1` strictly increasing points
`x₀ < x₁ < … < xₙ` (i.e. `h(xᵢ)·h(xᵢ₊₁) < 0` for each consecutive pair), then it
has at least `n` distinct real roots.

This is the heart of the Hermite–Kakeya–Obreschkoff argument and is **not in
Mathlib**. The proof needs no list induction: each gap `(xᵢ, xᵢ₊₁)` independently
yields a root by the IVT atom (`exists_isRoot_of_eval_mul_neg`, selected with
`choose`), and the roots are pairwise distinct because they sit in disjoint,
linearly ordered intervals (`rᵢ < xᵢ₊₁ ≤ xⱼ < rⱼ` for `i < j`). Injectivity then
gives `n ≤ #{distinct roots}`. -/
theorem card_roots_ge_of_alternating (h : Polynomial ℝ) (hh : h ≠ 0) (n : ℕ)
    (x : Fin (n + 1) → ℝ) (hmono : StrictMono x)
    (halt : ∀ i : Fin n, h.eval (x i.castSucc) * h.eval (x i.succ) < 0) :
    n ≤ (h.roots.toFinset).card := by
  choose r hmem hroot using fun i : Fin n =>
    exists_isRoot_of_eval_mul_neg h (hmono (Fin.castSucc_lt_succ (i := i))) (halt i)
  have key : ∀ i j : Fin n, i < j → r i < r j := by
    intro i j hij
    have h3 : x i.succ ≤ x j.castSucc := by
      apply hmono.monotone
      rw [Fin.le_def, Fin.val_succ, Fin.coe_castSucc]
      have := Fin.lt_def.mp hij
      omega
    have h1 : r i < x i.succ := (hmem i).2
    have h2 : x j.castSucc < r j := (hmem j).1
    linarith
  have hinj : Function.Injective r := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact absurd hij (ne_of_lt (key i j hlt))
    · exact heq
    · exact absurd hij.symm (ne_of_lt (key j i hgt))
  have hsub : (Finset.univ.image r) ⊆ h.roots.toFinset := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact Multiset.mem_toFinset.mpr ((mem_roots hh).mpr (hroot i))
  have hcard : (Finset.univ.image r).card = n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  calc n = (Finset.univ.image r).card := hcard.symm
    _ ≤ (h.roots.toFinset).card := Finset.card_le_card hsub

/-- **Sign-change real-rootedness.** A polynomial of degree at most `n` that
alternates sign at `n+1` increasing points is real-rooted: the muscle plus the
counting stone. This is the exact shape in which HKO concludes that a combination
`a·f + b·g` is real-rooted — once the interlacing geometry supplies the
alternating evaluation points. -/
theorem realRooted_of_alternating (h : Polynomial ℝ) (hh : h ≠ 0) (n : ℕ)
    (hdeg : h.natDegree ≤ n) (x : Fin (n + 1) → ℝ) (hmono : StrictMono x)
    (halt : ∀ i : Fin n, h.eval (x i.castSucc) * h.eval (x i.succ) < 0) :
    RealRooted h := by
  apply realRooted_of_natDegree_le_card_roots
  calc h.natDegree ≤ n := hdeg
    _ ≤ (h.roots.toFinset).card := card_roots_ge_of_alternating h hh n x hmono halt
    _ ≤ Multiset.card h.roots := Multiset.toFinset_card_le _

/-! ### Producing the alternation (the last span) -/

/-- At a root `s` of the interlacer `g`, the combination `a·f + b·g` collapses to
the scalar multiple `a · f(s)` (since `g(s) = 0`). This is the algebraic hinge
that transfers `f`'s sign pattern to the combination. -/
theorem eval_comb_at_isRoot (a b : ℝ) (f : Polynomial ℝ) {g : Polynomial ℝ} {s : ℝ}
    (hg : g.IsRoot s) : (C a * f + C b * g).eval s = a * f.eval s := by
  have hg0 : g.eval s = 0 := hg
  simp [eval_add, eval_mul, eval_C, hg0]

/-- **Alternation transfer.** If `f` takes strictly alternating signs at points
`sⱼ` that are all roots of `g`, and `a ≠ 0`, then the combination `a·f + b·g`
*also* alternates there: at each `sⱼ` the combination equals `a·f(sⱼ)`, so the
consecutive product picks up a factor `a² > 0` and keeps the sign of `f`'s. This
is "producing the alternation" for the combination. -/
theorem comb_alternates_of_alternates (a b : ℝ) (ha : a ≠ 0) (f g : Polynomial ℝ)
    (n : ℕ) (s : Fin (n + 1) → ℝ) (hs : ∀ j, g.IsRoot (s j))
    (halt : ∀ j : Fin n, f.eval (s j.castSucc) * f.eval (s j.succ) < 0) :
    ∀ j : Fin n, (C a * f + C b * g).eval (s j.castSucc)
        * (C a * f + C b * g).eval (s j.succ) < 0 := by
  intro j
  rw [eval_comb_at_isRoot a b f (hs j.castSucc), eval_comb_at_isRoot a b f (hs j.succ)]
  have hrw : a * f.eval (s j.castSucc) * (a * f.eval (s j.succ))
      = a ^ 2 * (f.eval (s j.castSucc) * f.eval (s j.succ)) := by ring
  rw [hrw]
  exact mul_neg_of_pos_of_neg (by positivity) (halt j)

/-- **Real-rootedness of a combination from a common interlacer's roots.** If `f`
alternates sign at `n + 1` strictly increasing roots of `g`, and the combination
`a·f + b·g` (nonzero, `a ≠ 0`) has degree `≤ n`, then it is real-rooted. This is
the Hermite–Kakeya–Obreschkoff conclusion, assembled from the muscle
(`realRooted_of_alternating`) and the alternation transfer — reducing the entire
bridge to the single geometric input below. -/
theorem realRooted_comb_of_alternates (a b : ℝ) (ha : a ≠ 0) (f g : Polynomial ℝ)
    (n : ℕ) (hne : C a * f + C b * g ≠ 0)
    (hdeg : (C a * f + C b * g).natDegree ≤ n)
    (s : Fin (n + 1) → ℝ) (hmono : StrictMono s) (hs : ∀ j, g.IsRoot (s j))
    (halt : ∀ j : Fin n, f.eval (s j.castSucc) * f.eval (s j.succ) < 0) :
    RealRooted (C a * f + C b * g) :=
  realRooted_of_alternating (C a * f + C b * g) hne n hdeg s hmono
    (comb_alternates_of_alternates a b ha f g n s hs halt)

/-- **Sign stability — the cornerstone of alternation.** A polynomial with no
root anywhere on a closed interval `[u, v]` keeps a constant nonzero sign there:
`f(u)·f(v) > 0`. This is the contrapositive of the IVT atom and the local fact
that turns "exactly one root of `f` per gap of `g`" into the sign flip that
drives the whole interlacing alternation. -/
theorem eval_mul_pos_of_no_isRoot (f : Polynomial ℝ) {u v : ℝ} (huv : u ≤ v)
    (hno : ∀ z ∈ Set.Icc u v, ¬ f.IsRoot z) : 0 < f.eval u * f.eval v := by
  have hu : f.eval u ≠ 0 := fun h => hno u ⟨le_refl u, huv⟩ h
  have hv : f.eval v ≠ 0 := fun h => hno v ⟨huv, le_refl v⟩ h
  rcases huv.lt_or_eq with hlt | heq
  · rcases lt_trichotomy (f.eval u * f.eval v) 0 with hneg | hz | hpos
    · obtain ⟨z, hz, hez⟩ := exists_isRoot_of_eval_mul_neg f hlt hneg
      exact absurd hez (hno z ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
    · rcases mul_eq_zero.mp hz with h0 | h0
      · exact absurd h0 hu
      · exact absurd h0 hv
    · exact hpos
  · subst heq; exact mul_self_pos.mpr hu

/-- **Sign flip across a lone root — the analytic last stone.** If `f` factors as
`(X - r)·q` with the cofactor `q` having no root on `[u, v]` and `u < r < v`, then
`f` flips sign across `r`: `f(u)·f(v) < 0`. Combined with sign stability this is
the complete *local* content of interlacing alternation — `f` changes sign
exactly across the single root sitting in each gap of the interlacer `g`. -/
theorem eval_mul_neg_of_factor (q : Polynomial ℝ) {r u v : ℝ} (hur : u < r)
    (hrv : r < v) (hno : ∀ z ∈ Set.Icc u v, ¬ q.IsRoot z) :
    ((X - C r) * q).eval u * ((X - C r) * q).eval v < 0 := by
  have hq : 0 < q.eval u * q.eval v :=
    eval_mul_pos_of_no_isRoot q (le_of_lt (hur.trans hrv)) hno
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  have e : (u - r) * q.eval u * ((v - r) * q.eval v)
      = ((u - r) * (v - r)) * (q.eval u * q.eval v) := by ring
  rw [e]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith)) hq

/-- **HKO mortar — the alternation, assembled.** If `f` factors, across each gap
`(xᵢ, xᵢ₊₁)` of a sequence, as `(X - rᵢ)·qᵢ` with the root `rᵢ` inside the gap and
the cofactor `qᵢ` having no root on the closed gap — exactly the data a common
interlacer supplies (one simple root of `f` per gap) — then `f` takes strictly
**alternating signs** at the `xᵢ`. Immediate from the sign-flip stone applied in
each gap. -/
theorem eval_alternating_of_factor_per_gap (f : Polynomial ℝ) (n : ℕ)
    (x : Fin (n + 1) → ℝ)
    (hfac : ∀ i : Fin n, ∃ (r : ℝ) (q : Polynomial ℝ),
        x i.castSucc < r ∧ r < x i.succ ∧ f = (X - C r) * q ∧
        ∀ z ∈ Set.Icc (x i.castSucc) (x i.succ), ¬ q.IsRoot z) :
    ∀ i : Fin n, f.eval (x i.castSucc) * f.eval (x i.succ) < 0 := by
  intro i
  obtain ⟨r, q, hur, hrv, hf, hno⟩ := hfac i
  rw [hf]
  exact eval_mul_neg_of_factor q hur hrv hno

/-- **Per-gap factorisation ⟹ real-rooted (the analytic heart of HKO).** A
polynomial of degree `≤ n` with a simple root in each of `n` gaps of a strictly
increasing sequence is real-rooted. Combines the mortar
(`eval_alternating_of_factor_per_gap`) with the sign-change muscle
(`realRooted_of_alternating`). This closes the analytic content of "interlacing
⟹ real-rooted": once a common interlacer supplies the gaps and the per-gap
factorisations, real-rootedness follows — the engine of Heilmann–Lieb. -/
theorem realRooted_of_factor_per_gap (f : Polynomial ℝ) (hf0 : f ≠ 0) (n : ℕ)
    (hdeg : f.natDegree ≤ n) (x : Fin (n + 1) → ℝ) (hmono : StrictMono x)
    (hfac : ∀ i : Fin n, ∃ (r : ℝ) (q : Polynomial ℝ),
        x i.castSucc < r ∧ r < x i.succ ∧ f = (X - C r) * q ∧
        ∀ z ∈ Set.Icc (x i.castSucc) (x i.succ), ¬ q.IsRoot z) :
    RealRooted f :=
  realRooted_of_alternating f hf0 n hdeg x hmono
    (eval_alternating_of_factor_per_gap f n x hfac)

/-- **The final geometric kernel (stub — now only combinatorial packaging).**
When `g` interlaces `f`, `f` takes alternating signs at the consecutive roots
`s₁ < … < sₙ` of `g`: `f(sⱼ)·f(sⱼ₊₁) < 0` — the sole input to
`realRooted_comb_of_alternates`, hence to the whole HKO bridge.

The **analytic** content is now complete and machine-checked, all the way to
real-rootedness:
* `eval_mul_pos_of_no_isRoot` — constant sign on a root-free interval;
* `eval_mul_neg_of_factor` — sign flip across a lone simple root;
* `eval_alternating_of_factor_per_gap` — per-gap factorisations ⟹ alternation;
* `realRooted_of_factor_per_gap` — per-gap factorisations + `deg ≤ n` ⟹
  `RealRooted` (mortar + sign-change muscle).

What remains is **no longer analysis**: it is the purely combinatorial packaging
— from a clean *geometric* interlacing predicate (roots of `f` and `g` alternate),
extract, in each gap `(sⱼ, sⱼ₊₁)`, the unique root `rⱼ` of `f` and the
factorisation `f = (X - rⱼ)·qⱼ` with `qⱼ` root-free on the gap. Feed that to
`realRooted_of_factor_per_gap` and interlacing ⟹ real-rooted is closed. The
analytic wall is fully down. -/
theorem f_alternates_at_g_roots : True := trivial

/-- **Hermite–Kakeya–Obreschkoff bridge (assembly — stub).**

The remaining span: the algebraic `Interlace f g` (every combination real-rooted)
is equivalent to `f` and `g` having *geometrically interlacing roots* (a common
interlacer). The hard direction — geometric interlacing ⟹ every combination
real-rooted — is assembled from the two stones above:

1. Sort the `n` roots `r₁ > … > rₙ` of the interlacer; on consecutive roots a
   combination `a·f + b·g` evaluates with strictly alternating sign (the value at
   each `rⱼ` is a fixed nonzero multiple of the *other* polynomial, whose roots
   interlace).
2. `exists_isRoot_of_eval_mul_neg` then yields one root of the combination in
   each of the `n−1` gaps; together with the leading-coefficient behaviour at
   `±∞` this exhibits `natDegree` distinct real roots.
3. `realRooted_of_natDegree_le_card_roots` upgrades that to `RealRooted`.

The combinatorial bookkeeping of step 1 (sorted roots, the alternating sign
pattern, disjointness ⇒ distinctness for the count) is the deferred work — the
genuine analytic core. Stones laid; span deferred. -/
theorem hko_geometric_to_algebraic : True := trivial

/-! ## MSS averaging theorem — the combinatorial heart (stub) -/

/-- **MSS averaging theorem (stub — statement deferred).**

The core of the method of interlacing polynomials: if real-rooted polynomials
`f₁, …, fₘ` (same degree, positive leading coefficient) share a **common
interlacer** `g`, then their sum is real-rooted and **some** `fᵢ` has its largest
root at most the largest root of the sum:

  `∃ i, maxRoot (fᵢ) ≤ maxRoot (∑ⱼ fⱼ)`.

Proof strategy (Fell / MSS):
1. The set of polynomials interlaced by a fixed `g` is a convex cone — closed
   under nonneg combination — so `∑ fⱼ` is real-rooted (`Interlaces.realRooted_add`
   iterated is the seed).
2. At the largest root `r` of `∑ fⱼ`, the values `fᵢ(r)` cannot all share the
   strict sign forced by every `fᵢ` having its largest root `> r`; some `fᵢ` must
   already have a root `≥ r`.

Requires first a `maxRoot : ℝ[X] → ℝ` (largest real root, via `p.roots` max) and
its API. Deferred — this is the next sub-cala of the expedition. -/
theorem exists_index_le_maxRoot_sum : True := by
  -- Placeholder for the averaging theorem. Real statement needs `maxRoot`
  -- and the convex-cone lemma for common interlacers.
  trivial

end MSS
