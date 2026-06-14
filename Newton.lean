/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

/-
# Newton's inequalities (real-rooted ⟹ log-concave elementary symmetric means)

Reverse-engine target (2026-06-14): confirmed ABSENT from Mathlib (it has `Multiset.esymm` but not
the Newton inequalities). FOUNDATIONAL — the classical bridge "real-rooted ⟹ log-concave coefficients"
underlying matching-poly / Chow / Heilmann–Lieb log-concavity. Built on our `RealStable` (RealRooted).

Skeleton: statement + key lemmas. Proof strategy:
  (1) derivative of a real-rooted real polynomial is real-rooted (Rolle between consecutive roots);
  (2) base case: a real-rooted real quadratic has discriminant ≥ 0;
  (3) reduce index k by differentiating (n-2) times + reversal x↦1/x to a real-rooted quadratic.
-/
public import RealStable
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.Polynomial.Vieta

open Polynomial MSS
open scoped Nat

namespace Newton

variable {p : Polynomial ℝ}

/-- **(1) Rolle stone.** The derivative of a real-rooted real polynomial is real-rooted. -/
public theorem RealRooted.derivative (hp : RealRooted p) :
    RealRooted (Polynomial.derivative p) := by
  rw [realRooted_iff_card_roots] at hp ⊢
  -- upper bound: #roots(p') ≤ deg(p');  Rolle bound: #roots(p) ≤ #roots(p') + 1;
  -- degree drop: deg(p') ≤ deg(p) - 1.  Squeeze with hp (#roots(p) = deg(p)) closes it.
  have hub : (Polynomial.derivative p).roots.card ≤ (Polynomial.derivative p).natDegree :=
    card_roots' _
  have hlb : p.roots.card ≤ (Polynomial.derivative p).roots.card + 1 :=
    card_roots_le_derivative p
  have hdle : (Polynomial.derivative p).natDegree ≤ p.natDegree - 1 :=
    natDegree_derivative_le p
  omega

/-- Real-rootedness is preserved by the **reversal** `x ↦ 1/x`. (The constant term may vanish:
reversal just drops trailing zeros, and the resulting product of `≤ 1`-degree factors still splits.) -/
public theorem RealRooted.reverse (hp : RealRooted p) :
    RealRooted p.reverse := by
  -- helper: the reverse of a product of monic linears is real-rooted (each reverse has degree ≤ 1)
  have key : ∀ s : Multiset ℝ,
      RealRooted ((s.map (fun r => X - C r)).prod).reverse := by
    intro s
    induction s using Multiset.induction with
    | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero]
      rw [← C_1, reverse_C]; exact realRooted_C 1
    | cons r t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain]
      refine RealRooted.mul ?_ ih
      have hd : ((X - C r : Polynomial ℝ).reverse).natDegree ≤ 1 :=
        le_trans (reverse_natDegree_le _) (by rw [natDegree_X_sub_C])
      exact Splits.of_natDegree_le_one hd
  -- p = C lc · ∏ (X - C r); reverse distributes, reverse (C lc) = C lc
  have hfact : C p.leadingCoeff * (p.roots.map (fun r => X - C r)).prod = p :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C (realRooted_iff_card_roots.mp hp)
  have hrev : p.reverse
      = C p.leadingCoeff * ((p.roots.map (fun r => X - C r)).prod).reverse := by
    conv_lhs => rw [← hfact]
    rw [reverse_mul_of_domain, reverse_C]
  rw [hrev]
  exact RealRooted.mul (realRooted_C _) (key p.roots)

/-- **(2) Base case.** A real-rooted real quadratic `a x² + b x + c` (a ≠ 0) has `b² - 4ac ≥ 0`. -/
public theorem realRooted_quadratic_discrim {a b c : ℝ} (ha : a ≠ 0)
    (h : RealRooted (C a * X ^ 2 + C b * X + C c)) :
    b ^ 2 - 4 * a * c ≥ 0 := by
  set q := C a * X ^ 2 + C b * X + C c with hq
  -- q has degree 2, hence is nonzero
  have hdeg : q.degree = 2 := degree_quadratic ha
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0, degree_zero] at hdeg; exact absurd hdeg (by decide)
  have hnat : q.natDegree = 2 := natDegree_eq_of_degree_eq_some hdeg
  -- real-rootedness ⟹ #roots = natDegree = 2 > 0, so a real root exists
  have hcard : q.roots.card = q.natDegree := realRooted_iff_card_roots.mp h
  rw [hnat] at hcard
  have hne : q.roots ≠ 0 := by
    intro h0; rw [h0, Multiset.card_zero] at hcard; exact absurd hcard (by decide)
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
  have hroot : q.IsRoot x := (mem_roots hq0).mp hx
  -- evaluate: a x² + b x + c = 0
  have he : a * x ^ 2 + b * x + c = 0 := by
    have h2 : q.eval x = 0 := hroot
    rw [hq] at h2
    simpa [eval_add, eval_mul, eval_pow, eval_C, eval_X] using h2
  -- b² − 4ac = (2ax+b)² − 4a·(a x²+b x+c) = (2ax+b)² ≥ 0
  have key : b ^ 2 - 4 * a * c
      = (2 * a * x + b) ^ 2 - 4 * a * (a * x ^ 2 + b * x + c) := by ring
  rw [he, mul_zero, sub_zero] at key
  rw [key]
  exact sq_nonneg _

/-- **Real-rootedness is preserved by iterated differentiation** (iterate Rolle). -/
public theorem RealRooted.iterate_derivative (hp : RealRooted p) (k : ℕ) :
    RealRooted (Polynomial.derivative^[k] p) := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact RealRooted.derivative ih

/-- **(2′) Base case, coefficient form.** A real-rooted polynomial of `natDegree ≤ 2` satisfies the
discriminant inequality on its low coefficients: `a₁² ≥ 4 a₂ a₀`. (For `natDegree < 2` the leading
`a₂ = 0` makes it `a₁² ≥ 0`.) This is the form the reduction below consumes. -/
public theorem realRooted_discrim_coeff {q : Polynomial ℝ} (hq : RealRooted q)
    (hdeg : q.natDegree ≤ 2) :
    q.coeff 1 ^ 2 ≥ 4 * q.coeff 2 * q.coeff 0 := by
  by_cases hc2 : q.coeff 2 = 0
  · rw [hc2]; simpa using sq_nonneg (q.coeff 1)
  · have h2 : q.natDegree = 2 := le_antisymm hdeg (le_natDegree_of_ne_zero hc2)
    have hq0 : q ≠ 0 := fun h => hc2 (by rw [h]; simp)
    have hcard : q.roots.card = 2 := by rw [realRooted_iff_card_roots.mp hq, h2]
    have hne : q.roots ≠ 0 := by
      intro h0; rw [h0, Multiset.card_zero] at hcard; exact absurd hcard (by decide)
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
    have hroot : q.IsRoot x := (mem_roots hq0).mp hx
    have he : q.coeff 0 + q.coeff 1 * x + q.coeff 2 * x ^ 2 = 0 := by
      have h3 : q.natDegree < 3 := by omega
      have hev : q.eval x = 0 := hroot
      rw [eval_eq_sum_range' h3] at hev
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, mul_one, pow_one,
        zero_add] at hev
      linarith [hev]
    have key : q.coeff 1 ^ 2 - 4 * q.coeff 2 * q.coeff 0
        = (2 * q.coeff 2 * x + q.coeff 1) ^ 2
          - 4 * q.coeff 2 * (q.coeff 0 + q.coeff 1 * x + q.coeff 2 * x ^ 2) := by ring
    rw [he, mul_zero, sub_zero] at key
    linarith [sq_nonneg (2 * q.coeff 2 * x + q.coeff 1), key]

/-- **Newton's inequalities, coefficient form.** For a real-rooted real polynomial `p` of degree
`n`, the coefficients `aⱼ = p.coeff j` satisfy, for `1 ≤ i ≤ n-1`,
`a_i² · C(n,i-1)·C(n,i+1) ≥ a_{i-1}·a_{i+1} · C(n,i)²`.

Proof (the classical reduction): `g := Dᴺ⁻²(reverse(Dⁱ⁻¹ p))` with `N = n-i+1` is a real-rooted
polynomial of `natDegree ≤ 2` whose three low coefficients are factorial multiples of
`a_{i-1}, a_i, a_{i+1}`; its discriminant `b²-4ac ≥ 0` (`realRooted_discrim_coeff`) is exactly this
inequality after clearing positive factorials (`Nat.choose_mul_factorial_mul_factorial`). -/
public theorem newton_inequality_coeff (hp : RealRooted p) {i : ℕ}
    (hi : 1 ≤ i) (hi2 : i + 1 ≤ p.natDegree) :
    (p.coeff i) ^ 2 * ((p.natDegree.choose (i - 1) : ℝ) * (p.natDegree.choose (i + 1) : ℝ))
      ≥ (p.coeff (i - 1) * p.coeff (i + 1)) * (p.natDegree.choose i : ℝ) ^ 2 := by
  set n := p.natDegree with hn_def
  set N := n - (i - 1) with hN_def
  have hi_le : i ≤ n := by omega
  have hN2 : 2 ≤ N := by omega
  -- exact degree of iterated derivatives over ℝ (char 0)
  have hnd : ∀ j, j ≤ n → (Polynomial.derivative^[j] p).natDegree = n - j := by
    intro j
    induction j with
    | zero => intro _; simp only [Function.iterate_zero_apply, Nat.sub_zero, hn_def]
    | succ j ih =>
        intro hj
        have hj' : j ≤ n := Nat.le_of_succ_le hj
        have hpos : 0 < (Polynomial.derivative^[j] p).natDegree := by rw [ih hj']; omega
        rw [Function.iterate_succ_apply']
        have hd := degree_derivative_eq (Polynomial.derivative^[j] p) hpos
        rw [ih hj'] at hd
        rw [natDegree_eq_of_degree_eq_some hd]; omega
  have hqN : (Polynomial.derivative^[i - 1] p).natDegree = N := by
    rw [hN_def]; exact hnd (i - 1) (by omega)
  -- the three coefficients of q = D^[i-1] p
  have hq0 : (Polynomial.derivative^[i - 1] p).coeff 0
      = (((i - 1).descFactorial (i - 1) : ℕ) : ℝ) * p.coeff (i - 1) := by
    rw [coeff_iterate_derivative, nsmul_eq_mul, Nat.zero_add]
  have hq1 : (Polynomial.derivative^[i - 1] p).coeff 1
      = ((i.descFactorial (i - 1) : ℕ) : ℝ) * p.coeff i := by
    rw [coeff_iterate_derivative, nsmul_eq_mul, show 1 + (i - 1) = i from by omega]
  have hq2 : (Polynomial.derivative^[i - 1] p).coeff 2
      = (((i + 1).descFactorial (i - 1) : ℕ) : ℝ) * p.coeff (i + 1) := by
    rw [coeff_iterate_derivative, nsmul_eq_mul, show 2 + (i - 1) = i + 1 from by omega]
  -- the three coefficients of g = D^[N-2] (reverse q), in terms of q's coefficients
  have hg1q : (Polynomial.derivative^[N - 2] ((Polynomial.derivative^[i - 1] p).reverse)).coeff 1
      = (((N - 1).descFactorial (N - 2) : ℕ) : ℝ) * (Polynomial.derivative^[i - 1] p).coeff 1 := by
    rw [coeff_iterate_derivative, nsmul_eq_mul, show 1 + (N - 2) = N - 1 from by omega]
    congr 1
    rw [coeff_reverse, hqN, revAt_le (show N - 1 ≤ N from by omega), show N - (N - 1) = 1 from by omega]
  have hg2q : (Polynomial.derivative^[N - 2] ((Polynomial.derivative^[i - 1] p).reverse)).coeff 2
      = ((N.descFactorial (N - 2) : ℕ) : ℝ) * (Polynomial.derivative^[i - 1] p).coeff 0 := by
    rw [coeff_iterate_derivative, nsmul_eq_mul, show 2 + (N - 2) = N from by omega]
    congr 1
    rw [coeff_reverse, hqN, revAt_le (le_refl N), Nat.sub_self]
  have hg0q : (Polynomial.derivative^[N - 2] ((Polynomial.derivative^[i - 1] p).reverse)).coeff 0
      = (((N - 2).descFactorial (N - 2) : ℕ) : ℝ) * (Polynomial.derivative^[i - 1] p).coeff 2 := by
    rw [coeff_iterate_derivative, nsmul_eq_mul, Nat.zero_add]
    congr 1
    rw [coeff_reverse, hqN, revAt_le (show N - 2 ≤ N from by omega), show N - (N - 2) = 2 from by omega]
  -- g is real-rooted of natDegree ≤ 2
  have hq_rr : RealRooted (Polynomial.derivative^[i - 1] p) := RealRooted.iterate_derivative hp (i - 1)
  have hr_rr : RealRooted ((Polynomial.derivative^[i - 1] p).reverse) := RealRooted.reverse hq_rr
  have hg : RealRooted (Polynomial.derivative^[N - 2] ((Polynomial.derivative^[i - 1] p).reverse)) :=
    RealRooted.iterate_derivative hr_rr (N - 2)
  have hgdeg :
      (Polynomial.derivative^[N - 2] ((Polynomial.derivative^[i - 1] p).reverse)).natDegree ≤ 2 := by
    have h1 := natDegree_iterate_derivative ((Polynomial.derivative^[i - 1] p).reverse) (N - 2)
    have h2 := reverse_natDegree_le (Polynomial.derivative^[i - 1] p)
    rw [hqN] at h2
    omega
  -- descFactorial → factorial bookkeeping
  have d_i : i.descFactorial (i - 1) = i ! := by
    have h := Nat.factorial_mul_descFactorial (show i - 1 ≤ i from by omega)
    rw [show i - (i - 1) = 1 from by omega, Nat.factorial_one, one_mul] at h; exact h
  have d_Nm : (N - 1).descFactorial (N - 2) = (N - 1)! := by
    have h := Nat.factorial_mul_descFactorial (show N - 2 ≤ N - 1 from by omega)
    rw [show (N - 1) - (N - 2) = 1 from by omega, Nat.factorial_one, one_mul] at h; exact h
  have d_imself : (i - 1).descFactorial (i - 1) = (i - 1)! := Nat.descFactorial_self _
  have d_N2self : (N - 2).descFactorial (N - 2) = (N - 2)! := Nat.descFactorial_self _
  have d_N : (2 : ℝ) * ((N.descFactorial (N - 2) : ℕ) : ℝ) = ((N ! : ℕ) : ℝ) := by
    have h := Nat.factorial_mul_descFactorial (show N - 2 ≤ N from by omega)
    rw [show N - (N - 2) = 2 from by omega, Nat.factorial_two] at h
    exact_mod_cast h
  have d_ip : (2 : ℝ) * (((i + 1).descFactorial (i - 1) : ℕ) : ℝ) = (((i + 1)! : ℕ) : ℝ) := by
    have h := Nat.factorial_mul_descFactorial (show i - 1 ≤ i + 1 from by omega)
    rw [show (i + 1) - (i - 1) = 2 from by omega, Nat.factorial_two] at h
    exact_mod_cast h
  have hprod : (4 : ℝ) * ((N.descFactorial (N - 2) : ℕ) : ℝ) * (((i + 1).descFactorial (i - 1) : ℕ) : ℝ)
      = ((N ! : ℕ) : ℝ) * (((i + 1)! : ℕ) : ℝ) := by
    linear_combination (2 * (((i + 1).descFactorial (i - 1) : ℕ) : ℝ)) * d_N + ((N ! : ℕ) : ℝ) * d_ip
  -- assemble the discriminant inequality, rewrite to clean factorial form
  have hbase := realRooted_discrim_coeff hg hgdeg
  rw [hg1q, hg2q, hg0q, hq1, hq0, hq2, d_Nm, d_i, d_imself, d_N2self] at hbase
  have hl : (((N - 1)! : ℝ) * ((i ! : ℝ) * p.coeff i)) ^ 2
      = (p.coeff i) ^ 2 * ((i ! : ℝ) ^ 2 * ((N - 1)! : ℝ) ^ 2) := by ring
  have hr : 4 * (((N.descFactorial (N - 2) : ℕ) : ℝ) * (((i - 1)! : ℝ) * p.coeff (i - 1)))
        * (((N - 2)! : ℝ) * ((((i + 1).descFactorial (i - 1) : ℕ) : ℝ) * p.coeff (i + 1)))
      = (p.coeff (i - 1) * p.coeff (i + 1))
        * (((i - 1)! : ℝ) * (N ! : ℝ) * ((i + 1)! : ℝ) * ((N - 2)! : ℝ)) := by
    linear_combination (((i - 1)! : ℝ) * ((N - 2)! : ℝ) * p.coeff (i - 1) * p.coeff (i + 1)) * hprod
  rw [hl, hr] at hbase
  -- hbase is now the clean factorial discriminant (hD)
  -- binomial identities
  have ch_i : n.choose i * (i ! * (N - 1)!) = n ! := by
    have h := Nat.choose_mul_factorial_mul_factorial hi_le
    rw [show n - i = N - 1 from by omega, mul_assoc] at h; exact h
  have ch_im : n.choose (i - 1) * ((i - 1)! * N !) = n ! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show i - 1 ≤ n from by omega)
    rw [show n - (i - 1) = N from by omega, mul_assoc] at h; exact h
  have ch_ip : n.choose (i + 1) * ((i + 1)! * (N - 2)!) = n ! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show i + 1 ≤ n from by omega)
    rw [show n - (i + 1) = N - 2 from by omega, mul_assoc] at h; exact h
  have ci_eq : (n.choose i : ℝ) * ((i ! : ℝ) * ((N - 1)! : ℝ)) = (n ! : ℝ) := by exact_mod_cast ch_i
  have cim_eq : (n.choose (i - 1) : ℝ) * (((i - 1)! : ℝ) * (N ! : ℝ)) = (n ! : ℝ) := by
    exact_mod_cast ch_im
  have cip_eq : (n.choose (i + 1) : ℝ) * (((i + 1)! : ℝ) * ((N - 2)! : ℝ)) = (n ! : ℝ) := by
    exact_mod_cast ch_ip
  -- positivity
  have hfi : (0 : ℝ) < (i ! : ℝ) := by exact_mod_cast i.factorial_pos
  have hfim : (0 : ℝ) < ((i - 1)! : ℝ) := by exact_mod_cast (i - 1).factorial_pos
  have hfip : (0 : ℝ) < ((i + 1)! : ℝ) := by exact_mod_cast (i + 1).factorial_pos
  have hfN : (0 : ℝ) < (N ! : ℝ) := by exact_mod_cast N.factorial_pos
  have hfNm : (0 : ℝ) < ((N - 1)! : ℝ) := by exact_mod_cast (N - 1).factorial_pos
  have hfN2 : (0 : ℝ) < ((N - 2)! : ℝ) := by exact_mod_cast (N - 2).factorial_pos
  have hfn : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have hK1 : (0 : ℝ) < ((i ! : ℝ) * ((N - 1)! : ℝ)) ^ 2 := pow_pos (mul_pos hfi hfNm) 2
  have hK2 : (0 : ℝ) < ((i - 1)! : ℝ) * (N ! : ℝ) * ((i + 1)! : ℝ) * ((N - 2)! : ℝ) :=
    mul_pos (mul_pos (mul_pos hfim hfN) hfip) hfN2
  -- rewrite the choose-products via the binomial identities, clear denominators, conclude
  have hcI2 : (n.choose i : ℝ) ^ 2 = (n ! : ℝ) ^ 2 / ((i ! : ℝ) * ((N - 1)! : ℝ)) ^ 2 := by
    rw [eq_div_iff (ne_of_gt hK1), ← ci_eq]; ring
  have hcImcIp : (n.choose (i - 1) : ℝ) * (n.choose (i + 1) : ℝ)
      = (n ! : ℝ) ^ 2 / (((i - 1)! : ℝ) * (N ! : ℝ) * ((i + 1)! : ℝ) * ((N - 2)! : ℝ)) := by
    rw [eq_div_iff (ne_of_gt hK2)]
    have hnn : (n ! : ℝ) ^ 2
        = ((n.choose (i - 1) : ℝ) * (((i - 1)! : ℝ) * (N ! : ℝ)))
          * ((n.choose (i + 1) : ℝ) * (((i + 1)! : ℝ) * ((N - 2)! : ℝ))) := by
      rw [cim_eq, cip_eq]; ring
    linear_combination -hnn
  rw [hcI2, hcImcIp, ge_iff_le, ← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ hK1 hK2]
  nlinarith [hbase, sq_nonneg (n ! : ℝ), hfn]

/-- **(3) Newton's inequalities.** For a monic real-rooted polynomial of degree `n` with roots
multiset `s = p.roots`, for `1 ≤ k ≤ n-1`,
`e_k(s)² · C(n,k-1)·C(n,k+1) ≥ e_{k-1}(s)·e_{k+1}(s) · C(n,k)²`. -/
public theorem newton_inequality (hp : RealRooted p) (hmonic : p.Monic)
    {k : ℕ} (hk : 1 ≤ k) (hk2 : k + 1 ≤ p.natDegree) :
    (p.roots.esymm k) ^ 2 * ((p.natDegree.choose (k - 1) : ℝ) * (p.natDegree.choose (k + 1) : ℝ))
      ≥ (p.roots.esymm (k - 1)) * (p.roots.esymm (k + 1)) * ((p.natDegree.choose k : ℝ)) ^ 2 := by
  set n := p.natDegree with hn_def
  have hcard : Multiset.card p.roots = n := realRooted_iff_card_roots.mp hp
  have hk_le : k ≤ n := by omega
  -- Vieta: esymm m = (-1)^m · coeff (n-m) for a monic real-rooted polynomial
  have key : ∀ m, m ≤ n → p.roots.esymm m = (-1 : ℝ) ^ m * p.coeff (n - m) := by
    intro m hm
    have h := coeff_eq_esymm_roots_of_card hcard (Nat.sub_le n m)
    rw [hmonic, show n - (n - m) = m from by omega, one_mul] at h
    have hsq : ((-1 : ℝ) ^ m) * ((-1 : ℝ) ^ m) = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨m, rfl⟩
    calc p.roots.esymm m = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) * p.roots.esymm m := by rw [hsq, one_mul]
      _ = (-1 : ℝ) ^ m * ((-1 : ℝ) ^ m * p.roots.esymm m) := by ring
      _ = (-1 : ℝ) ^ m * p.coeff (n - m) := by rw [← h]
  -- the squared / product esymm terms reduce to coefficients (signs cancel)
  have sq_k : (p.roots.esymm k) ^ 2 = (p.coeff (n - k)) ^ 2 := by
    rw [key k hk_le, mul_pow, ← pow_mul, Even.neg_one_pow ⟨k, by ring⟩, one_mul]
  have prod_pm : (p.roots.esymm (k - 1)) * (p.roots.esymm (k + 1))
      = p.coeff (n - (k - 1)) * p.coeff (n - (k + 1)) := by
    rw [key (k - 1) (by omega), key (k + 1) (by omega)]
    have hs : ((-1 : ℝ) ^ (k - 1)) * ((-1 : ℝ) ^ (k + 1)) = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨k, by omega⟩
    calc (-1 : ℝ) ^ (k - 1) * p.coeff (n - (k - 1))
          * ((-1 : ℝ) ^ (k + 1) * p.coeff (n - (k + 1)))
        = ((-1 : ℝ) ^ (k - 1) * (-1 : ℝ) ^ (k + 1))
          * (p.coeff (n - (k - 1)) * p.coeff (n - (k + 1))) := by ring
      _ = p.coeff (n - (k - 1)) * p.coeff (n - (k + 1)) := by rw [hs, one_mul]
  -- reindex binomials and coefficient indices to match the coefficient-form lemma at i = n - k
  have ci1 : n.choose (k - 1) = n.choose ((n - k) + 1) := by
    rw [show (n - k) + 1 = n - (k - 1) from by omega]; exact (Nat.choose_symm (by omega)).symm
  have ci2 : n.choose (k + 1) = n.choose ((n - k) - 1) := by
    rw [show (n - k) - 1 = n - (k + 1) from by omega]; exact (Nat.choose_symm (by omega)).symm
  have ci3 : n.choose k = n.choose (n - k) := (Nat.choose_symm hk_le).symm
  have hidx1 : n - (k - 1) = (n - k) + 1 := by omega
  have hidx2 : n - (k + 1) = (n - k) - 1 := by omega
  rw [sq_k, prod_pm, ci1, ci2, ci3, hidx1, hidx2]
  have H := newton_inequality_coeff hp (i := n - k) (by omega) (by omega)
  rw [mul_comm (p.coeff ((n - k) + 1)) (p.coeff ((n - k) - 1)),
    mul_comm ((n.choose ((n - k) + 1) : ℝ)) ((n.choose ((n - k) - 1) : ℝ))]
  exact H

/-- **Corollary (log-concavity of normalized means).** `p_{k-1} · p_{k+1} ≤ p_k²`. -/
public theorem newton_logConcave (hp : RealRooted p) (hmonic : p.Monic)
    {k : ℕ} (hk : 1 ≤ k) (hk2 : k + 1 ≤ p.natDegree) :
    (p.roots.esymm (k - 1) / (p.natDegree.choose (k - 1) : ℝ)) *
      (p.roots.esymm (k + 1) / (p.natDegree.choose (k + 1) : ℝ))
      ≤ (p.roots.esymm k / (p.natDegree.choose k : ℝ)) ^ 2 := by
  set n := p.natDegree with hn_def
  have H := newton_inequality hp hmonic hk hk2
  have hc1 : (0 : ℝ) < (n.choose (k - 1) : ℝ) := by exact_mod_cast Nat.choose_pos (show k - 1 ≤ n by omega)
  have hc2 : (0 : ℝ) < (n.choose (k + 1) : ℝ) := by exact_mod_cast Nat.choose_pos (show k + 1 ≤ n by omega)
  have hck : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos (show k ≤ n by omega)
  rw [div_mul_div_comm, div_pow, div_le_div_iff₀ (mul_pos hc1 hc2) (pow_pos hck 2)]
  linarith [H]

end Newton
