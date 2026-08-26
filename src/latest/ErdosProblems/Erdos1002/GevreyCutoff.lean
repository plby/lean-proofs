import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A quantitative Gevrey precursor for the flat exponential cutoff

`expNegInvGlue` is the standard one-sided flat function
`x ↦ exp (-1/x)` for `x > 0`, extended by zero to `x ≤ 0`.  Its existing
smoothness theorem does not, by itself, control derivatives whose order is
allowed to grow.  This file records the exact polynomial recurrence for all
of its derivatives and proves quantitative coefficient bounds for those
polynomials.

No estimate is inferred from an abstract `ContDiffBump`.
-/

open Filter Polynomial Real Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- Polynomial multiplying `expNegInvGlue` in its `n`-th derivative.
The recurrence is exactly the one used in mathlib's smoothness proof. -/
def expNegInvDerivativePoly : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X ^ 2 *
      (expNegInvDerivativePoly n -
        derivative (expNegInvDerivativePoly n))

@[simp]
theorem expNegInvDerivativePoly_zero :
    expNegInvDerivativePoly 0 = 1 := rfl

@[simp]
theorem expNegInvDerivativePoly_succ (n : ℕ) :
    expNegInvDerivativePoly (n + 1) = X ^ 2 *
      (expNegInvDerivativePoly n -
        derivative (expNegInvDerivativePoly n)) := rfl

/-- Exact formula for every classical derivative, valid also at and to the
left of the flat gluing point. -/
theorem iteratedDeriv_expNegInvGlue (n : ℕ) (x : ℝ) :
    iteratedDeriv n expNegInvGlue x =
      (expNegInvDerivativePoly n).eval x⁻¹ * expNegInvGlue x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n expNegInvGlue =
          fun y : ℝ ↦
            (expNegInvDerivativePoly n).eval y⁻¹ * expNegInvGlue y :=
        funext ih
      rw [hfun]
      exact (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
        (expNegInvDerivativePoly n) x).deriv

/-- The multiplier polynomial in the `n`-th derivative has degree at most
`2n`. -/
theorem natDegree_expNegInvDerivativePoly_le (n : ℕ) :
    (expNegInvDerivativePoly n).natDegree ≤ 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [expNegInvDerivativePoly_succ]
      calc
        (X ^ 2 *
            (expNegInvDerivativePoly n -
              derivative (expNegInvDerivativePoly n))).natDegree ≤
            (X ^ 2).natDegree +
              (expNegInvDerivativePoly n -
                derivative (expNegInvDerivativePoly n)).natDegree :=
          natDegree_mul_le
        _ ≤ 2 + max (expNegInvDerivativePoly n).natDegree
              (derivative (expNegInvDerivativePoly n)).natDegree := by
          gcongr
          · simp
          · exact natDegree_sub_le _ _
        _ ≤ 2 + 2 * n := by
          gcongr
          apply max_le ih
          exact (natDegree_derivative_le _).trans (by omega :
            (expNegInvDerivativePoly n).natDegree - 1 ≤ 2 * n)
        _ = 2 * (n + 1) := by omega

/-- Coefficient recurrence away from the two forced initial zeros. -/
theorem coeff_expNegInvDerivativePoly_succ_of_two_le
    (n k : ℕ) (hk : 2 ≤ k) :
    (expNegInvDerivativePoly (n + 1)).coeff k =
      (expNegInvDerivativePoly n).coeff (k - 2) -
        (expNegInvDerivativePoly n).coeff (k - 1) *
          ((k - 1 : ℕ) : ℝ) := by
  rw [expNegInvDerivativePoly_succ,
    Polynomial.coeff_X_pow_mul']
  simp only [if_pos hk, Polynomial.coeff_sub,
    Polynomial.coeff_derivative]
  have hkidx : k - 2 + 1 = k - 1 := by omega
  have hkidxR : ((k - 2 : ℕ) : ℝ) + 1 =
      ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hkidx
  rw [hkidx, hkidxR]

/-- The factor `X²` forces the first two coefficients to vanish. -/
theorem coeff_expNegInvDerivativePoly_succ_of_lt_two
    (n k : ℕ) (hk : k < 2) :
    (expNegInvDerivativePoly (n + 1)).coeff k = 0 := by
  rw [expNegInvDerivativePoly_succ,
    Polynomial.coeff_X_pow_mul']
  exact if_neg (not_le.mpr hk)

/-- Target pointwise majorant for the factorial-weighted coefficients. -/
def expNegInvCoeffMajorant (n : ℕ) : ℝ :=
  8 ^ n * (n.factorial : ℝ) ^ 2

theorem expNegInvCoeffMajorant_nonneg (n : ℕ) :
    0 ≤ expNegInvCoeffMajorant n := by
  unfold expNegInvCoeffMajorant
  positivity

private theorem cast_factorial_eq_mul_pred_factorial
    (k : ℕ) (hk : 0 < k) :
    (k.factorial : ℝ) =
      (k : ℝ) * ((k - 1).factorial : ℝ) := by
  have hkEq : k = (k - 1) + 1 := by omega
  nth_rewrite 1 [hkEq]
  rw [Nat.factorial_succ]
  push_cast
  have hkEqR : (((k - 1) : ℕ) : ℝ) + 1 = (k : ℝ) := by
    exact_mod_cast hkEq.symm
  rw [hkEqR]

private theorem cast_factorial_eq_mul_pred_mul_predpred_factorial
    (k : ℕ) (hk : 2 ≤ k) :
    (k.factorial : ℝ) =
      (k : ℝ) * ((k - 1 : ℕ) : ℝ) *
        ((k - 2).factorial : ℝ) := by
  rw [cast_factorial_eq_mul_pred_factorial k (by omega),
    cast_factorial_eq_mul_pred_factorial (k - 1) (by omega)]
  have hpred : k - 1 - 1 = k - 2 := by omega
  rw [hpred]
  ring

/-- Every coefficient of the derivative polynomial obeys a factorially
weighted Gevrey-2 bound.  The constant `8` comes directly from the two
terms in the recurrence and the degree bound `deg Pₙ ≤ 2n`. -/
theorem abs_coeff_expNegInvDerivativePoly_mul_factorial_le
    (n k : ℕ) :
    |(expNegInvDerivativePoly n).coeff k| * (k.factorial : ℝ) ≤
      expNegInvCoeffMajorant n := by
  induction n generalizing k with
  | zero =>
      by_cases hk : k = 0
      · subst k
        norm_num [expNegInvCoeffMajorant]
      · simp [expNegInvDerivativePoly, Polynomial.coeff_one, hk,
          expNegInvCoeffMajorant]
  | succ n ih =>
      by_cases hlarge : 2 * (n + 1) < k
      · have hcoeff : (expNegInvDerivativePoly (n + 1)).coeff k = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt
            ((natDegree_expNegInvDerivativePoly_le (n + 1)).trans_lt hlarge)
        rw [hcoeff, abs_zero, zero_mul]
        exact expNegInvCoeffMajorant_nonneg (n + 1)
      · have hkUpper : k ≤ 2 * (n + 1) := by omega
        by_cases hkTwo : 2 ≤ k
        · rw [coeff_expNegInvDerivativePoly_succ_of_two_le n k hkTwo]
          let a : ℝ := |(expNegInvDerivativePoly n).coeff (k - 2)|
          let b : ℝ := |(expNegInvDerivativePoly n).coeff (k - 1)|
          let M : ℝ := expNegInvCoeffMajorant n
          let R : ℝ := (k : ℝ) * ((k - 1 : ℕ) : ℝ)
          have ha : a * ((k - 2).factorial : ℝ) ≤ M := by
            simpa only [a, M] using! ih (k - 2)
          have hb : b * ((k - 1).factorial : ℝ) ≤ M := by
            simpa only [b, M] using! ih (k - 1)
          have hRnonneg : 0 ≤ R := by
            dsimp [R]
            positivity
          have htermA : a * (k.factorial : ℝ) =
              (a * ((k - 2).factorial : ℝ)) * R := by
            rw [cast_factorial_eq_mul_pred_mul_predpred_factorial k hkTwo]
            dsimp [R]
            ring
          have htermB :
              |(expNegInvDerivativePoly n).coeff (k - 1) *
                  ((k - 1 : ℕ) : ℝ)| * (k.factorial : ℝ) =
                (b * ((k - 1).factorial : ℝ)) * R := by
            have hcastAbs : |(((k - 1 : ℕ) : ℝ))| =
                ((k - 1 : ℕ) : ℝ) :=
              abs_of_nonneg (Nat.cast_nonneg _)
            rw [abs_mul, hcastAbs,
              cast_factorial_eq_mul_pred_factorial k (by omega)]
            dsimp [b, R]
            ring
          have hR : R ≤ 4 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
            have hkR : (k : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
              exact_mod_cast hkUpper
            have hkPredR : ((k - 1 : ℕ) : ℝ) ≤
                2 * ((n + 1 : ℕ) : ℝ) := by
              exact_mod_cast (show k - 1 ≤ 2 * (n + 1) by omega)
            dsimp [R]
            calc
              (k : ℝ) * ((k - 1 : ℕ) : ℝ) ≤
                  (2 * ((n + 1 : ℕ) : ℝ)) *
                    (2 * ((n + 1 : ℕ) : ℝ)) := by
                gcongr
              _ = 4 * ((n + 1 : ℕ) : ℝ) ^ 2 := by ring
          have hMnonneg : 0 ≤ M := by
            exact expNegInvCoeffMajorant_nonneg n
          have hmajorantStep :
              8 * ((n + 1 : ℕ) : ℝ) ^ 2 * M =
                expNegInvCoeffMajorant (n + 1) := by
            dsimp [M, expNegInvCoeffMajorant]
            rw [pow_succ, Nat.factorial_succ]
            push_cast
            ring
          calc
            |(expNegInvDerivativePoly n).coeff (k - 2) -
                (expNegInvDerivativePoly n).coeff (k - 1) *
                  ((k - 1 : ℕ) : ℝ)| * (k.factorial : ℝ) ≤
                (a + |(expNegInvDerivativePoly n).coeff (k - 1) *
                  ((k - 1 : ℕ) : ℝ)|) * (k.factorial : ℝ) := by
              gcongr
              exact abs_sub _ _
            _ = (a * ((k - 2).factorial : ℝ) +
                  b * ((k - 1).factorial : ℝ)) * R := by
              rw [add_mul, htermA, htermB, ← add_mul]
            _ ≤ (M + M) * R := by
              gcongr
            _ ≤ (M + M) * (4 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
              gcongr
            _ = 8 * ((n + 1 : ℕ) : ℝ) ^ 2 * M := by ring
            _ = expNegInvCoeffMajorant (n + 1) := hmajorantStep
        · have hkLt : k < 2 := by omega
          rw [coeff_expNegInvDerivativePoly_succ_of_lt_two n k hkLt,
            abs_zero, zero_mul]
          exact expNegInvCoeffMajorant_nonneg (n + 1)

/-- Elementary exponential damping of one monomial. -/
theorem pow_mul_exp_neg_le_factorial
    (t : ℝ) (k : ℕ) (ht : 0 ≤ t) :
    t ^ k * Real.exp (-t) ≤ (k.factorial : ℝ) := by
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hpow : t ^ k ≤ Real.exp t * (k.factorial : ℝ) :=
    (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp t ht k)
  calc
    t ^ k * Real.exp (-t) ≤
        (Real.exp t * (k.factorial : ℝ)) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = (k.factorial : ℝ) := by
      rw [mul_assoc, mul_comm (k.factorial : ℝ), ← mul_assoc,
        ← Real.exp_add]
      simp

private theorem two_mul_add_one_le_three_pow (n : ℕ) :
    2 * n + 1 ≤ 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      omega

/-- The derivative polynomial, after multiplication by the flat
exponential, has a uniform Gevrey-2 bound on the nonnegative half-line. -/
theorem abs_eval_expNegInvDerivativePoly_mul_exp_neg_le
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    |(expNegInvDerivativePoly n).eval t| * Real.exp (-t) ≤
      24 ^ n * (n.factorial : ℝ) ^ 2 := by
  have hdeg : (expNegInvDerivativePoly n).natDegree < 2 * n + 1 :=
    (natDegree_expNegInvDerivativePoly_le n).trans_lt (by omega)
  rw [Polynomial.eval_eq_sum_range' hdeg t]
  calc
    |∑ i ∈ Finset.range (2 * n + 1),
        (expNegInvDerivativePoly n).coeff i * t ^ i| * Real.exp (-t) ≤
        (∑ i ∈ Finset.range (2 * n + 1),
          |(expNegInvDerivativePoly n).coeff i * t ^ i|) *
            Real.exp (-t) := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (2 * n + 1),
        |(expNegInvDerivativePoly n).coeff i| *
          (t ^ i * Real.exp (-t)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul, abs_pow, abs_of_nonneg ht]
      ring
    _ ≤ ∑ _i ∈ Finset.range (2 * n + 1),
        expNegInvCoeffMajorant n := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        |(expNegInvDerivativePoly n).coeff i| *
            (t ^ i * Real.exp (-t)) ≤
            |(expNegInvDerivativePoly n).coeff i| *
              (i.factorial : ℝ) := by
          gcongr
          exact pow_mul_exp_neg_le_factorial t i ht
        _ ≤ expNegInvCoeffMajorant n :=
          abs_coeff_expNegInvDerivativePoly_mul_factorial_le n i
    _ = ((2 * n + 1 : ℕ) : ℝ) * expNegInvCoeffMajorant n := by
      simp
    _ ≤ ((3 ^ n : ℕ) : ℝ) * expNegInvCoeffMajorant n := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast two_mul_add_one_le_three_pow n
      · exact expNegInvCoeffMajorant_nonneg n
    _ = 24 ^ n * (n.factorial : ℝ) ^ 2 := by
      unfold expNegInvCoeffMajorant
      push_cast
      rw [← mul_assoc, ← mul_pow]
      norm_num

/-- Global quantitative Gevrey-2 estimate for the one-sided flat profile.
In particular, this controls derivative orders that grow with an external
parameter; it is strictly stronger than `ContDiff`.-/
theorem abs_iteratedDeriv_expNegInvGlue_le (n : ℕ) (x : ℝ) :
    |iteratedDeriv n expNegInvGlue x| ≤
      24 ^ n * (n.factorial : ℝ) ^ 2 := by
  rw [iteratedDeriv_expNegInvGlue]
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx, mul_zero, abs_zero]
    positivity
  · have hxpos : 0 < x := lt_of_not_ge hx
    have hinv : 0 ≤ x⁻¹ := (inv_pos.mpr hxpos).le
    rw [expNegInvGlue]
    simp only [if_neg hx]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact abs_eval_expNegInvDerivativePoly_mul_exp_neg_le n x⁻¹ hinv

/-- The same estimate in the conventional `C^(n+1) (n!)²` format. -/
theorem abs_iteratedDeriv_expNegInvGlue_le_gevreyForm
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv n expNegInvGlue x| ≤
      24 ^ (n + 1) * (n.factorial : ℝ) ^ 2 := by
  calc
    |iteratedDeriv n expNegInvGlue x| ≤
        24 ^ n * (n.factorial : ℝ) ^ 2 :=
      abs_iteratedDeriv_expNegInvGlue_le n x
    _ ≤ 24 ^ (n + 1) * (n.factorial : ℝ) ^ 2 := by
      gcongr
      · norm_num
      · exact Nat.le_succ n

/-! ## An explicit compactly supported profile -/

/-- A symmetric compactly supported bump made only from the quantitatively
controlled flat exponential. -/
def gevreyCompactBump (x : ℝ) : ℝ :=
  expNegInvGlue x * expNegInvGlue (1 - x)

theorem gevreyCompactBump_eq_zero_of_nonpos
    {x : ℝ} (hx : x ≤ 0) :
    gevreyCompactBump x = 0 := by
  rw [gevreyCompactBump, expNegInvGlue.zero_of_nonpos hx, zero_mul]

theorem gevreyCompactBump_eq_zero_of_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    gevreyCompactBump x = 0 := by
  rw [gevreyCompactBump,
    expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr hx), mul_zero]

theorem gevreyCompactBump_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < gevreyCompactBump x := by
  unfold gevreyCompactBump
  exact mul_pos (expNegInvGlue.pos_of_pos hx0)
    (expNegInvGlue.pos_of_pos (sub_pos.mpr hx1))

theorem gevreyCompactBump_nonneg (x : ℝ) :
    0 ≤ gevreyCompactBump x := by
  exact mul_nonneg (expNegInvGlue.nonneg x)
    (expNegInvGlue.nonneg (1 - x))

theorem gevreyCompactBump_contDiff {m : ℕ∞} :
    ContDiff ℝ m gevreyCompactBump := by
  unfold gevreyCompactBump
  fun_prop

theorem support_gevreyCompactBump_subset :
    Function.support gevreyCompactBump ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  constructor
  · by_contra h
    exact hx (gevreyCompactBump_eq_zero_of_nonpos (le_of_not_ge h))
  · by_contra h
    exact hx (gevreyCompactBump_eq_zero_of_one_le (le_of_not_ge h))

/-- Exact Leibniz expansion of every derivative of the compact bump. -/
theorem iteratedDeriv_gevreyCompactBump (n : ℕ) (x : ℝ) :
    iteratedDeriv n gevreyCompactBump x =
      ∑ i ∈ Finset.range (n + 1),
        n.choose i * iteratedDeriv i expNegInvGlue x *
          (((-1 : ℝ) ^ (n - i)) *
            iteratedDeriv (n - i) expNegInvGlue (1 - x)) := by
  have hprod := iteratedDeriv_fun_mul
    (n := n) (x := x)
    (f := expNegInvGlue)
    (g := fun y : ℝ ↦ expNegInvGlue (1 - y))
    expNegInvGlue.contDiff.contDiffAt
    ((expNegInvGlue.contDiff.comp
      (contDiff_const.sub contDiff_id)).contDiffAt)
  rw [show gevreyCompactBump = fun y : ℝ ↦
      expNegInvGlue y * expNegInvGlue (1 - y) by rfl,
    hprod]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [congrFun (iteratedDeriv_comp_const_sub (n - i)
    expNegInvGlue 1) x]
  simp only [smul_eq_mul]

private theorem succ_le_two_pow (n : ℕ) :
    n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      omega

private theorem factorial_mul_factorial_sub_le
    {n i : ℕ} (hi : i ≤ n) :
    i.factorial * (n - i).factorial ≤ n.factorial := by
  exact Nat.le_of_dvd (Nat.factorial_pos n)
    (Nat.factorial_mul_factorial_dvd_factorial hi)

private theorem abs_gevreyCompactBump_leibnizTerm_le
    (n i : ℕ) (x : ℝ) (hi : i ≤ n) :
    |(n.choose i : ℝ) * iteratedDeriv i expNegInvGlue x *
        (((-1 : ℝ) ^ (n - i)) *
          iteratedDeriv (n - i) expNegInvGlue (1 - x))| ≤
      48 ^ n * (n.factorial : ℝ) ^ 2 := by
  have hchoose : ((n.choose i : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast Nat.choose_le_two_pow n i
  have hleft := abs_iteratedDeriv_expNegInvGlue_le i x
  have hright := abs_iteratedDeriv_expNegInvGlue_le
    (n - i) (1 - x)
  have hfac :
      ((i.factorial : ℕ) : ℝ) * (((n - i).factorial : ℕ) : ℝ) ≤
        (n.factorial : ℝ) := by
    exact_mod_cast factorial_mul_factorial_sub_le hi
  have hfacSq :
      (((i.factorial : ℕ) : ℝ) *
        (((n - i).factorial : ℕ) : ℝ)) ^ 2 ≤
        (n.factorial : ℝ) ^ 2 := by
    gcongr
  have hpow24 :
      (24 : ℝ) ^ i * 24 ^ (n - i) = 24 ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  have hpow48 :
      (2 : ℝ) ^ n * 24 ^ n = 48 ^ n := by
    rw [← mul_pow]
    norm_num
  have habsChoose : |((n.choose i : ℕ) : ℝ)| =
      ((n.choose i : ℕ) : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  calc
    |(n.choose i : ℝ) * iteratedDeriv i expNegInvGlue x *
        (((-1 : ℝ) ^ (n - i)) *
          iteratedDeriv (n - i) expNegInvGlue (1 - x))| =
        (n.choose i : ℝ) *
          |iteratedDeriv i expNegInvGlue x| *
            |iteratedDeriv (n - i) expNegInvGlue (1 - x)| := by
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        habsChoose, one_mul]
    _ ≤ (2 : ℝ) ^ n *
        (24 ^ i * (i.factorial : ℝ) ^ 2) *
          (24 ^ (n - i) * ((n - i).factorial : ℝ) ^ 2) := by
      gcongr
    _ = 48 ^ n *
        (((i.factorial : ℕ) : ℝ) *
          (((n - i).factorial : ℕ) : ℝ)) ^ 2 := by
      rw [← hpow48, ← hpow24]
      ring
    _ ≤ 48 ^ n * (n.factorial : ℝ) ^ 2 := by
      gcongr

/-- The explicit compactly supported bump is globally Gevrey of order two.
The numerical constant is intentionally coarse but completely uniform in
the derivative order. -/
theorem abs_iteratedDeriv_gevreyCompactBump_le
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv n gevreyCompactBump x| ≤
      96 ^ n * (n.factorial : ℝ) ^ 2 := by
  rw [iteratedDeriv_gevreyCompactBump]
  calc
    |∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * iteratedDeriv i expNegInvGlue x *
          (((-1 : ℝ) ^ (n - i)) *
            iteratedDeriv (n - i) expNegInvGlue (1 - x))| ≤
        ∑ i ∈ Finset.range (n + 1),
          |(n.choose i : ℝ) * iteratedDeriv i expNegInvGlue x *
            (((-1 : ℝ) ^ (n - i)) *
              iteratedDeriv (n - i) expNegInvGlue (1 - x))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (n + 1),
        48 ^ n * (n.factorial : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact abs_gevreyCompactBump_leibnizTerm_le n i x
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    _ = ((n + 1 : ℕ) : ℝ) *
        (48 ^ n * (n.factorial : ℝ) ^ 2) := by
      simp
    _ ≤ ((2 ^ n : ℕ) : ℝ) *
        (48 ^ n * (n.factorial : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast succ_le_two_pow n
      · positivity
    _ = 96 ^ n * (n.factorial : ℝ) ^ 2 := by
      push_cast
      rw [← mul_assoc, ← mul_pow]
      norm_num

theorem abs_iteratedDeriv_gevreyCompactBump_le_gevreyForm
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv n gevreyCompactBump x| ≤
      96 ^ (n + 1) * (n.factorial : ℝ) ^ 2 := by
  calc
    |iteratedDeriv n gevreyCompactBump x| ≤
        96 ^ n * (n.factorial : ℝ) ^ 2 :=
      abs_iteratedDeriv_gevreyCompactBump_le n x
    _ ≤ 96 ^ (n + 1) * (n.factorial : ℝ) ^ 2 := by
      gcongr
      · norm_num
      · exact Nat.le_succ n

/-! ## Integral-normalized transition -/

/-- Positive normalizing mass of the compact Gevrey bump. -/
def gevreyCompactBumpMass : ℝ :=
  ∫ t : ℝ in (0 : ℝ)..1, gevreyCompactBump t

theorem gevreyCompactBumpMass_pos : 0 < gevreyCompactBumpMass := by
  unfold gevreyCompactBumpMass
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
      ((@gevreyCompactBump_contDiff 0).continuous.intervalIntegrable 0 1)
      (fun x hx ↦ gevreyCompactBump_pos hx.1 hx.2)
  norm_num

/-- A normalized transition obtained by integrating the compact bump. -/
def gevreyTransition (x : ℝ) : ℝ :=
  gevreyCompactBumpMass⁻¹ *
    ∫ t : ℝ in (0 : ℝ)..x, gevreyCompactBump t

theorem gevreyTransition_eq_zero_of_nonpos
    {x : ℝ} (hx : x ≤ 0) :
    gevreyTransition x = 0 := by
  have hint : (∫ t : ℝ in (0 : ℝ)..x, gevreyCompactBump t) = 0 := by
    calc
      (∫ t : ℝ in (0 : ℝ)..x, gevreyCompactBump t) =
          ∫ _t : ℝ in (0 : ℝ)..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_ge hx] at ht
        exact gevreyCompactBump_eq_zero_of_nonpos ht.2
      _ = 0 := by simp
  rw [gevreyTransition, hint, mul_zero]

theorem gevreyTransition_eq_one_of_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    gevreyTransition x = 1 := by
  have hcont : Continuous gevreyCompactBump :=
    (@gevreyCompactBump_contDiff 0).continuous
  have htail : (∫ t : ℝ in (1 : ℝ)..x, gevreyCompactBump t) = 0 := by
    calc
      (∫ t : ℝ in (1 : ℝ)..x, gevreyCompactBump t) =
          ∫ _t : ℝ in (1 : ℝ)..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hx] at ht
        exact gevreyCompactBump_eq_zero_of_one_le ht.1
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) 1)
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) (1 : ℝ) x)
  rw [htail, add_zero] at hadd
  unfold gevreyTransition
  rw [← hadd]
  change gevreyCompactBumpMass⁻¹ * gevreyCompactBumpMass = 1
  exact inv_mul_cancel₀ gevreyCompactBumpMass_pos.ne'

theorem hasDerivAt_gevreyTransition (x : ℝ) :
    HasDerivAt gevreyTransition
      (gevreyCompactBumpMass⁻¹ * gevreyCompactBump x) x := by
  unfold gevreyTransition
  exact ((@gevreyCompactBump_contDiff 0).continuous
    |>.integral_hasStrictDerivAt 0 x).hasDerivAt.const_mul _

theorem deriv_gevreyTransition (x : ℝ) :
    deriv gevreyTransition x =
      gevreyCompactBumpMass⁻¹ * gevreyCompactBump x :=
  (hasDerivAt_gevreyTransition x).deriv

theorem iteratedDeriv_gevreyTransition_succ
    (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) gevreyTransition x =
      gevreyCompactBumpMass⁻¹ *
        iteratedDeriv n gevreyCompactBump x := by
  rw [iteratedDeriv_succ']
  have hderiv : deriv gevreyTransition =
      fun y : ℝ ↦ gevreyCompactBumpMass⁻¹ * gevreyCompactBump y :=
    funext deriv_gevreyTransition
  rw [hderiv]
  exact iteratedDeriv_const_mul gevreyCompactBumpMass⁻¹
    (@gevreyCompactBump_contDiff n).contDiffAt

/-- The integral-normalized transition is smooth.  This is proved from its
explicit derivative, not assumed from a generic bump-function interface. -/
theorem gevreyTransition_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) gevreyTransition := by
  rw [contDiff_infty_iff_deriv]
  constructor
  · exact fun x ↦ (hasDerivAt_gevreyTransition x).differentiableAt
  · have hderiv : deriv gevreyTransition =
        fun y : ℝ ↦ gevreyCompactBumpMass⁻¹ * gevreyCompactBump y :=
      funext deriv_gevreyTransition
    rw [hderiv]
    exact contDiff_const.mul gevreyCompactBump_contDiff

theorem gevreyTransition_monotone : Monotone gevreyTransition := by
  apply monotone_of_deriv_nonneg
  · exact fun x ↦ (hasDerivAt_gevreyTransition x).differentiableAt
  · intro x
    rw [deriv_gevreyTransition]
    exact mul_nonneg (inv_nonneg.mpr gevreyCompactBumpMass_pos.le)
      (gevreyCompactBump_nonneg x)

theorem gevreyTransition_nonneg (x : ℝ) :
    0 ≤ gevreyTransition x := by
  by_cases hx : x ≤ 0
  · rw [gevreyTransition_eq_zero_of_nonpos hx]
  · have hmono := gevreyTransition_monotone
        (show (0 : ℝ) ≤ x from (lt_of_not_ge hx).le)
    simpa [gevreyTransition_eq_zero_of_nonpos (le_refl (0 : ℝ))]
      using! hmono

theorem gevreyTransition_le_one (x : ℝ) :
    gevreyTransition x ≤ 1 := by
  by_cases hx : 1 ≤ x
  · rw [gevreyTransition_eq_one_of_one_le hx]
  · have hmono := gevreyTransition_monotone
        (show x ≤ (1 : ℝ) from (lt_of_not_ge hx).le)
    simpa [gevreyTransition_eq_one_of_one_le (le_refl (1 : ℝ))]
      using! hmono

theorem gevreyTransition_mem_Icc (x : ℝ) :
    gevreyTransition x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨gevreyTransition_nonneg x, gevreyTransition_le_one x⟩

/-- Quantitative Gevrey-2 estimate for every positive-order derivative of
the normalized transition.  The displayed normalization constant is exact;
the only coarse numerical constant is the `96` inherited from the compact
bump estimate. -/
theorem abs_iteratedDeriv_gevreyTransition_succ_le
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv (n + 1) gevreyTransition x| ≤
      gevreyCompactBumpMass⁻¹ *
        (96 ^ n * (n.factorial : ℝ) ^ 2) := by
  rw [iteratedDeriv_gevreyTransition_succ, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr gevreyCompactBumpMass_pos.le)]
  exact mul_le_mul_of_nonneg_left
    (abs_iteratedDeriv_gevreyCompactBump_le n x)
    (inv_nonneg.mpr gevreyCompactBumpMass_pos.le)

/-- Exact chain rule for an affine rescaling of the normalized transition. -/
theorem iteratedDeriv_gevreyTransition_affine
    (n : ℕ) (c s x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ gevreyTransition (c * y + s)) x =
      c ^ n * iteratedDeriv n gevreyTransition (c * x + s) := by
  have hn : ((n : ℕ∞) : WithTop ℕ∞) ≤
      ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  have hshift : ContDiff ℝ n (fun y : ℝ ↦ gevreyTransition (y + s)) :=
    (gevreyTransition_contDiff.of_le hn).comp
      (contDiff_id.add contDiff_const)
  rw [congrFun (iteratedDeriv_comp_const_smul hshift c) x,
    congrFun (iteratedDeriv_comp_add_const n gevreyTransition s) (c * x)]
  simp only [smul_eq_mul]

theorem gevreyTransition_affine_contDiff
    {m : ℕ∞} (c s : ℝ) :
    ContDiff ℝ m (fun y : ℝ ↦ gevreyTransition (c * y + s)) := by
  have hm : ((m : ℕ∞) : WithTop ℕ∞) ≤
      ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  exact (gevreyTransition_contDiff.of_le hm).comp
    (contDiff_const.mul contDiff_id |>.add contDiff_const)

/-- Quantitative chain-rule estimate for an affine rescaling. -/
theorem abs_iteratedDeriv_gevreyTransition_affine_succ_le
    (n : ℕ) (c s x : ℝ) :
    |iteratedDeriv (n + 1)
        (fun y : ℝ ↦ gevreyTransition (c * y + s)) x| ≤
      |c| ^ (n + 1) *
        (gevreyCompactBumpMass⁻¹ *
          (96 ^ n * (n.factorial : ℝ) ^ 2)) := by
  rw [iteratedDeriv_gevreyTransition_affine, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left
    (abs_iteratedDeriv_gevreyTransition_succ_le n (c * x + s))
    (pow_nonneg (abs_nonneg c) _)

/-! ## Even inner and outer plateaux -/

/-- Even cutoff which vanishes on `[-a,a]` and equals one outside
`[-2a,2a]` when `a > 0`.  The affine form makes the derivative scaling
transparent. -/
def gevreyInnerCutoff (a x : ℝ) : ℝ :=
  gevreyTransition (a⁻¹ * x - 1) +
    gevreyTransition ((-a⁻¹) * x - 1)

/-- Identification with the quotient formula normally used in the paper. -/
theorem gevreyInnerCutoff_eq_div
    {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    gevreyInnerCutoff a x =
      gevreyTransition ((x - a) / a) +
        gevreyTransition ((-x - a) / a) := by
  unfold gevreyInnerCutoff
  congr 1
  · congr 1
    field_simp
  · congr 1
    field_simp

theorem gevreyInnerCutoff_contDiff
    {m : ℕ∞} (a : ℝ) :
    ContDiff ℝ m (gevreyInnerCutoff a) := by
  unfold gevreyInnerCutoff
  simpa only [sub_eq_add_neg] using!
    (gevreyTransition_affine_contDiff (m := m) a⁻¹ (-1)).add
      (gevreyTransition_affine_contDiff (m := m) (-a⁻¹) (-1))

theorem gevreyInnerCutoff_even (a x : ℝ) :
    gevreyInnerCutoff a (-x) = gevreyInnerCutoff a x := by
  unfold gevreyInnerCutoff
  have hfirst : a⁻¹ * (-x) = (-a⁻¹) * x := by ring
  have hsecond : (-a⁻¹) * (-x) = a⁻¹ * x := by ring
  rw [hfirst, hsecond, add_comm]

theorem gevreyInnerCutoff_eq_zero_of_abs_le
    {a x : ℝ} (ha : 0 < a) (hx : |x| ≤ a) :
    gevreyInnerCutoff a x = 0 := by
  have hainv : 0 ≤ a⁻¹ := (inv_pos.mpr ha).le
  have hright : x ≤ a := (le_abs_self x).trans hx
  have hleft : -x ≤ a := (neg_le_abs x).trans hx
  have hscaledRight : a⁻¹ * x ≤ 1 := by
    calc
      a⁻¹ * x ≤ a⁻¹ * a :=
        mul_le_mul_of_nonneg_left hright hainv
      _ = 1 := inv_mul_cancel₀ ha.ne'
  have hscaledLeft : (-a⁻¹) * x ≤ 1 := by
    calc
      (-a⁻¹) * x = a⁻¹ * (-x) := by ring
      _ ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left hleft hainv
      _ = 1 := inv_mul_cancel₀ ha.ne'
  rw [gevreyInnerCutoff,
    gevreyTransition_eq_zero_of_nonpos (by linarith : a⁻¹ * x - 1 ≤ 0),
    gevreyTransition_eq_zero_of_nonpos
      (by linarith : (-a⁻¹) * x - 1 ≤ 0),
    add_zero]

theorem gevreyInnerCutoff_eq_one_of_two_mul_le
    {a x : ℝ} (ha : 0 < a) (hx : 2 * a ≤ x) :
    gevreyInnerCutoff a x = 1 := by
  have hainv : 0 ≤ a⁻¹ := (inv_pos.mpr ha).le
  have hscaled : 2 ≤ a⁻¹ * x := by
    calc
      (2 : ℝ) = a⁻¹ * (2 * a) := by
        field_simp
      _ ≤ a⁻¹ * x := mul_le_mul_of_nonneg_left hx hainv
  have hnegative : (-a⁻¹) * x - 1 ≤ 0 := by
    have : (-a⁻¹) * x = -(a⁻¹ * x) := by ring
    rw [this]
    linarith
  rw [gevreyInnerCutoff,
    gevreyTransition_eq_one_of_one_le
      (by linarith : 1 ≤ a⁻¹ * x - 1),
    gevreyTransition_eq_zero_of_nonpos hnegative,
    add_zero]

theorem gevreyInnerCutoff_eq_one_of_le_neg_two_mul
    {a x : ℝ} (ha : 0 < a) (hx : x ≤ -(2 * a)) :
    gevreyInnerCutoff a x = 1 := by
  have hainv : 0 ≤ a⁻¹ := (inv_pos.mpr ha).le
  have hscaled : 2 ≤ (-a⁻¹) * x := by
    calc
      (2 : ℝ) = (-a⁻¹) * (-(2 * a)) := by
        field_simp
      _ ≤ (-a⁻¹) * x := by
        exact mul_le_mul_of_nonpos_left hx (neg_nonpos.mpr hainv)
  have hnegative : a⁻¹ * x - 1 ≤ 0 := by
    have : a⁻¹ * x = -((-a⁻¹) * x) := by ring
    rw [this]
    linarith
  rw [gevreyInnerCutoff,
    gevreyTransition_eq_zero_of_nonpos hnegative,
    gevreyTransition_eq_one_of_one_le
      (by linarith : 1 ≤ (-a⁻¹) * x - 1),
    zero_add]

theorem gevreyInnerCutoff_eq_one_of_two_mul_le_abs
    {a x : ℝ} (ha : 0 < a) (hx : 2 * a ≤ |x|) :
    gevreyInnerCutoff a x = 1 := by
  by_cases hx0 : 0 ≤ x
  · apply gevreyInnerCutoff_eq_one_of_two_mul_le ha
    simpa [abs_of_nonneg hx0] using! hx
  · apply gevreyInnerCutoff_eq_one_of_le_neg_two_mul ha
    have hnonpos : x ≤ 0 := (lt_of_not_ge hx0).le
    rw [abs_of_nonpos hnonpos] at hx
    linarith

theorem gevreyInnerCutoff_mem_Icc
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    gevreyInnerCutoff a x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact add_nonneg
      (gevreyTransition_nonneg (a⁻¹ * x - 1))
      (gevreyTransition_nonneg ((-a⁻¹) * x - 1))
  · by_cases hx : 0 ≤ x
    · have hsecond : (-a⁻¹) * x - 1 ≤ 0 := by
        have hinv : 0 ≤ a⁻¹ := (inv_pos.mpr ha).le
        have : (-a⁻¹) * x ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hinv) hx
        linarith
      rw [gevreyInnerCutoff,
        gevreyTransition_eq_zero_of_nonpos hsecond, add_zero]
      exact gevreyTransition_le_one _
    · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
      have hfirst : a⁻¹ * x - 1 ≤ 0 := by
        have hinv : 0 ≤ a⁻¹ := (inv_pos.mpr ha).le
        have : a⁻¹ * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hinv hx'
        linarith
      rw [gevreyInnerCutoff,
        gevreyTransition_eq_zero_of_nonpos hfirst, zero_add]
      exact gevreyTransition_le_one _

/-- Exact derivative formula for the even inner cutoff. -/
theorem iteratedDeriv_gevreyInnerCutoff
    (n : ℕ) (a x : ℝ) :
    iteratedDeriv n (gevreyInnerCutoff a) x =
      (a⁻¹) ^ n *
          iteratedDeriv n gevreyTransition (a⁻¹ * x - 1) +
        (-a⁻¹) ^ n *
          iteratedDeriv n gevreyTransition ((-a⁻¹) * x - 1) := by
  unfold gevreyInnerCutoff
  change iteratedDeriv n
      ((fun y : ℝ ↦ gevreyTransition (a⁻¹ * y - 1)) +
        fun y : ℝ ↦ gevreyTransition ((-a⁻¹) * y - 1)) x = _
  have hfirst := iteratedDeriv_gevreyTransition_affine
    n a⁻¹ (-1) x
  have hsecond := iteratedDeriv_gevreyTransition_affine
    n (-a⁻¹) (-1) x
  have hfirstSmooth : ContDiffAt ℝ n
      (fun y : ℝ ↦ gevreyTransition (a⁻¹ * y - 1)) x := by
    simpa only [sub_eq_add_neg] using!
      (gevreyTransition_affine_contDiff
        (m := (n : ℕ∞)) a⁻¹ (-1)).contDiffAt
  have hsecondSmooth : ContDiffAt ℝ n
      (fun y : ℝ ↦ gevreyTransition ((-a⁻¹) * y - 1)) x := by
    simpa only [sub_eq_add_neg] using!
      (gevreyTransition_affine_contDiff
        (m := (n : ℕ∞)) (-a⁻¹) (-1)).contDiffAt
  rw [iteratedDeriv_add hfirstSmooth hsecondSmooth]
  simpa only [sub_eq_add_neg] using! congrArg₂ (fun u v : ℝ ↦ u + v)
    hfirst hsecond

/-- Quantitative derivative bound for the inner cutoff. -/
theorem abs_iteratedDeriv_gevreyInnerCutoff_succ_le
    (n : ℕ) (a x : ℝ) :
    |iteratedDeriv (n + 1) (gevreyInnerCutoff a) x| ≤
      2 * |a⁻¹| ^ (n + 1) *
        (gevreyCompactBumpMass⁻¹ *
          (96 ^ n * (n.factorial : ℝ) ^ 2)) := by
  rw [iteratedDeriv_gevreyInnerCutoff]
  calc
    |(a⁻¹) ^ (n + 1) *
          iteratedDeriv (n + 1) gevreyTransition (a⁻¹ * x - 1) +
        (-a⁻¹) ^ (n + 1) *
          iteratedDeriv (n + 1) gevreyTransition ((-a⁻¹) * x - 1)| ≤
        |(a⁻¹) ^ (n + 1) *
          iteratedDeriv (n + 1) gevreyTransition (a⁻¹ * x - 1)| +
        |(-a⁻¹) ^ (n + 1) *
          iteratedDeriv (n + 1) gevreyTransition ((-a⁻¹) * x - 1)| :=
      abs_add_le _ _
    _ ≤ |a⁻¹| ^ (n + 1) *
          (gevreyCompactBumpMass⁻¹ *
            (96 ^ n * (n.factorial : ℝ) ^ 2)) +
        |-a⁻¹| ^ (n + 1) *
          (gevreyCompactBumpMass⁻¹ *
            (96 ^ n * (n.factorial : ℝ) ^ 2)) := by
      simp only [abs_mul, abs_pow]
      gcongr
      · exact abs_iteratedDeriv_gevreyTransition_succ_le n _
      · exact abs_iteratedDeriv_gevreyTransition_succ_le n _
    _ = 2 * |a⁻¹| ^ (n + 1) *
        (gevreyCompactBumpMass⁻¹ *
          (96 ^ n * (n.factorial : ℝ) ^ 2)) := by
      rw [abs_neg]
      ring

/-- Even outer cutoff: one on `[-ε/2,ε/2]`, zero outside
`[-ε,ε]`. -/
def gevreyOuterCutoff (ε x : ℝ) : ℝ :=
  1 - gevreyInnerCutoff (ε / 2) x

theorem gevreyOuterCutoff_eq_transition_div
    {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    gevreyOuterCutoff ε x =
      1 - gevreyTransition ((x - ε / 2) / (ε / 2)) -
        gevreyTransition ((-x - ε / 2) / (ε / 2)) := by
  rw [gevreyOuterCutoff,
    gevreyInnerCutoff_eq_div (div_ne_zero hε (by norm_num))]
  ring

theorem gevreyOuterCutoff_contDiff
    {m : ℕ∞} (ε : ℝ) :
    ContDiff ℝ m (gevreyOuterCutoff ε) := by
  unfold gevreyOuterCutoff
  exact contDiff_const.sub (gevreyInnerCutoff_contDiff (ε / 2))

theorem gevreyOuterCutoff_even (ε x : ℝ) :
    gevreyOuterCutoff ε (-x) = gevreyOuterCutoff ε x := by
  rw [gevreyOuterCutoff, gevreyInnerCutoff_even, gevreyOuterCutoff]

theorem gevreyOuterCutoff_eq_one_of_abs_le_half
    {ε x : ℝ} (hε : 0 < ε) (hx : |x| ≤ ε / 2) :
    gevreyOuterCutoff ε x = 1 := by
  rw [gevreyOuterCutoff,
    gevreyInnerCutoff_eq_zero_of_abs_le (half_pos hε) hx,
    sub_zero]

theorem gevreyOuterCutoff_eq_zero_of_le_abs
    {ε x : ℝ} (hε : 0 < ε) (hx : ε ≤ |x|) :
    gevreyOuterCutoff ε x = 0 := by
  have hscale : 2 * (ε / 2) ≤ |x| := by
    convert! hx using 1
    ring
  rw [gevreyOuterCutoff,
    gevreyInnerCutoff_eq_one_of_two_mul_le_abs (half_pos hε) hscale,
    sub_self]

theorem gevreyOuterCutoff_mem_Icc
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    gevreyOuterCutoff ε x ∈ Set.Icc (0 : ℝ) 1 := by
  have hinner := gevreyInnerCutoff_mem_Icc (half_pos hε) x
  unfold gevreyOuterCutoff
  constructor <;> linarith [hinner.1, hinner.2]

theorem support_gevreyOuterCutoff_subset
    {ε : ℝ} (hε : 0 < ε) :
    Function.support (gevreyOuterCutoff ε) ⊆ Set.Icc (-ε) ε := by
  intro x hx
  constructor
  · by_contra hleft
    have hlt : x < -ε := lt_of_not_ge hleft
    have hxneg : x < 0 := lt_trans hlt (neg_neg_of_pos hε)
    have habs : ε ≤ |x| := by
      rw [abs_of_neg hxneg]
      linarith
    exact hx (gevreyOuterCutoff_eq_zero_of_le_abs hε habs)
  · by_contra hright
    have hlt : ε < x := lt_of_not_ge hright
    have hxpos : 0 < x := hε.trans hlt
    have habs : ε ≤ |x| := by
      rw [abs_of_pos hxpos]
      exact hlt.le
    exact hx (gevreyOuterCutoff_eq_zero_of_le_abs hε habs)

theorem abs_iteratedDeriv_gevreyOuterCutoff_succ_le
    (n : ℕ) (ε x : ℝ) :
    |iteratedDeriv (n + 1) (gevreyOuterCutoff ε) x| ≤
      2 * |(ε / 2)⁻¹| ^ (n + 1) *
        (gevreyCompactBumpMass⁻¹ *
          (96 ^ n * (n.factorial : ℝ) ^ 2)) := by
  unfold gevreyOuterCutoff
  rw [iteratedDeriv_const_sub (Nat.succ_pos n) (1 : ℝ),
    iteratedDeriv_neg, abs_neg]
  exact abs_iteratedDeriv_gevreyInnerCutoff_succ_le n (ε / 2) x

end

end Erdos1002
