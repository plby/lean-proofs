import ErdosProblems.Erdos67b.MRGSA10SourceSmallPowerRowScalar
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Explicit dyadic height and bounded weighted source row

The natural ceiling of `(log X)^2` is a sufficient dyadic exponent.
The affine-row estimate absorbs its shell cost whenever `log(X)^4 ≤ y`.
-/

namespace Erdos67b

open MRHalaszBands

noncomputable section

def mrCofactorDyadicHeight (X : ℕ) : ℕ := ⌈(Real.log (X : ℝ)) ^ 2⌉₊

theorem mrCofactor_sourceHeight_le_two_pow (X : ℕ) :
    (Real.log (X : ℝ)) ^ 2 ≤ (((2 : ℕ) ^ mrCofactorDyadicHeight X : ℕ) : ℝ) := by
  have hceil : (Real.log (X : ℝ)) ^ 2 ≤ (mrCofactorDyadicHeight X : ℝ) := Nat.le_ceil _
  exact hceil.trans (by
    exact_mod_cast (Nat.lt_two_pow_self (n := mrCofactorDyadicHeight X)).le)

theorem mrCofactorDyadicHeight_le_twice_log_sq {X : ℕ} (hlogX : 1 ≤ Real.log (X : ℝ)) :
    (mrCofactorDyadicHeight X : ℝ) ≤ 2 * (Real.log (X : ℝ)) ^ 2 := by
  apply Nat.ceil_le_two_mul
  have hsq : (1 : ℝ) ≤ (Real.log (X : ℝ)) ^ 2 := one_le_pow₀ hlogX
  exact (by norm_num : (2 : ℝ)⁻¹ ≤ 1).trans hsq

theorem mrCofactor_weightedRow_le {C : ℝ} (hC : 1 ≤ C) {y X : ℕ}
    (hy : 0 < y) (hX : 4 ≤ X) (hlogFour : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ)) :
    gsA10PrimeSourceWeightedRowFactor C y X (mrCofactorDyadicHeight X) ≤
      10 * gsA10SmallPowerSourceRowBound C := by
  have hlog4 : Real.log 4 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  have hlog4One : (1 : ℝ) ≤ Real.log 4 :=
    (Real.le_log_iff_exp_le (by norm_num)).2 (Real.exp_one_lt_three.le.trans (by norm_num))
  have hlogX : 1 ≤ Real.log (X : ℝ) := hlog4One.trans hlog4
  have hK := mrCofactorDyadicHeight_le_twice_log_sq hlogX
  have hLsq : (1 : ℝ) ≤ (Real.log (X : ℝ)) ^ 2 := one_le_pow₀ hlogX
  have hcount : 2 + 4 * (mrCofactorDyadicHeight X : ℝ) ≤ 10 * (Real.log (X : ℝ)) ^ 2 := by
    linarith
  have hA := gsA10PrimeSourceAffineRowConstant_nonneg hC
  have hB := gsA10PrimeSourceAffineRowSlope_nonneg hC hy (show 1 ≤ X by omega)
  have hinner :
      6 * gsA10PrimeSourceAffineRowConstant C +
          (2 + 4 * (mrCofactorDyadicHeight X : ℝ)) * gsA10PrimeSourceAffineRowSlope C y X ≤
        10 * (gsA10PrimeSourceAffineRowConstant C +
          gsA10PrimeSourceAffineRowSlope C y X * (Real.log (X : ℝ)) ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_right hcount hB
    nlinarith
  have hrow := gsA10PrimeSourceAffineRow_smallPower_mul_log_sq_le hC hy hlog4 hlogFour
  unfold gsA10PrimeSourceWeightedRowFactor
  calc
    _ ≤ (Real.exp 1 * Real.sqrt Real.pi) *
        (10 * (gsA10PrimeSourceAffineRowConstant C +
          gsA10PrimeSourceAffineRowSlope C y X * (Real.log (X : ℝ)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 10 * ((Real.exp 1 * Real.sqrt Real.pi) *
        (gsA10PrimeSourceAffineRowConstant C +
          gsA10PrimeSourceAffineRowSlope C y X * (Real.log (X : ℝ)) ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrow (by norm_num)

end

end Erdos67b
