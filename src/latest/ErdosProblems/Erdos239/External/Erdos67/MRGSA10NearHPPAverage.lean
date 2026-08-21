import ErdosProblems.Erdos239.External.Erdos67.MRGSA10TailoredNearMassOrdinary
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10NearWeightAverage
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10PrimeLambdaDiagonal

/-!
# Averaging the higher-prime-power part of the A.10 near mass

This module is the ordinary-multiplicative companion to
`MRGSA10NearPrimeAverage`.  It separates the three terms containing at
least one higher-prime-power Lambda coefficient.  The real shifts are kept
exactly: each pair is a fixed zero-shift coefficient times the same
two-variable exponential occurring in the prime--prime term.

The final lemmas give both the sharp reciprocal-logarithm average and a
uniform zero-shift envelope.  The latter is designed to be summed using
`gsA10HigherPrimePowerGeometricMass`.
-/

open scoped BigOperators
open Finset MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The part of the product of two ordinary Lambda-window majorants which
contains at least one higher-prime-power coefficient. -/
def gsA10NearHPPPairWeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (alpha beta : ℝ) (a b : ℕ) : ℝ :=
  gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
      gsA10HigherPrimePowerLambdaWindowWeight hmul y X
        (alpha + 2 * beta) b +
    gsA10HigherPrimePowerLambdaWindowWeight hmul y X alpha a *
      gsA10ShiftedPrimeLambdaWindowWeight y X
        (alpha + 2 * beta) b +
    gsA10HigherPrimePowerLambdaWindowWeight hmul y X alpha a *
      gsA10HigherPrimePowerLambdaWindowWeight hmul y X
        (alpha + 2 * beta) b

theorem gsA10NearHPPPairWeight_nonneg
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (alpha beta : ℝ) (a b : ℕ) :
    0 ≤ gsA10NearHPPPairWeight hmul y X alpha beta a b := by
  unfold gsA10NearHPPPairWeight
  exact add_nonneg
    (add_nonneg
      (mul_nonneg
        (gsA10ShiftedPrimeLambdaWindowWeight_nonneg y X alpha a)
        (gsA10HigherPrimePowerLambdaWindowWeight_nonneg
          hmul y X (alpha + 2 * beta) b))
      (mul_nonneg
        (gsA10HigherPrimePowerLambdaWindowWeight_nonneg
          hmul y X alpha a)
        (gsA10ShiftedPrimeLambdaWindowWeight_nonneg
          y X (alpha + 2 * beta) b)))
    (mul_nonneg
      (gsA10HigherPrimePowerLambdaWindowWeight_nonneg hmul y X alpha a)
      (gsA10HigherPrimePowerLambdaWindowWeight_nonneg
        hmul y X (alpha + 2 * beta) b))

/-- Exact separation of the prime--prime term from the ordinary product. -/
theorem gsA10OrdinaryLambdaNearWeight_mul_eq_prime_mul_prime_add_hpp
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (alpha beta : ℝ) (a b : ℕ) :
    gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
        gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta) b =
      gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
          gsA10ShiftedPrimeLambdaWindowWeight y X
            (alpha + 2 * beta) b +
        gsA10NearHPPPairWeight hmul y X alpha beta a b := by
  unfold gsA10OrdinaryLambdaNearWeight gsA10NearHPPPairWeight
  ring

/-- The shifted prime window is its zero-shift value times the exact real
exponential. -/
theorem gsA10ShiftedPrimeLambdaWindowWeight_eq_exp_mul_zero
    (y X : ℕ) (rho : ℝ) (n : ℕ) :
    gsA10ShiftedPrimeLambdaWindowWeight y X rho n =
      Real.exp (-rho * Real.log (n : ℝ)) *
        gsA10ShiftedPrimeLambdaWindowWeight y X 0 n := by
  unfold gsA10ShiftedPrimeLambdaWindowWeight
  split_ifs <;> simp

/-- The shifted HPP window is its zero-shift norm times the exact real
exponential. -/
theorem gsA10HigherPrimePowerLambdaWindowWeight_eq_exp_mul_zero
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (rho : ℝ) (n : ℕ) :
    gsA10HigherPrimePowerLambdaWindowWeight hmul y X rho n =
      Real.exp (-rho * Real.log (n : ℝ)) *
        gsA10HigherPrimePowerLambdaWindowWeight hmul y X 0 n := by
  unfold gsA10HigherPrimePowerLambdaWindowWeight
  split_ifs with hwin
  · have hn : n ≠ 0 := by omega
    rw [gsRealShift_apply_of_ne_zero rho _ hn,
      gsRealShift_apply_of_ne_zero 0 _ hn, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    simp only [zero_mul, neg_zero, Real.exp_zero, abs_one, one_mul]
    rw [abs_of_nonneg (Real.exp_nonneg _)]
  · simp

/-- All three HPP-containing products have the same retained two-shift
exponential. -/
theorem gsA10NearHPPPairWeight_eq_zero_mul_exp
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (alpha beta : ℝ) (a b : ℕ) :
    gsA10NearHPPPairWeight hmul y X alpha beta a b =
      gsA10NearHPPPairWeight hmul y X 0 0 a b *
        (Real.exp (-alpha * Real.log (a : ℝ)) *
          Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ))) := by
  have hPa := gsA10ShiftedPrimeLambdaWindowWeight_eq_exp_mul_zero
    y X alpha a
  have hHa := gsA10HigherPrimePowerLambdaWindowWeight_eq_exp_mul_zero
    hmul y X alpha a
  have hPb := gsA10ShiftedPrimeLambdaWindowWeight_eq_exp_mul_zero
    y X (alpha + 2 * beta) b
  have hHb := gsA10HigherPrimePowerLambdaWindowWeight_eq_exp_mul_zero
    hmul y X (alpha + 2 * beta) b
  unfold gsA10NearHPPPairWeight
  simp only [hPa, hHa, hPb, hHb]
  simp only [zero_add]
  ring_nf

/-- Sharp retained-shift alpha--beta average for one pair containing an HPP
coefficient.  No complete multiplicativity is used. -/
theorem two_mul_intervalIntegral_nearHPPPairWeight_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    {y X a b : ℕ} (hy : 2 ≤ y) {eta : ℝ} (heta : 0 ≤ eta) :
    2 * (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        gsA10NearHPPPairWeight hmul y X alpha beta a b) ≤
      2 * gsA10NearHPPPairWeight hmul y X 0 0 a b *
        ((Real.log (a : ℝ) + Real.log (b : ℝ))⁻¹ *
          (2 * Real.log (b : ℝ))⁻¹) := by
  by_cases ha : y < a ∧ a < X / y
  · by_cases hb : y < b ∧ b < X / y
    · have ha2 : 2 ≤ a := hy.trans (Nat.le_of_lt ha.1)
      have hb2 : 2 ≤ b := hy.trans (Nat.le_of_lt hb.1)
      have havg := intervalIntegral_intervalIntegral_exp_natLog_two_shift_le
        ha2 hb2 heta
      have hrewrite :
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              gsA10NearHPPPairWeight hmul y X alpha beta a b) =
            gsA10NearHPPPairWeight hmul y X 0 0 a b *
              (∫ alpha : ℝ in 0..eta,
                ∫ beta : ℝ in 0..eta,
                  Real.exp (-alpha * Real.log (a : ℝ)) *
                    Real.exp (-(alpha + 2 * beta) *
                      Real.log (b : ℝ))) := by
        have hfun :
            (fun alpha : ℝ ↦
              ∫ beta : ℝ in 0..eta,
                gsA10NearHPPPairWeight hmul y X alpha beta a b) =
              (fun alpha : ℝ ↦
                ∫ beta : ℝ in 0..eta,
                  gsA10NearHPPPairWeight hmul y X 0 0 a b *
                    (Real.exp (-alpha * Real.log (a : ℝ)) *
                      Real.exp (-(alpha + 2 * beta) *
                        Real.log (b : ℝ)))) := by
          funext alpha
          apply intervalIntegral.integral_congr
          intro beta _
          exact gsA10NearHPPPairWeight_eq_zero_mul_exp
            hmul y X alpha beta a b
        rw [hfun]
        simp_rw [intervalIntegral.integral_const_mul]
      rw [hrewrite]
      have hC : 0 ≤ 2 * gsA10NearHPPPairWeight hmul y X 0 0 a b :=
        mul_nonneg (by norm_num)
          (gsA10NearHPPPairWeight_nonneg hmul y X 0 0 a b)
      calc
        2 * (gsA10NearHPPPairWeight hmul y X 0 0 a b *
            (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta,
                Real.exp (-alpha * Real.log (a : ℝ)) *
                  Real.exp (-(alpha + 2 * beta) *
                    Real.log (b : ℝ)))) =
            (2 * gsA10NearHPPPairWeight hmul y X 0 0 a b) *
              (∫ alpha : ℝ in 0..eta,
                ∫ beta : ℝ in 0..eta,
                  Real.exp (-alpha * Real.log (a : ℝ)) *
                    Real.exp (-(alpha + 2 * beta) *
                      Real.log (b : ℝ))) := by ring
        _ ≤ (2 * gsA10NearHPPPairWeight hmul y X 0 0 a b) *
              ((Real.log (a : ℝ) + Real.log (b : ℝ))⁻¹ *
                (2 * Real.log (b : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_left havg hC
        _ = _ := by ring
    · have hb0 (rho : ℝ) :
          gsA10ShiftedPrimeLambdaWindowWeight y X rho b = 0 := by
        simp [gsA10ShiftedPrimeLambdaWindowWeight, hb]
      have hbH0 (rho : ℝ) :
          gsA10HigherPrimePowerLambdaWindowWeight hmul y X rho b = 0 := by
        simp [gsA10HigherPrimePowerLambdaWindowWeight, hb]
      simp [gsA10NearHPPPairWeight, hb0, hbH0]
  · have ha0 (rho : ℝ) :
        gsA10ShiftedPrimeLambdaWindowWeight y X rho a = 0 := by
      simp [gsA10ShiftedPrimeLambdaWindowWeight, ha]
    have haH0 (rho : ℝ) :
        gsA10HigherPrimePowerLambdaWindowWeight hmul y X rho a = 0 := by
      simp [gsA10HigherPrimePowerLambdaWindowWeight, ha]
    simp [gsA10NearHPPPairWeight, ha0, haH0]

/-- The retained two-shift exponential is at most one throughout a
nonnegative source square, so its double average is at most the area. -/
theorem intervalIntegral_intervalIntegral_exp_natLog_two_shift_le_sq
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        Real.exp (-alpha * Real.log (a : ℝ)) *
          Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ))) ≤
      eta ^ 2 := by
  let F : ℝ → ℝ → ℝ := fun alpha beta ↦
    Real.exp (-alpha * Real.log (a : ℝ)) *
      Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ))
  have hF : Continuous (Function.uncurry F) := by
    dsimp only [F, Function.uncurry_apply_pair]
    fun_prop
  have hinner : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, F alpha beta) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hF
  have honeInner : Continuous (fun _alpha : ℝ ↦
      ∫ _beta : ℝ in 0..eta, (1 : ℝ)) := by fun_prop
  calc
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        Real.exp (-alpha * Real.log (a : ℝ)) *
          Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ))) =
        ∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, F alpha beta := rfl
    _ ≤ ∫ alpha : ℝ in 0..eta, ∫ _beta : ℝ in 0..eta, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on heta
      · exact hinner.intervalIntegrable 0 eta
      · exact honeInner.intervalIntegrable 0 eta
      · intro alpha halpha
        apply intervalIntegral.integral_mono_on heta
        · exact (hF.comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
        · exact continuous_const.intervalIntegrable 0 eta
        · intro beta hbeta
          have hloga : 0 ≤ Real.log (a : ℝ) :=
            Real.log_nonneg (by exact_mod_cast ha)
          have hlogb : 0 ≤ Real.log (b : ℝ) :=
            Real.log_nonneg (by exact_mod_cast hb)
          have heA : Real.exp (-alpha * Real.log (a : ℝ)) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            exact mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr halpha.1) hloga
          have heB :
              Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ)) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            exact mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr (add_nonneg halpha.1
                (mul_nonneg (by norm_num) hbeta.1))) hlogb
          calc
            Real.exp (-alpha * Real.log (a : ℝ)) *
                Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ)) ≤
                1 * Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ)) :=
              mul_le_mul_of_nonneg_right heA (Real.exp_nonneg _)
            _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left heB (by norm_num)
            _ = 1 := one_mul 1
    _ = eta ^ 2 := by
      simp only [intervalIntegral.integral_const, sub_zero]
      ring

/-- Uniform HPP-pair envelope on the source square.  Unlike the old coarse
ordinary weight, this follows from the retained shifts and costs the exact
area `eta²`. -/
theorem two_mul_intervalIntegral_nearHPPPairWeight_le_sq_mul_zero
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    {y X a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    {eta : ℝ} (heta : 0 ≤ eta) :
    2 * (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        gsA10NearHPPPairWeight hmul y X alpha beta a b) ≤
      2 * eta ^ 2 * gsA10NearHPPPairWeight hmul y X 0 0 a b := by
  have hrewrite :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          gsA10NearHPPPairWeight hmul y X alpha beta a b) =
        gsA10NearHPPPairWeight hmul y X 0 0 a b *
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              Real.exp (-alpha * Real.log (a : ℝ)) *
                Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ))) := by
    have hfun :
        (fun alpha : ℝ ↦
          ∫ beta : ℝ in 0..eta,
            gsA10NearHPPPairWeight hmul y X alpha beta a b) =
          (fun alpha : ℝ ↦
            ∫ beta : ℝ in 0..eta,
              gsA10NearHPPPairWeight hmul y X 0 0 a b *
                (Real.exp (-alpha * Real.log (a : ℝ)) *
                  Real.exp (-(alpha + 2 * beta) *
                    Real.log (b : ℝ)))) := by
      funext alpha
      apply intervalIntegral.integral_congr
      intro beta _
      exact gsA10NearHPPPairWeight_eq_zero_mul_exp
        hmul y X alpha beta a b
    rw [hfun]
    simp_rw [intervalIntegral.integral_const_mul]
  rw [hrewrite]
  have havg := intervalIntegral_intervalIntegral_exp_natLog_two_shift_le_sq
    ha hb heta
  have hC : 0 ≤ 2 * gsA10NearHPPPairWeight hmul y X 0 0 a b :=
    mul_nonneg (by norm_num)
      (gsA10NearHPPPairWeight_nonneg hmul y X 0 0 a b)
  calc
    2 * (gsA10NearHPPPairWeight hmul y X 0 0 a b *
        (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            Real.exp (-alpha * Real.log (a : ℝ)) *
              Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ)))) =
        (2 * gsA10NearHPPPairWeight hmul y X 0 0 a b) *
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              Real.exp (-alpha * Real.log (a : ℝ)) *
                Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ))) := by ring
    _ ≤ (2 * gsA10NearHPPPairWeight hmul y X 0 0 a b) * eta ^ 2 :=
      mul_le_mul_of_nonneg_left havg hC
    _ = 2 * eta ^ 2 * gsA10NearHPPPairWeight hmul y X 0 0 a b := by ring

/-- At zero shift the exact finite prime window has the standard harmonic
Lambda budget. -/
theorem sum_gsA10ShiftedPrimeLambdaWindowWeight_zero_div_le_budget
    {y X K : ℕ} (hK : 2 ≤ K) :
    (∑ n ∈ Finset.Icc 1 K,
        gsA10ShiftedPrimeLambdaWindowWeight y X 0 n / (n : ℝ)) ≤
      gsA10PrimeLambdaHarmonicBudget K := by
  have hpoint : ∀ n ∈ Finset.Icc 1 K,
      gsA10ShiftedPrimeLambdaWindowWeight y X 0 n / (n : ℝ) ≤
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ) := by
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hweight :
        gsA10ShiftedPrimeLambdaWindowWeight y X 0 n ≤
          ArithmeticFunction.vonMangoldt n := by
      unfold gsA10ShiftedPrimeLambdaWindowWeight
      split_ifs
      · simp
      · simp only [mul_zero]
        exact ArithmeticFunction.vonMangoldt_nonneg
      · exact ArithmeticFunction.vonMangoldt_nonneg
    calc
      gsA10ShiftedPrimeLambdaWindowWeight y X 0 n / (n : ℝ) ≤
          ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
        div_le_div_of_nonneg_right hweight (by positivity)
      _ = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
        exact div_eq_mul_inv _ _
  calc
    (∑ n ∈ Finset.Icc 1 K,
        gsA10ShiftedPrimeLambdaWindowWeight y X 0 n / (n : ℝ)) ≤
        ∑ n ∈ Finset.Icc 1 K,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ) :=
      Finset.sum_le_sum hpoint
    _ ≤ gsA10PrimeLambdaHarmonicBudget K := by
      simpa only [gsA10PrimeLambdaHarmonicBudget, neg_one_mul,
        sub_self, Real.rpow_zero, mul_one] using
        (sum_vonMangoldt_mul_rpow_neg_le_one
          (K := K) (alpha := (1 : ℝ)) hK zero_le_one le_rfl)

/-- The rectangular reciprocal mass of the three HPP-containing products
is bounded by the two prime--HPP cross masses and the HPP square.  This is
the scalar form needed for the reciprocal part of the Perron near kernel. -/
theorem sum_sum_gsA10NearHPPPairWeight_zero_div_mul_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X K : ℕ} (hK : 2 ≤ K) :
    (∑ a ∈ Finset.Icc 1 K,
      ∑ b ∈ Finset.Icc 1 K,
        gsA10NearHPPPairWeight hmul y X 0 0 a b /
          ((a : ℝ) * (b : ℝ))) ≤
      2 * gsA10PrimeLambdaHarmonicBudget K *
          gsA10HigherPrimePowerGeometricMass y K +
        (gsA10HigherPrimePowerGeometricMass y K) ^ 2 := by
  let P : ℕ → ℝ := gsA10ShiftedPrimeLambdaWindowWeight y X 0
  let H : ℕ → ℝ :=
    gsA10HigherPrimePowerLambdaWindowWeight hmul y X 0
  let PS : ℝ := ∑ n ∈ Finset.Icc 1 K, P n / (n : ℝ)
  let HS : ℝ := ∑ n ∈ Finset.Icc 1 K, H n / (n : ℝ)
  let PB : ℝ := gsA10PrimeLambdaHarmonicBudget K
  let HM : ℝ := gsA10HigherPrimePowerGeometricMass y K
  have hPS0 : 0 ≤ PS := by
    dsimp only [PS]
    exact Finset.sum_nonneg fun n hn ↦
      div_nonneg (gsA10ShiftedPrimeLambdaWindowWeight_nonneg y X 0 n)
        (Nat.cast_nonneg n)
  have hHS0 : 0 ≤ HS := by
    dsimp only [HS]
    exact Finset.sum_nonneg fun n hn ↦
      div_nonneg
        (gsA10HigherPrimePowerLambdaWindowWeight_nonneg hmul y X 0 n)
        (Nat.cast_nonneg n)
  have hPB0 : 0 ≤ PB := by
    dsimp only [PB, gsA10PrimeLambdaHarmonicBudget]
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hPS : PS ≤ PB := by
    simpa only [PS, PB, P] using
      (sum_gsA10ShiftedPrimeLambdaWindowWeight_zero_div_le_budget
        (y := y) (X := X) hK)
  have hHS : HS ≤ HM := by
    simpa only [HS, HM, H] using
      (sum_gsA10HigherPrimePowerLambdaWindowWeight_div_le_mass
        hmul hbound (y := y) (X := X) (K := K) (rho := (0 : ℝ))
          (le_rfl))
  have hHM0 : 0 ≤ HM := hHS0.trans hHS
  have hfactor :
      (∑ a ∈ Finset.Icc 1 K,
        ∑ b ∈ Finset.Icc 1 K,
          gsA10NearHPPPairWeight hmul y X 0 0 a b /
            ((a : ℝ) * (b : ℝ))) =
        PS * HS + HS * PS + HS ^ 2 := by
    dsimp only [PS, HS, P, H]
    simp_rw [gsA10NearHPPPairWeight, add_div,
      div_mul_eq_div_mul_one_div, Finset.sum_add_distrib]
    have hterm (A B x z : ℝ) :
        A * B / x * (1 / z) = (A / x) * (B / z) := by ring
    simp_rw [hterm]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    ring_nf
  rw [hfactor]
  calc
    PS * HS + HS * PS + HS ^ 2 ≤
        PB * HM + HM * PB + HM ^ 2 := by
      exact add_le_add
        (add_le_add
          (mul_le_mul hPS hHS hHS0 hPB0)
          (mul_le_mul hHS hPS hPS0 hHM0))
        (sq_le_sq₀ hHS0 hHM0 |>.2 hHS)
    _ = 2 * PB * HM + HM ^ 2 := by ring
    _ = _ := by rfl

/-- Summed finite-hyperbola form of the uniform HPP-pair average.  The
right side is left as the exact zero-shift hyperbola sum, so it may be
combined directly with the constant part of `dirichletPerronNearMass`. -/
theorem sum_two_mul_intervalIntegral_nearHPPPairWeight_le_zero
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    {y X : ℕ} {eta : ℝ} (heta : 0 ≤ eta) :
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            gsA10NearHPPPairWeight hmul y X alpha beta a b)) ≤
      ∑ a ∈ gsPositiveBelow (2 * X + 1),
        ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
            (fun b ↦ a * b < 2 * X + 1),
          2 * eta ^ 2 *
            gsA10NearHPPPairWeight hmul y X 0 0 a b := by
  apply Finset.sum_le_sum
  intro a ha
  have ha1 : 1 ≤ a := (Finset.mem_Ico.mp ha).1
  apply Finset.sum_le_sum
  intro b hb
  have hb1 : 1 ≤ b :=
    (Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1).1
  exact two_mul_intervalIntegral_nearHPPPairWeight_le_sq_mul_zero
    hmul ha1 hb1 heta

/-- Fully scalar reciprocal-kernel HPP average.  This is the term multiplied
by `4 X T⁻¹ harmonic(2X)` in the ordinary Perron near-mass bound. -/
theorem sum_two_mul_inv_intervalIntegral_nearHPPPairWeight_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 1 ≤ X) {eta : ℝ} (heta : 0 ≤ eta) :
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        2 * (((a * b : ℕ) : ℝ)⁻¹ *
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              gsA10NearHPPPairWeight hmul y X alpha beta a b))) ≤
      2 * eta ^ 2 *
        (2 * gsA10PrimeLambdaHarmonicBudget (2 * X) *
            gsA10HigherPrimePowerGeometricMass y (2 * X) +
          (gsA10HigherPrimePowerGeometricMass y (2 * X)) ^ 2) := by
  let Q : Finset ℕ := gsPositiveBelow (2 * X + 1)
  let R : Finset ℕ := Finset.Icc 1 (2 * X)
  let C : ℝ := 2 * eta ^ 2
  let G : ℕ → ℕ → ℝ := fun a b ↦
    gsA10NearHPPPairWeight hmul y X 0 0 a b /
      ((a : ℝ) * (b : ℝ))
  have hQR : Q ⊆ R := by
    intro n hn
    have hn' := Finset.mem_Ico.mp
      (by simpa only [Q, gsPositiveBelow] using hn)
    exact Finset.mem_Icc.mpr ⟨hn'.1, by omega⟩
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hpoint : ∀ a ∈ Q,
      ∀ b ∈ Q.filter (fun b ↦ a * b < 2 * X + 1),
        2 * (((a * b : ℕ) : ℝ)⁻¹ *
            (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta,
                gsA10NearHPPPairWeight hmul y X alpha beta a b)) ≤
          C * G a b := by
    intro a ha b hb
    have ha1 : 1 ≤ a :=
      (Finset.mem_Ico.mp (by simpa only [Q, gsPositiveBelow] using ha)).1
    have hbQ : b ∈ Q := (Finset.mem_filter.mp hb).1
    have hb1 : 1 ≤ b :=
      (Finset.mem_Ico.mp (by simpa only [Q, gsPositiveBelow] using hbQ)).1
    have hp := two_mul_intervalIntegral_nearHPPPairWeight_le_sq_mul_zero
      hmul (y := y) (X := X) ha1 hb1 heta
    have hinv : 0 ≤ (((a * b : ℕ) : ℝ)⁻¹) := by positivity
    calc
      2 * (((a * b : ℕ) : ℝ)⁻¹ *
            (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta,
              gsA10NearHPPPairWeight hmul y X alpha beta a b)) =
          (((a * b : ℕ) : ℝ)⁻¹ *
            (2 * (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta,
                gsA10NearHPPPairWeight hmul y X alpha beta a b))) := by ring
      _ ≤ (((a * b : ℕ) : ℝ)⁻¹ *
            (2 * eta ^ 2 *
              gsA10NearHPPPairWeight hmul y X 0 0 a b)) :=
        mul_le_mul_of_nonneg_left hp hinv
      _ = C * G a b := by
        dsimp only [C, G]
        push_cast
        rw [mul_inv]
        ring
  calc
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        2 * (((a * b : ℕ) : ℝ)⁻¹ *
            (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta,
              gsA10NearHPPPairWeight hmul y X alpha beta a b))) ≤
        ∑ a ∈ Q, ∑ b ∈ Q.filter (fun b ↦ a * b < 2 * X + 1),
          C * G a b := by
      simpa only [Q] using Finset.sum_le_sum fun a ha ↦
        Finset.sum_le_sum fun b hb ↦ hpoint a ha b hb
    _ ≤ ∑ a ∈ R, ∑ b ∈ R, C * G a b := by
      have hnonneg (a b : ℕ) : 0 ≤ C * G a b := by
        exact mul_nonneg hC0 <| div_nonneg
          (gsA10NearHPPPairWeight_nonneg hmul y X 0 0 a b)
          (mul_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b))
      calc
        (∑ a ∈ Q, ∑ b ∈ Q.filter (fun b ↦ a * b < 2 * X + 1),
            C * G a b) ≤
            ∑ a ∈ Q, ∑ b ∈ R, C * G a b := by
          apply Finset.sum_le_sum
          intro a ha
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (fun b hb ↦ hQR (Finset.mem_filter.mp hb).1)
          intro b hbR hb
          exact hnonneg a b
        _ ≤ ∑ a ∈ R, ∑ b ∈ R, C * G a b := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hQR
          intro a haR haQ
          exact Finset.sum_nonneg fun b hb ↦ hnonneg a b
    _ = C * (∑ a ∈ R, ∑ b ∈ R, G a b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ ≤ C *
        (2 * gsA10PrimeLambdaHarmonicBudget (2 * X) *
            gsA10HigherPrimePowerGeometricMass y (2 * X) +
          (gsA10HigherPrimePowerGeometricMass y (2 * X)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      simpa only [R, G] using
        (sum_sum_gsA10NearHPPPairWeight_zero_div_mul_le
          hmul hbound (y := y) (X := X) (K := 2 * X) (by omega))
    _ = _ := by rfl

/-- The unweighted zero-shift HPP hyperbola is at most `2X` times its
rectangular reciprocal mass. -/
theorem sum_gsA10NearHPPPairWeight_zero_le_twoX_mul_budget
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 1 ≤ X) :
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        gsA10NearHPPPairWeight hmul y X 0 0 a b) ≤
      (2 * X : ℕ) *
        (2 * gsA10PrimeLambdaHarmonicBudget (2 * X) *
            gsA10HigherPrimePowerGeometricMass y (2 * X) +
          (gsA10HigherPrimePowerGeometricMass y (2 * X)) ^ 2) := by
  let Q : Finset ℕ := gsPositiveBelow (2 * X + 1)
  let R : Finset ℕ := Finset.Icc 1 (2 * X)
  let D : ℝ := (2 * X : ℕ)
  let G : ℕ → ℕ → ℝ := fun a b ↦
    gsA10NearHPPPairWeight hmul y X 0 0 a b /
      ((a : ℝ) * (b : ℝ))
  let S : ℝ :=
    2 * gsA10PrimeLambdaHarmonicBudget (2 * X) *
        gsA10HigherPrimePowerGeometricMass y (2 * X) +
      (gsA10HigherPrimePowerGeometricMass y (2 * X)) ^ 2
  have hQR : Q ⊆ R := by
    intro n hn
    have hn' := Finset.mem_Ico.mp
      (by simpa only [Q, gsPositiveBelow] using hn)
    exact Finset.mem_Icc.mpr ⟨hn'.1, by omega⟩
  have hD0 : 0 ≤ D := by positivity
  have hpoint : ∀ a ∈ Q,
      ∀ b ∈ Q.filter (fun b ↦ a * b < 2 * X + 1),
        gsA10NearHPPPairWeight hmul y X 0 0 a b ≤ D * G a b := by
    intro a ha b hb
    have ha1 : 1 ≤ a :=
      (Finset.mem_Ico.mp (by simpa only [Q, gsPositiveBelow] using ha)).1
    have hbData := Finset.mem_filter.mp hb
    have hb1 : 1 ≤ b :=
      (Finset.mem_Ico.mp
        (by simpa only [Q, gsPositiveBelow] using hbData.1)).1
    have habpos : 0 < (a : ℝ) * (b : ℝ) := by positivity
    have habD : (a : ℝ) * (b : ℝ) ≤ D := by
      dsimp only [D]
      push_cast
      exact_mod_cast (show a * b ≤ 2 * X by omega)
    have hG0 : 0 ≤ G a b := by
      dsimp only [G]
      exact div_nonneg
        (gsA10NearHPPPairWeight_nonneg hmul y X 0 0 a b) habpos.le
    calc
      gsA10NearHPPPairWeight hmul y X 0 0 a b =
          ((a : ℝ) * (b : ℝ)) * G a b := by
        dsimp only [G]
        rw [mul_div_cancel₀ _ (ne_of_gt habpos)]
      _ ≤ D * G a b := mul_le_mul_of_nonneg_right habD hG0
  have hrect :
      (∑ a ∈ Q, ∑ b ∈ Q.filter (fun b ↦ a * b < 2 * X + 1),
        D * G a b) ≤ D * (∑ a ∈ R, ∑ b ∈ R, G a b) := by
    have hnonneg (a b : ℕ) : 0 ≤ D * G a b := by
      exact mul_nonneg hD0 <| div_nonneg
        (gsA10NearHPPPairWeight_nonneg hmul y X 0 0 a b)
        (mul_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b))
    calc
      (∑ a ∈ Q, ∑ b ∈ Q.filter (fun b ↦ a * b < 2 * X + 1),
          D * G a b) ≤ ∑ a ∈ Q, ∑ b ∈ R, D * G a b := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (fun b hb ↦ hQR (Finset.mem_filter.mp hb).1)
        intro b hbR hb
        exact hnonneg a b
      _ ≤ ∑ a ∈ R, ∑ b ∈ R, D * G a b := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hQR
        intro a haR haQ
        exact Finset.sum_nonneg fun b hb ↦ hnonneg a b
      _ = D * (∑ a ∈ R, ∑ b ∈ R, G a b) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
  have hS : (∑ a ∈ R, ∑ b ∈ R, G a b) ≤ S := by
    simpa only [R, G, S] using
      (sum_sum_gsA10NearHPPPairWeight_zero_div_mul_le
        hmul hbound (y := y) (X := X) (K := 2 * X) (by omega))
  calc
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        gsA10NearHPPPairWeight hmul y X 0 0 a b) ≤
        ∑ a ∈ Q, ∑ b ∈ Q.filter (fun b ↦ a * b < 2 * X + 1),
          D * G a b := by
      simpa only [Q] using Finset.sum_le_sum fun a ha ↦
        Finset.sum_le_sum fun b hb ↦ hpoint a ha b hb
    _ ≤ D * (∑ a ∈ R, ∑ b ∈ R, G a b) := hrect
    _ ≤ D * S := mul_le_mul_of_nonneg_left hS hD0
    _ = _ := by rfl

/-- Fully scalar constant-kernel HPP average. -/
theorem sum_two_mul_intervalIntegral_nearHPPPairWeight_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 1 ≤ X) {eta : ℝ} (heta : 0 ≤ eta) :
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            gsA10NearHPPPairWeight hmul y X alpha beta a b)) ≤
      2 * eta ^ 2 * (2 * X : ℕ) *
        (2 * gsA10PrimeLambdaHarmonicBudget (2 * X) *
            gsA10HigherPrimePowerGeometricMass y (2 * X) +
          (gsA10HigherPrimePowerGeometricMass y (2 * X)) ^ 2) := by
  have havg := sum_two_mul_intervalIntegral_nearHPPPairWeight_le_zero
    hmul (y := y) (X := X) heta
  have hzero := sum_gsA10NearHPPPairWeight_zero_le_twoX_mul_budget
    hmul hbound (y := y) (X := X) hX
  calc
    _ ≤ ∑ a ∈ gsPositiveBelow (2 * X + 1),
        ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
            (fun b ↦ a * b < 2 * X + 1),
          2 * eta ^ 2 * gsA10NearHPPPairWeight hmul y X 0 0 a b := havg
    _ = 2 * eta ^ 2 *
        (∑ a ∈ gsPositiveBelow (2 * X + 1),
          ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
              (fun b ↦ a * b < 2 * X + 1),
            gsA10NearHPPPairWeight hmul y X 0 0 a b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ ≤ 2 * eta ^ 2 * ((2 * X : ℕ) *
        (2 * gsA10PrimeLambdaHarmonicBudget (2 * X) *
            gsA10HigherPrimePowerGeometricMass y (2 * X) +
          (gsA10HigherPrimePowerGeometricMass y (2 * X)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hzero (by positivity)
    _ = _ := by ring

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.gsA10NearHPPPairWeight_eq_zero_mul_exp
#print axioms Erdos67.MRHalaszBands.two_mul_intervalIntegral_nearHPPPairWeight_le
#print axioms Erdos67.MRHalaszBands.sum_sum_gsA10NearHPPPairWeight_zero_div_mul_le
#print axioms Erdos67.MRHalaszBands.sum_two_mul_intervalIntegral_nearHPPPairWeight_le_zero
#print axioms Erdos67.MRHalaszBands.sum_two_mul_inv_intervalIntegral_nearHPPPairWeight_le
#print axioms Erdos67.MRHalaszBands.sum_gsA10NearHPPPairWeight_zero_le_twoX_mul_budget
#print axioms Erdos67.MRHalaszBands.sum_two_mul_intervalIntegral_nearHPPPairWeight_le
