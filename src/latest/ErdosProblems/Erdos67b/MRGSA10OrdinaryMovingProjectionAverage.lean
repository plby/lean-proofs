import ErdosProblems.Erdos67b.MRGSA10MovingPerronProjection
import ErdosProblems.Erdos67b.MRGSA10HalfEndpointOrdinaryScalar
import ErdosProblems.Erdos67b.MRGSA10NearPrimeAverage
import ErdosProblems.Erdos67b.MRGSA10NearHPPAverage
import ErdosProblems.Erdos67b.MRGSA10DoubleIntegralMajorant
import ErdosProblems.Erdos67b.MRGSA10CoefficientInterchange

/-!
# Averaged ordinary-multiplicative moving Perron projection

This module combines the three source-correct projection errors only after
the alpha--beta average: the local near kernel is split into its prime and
higher-prime-power parts, the moving complete mass uses its existing
rectangle estimate, and the half endpoint uses the ordinary scalar bound.
-/

open scoped BigOperators
open Finset MeasureTheory Set

namespace Erdos67b.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard
open Erdos67b.PrimeEstimates

def gsA10OrdinaryNearKernel (X : ℕ) (T : ℝ) (a b : ℕ) : ℝ :=
  2 + (4 * (X : ℝ) / T) * (((a * b : ℕ) : ℝ))⁻¹ *
    (harmonic (2 * X) : ℝ)

def gsA10OrdinaryNearPrimeAverageBound
    (y X : ℕ) (T : ℝ) : ℝ :=
  2 * ((gsA10NearChebyshevConstant * (2 * X : ℕ) /
      Real.log (y : ℝ)) * primeReciprocals (2 * X)) +
    (4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ) *
      (primeReciprocals (2 * X)) ^ 2

def gsA10OrdinaryNearHPPConstantAverage
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (eta : ℝ) : ℝ :=
  ∑ a ∈ gsPositiveBelow (2 * X + 1),
    ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
        (fun b ↦ a * b < 2 * X + 1),
      4 * eta ^ 2 * gsA10NearHPPPairWeight hmul y X 0 0 a b

def gsA10OrdinaryNearHPPReciprocalAverageBound
    (y X : ℕ) (T eta : ℝ) : ℝ :=
  (4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ) *
    (2 * eta ^ 2 *
      (2 * gsA10PrimeLambdaHarmonicBudget (2 * X) *
          gsA10HigherPrimePowerGeometricMass y (2 * X) +
        (gsA10HigherPrimePowerGeometricMass y (2 * X)) ^ 2))

def gsA10OrdinaryNearHPPMassBudget (y X : ℕ) : ℝ :=
  2 * gsA10PrimeLambdaHarmonicBudget (2 * X) *
      gsA10HigherPrimePowerGeometricMass y (2 * X) +
    (gsA10HigherPrimePowerGeometricMass y (2 * X)) ^ 2

def gsA10OrdinaryNearHPPAverageBound
    (y X : ℕ) (T eta : ℝ) : ℝ :=
  4 * eta ^ 2 * (2 * X : ℕ) * gsA10OrdinaryNearHPPMassBudget y X +
    (4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ) *
      (2 * eta ^ 2 * gsA10OrdinaryNearHPPMassBudget y X)

def gsA10NearPrimeConstantAverage
    (y X : ℕ) (eta : ℝ) : ℝ :=
  ∑ a ∈ gsPositiveBelow (2 * X + 1),
    ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
        (fun b ↦ a * b < 2 * X + 1),
      2 * (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
            gsA10ShiftedPrimeLambdaWindowWeight
              y X (alpha + 2 * beta) b)

def gsA10NearPrimeReciprocalAverage
    (y X : ℕ) (eta : ℝ) : ℝ :=
  ∑ a ∈ gsPositiveBelow (2 * X + 1),
    ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
        (fun b ↦ a * b < 2 * X + 1),
      2 * (((a * b : ℕ) : ℝ))⁻¹ *
        (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
              gsA10ShiftedPrimeLambdaWindowWeight
                y X (alpha + 2 * beta) b)

def gsA10NearHPPConstantAverage
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (eta : ℝ) : ℝ :=
  ∑ a ∈ gsPositiveBelow (2 * X + 1),
    ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
        (fun b ↦ a * b < 2 * X + 1),
      2 * (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          gsA10NearHPPPairWeight hmul y X alpha beta a b)

def gsA10NearHPPReciprocalAverage
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (eta : ℝ) : ℝ :=
  ∑ a ∈ gsPositiveBelow (2 * X + 1),
    ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
        (fun b ↦ a * b < 2 * X + 1),
      2 * (((a * b : ℕ) : ℝ))⁻¹ *
        (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            gsA10NearHPPPairWeight hmul y X alpha beta a b)

private theorem continuous_shiftedPrimePair
    (y X a b : ℕ) :
    Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
        gsA10ShiftedPrimeLambdaWindowWeight y X (alpha + 2 * beta) b)) := by
  unfold gsA10ShiftedPrimeLambdaWindowWeight
  split_ifs <;> fun_prop

private theorem continuous_nearHPPPair
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X a b : ℕ) :
    Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      gsA10NearHPPPairWeight hmul y X alpha beta a b)) := by
  rw [show Function.uncurry (fun alpha beta : ℝ ↦
      gsA10NearHPPPairWeight hmul y X alpha beta a b) =
    Function.uncurry (fun alpha beta : ℝ ↦
      gsA10NearHPPPairWeight hmul y X 0 0 a b *
        (Real.exp (-alpha * Real.log (a : ℝ)) *
          Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ)))) by
      funext z
      exact gsA10NearHPPPairWeight_eq_zero_mul_exp
        hmul y X z.1 z.2 a b]
  fun_prop

private theorem integral_ordinaryPair_mul_kernel_eq
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X a b : ℕ) (T eta : ℝ) :
    2 * (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
          gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta) b *
            gsA10OrdinaryNearKernel X T a b) =
      2 * (2 * (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
            gsA10ShiftedPrimeLambdaWindowWeight
              y X (alpha + 2 * beta) b)) +
      ((4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ)) *
        (2 * (((a * b : ℕ) : ℝ))⁻¹ *
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
                gsA10ShiftedPrimeLambdaWindowWeight
                  y X (alpha + 2 * beta) b)) +
      2 * (2 * (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          gsA10NearHPPPairWeight hmul y X alpha beta a b)) +
      ((4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ)) *
        (2 * (((a * b : ℕ) : ℝ))⁻¹ *
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              gsA10NearHPPPairWeight hmul y X alpha beta a b)) := by
  let P : ℝ → ℝ → ℝ := fun alpha beta ↦
    gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
      gsA10ShiftedPrimeLambdaWindowWeight y X (alpha + 2 * beta) b
  let H : ℝ → ℝ → ℝ := fun alpha beta ↦
    gsA10NearHPPPairWeight hmul y X alpha beta a b
  have hP : Continuous (Function.uncurry P) := by
    simpa only [P] using continuous_shiftedPrimePair y X a b
  have hH : Continuous (Function.uncurry H) := by
    simpa only [H] using continuous_nearHPPPair hmul y X a b
  have hsplit :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
            gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta) b) =
        (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, P alpha beta) +
        (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, H alpha beta) := by
    simp_rw [gsA10OrdinaryLambdaNearWeight_mul_eq_prime_mul_prime_add_hpp]
    change (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta, P alpha beta + H alpha beta) = _
    calc
      _ = ∫ alpha : ℝ in 0..eta,
          ((∫ beta : ℝ in 0..eta, P alpha beta) +
            ∫ beta : ℝ in 0..eta, H alpha beta) := by
        apply intervalIntegral.integral_congr
        intro alpha halpha
        change (∫ beta : ℝ in 0..eta, P alpha beta + H alpha beta) =
          (∫ beta : ℝ in 0..eta, P alpha beta) +
            ∫ beta : ℝ in 0..eta, H alpha beta
        rw [intervalIntegral.integral_add]
        · exact (hP.comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
        · exact (hH.comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
      _ = _ := by
        rw [intervalIntegral.integral_add]
        · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
            hP 0 eta).intervalIntegrable 0 eta
        · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
            hH 0 eta).intervalIntegrable 0 eta
  have hpull :
      (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
            gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta) b *
              gsA10OrdinaryNearKernel X T a b) =
        gsA10OrdinaryNearKernel X T a b *
          ((∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
                gsA10OrdinaryLambdaNearWeight hmul y X
                  (alpha + 2 * beta) b)) := by
    simp_rw [mul_comm _ (gsA10OrdinaryNearKernel X T a b),
      intervalIntegral.integral_const_mul]
  rw [hpull, hsplit]
  dsimp only [P, H, gsA10OrdinaryNearKernel]
  ring

/-- Exact separation of the averaged local Perron kernel into its
prime--prime and HPP-containing constant and reciprocal pieces. -/
theorem sum_integral_ordinaryNearKernel_eq_prime_add_hpp
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (T eta : ℝ) :
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
              gsA10OrdinaryLambdaNearWeight hmul y X
                (alpha + 2 * beta) b *
              gsA10OrdinaryNearKernel X T a b)) =
      2 * gsA10NearPrimeConstantAverage y X eta +
        ((4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ)) *
          gsA10NearPrimeReciprocalAverage y X eta +
      2 * gsA10NearHPPConstantAverage hmul y X eta +
        ((4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ)) *
          gsA10NearHPPReciprocalAverage hmul y X eta := by
  calc
    _ = ∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        (2 * (2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
              gsA10ShiftedPrimeLambdaWindowWeight
                y X (alpha + 2 * beta) b)) +
        ((4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ)) *
          (2 * (((a * b : ℕ) : ℝ))⁻¹ *
            (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta,
                gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
                  gsA10ShiftedPrimeLambdaWindowWeight
                    y X (alpha + 2 * beta) b)) +
        2 * (2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            gsA10NearHPPPairWeight hmul y X alpha beta a b)) +
        ((4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ)) *
          (2 * (((a * b : ℕ) : ℝ))⁻¹ *
            (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta,
                gsA10NearHPPPairWeight hmul y X alpha beta a b))) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact integral_ordinaryPair_mul_kernel_eq hmul y X a b T eta
    _ = _ := by
      unfold gsA10NearPrimeConstantAverage
        gsA10NearPrimeReciprocalAverage gsA10NearHPPConstantAverage
        gsA10NearHPPReciprocalAverage
      simp_rw [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]

/-- Scalar alpha--beta average of the complete ordinary local near
majorant, with the Perron kernel's constant and reciprocal pieces retained
separately until the last line. -/
theorem sum_integral_ordinaryNearKernel_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hy : 2 ≤ y) (hX : 1 ≤ X)
    {T eta : ℝ} (hT : 0 < T) (heta : 0 ≤ eta) :
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
              gsA10OrdinaryLambdaNearWeight hmul y X
                (alpha + 2 * beta) b *
              gsA10OrdinaryNearKernel X T a b)) ≤
      gsA10OrdinaryNearPrimeAverageBound y X T +
        gsA10OrdinaryNearHPPAverageBound y X T eta := by
  rw [sum_integral_ordinaryNearKernel_eq_prime_add_hpp]
  have hPC := sum_two_mul_intervalIntegral_primeWindowWeights_le
    hy (show 0 < X by omega) heta
  have hPR := sum_two_mul_inv_intervalIntegral_primeWindowWeights_le
    (X := X) hy heta
  have hHC := sum_two_mul_intervalIntegral_nearHPPPairWeight_le
    hmul hbound (y := y) (X := X) hX heta
  have hHR := sum_two_mul_inv_intervalIntegral_nearHPPPairWeight_le
    hmul hbound (y := y) (X := X) hX heta
  have hHR' : gsA10NearHPPReciprocalAverage hmul y X eta ≤
      2 * eta ^ 2 *
        (2 * gsA10PrimeLambdaHarmonicBudget (2 * X) *
            gsA10HigherPrimePowerGeometricMass y (2 * X) +
          (gsA10HigherPrimePowerGeometricMass y (2 * X)) ^ 2) := by
    simpa only [gsA10NearHPPReciprocalAverage, mul_assoc] using hHR
  have hR0 : 0 ≤ (4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ) := by
    exact mul_nonneg (by positivity) (gsA10_harmonic_cast_nonneg (2 * X))
  unfold gsA10OrdinaryNearPrimeAverageBound
    gsA10OrdinaryNearHPPAverageBound gsA10OrdinaryNearHPPMassBudget
  calc
    _ = (2 * gsA10NearPrimeConstantAverage y X eta +
          ((4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ)) *
            gsA10NearPrimeReciprocalAverage y X eta) +
        (2 * gsA10NearHPPConstantAverage hmul y X eta +
          ((4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ)) *
            gsA10NearHPPReciprocalAverage hmul y X eta) := by ring
    _ ≤
        (2 * ((gsA10NearChebyshevConstant * (2 * X : ℕ) /
              Real.log (y : ℝ)) * primeReciprocals (2 * X)) +
          ((4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ)) *
            (primeReciprocals (2 * X)) ^ 2) +
        (2 * (2 * eta ^ 2 * (2 * X : ℕ) *
              (2 * gsA10PrimeLambdaHarmonicBudget (2 * X) *
                  gsA10HigherPrimePowerGeometricMass y (2 * X) +
                (gsA10HigherPrimePowerGeometricMass y (2 * X)) ^ 2)) +
          ((4 * (X : ℝ) / T) * (harmonic (2 * X) : ℝ)) *
            (2 * eta ^ 2 *
              (2 * gsA10PrimeLambdaHarmonicBudget (2 * X) *
                  gsA10HigherPrimePowerGeometricMass y (2 * X) +
                (gsA10HigherPrimePowerGeometricMass y (2 * X)) ^ 2))) := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hPC (by norm_num))
          (mul_le_mul_of_nonneg_left hPR hR0))
        (add_le_add
          (mul_le_mul_of_nonneg_left hHC (by norm_num))
          (mul_le_mul_of_nonneg_left hHR' hR0))
    _ = _ := by ring

/-- The local ordinary-multiplicative near mass before the source
alpha--beta average. -/
def gsA10OrdinaryMovingProjectionNear
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (T alpha beta : ℝ) : ℝ :=
  ∑ a ∈ gsPositiveBelow (2 * X + 1),
    ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
        (fun b ↦ a * b < 2 * X + 1),
      gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
        gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta) b *
          gsA10OrdinaryNearKernel X T a b

/-- The fixed-high coefficient-mass envelope at one point of the source
rectangle. -/
def gsA10OrdinaryMovingProjectionMass
    (y X : ℕ) (alpha beta : ℝ) : ℝ :=
  (32 / (Real.log (X : ℝ)) ^ 2) *
    (gsA10MovingPerronMassConstant y X *
      ((X : ℝ) ^
          (Erdos67b.EulerResidue.taoExponent X - alpha - 2 * beta) *
        (X : ℝ) ^
          (1 - min
            (Erdos67b.EulerResidue.taoExponent X - 2 * beta) 1)))

/-- Uniform normalized half-endpoint budget on the source rectangle. -/
def gsA10OrdinaryHalfEndpointBound (y X : ℕ) : ℝ :=
  (Real.log (X : ℝ)) ^ 2 / (2 * (X : ℝ)) +
    gsA10HalfEndpointPrimeMass X *
      gsA10HigherPrimePowerGeometricMass y X +
    (gsA10HigherPrimePowerGeometricMass y X) ^ 2 / 2

/-- Complete pointwise ordinary projection majorant.  Its last term is
already written as `X` times a normalized half-endpoint bound, which makes
the subsequent rectangle average exact. -/
def gsA10OrdinaryMovingProjectionMajorant
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (T alpha beta : ℝ) : ℝ :=
  gsA10OrdinaryMovingProjectionNear hmul y X T alpha beta +
    gsA10OrdinaryMovingProjectionMass y X alpha beta +
    (X : ℝ) * gsA10OrdinaryHalfEndpointBound y X

/-- Source-correct pointwise ordinary projection: local mass, moving
coefficient mass, and the half endpoint are all replaced by their exact
ordinary-multiplicative majorants. -/
theorem norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_ordinaryMajorant
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ))
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {alpha beta : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖positivePrefixSum
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X -
        gsA10TwoBlockMovingPerronIntegral
          f hmul P₁ P₂ y X alpha beta
            ((Real.log (X : ℝ)) ^ 2)‖ ≤
      gsA10OrdinaryMovingProjectionMajorant hmul y X
        ((Real.log (X : ℝ)) ^ 2) alpha beta := by
  have hbase :=
    norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_massEnvelope
      hmul hbound P₁ P₂ hy hX hlogX hlogy hQ₂ hQ₃
        halpha0 halpha hbeta0 hbeta
  have hnear :=
    dirichletPerronNearMass_gsA10TwoBlockTailoredCoefficient_le_ordinary
      hmul hbound P₁ P₂ hQ₂ hQ₃ (show 0 < X by omega)
        (show 0 < (Real.log (X : ℝ)) ^ 2 by
          exact sq_pos_of_pos (zero_lt_one.trans_le hlogX)) halpha0 hbeta0
  have hend := norm_gsA10TwoBlockTailoredCoefficient_div_two_mul_le_mass
    hmul hbound P₁ P₂ hQ₂ hQ₃ hX halpha0 hbeta0
  have hXreal : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hend' :
      (1 / 2 : ℝ) *
          ‖gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta X‖ ≤
        (X : ℝ) * gsA10OrdinaryHalfEndpointBound y X := by
    have hmulEnd := mul_le_mul_of_nonneg_left hend hXreal.le
    unfold gsA10OrdinaryHalfEndpointBound
    calc
      (1 / 2 : ℝ) *
          ‖gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta X‖ =
          (X : ℝ) *
            (‖gsA10TwoBlockTailoredCoefficient
                f hmul P₁ P₂ y X alpha beta X‖ /
              (2 * (X : ℝ))) := by field_simp
      _ ≤ _ := hmulEnd
  apply hbase.trans
  unfold gsA10OrdinaryMovingProjectionMajorant
    gsA10OrdinaryMovingProjectionMass
    gsA10OrdinaryMovingProjectionNear
  exact add_le_add (add_le_add hnear le_rfl) hend'

private theorem continuous_ordinaryNearPair
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X a b : ℕ) (T : ℝ) :
    Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
        gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta) b *
          gsA10OrdinaryNearKernel X T a b)) := by
  rw [show Function.uncurry (fun alpha beta : ℝ ↦
      gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
        gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta) b *
          gsA10OrdinaryNearKernel X T a b) =
    Function.uncurry (fun alpha beta : ℝ ↦
      (gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
          gsA10ShiftedPrimeLambdaWindowWeight y X (alpha + 2 * beta) b +
        gsA10NearHPPPairWeight hmul y X alpha beta a b) *
          gsA10OrdinaryNearKernel X T a b) by
      funext z
      rcases z with ⟨alpha, beta⟩
      simp only [Function.uncurry_apply_pair]
      rw [gsA10OrdinaryLambdaNearWeight_mul_eq_prime_mul_prime_add_hpp]]
  exact ((continuous_shiftedPrimePair y X a b).add
    (continuous_nearHPPPair hmul y X a b)).mul continuous_const

theorem continuous_gsA10OrdinaryMovingProjectionNear
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (T : ℝ) :
    Continuous (Function.uncurry
      (gsA10OrdinaryMovingProjectionNear hmul y X T)) := by
  unfold gsA10OrdinaryMovingProjectionNear
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  exact continuous_ordinaryNearPair hmul y X a b T

theorem continuous_gsA10OrdinaryMovingProjectionMass
    {y X : ℕ} (hX : 0 < X) :
    Continuous (Function.uncurry
      (gsA10OrdinaryMovingProjectionMass y X)) := by
  unfold gsA10OrdinaryMovingProjectionMass
  have hXne : (X : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hX)
  exact continuous_const.mul <| continuous_const.mul <|
    ((Real.continuous_const_rpow hXne).comp (by fun_prop)).mul
      ((Real.continuous_const_rpow hXne).comp (by fun_prop))

theorem continuous_gsA10OrdinaryMovingProjectionMajorant
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y : ℕ) {X : ℕ} (hX : 0 < X) (T : ℝ) :
    Continuous (Function.uncurry
      (gsA10OrdinaryMovingProjectionMajorant hmul y X T)) := by
  unfold gsA10OrdinaryMovingProjectionMajorant
  exact ((continuous_gsA10OrdinaryMovingProjectionNear hmul y X T).add
    (continuous_gsA10OrdinaryMovingProjectionMass hX)).add continuous_const

theorem continuous_gsA10TwoBlockTailoredCoefficient_apply
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) {n : ℕ} (hn : n ≠ 0) :
    Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta n)) := by
  rw [show Function.uncurry (fun alpha beta : ℝ ↦
      gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta n) =
    Function.uncurry (fun alpha beta : ℝ ↦
      ∑ uv ∈ n.divisorsAntidiagonal,
        ∑ ab ∈ uv.1.divisorsAntidiagonal,
          ∑ cd ∈ uv.2.divisorsAntidiagonal,
            (gsA10TwoBlockAlternatingLow f P₁ P₂ y ab.1 *
              gsA9HighArithmetic f y ab.2 *
              gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y)
                y X cd.1 *
              gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y)
                y X cd.2) *
              gsA10ThreeShiftAverageIntegrand
                ab.2 cd.1 cd.2 alpha beta) by
      funext z
      rcases z with ⟨alpha, beta⟩
      simp only [Function.uncurry_apply_pair]
      exact gsA10TailoredCoefficient_apply_eq_nested
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y)
        y X alpha beta hn]
  apply continuous_finsetSum
  intro uv huv
  apply continuous_finsetSum
  intro ab hab
  apply continuous_finsetSum
  intro cd hcd
  unfold gsA10ThreeShiftAverageIntegrand
  fun_prop

private theorem positivePrefixSum_eq_Icc
    (a : ℕ → ℂ) (N : ℕ) :
    positivePrefixSum a N = ∑ n ∈ Finset.Icc 1 N, a n := by
  have h := sum_Ioc_eq_positivePrefixSum_sub a (Nat.zero_le N)
  have hz : positivePrefixSum a 0 = 0 := by simp [positivePrefixSum]
  calc
    positivePrefixSum a N = positivePrefixSum a N - positivePrefixSum a 0 := by
      rw [hz, sub_zero]
    _ = ∑ n ∈ Finset.Ioc 0 N, a n := h.symm
    _ = ∑ n ∈ Finset.Icc 1 N, a n := by
      apply Finset.sum_congr
      · ext n
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      · intro n hn
        rfl

theorem continuous_positivePrefixSum_gsA10TwoBlockTailoredCoefficient
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) :
    Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      positivePrefixSum
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta) X)) := by
  rw [show Function.uncurry (fun alpha beta : ℝ ↦
      positivePrefixSum
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta) X) =
    Function.uncurry (fun alpha beta : ℝ ↦
      ∑ n ∈ Finset.Icc 1 X,
        gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta n) by
      funext z
      rcases z with ⟨alpha, beta⟩
      simp only [Function.uncurry_apply_pair]
      exact positivePrefixSum_eq_Icc _ X]
  apply continuous_finsetSum
  intro n hn
  exact continuous_gsA10TwoBlockTailoredCoefficient_apply
    hmul P₁ P₂ y X (by
      have hn1 := (Finset.mem_Icc.mp hn).1
      omega)

private theorem doubleIntervalIntegral_add
    {F G : ℝ → ℝ → ℝ} {eta : ℝ}
    (hF : Continuous (Function.uncurry F))
    (hG : Continuous (Function.uncurry G)) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta, F alpha beta + G alpha beta) =
      (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, F alpha beta) +
      (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, G alpha beta) := by
  have hFinner : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, F alpha beta) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 eta
  have hGinner : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, G alpha beta) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG 0 eta
  calc
    _ = ∫ alpha : ℝ in 0..eta,
        ((∫ beta : ℝ in 0..eta, F alpha beta) +
          ∫ beta : ℝ in 0..eta, G alpha beta) := by
      apply intervalIntegral.integral_congr
      intro alpha halpha
      exact intervalIntegral.integral_add
        ((hF.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta)
        ((hG.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta)
    _ = _ := intervalIntegral.integral_add
      (hFinner.intervalIntegrable 0 eta) (hGinner.intervalIntegrable 0 eta)

private theorem two_mul_doubleIntervalIntegral_ordinaryNear_eq_sum
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (T eta : ℝ) :
    2 * (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        gsA10OrdinaryMovingProjectionNear hmul y X T alpha beta) =
      ∑ a ∈ gsPositiveBelow (2 * X + 1),
        ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
            (fun b ↦ a * b < 2 * X + 1),
          2 * (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
                gsA10OrdinaryLambdaNearWeight hmul y X
                  (alpha + 2 * beta) b *
                gsA10OrdinaryNearKernel X T a b) := by
  let D := gsPositiveBelow (2 * X + 1)
  let E : ℕ → Finset ℕ := fun a ↦
    D.filter (fun b ↦ a * b < 2 * X + 1)
  let H : ℕ → ℕ → ℝ → ℝ → ℝ := fun a b alpha beta ↦
    gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
      gsA10OrdinaryLambdaNearWeight hmul y X (alpha + 2 * beta) b *
        gsA10OrdinaryNearKernel X T a b
  have hH (a b : ℕ) : Continuous (Function.uncurry (H a b)) := by
    simpa only [H] using continuous_ordinaryNearPair hmul y X a b T
  have hinner (alpha : ℝ) :
      (∫ beta : ℝ in 0..eta,
        ∑ a ∈ D, ∑ b ∈ E a, H a b alpha beta) =
      ∑ a ∈ D, ∑ b ∈ E a,
        ∫ beta : ℝ in 0..eta, H a b alpha beta := by
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [intervalIntegral.integral_finsetSum]
      intro b hb
      exact ((hH a b).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
    · intro a ha
      exact (continuous_finsetSum _ fun b hb ↦
        (hH a b).comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta
  change 2 * (∫ alpha : ℝ in 0..eta,
    ∫ beta : ℝ in 0..eta,
      ∑ a ∈ D, ∑ b ∈ E a, H a b alpha beta) = _
  simp_rw [hinner]
  have hout :
      (∫ alpha : ℝ in 0..eta,
        ∑ a ∈ D, ∑ b ∈ E a,
          ∫ beta : ℝ in 0..eta, H a b alpha beta) =
        ∑ a ∈ D, ∑ b ∈ E a,
          ∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta, H a b alpha beta := by
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [intervalIntegral.integral_finsetSum]
      intro b hb
      exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (hH a b) 0 eta).intervalIntegrable 0 eta
    · intro a ha
      exact (continuous_finsetSum _ fun b hb ↦
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (hH a b) 0 eta).intervalIntegrable 0 eta
  rw [hout]
  dsimp only [D, E, H]
  simp_rw [Finset.mul_sum]

/-- Normalized double integral of the complete pointwise projection
majorant. -/
def gsA10OrdinaryMovingProjectionRectangleMajorant
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (T eta : ℝ) : ℝ :=
  2 * (∫ alpha : ℝ in 0..eta,
    ∫ beta : ℝ in 0..eta,
      gsA10OrdinaryMovingProjectionMajorant
        hmul y X T alpha beta) / (X : ℝ)

/-- Exact separation of the normalized projection rectangle into the
averaged local near mass, the moving coefficient-mass rectangle, and the
uniform half endpoint. -/
theorem gsA10OrdinaryMovingProjectionRectangleMajorant_eq
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    {X : ℕ} (hX : 0 < X) (y : ℕ) (T eta : ℝ) :
    gsA10OrdinaryMovingProjectionRectangleMajorant
        hmul y X T eta =
      (∑ a ∈ gsPositiveBelow (2 * X + 1),
        ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
            (fun b ↦ a * b < 2 * X + 1),
          2 * (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              gsA10OrdinaryLambdaNearWeight hmul y X alpha a *
                gsA10OrdinaryLambdaNearWeight hmul y X
                  (alpha + 2 * beta) b *
                gsA10OrdinaryNearKernel X T a b)) / (X : ℝ) +
        gsA10MovingPerronMassRectangle y X eta +
        2 * eta ^ 2 * gsA10OrdinaryHalfEndpointBound y X := by
  let N : ℝ → ℝ → ℝ :=
    gsA10OrdinaryMovingProjectionNear hmul y X T
  let M : ℝ → ℝ → ℝ :=
    gsA10OrdinaryMovingProjectionMass y X
  let E : ℝ := (X : ℝ) * gsA10OrdinaryHalfEndpointBound y X
  have hN : Continuous (Function.uncurry N) := by
    simpa only [N] using
      continuous_gsA10OrdinaryMovingProjectionNear hmul y X T
  have hM : Continuous (Function.uncurry M) := by
    simpa only [M] using
      continuous_gsA10OrdinaryMovingProjectionMass hX
  have hNM : Continuous (Function.uncurry (fun alpha beta ↦
      N alpha beta + M alpha beta)) := hN.add hM
  have hsplitNM := doubleIntervalIntegral_add (eta := eta) hN hM
  have hsplitE := doubleIntervalIntegral_add (eta := eta) hNM
    (show Continuous (Function.uncurry (fun _ _ : ℝ ↦ E)) by fun_prop)
  have hnear := two_mul_doubleIntervalIntegral_ordinaryNear_eq_sum
    hmul y X T eta
  unfold gsA10OrdinaryMovingProjectionRectangleMajorant
    gsA10OrdinaryMovingProjectionMajorant
  change 2 * (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (N alpha beta + M alpha beta) + E) / (X : ℝ) = _
  rw [hsplitE, hsplitNM]
  change 2 *
      (((∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta,
          gsA10OrdinaryMovingProjectionNear hmul y X T alpha beta) +
        (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta,
          gsA10OrdinaryMovingProjectionMass y X alpha beta)) +
        (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, E)) /
      (X : ℝ) = _
  have hXne : (X : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hX)
  calc
    _ = (2 * (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              gsA10OrdinaryMovingProjectionNear hmul y X T alpha beta)) /
          (X : ℝ) +
        (2 * (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              gsA10OrdinaryMovingProjectionMass y X alpha beta)) /
          (X : ℝ) +
        (2 * (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta, E)) / (X : ℝ) := by ring
    _ = _ := by
      rw [hnear]
      unfold gsA10MovingPerronMassRectangle
        gsA10OrdinaryMovingProjectionMass
      simp only [intervalIntegral.integral_const, sub_zero]
      dsimp only [E]
      field_simp [hXne]
      ring

/-- Explicit normalized budget for the moving projection rectangle. -/
def gsA10OrdinaryMovingProjectionAveragedBound
    (y X : ℕ) (eta : ℝ) : ℝ :=
  (gsA10OrdinaryNearPrimeAverageBound y X ((Real.log (X : ℝ)) ^ 2) +
      gsA10OrdinaryNearHPPAverageBound
        y X ((Real.log (X : ℝ)) ^ 2) eta) / (X : ℝ) +
    gsA10MovingPerronAveragedMassConstant * eta +
    2 * eta ^ 2 * gsA10OrdinaryHalfEndpointBound y X

/-- All three ordinary projection errors are scalarized after the source
rectangle average.  In particular, the local near term keeps both the
constant and reciprocal Perron kernels until the prime/HPP estimates have
been summed. -/
theorem gsA10OrdinaryMovingProjectionRectangleMajorant_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hprimeMass : Erdos67b.PrimeEstimates.primeReciprocals X ≤
      Real.log (X : ℝ))
    (hySize : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ))
    {eta : ℝ} (heta : 0 ≤ eta) :
    gsA10OrdinaryMovingProjectionRectangleMajorant hmul y X
        ((Real.log (X : ℝ)) ^ 2) eta ≤
      gsA10OrdinaryMovingProjectionAveragedBound y X eta := by
  rw [gsA10OrdinaryMovingProjectionRectangleMajorant_eq
    hmul (show 0 < X by omega)]
  have hlogXpos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlogX
  have hnear := sum_integral_ordinaryNearKernel_le
    hmul hbound (show 2 ≤ y by omega) (show 1 ≤ X by omega)
      (sq_pos_of_pos hlogXpos) heta
  have hmass := gsA10MovingPerronMassRectangle_le_eta
    hX (show 3 ≤ y by omega) hlogX hprimeMass hySize heta
  unfold gsA10OrdinaryMovingProjectionAveragedBound
  have hXR : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  exact add_le_add (add_le_add
    (div_le_div_of_nonneg_right hnear hXR) hmass) le_rfl

/-- Normalized two-fold moving-Perron projection error.  The only regularity
hypotheses are the continuity needed to pass the norm through the two
Bochner interval integrals; every quantitative term is discharged by the
ordinary-multiplicative estimates above. -/
theorem norm_two_mul_doubleIntervalIntegral_twoBlockTailored_sub_movingPerron_div_le_ordinary
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ))
    (hprimeMass : Erdos67b.PrimeEstimates.primeReciprocals X ≤
      Real.log (X : ℝ))
    (hySize : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ))
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hetaLog : eta ≤ (Real.log (y : ℝ))⁻¹)
    (hprefix : Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      positivePrefixSum
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta) X)))
    (hperron : Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      gsA10TwoBlockMovingPerronIntegral
        f hmul P₁ P₂ y X alpha beta
          ((Real.log (X : ℝ)) ^ 2)))) :
    ‖2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            positivePrefixSum
              (gsA10TwoBlockTailoredCoefficient
                f hmul P₁ P₂ y X alpha beta) X) -
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            gsA10TwoBlockMovingPerronIntegral
              f hmul P₁ P₂ y X alpha beta
                ((Real.log (X : ℝ)) ^ 2))‖ / (X : ℝ) ≤
      gsA10OrdinaryMovingProjectionAveragedBound y X eta := by
  let P : ℝ → ℝ → ℂ := fun alpha beta ↦
    positivePrefixSum
      (gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta) X
  let Q : ℝ → ℝ → ℂ := fun alpha beta ↦
    gsA10TwoBlockMovingPerronIntegral
      f hmul P₁ P₂ y X alpha beta ((Real.log (X : ℝ)) ^ 2)
  let G : ℝ → ℝ → ℝ :=
    gsA10OrdinaryMovingProjectionMajorant
      hmul y X ((Real.log (X : ℝ)) ^ 2)
  have hP : Continuous (Function.uncurry P) := by
    simpa only [P] using hprefix
  have hQ : Continuous (Function.uncurry Q) := by
    simpa only [Q] using hperron
  have hG : Continuous (Function.uncurry G) := by
    simpa only [G] using
      continuous_gsA10OrdinaryMovingProjectionMajorant
        hmul y (show 0 < X by omega) ((Real.log (X : ℝ)) ^ 2)
  have hpoint : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ∀ beta ∈ Set.Icc (0 : ℝ) eta,
        ‖P alpha beta - Q alpha beta‖ ≤ G alpha beta := by
    intro alpha halpha beta hbeta
    exact
      norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_ordinaryMajorant
        hmul hbound P₁ P₂ hy hX hlogX hlogy hQ₂ hQ₃
          halpha.1 (halpha.2.trans hetaLog)
          hbeta.1 (hbeta.2.trans hetaLog)
  have havg := norm_two_mul_doubleIntervalIntegral_sub_le_of_pointwise
    (P := P) (Q := Q) (G := G) heta hP hQ hG hpoint
  have hXreal : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hdiv := div_le_div_of_nonneg_right havg hXreal
  change ‖2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, P alpha beta) -
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, Q alpha beta)‖ / (X : ℝ) ≤ _
  calc
    _ ≤ 2 * (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, G alpha beta) / (X : ℝ) := hdiv
    _ = gsA10OrdinaryMovingProjectionRectangleMajorant hmul y X
        ((Real.log (X : ℝ)) ^ 2) eta := by rfl
    _ ≤ _ := gsA10OrdinaryMovingProjectionRectangleMajorant_le
      hmul hbound hy hX hlogX hprimeMass hySize heta

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.sum_integral_ordinaryNearKernel_le
#print axioms
  Erdos67b.MRHalaszBands.norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_ordinaryMajorant
#print axioms
  Erdos67b.MRHalaszBands.gsA10OrdinaryMovingProjectionRectangleMajorant_le
#print axioms
  Erdos67b.MRHalaszBands.norm_two_mul_doubleIntervalIntegral_twoBlockTailored_sub_movingPerron_div_le_ordinary
