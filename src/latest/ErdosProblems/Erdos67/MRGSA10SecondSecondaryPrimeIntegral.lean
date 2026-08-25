import ErdosProblems.Erdos67.MRGSA10SecondSecondaryPrimeChebyshev
import ErdosProblems.Erdos67.MRGSA10SecondSecondaryIntegral
import ErdosProblems.Erdos67.MRGSA10SecondSecondarySplit
import ErdosProblems.Erdos67.MRGSA10SecondSecondaryHigherPrimePower
import ErdosProblems.Erdos67.MRGSA10FiniteHighMass
import ErdosProblems.Erdos67.MRGSA10FiniteLowMassScalar
import ErdosProblems.Erdos67.MRGSA10RpowAverage

/-!
# The ordinary-multiplicative prime secondary in GS A.10

The generalized Mangoldt coefficient attached to an ordinary multiplicative
function is split into its prime and higher-prime-power parts.  This file
integrates the source-sharp weighted-Chebyshev estimate for the prime part.
The factor `X^(1-alpha)` is retained until the final integration, producing
the required `X / log X` rather than an interval-length loss.

The last theorem recombines this prime estimate with the separately bounded
higher-prime-power part.  No complete-multiplicativity hypothesis is used.
-/

open scoped BigOperators
open Set MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The absolute constant in the prime part of the second A.10 secondary. -/
def gsA10SecondSecondaryPrimeConstant : ℝ :=
  12 * (Real.log 4 + 4) * gsA10FiniteLowMassConstant *
    Real.exp (Real.log 2 + 2 * Erdos67.PrimeEstimates.mertensBound +
      3 * Erdos67.EulerQuantitative.primeQuadraticConstant)

theorem gsA10SecondSecondaryPrimeConstant_nonneg :
    0 ≤ gsA10SecondSecondaryPrimeConstant := by
  unfold gsA10SecondSecondaryPrimeConstant
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (by linarith))
      gsA10FiniteLowMassConstant_nonneg)
    (Real.exp_pos _).le

/-- The prime component of the second A.10 secondary has the source size
`O((X / log X) (1 + log y))`, uniformly for ordinary multiplicative
one-bounded coefficients. -/
theorem norm_gsA10TwoBlockSecondSecondaryPrimePrefix_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hyX : y ≤ X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    ‖gsA10SecondSecondaryPrefix
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsPrimePart (gsA9HighGeneralizedMangoldt hmul y)) X
        (Real.log (y : ℝ))⁻¹‖ ≤
      gsA10SecondSecondaryPrimeConstant *
        ((X : ℝ) / Real.log (X : ℝ)) * (1 + Real.log (y : ℝ)) := by
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  let low := gsA10TwoBlockAlternatingLow f P₁ P₂ y
  let high := gsA9HighArithmetic f y
  let lambda := gsPrimePart (gsA9HighGeneralizedMangoldt hmul y)
  let C : ℝ := 12 * (Real.log 4 + 4)
  let L : ℝ := gsA10FiniteLowMassConstant * (1 + Real.log (y : ℝ))
  let H : ℝ := Real.exp (Real.log 2 +
    2 * Erdos67.PrimeEstimates.mertensBound +
    3 * Erdos67.EulerQuantitative.primeQuadraticConstant)
  have hy2 : 2 ≤ y := by omega
  have hX1 : 1 < X := by omega
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have heta0 : 0 ≤ eta := (inv_pos.mpr hlogy).le
  have hC : 0 ≤ C := by
    dsimp [C]
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    have hlogy0 : 0 ≤ Real.log (y : ℝ) := hlogy.le
    exact mul_nonneg gsA10FiniteLowMassConstant_nonneg (by linarith)
  have hH : 0 ≤ H := by positivity
  have hcont : Continuous (fun alpha : ℝ ↦
      positivePrefixSum
        (fun n ↦ ((low * gsRealShift alpha lambda) *
          gsRealShift (2 * eta + alpha) high) n) X) :=
    continuous_positivePrefixSum_secondSecondaryIntegrand low high lambda X eta
  have hpoint : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ‖positivePrefixSum
          (fun n ↦ ((low * gsRealShift alpha lambda) *
            gsRealShift (2 * eta + alpha) high) n) X‖ ≤
        C * L * H * (X : ℝ) ^ (1 - alpha) := by
    intro alpha halpha
    have halphaHalf : alpha ≤ 1 / 2 := by
      have hexpTwo : Real.exp 2 < (y : ℝ) := by
        calc
          Real.exp 2 = Real.exp 1 * Real.exp 1 := by
            rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
          _ < 3 * 3 := by
            nlinarith [Real.exp_pos 1, Real.exp_one_lt_three]
          _ < 23 := by norm_num
          _ ≤ y := by exact_mod_cast hy
      have hlogTwo : 2 < Real.log (y : ℝ) := by
        rw [Real.lt_log_iff_exp_lt (by positivity)]
        exact hexpTwo
      have hetaHalf : eta ≤ 1 / 2 := by
        dsimp only [eta]
        have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hlogTwo.le
        norm_num at hinv ⊢
        exact hinv
      exact halpha.2.trans hetaHalf
    have halphaOne : alpha ≤ 1 := halphaHalf.trans (by norm_num)
    have hraw := norm_positivePrefixSum_secondSecondaryPrimeIntegrand_le
      (y := y) (X := X) (eta := eta) (alpha := alpha)
      hmul hbound P₁ P₂ halpha.1 halphaHalf halphaOne
    have hlow :
        gsFiniteNormDirichletMass low X (1 - alpha) ≤ L := by
      exact gsFiniteNormDirichletMass_twoBlockAlternatingLow_le_sourceConstant
        hmul hbound P₁ P₂ hy hQ₂ hQ₃ halpha.1 halpha.2
    have hhigh :
        gsFiniteNormDirichletMass high X (1 + 2 * eta) ≤ H := by
      exact gsFiniteNormDirichletMass_gsA9HighArithmetic_le_sourceConstant
        hbound hy2 hyX
    have hbase : 0 ≤ C * (X : ℝ) ^ (1 - alpha) := by
      exact mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
    calc
      ‖positivePrefixSum
          (fun n ↦ ((low * gsRealShift alpha lambda) *
            gsRealShift (2 * eta + alpha) high) n) X‖ ≤
          C * (X : ℝ) ^ (1 - alpha) *
            gsFiniteNormDirichletMass low X (1 - alpha) *
            gsFiniteNormDirichletMass high X (1 + 2 * eta) := hraw
      _ ≤ C * (X : ℝ) ^ (1 - alpha) * L * H := by
        calc
          C * (X : ℝ) ^ (1 - alpha) *
                gsFiniteNormDirichletMass low X (1 - alpha) *
                gsFiniteNormDirichletMass high X (1 + 2 * eta) ≤
              C * (X : ℝ) ^ (1 - alpha) * L *
                gsFiniteNormDirichletMass high X (1 + 2 * eta) := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left hlow hbase
            · unfold gsFiniteNormDirichletMass
              positivity
          _ ≤ C * (X : ℝ) ^ (1 - alpha) * L * H := by
            exact mul_le_mul_of_nonneg_left hhigh (mul_nonneg hbase hL)
      _ = C * L * H * (X : ℝ) ^ (1 - alpha) := by ring
  unfold gsA10SecondSecondaryPrefix
  change ‖∫ alpha in (0 : ℝ)..eta,
      positivePrefixSum
        (fun n ↦ ((low * gsRealShift alpha lambda) *
          gsRealShift (2 * eta + alpha) high) n) X‖ ≤ _
  calc
    ‖∫ alpha in (0 : ℝ)..eta,
        positivePrefixSum
          (fun n ↦ ((low * gsRealShift alpha lambda) *
            gsRealShift (2 * eta + alpha) high) n) X‖ ≤
        ∫ alpha in (0 : ℝ)..eta,
          ‖positivePrefixSum
            (fun n ↦ ((low * gsRealShift alpha lambda) *
              gsRealShift (2 * eta + alpha) high) n) X‖ :=
      intervalIntegral.norm_integral_le_integral_norm heta0
    _ ≤ ∫ alpha in (0 : ℝ)..eta,
          C * L * H * (X : ℝ) ^ (1 - alpha) := by
      apply intervalIntegral.integral_mono_on heta0
      · exact hcont.norm.intervalIntegrable 0 eta
      · have hmajor : Continuous (fun alpha : ℝ ↦
            C * L * H * (X : ℝ) ^ (1 - alpha)) := by
          exact continuous_const.mul
            ((Real.continuous_const_rpow
              (by exact_mod_cast (show X ≠ 0 by omega))).comp
                (continuous_const.sub continuous_id))
        exact hmajor.intervalIntegrable 0 eta
      · exact hpoint
    _ = C * L * H *
          (∫ alpha in (0 : ℝ)..eta, (X : ℝ) ^ (1 - alpha)) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ C * L * H * ((X : ℝ) / Real.log (X : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (intervalIntegral_rpow_one_sub_le_div_log hX1 heta0)
        (mul_nonneg (mul_nonneg hC hL) hH)
    _ = gsA10SecondSecondaryPrimeConstant *
          ((X : ℝ) / Real.log (X : ℝ)) *
            (1 + Real.log (y : ℝ)) := by
      dsimp [C, L, H]
      unfold gsA10SecondSecondaryPrimeConstant
      ring

/-- The whole ordinary-multiplicative second secondary is the sum of the
source-sharp prime error and the explicit higher-prime-power error. -/
theorem norm_gsA10TwoBlockSecondSecondaryPrefix_le_prime_add_higher
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hyX : y ≤ X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y) :
    ‖gsA10SecondSecondaryPrefix
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y) X
        (Real.log (y : ℝ))⁻¹‖ ≤
      gsA10SecondSecondaryPrimeConstant *
          ((X : ℝ) / Real.log (X : ℝ)) * (1 + Real.log (y : ℝ)) +
        12 * (X : ℝ) * Real.log X / y *
          Erdos67.PrimeEstimates.primeReciprocals X := by
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have heta0 : 0 ≤ eta := (inv_pos.mpr hlogy).le
  have heta1 : eta ≤ 1 := by
    have hlogOne : 1 ≤ Real.log (y : ℝ) := by
      have hexpOne : Real.exp 1 < (y : ℝ) := by
        calc
          Real.exp 1 < 3 := Real.exp_one_lt_three
          _ < 23 := by norm_num
          _ ≤ y := by exact_mod_cast hy
      exact (Real.le_log_iff_exp_le (by positivity)).2 hexpOne.le
    dsimp only [eta]
    exact (inv_le_one₀ hlogy).2 hlogOne
  have hsplit := gsA10TwoBlockSecondSecondaryPrefix_eq_prime_add_higherPrimePower
    hmul P₁ P₂ y X eta
  have hprime := norm_gsA10TwoBlockSecondSecondaryPrimePrefix_le
    hmul hbound P₁ P₂ hy hyX hQ₂ hQ₃
  have hhigher := norm_gsA10TwoBlockSecondSecondaryHigherPrimePowerPrefix_le
    hmul hbound P₁ P₂ (y := y) (X := X) (eta := eta)
      (by omega) hyX heta0 heta1 hQ₂ hQ₃
  have hhigher' :
      ‖gsA10SecondSecondaryPrefix
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y)) X
          eta‖ ≤
        12 * (X : ℝ) * Real.log X / y *
          Erdos67.PrimeEstimates.primeReciprocals X := by
    simpa only [gsA10SecondSecondaryHigherPrimePowerPrefix,
      gsA10SecondSecondaryPrefix] using hhigher
  rw [show (Real.log (y : ℝ))⁻¹ = eta by rfl, hsplit]
  exact (norm_add_le _ _).trans (add_le_add hprime hhigher')

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.norm_gsA10TwoBlockSecondSecondaryPrimePrefix_le
#print axioms Erdos67.MRHalaszBands.norm_gsA10TwoBlockSecondSecondaryPrefix_le_prime_add_higher
