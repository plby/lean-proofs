import ErdosProblems.Erdos67b.MRTypicalCofactorReconstruction
import ErdosProblems.Erdos67b.MRGSA10SecondSecondaryHigherPrimePower

/-! # Higher-prime-power secondary of the actual typical cofactor -/

open scoped BigOperators

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrNorm_positivePrefix_mul_le_reciprocalMass
    (a b : ArithmeticFunction ℂ) (X : ℕ)
    (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1) :
    ‖positivePrefixSum (fun n ↦ (a * b) n) X‖ ≤
      (X : ℝ) * ∑ c ∈ Finset.Icc 1 X, ‖b c‖ / (c : ℝ) := by
  rw [mul_comm a b]
  apply (norm_positivePrefixSum_mul_le_cutoff b a X).trans
  calc
    _ ≤ ∑ c ∈ Finset.Icc 1 X, ‖b c‖ * ((X / c : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ ∑ k ∈ Finset.Icc 1 (X / c), (1 : ℝ) :=
          Finset.sum_le_sum (fun k hk ↦ ha k (Finset.mem_Icc.mp hk).1)
        _ = _ := by simp
    _ ≤ ∑ c ∈ Finset.Icc 1 X, ‖b c‖ * ((X : ℝ) / (c : ℝ)) :=
      Finset.sum_le_sum (fun c _ ↦ mul_le_mul_of_nonneg_left Nat.cast_div_le (norm_nonneg _))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring

theorem mrNorm_typicalCofactorSecondSecondaryHigher_le_mass
    {ι : Type*} (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ι) (B : ι → Finset ℕ) (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ}
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    {eta : ℝ} (heta : 0 ≤ eta) :
    ‖gsA10SecondSecondaryPrefix (mrTypicalCofactorLowArithmetic A J B f y)
        (gsA9HighArithmetic f y) (gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y))
        X eta‖ ≤ eta * (X : ℝ) * gsA10HigherPrimePowerGeometricMass y X := by
  let low := mrTypicalCofactorLowArithmetic A J B f y
  let high := gsA9HighArithmetic f y
  let lambda := gsA9HighGeneralizedMangoldt hmul y
  unfold gsA10SecondSecondaryPrefix
  rw [show eta * (X : ℝ) * gsA10HigherPrimePowerGeometricMass y X =
    eta * ((X : ℝ) * gsA10HigherPrimePowerGeometricMass y X) by ring]
  apply norm_intervalIntegral_positivePrefixSum_le heta
  intro alpha halpha
  let gamma : ℝ := 2 * eta + alpha
  let a : ArithmeticFunction ℂ := low * gsRealShift gamma high
  let b : ArithmeticFunction ℂ := gsRealShift alpha (gsHigherPrimePowerPart lambda)
  have hgamma : 0 ≤ gamma := by dsimp [gamma]; linarith [halpha.1]
  have ha : ∀ n, 0 < n → ‖a n‖ ≤ 1 := fun n _ ↦
    mrNorm_typicalCofactorSecondary_le_one A hA J B hB hmul hbound y hAy hBy hgamma n
  have hreassoc : (low * gsRealShift alpha (gsHigherPrimePowerPart lambda)) *
      gsRealShift gamma high = a * b := by dsimp [a, b]; ring
  change ‖positivePrefixSum (fun n ↦
    ((low * gsRealShift alpha (gsHigherPrimePowerPart lambda)) * gsRealShift gamma high) n) X‖ ≤
      (X : ℝ) * gsA10HigherPrimePowerGeometricMass y X
  rw [hreassoc]
  exact (mrNorm_positivePrefix_mul_le_reciprocalMass a b X ha).trans
    (mul_le_mul_of_nonneg_left (sum_norm_shift_higherPrimePowerPart_div_le_mass
      hmul hbound halpha.1) (Nat.cast_nonneg _))

theorem mrNorm_typicalCofactorSecondSecondaryHigher_le
    {ι : Type*} (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ι) (B : ι → Finset ℕ) (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {y X : ℕ} (hy : 3 ≤ y) (hyX : y ≤ X)
    (hAy : ∀ p ∈ A, p ≤ y) (hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
    {eta : ℝ} (heta : 0 ≤ eta) (heta1 : eta ≤ 1) :
    ‖gsA10SecondSecondaryPrefix (mrTypicalCofactorLowArithmetic A J B f y)
        (gsA9HighArithmetic f y) (gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y))
        X eta‖ ≤ 12 * (X : ℝ) * Real.log X / y * PrimeEstimates.primeReciprocals X := by
  have hraw := mrNorm_typicalCofactorSecondSecondaryHigher_le_mass
    A hA J B hB hmul hbound (X := X) hAy hBy heta
  have hmass := gsA10HigherPrimePowerGeometricMass_le (X := X) hy
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hprime := PrimeEstimates.primeReciprocals_nonneg X
  let E : ℝ := 12 * Real.log X / y * PrimeEstimates.primeReciprocals X
  have hE : 0 ≤ E := by dsimp [E]; positivity
  calc
    _ ≤ eta * (X : ℝ) * gsA10HigherPrimePowerGeometricMass y X := hraw
    _ ≤ eta * (X : ℝ) * E :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg heta (Nat.cast_nonneg _))
    _ ≤ (X : ℝ) * E := mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (Nat.cast_nonneg X) heta1) hE
    _ = _ := by dsimp [E]; ring

end

end Erdos67b
