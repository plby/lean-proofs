import ErdosProblems.Erdos67b.MRCofactorWeightedCauchy
import ErdosProblems.Erdos67b.MRGSA10PrimeLambdaSourceCumulative

/-!
# Weighted prime-window energies on the actual fixed-high pair

Apply the proved source affine row at shifts `2 beta` and `0`. The square
root leaves exactly `(X / y)^(2 beta)`, ready to cancel the moving power.
-/

namespace Erdos67b

open MRHalaszBands EulerResidue

noncomputable section

theorem mrExists_weightedPrime_fixedHigh_pair_le :
    ∃ C : ℝ, ∃ Y : ℕ, 1 ≤ C ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (y X : ℕ) (beta sigma T : ℝ) (K : ℕ),
        Y ≤ y → 2 ≤ X → 0 ≤ beta → 1 / 2 ≤ sigma → 0 ≤ T →
        T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
        (gsA10WeightedVerticalEnergy
            (gsA10PrimeLambdaPolynomial hmul y X (taoExponent X - 2 * beta))
            sigma (-T) T) ^ ((1 : ℝ) / 2) *
          (gsA10WeightedVerticalEnergy
            (gsA10PrimeLambdaPolynomial hmul y X (taoExponent X))
            sigma (-T) T) ^ ((1 : ℝ) / 2) ≤
          gsA10PrimeSourceWeightedRowFactor C y X K *
            (((X / y : ℕ) : ℝ) ^ (2 * beta) * gsA10PrimeLambdaHarmonicBudget X) := by
  obtain ⟨C, Y₀, hC, henergy⟩ := exists_two_gsA10WeightedVerticalEnergy_tao_sourceSchedule
  refine ⟨C, max Y₀ 1, hC, ?_⟩
  intro f hmul hbound y X beta sigma T K hY hX hbeta hsigma hT hTK
  have hY₀ : Y₀ ≤ y := (le_max_left _ _).trans hY
  have hy : 1 ≤ y := (le_max_right _ _).trans hY
  have hleft := (henergy hmul hbound y X (2 * beta) sigma T K
    hY₀ hX (by positivity) hsigma hT hTK).1
  have hright := (henergy hmul hbound y X 0 sigma T K
    hY₀ hX le_rfl hsigma hT hTK).2
  let Q := gsA10PrimeSourceWeightedRowFactor C y X K
  let H := gsA10PrimeLambdaHarmonicBudget X
  let D := Q * H
  let growth : ℝ := ((X / y : ℕ) : ℝ) ^ (2 * (2 * beta))
  let EL := gsA10WeightedVerticalEnergy
    (gsA10PrimeLambdaPolynomial hmul y X (taoExponent X - 2 * beta)) sigma (-T) T
  let ER := gsA10WeightedVerticalEnergy
    (gsA10PrimeLambdaPolynomial hmul y X (taoExponent X)) sigma (-T) T
  have hQ : 0 ≤ Q := by
    dsimp only [Q, gsA10PrimeSourceWeightedRowFactor]
    have hmain := gsA10PrimeSourceAffineRowConstant_nonneg hC
    have hslope := gsA10PrimeSourceAffineRowSlope_nonneg hC hy (show 1 ≤ X by omega)
    positivity
  have hH : 0 ≤ H := by dsimp [H, gsA10PrimeLambdaHarmonicBudget]; positivity
  have hD : 0 ≤ D := mul_nonneg hQ hH
  have hgrowth : 0 ≤ growth := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hEL : 0 ≤ EL := mrWeightedVerticalEnergy_nonneg _ sigma hT
  have hER : 0 ≤ ER := mrWeightedVerticalEnergy_nonneg _ sigma hT
  have hleft' : EL ≤ growth * D := by
    apply hleft.trans_eq
    dsimp [gsA10PrimeSourceEnergyConstant, gsA10PrimeSourceEnergySlope,
      gsA10PrimeAffineEnergyConstant, gsA10PrimeAffineEnergySlope,
      growth, D, Q, H, gsA10PrimeSourceWeightedRowFactor]
    ring
  have hright' : ER ≤ D := by
    simp only [add_zero] at hright
    apply hright.trans_eq
    dsimp [gsA10PrimeSourceEnergyConstant, gsA10PrimeSourceEnergySlope,
      gsA10PrimeAffineEnergyConstant, gsA10PrimeAffineEnergySlope,
      D, Q, H, gsA10PrimeSourceWeightedRowFactor]
    ring
  have hgrowthRoot : growth ^ ((1 : ℝ) / 2) = ((X / y : ℕ) : ℝ) ^ (2 * beta) := by
    dsimp only [growth]
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  have hDroot : D ^ ((1 : ℝ) / 2) * D ^ ((1 : ℝ) / 2) = D := by
    rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hD]
  change EL ^ ((1 : ℝ) / 2) * ER ^ ((1 : ℝ) / 2) ≤ Q * (_ * H)
  calc
    _ ≤ (growth * D) ^ ((1 : ℝ) / 2) * D ^ ((1 : ℝ) / 2) :=
      mul_le_mul (Real.rpow_le_rpow hEL hleft' (by norm_num))
        (Real.rpow_le_rpow hER hright' (by norm_num))
        (Real.rpow_nonneg hER _) (Real.rpow_nonneg (mul_nonneg hgrowth hD) _)
    _ = ((X / y : ℕ) : ℝ) ^ (2 * beta) * D := by
      rw [Real.mul_rpow hgrowth hD, hgrowthRoot, mul_assoc, hDroot]
    _ = _ := by dsimp only [D]; ring

end

end Erdos67b
