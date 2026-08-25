import ErdosProblems.Erdos67.MRGSA10RealOrdinaryPrefixJointSource
import ErdosProblems.Erdos67.MRGSA10TwoBlockAtypicalSourceScale

/-!
# Non-contour A.10 errors at the source-scale blocks

This file packages the joint projection, global Shiu secondary, and
source-window mass into one fixed negative logarithmic power.  The moving
Perron rectangle is deliberately kept separate.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Fixed coefficient for all source-scale ordinary-prefix errors other
than the moving Perron rectangle and atypical density. -/
def gsA10SourceScaleNoncontourConstant (S : ℕ) : ℝ :=
  (9 + gsA10GlobalSecondaryShiuConstant) *
      Real.sqrt (2 * Real.log 2) +
    gsA10MovingPerronAveragedMassConstant *
      ((256 * S : ℝ) * (1 + Real.sqrt (2 * Real.log 2)))

theorem gsA10SourceScaleNoncontourConstant_nonneg (S : ℕ) :
    0 ≤ gsA10SourceScaleNoncontourConstant S := by
  unfold gsA10SourceScaleNoncontourConstant
  exact add_nonneg
    (mul_nonneg
      (add_nonneg (by norm_num) gsA10GlobalSecondaryShiuConstant_nonneg)
      (Real.sqrt_nonneg _))
    (mul_nonneg gsA10MovingPerronAveragedMassConstant_nonneg (by positivity))

/-- Joint projection plus both global secondaries are
`O((log Z)^(-1/4))` for the source-scale block choice. -/
theorem jointSource_add_shiu_sourceBlock_le_realLog_quarter
    {S Z : ℕ} (hS : 1 ≤ S)
    (hK : 5 ≤ Erdos67.gsA10SourceBlockExponent S Z) (hZ : 4 ≤ Z) :
    gsA10JointMovingProjectionSourceBudget
          (2 ^ ((Erdos67.gsA10SourceBlockExponent S Z) ^ 2)) Z +
        gsA10GlobalSecondaryShiuConstant *
          Real.log
              ((2 ^ ((Erdos67.gsA10SourceBlockExponent S Z) ^ 2) : ℕ) : ℝ) /
            Real.log (Z : ℝ) ≤
      gsA10SourceScaleNoncontourConstant S *
        ((Real.log (Z : ℝ)) ^ (-(1 / 4 : ℝ))) := by
  let y : ℕ := 2 ^ ((Erdos67.gsA10SourceBlockExponent S Z) ^ 2)
  let R : ℝ := Real.log (Z : ℝ)
  let A : ℝ :=
    (9 + gsA10GlobalSecondaryShiuConstant) *
      Real.sqrt (2 * Real.log 2)
  let F : ℝ :=
    (256 * S : ℝ) * (1 + Real.sqrt (2 * Real.log 2))
  have hmain :=
    Erdos67.jointNearProjection_add_secondary_sourceBlock_le_realLog_quarter
      (Csecondary := gsA10GlobalSecondaryShiuConstant)
      gsA10GlobalSecondaryShiuConstant_nonneg hS (by omega) hZ
  have hinv := Erdos67.inv_log_sourceBlockCutoff_le_realLog_quarter
    hS hK hZ
  have hmass :
      gsA10MovingPerronAveragedMassConstant *
          (Real.log (y : ℝ))⁻¹ ≤
        gsA10MovingPerronAveragedMassConstant *
          (F * R ^ (-(1 / 4 : ℝ))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa only [y, F, R] using hinv)
      gsA10MovingPerronAveragedMassConstant_nonneg
  calc
    gsA10JointMovingProjectionSourceBudget y Z +
          gsA10GlobalSecondaryShiuConstant *
            Real.log (y : ℝ) / Real.log (Z : ℝ) =
        (4 * (harmonic Z : ℝ) * Real.log (y : ℝ) /
              Real.log (Z : ℝ) ^ 2 +
            Real.log (y : ℝ) / (2 * (Z : ℝ)) +
            gsA10GlobalSecondaryShiuConstant *
              (Real.log (y : ℝ) / Real.log (Z : ℝ))) +
          gsA10MovingPerronAveragedMassConstant *
            (Real.log (y : ℝ))⁻¹ := by
      unfold gsA10JointMovingProjectionSourceBudget
      ring
    _ ≤ A * R ^ (-(1 / 4 : ℝ)) +
          gsA10MovingPerronAveragedMassConstant *
            (F * R ^ (-(1 / 4 : ℝ))) := by
      exact add_le_add (by simpa only [y, R, A] using hmain) hmass
    _ = gsA10SourceScaleNoncontourConstant S *
          R ^ (-(1 / 4 : ℝ)) := by
      unfold gsA10SourceScaleNoncontourConstant
      dsimp only [A, F]
      ring
    _ = gsA10SourceScaleNoncontourConstant S *
        ((Real.log (Z : ℝ)) ^ (-(1 / 4 : ℝ))) := by rfl

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.jointSource_add_shiu_sourceBlock_le_realLog_quarter
