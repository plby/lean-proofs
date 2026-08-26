import ErdosProblems.Erdos1038.PlatformResidualMaterialField
import ErdosProblems.Erdos1038.PlatformAdjointAbelSeries

/-!
# Cosine data of the residual material field

The endpoint-corrected adjoint argument applies Abel regularization to the
cosine coefficients of the concrete density-weighted material velocity.
This file defines those coefficients and proves the uniform bound required
by the existing Abel-series infrastructure directly from `L¹` integrability.
-/

set_option warningAsError false

open MeasureTheory Set

namespace Erdos1038

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The normalized cosine coefficient of the concrete material field. -/
def platformResidualMaterialCosineCoefficient
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ) : ℝ :=
  (1 / Real.pi) *
    ∫ theta in 0..Real.pi,
      platformResidualMaterialField C k a hk ha ha2 hthreshold theta *
        Real.cos ((n : ℝ) * theta)

/-- Frequency zero, separated in the convention
`f0 + 2 * sum_{n >= 1} f_n cos(n theta)`. -/
def platformResidualMaterialMean
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) : ℝ :=
  (1 / Real.pi) *
    ∫ theta in 0..Real.pi,
      platformResidualMaterialField C k a hk ha ha2 hthreshold theta

/-- An explicit uniform coefficient bound supplied by the `L¹` norm. -/
def platformResidualMaterialCoefficientBound
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) : ℝ :=
  (1 / Real.pi) *
    ∫ theta in 0..Real.pi,
      |platformResidualMaterialField C k a hk ha ha2 hthreshold theta|

theorem platformResidualMaterialCosineCoefficient_zero
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    platformResidualMaterialCosineCoefficient C k a hk ha ha2 hthreshold 0 =
      platformResidualMaterialMean C k a hk ha ha2 hthreshold := by
  unfold platformResidualMaterialCosineCoefficient
    platformResidualMaterialMean
  simp

theorem platformResidualMaterialCoefficientBound_nonneg
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    0 ≤ platformResidualMaterialCoefficientBound
      C k a hk ha ha2 hthreshold := by
  unfold platformResidualMaterialCoefficientBound
  exact mul_nonneg (one_div_nonneg.mpr Real.pi_pos.le)
    (intervalIntegral.integral_nonneg_of_forall Real.pi_pos.le
      (fun theta ↦ abs_nonneg _))

/-- Every material cosine coefficient is bounded by the normalized `L¹`
norm, uniformly in frequency. -/
theorem platformResidualMaterialCosineCoefficient_bounded
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    RealSequenceBoundedBy
      (platformResidualMaterialCosineCoefficient
        C k a hk ha ha2 hthreshold)
      (platformResidualMaterialCoefficientBound
        C k a hk ha ha2 hthreshold) := by
  let F := platformResidualMaterialField C k a hk ha ha2 hthreshold
  have hF : IntervalIntegrable F volume 0 Real.pi :=
    intervalIntegrable_platformResidualMaterialField
      C k a hk ha ha2 hthreshold
  intro n
  have hcos : Continuous (fun theta : ℝ ↦ Real.cos ((n : ℝ) * theta)) := by
    fun_prop
  have hprod : IntervalIntegrable
      (fun theta ↦ F theta * Real.cos ((n : ℝ) * theta))
      volume 0 Real.pi :=
    hF.mul_continuousOn hcos.continuousOn
  have hmono :
      (∫ theta in 0..Real.pi,
          |F theta * Real.cos ((n : ℝ) * theta)|) ≤
        ∫ theta in 0..Real.pi, |F theta| := by
    apply intervalIntegral.integral_mono_on Real.pi_pos.le hprod.abs hF.abs
    intro theta _htheta
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg (F theta))
      (Real.abs_cos_le_one ((n : ℝ) * theta))
  have habs :
      |∫ theta in 0..Real.pi,
          F theta * Real.cos ((n : ℝ) * theta)| ≤
        ∫ theta in 0..Real.pi, |F theta| :=
    (intervalIntegral.abs_integral_le_integral_abs Real.pi_pos.le).trans hmono
  unfold platformResidualMaterialCosineCoefficient
    platformResidualMaterialCoefficientBound
  rw [abs_mul, abs_of_pos (one_div_pos.mpr Real.pi_pos)]
  exact mul_le_mul_of_nonneg_left habs (one_div_nonneg.mpr Real.pi_pos.le)

end

end Erdos1038
