import ErdosProblems.Erdos1038.PlatformAngularEnergyKernel

/-!
# Deficit form of the platform block energy

The logarithmic circle kernel is most conveniently represented as the
fixed mass term `2 * log 2` minus the nonnegative circle deficit.  This
file packages that exact normalization and applies the unconditional
platform rearrangement theorem.  The result is the analytic half of
manuscript equation `(5.3)`, separated from the later Fourier evaluation
of the centered two-arc energy.
-/

set_option warningAsError false

open Set MeasureTheory
open scoped ENNReal

namespace Erdos1038

noncomputable section

/-- Normalized logarithmic energy associated with a finite circle deficit.
The two circle masses are `2Q` and `2R`, so the normalization denominator
is `2QR` after the four sign choices in equation `(5.3)`. -/
def normalizedCircleLogEnergy
    (H Q R : ℝ) (deficit : ℝ≥0∞) : ℝ :=
  Real.log H + 2 * Real.log 2 - deficit.toReal / (2 * Q * R)

/-- The normalized logarithmic energy of the two concrete platform circle
densities on one angular interval. -/
def platformNormalizedCircleLogEnergy
    (k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ) : ℝ :=
  normalizedCircleLogEnergy
    (platformCapacity a)
    (platformReferenceCircleRadius k a left right)
    (platformAdjointCircleRadius
      a xMinus xPlus sigmaMinus sigmaPlus left right)
    (circleDensityLogDeficit
      (platformReferenceCircleDensity k a left right)
      (platformAdjointCircleDensity
        a xMinus xPlus sigmaMinus sigmaPlus left right))

/-- The corresponding physical block energy.  Its two physical masses
are the reference and adjoint interval masses from equation `(5.1)`. -/
def platformDeficitBlockEnergy
    (k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ) : ℝ :=
  platformReferenceIntervalMass k a left right *
      platformAdjointIntervalMass
        a xMinus xPlus sigmaMinus sigmaPlus left right *
    platformNormalizedCircleLogEnergy
      k a xMinus xPlus sigmaMinus sigmaPlus left right

/-- The concrete platform deficit is finite.  This is a consequence of
the unconditional rearrangement to a finite centered two-arc deficit. -/
theorem platformCircleDensity_logDeficit_ne_top
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    circleDensityLogDeficit
        (platformReferenceCircleDensity k a left right)
        (platformAdjointCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right) ≠ ∞ := by
  apply ne_top_of_le_ne_top
    (platformCircleTwoArcEnergy_ne_top
      k a xMinus xPlus sigmaMinus sigmaPlus left right)
  exact platformCircleDensity_logDeficit_le_twoArcEnergy
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
    hleft hle hright

/-- Rearrangement gives an unconditional lower bound for the normalized
platform log energy by the normalized centered two-arc log energy. -/
theorem centered_normalizedCircleLogEnergy_le_platform
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi) :
    normalizedCircleLogEnergy
        (platformCapacity a)
        (platformReferenceCircleRadius k a left right)
        (platformAdjointCircleRadius
          a xMinus xPlus sigmaMinus sigmaPlus left right)
        (circleLogTwoArcEnergy
          (platformReferenceCircleRadius k a left right)
          (platformAdjointCircleRadius
            a xMinus xPlus sigmaMinus sigmaPlus left right) 0) ≤
      platformNormalizedCircleLogEnergy
        k a xMinus xPlus sigmaMinus sigmaPlus left right := by
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  have hQ : 0 < platformReferenceCircleRadius k a left right :=
    platformReferenceCircleRadius_pos hk ha ha2 hthreshold
      hleft hlt hright
  have hR : 0 < platformAdjointCircleRadius
      a xMinus xPlus sigmaMinus sigmaPlus left right :=
    platformAdjointCircleRadius_pos
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hlt hright
  unfold normalizedCircleLogEnergy platformNormalizedCircleLogEnergy
  exact normalized_log_energy_ge_of_deficit_le hQ hR
    (platformCircleDensity_logDeficit_le_twoArcEnergy
      hk0 ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      hleft hlt.le hright)
    (platformCircleTwoArcEnergy_ne_top
      k a xMinus xPlus sigmaMinus sigmaPlus left right)

/-- Dividing the physical deficit energy by its positive product of block
masses recovers the normalized energy exactly. -/
theorem platformDeficitBlockEnergy_div_masses
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi) :
    platformDeficitBlockEnergy
          k a xMinus xPlus sigmaMinus sigmaPlus left right /
        (platformReferenceIntervalMass k a left right *
          platformAdjointIntervalMass
            a xMinus xPlus sigmaMinus sigmaPlus left right) =
      platformNormalizedCircleLogEnergy
        k a xMinus xPlus sigmaMinus sigmaPlus left right := by
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  have hQ : 0 < platformReferenceCircleRadius k a left right :=
    platformReferenceCircleRadius_pos hk ha ha2 hthreshold
      hleft hlt hright
  have hR : 0 < platformAdjointCircleRadius
      a xMinus xPlus sigmaMinus sigmaPlus left right :=
    platformAdjointCircleRadius_pos
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hlt hright
  have hq : 0 < platformReferenceIntervalMass k a left right := by
    rw [platformReferenceIntervalMass_eq_endpoint_mul_radius hk0 ha ha2.le]
    exact div_pos
      (mul_pos (platformAPi_pos hk0 ha ha2.le) hQ) Real.pi_pos
  have hr : 0 < platformAdjointIntervalMass
      a xMinus xPlus sigmaMinus sigmaPlus left right := by
    rw [platformAdjointIntervalMass_eq_endpoint_mul_radius
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2]
    exact div_pos
      (mul_pos
        (platformBPi_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2) hR)
      Real.pi_pos
  unfold platformDeficitBlockEnergy
  field_simp [hq.ne', hr.ne']

/-- The physical deficit energy inherits the centered two-arc normalized
lower bound without any remaining rearrangement hypothesis. -/
theorem centered_normalizedCircleLogEnergy_le_deficitBlockEnergy_div
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi) :
    normalizedCircleLogEnergy
        (platformCapacity a)
        (platformReferenceCircleRadius k a left right)
        (platformAdjointCircleRadius
          a xMinus xPlus sigmaMinus sigmaPlus left right)
        (circleLogTwoArcEnergy
          (platformReferenceCircleRadius k a left right)
          (platformAdjointCircleRadius
            a xMinus xPlus sigmaMinus sigmaPlus left right) 0) ≤
      platformDeficitBlockEnergy
          k a xMinus xPlus sigmaMinus sigmaPlus left right /
        (platformReferenceIntervalMass k a left right *
          platformAdjointIntervalMass
            a xMinus xPlus sigmaMinus sigmaPlus left right) := by
  rw [platformDeficitBlockEnergy_div_masses hk ha ha2 hthreshold
    hxMinus hxPlus hsigmaMinus hsigmaPlus hleft hlt hright]
  exact centered_normalizedCircleLogEnergy_le_platform
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
    hleft hlt hright

end

end Erdos1038
