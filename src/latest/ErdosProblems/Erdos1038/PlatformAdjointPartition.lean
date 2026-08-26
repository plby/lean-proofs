import ErdosProblems.Erdos1038.PlatformReferencePartition

/-!
# Adjoint mass of the consecutive platform blocks

The reference CDF cuts partition the whole angular interval.  Although the
cuts were selected using reference mass, summing the adjoint masses of the
same consecutive blocks telescopes to the full adjoint mass.  This is the
identity `∑ r_i = R₀` required by the finite block reduction.
-/

set_option warningAsError false

open Set MeasureTheory
open scoped BigOperators

namespace Erdos1038

noncomputable section

/-- Physical adjoint mass accumulated from angle `0` through `theta`. -/
def platformAdjointCumulative
    (a xMinus xPlus sigmaMinus sigmaPlus theta : ℝ) : ℝ :=
  platformAdjointIntervalMass
    a xMinus xPlus sigmaMinus sigmaPlus 0 theta

lemma platformAdjointCumulative_zero
    (a xMinus xPlus sigmaMinus sigmaPlus : ℝ) :
    platformAdjointCumulative
      a xMinus xPlus sigmaMinus sigmaPlus 0 = 0 := by
  simp [platformAdjointCumulative, platformAdjointIntervalMass]

lemma platformAdjointCumulative_sub
    {a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    platformAdjointCumulative
          a xMinus xPlus sigmaMinus sigmaPlus right -
        platformAdjointCumulative
          a xMinus xPlus sigmaMinus sigmaPlus left =
      platformAdjointIntervalMass
        a xMinus xPlus sigmaMinus sigmaPlus left right := by
  let density : ℝ → ℝ := platformAngularAdjointDensity
    a xMinus xPlus sigmaMinus sigmaPlus
  have hwhole : IntervalIntegrable density volume 0 Real.pi :=
    intervalIntegrable_platformAngularAdjointDensity hxMinus hxPlus ha2
  have hleftInt : IntervalIntegrable density volume 0 left := by
    apply hwhole.mono_set
    rw [uIcc_of_le Real.pi_pos.le, uIcc_of_le hleft]
    exact Icc_subset_Icc_right (hle.trans hright)
  have hrightInt : IntervalIntegrable density volume left right := by
    apply hwhole.mono_set
    rw [uIcc_of_le Real.pi_pos.le, uIcc_of_le hle]
    exact Icc_subset_Icc hleft hright
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    hleftInt hrightInt
  have hdiff :
      (∫ theta : ℝ in 0..right, density theta) -
          ∫ theta : ℝ in 0..left, density theta =
        ∫ theta : ℝ in left..right, density theta := by
    linarith
  unfold platformAdjointCumulative platformAdjointIntervalMass
  change
    (1 / Real.pi * ∫ theta : ℝ in 0..right, density theta) -
        1 / Real.pi * ∫ theta : ℝ in 0..left, density theta =
      1 / Real.pi * ∫ theta : ℝ in left..right, density theta
  rw [← mul_sub, hdiff]

lemma platformAdjointCumulative_pi
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2) :
    platformAdjointCumulative
        a xMinus xPlus sigmaMinus sigmaPlus Real.pi =
      platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus := by
  unfold platformAdjointCumulative platformAdjointIntervalMass
  rw [integral_platformAngularAdjointDensity hxMinus hxPlus ha2]
  field_simp [Real.pi_ne_zero]

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Exact telescoping of the adjoint masses over the blocks determined by
an ordered residual probability. -/
theorem sum_platformAdjointIntervalMass_residualBlocks
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) :
    (∑ i, platformAdjointIntervalMass
        a xMinus xPlus sigmaMinus sigmaPlus
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) =
      platformAdjointMass a xMinus xPlus sigmaMinus sigmaPlus := by
  let G : Icc (0 : ℝ) 1 → ℝ := fun u ↦
    platformAdjointCumulative a xMinus xPlus sigmaMinus sigmaPlus
      (platformReferenceCut k a hk ha ha2 hthreshold u)
  have htel := sum_apply_orderedResidualRight_sub_left_Icc C G
  have hblocks :
      (∑ i, platformAdjointIntervalMass
          a xMinus xPlus sigmaMinus sigmaPlus
            (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
            (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) =
        ∑ i,
          (G ⟨orderedResidualRightMass C i,
              orderedResidualRightMass_mem_Icc C i⟩ -
            G ⟨orderedResidualLeftMass C i,
              orderedResidualLeftMass_mem_Icc C i⟩) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← platformAdjointCumulative_sub hxMinus hxPlus ha2
      (platformResidualBlockLeft_mem_Icc
        C k a hk ha ha2 hthreshold i).1
      (platformResidualBlockLeft_lt_right
        C k a hk ha ha2 hthreshold i).le
      (platformResidualBlockRight_mem_Icc
        C k a hk ha ha2 hthreshold i).2]
    rfl
  rw [hblocks, htel]
  dsimp only [G]
  rw [platformReferenceCut_one, platformReferenceCut_zero,
    platformAdjointCumulative_pi hxMinus hxPlus ha2,
    platformAdjointCumulative_zero, sub_zero]

end

end Erdos1038
