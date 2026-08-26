import ErdosProblems.Erdos1038.PlatformResidualMaterialBoundaryKernel
import ErdosProblems.Erdos1038.PlatformResidualBlockTangent

/-!
# Identification of the material boundary transform

At a point in the interior of residual block `i`, the boundary transform
can be written without a principal value by subtracting the smooth value of
that block at the observation point.  This file identifies the resulting
regularized block sum with the reduced directional field used by the block
tangent argument.
-/

set_option warningAsError false

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- Boundary-kernel endpoint increments telescope over the canonical
residual partition. -/
theorem sum_platformHalfCircleBoundaryLogDifference_right_sub_left
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (theta : ℝ) :
    (∑ i,
      (platformHalfCircleBoundaryLogDifference theta
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i) -
        platformHalfCircleBoundaryLogDifference theta
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i))) = 0 := by
  let F : Icc (0 : ℝ) 1 → ℝ := fun u ↦
    platformHalfCircleBoundaryLogDifference theta
      (platformReferenceCut k a hk ha ha2 hthreshold u)
  have htel := sum_apply_orderedResidualRight_sub_left_Icc C F
  change (∑ i,
      (F ⟨orderedResidualRightMass C i,
          orderedResidualRightMass_mem_Icc C i⟩ -
        F ⟨orderedResidualLeftMass C i,
          orderedResidualLeftMass_mem_Icc C i⟩)) = 0
  rw [htel]
  dsimp only [F]
  rw [platformReferenceCut_one, platformReferenceCut_zero]
  simp

/-- Away from the diagonal, the boundary kernel is continuous even when
the second argument is one of the half-circle endpoints. -/
theorem continuousAt_platformHalfCircleBoundaryLogDifference_of_ne
    {theta phi : ℝ} (htheta : theta ∈ Ioo 0 Real.pi)
    (hphi : phi ∈ Icc 0 Real.pi) (hne : theta ≠ phi) :
    ContinuousAt (platformHalfCircleBoundaryLogDifference theta) phi := by
  have hthetaIcc : theta ∈ Icc 0 Real.pi :=
    ⟨htheta.1.le, htheta.2.le⟩
  have hminus : 0 < platformBoundaryPoissonDenominator (theta - phi) :=
    platformBoundaryPoissonDenominator_sub_pos_of_ne
      hthetaIcc hphi hne
  have horder : platformBoundaryPoissonDenominator (theta - phi) ≤
      platformBoundaryPoissonDenominator (theta + phi) := by
    rw [← sub_nonneg, platformBoundaryPoissonDenominator_sub]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_nonneg_of_le_pi hthetaIcc.1 hthetaIcc.2))
      (Real.sin_nonneg_of_nonneg_of_le_pi hphi.1 hphi.2)
  have hplus : 0 < platformBoundaryPoissonDenominator (theta + phi) :=
    hminus.trans_le horder
  have hplusCont : ContinuousAt
      (fun x : ℝ ↦ platformBoundaryPoissonDenominator (theta + x)) phi := by
    unfold platformBoundaryPoissonDenominator
    fun_prop
  have hminusCont : ContinuousAt
      (fun x : ℝ ↦ platformBoundaryPoissonDenominator (theta - x)) phi := by
    unfold platformBoundaryPoissonDenominator
    fun_prop
  unfold platformHalfCircleBoundaryLogDifference
  exact ((hplusCont.log hplus.ne').sub
    (hminusCont.log hminus.ne')).const_mul (1 / 2)

/-- The ordinary, removable-singularity block integral obtained by
subtracting the observation-block material value. -/
def platformResidualMaterialRegularizedBoundaryBlock
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i j : iota) (theta : ℝ) : ℝ :=
  (1 / Real.pi) *
    ∫ phi in
      platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
      platformResidualBlockRight C k a hk ha ha2 hthreshold j,
      (platformResidualMaterialSmoothBlock C k a i theta -
          platformResidualMaterialSmoothBlock C k a j phi) /
        (platformAngularDistance a theta - platformAngularDistance a phi)

private theorem platformAngularDistance_sub_ne_of_mem_block_ne
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i j : iota) {theta phi : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
    (hphi : phi ∈ Icc
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold j)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold j))
    (hne : phi ≠ theta) :
    platformAngularDistance a theta - platformAngularDistance a phi ≠ 0 := by
  have hthetaIcc : theta ∈ Icc 0 Real.pi :=
    ⟨(platformResidualBlockLeft_mem_Icc C k a hk ha ha2
        hthreshold i).1.trans htheta.1.le,
      htheta.2.le.trans
        (platformResidualBlockRight_mem_Icc C k a hk ha ha2
          hthreshold i).2⟩
  have hphiIcc : phi ∈ Icc 0 Real.pi :=
    ⟨(platformResidualBlockLeft_mem_Icc C k a hk ha ha2
        hthreshold j).1.trans hphi.1,
      hphi.2.trans
        (platformResidualBlockRight_mem_Icc C k a hk ha ha2
          hthreshold j).2⟩
  rcases lt_or_gt_of_ne hne with hphiTheta | hthetaPhi
  · exact (sub_pos.mpr (platformAngularDistance_strictMonoOn ha2
      hphiIcc hthetaIcc hphiTheta)).ne'
  · exact (sub_neg.mpr (platformAngularDistance_strictMonoOn ha2
      hthetaIcc hphiIcc hthetaPhi)).ne

omit [LinearOrder iota] in
/-- Algebraic decomposition of the regularized material quotient into the
target-velocity quotient and the smooth density-resolvent correction. -/
theorem platformResidualMaterial_regularizedQuotient_eq
    (C : ResidualConfiguration iota)
    (k a : ℝ) (i j : iota) {theta phi : ℝ}
    (ha : 0 < a) (ha2 : a < 2)
    (hden : platformAngularDistance a theta -
      platformAngularDistance a phi ≠ 0) :
    (platformResidualMaterialSmoothBlock C k a i theta -
        platformResidualMaterialSmoothBlock C k a j phi) /
          (platformAngularDistance a theta -
            platformAngularDistance a phi) =
      platformAngularDensity k a phi *
          ((platformResidualBlockMaterialVelocity C a i theta -
              platformResidualBlockMaterialVelocity C a j phi) /
            (platformAngularDistance a theta -
              platformAngularDistance a phi)) +
        platformResidualBlockMaterialVelocity C a i theta *
          (k * Real.sqrt (2 * a) /
            (platformAngularDistance a theta *
              platformAngularDistance a phi)) := by
  have hdtheta : platformAngularDistance a theta ≠ 0 :=
    (ha.trans_le (platformAngularDistance_ge_all ha2.le theta)).ne'
  have hdphi : platformAngularDistance a phi ≠ 0 :=
    (ha.trans_le (platformAngularDistance_ge_all ha2.le phi)).ne'
  unfold platformResidualMaterialSmoothBlock
    platformResidualBlockMaterialVelocity platformAngularDensity
    platformDensityCoefficient
  field_simp [hden, hdtheta, hdphi]
  ring

omit [LinearOrder iota] in
private theorem continuous_platformAngularDensity_for_boundaryIdentification
    (k : ℝ) {a : ℝ} (ha : 0 < a) (ha2 : a < 2) :
    Continuous (platformAngularDensity k a) := by
  have hd : Continuous (platformAngularDistance a) := by
    unfold platformAngularDistance
    fun_prop
  have hdne (theta : ℝ) : platformAngularDistance a theta ≠ 0 :=
    (ha.trans_le (platformAngularDistance_ge_all ha2.le theta)).ne'
  unfold platformAngularDensity platformDensityCoefficient
  exact continuous_const.sub (continuous_const.div hd hdne)

private theorem intervalIntegrable_platformResidualVelocityQuotient
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i j : iota) {theta : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    IntervalIntegrable
      (fun phi : ℝ ↦ platformAngularDensity k a phi *
        ((platformResidualBlockMaterialVelocity C a i theta -
            platformResidualBlockMaterialVelocity C a j phi) /
          (platformAngularDistance a theta -
            platformAngularDistance a phi)))
      volume
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold j)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold j) := by
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold j
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold j
  have hleftRight : left ≤ right :=
    (platformResidualBlockLeft_lt_right C k a hk ha ha2
      hthreshold j).le
  by_cases hji : j = i
  · subst j
    have hdensityFull := intervalIntegrable_platformAngularDensity k ha ha2.le
    have hdensity : IntervalIntegrable (platformAngularDensity k a)
        volume left right := by
      apply hdensityFull.mono_set
      rw [uIcc_of_le hleftRight, uIcc_of_le Real.pi_pos.le]
      exact Icc_subset_Icc
        (platformResidualBlockLeft_mem_Icc C k a hk ha ha2
          hthreshold i).1
        (platformResidualBlockRight_mem_Icc C k a hk ha ha2
          hthreshold i).2
    apply hdensity.neg.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae
        (Measure.ae_ne (volume : Measure ℝ) theta)]
      with phi hphi hphiNe
    rw [uIoc_of_le hleftRight] at hphi
    have hphiIcc : phi ∈ Icc left right := ⟨hphi.1.le, hphi.2⟩
    have hden := platformAngularDistance_sub_ne_of_mem_block_ne
      C k a hk ha ha2 hthreshold i i htheta hphiIcc hphiNe
    unfold platformResidualBlockMaterialVelocity
    field_simp [hden]
    simp only [Pi.neg_apply]
    ring
  · have hleftMem := platformResidualBlockLeft_mem_Icc
      C k a hk ha ha2 hthreshold j
    have hrightMem := platformResidualBlockRight_mem_Icc
      C k a hk ha ha2 hthreshold j
    have hden (phi : ℝ) (hphi : phi ∈ Icc left right) :
        platformAngularDistance a theta -
            platformAngularDistance a phi ≠ 0 := by
      apply platformAngularDistance_sub_ne_of_mem_block_ne
        C k a hk ha ha2 hthreshold i j htheta hphi
      intro hEq
      subst phi
      have hthetaInJ : theta ∈ Icc left right := hphi
      rcases lt_or_gt_of_ne hji with hjiLt | hijLt
      · have hordered := platformResidualBlocks_ordered
          C k a hk ha ha2 hthreshold hjiLt
        exact (not_lt_of_ge hthetaInJ.2)
          (hordered.trans_lt htheta.1)
      · have hordered := platformResidualBlocks_ordered
          C k a hk ha ha2 hthreshold hijLt
        exact (not_lt_of_ge hthetaInJ.1)
          (htheta.2.trans_le hordered)
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hleftRight]
    have hd : Continuous (platformAngularDistance a) := by
      unfold platformAngularDistance
      fun_prop
    have hv : Continuous (platformResidualBlockMaterialVelocity C a j) := by
      unfold platformResidualBlockMaterialVelocity
      exact continuous_const.sub hd
    exact (continuous_platformAngularDensity_for_boundaryIdentification
      k ha ha2).continuousOn.mul
        ((continuous_const.sub hv).continuousOn.div
          (continuous_const.sub hd).continuousOn hden)

private theorem intervalIntegrable_platformResidualDensityCorrection
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i j : iota) (theta : ℝ) :
    IntervalIntegrable
      (fun phi : ℝ ↦
        platformResidualBlockMaterialVelocity C a i theta *
          (k * Real.sqrt (2 * a) /
            (platformAngularDistance a theta *
              platformAngularDistance a phi)))
      volume
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold j)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold j) := by
  have hreciprocal := intervalIntegrable_one_div_platformAngularDistance
    ha ha2.le
  have hblock : IntervalIntegrable
      (fun phi : ℝ ↦ 1 / platformAngularDistance a phi)
      volume
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold j)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold j) := by
    apply hreciprocal.mono_set
    rw [uIcc_of_le
        (platformResidualBlockLeft_lt_right C k a hk ha ha2
          hthreshold j).le,
      uIcc_of_le Real.pi_pos.le]
    exact Icc_subset_Icc
      (platformResidualBlockLeft_mem_Icc C k a hk ha ha2
        hthreshold j).1
      (platformResidualBlockRight_mem_Icc C k a hk ha ha2
        hthreshold j).2
  have hscaled := hblock.const_mul
    (platformResidualBlockMaterialVelocity C a i theta *
      (k * Real.sqrt (2 * a) / platformAngularDistance a theta))
  convert! hscaled using 1
  funext phi
  ring

private theorem intervalIntegrable_platformResidualMaterialRegularizedQuotient
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i j : iota) {theta : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    IntervalIntegrable
      (fun phi : ℝ ↦
        (platformResidualMaterialSmoothBlock C k a i theta -
            platformResidualMaterialSmoothBlock C k a j phi) /
          (platformAngularDistance a theta -
            platformAngularDistance a phi))
      volume
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold j)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold j) := by
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold j
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold j
  have hleftRight : left ≤ right :=
    (platformResidualBlockLeft_lt_right C k a hk ha ha2
      hthreshold j).le
  have hmain := intervalIntegrable_platformResidualVelocityQuotient
    C k a hk ha ha2 hthreshold i j htheta
  have hcorrection := intervalIntegrable_platformResidualDensityCorrection
    C k a hk ha ha2 hthreshold i j theta
  have hsum := hmain.add hcorrection
  apply hsum.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) theta)]
    with phi hphi hphiNe
  rw [uIoc_of_le hleftRight] at hphi
  have hphiIcc : phi ∈ Icc left right := ⟨hphi.1.le, hphi.2⟩
  have hden := platformAngularDistance_sub_ne_of_mem_block_ne
    C k a hk ha ha2 hthreshold i j htheta hphiIcc hphiNe
  exact (platformResidualMaterial_regularizedQuotient_eq
    C k a i j ha ha2 hden).symm

private theorem hasDerivAt_platformResidualMaterialRegularizedBoundaryPrimitive
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i j : iota) {theta phi : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
    (hphi : phi ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold j)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold j))
    (hphiNe : phi ≠ theta) :
    HasDerivAt
      (fun x : ℝ ↦
        (platformResidualMaterialSmoothBlock C k a j x -
            platformResidualMaterialSmoothBlock C k a i theta) *
          platformHalfCircleBoundaryLogDifference theta x)
      (deriv (platformResidualMaterialSmoothBlock C k a j) phi *
          platformHalfCircleBoundaryLogDifference theta phi -
        platformRadius a * Real.sin theta *
          ((platformResidualMaterialSmoothBlock C k a i theta -
              platformResidualMaterialSmoothBlock C k a j phi) /
            (platformAngularDistance a theta -
              platformAngularDistance a phi))) phi := by
  have hthetaHalf : theta ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨(platformResidualBlockLeft_mem_Icc C k a hk ha ha2
        hthreshold i).1.trans_lt htheta.1,
      htheta.2.trans_le
        (platformResidualBlockRight_mem_Icc C k a hk ha ha2
          hthreshold i).2⟩
  have hphiHalf : phi ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨(platformResidualBlockLeft_mem_Icc C k a hk ha ha2
        hthreshold j).1.trans_lt hphi.1,
      hphi.2.trans_le
        (platformResidualBlockRight_mem_Icc C k a hk ha ha2
          hthreshold j).2⟩
  have hphiIcc : phi ∈ Icc
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold j)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold j) :=
    ⟨hphi.1.le, hphi.2.le⟩
  have hden := platformAngularDistance_sub_ne_of_mem_block_ne
    C k a hk ha ha2 hthreshold i j htheta hphiIcc hphiNe
  have hcos : Real.cos phi - Real.cos theta ≠ 0 := by
    intro hzero
    apply hden
    rw [sub_eq_zero] at hzero ⊢
    unfold platformAngularDistance
    rw [hzero]
  have hdistance :
      platformAngularDistance a theta - platformAngularDistance a phi =
        platformRadius a * (Real.cos phi - Real.cos theta) := by
    unfold platformAngularDistance
    ring
  have hG := hasDerivAt_platformResidualMaterialSmoothBlock
    C k ha ha2 j phi
  have hK := hasDerivAt_platformHalfCircleBoundaryLogDifference_phi
    hthetaHalf hphiHalf hphiNe.symm
  convert! (hG.sub_const
    (platformResidualMaterialSmoothBlock C k a i theta)).mul hK using 1
  field_simp [hden, hcos]
  rw [hdistance]
  ring

private theorem platformResidualObservationPoint_ne_of_mem_other_block
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i j : iota) {theta phi : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
    (hphi : phi ∈ Icc
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold j)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold j))
    (hji : j ≠ i) :
    phi ≠ theta := by
  intro hEq
  subst phi
  rcases lt_or_gt_of_ne hji with hjiLt | hijLt
  · have hordered := platformResidualBlocks_ordered
      C k a hk ha ha2 hthreshold hjiLt
    exact (not_lt_of_ge hphi.2) (hordered.trans_lt htheta.1)
  · have hordered := platformResidualBlocks_ordered
      C k a hk ha ha2 hthreshold hijLt
    exact (not_lt_of_ge hphi.1) (htheta.2.trans_le hordered)

private theorem platformResidualMaterialBoundaryBlock_eq_regularized_of_ne
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i j : iota) {theta : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
    (hji : j ≠ i) :
    (platformResidualMaterialSmoothBlock C k a j
          (platformResidualBlockRight C k a hk ha ha2 hthreshold j) -
        platformResidualMaterialSmoothBlock C k a i theta) *
          platformHalfCircleBoundaryLogDifference theta
            (platformResidualBlockRight C k a hk ha ha2 hthreshold j) -
      (platformResidualMaterialSmoothBlock C k a j
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold j) -
        platformResidualMaterialSmoothBlock C k a i theta) *
          platformHalfCircleBoundaryLogDifference theta
            (platformResidualBlockLeft C k a hk ha ha2 hthreshold j) -
      (∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
          platformResidualBlockRight C k a hk ha ha2 hthreshold j,
        deriv (platformResidualMaterialSmoothBlock C k a j) phi *
          platformHalfCircleBoundaryLogDifference theta phi) =
      -platformRadius a * Real.sin theta *
        (∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
          platformResidualBlockRight C k a hk ha ha2 hthreshold j,
          (platformResidualMaterialSmoothBlock C k a i theta -
              platformResidualMaterialSmoothBlock C k a j phi) /
            (platformAngularDistance a theta -
              platformAngularDistance a phi)) := by
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold j
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold j
  let G := platformResidualMaterialSmoothBlock C k a j
  let Gi := platformResidualMaterialSmoothBlock C k a i theta
  let K := platformHalfCircleBoundaryLogDifference theta
  let Q : ℝ → ℝ := fun phi ↦
    (Gi - G phi) /
      (platformAngularDistance a theta - platformAngularDistance a phi)
  let P : ℝ → ℝ := fun phi ↦ (G phi - Gi) * K phi
  let c := platformRadius a * Real.sin theta
  let D : ℝ → ℝ := fun phi ↦
    deriv G phi * K phi - c * Q phi
  have hleftRight : left ≤ right :=
    (platformResidualBlockLeft_lt_right C k a hk ha ha2
      hthreshold j).le
  have hthetaHalf : theta ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨(platformResidualBlockLeft_mem_Icc C k a hk ha ha2
        hthreshold i).1.trans_lt htheta.1,
      htheta.2.trans_le
        (platformResidualBlockRight_mem_Icc C k a hk ha ha2
          hthreshold i).2⟩
  have hblockHalf : Icc left right ⊆ Icc (0 : ℝ) Real.pi := by
    exact Icc_subset_Icc
      (platformResidualBlockLeft_mem_Icc C k a hk ha ha2
        hthreshold j).1
      (platformResidualBlockRight_mem_Icc C k a hk ha ha2
        hthreshold j).2
  have hne (phi : ℝ) (hphi : phi ∈ Icc left right) : phi ≠ theta := by
    exact platformResidualObservationPoint_ne_of_mem_other_block
      C k a hk ha ha2 hthreshold i j htheta hphi hji
  have hPcont : ContinuousOn P (Icc left right) := by
    intro phi hphi
    have hphiHalf := hblockHalf hphi
    have hGcont : ContinuousAt (fun x ↦ G x - Gi) phi := by
      dsimp only [G, Gi]
      exact ((contDiff_platformResidualMaterialSmoothBlock
        C k ha ha2 j).continuous.continuousAt).sub_const _
    have hKcont : ContinuousAt K phi := by
      dsimp only [K]
      exact continuousAt_platformHalfCircleBoundaryLogDifference_of_ne
        hthetaHalf hphiHalf (hne phi hphi).symm
    exact (hGcont.mul hKcont).continuousWithinAt
  have hDderiv (phi : ℝ) (hphi : phi ∈ Ioo left right) :
      HasDerivAt P (D phi) phi := by
    dsimp only [P, D, G, Gi, K, Q, c]
    exact hasDerivAt_platformResidualMaterialRegularizedBoundaryPrimitive
      C k a hk ha ha2 hthreshold i j htheta hphi (hne phi ⟨hphi.1.le, hphi.2.le⟩)
  have hGK : IntervalIntegrable (fun phi ↦ deriv G phi * K phi)
      volume left right := by
    have hKint := intervalIntegrable_platformHalfCircleBoundaryLogDifference
      theta left right
    have hG'cont : ContinuousOn (deriv G) (uIcc left right) := by
      dsimp only [G]
      exact (contDiff_platformResidualMaterialSmoothBlock
        C k ha ha2 j).continuous_deriv (by norm_num) |>.continuousOn
    exact hKint.continuousOn_mul hG'cont
  have hQ : IntervalIntegrable Q volume left right := by
    dsimp only [Q, G, Gi, left, right]
    exact intervalIntegrable_platformResidualMaterialRegularizedQuotient
      C k a hk ha ha2 hthreshold i j htheta
  have hDint : IntervalIntegrable D volume left right := by
    dsimp only [D]
    exact hGK.sub (hQ.const_mul c)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hleftRight hPcont hDderiv hDint
  dsimp only [D] at hFTC
  rw [intervalIntegral.integral_sub hGK (hQ.const_mul c),
    intervalIntegral.integral_const_mul] at hFTC
  dsimp only [P, Q, G, Gi, K, c, left, right] at hFTC ⊢
  linarith

omit [LinearOrder iota] in
private theorem tendsto_platformResidualMaterialRegularizedBoundaryPrimitive_diagonal
    (C : ResidualConfiguration iota) (k : ℝ) {a theta : ℝ}
    (ha : 0 < a) (ha2 : a < 2) (i : iota)
    (hdiag : Tendsto
      (fun phi : ℝ ↦ (phi - theta) *
        platformHalfCircleBoundaryLogDifference theta phi)
      (𝓝 theta) (𝓝 0)) :
    Tendsto
        (fun phi : ℝ ↦
          (platformResidualMaterialSmoothBlock C k a i phi -
              platformResidualMaterialSmoothBlock C k a i theta) *
            platformHalfCircleBoundaryLogDifference theta phi)
        (𝓝[<] theta) (𝓝 0) ∧
      Tendsto
        (fun phi : ℝ ↦
          (platformResidualMaterialSmoothBlock C k a i phi -
              platformResidualMaterialSmoothBlock C k a i theta) *
            platformHalfCircleBoundaryLogDifference theta phi)
        (𝓝[>] theta) (𝓝 0) := by
  let G := platformResidualMaterialSmoothBlock C k a i
  let K := platformHalfCircleBoundaryLogDifference theta
  have hG := hasDerivAt_platformResidualMaterialSmoothBlock
    C k ha ha2 i theta
  have hslope := hasDerivAt_iff_tendsto_slope_left_right.mp hG
  have hdiagLeft : Tendsto (fun phi : ℝ ↦ (phi - theta) * K phi)
      (𝓝[<] theta) (𝓝 0) :=
    hdiag.mono_left inf_le_left
  have hdiagRight : Tendsto (fun phi : ℝ ↦ (phi - theta) * K phi)
      (𝓝[>] theta) (𝓝 0) :=
    hdiag.mono_left inf_le_left
  constructor
  · have hprod := hslope.1.mul hdiagLeft
    have hprod0 : Tendsto
        (fun x ↦ slope G theta x * ((x - theta) * K x))
        (𝓝[<] theta) (𝓝 0) := by simpa using! hprod
    apply hprod0.congr'
    filter_upwards [self_mem_nhdsWithin] with phi hphi
    have hlt : phi < theta := hphi
    dsimp only [G, K]
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hlt.ne]
  · have hprod := hslope.2.mul hdiagRight
    have hprod0 : Tendsto
        (fun x ↦ slope G theta x * ((x - theta) * K x))
        (𝓝[>] theta) (𝓝 0) := by simpa using! hprod
    apply hprod0.congr'
    filter_upwards [self_mem_nhdsWithin] with phi hphi
    have hgt : theta < phi := hphi
    dsimp only [G, K]
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hgt.ne']

private theorem platformResidualMaterialBoundaryBlock_eq_regularized_self
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i : iota) {theta : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    (platformResidualMaterialSmoothBlock C k a i
          (platformResidualBlockRight C k a hk ha ha2 hthreshold i) -
        platformResidualMaterialSmoothBlock C k a i theta) *
          platformHalfCircleBoundaryLogDifference theta
            (platformResidualBlockRight C k a hk ha ha2 hthreshold i) -
      (platformResidualMaterialSmoothBlock C k a i
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) -
        platformResidualMaterialSmoothBlock C k a i theta) *
          platformHalfCircleBoundaryLogDifference theta
            (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) -
      (∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
          platformResidualBlockRight C k a hk ha ha2 hthreshold i,
        deriv (platformResidualMaterialSmoothBlock C k a i) phi *
          platformHalfCircleBoundaryLogDifference theta phi) =
      -platformRadius a * Real.sin theta *
        (∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
          platformResidualBlockRight C k a hk ha ha2 hthreshold i,
          (platformResidualMaterialSmoothBlock C k a i theta -
              platformResidualMaterialSmoothBlock C k a i phi) /
            (platformAngularDistance a theta -
              platformAngularDistance a phi)) := by
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold i
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold i
  let G := platformResidualMaterialSmoothBlock C k a i
  let Gi := G theta
  let K := platformHalfCircleBoundaryLogDifference theta
  let Q : ℝ → ℝ := fun phi ↦
    (Gi - G phi) /
      (platformAngularDistance a theta - platformAngularDistance a phi)
  let P : ℝ → ℝ := fun phi ↦ (G phi - Gi) * K phi
  let c := platformRadius a * Real.sin theta
  let D : ℝ → ℝ := fun phi ↦
    deriv G phi * K phi - c * Q phi
  have hleftTheta : left < theta := htheta.1
  have hthetaRight : theta < right := htheta.2
  have hleftRight : left ≤ right := hleftTheta.le.trans hthetaRight.le
  have hthetaHalf : theta ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨(platformResidualBlockLeft_mem_Icc C k a hk ha ha2
        hthreshold i).1.trans_lt htheta.1,
      htheta.2.trans_le
        (platformResidualBlockRight_mem_Icc C k a hk ha ha2
          hthreshold i).2⟩
  have hleftHalf := platformResidualBlockLeft_mem_Icc
    C k a hk ha ha2 hthreshold i
  have hrightHalf := platformResidualBlockRight_mem_Icc
    C k a hk ha ha2 hthreshold i
  have hGK : IntervalIntegrable (fun phi ↦ deriv G phi * K phi)
      volume left right := by
    have hKint := intervalIntegrable_platformHalfCircleBoundaryLogDifference
      theta left right
    have hG'cont : ContinuousOn (deriv G) (uIcc left right) := by
      dsimp only [G]
      exact (contDiff_platformResidualMaterialSmoothBlock
        C k ha ha2 i).continuous_deriv (by norm_num) |>.continuousOn
    exact hKint.continuousOn_mul hG'cont
  have hQ : IntervalIntegrable Q volume left right := by
    dsimp only [Q, G, Gi, left, right]
    exact intervalIntegrable_platformResidualMaterialRegularizedQuotient
      C k a hk ha ha2 hthreshold i i htheta
  have hDint : IntervalIntegrable D volume left right := by
    dsimp only [D]
    exact hGK.sub (hQ.const_mul c)
  have hDleft : IntervalIntegrable D volume left theta := by
    apply hDint.mono_set
    rw [uIcc_of_le hleftTheta.le, uIcc_of_le hleftRight]
    exact Icc_subset_Icc_right hthetaRight.le
  have hDright : IntervalIntegrable D volume theta right := by
    apply hDint.mono_set
    rw [uIcc_of_le hthetaRight.le, uIcc_of_le hleftRight]
    exact Icc_subset_Icc_left hleftTheta.le
  have hPleftCont : ContinuousAt P left := by
    have hGcont : ContinuousAt (fun x ↦ G x - Gi) left := by
      dsimp only [G, Gi]
      exact ((contDiff_platformResidualMaterialSmoothBlock
        C k ha ha2 i).continuous.continuousAt).sub_const _
    have hKcont : ContinuousAt K left := by
      dsimp only [K]
      exact continuousAt_platformHalfCircleBoundaryLogDifference_of_ne
        hthetaHalf hleftHalf hleftTheta.ne'
    exact hGcont.mul hKcont
  have hPrightCont : ContinuousAt P right := by
    have hGcont : ContinuousAt (fun x ↦ G x - Gi) right := by
      dsimp only [G, Gi]
      exact ((contDiff_platformResidualMaterialSmoothBlock
        C k ha ha2 i).continuous.continuousAt).sub_const _
    have hKcont : ContinuousAt K right := by
      dsimp only [K]
      exact continuousAt_platformHalfCircleBoundaryLogDifference_of_ne
        hthetaHalf hrightHalf hthetaRight.ne
    exact hGcont.mul hKcont
  have hPdiag :=
    tendsto_platformResidualMaterialRegularizedBoundaryPrimitive_diagonal
      C k ha ha2 i
        (tendsto_sub_mul_platformHalfCircleBoundaryLogDifference hthetaHalf)
  have hleftFTC : (∫ phi in left..theta, D phi) = 0 - P left := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      hleftTheta
    · intro phi hphi
      dsimp only [P, D, G, Gi, K, Q, c]
      exact hasDerivAt_platformResidualMaterialRegularizedBoundaryPrimitive
        C k a hk ha ha2 hthreshold i i htheta
          ⟨hphi.1, hphi.2.trans hthetaRight⟩ hphi.2.ne
    · exact hDleft
    · exact tendsto_nhdsWithin_of_tendsto_nhds hPleftCont.tendsto
    · exact hPdiag.1
  have hrightFTC : (∫ phi in theta..right, D phi) = P right - 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      hthetaRight
    · intro phi hphi
      dsimp only [P, D, G, Gi, K, Q, c]
      exact hasDerivAt_platformResidualMaterialRegularizedBoundaryPrimitive
        C k a hk ha ha2 hthreshold i i htheta
          ⟨hleftTheta.trans hphi.1, hphi.2⟩ hphi.1.ne'
    · exact hDright
    · exact hPdiag.2
    · exact tendsto_nhdsWithin_of_tendsto_nhds hPrightCont.tendsto
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    hDleft hDright
  have hFTC : (∫ phi in left..right, D phi) = P right - P left := by
    linarith
  dsimp only [D] at hFTC
  rw [intervalIntegral.integral_sub hGK (hQ.const_mul c),
    intervalIntegral.integral_const_mul] at hFTC
  dsimp only [P, Q, G, Gi, K, c, left, right] at hFTC ⊢
  linarith

private theorem platformResidualMaterialBoundaryBlock_eq_regularized
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i j : iota) {theta : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    (platformResidualMaterialSmoothBlock C k a j
          (platformResidualBlockRight C k a hk ha ha2 hthreshold j) -
        platformResidualMaterialSmoothBlock C k a i theta) *
          platformHalfCircleBoundaryLogDifference theta
            (platformResidualBlockRight C k a hk ha ha2 hthreshold j) -
      (platformResidualMaterialSmoothBlock C k a j
          (platformResidualBlockLeft C k a hk ha ha2 hthreshold j) -
        platformResidualMaterialSmoothBlock C k a i theta) *
          platformHalfCircleBoundaryLogDifference theta
            (platformResidualBlockLeft C k a hk ha ha2 hthreshold j) -
      (∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
          platformResidualBlockRight C k a hk ha ha2 hthreshold j,
        deriv (platformResidualMaterialSmoothBlock C k a j) phi *
          platformHalfCircleBoundaryLogDifference theta phi) =
      -platformRadius a * Real.sin theta *
        (∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
          platformResidualBlockRight C k a hk ha ha2 hthreshold j,
          (platformResidualMaterialSmoothBlock C k a i theta -
              platformResidualMaterialSmoothBlock C k a j phi) /
            (platformAngularDistance a theta -
              platformAngularDistance a phi)) := by
  by_cases hji : j = i
  · subst j
    exact platformResidualMaterialBoundaryBlock_eq_regularized_self
      C k a hk ha ha2 hthreshold i htheta
  · exact platformResidualMaterialBoundaryBlock_eq_regularized_of_ne
      C k a hk ha ha2 hthreshold i j htheta hji

/-- After subtracting the material value of the observation block, the
boundary-log representation is an ordinary sum of removable-singularity
quotient integrals. -/
theorem platformResidualMaterialBoundaryLogRepresentation_eq_integral_sum
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i : iota) {theta : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    platformResidualMaterialBoundaryLogRepresentation C k a
        hk ha ha2 hthreshold theta =
      -(platformRadius a * Real.sin theta) / 2 *
        ∑ j, ∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
          platformResidualBlockRight C k a hk ha ha2 hthreshold j,
          (platformResidualMaterialSmoothBlock C k a i theta -
              platformResidualMaterialSmoothBlock C k a j phi) /
            (platformAngularDistance a theta -
              platformAngularDistance a phi) := by
  classical
  let Gi := platformResidualMaterialSmoothBlock C k a i theta
  let L : iota → ℝ := fun j ↦
    platformResidualBlockLeft C k a hk ha ha2 hthreshold j
  let R : iota → ℝ := fun j ↦
    platformResidualBlockRight C k a hk ha ha2 hthreshold j
  let G : iota → ℝ → ℝ := fun j ↦
    platformResidualMaterialSmoothBlock C k a j
  let K := platformHalfCircleBoundaryLogDifference theta
  let I : iota → ℝ := fun j ↦
    ∫ phi in L j..R j, deriv (G j) phi * K phi
  let Q : iota → ℝ := fun j ↦
    ∫ phi in L j..R j,
      (Gi - G j phi) /
        (platformAngularDistance a theta - platformAngularDistance a phi)
  let E : iota → ℝ := fun j ↦
    G j (R j) * K (R j) - G j (L j) * K (L j) - I j
  let A : iota → ℝ := fun j ↦
    (G j (R j) - Gi) * K (R j) -
      (G j (L j) - Gi) * K (L j) - I j
  have htel : (∑ j, (K (R j) - K (L j))) = 0 := by
    dsimp only [K, R, L]
    exact sum_platformHalfCircleBoundaryLogDifference_right_sub_left
      C k a hk ha ha2 hthreshold theta
  have hEA : (∑ j, E j) = ∑ j, A j := by
    calc
      (∑ j, E j) = ∑ j, (A j + Gi * (K (R j) - K (L j))) := by
        apply Finset.sum_congr rfl
        intro j _hj
        dsimp only [E, A]
        ring
      _ = (∑ j, A j) + Gi * ∑ j, (K (R j) - K (L j)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ j, A j := by rw [htel]; ring
  have hAQ : ∀ j, A j =
      -(platformRadius a * Real.sin theta) * Q j := by
    intro j
    dsimp only [A, Q, G, Gi, K, I, L, R]
    simpa only [neg_mul] using!
      (platformResidualMaterialBoundaryBlock_eq_regularized
        C k a hk ha ha2 hthreshold i j htheta)
  calc
    platformResidualMaterialBoundaryLogRepresentation C k a
        hk ha ha2 hthreshold theta = (1 / 2 : ℝ) * ∑ j, E j := by
      unfold platformResidualMaterialBoundaryLogRepresentation
      dsimp only [E, G, K, I, L, R]
      rw [Finset.mul_sum]
    _ = (1 / 2 : ℝ) * ∑ j, A j := by rw [hEA]
    _ = (1 / 2 : ℝ) * ∑ j,
        (-(platformRadius a * Real.sin theta) * Q j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      exact hAQ j
    _ = -(platformRadius a * Real.sin theta) / 2 * ∑ j, Q j := by
      rw [← Finset.mul_sum]
      ring
    _ = _ := by rfl

/-- Each regularized boundary block splits into its target-velocity quotient
and the universal smooth density correction. -/
theorem platformResidualMaterialRegularizedBoundaryBlock_eq_velocity_add_correction
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i j : iota) {theta : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    platformResidualMaterialRegularizedBoundaryBlock C k a
        hk ha ha2 hthreshold i j theta =
      (1 / Real.pi) *
        (∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
          platformResidualBlockRight C k a hk ha ha2 hthreshold j,
          platformAngularDensity k a phi *
            ((platformResidualBlockMaterialVelocity C a i theta -
                platformResidualBlockMaterialVelocity C a j phi) /
              (platformAngularDistance a theta -
                platformAngularDistance a phi))) +
      (1 / Real.pi) *
        (∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
          platformResidualBlockRight C k a hk ha ha2 hthreshold j,
          platformResidualBlockMaterialVelocity C a i theta *
            (k * Real.sqrt (2 * a) /
              (platformAngularDistance a theta *
                platformAngularDistance a phi))) := by
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold j
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold j
  have hleftRight : left ≤ right :=
    (platformResidualBlockLeft_lt_right C k a hk ha ha2
      hthreshold j).le
  have hmain := intervalIntegrable_platformResidualVelocityQuotient
    C k a hk ha ha2 hthreshold i j htheta
  have hcorrection := intervalIntegrable_platformResidualDensityCorrection
    C k a hk ha ha2 hthreshold i j theta
  have heq : ∀ᵐ phi ∂volume, phi ∈ uIoc left right →
      (platformResidualMaterialSmoothBlock C k a i theta -
          platformResidualMaterialSmoothBlock C k a j phi) /
          (platformAngularDistance a theta -
            platformAngularDistance a phi) =
        platformAngularDensity k a phi *
            ((platformResidualBlockMaterialVelocity C a i theta -
                platformResidualBlockMaterialVelocity C a j phi) /
              (platformAngularDistance a theta -
                platformAngularDistance a phi)) +
          platformResidualBlockMaterialVelocity C a i theta *
            (k * Real.sqrt (2 * a) /
              (platformAngularDistance a theta *
                platformAngularDistance a phi)) := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) theta]
      with phi hphiNe
    intro hphi
    rw [uIoc_of_le hleftRight] at hphi
    have hphiIcc : phi ∈ Icc left right := ⟨hphi.1.le, hphi.2⟩
    have hden := platformAngularDistance_sub_ne_of_mem_block_ne
      C k a hk ha ha2 hthreshold i j htheta hphiIcc hphiNe
    exact platformResidualMaterial_regularizedQuotient_eq
      C k a i j ha ha2 hden
  unfold platformResidualMaterialRegularizedBoundaryBlock
  change (1 / Real.pi) * (∫ phi in left..right, _) = _
  rw [intervalIntegral.integral_congr_ae heq,
    intervalIntegral.integral_add hmain hcorrection]
  ring

/-- The velocity-quotient pieces are exactly the off-block directional
terms together with the removable same-block contribution `-q_i`. -/
theorem sum_platformResidualVelocityQuotient_eq_offBlock_sub_weight
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i : iota) {theta : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    (∑ j, (1 / Real.pi) *
      (∫ phi in
        platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
        platformResidualBlockRight C k a hk ha ha2 hthreshold j,
        platformAngularDensity k a phi *
          ((platformResidualBlockMaterialVelocity C a i theta -
              platformResidualBlockMaterialVelocity C a j phi) /
            (platformAngularDistance a theta -
              platformAngularDistance a phi)))) =
      (∑ j ∈ Finset.univ.erase i,
        platformResidualOffBlockDirectionalTerm C k a hk ha ha2
          hthreshold i j theta) - C.weight i := by
  classical
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold i
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold i
  let selfTerm : ℝ := (1 / Real.pi) *
    (∫ phi in left..right,
      platformAngularDensity k a phi *
        ((platformResidualBlockMaterialVelocity C a i theta -
            platformResidualBlockMaterialVelocity C a i phi) /
          (platformAngularDistance a theta -
            platformAngularDistance a phi)))
  have hleftRight : left ≤ right :=
    (platformResidualBlockLeft_lt_right C k a hk ha ha2
      hthreshold i).le
  have hselfIntegral :
      (∫ phi in left..right,
        platformAngularDensity k a phi *
          ((platformResidualBlockMaterialVelocity C a i theta -
              platformResidualBlockMaterialVelocity C a i phi) /
            (platformAngularDistance a theta -
              platformAngularDistance a phi))) =
        ∫ phi in left..right, -platformAngularDensity k a phi := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) theta]
      with phi hphiNe
    intro hphi
    rw [uIoc_of_le hleftRight] at hphi
    have hphiIcc : phi ∈ Icc left right := ⟨hphi.1.le, hphi.2⟩
    have hden := platformAngularDistance_sub_ne_of_mem_block_ne
      C k a hk ha ha2 hthreshold i i htheta hphiIcc hphiNe
    unfold platformResidualBlockMaterialVelocity
    field_simp [hden]
    ring
  have hmass := platformReferenceIntervalMass_residualBlock
    C k a hk ha ha2 hthreshold i
  have hself : selfTerm = -C.weight i := by
    dsimp only [selfTerm]
    rw [hselfIntegral, intervalIntegral.integral_neg]
    change (1 / Real.pi) * (∫ phi in left..right,
      platformAngularDensity k a phi) = C.weight i at hmass
    rw [← hmass]
    ring
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hoff :
      (∑ j ∈ Finset.univ.erase i, (1 / Real.pi) *
        (∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
          platformResidualBlockRight C k a hk ha ha2 hthreshold j,
          platformAngularDensity k a phi *
            ((platformResidualBlockMaterialVelocity C a i theta -
                platformResidualBlockMaterialVelocity C a j phi) /
              (platformAngularDistance a theta -
                platformAngularDistance a phi)))) =
        ∑ j ∈ Finset.univ.erase i,
          platformResidualOffBlockDirectionalTerm C k a hk ha ha2
            hthreshold i j theta := by
    apply Finset.sum_congr rfl
    intro j _hj
    rfl
  rw [hoff]
  change selfTerm = -C.weight i at hself
  change
    (∑ j ∈ Finset.univ.erase i,
      platformResidualOffBlockDirectionalTerm C k a hk ha ha2
        hthreshold i j theta) + selfTerm = _
  rw [hself]
  ring

/-- The universal density correction recombines over the partition and is
exactly the external-field term `k v_i(theta) / d(theta)`. -/
theorem sum_platformResidualDensityCorrection_eq_external
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i : iota) (theta : ℝ) :
    (∑ j, (1 / Real.pi) *
      (∫ phi in
        platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
        platformResidualBlockRight C k a hk ha ha2 hthreshold j,
        platformResidualBlockMaterialVelocity C a i theta *
          (k * Real.sqrt (2 * a) /
            (platformAngularDistance a theta *
              platformAngularDistance a phi)))) =
      k * (platformResidualBlockMaterialVelocity C a i theta /
        platformAngularDistance a theta) := by
  let v := platformResidualBlockMaterialVelocity C a i theta
  let d := platformAngularDistance a theta
  let S := Real.sqrt (2 * a)
  let correction : ℝ → ℝ := fun phi ↦
    v * (k * S / (d * platformAngularDistance a phi))
  have hd : 0 < d := by
    dsimp only [d]
    exact ha.trans_le (platformAngularDistance_ge_all ha2.le theta)
  have hS : 0 < S := by
    dsimp only [S]
    exact Real.sqrt_pos.2 (mul_pos (by norm_num) ha)
  have hcorrection : IntervalIntegrable correction volume 0 Real.pi := by
    have hreciprocal := intervalIntegrable_one_div_platformAngularDistance
      ha ha2.le
    have hscaled := hreciprocal.const_mul (v * (k * S / d))
    convert! hscaled using 1
    funext phi
    dsimp only [correction]
    ring
  have hpartition := sum_intervalIntegral_platformResidualBlocks
    C k a hk ha ha2 hthreshold hcorrection
  have hreciprocal := integral_one_div_platformAngularDistance ha ha2.le
  have hfun : correction = fun phi : ℝ ↦
      (v * (k * S / d)) * (1 / platformAngularDistance a phi) := by
    funext phi
    dsimp only [correction]
    ring
  calc
    (∑ j, (1 / Real.pi) *
        (∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
          platformResidualBlockRight C k a hk ha ha2 hthreshold j,
          platformResidualBlockMaterialVelocity C a i theta *
            (k * Real.sqrt (2 * a) /
              (platformAngularDistance a theta *
                platformAngularDistance a phi)))) =
        (1 / Real.pi) *
          ∑ j, ∫ phi in
            platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
            platformResidualBlockRight C k a hk ha ha2 hthreshold j,
            correction phi := by
              rw [Finset.mul_sum]
    _ = (1 / Real.pi) * (∫ phi in 0..Real.pi, correction phi) := by
      rw [hpartition]
    _ = (1 / Real.pi) *
        ((v * (k * S / d)) *
          (∫ phi in 0..Real.pi,
            1 / platformAngularDistance a phi)) := by
      rw [hfun, intervalIntegral.integral_const_mul]
    _ = k * (platformResidualBlockMaterialVelocity C a i theta /
        platformAngularDistance a theta) := by
      rw [hreciprocal]
      dsimp only [v, d, S]
      field_simp [Real.pi_ne_zero, hS.ne', hd.ne']

/-- The complete regularized boundary quotient is precisely the reduced
directional field on the containing block. -/
theorem sum_platformResidualMaterialRegularizedBoundaryBlock_eq_reducedDirectionalField
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i : iota) {theta : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    (∑ j, platformResidualMaterialRegularizedBoundaryBlock C k a
      hk ha ha2 hthreshold i j theta) =
      platformResidualReducedDirectionalField C k a
        hk ha ha2 hthreshold i theta := by
  classical
  have hsplit :
      (∑ j, platformResidualMaterialRegularizedBoundaryBlock C k a
        hk ha ha2 hthreshold i j theta) =
        (∑ j, (1 / Real.pi) *
          (∫ phi in
            platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
            platformResidualBlockRight C k a hk ha ha2 hthreshold j,
            platformAngularDensity k a phi *
              ((platformResidualBlockMaterialVelocity C a i theta -
                  platformResidualBlockMaterialVelocity C a j phi) /
                (platformAngularDistance a theta -
                  platformAngularDistance a phi)))) +
        (∑ j, (1 / Real.pi) *
          (∫ phi in
            platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
            platformResidualBlockRight C k a hk ha ha2 hthreshold j,
            platformResidualBlockMaterialVelocity C a i theta *
              (k * Real.sqrt (2 * a) /
                (platformAngularDistance a theta *
                  platformAngularDistance a phi)))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    exact platformResidualMaterialRegularizedBoundaryBlock_eq_velocity_add_correction
      C k a hk ha ha2 hthreshold i j htheta
  rw [hsplit,
    sum_platformResidualVelocityQuotient_eq_offBlock_sub_weight
      C k a hk ha ha2 hthreshold i htheta,
    sum_platformResidualDensityCorrection_eq_external
      C k a hk ha ha2 hthreshold i theta]
  unfold platformResidualReducedDirectionalField
  ring

/-- The boundary logarithmic transform, with its exact Hilbert scaling,
is the reduced directional field on the unique block containing the
observation point. -/
theorem scaled_platformResidualMaterialBoundaryLogRepresentation_eq_reducedDirectionalField
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i : iota) {theta : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    -(2 / platformRadius a) * (1 / Real.pi) *
        platformResidualMaterialBoundaryLogRepresentation C k a
          hk ha ha2 hthreshold theta /
      Real.sin theta =
      platformResidualReducedDirectionalField C k a
        hk ha ha2 hthreshold i theta := by
  classical
  have hthetaHalf : theta ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨(platformResidualBlockLeft_mem_Icc C k a hk ha ha2
        hthreshold i).1.trans_lt htheta.1,
      htheta.2.trans_le
        (platformResidualBlockRight_mem_Icc C k a hk ha ha2
          hthreshold i).2⟩
  have hr : 0 < platformRadius a := platformRadius_pos ha2
  have hsin : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi hthetaHalf.1 hthetaHalf.2
  have hrepresentation :=
    platformResidualMaterialBoundaryLogRepresentation_eq_integral_sum
      C k a hk ha ha2 hthreshold i htheta
  have hregularized :
      (∑ j, platformResidualMaterialRegularizedBoundaryBlock C k a
        hk ha ha2 hthreshold i j theta) =
      (1 / Real.pi) *
        ∑ j, ∫ phi in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
          platformResidualBlockRight C k a hk ha ha2 hthreshold j,
          (platformResidualMaterialSmoothBlock C k a i theta -
              platformResidualMaterialSmoothBlock C k a j phi) /
            (platformAngularDistance a theta -
              platformAngularDistance a phi) := by
    unfold platformResidualMaterialRegularizedBoundaryBlock
    rw [Finset.mul_sum]
  calc
    -(2 / platformRadius a) * (1 / Real.pi) *
          platformResidualMaterialBoundaryLogRepresentation C k a
            hk ha ha2 hthreshold theta /
        Real.sin theta =
        (1 / Real.pi) *
          ∑ j, ∫ phi in
            platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
            platformResidualBlockRight C k a hk ha ha2 hthreshold j,
            (platformResidualMaterialSmoothBlock C k a i theta -
                platformResidualMaterialSmoothBlock C k a j phi) /
              (platformAngularDistance a theta -
                platformAngularDistance a phi) := by
      rw [hrepresentation]
      field_simp [hr.ne', hsin.ne', Real.pi_ne_zero]
    _ = ∑ j, platformResidualMaterialRegularizedBoundaryBlock C k a
          hk ha ha2 hthreshold i j theta := hregularized.symm
    _ = platformResidualReducedDirectionalField C k a
          hk ha ha2 hthreshold i theta :=
      sum_platformResidualMaterialRegularizedBoundaryBlock_eq_reducedDirectionalField
        C k a hk ha ha2 hthreshold i htheta

end

end Erdos1038
