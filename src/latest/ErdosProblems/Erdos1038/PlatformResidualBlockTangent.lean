import ErdosProblems.Erdos1038.PlatformDeficitAngularIntegral
import ErdosProblems.Erdos1038.PlatformResidualMaterialField
import ErdosProblems.Erdos1038.PlatformPotential
import ErdosProblems.Erdos1038.HighKBlockFunctionalAssembly

/-!
# Concrete angular form of the residual block tangent

The supporting interface in `HighKBlockFunctionalAssembly` is stated using
`platformDeficitBlockEnergy`.  This file replaces that abstract block energy
by its physical mixed angular integral.  It also records the two pointwise
logarithmic tangent inequalities used before integration in manuscript
equations `(4.27)`--`(4.28)`.
-/

set_option warningAsError false

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1038

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The canonical residual blocks recombine any integrable angular
observable into its integral over the full platform interval. -/
theorem sum_intervalIntegral_platformResidualBlocks
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 Real.pi) :
    (∑ i, ∫ theta : ℝ in
        platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
        platformResidualBlockRight C k a hk ha ha2 hthreshold i,
        f theta) =
      ∫ theta : ℝ in 0..Real.pi, f theta := by
  let F : Icc (0 : ℝ) 1 → ℝ := fun u ↦
    ∫ theta : ℝ in 0..
      platformReferenceCut k a hk ha ha2 hthreshold u, f theta
  calc
    (∑ i, ∫ theta : ℝ in
        platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
        platformResidualBlockRight C k a hk ha ha2 hthreshold i,
        f theta) =
        ∑ i,
          (F ⟨orderedResidualRightMass C i,
              orderedResidualRightMass_mem_Icc C i⟩ -
            F ⟨orderedResidualLeftMass C i,
              orderedResidualLeftMass_mem_Icc C i⟩) := by
      apply Finset.sum_congr rfl
      intro i _hi
      let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold i
      let right := platformResidualBlockRight C k a hk ha ha2 hthreshold i
      have hleftMem :=
        platformResidualBlockLeft_mem_Icc C k a hk ha ha2 hthreshold i
      have hrightMem :=
        platformResidualBlockRight_mem_Icc C k a hk ha ha2 hthreshold i
      have hleftRight :=
        (platformResidualBlockLeft_lt_right C k a hk ha ha2
          hthreshold i).le
      have hzeroLeft : IntervalIntegrable f volume 0 left := by
        apply hf.mono_set
        rw [uIcc_of_le hleftMem.1, uIcc_of_le Real.pi_pos.le]
        exact Icc_subset_Icc_right hleftMem.2
      have hleftRightInt : IntervalIntegrable f volume left right := by
        apply hf.mono_set
        rw [uIcc_of_le hleftRight, uIcc_of_le Real.pi_pos.le]
        exact Icc_subset_Icc hleftMem.1 hrightMem.2
      change (∫ theta : ℝ in left..right, f theta) =
        (∫ theta : ℝ in 0..right, f theta) -
          ∫ theta : ℝ in 0..left, f theta
      rw [← intervalIntegral.integral_add_adjacent_intervals
        hzeroLeft hleftRightInt]
      ring
    _ = F ⟨1, by constructor <;> norm_num⟩ -
          F ⟨0, by constructor <;> norm_num⟩ :=
      sum_apply_orderedResidualRight_sub_left_Icc C F
    _ = ∫ theta : ℝ in 0..Real.pi, f theta := by
      dsimp only [F]
      rw [platformReferenceCut_one, platformReferenceCut_zero]
      simp

private lemma continuous_platformAngularDensity_for_blockTangent
    (k : ℝ) {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) :
    Continuous (platformAngularDensity k a) := by
  have hradius : 0 ≤ platformRadius a := by
    unfold platformRadius
    linarith
  have hdistance : Continuous (platformAngularDistance a) := by
    unfold platformAngularDistance
    fun_prop
  have hdistancePos (theta : ℝ) :
      0 < platformAngularDistance a theta := by
    have hcos := Real.cos_le_one theta
    have hmul : platformRadius a * Real.cos theta ≤ platformRadius a :=
      by simpa only [mul_one] using! mul_le_mul_of_nonneg_left hcos hradius
    have hlower : a ≤ platformAngularDistance a theta := by
      unfold platformAngularDistance
      linarith [platformCenter_sub_radius a]
    exact ha.trans_le hlower
  unfold platformAngularDensity platformDensityCoefficient
  exact continuous_const.sub
    (continuous_const.div hdistance fun theta ↦ (hdistancePos theta).ne')

/-- The weighted logarithmic potential is integrable even when its pole
lies inside the platform interval. -/
theorem intervalIntegrable_platformAngularDensity_mul_logDistance
    (k : ℝ) {a theta : ℝ} (ha : 0 < a) (ha2 : a < 2) :
    IntervalIntegrable
      (fun phi : ℝ ↦
        platformAngularDensity k a phi *
          Real.log |platformAngularDistance a theta -
            platformAngularDistance a phi|)
      volume 0 Real.pi := by
  have hlog : IntervalIntegrable
      (fun phi : ℝ ↦
        Real.log |platformAngularDistance a theta -
          platformAngularDistance a phi|)
      volume 0 Real.pi := by
    have han : AnalyticOnNhd ℝ
        (fun phi : ℝ ↦ platformAngularDistance a theta -
          platformAngularDistance a phi) Set.univ :=
      fun _ _ ↦ by
        unfold platformAngularDistance
        fun_prop
    have hmer : MeromorphicOn
        (fun phi : ℝ ↦ platformAngularDistance a theta -
          platformAngularDistance a phi)
        (Set.uIcc 0 Real.pi) :=
      fun x _hx ↦ han.meromorphicOn x (Set.mem_univ x)
    simpa only [Real.norm_eq_abs] using!
      MeromorphicOn.intervalIntegrable_log_norm hmer
  exact hlog.continuousOn_mul
    (continuous_platformAngularDensity_for_blockTangent
      k ha ha2.le).continuousOn

/-- Material velocity on the block assigned to one target atom. -/
def platformResidualBlockMaterialVelocity
    (C : ResidualConfiguration ι)
    (a : ℝ) (i : ι) (theta : ℝ) : ℝ :=
  C.location i - platformAngularDistance a theta

/-- The piecewise material field is the platform density times the block
material velocity. -/
theorem platformResidualMaterialField_eq_density_mul_blockVelocity
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) {theta : ℝ}
    (htheta : theta ∈ Ioc
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    platformResidualMaterialField C k a hk ha ha2 hthreshold theta =
      platformAngularDensity k a theta *
        platformResidualBlockMaterialVelocity C a i theta := by
  exact platformResidualMaterialField_eq_on_block C k a hk ha ha2
    hthreshold i htheta

/-- Reference logarithmic potential contributed by one canonical block. -/
def platformResidualBlockLogPotential
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) (theta : ℝ) : ℝ :=
  (1 / Real.pi) *
    ∫ phi : ℝ in
      platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
      platformResidualBlockRight C k a hk ha ha2 hthreshold i,
      platformAngularDensity k a phi *
        Real.log |platformAngularDistance a theta -
          platformAngularDistance a phi|

/-- The off-block part of the unreduced first variation at a point of block
`i`, integrated over block `j`. -/
def platformResidualOffBlockDirectionalTerm
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i j : ι) (theta : ℝ) : ℝ :=
  (1 / Real.pi) *
    ∫ phi : ℝ in
      platformResidualBlockLeft C k a hk ha ha2 hthreshold j..
      platformResidualBlockRight C k a hk ha ha2 hthreshold j,
      platformAngularDensity k a phi *
        ((platformResidualBlockMaterialVelocity C a i theta -
            platformResidualBlockMaterialVelocity C a j phi) /
          (platformAngularDistance a theta -
            platformAngularDistance a phi))

/-- The pointwise unreduced first variation with the same-block principal
value already replaced by its exact value `-q_i`. -/
def platformResidualReducedDirectionalField
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i : ι) (theta : ℝ) : ℝ :=
  k * (platformResidualBlockMaterialVelocity C a i theta /
      platformAngularDistance a theta) +
    ∑ j ∈ Finset.univ.erase i,
      platformResidualOffBlockDirectionalTerm C k a hk ha ha2
        hthreshold i j theta -
    C.weight i

/-- The right side of the pointwise block lower bound `(4.28)`. -/
def platformResidualBlockLogTangentLower
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (i : ι) (theta : ℝ) : ℝ :=
  residualBackgroundAt C k i - platformPotentialConstant k a -
    C.weight i +
      platformResidualBlockLogPotential C k a hk ha ha2 hthreshold i theta

/-- The off-block directional term is Borel measurable as a parameterized
integral of a Borel function. -/
theorem measurable_platformResidualOffBlockDirectionalTerm
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i j : ι) :
    Measurable (platformResidualOffBlockDirectionalTerm C k a
      hk ha ha2 hthreshold i j) := by
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold j
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold j
  have hleftRight : left ≤ right :=
    (platformResidualBlockLeft_lt_right C k a hk ha ha2
      hthreshold j).le
  have hjoint : Measurable (fun p : ℝ × ℝ ↦
      platformAngularDensity k a p.2 *
        ((platformResidualBlockMaterialVelocity C a i p.1 -
            platformResidualBlockMaterialVelocity C a j p.2) /
          (platformAngularDistance a p.1 -
            platformAngularDistance a p.2))) := by
    unfold platformResidualBlockMaterialVelocity platformAngularDensity
      platformDensityCoefficient platformAngularDistance
    fun_prop
  have hinner : StronglyMeasurable (fun theta : ℝ ↦
      ∫ phi : ℝ,
        platformAngularDensity k a phi *
          ((platformResidualBlockMaterialVelocity C a i theta -
              platformResidualBlockMaterialVelocity C a j phi) /
            (platformAngularDistance a theta -
              platformAngularDistance a phi))
        ∂(volume.restrict (Ioc left right))) :=
    hjoint.stronglyMeasurable.integral_prod_right
  unfold platformResidualOffBlockDirectionalTerm
  change Measurable (fun theta : ℝ ↦ (1 / Real.pi) *
    ∫ phi : ℝ in left..right,
      platformAngularDensity k a phi *
        ((platformResidualBlockMaterialVelocity C a i theta -
            platformResidualBlockMaterialVelocity C a j phi) /
          (platformAngularDistance a theta -
            platformAngularDistance a phi)))
  have hscaledEq : (fun theta : ℝ ↦ (1 / Real.pi) *
      ∫ phi : ℝ in left..right,
        platformAngularDensity k a phi *
          ((platformResidualBlockMaterialVelocity C a i theta -
              platformResidualBlockMaterialVelocity C a j phi) /
            (platformAngularDistance a theta -
              platformAngularDistance a phi))) =
    fun theta : ℝ ↦ (1 / Real.pi) *
      ∫ phi : ℝ in Ioc left right,
        platformAngularDensity k a phi *
          ((platformResidualBlockMaterialVelocity C a i theta -
              platformResidualBlockMaterialVelocity C a j phi) /
            (platformAngularDistance a theta -
              platformAngularDistance a phi)) := by
    funext theta
    rw [intervalIntegral.integral_of_le hleftRight]
  have hmeas : Measurable (fun theta : ℝ ↦ (1 / Real.pi) *
      ∫ phi : ℝ in Ioc left right,
        platformAngularDensity k a phi *
          ((platformResidualBlockMaterialVelocity C a i theta -
              platformResidualBlockMaterialVelocity C a j phi) /
            (platformAngularDistance a theta -
              platformAngularDistance a phi))) :=
    measurable_const.mul hinner.measurable
  exact hscaledEq.symm ▸ hmeas

/-- The reduced directional field is Borel measurable on the whole real
line; its exceptional block-endpoint values are immaterial to integration. -/
theorem measurable_platformResidualReducedDirectionalField
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) :
    Measurable (platformResidualReducedDirectionalField C k a
      hk ha ha2 hthreshold i) := by
  classical
  unfold platformResidualReducedDirectionalField
  have hdistance : Measurable (platformAngularDistance a) := by
    unfold platformAngularDistance
    fun_prop
  have hvelocity : Measurable
      (platformResidualBlockMaterialVelocity C a i) := by
    unfold platformResidualBlockMaterialVelocity
    exact measurable_const.sub hdistance
  apply Measurable.sub
  · apply Measurable.add
    · exact measurable_const.mul (hvelocity.div hdistance)
    · apply Finset.measurable_sum
      intro j _hj
      exact measurable_platformResidualOffBlockDirectionalTerm C k a
        hk ha ha2 hthreshold i j
  · exact measurable_const

/-- The blockwise reduced directional field, assembled with the same
half-open convention as the material field. -/
def platformResidualPiecewiseReducedDirectionalField
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (theta : ℝ) : ℝ :=
  ∑ i,
    (Ioc
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)).indicator
      (platformResidualReducedDirectionalField C k a
        hk ha ha2 hthreshold i) theta

/-- On a canonical half-open block, the piecewise field reduces to that
block's reduced directional field. -/
theorem platformResidualPiecewiseReducedDirectionalField_eq_on_block
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) {theta : ℝ}
    (htheta : theta ∈ Ioc
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    platformResidualPiecewiseReducedDirectionalField C k a
        hk ha ha2 hthreshold theta =
      platformResidualReducedDirectionalField C k a
        hk ha ha2 hthreshold i theta := by
  classical
  unfold platformResidualPiecewiseReducedDirectionalField
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem htheta _
  · intro j _hj hji
    rcases lt_or_gt_of_ne hji with hji | hij
    · have hordered := platformResidualBlocks_ordered C k a hk ha ha2
        hthreshold hji
      have hrightLt :
          platformResidualBlockRight C k a hk ha ha2 hthreshold j < theta :=
        hordered.trans_lt htheta.1
      rw [indicator_of_notMem]
      exact fun hmem ↦ (not_le_of_gt hrightLt) hmem.2
    · have hordered := platformResidualBlocks_ordered C k a hk ha ha2
        hthreshold hij
      have hthetaLe : theta ≤
          platformResidualBlockLeft C k a hk ha ha2 hthreshold j :=
        htheta.2.trans hordered
      rw [indicator_of_notMem]
      exact fun hmem ↦ (not_lt_of_ge hthetaLe) hmem.1
  · simp

/-- The assembled reduced directional field is Borel measurable. -/
theorem measurable_platformResidualPiecewiseReducedDirectionalField
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Measurable (platformResidualPiecewiseReducedDirectionalField C k a
      hk ha ha2 hthreshold) := by
  classical
  unfold platformResidualPiecewiseReducedDirectionalField
  apply Finset.measurable_sum
  intro i _hi
  exact (measurable_platformResidualReducedDirectionalField C k a
    hk ha ha2 hthreshold i).indicator measurableSet_Ioc

/-- Adjoint pairing of the logarithmic lower tangent on one block. -/
def platformResidualBlockLogTangentPairing
    (C : ResidualConfiguration ι)
    (k a xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) : ℝ :=
  (1 / Real.pi) *
    ∫ theta : ℝ in
      platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
      platformResidualBlockRight C k a hk ha ha2 hthreshold i,
      platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta *
        platformResidualBlockLogTangentLower C k a
          hk ha ha2 hthreshold i theta

/-- Adjoint pairing of the reduced directional field on one block. -/
def platformResidualReducedDirectionalBlockPairing
    (C : ResidualConfiguration ι)
    (k a xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) : ℝ :=
  (1 / Real.pi) *
    ∫ theta : ℝ in
      platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
      platformResidualBlockRight C k a hk ha ha2 hthreshold i,
      platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta *
        platformResidualReducedDirectionalField C k a
          hk ha ha2 hthreshold i theta

/-- The real pairing functional left for the Fourier/Abel branch to
identify. -/
def platformResidualReducedDirectionalPairing
    (C : ResidualConfiguration ι)
    (k a xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) : ℝ :=
  (1 / Real.pi) *
    ∫ theta : ℝ in 0..Real.pi,
      platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta *
        platformResidualPiecewiseReducedDirectionalField C k a
          hk ha ha2 hthreshold theta

/-- Exact integrability interface for the block-side pairing argument.  The
first field is the logarithmic lower tangent; the second is the assembled
unreduced first variation. -/
def PlatformResidualPairingIntegrable
    (C : ResidualConfiguration ι)
    (k a xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) : Prop :=
  (∀ i, IntervalIntegrable
    (fun theta : ℝ ↦
      platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta *
        platformResidualBlockLogTangentLower C k a
          hk ha ha2 hthreshold i theta)
    volume
    (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
    (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) ∧
  IntervalIntegrable
    (fun theta : ℝ ↦
      platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta *
        platformResidualPiecewiseReducedDirectionalField C k a
          hk ha ha2 hthreshold theta)
    volume 0 Real.pi

/-- One canonical tangent block with the deficit energy written as its
physical mixed angular integral. -/
def platformResidualAngularTangentBlockTerm
    (C : ResidualConfiguration ι)
    (k a xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) : ℝ :=
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold i
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold i
  platformAdjointIntervalMass
      a xMinus xPlus sigmaMinus sigmaPlus left right *
      (residualBackgroundAt C k i -
        platformPotentialConstant k a - C.weight i) +
    (1 / Real.pi ^ 2) *
      ∫ theta : ℝ in left..right,
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          ∫ phi : ℝ in left..right,
            platformAngularDensity k a phi *
              Real.log |platformAngularDistance a theta -
                platformAngularDistance a phi|

/-- The abstract deficit-energy block is exactly its concrete angular form. -/
theorem platformResidualTangentBlockTerm_eq_angular
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (i : ι) :
    platformResidualTangentBlockTerm C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i =
      platformResidualAngularTangentBlockTerm C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i := by
  rw [platformResidualTangentBlockTerm_eq_background]
  dsimp only [platformResidualAngularTangentBlockTerm]
  rw [platformDeficitBlockEnergy_eq_angularIntegral hk ha ha2 hthreshold
    hxMinus hxPlus hsigmaMinus hsigmaPlus
    (platformResidualBlockLeft_mem_Icc C k a hk ha ha2 hthreshold i).1
    (platformResidualBlockLeft_lt_right C k a hk ha ha2 hthreshold i)
    (platformResidualBlockRight_mem_Icc C k a hk ha ha2 hthreshold i).2]

/-- The concrete angular block is the adjoint integral of the pointwise
logarithmic lower tangent. -/
theorem platformResidualAngularTangentBlockTerm_eq_logTangentPairing
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (i : ι)
    (hintegrable : IntervalIntegrable
      (fun theta : ℝ ↦
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformResidualBlockLogTangentLower C k a
            hk ha ha2 hthreshold i theta)
      volume
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    platformResidualAngularTangentBlockTerm C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i =
      platformResidualBlockLogTangentPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i := by
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold i
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold i
  let B : ℝ → ℝ := platformAngularAdjointDensity
    a xMinus xPlus sigmaMinus sigmaPlus
  let constant := residualBackgroundAt C k i -
    platformPotentialConstant k a - C.weight i
  let logPart : ℝ → ℝ :=
    platformResidualBlockLogPotential C k a hk ha ha2 hthreshold i
  have hleftMem :=
    platformResidualBlockLeft_mem_Icc C k a hk ha ha2 hthreshold i
  have hrightMem :=
    platformResidualBlockRight_mem_Icc C k a hk ha ha2 hthreshold i
  have hleftRight : left ≤ right :=
    (platformResidualBlockLeft_lt_right C k a hk ha ha2
      hthreshold i).le
  have hBfull : IntervalIntegrable B volume 0 Real.pi :=
    intervalIntegrable_platformAngularAdjointDensity
      hxMinus hxPlus ha2
  have hBblock : IntervalIntegrable B volume left right := by
    apply hBfull.mono_set
    rw [uIcc_of_le hleftRight, uIcc_of_le Real.pi_pos.le]
    exact Icc_subset_Icc hleftMem.1 hrightMem.2
  have hconstant : IntervalIntegrable
      (fun theta : ℝ ↦ B theta * constant) volume left right :=
    hBblock.mul_const constant
  have hlogPart : IntervalIntegrable
      (fun theta : ℝ ↦ B theta * logPart theta) volume left right := by
    have hdiff := hintegrable.sub hconstant
    apply hdiff.congr
    intro theta _htheta
    dsimp only [B, logPart, constant]
    unfold platformResidualBlockLogTangentLower
    ring
  have hsplit :
      (∫ theta : ℝ in left..right,
          B theta *
            platformResidualBlockLogTangentLower C k a
              hk ha ha2 hthreshold i theta) =
        (∫ theta : ℝ in left..right, B theta * constant) +
          ∫ theta : ℝ in left..right, B theta * logPart theta := by
    rw [← intervalIntegral.integral_add hconstant hlogPart]
    apply intervalIntegral.integral_congr
    intro theta _htheta
    dsimp only [B, logPart, constant]
    unfold platformResidualBlockLogTangentLower
    ring
  have hconstantIntegral :
      (∫ theta : ℝ in left..right, B theta * constant) =
        (∫ theta : ℝ in left..right, B theta) * constant := by
    rw [intervalIntegral.integral_mul_const]
  have hlogScale :
      (∫ theta : ℝ in left..right, B theta * logPart theta) =
        (1 / Real.pi) *
          ∫ theta : ℝ in left..right,
            B theta *
              ∫ phi : ℝ in left..right,
                platformAngularDensity k a phi *
                  Real.log |platformAngularDistance a theta -
                    platformAngularDistance a phi| := by
    dsimp only [logPart, platformResidualBlockLogPotential]
    rw [show (fun theta : ℝ ↦
        B theta *
          ((1 / Real.pi) *
            ∫ phi : ℝ in left..right,
              platformAngularDensity k a phi *
                Real.log |platformAngularDistance a theta -
                  platformAngularDistance a phi|)) =
      fun theta : ℝ ↦ (1 / Real.pi) *
        (B theta *
          ∫ phi : ℝ in left..right,
            platformAngularDensity k a phi *
              Real.log |platformAngularDistance a theta -
                platformAngularDistance a phi|) by
          funext theta
          ring,
      intervalIntegral.integral_const_mul]
  dsimp only [platformResidualAngularTangentBlockTerm,
    platformResidualBlockLogTangentPairing]
  rw [hsplit, hconstantIntegral, hlogScale]
  unfold platformAdjointIntervalMass
  dsimp only [B, constant]
  ring

/-- Exact concrete-angular characterization of the global supporting bound. -/
theorem platformResidualSupportingBound_iff_angular
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus M0 targetWidth : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus) :
    PlatformResidualSupportingBound C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
        M0 targetWidth ↔
      M0 + ∑ i, platformResidualAngularTangentBlockTerm C k a
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
        targetWidth := by
  unfold PlatformResidualSupportingBound
  simp_rw [platformResidualTangentBlockTerm_eq_angular C hk ha ha2
    hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus]

/-- A concrete angular block estimate directly instantiates
`PlatformResidualSupportingBound`. -/
theorem platformResidualSupportingBound_of_angular
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus M0 targetWidth : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hangular :
      M0 + ∑ i, platformResidualAngularTangentBlockTerm C k a
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
        targetWidth) :
    PlatformResidualSupportingBound C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      M0 targetWidth :=
  (platformResidualSupportingBound_iff_angular C hk ha ha2 hthreshold
    hxMinus hxPlus hsigmaMinus hsigmaPlus).2 hangular

omit [LinearOrder ι] in
/-- The external-field part of the block tangent inequality. -/
theorem platformResidual_external_log_tangent
    (C : ResidualConfiguration ι) {k a : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2) (i : ι)
    {theta : ℝ} (htheta : theta ∈ Icc 0 Real.pi) :
    k * (Real.log (C.location i) -
        Real.log (platformAngularDistance a theta)) ≤
      k * ((C.location i - platformAngularDistance a theta) /
        platformAngularDistance a theta) := by
  have hlocation : 0 < C.location i :=
    zero_lt_one.trans_le (C.location_mem i).1
  have hdistance : 0 < platformAngularDistance a theta :=
    ha.trans_le (platformAngularDistance_mem_Icc ha2.le htheta).1
  have hratio : 0 < C.location i / platformAngularDistance a theta :=
    div_pos hlocation hdistance
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hlocation.ne' hdistance.ne'] at hlog
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hscaled := mul_le_mul_of_nonneg_left hlog hk0
  convert! hscaled using 1
  field_simp [hdistance.ne']

/-- Signed form of `(4.27)`: if the target and reference differences have
the same nonzero sign, their logarithmic difference is below the quotient
first variation. -/
theorem log_abs_sub_le_difference_quotient
    {targetDifference referenceDifference : ℝ}
    (hsame : 0 < targetDifference * referenceDifference) :
    Real.log |targetDifference| - Real.log |referenceDifference| ≤
      (targetDifference - referenceDifference) / referenceDifference := by
  have htarget : targetDifference ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hsame
    exact (lt_irrefl 0) hsame
  have hreference : referenceDifference ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hsame
    exact (lt_irrefl 0) hsame
  have hratio : 0 < targetDifference / referenceDifference :=
    (div_pos_iff.mpr (mul_pos_iff.mp hsame))
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div htarget hreference] at hlog
  rw [Real.log_abs, Real.log_abs]
  convert! hlog using 1
  field_simp [hreference]

/-- Concrete off-block instance of the logarithmic tangent inequality.
The target locations must increase with the index order used to construct
the consecutive reference blocks. -/
theorem platformResidual_offBlock_log_tangent
    (C : ResidualConfiguration ι) {k a : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hlocation : StrictMono C.location)
    {i j : ι} (hij : i ≠ j) {theta phi : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
    (hphi : phi ∈ Icc
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold j)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold j)) :
    Real.log |C.location i - C.location j| -
        Real.log |platformAngularDistance a theta -
          platformAngularDistance a phi| ≤
      ((C.location i - C.location j) -
          (platformAngularDistance a theta -
            platformAngularDistance a phi)) /
        (platformAngularDistance a theta -
          platformAngularDistance a phi) := by
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
  apply log_abs_sub_le_difference_quotient
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hblocks := platformResidualBlocks_ordered C k a hk ha ha2
      hthreshold hij
    have hthetaPhi : theta < phi :=
      htheta.2.trans_le (hblocks.trans hphi.1)
    have hdistance := platformAngularDistance_strictMonoOn ha2
      hthetaIcc hphiIcc hthetaPhi
    exact mul_pos_of_neg_of_neg (sub_neg.mpr (hlocation hij))
      (sub_neg.mpr hdistance)
  · have hblocks := platformResidualBlocks_ordered C k a hk ha ha2
      hthreshold hji
    have hphiTheta : phi < theta :=
      (hphi.2.trans hblocks).trans_lt htheta.1
    have hdistance := platformAngularDistance_strictMonoOn ha2
      hphiIcc hthetaIcc hphiTheta
    exact mul_pos (sub_pos.mpr (hlocation hji))
      (sub_pos.mpr hdistance)

/-- Integrated off-block form of `(4.27)`.  The exact reference mass of
block `j` turns the constant target logarithm into `q_j log|d_i-d_j|`. -/
theorem platformResidual_offBlock_logPotential_tangent
    (C : ResidualConfiguration ι) {k a : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hlocation : StrictMono C.location)
    {i j : ι} (hij : i ≠ j) {theta : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    C.weight j * Real.log |C.location i - C.location j| -
        platformResidualBlockLogPotential C k a hk ha ha2
          hthreshold j theta ≤
      platformResidualOffBlockDirectionalTerm C k a hk ha ha2
        hthreshold i j theta := by
  classical
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold j
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold j
  let targetLog := Real.log |C.location i - C.location j|
  let referenceLog : ℝ → ℝ := fun phi ↦
    Real.log |platformAngularDistance a theta -
      platformAngularDistance a phi|
  let density : ℝ → ℝ := platformAngularDensity k a
  let quotient : ℝ → ℝ := fun phi ↦
    (platformResidualBlockMaterialVelocity C a i theta -
        platformResidualBlockMaterialVelocity C a j phi) /
      (platformAngularDistance a theta -
        platformAngularDistance a phi)
  have hleftMem :=
    platformResidualBlockLeft_mem_Icc C k a hk ha ha2 hthreshold j
  have hrightMem :=
    platformResidualBlockRight_mem_Icc C k a hk ha ha2 hthreshold j
  have hleftRight : left ≤ right :=
    (platformResidualBlockLeft_lt_right C k a hk ha ha2
      hthreshold j).le
  have hthetaIcc : theta ∈ Icc 0 Real.pi :=
    ⟨(platformResidualBlockLeft_mem_Icc C k a hk ha ha2
        hthreshold i).1.trans htheta.1.le,
      htheta.2.le.trans
        (platformResidualBlockRight_mem_Icc C k a hk ha ha2
          hthreshold i).2⟩
  have hlogFull :=
    intervalIntegrable_platformAngularDensity_mul_logDistance
      k ha ha2 (theta := theta)
  have hlogBlock : IntervalIntegrable
      (fun phi : ℝ ↦ density phi * referenceLog phi)
      volume left right := by
    apply hlogFull.mono_set
    rw [uIcc_of_le hleftRight, uIcc_of_le Real.pi_pos.le]
    exact Icc_subset_Icc hleftMem.1 hrightMem.2
  have hdensityContinuous : Continuous density :=
    continuous_platformAngularDensity_for_blockTangent k ha ha2.le
  have hconstantBlock : IntervalIntegrable
      (fun phi : ℝ ↦ density phi * targetLog)
      volume left right :=
    (hdensityContinuous.mul continuous_const).intervalIntegrable left right
  have hlowerIntegrable : IntervalIntegrable
      (fun phi : ℝ ↦ density phi *
        (targetLog - referenceLog phi)) volume left right := by
    simpa only [mul_sub] using! hconstantBlock.sub hlogBlock
  have hdenominator (phi : ℝ) (hphi : phi ∈ Icc left right) :
      platformAngularDistance a theta -
          platformAngularDistance a phi ≠ 0 := by
    have hphiIcc : phi ∈ Icc 0 Real.pi :=
      ⟨hleftMem.1.trans hphi.1, hphi.2.trans hrightMem.2⟩
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hblocks := platformResidualBlocks_ordered C k a hk ha ha2
        hthreshold hij
      have hthetaPhi : theta < phi :=
        htheta.2.trans_le (hblocks.trans hphi.1)
      exact (sub_neg.mpr (platformAngularDistance_strictMonoOn ha2
        hthetaIcc hphiIcc hthetaPhi)).ne
    · have hblocks := platformResidualBlocks_ordered C k a hk ha ha2
        hthreshold hji
      have hphiTheta : phi < theta :=
        (hphi.2.trans hblocks).trans_lt htheta.1
      exact (sub_pos.mpr (platformAngularDistance_strictMonoOn ha2
        hphiIcc hthetaIcc hphiTheta)).ne'
  have hdistanceContinuous : Continuous (platformAngularDistance a) := by
    unfold platformAngularDistance
    fun_prop
  have hquotientContinuous : ContinuousOn quotient (Icc left right) := by
    apply ContinuousOn.div
    · unfold platformResidualBlockMaterialVelocity
      exact (continuous_const.sub
        (continuous_const.sub hdistanceContinuous)).continuousOn
    · exact (continuous_const.sub hdistanceContinuous).continuousOn
    · exact hdenominator
  have hupperIntegrable : IntervalIntegrable
      (fun phi : ℝ ↦ density phi * quotient phi)
      volume left right := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hleftRight]
    exact hdensityContinuous.continuousOn.mul hquotientContinuous
  have hintegral :
      (∫ phi : ℝ in left..right,
          density phi * (targetLog - referenceLog phi)) ≤
        ∫ phi : ℝ in left..right, density phi * quotient phi := by
    apply intervalIntegral.integral_mono_on hleftRight
      hlowerIntegrable hupperIntegrable
    intro phi hphi
    have hphiIcc : phi ∈ Icc 0 Real.pi :=
      ⟨hleftMem.1.trans hphi.1, hphi.2.trans hrightMem.2⟩
    have hdensityNonneg : 0 ≤ density phi :=
      platformAngularDensity_nonneg (zero_le_one.trans hk) ha ha2.le
        hthreshold hphiIcc
    apply mul_le_mul_of_nonneg_left _ hdensityNonneg
    have htangent := platformResidual_offBlock_log_tangent C hk ha ha2
      hthreshold hlocation hij htheta hphi
    dsimp only [targetLog, referenceLog, quotient,
      platformResidualBlockMaterialVelocity]
    convert! htangent using 1
    ring_nf
  have hscaled := mul_le_mul_of_nonneg_left hintegral
    (one_div_nonneg.mpr Real.pi_pos.le)
  have hintegralSplit :
      (∫ phi : ℝ in left..right,
          density phi * (targetLog - referenceLog phi)) =
        (∫ phi : ℝ in left..right, density phi) * targetLog -
          ∫ phi : ℝ in left..right,
            density phi * referenceLog phi := by
    calc
      (∫ phi : ℝ in left..right,
          density phi * (targetLog - referenceLog phi)) =
        ∫ phi : ℝ in left..right,
          ((fun x : ℝ ↦ density x * targetLog) -
            fun x : ℝ ↦ density x * referenceLog x) phi := by
          apply intervalIntegral.integral_congr
          intro phi _hphi
          simp only [Pi.sub_apply]
          ring
      _ = (∫ phi : ℝ in left..right, density phi * targetLog) -
          ∫ phi : ℝ in left..right,
            density phi * referenceLog phi :=
        intervalIntegral.integral_sub hconstantBlock hlogBlock
      _ = (∫ phi : ℝ in left..right, density phi) * targetLog -
          ∫ phi : ℝ in left..right,
            density phi * referenceLog phi := by
        rw [intervalIntegral.integral_mul_const]
  rw [hintegralSplit] at hscaled
  have hmass := platformReferenceIntervalMass_residualBlock
    C k a hk ha ha2 hthreshold j
  change C.weight j * targetLog -
      (1 / Real.pi) *
        (∫ phi : ℝ in left..right, density phi * referenceLog phi) ≤
    (1 / Real.pi) *
      ∫ phi : ℝ in left..right, density phi * quotient phi
  change (1 / Real.pi) * (∫ phi : ℝ in left..right, density phi) =
    C.weight j at hmass
  calc
    C.weight j * targetLog -
        (1 / Real.pi) *
          (∫ phi : ℝ in left..right, density phi * referenceLog phi) =
      (1 / Real.pi) *
        ((∫ phi : ℝ in left..right, density phi) * targetLog -
          ∫ phi : ℝ in left..right,
            density phi * referenceLog phi) := by
      rw [← hmass]
      ring
    _ ≤ (1 / Real.pi) *
        ∫ phi : ℝ in left..right, density phi * quotient phi := hscaled

/-- Concrete pointwise block tangent `(4.28)`.  It holds away from the
finitely many block endpoints, exactly where the unreduced first variation
is an ordinary off-block integral. -/
theorem platformResidualBlockLogTangentLower_le_reducedDirectionalField
    (C : ResidualConfiguration ι) {k a : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hlocation : StrictMono C.location)
    (i : ι) {theta : ℝ}
    (htheta : theta ∈ Ioo
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    platformResidualBlockLogTangentLower C k a hk ha ha2
        hthreshold i theta ≤
      platformResidualReducedDirectionalField C k a hk ha ha2
        hthreshold i theta := by
  classical
  have hthetaIcc : theta ∈ Icc 0 Real.pi :=
    ⟨(platformResidualBlockLeft_mem_Icc C k a hk ha ha2
        hthreshold i).1.trans htheta.1.le,
      htheta.2.le.trans
        (platformResidualBlockRight_mem_Icc C k a hk ha ha2
          hthreshold i).2⟩
  have hexternal := platformResidual_external_log_tangent C hk ha ha2 i
    hthetaIcc
  have hoffSum :
      (∑ j ∈ Finset.univ.erase i,
          (C.weight j * Real.log |C.location i - C.location j| -
            platformResidualBlockLogPotential C k a hk ha ha2
              hthreshold j theta)) ≤
        ∑ j ∈ Finset.univ.erase i,
          platformResidualOffBlockDirectionalTerm C k a hk ha ha2
            hthreshold i j theta := by
    apply Finset.sum_le_sum
    intro j hj
    exact platformResidual_offBlock_logPotential_tangent C hk ha ha2
      hthreshold hlocation (Finset.ne_of_mem_erase hj).symm htheta
  have hlogIntegrable :=
    intervalIntegrable_platformAngularDensity_mul_logDistance
      k ha ha2 (theta := theta)
  have hpartition := sum_intervalIntegral_platformResidualBlocks
    C k a hk ha ha2 hthreshold hlogIntegrable
  have hpotential := integral_platformAngularDensity_log_potential
    (k := k) (a := a) (theta := theta) ha ha2 hthetaIcc
  have hcommute :
      (∫ phi : ℝ in 0..Real.pi,
          platformAngularDensity k a phi *
            Real.log |platformAngularDistance a theta -
              platformAngularDistance a phi|) =
        ∫ phi : ℝ in 0..Real.pi,
          Real.log |platformAngularDistance a theta -
              platformAngularDistance a phi| *
            platformAngularDensity k a phi := by
    apply intervalIntegral.integral_congr
    intro phi _hphi
    ring
  have hpotentialBlocks :
      k * Real.log (platformAngularDistance a theta) +
          ∑ j, platformResidualBlockLogPotential C k a hk ha ha2
            hthreshold j theta =
        platformPotentialConstant k a := by
    unfold platformResidualBlockLogPotential
    rw [← Finset.mul_sum, hpartition, hcommute]
    simpa only [platformPotentialConstant] using! hpotential
  have hblockSplit :
      (∑ j, platformResidualBlockLogPotential C k a hk ha ha2
          hthreshold j theta) =
        (∑ j ∈ Finset.univ.erase i,
          platformResidualBlockLogPotential C k a hk ha ha2
            hthreshold j theta) +
          platformResidualBlockLogPotential C k a hk ha ha2
            hthreshold i theta := by
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  have hlowerEq :
      platformResidualBlockLogTangentLower C k a hk ha ha2
          hthreshold i theta =
        k * (Real.log (C.location i) -
            Real.log (platformAngularDistance a theta)) +
          (∑ j ∈ Finset.univ.erase i,
            (C.weight j * Real.log |C.location i - C.location j| -
              platformResidualBlockLogPotential C k a hk ha ha2
                hthreshold j theta)) -
          C.weight i := by
    unfold platformResidualBlockLogTangentLower residualBackgroundAt
    rw [← hpotentialBlocks, hblockSplit, Finset.sum_sub_distrib]
    ring_nf
    simp
    abel
  rw [hlowerEq]
  unfold platformResidualReducedDirectionalField
  have htotal := add_le_add hexternal hoffSum
  simpa only [platformResidualBlockMaterialVelocity] using!
    sub_le_sub_right htotal (C.weight i)

/-- The blockwise reduced-field pairings recombine into the clean global
pairing functional. -/
theorem sum_platformResidualReducedDirectionalBlockPairing_eq_pairing
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hintegrable : IntervalIntegrable
      (fun theta : ℝ ↦
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformResidualPiecewiseReducedDirectionalField C k a
            hk ha ha2 hthreshold theta)
      volume 0 Real.pi) :
    (∑ i, platformResidualReducedDirectionalBlockPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i) =
      platformResidualReducedDirectionalPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold := by
  let G : ℝ → ℝ := fun theta ↦
    platformAngularAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus theta *
      platformResidualPiecewiseReducedDirectionalField C k a
        hk ha ha2 hthreshold theta
  have hblock (i : ι) :
      (∫ theta : ℝ in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
          platformResidualBlockRight C k a hk ha ha2 hthreshold i,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformResidualReducedDirectionalField C k a
              hk ha ha2 hthreshold i theta) =
        ∫ theta : ℝ in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
          platformResidualBlockRight C k a hk ha ha2 hthreshold i,
          G theta := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with theta
    intro htheta
    rw [uIoc_of_le (platformResidualBlockLeft_lt_right C k a hk ha ha2
      hthreshold i).le] at htheta
    dsimp only [G]
    rw [platformResidualPiecewiseReducedDirectionalField_eq_on_block
      C k a hk ha ha2 hthreshold i htheta]
  have hpartition := sum_intervalIntegral_platformResidualBlocks
    C k a hk ha ha2 hthreshold hintegrable
  unfold platformResidualReducedDirectionalBlockPairing
    platformResidualReducedDirectionalPairing
  rw [← Finset.mul_sum]
  congr 1
  calc
    (∑ i, ∫ theta : ℝ in
        platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
        platformResidualBlockRight C k a hk ha ha2 hthreshold i,
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformResidualReducedDirectionalField C k a
            hk ha ha2 hthreshold i theta) =
      ∑ i, ∫ theta : ℝ in
        platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
        platformResidualBlockRight C k a hk ha ha2 hthreshold i,
        G theta := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hblock i
    _ = ∫ theta : ℝ in 0..Real.pi, G theta := hpartition

/-- Weighted integrated form of `(4.28)` on one block. -/
theorem platformResidualBlockLogTangentPairing_le_reducedDirectionalBlockPairing
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hlocation : StrictMono C.location) (i : ι)
    (hlowerIntegrable : IntervalIntegrable
      (fun theta : ℝ ↦
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformResidualBlockLogTangentLower C k a
            hk ha ha2 hthreshold i theta)
      volume
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i))
    (hupperIntegrable : IntervalIntegrable
      (fun theta : ℝ ↦
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformResidualReducedDirectionalField C k a
            hk ha ha2 hthreshold i theta)
      volume
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    platformResidualBlockLogTangentPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
      platformResidualReducedDirectionalBlockPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i := by
  have hintegral :
      (∫ theta : ℝ in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
          platformResidualBlockRight C k a hk ha ha2 hthreshold i,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformResidualBlockLogTangentLower C k a
              hk ha ha2 hthreshold i theta) ≤
        ∫ theta : ℝ in
          platformResidualBlockLeft C k a hk ha ha2 hthreshold i..
          platformResidualBlockRight C k a hk ha ha2 hthreshold i,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformResidualReducedDirectionalField C k a
              hk ha ha2 hthreshold i theta := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (platformResidualBlockLeft_lt_right C k a hk ha ha2
        hthreshold i).le hlowerIntegrable hupperIntegrable
    intro theta htheta
    have hthetaIcc : theta ∈ Icc 0 Real.pi :=
      ⟨(platformResidualBlockLeft_mem_Icc C k a hk ha ha2
          hthreshold i).1.trans htheta.1.le,
        htheta.2.le.trans
          (platformResidualBlockRight_mem_Icc C k a hk ha ha2
            hthreshold i).2⟩
    apply mul_le_mul_of_nonneg_left
      (platformResidualBlockLogTangentLower_le_reducedDirectionalField
        C hk ha ha2 hthreshold hlocation i htheta)
    exact platformAngularAdjointDensity_nonneg hxMinus hxPlus
      hsigmaMinus hsigmaPlus ha2 hthetaIcc
  unfold platformResidualBlockLogTangentPairing
    platformResidualReducedDirectionalBlockPairing
  exact mul_le_mul_of_nonneg_left hintegral
    (one_div_nonneg.mpr Real.pi_pos.le)

/-- Summed integrated block tangent, with the abstract deficit blocks already
replaced by their exact angular form. -/
theorem sum_platformResidualAngularTangentBlockTerm_le_reducedFieldPairing
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hlocation : StrictMono C.location)
    (hintegrable : PlatformResidualPairingIntegrable C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold) :
    (∑ i, platformResidualAngularTangentBlockTerm C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i) ≤
      platformResidualReducedDirectionalPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold := by
  have hupper (i : ι) : IntervalIntegrable
      (fun theta : ℝ ↦
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformResidualReducedDirectionalField C k a
            hk ha ha2 hthreshold i theta)
      volume
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i) := by
    have hrestricted := hintegrable.2.mono_set (by
      rw [uIcc_of_le (platformResidualBlockLeft_lt_right C k a hk ha ha2
          hthreshold i).le, uIcc_of_le Real.pi_pos.le]
      exact Icc_subset_Icc
        (platformResidualBlockLeft_mem_Icc C k a hk ha ha2
          hthreshold i).1
        (platformResidualBlockRight_mem_Icc C k a hk ha ha2
          hthreshold i).2)
    apply hrestricted.congr
    intro theta htheta
    rw [uIoc_of_le (platformResidualBlockLeft_lt_right C k a hk ha ha2
      hthreshold i).le] at htheta
    change platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta *
        platformResidualPiecewiseReducedDirectionalField C k a
          hk ha ha2 hthreshold theta =
      platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta *
        platformResidualReducedDirectionalField C k a
          hk ha ha2 hthreshold i theta
    rw [platformResidualPiecewiseReducedDirectionalField_eq_on_block
      C k a hk ha ha2 hthreshold i htheta]
  have hblockSum :
      (∑ i, platformResidualBlockLogTangentPairing C k a
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i) ≤
        ∑ i, platformResidualReducedDirectionalBlockPairing C k a
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i := by
    apply Finset.sum_le_sum
    intro i _hi
    exact platformResidualBlockLogTangentPairing_le_reducedDirectionalBlockPairing
      C hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        hlocation i (hintegrable.1 i) (hupper i)
  have hleft :
      (∑ i, platformResidualAngularTangentBlockTerm C k a
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i) =
        ∑ i, platformResidualBlockLogTangentPairing C k a
          xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact platformResidualAngularTangentBlockTerm_eq_logTangentPairing
      C hk ha ha2 hthreshold hxMinus hxPlus i (hintegrable.1 i)
  rw [hleft]
  calc
    (∑ i, platformResidualBlockLogTangentPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i) ≤
      ∑ i, platformResidualReducedDirectionalBlockPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i := hblockSum
    _ = platformResidualReducedDirectionalPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold :=
      sum_platformResidualReducedDirectionalBlockPairing_eq_pairing
        C hk ha ha2 hthreshold hintegrable.2

/-- Final block-side inequality in the exact form consumed by the canonical
Abel interface. -/
theorem sum_platformResidualTangentBlockTerm_le_reducedFieldPairing
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hlocation : StrictMono C.location)
    (hintegrable : PlatformResidualPairingIntegrable C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold) :
    (∑ i, platformResidualTangentBlockTerm C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i) ≤
      platformResidualReducedDirectionalPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold := by
  simp_rw [platformResidualTangentBlockTerm_eq_angular C hk ha ha2
    hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus]
  exact sum_platformResidualAngularTangentBlockTerm_le_reducedFieldPairing
    C hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      hlocation hintegrable

/-- A bound for the clean reduced-field pairing directly instantiates the
global supporting inequality. -/
theorem platformResidualSupportingBound_of_reducedFieldPairing
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus M0 targetWidth : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hlocation : StrictMono C.location)
    (hintegrable : PlatformResidualPairingIntegrable C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold)
    (hpairing : M0 + platformResidualReducedDirectionalPairing C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold ≤
      targetWidth) :
    PlatformResidualSupportingBound C k a
      xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold
      M0 targetWidth := by
  unfold PlatformResidualSupportingBound
  have hsum := sum_platformResidualTangentBlockTerm_le_reducedFieldPairing
    C hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
      hlocation hintegrable
  calc
    M0 + ∑ i, platformResidualTangentBlockTerm C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold i ≤
      M0 + platformResidualReducedDirectionalPairing C k a
        xMinus xPlus sigmaMinus sigmaPlus hk ha ha2 hthreshold := by
      exact add_le_add_right hsum M0
    _ ≤ targetWidth := hpairing

end

end Erdos1038
