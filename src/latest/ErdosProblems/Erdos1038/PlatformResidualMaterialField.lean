import ErdosProblems.Erdos1038.PlatformReferencePartition
import ErdosProblems.Erdos1038.PlatformAngularMonotonicity
import ErdosProblems.Erdos1038.ResidualDeficit

/-!
# The material field of an atomized residual target

For the constant-platform reference, the target quantile is constant on the
consecutive angular blocks assigned by `PlatformReferencePartition`.  Its
spatial velocity is `C.location i - platformAngularDistance a theta` on the
`i`th block.  The endpoint-adjoint calculation uses this velocity multiplied
by the platform density.  This file defines that concrete piecewise field and
records its block values and its one-sided value at the top endpoint.
-/

set_option warningAsError false

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1038

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The density-weighted material velocity of an atomized residual target.
The half-open convention makes the blocks disjoint and assigns `pi` to the
last block. -/
def platformResidualMaterialField
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (theta : ℝ) : ℝ :=
  ∑ i,
    (Ioc
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)).indicator
      (fun phi ↦
        platformAngularDensity k a phi *
          (C.location i - platformAngularDistance a phi)) theta

omit [LinearOrder ι] in
private lemma continuous_platformResidualMaterialTerm
    (C : ResidualConfiguration ι) (k a : ℝ) (ha : 0 < a) (ha2 : a < 2)
    (i : ι) :
    Continuous (fun theta ↦
      platformAngularDensity k a theta *
        (C.location i - platformAngularDistance a theta)) := by
  have hd : Continuous (platformAngularDistance a) := by
    unfold platformAngularDistance
    fun_prop
  have hdpos (theta : ℝ) : 0 < platformAngularDistance a theta := by
    have hr : 0 ≤ platformRadius a := by
      unfold platformRadius
      linarith
    have hcos := Real.cos_le_one theta
    have hmul : platformRadius a * Real.cos theta ≤ platformRadius a :=
      by simpa only [mul_one] using! mul_le_mul_of_nonneg_left hcos hr
    have hge : a ≤ platformAngularDistance a theta := by
      unfold platformAngularDistance
      linarith [platformCenter_sub_radius a]
    exact ha.trans_le hge
  have hA : Continuous (platformAngularDensity k a) := by
    unfold platformAngularDensity platformDensityCoefficient
    exact continuous_const.sub
      (continuous_const.div hd (fun theta ↦ (hdpos theta).ne'))
  exact hA.mul (continuous_const.sub hd)

/-- The material field is Borel measurable despite its finitely many block
jumps. -/
theorem measurable_platformResidualMaterialField
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Measurable
      (platformResidualMaterialField C k a hk ha ha2 hthreshold) := by
  classical
  unfold platformResidualMaterialField
  apply Finset.measurable_sum
  intro i _hi
  exact (continuous_platformResidualMaterialTerm C k a ha ha2 i).measurable.indicator
    measurableSet_Ioc

/-- The material field is integrable on the full angular platform interval. -/
theorem intervalIntegrable_platformResidualMaterialField
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    IntervalIntegrable
      (platformResidualMaterialField C k a hk ha ha2 hthreshold)
      volume 0 Real.pi := by
  classical
  unfold platformResidualMaterialField
  have hterm (i : ι) : IntervalIntegrable
      ((Ioc
        (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
        (platformResidualBlockRight C k a hk ha ha2 hthreshold i)).indicator
        (fun theta ↦
          platformAngularDensity k a theta *
            (C.location i - platformAngularDistance a theta)))
      volume 0 Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
    have hbase : IntegrableOn
        (fun theta ↦
          platformAngularDensity k a theta *
            (C.location i - platformAngularDistance a theta))
        (Ioc (0 : ℝ) Real.pi) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
      exact (continuous_platformResidualMaterialTerm C k a ha ha2 i).intervalIntegrable
        0 Real.pi
    exact hbase.indicator measurableSet_Ioc
  have hsum := IntervalIntegrable.sum Finset.univ (fun i _hi ↦ hterm i)
  refine hsum.congr ?_
  intro theta _htheta
  simp only [Finset.sum_apply]

/-- On its assigned half-open block, the finite sum reduces to the expected
density-weighted target velocity. -/
theorem platformResidualMaterialField_eq_on_block
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (i : ι) {theta : ℝ}
    (htheta : theta ∈ Ioc
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i)) :
    platformResidualMaterialField C k a hk ha ha2 hthreshold theta =
      platformAngularDensity k a theta *
        (C.location i - platformAngularDistance a theta) := by
  classical
  unfold platformResidualMaterialField
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem htheta _
  · intro j _hj hji
    rcases lt_or_gt_of_ne hji with hji | hij
    · have hordered := platformResidualBlocks_ordered C k a hk ha ha2
        hthreshold hji
      have hright_lt :
          platformResidualBlockRight C k a hk ha ha2 hthreshold j < theta :=
        hordered.trans_lt htheta.1
      rw [indicator_of_notMem]
      exact fun hmem ↦ (not_le_of_gt hright_lt) hmem.2
    · have hordered := platformResidualBlocks_ordered C k a hk ha ha2
        hthreshold hij
      have htheta_le : theta ≤
          platformResidualBlockLeft C k a hk ha ha2 hthreshold j :=
        htheta.2.trans hordered
      rw [indicator_of_notMem]
      exact fun hmem ↦ (not_lt_of_ge htheta_le) hmem.1
  · simp

/-- The maximal residual index, which exists because the positive weights
sum to one. -/
def platformResidualLastIndex (C : ResidualConfiguration ι) : ι :=
  Finset.max' Finset.univ (residual_index_univ_nonempty C)

lemma le_platformResidualLastIndex
    (C : ResidualConfiguration ι) (i : ι) :
    i ≤ platformResidualLastIndex C := by
  unfold platformResidualLastIndex
  exact Finset.le_max' Finset.univ i (Finset.mem_univ i)

theorem orderedResidualRightMass_lastIndex
    (C : ResidualConfiguration ι) :
    orderedResidualRightMass C (platformResidualLastIndex C) = 1 := by
  have hfilter :
      Finset.filter (fun j : ι ↦ j ≤ platformResidualLastIndex C)
          Finset.univ = Finset.univ := by
    ext j
    simp [le_platformResidualLastIndex C j]
  unfold orderedResidualRightMass
  rw [hfilter, C.sum_weight]

/-- The last residual block ends exactly at the top platform endpoint. -/
theorem platformResidualBlockRight_lastIndex
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    platformResidualBlockRight C k a hk ha ha2 hthreshold
        (platformResidualLastIndex C) = Real.pi := by
  unfold platformResidualBlockRight
  let u : Icc (0 : ℝ) 1 :=
    ⟨orderedResidualRightMass C (platformResidualLastIndex C),
      orderedResidualRightMass_mem_Icc C (platformResidualLastIndex C)⟩
  have hu : u = ⟨1, by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    exact orderedResidualRightMass_lastIndex C
  change platformReferenceCut k a hk ha ha2 hthreshold u = Real.pi
  rw [hu]
  exact platformReferenceCut_one k a hk ha ha2 hthreshold

/-- Exact endpoint value needed by the endpoint-corrected adjoint identity. -/
theorem platformResidualMaterialField_pi
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    platformResidualMaterialField C k a hk ha ha2 hthreshold Real.pi =
      platformAPi k a *
        (C.location (platformResidualLastIndex C) - 2) := by
  have hright := platformResidualBlockRight_lastIndex C k a hk ha ha2 hthreshold
  have hleftRight := platformResidualBlockLeft_lt_right C k a hk ha ha2
    hthreshold (platformResidualLastIndex C)
  have hpi : Real.pi ∈ Ioc
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold
        (platformResidualLastIndex C))
      (platformResidualBlockRight C k a hk ha ha2 hthreshold
        (platformResidualLastIndex C)) := by
    constructor
    · simpa only [hright] using! hleftRight
    · exact hright.ge
  rw [platformResidualMaterialField_eq_on_block C k a hk ha ha2
      hthreshold (platformResidualLastIndex C) hpi,
    platformAngularDistance_pi]
  rfl

/-- The endpoint correction has the favorable sign for every residual
configuration because its top atom lies at or below distance two. -/
theorem platformResidualMaterialField_pi_nonpos
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    platformResidualMaterialField C k a hk ha ha2 hthreshold Real.pi ≤ 0 := by
  rw [platformResidualMaterialField_pi C k a hk ha ha2 hthreshold]
  exact mul_nonpos_of_nonneg_of_nonpos
    (platformAPi_pos (le_trans (by norm_num) hk) ha ha2.le).le
    (sub_nonpos.mpr (C.location_mem (platformResidualLastIndex C)).2)

/-- The material field is continuous from the left at the top endpoint.  All
possible jumps occur at earlier block boundaries; a whole one-sided
neighborhood of `pi` lies in the final half-open block. -/
theorem continuousWithinAt_platformResidualMaterialField_pi
    (C : ResidualConfiguration ι)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    ContinuousWithinAt
      (platformResidualMaterialField C k a hk ha ha2 hthreshold)
      (Icc (0 : ℝ) Real.pi) Real.pi := by
  let i := platformResidualLastIndex C
  let G : ℝ → ℝ := fun theta ↦
    platformAngularDensity k a theta *
      (C.location i - platformAngularDistance a theta)
  have hG : Continuous G := by
    dsimp only [G, i]
    exact continuous_platformResidualMaterialTerm C k a ha ha2
      (platformResidualLastIndex C)
  have hright := platformResidualBlockRight_lastIndex
    C k a hk ha ha2 hthreshold
  have hleftPi :
      platformResidualBlockLeft C k a hk ha ha2 hthreshold i < Real.pi := by
    have hleftRight := platformResidualBlockLeft_lt_right C k a hk ha ha2
      hthreshold i
    simpa only [i, hright] using! hleftRight
  have hnear : Ioi
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i) ∈
      nhdsWithin Real.pi (Icc (0 : ℝ) Real.pi) :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hleftPi)
  have hevent :
      platformResidualMaterialField C k a hk ha ha2 hthreshold =ᶠ[
        nhdsWithin Real.pi (Icc (0 : ℝ) Real.pi)] G := by
    filter_upwards [hnear, self_mem_nhdsWithin] with theta hthetaNear hthetaFull
    apply platformResidualMaterialField_eq_on_block
      C k a hk ha ha2 hthreshold i
    constructor
    · exact hthetaNear
    · simpa only [i, hright] using! hthetaFull.2
  exact hG.continuousWithinAt.congr_of_eventuallyEq_of_mem hevent
    ⟨Real.pi_pos.le, le_rfl⟩

end

end Erdos1038
