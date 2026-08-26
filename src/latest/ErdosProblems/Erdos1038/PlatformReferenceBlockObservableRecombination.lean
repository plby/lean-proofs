import ErdosProblems.Erdos1038.PlatformReferenceMomentLimits
import ErdosProblems.Erdos1038.PlatformReferenceQuantileAngularIntegral

/-!
# Recombining canonical platform block observables

The canonical refinement is sampled separately on each atomic target block.
After the affine change from a block parameter to global probability mass,
those block integrals telescope to the integral over the full platform
quantile.  Consequently the continuum observable limit is independent of
the auxiliary target partition whenever the observable itself is.
-/

set_option warningAsError false

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- A scalar observable pulled back along the full platform quantile and
extended continuously to real arguments by projection onto `[0,1]`. -/
def platformReferenceQuantileIntegrand
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  F (platformReferenceQuantile k a hk ha ha2 hthreshold
    (projIcc 0 1 zero_le_one u))

theorem continuous_platformReferenceQuantileIntegrand
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc a 2)) :
    Continuous (platformReferenceQuantileIntegrand k a
      hk ha ha2 hthreshold F) := by
  have hquantile : Continuous (fun u : ℝ ↦
      platformReferenceQuantile k a hk ha ha2 hthreshold
        (projIcc 0 1 zero_le_one u)) :=
    (continuous_platformReferenceQuantile k a hk ha ha2 hthreshold).comp
      continuous_projIcc
  exact hF.comp_continuous hquantile fun u ↦
    platformReferenceQuantile_mem_Icc k a hk ha ha2 hthreshold
      (projIcc 0 1 zero_le_one u)

/-- On one target block, multiplication by its mass is exactly the affine
Jacobian that changes the local parameter integral into the corresponding
global probability-mass interval integral. -/
theorem weight_mul_integral_platformResidualBlockReferenceIntegrand
    (C : ResidualConfiguration iota) (i : iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) :
    C.weight i *
        (∫ t in (0 : ℝ)..1,
          platformResidualBlockReferenceIntegrand C i
            k a hk ha ha2 hthreshold F t) =
      ∫ u in orderedResidualLeftMass C i..orderedResidualRightMass C i,
        platformReferenceQuantileIntegrand k a
          hk ha ha2 hthreshold F u := by
  let G := platformReferenceQuantileIntegrand k a
    hk ha ha2 hthreshold F
  have hlocal :
      (∫ t in (0 : ℝ)..1,
        platformResidualBlockReferenceIntegrand C i
          k a hk ha ha2 hthreshold F t) =
        ∫ t in (0 : ℝ)..1,
          G (orderedResidualLeftMass C i + C.weight i * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hmass : orderedResidualLeftMass C i + C.weight i * t ∈
        Icc (0 : ℝ) 1 :=
      (platformResidualBlockMassParameter C i ⟨t, ht⟩).property
    unfold platformResidualBlockReferenceIntegrand G
      platformReferenceQuantileIntegrand
    rw [projIcc_of_mem zero_le_one ht]
    change F (platformReferenceQuantile k a hk ha ha2 hthreshold
        (platformResidualBlockMassParameter C i ⟨t, ht⟩)) =
      F (platformReferenceQuantile k a hk ha ha2 hthreshold
        (projIcc 0 1 zero_le_one
          (orderedResidualLeftMass C i + C.weight i * t)))
    rw [projIcc_of_mem zero_le_one hmass]
    congr 2
  rw [hlocal]
  have haffine := intervalIntegral.smul_integral_comp_add_mul
    (f := G) (a := (0 : ℝ)) (b := 1)
      (C.weight i) (orderedResidualLeftMass C i)
  simpa only [smul_eq_mul, mul_zero, add_zero, mul_one,
    orderedResidualRightMass_eq_left_add_weight] using! haffine

/-- The global probability-mass intervals of all ordered target blocks
recombine exactly into `[0,1]`. -/
theorem sum_integral_platformReferenceQuantileIntegrand_blocks
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc a 2)) :
    (∑ i,
      ∫ u in orderedResidualLeftMass C i..orderedResidualRightMass C i,
        platformReferenceQuantileIntegrand k a
          hk ha ha2 hthreshold F u) =
      ∫ u in (0 : ℝ)..1,
        platformReferenceQuantileIntegrand k a
          hk ha ha2 hthreshold F u := by
  let G := platformReferenceQuantileIntegrand k a
    hk ha ha2 hthreshold F
  let primitive : ℝ → ℝ := fun x ↦ ∫ u in (0 : ℝ)..x, G u
  have hcontinuous : Continuous G := by
    simpa only [G] using! continuous_platformReferenceQuantileIntegrand
      k a hk ha ha2 hthreshold F hF
  have hblock (i : iota) :
      (∫ u in orderedResidualLeftMass C i..orderedResidualRightMass C i,
        G u) =
        primitive (orderedResidualRightMass C i) -
          primitive (orderedResidualLeftMass C i) := by
    have hleft : IntervalIntegrable G volume (0 : ℝ)
        (orderedResidualLeftMass C i) :=
      hcontinuous.intervalIntegrable _ _
    have hright : IntervalIntegrable G volume
        (orderedResidualLeftMass C i) (orderedResidualRightMass C i) :=
      hcontinuous.intervalIntegrable _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      hleft hright
    dsimp only [primitive]
    linarith
  have htelescope := sum_apply_orderedResidualRight_sub_left C primitive
  calc
    (∑ i,
        ∫ u in orderedResidualLeftMass C i..orderedResidualRightMass C i,
          platformReferenceQuantileIntegrand k a
            hk ha ha2 hthreshold F u) =
        ∑ i,
          (primitive (orderedResidualRightMass C i) -
            primitive (orderedResidualLeftMass C i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simpa only [G] using! hblock i
    _ = primitive 1 - primitive 0 := htelescope
    _ = ∫ u in (0 : ℝ)..1,
          platformReferenceQuantileIntegrand k a
            hk ha ha2 hthreshold F u := by
      simp only [primitive, intervalIntegral.integral_same, sub_zero, G]

/-- A block-independent continuum observable limit is `1/k` times its
integral over the full platform reference quantile. -/
theorem platformReferenceBlockObservableLimit_const_eq_quantileIntegral
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc a 2)) :
    platformReferenceBlockObservableLimit C k a hk ha ha2 hthreshold
        (fun _i ↦ F) =
      (1 / k) *
        (∫ u in (0 : ℝ)..1,
          platformReferenceQuantileIntegrand k a
            hk ha ha2 hthreshold F u) := by
  unfold platformReferenceBlockObservableLimit
  calc
    (∑ i, residualLagrangeAlpha C k i *
        (∫ t in (0 : ℝ)..1,
          platformResidualBlockReferenceIntegrand C i
            k a hk ha ha2 hthreshold F t)) =
      ∑ i, (1 / k) *
        (C.weight i *
          (∫ t in (0 : ℝ)..1,
            platformResidualBlockReferenceIntegrand C i
              k a hk ha ha2 hthreshold F t)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      unfold residualLagrangeAlpha
      ring
    _ = ∑ i, (1 / k) *
        (∫ u in orderedResidualLeftMass C i..orderedResidualRightMass C i,
          platformReferenceQuantileIntegrand k a
            hk ha ha2 hthreshold F u) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [weight_mul_integral_platformResidualBlockReferenceIntegrand]
    _ = (1 / k) *
        (∑ i,
          ∫ u in orderedResidualLeftMass C i..orderedResidualRightMass C i,
            platformReferenceQuantileIntegrand k a
              hk ha ha2 hthreshold F u) := by
      rw [Finset.mul_sum]
    _ = (1 / k) *
        (∫ u in (0 : ℝ)..1,
          platformReferenceQuantileIntegrand k a
            hk ha ha2 hthreshold F u) := by
      rw [sum_integral_platformReferenceQuantileIntegrand_blocks
        C k a hk ha ha2 hthreshold F hF]

/-- Final partition-free form: a block-independent continuum observable is
the normalized angular integral against the constant-platform density. -/
theorem platformReferenceBlockObservableLimit_const_eq_angularIntegral
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc a 2)) :
    platformReferenceBlockObservableLimit C k a hk ha ha2 hthreshold
        (fun _i ↦ F) =
      (1 / k) * (1 / Real.pi) *
        (∫ theta in (0 : ℝ)..Real.pi,
          platformAngularDensity k a theta *
            F (platformAngularDistance a theta)) := by
  rw [platformReferenceBlockObservableLimit_const_eq_quantileIntegral
    C k a hk ha ha2 hthreshold F hF]
  change (1 / k) *
      (∫ u in (0 : ℝ)..1,
        F (platformReferenceQuantile k a hk ha ha2 hthreshold
          (projIcc 0 1 zero_le_one u))) = _
  rw [integral_platformReferenceQuantile_eq_angular
    k a hk ha ha2 hthreshold F hF]
  ring

/-- The continuum inverse moment is the corresponding full-quantile
integral, divided by `k`. -/
theorem platformReferenceInverseMomentLimit_eq_quantileIntegral
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (ell : ℕ) :
    platformReferenceInverseMomentLimit C k a
        hk ha ha2 hthreshold ell =
      (1 / k) *
        (∫ u in (0 : ℝ)..1,
          platformReferenceQuantileIntegrand k a
            hk ha ha2 hthreshold (fun d ↦ d⁻¹ ^ ell) u) := by
  unfold platformReferenceInverseMomentLimit
  apply platformReferenceBlockObservableLimit_const_eq_quantileIntegral
  exact (continuousOn_id.inv₀ fun d hd ↦
    (ha.trans_le hd.1).ne').pow ell

/-- Angular-density form of every continuum inverse moment. -/
theorem platformReferenceInverseMomentLimit_eq_angularIntegral
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (ell : ℕ) :
    platformReferenceInverseMomentLimit C k a
        hk ha ha2 hthreshold ell =
      (1 / k) * (1 / Real.pi) *
        (∫ theta in (0 : ℝ)..Real.pi,
          platformAngularDensity k a theta *
            (platformAngularDistance a theta)⁻¹ ^ ell) := by
  unfold platformReferenceInverseMomentLimit
  apply platformReferenceBlockObservableLimit_const_eq_angularIntegral
  exact (continuousOn_id.inv₀ fun d hd ↦
    (ha.trans_le hd.1).ne').pow ell

/-- The continuum logarithmic scale is the full-quantile logarithmic
moment, divided by `k`. -/
theorem platformReferenceLogMomentLimit_eq_quantileIntegral
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    platformReferenceLogMomentLimit C k a
        hk ha ha2 hthreshold =
      (1 / k) *
        (∫ u in (0 : ℝ)..1,
          platformReferenceQuantileIntegrand k a
            hk ha ha2 hthreshold Real.log u) := by
  unfold platformReferenceLogMomentLimit
  apply platformReferenceBlockObservableLimit_const_eq_quantileIntegral
  exact continuousOn_id.log fun d hd ↦ (ha.trans_le hd.1).ne'

/-- Angular-density form of the continuum logarithmic scale. -/
theorem platformReferenceLogMomentLimit_eq_angularIntegral
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    platformReferenceLogMomentLimit C k a
        hk ha ha2 hthreshold =
      (1 / k) * (1 / Real.pi) *
        (∫ theta in (0 : ℝ)..Real.pi,
          platformAngularDensity k a theta *
            Real.log (platformAngularDistance a theta)) := by
  unfold platformReferenceLogMomentLimit
  apply platformReferenceBlockObservableLimit_const_eq_angularIntegral
  exact continuousOn_id.log fun d hd ↦ (ha.trans_le hd.1).ne'

/-- The continuum exterior logarithmic potential is the full-quantile
potential in the expected normalization. -/
theorem platformReferenceExteriorLogPotentialLimit_eq_quantileIntegral
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ} (hsa : s < a) :
    platformReferenceExteriorLogPotentialLimit C k a
        hk ha ha2 hthreshold s =
      Real.log s + (1 / k) *
        (∫ u in (0 : ℝ)..1,
          platformReferenceQuantileIntegrand k a
            hk ha ha2 hthreshold (fun d ↦ Real.log (d - s)) u) := by
  unfold platformReferenceExteriorLogPotentialLimit
  rw [platformReferenceBlockObservableLimit_const_eq_quantileIntegral]
  exact (continuousOn_id.sub continuousOn_const).log fun d hd ↦
    (sub_pos.mpr (hsa.trans_le hd.1)).ne'

/-- Angular-density form of the continuum exterior logarithmic potential. -/
theorem platformReferenceExteriorLogPotentialLimit_eq_angularIntegral
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ} (hsa : s < a) :
    platformReferenceExteriorLogPotentialLimit C k a
        hk ha ha2 hthreshold s =
      Real.log s + (1 / k) * (1 / Real.pi) *
        (∫ theta in (0 : ℝ)..Real.pi,
          platformAngularDensity k a theta *
            Real.log (platformAngularDistance a theta - s)) := by
  unfold platformReferenceExteriorLogPotentialLimit
  rw [platformReferenceBlockObservableLimit_const_eq_angularIntegral]
  exact (continuousOn_id.sub continuousOn_const).log fun d hd ↦
    (sub_pos.mpr (hsa.trans_le hd.1)).ne'

end

end Erdos1038
