import ErdosProblems.Erdos1038.PlatformResidualBlockTangent

/-!
# Integrability of residual block logarithmic tangents

The deficit-energy calculation already contains the mixed logarithmic
product estimate needed for the block tangent.  This file exposes the
integrability consequence independently of the value of that energy.
-/

set_option warningAsError false

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1038

noncomputable section

local notation "AngleCircle" => AddCircle (2 * Real.pi)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private lemma residualLog_circleIntervalRadialDensity_neg
    (density : ℝ → ℝ) (left right : ℝ) (z : AngleCircle) :
    circleIntervalRadialDensity density left right (-z) =
      circleIntervalRadialDensity density left right z := by
  unfold circleIntervalRadialDensity
  have hdist : dist (-z) (0 : AngleCircle) = dist z 0 := by
    simpa only [neg_zero] using! (dist_neg_neg z (0 : AngleCircle))
  rw [hdist]

private lemma residualLog_circleIntervalRadialDensity_coe
    (density : ℝ → ℝ) (left right : ℝ)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) Real.pi) :
    circleIntervalRadialDensity density left right (theta : AngleCircle) =
      (Icc left right).indicator density theta := by
  have habs : |theta - 0| ≤ Real.pi := by
    simpa only [sub_zero, abs_of_nonneg htheta.1] using! htheta.2
  have hdist : dist (theta : AngleCircle) (0 : AngleCircle) = theta := by
    simpa only [sub_zero, abs_of_nonneg htheta.1] using!
      (addCircle_dist_coe_coe_eq_abs_sub (theta := theta) (phi := 0) habs)
  unfold circleIntervalRadialDensity
  rw [hdist]

private lemma residualLog_circleIntervalRadialDensity_neg_coe
    (density : ℝ → ℝ) (left right : ℝ)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) Real.pi) :
    circleIntervalRadialDensity density left right
        ((-theta : ℝ) : AngleCircle) =
      (Icc left right).indicator density theta := by
  rw [show ((-theta : ℝ) : AngleCircle) =
      -((theta : ℝ) : AngleCircle) by simp only [AddCircle.coe_neg]]
  rw [residualLog_circleIntervalRadialDensity_neg,
    residualLog_circleIntervalRadialDensity_coe density left right htheta]

private theorem residualLog_integrable_positive_square
    {F : AngleCircle × AngleCircle → ℝ}
    (hF : Integrable F (volume.prod volume))
    {left right : ℝ} (hleft : 0 ≤ left)
    (hle : left ≤ right) (hright : right ≤ Real.pi) :
    Integrable
      (fun p : ℝ × ℝ ↦
        F ((p.1 : AngleCircle), (p.2 : AngleCircle)))
      ((volume.restrict (Ioc left right)).prod
        (volume.restrict (Ioc left right))) := by
  have hfundamental :
      Integrable
        (fun p : ℝ × ℝ ↦
          F ((p.1 : AngleCircle), (p.2 : AngleCircle)))
        ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod
          (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    have hmap := MeasurePreserving.prod
      (AddCircle.measurePreserving_mk (2 * Real.pi) 0)
      (AddCircle.measurePreserving_mk (2 * Real.pi) 0)
    have hpull := (hmap.integrable_comp hF.aestronglyMeasurable).2 hF
    simpa only [zero_add, Function.comp_apply, Prod.map_apply] using! hpull
  apply hfundamental.mono_measure
  rw [Measure.prod_restrict, Measure.prod_restrict]
  apply Measure.restrict_mono _ le_rfl
  apply Set.prod_mono <;> intro theta htheta
  · exact ⟨hleft.trans_lt htheta.1, by
      linarith [htheta.2, hright, Real.pi_pos]⟩
  · exact ⟨hleft.trans_lt htheta.1, by
      linarith [htheta.2, hright, Real.pi_pos]⟩

/-- The normalized adjoint density times one normalized reference block
logarithmic potential is integrable in the outer block variable. -/
theorem intervalIntegrable_platformNormalizedAdjointDensity_mul_blockLogPotential
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi) :
    IntervalIntegrable
      (fun theta : ℝ ↦
        platformNormalizedAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          ∫ phi : ℝ in left..right,
            platformNormalizedReferenceDensity k a phi *
              Real.log |platformAngularDistance a theta -
                platformAngularDistance a phi|)
      volume left right := by
  let f : AngleCircle → ℝ :=
    platformAdjointCircleDensity
      a xMinus xPlus sigmaMinus sigmaPlus left right
  let g : AngleCircle → ℝ :=
    platformReferenceCircleDensity k a left right
  let F : AngleCircle × AngleCircle → ℝ := fun p ↦
    f p.1 * g p.2 * circleLogDeficitAt p.1 p.2
  let A : ℝ → ℝ := platformNormalizedReferenceDensity k a
  let B : ℝ → ℝ := platformNormalizedAdjointDensity
    a xMinus xPlus sigmaMinus sigmaPlus
  let C0 : ℝ := Real.log (platformCapacity a) + 2 * Real.log 2
  let DS : ℝ × ℝ → ℝ := fun p ↦
    B p.1 * A p.2 *
      circleLogDeficitAt (p.1 : AngleCircle) (p.2 : AngleCircle)
  let DO : ℝ × ℝ → ℝ := fun p ↦
    B p.1 * A p.2 *
      circleLogDeficitAt ((-p.1 : ℝ) : AngleCircle)
        (p.2 : AngleCircle)
  let L : ℝ × ℝ → ℝ := fun p ↦
    B p.1 * A p.2 *
      Real.log |platformAngularDistance a p.1 -
        platformAngularDistance a p.2|
  let mu : Measure ℝ := volume.restrict (Ioc left right)
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  have hf : Measurable f :=
    measurable_platformAdjointCircleDensity
      a xMinus xPlus sigmaMinus sigmaPlus left right
  have hg : Measurable g :=
    measurable_platformReferenceCircleDensity k a left right
  have hf0 : ∀ z, 0 ≤ f z := fun z ↦
    (platformAdjointCircleDensity_mem_Icc
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hright z).1
  have hg0 : ∀ z, 0 ≤ g z := fun z ↦
    (platformReferenceCircleDensity_mem_Icc
      hk0 ha ha2.le hthreshold hleft hright z).1
  have hfinite : circleDensityLogDeficit f g ≠ ∞ := by
    rw [circleDensityLogDeficit_comm hf hg]
    exact platformCircleDensity_logDeficit_ne_top hk0 ha ha2 hthreshold
      hxMinus hxPlus hsigmaMinus hsigmaPlus hleft hlt.le hright
  have hF : Integrable F (volume.prod volume) :=
    integrable_circleDensityLogDeficit_product_of_ne_top
      hf hg hf0 hg0 hfinite
  have hFnegative : Integrable
      (fun p : AngleCircle × AngleCircle ↦ F (-p.1, p.2))
        (volume.prod volume) := by
    have hmap := MeasurePreserving.prod
      (Measure.measurePreserving_neg (volume : Measure AngleCircle))
      (MeasurePreserving.id (volume : Measure AngleCircle))
    have hpull := (hmap.integrable_comp hF.aestronglyMeasurable).2 hF
    simpa only [Function.comp_apply, Prod.map_apply, id_eq] using! hpull
  have hDSpull := residualLog_integrable_positive_square
    hF hleft hlt.le hright
  have hDOpull := residualLog_integrable_positive_square
    hFnegative hleft hlt.le hright
  have hDS : Integrable DS (mu.prod mu) := by
    apply hDSpull.congr
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have hp1 : p.1 ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hleft.trans hp.1.1.le, hp.1.2.trans hright⟩
    have hp2 : p.2 ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hleft.trans hp.2.1.le, hp.2.2.trans hright⟩
    have hpmem1 : p.1 ∈ Icc left right := ⟨hp.1.1.le, hp.1.2⟩
    have hpmem2 : p.2 ∈ Icc left right := ⟨hp.2.1.le, hp.2.2⟩
    have hfcoe : f (p.1 : AngleCircle) = B p.1 := by
      dsimp only [f, B, platformAdjointCircleDensity]
      rw [residualLog_circleIntervalRadialDensity_coe _ _ _ hp1,
        indicator_of_mem hpmem1]
    have hgcoe : g (p.2 : AngleCircle) = A p.2 := by
      dsimp only [g, A, platformReferenceCircleDensity]
      rw [residualLog_circleIntervalRadialDensity_coe _ _ _ hp2,
        indicator_of_mem hpmem2]
    dsimp only [F, DS]
    rw [hfcoe, hgcoe]
  have hDO : Integrable DO (mu.prod mu) := by
    apply hDOpull.congr
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have hp1 : p.1 ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hleft.trans hp.1.1.le, hp.1.2.trans hright⟩
    have hp2 : p.2 ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hleft.trans hp.2.1.le, hp.2.2.trans hright⟩
    have hpmem1 : p.1 ∈ Icc left right := ⟨hp.1.1.le, hp.1.2⟩
    have hpmem2 : p.2 ∈ Icc left right := ⟨hp.2.1.le, hp.2.2⟩
    have hfcoe : f (-((p.1 : ℝ) : AngleCircle)) = B p.1 := by
      rw [← show ((-p.1 : ℝ) : AngleCircle) =
        -((p.1 : ℝ) : AngleCircle) by simp only [AddCircle.coe_neg]]
      dsimp only [f, B, platformAdjointCircleDensity]
      rw [residualLog_circleIntervalRadialDensity_neg_coe _ _ _ hp1,
        indicator_of_mem hpmem1]
    have hgcoe : g (p.2 : AngleCircle) = A p.2 := by
      dsimp only [g, A, platformReferenceCircleDensity]
      rw [residualLog_circleIntervalRadialDensity_coe _ _ _ hp2,
        indicator_of_mem hpmem2]
    dsimp only [F, DO]
    rw [hfcoe, hgcoe]
    simp only [AddCircle.coe_neg]
  have hA : Integrable A mu := by
    have hAinterval :=
      (intervalIntegrable_platformNormalizedReferenceDensity
        k ha ha2.le).mono_set (by
          rw [uIcc_of_le hlt.le, uIcc_of_le Real.pi_pos.le]
          exact Icc_subset_Icc hleft hright)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le] at hAinterval
    simpa only [A, mu] using! hAinterval
  have hB : Integrable B mu := by
    have hBinterval :=
      (intervalIntegrable_platformNormalizedAdjointDensity
        (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
        hxMinus hxPlus ha2).mono_set (by
          rw [uIcc_of_le hlt.le, uIcc_of_le Real.pi_pos.le]
          exact Icc_subset_Icc hleft hright)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le] at hBinterval
    simpa only [B, mu] using! hBinterval
  have hconstant : Integrable
      (fun p : ℝ × ℝ ↦ C0 * (B p.1 * A p.2))
      (mu.prod mu) := (hB.mul_prod hA).const_mul C0
  have hfstPi : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      p.1 ≠ Real.pi := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_eq_fun measurable_fst measurable_const).compl)).2
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) Real.pi]
      with theta htheta
    exact Filter.Eventually.of_forall fun _phi ↦ htheta
  have hsndPi : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      p.2 ≠ Real.pi := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_eq_fun measurable_snd measurable_const).compl)).2
    exact Filter.Eventually.of_forall fun _theta ↦
      Measure.ae_ne (volume : Measure ℝ) Real.pi
  have hdiagonal : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      p.1 ≠ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_eq_fun measurable_fst measurable_snd).compl)).2
    filter_upwards with theta
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) theta]
      with phi hphi
    exact hphi.symm
  have hpointwise : L =ᵐ[mu.prod mu]
      fun p ↦ C0 * (B p.1 * A p.2) - DS p - DO p := by
    change L =ᵐ[
      (volume.restrict (Ioc left right)).prod
        (volume.restrict (Ioc left right))] _
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem
        (measurableSet_Ioc.prod measurableSet_Ioc),
      ae_restrict_of_ae hfstPi, ae_restrict_of_ae hsndPi,
      ae_restrict_of_ae hdiagonal] with p hp hfst hsnd hne
    have hp1 : p.1 ∈ Ioo (0 : ℝ) Real.pi :=
      ⟨hleft.trans_lt hp.1.1,
        lt_of_le_of_ne (hp.1.2.trans hright) hfst⟩
    have hp2 : p.2 ∈ Ioo (0 : ℝ) Real.pi :=
      ⟨hleft.trans_lt hp.2.1,
        lt_of_le_of_ne (hp.2.2.trans hright) hsnd⟩
    have hkernel :=
      log_abs_platformAngularDistance_sub_eq_circleDeficits
        ha2 hp1 hp2 hne
    dsimp only [L, C0, DS, DO]
    rw [hkernel]
    ring
  have hL : Integrable L (mu.prod mu) :=
    ((hconstant.sub hDS).sub hDO).congr hpointwise.symm
  have hLsection :
      (fun theta ↦ ∫ phi, L (theta, phi) ∂mu) =ᵐ[mu]
        fun theta ↦ B theta * ∫ phi, A phi *
          Real.log |platformAngularDistance a theta -
            platformAngularDistance a phi| ∂mu := by
    exact Filter.Eventually.of_forall fun theta ↦ by
      calc
        (∫ phi, L (theta, phi) ∂mu) =
            ∫ phi, B theta *
              (A phi * Real.log |platformAngularDistance a theta -
                platformAngularDistance a phi|) ∂mu := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun phi ↦ by
            dsimp only [L]
            ring
        _ = B theta * ∫ phi, A phi *
              Real.log |platformAngularDistance a theta -
                platformAngularDistance a phi| ∂mu := by
          rw [integral_const_mul]
  have houter : Integrable
      (fun theta ↦ B theta * ∫ phi, A phi *
        Real.log |platformAngularDistance a theta -
          platformAngularDistance a phi| ∂mu) mu :=
    hL.integral_prod_left.congr hLsection
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le]
  simpa only [A, B, mu, intervalIntegral.integral_of_le hlt.le] using! houter

/-- Unnormalized form of the mixed logarithmic block integrability. -/
theorem intervalIntegrable_platformAngularAdjointDensity_mul_blockLogPotentialKernel
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi) :
    IntervalIntegrable
      (fun theta : ℝ ↦
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          ∫ phi : ℝ in left..right,
            platformAngularDensity k a phi *
              Real.log |platformAngularDistance a theta -
                platformAngularDistance a phi|)
      volume left right := by
  have hnormalized :=
    intervalIntegrable_platformNormalizedAdjointDensity_mul_blockLogPotential
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        hleft hlt hright
  let P := platformAPi k a
  let Q := platformBPi a xMinus xPlus sigmaMinus sigmaPlus
  have hP : 0 < P := by
    exact platformAPi_pos (zero_le_one.trans hk) ha ha2.le
  have hQ : 0 < Q := by
    exact platformBPi_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
  have hinner (theta : ℝ) :
      (∫ phi : ℝ in left..right,
        platformNormalizedReferenceDensity k a phi *
          Real.log |platformAngularDistance a theta -
            platformAngularDistance a phi|) =
        (1 / P) *
          ∫ phi : ℝ in left..right,
            platformAngularDensity k a phi *
              Real.log |platformAngularDistance a theta -
                platformAngularDistance a phi| := by
    unfold platformNormalizedReferenceDensity
    change (∫ phi : ℝ in left..right,
      platformAngularDensity k a phi / P *
        Real.log |platformAngularDistance a theta -
          platformAngularDistance a phi|) = _
    rw [show (fun phi : ℝ ↦
        platformAngularDensity k a phi / P *
          Real.log |platformAngularDistance a theta -
            platformAngularDistance a phi|) =
      fun phi ↦
        (platformAngularDensity k a phi *
          Real.log |platformAngularDistance a theta -
            platformAngularDistance a phi|) / P by
        funext phi
        ring,
      intervalIntegral.integral_div]
    ring
  apply (hnormalized.const_mul (Q * P)).congr
  intro theta _htheta
  change Q * P *
      (platformNormalizedAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta *
        (∫ phi : ℝ in left..right,
          platformNormalizedReferenceDensity k a phi *
            Real.log |platformAngularDistance a theta -
              platformAngularDistance a phi|)) =
    platformAngularAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus theta *
      ∫ phi : ℝ in left..right,
        platformAngularDensity k a phi *
          Real.log |platformAngularDistance a theta -
            platformAngularDistance a phi|
  rw [hinner]
  unfold platformNormalizedAdjointDensity
  change Q * P *
      (platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta / Q *
        ((1 / P) *
          ∫ phi : ℝ in left..right,
            platformAngularDensity k a phi *
              Real.log |platformAngularDistance a theta -
                platformAngularDistance a phi|)) = _
  field_simp [hP.ne', hQ.ne']

/-- Every lower logarithmic block-tangent integrand in Dalton's interface
is interval integrable. -/
theorem intervalIntegrable_platformResidualBlockLogTangentPairingIntegrand
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (C : ResidualConfiguration ι)
    {k a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (i : ι) :
    IntervalIntegrable
      (fun theta : ℝ ↦
        platformAngularAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          platformResidualBlockLogTangentLower C k a
            hk ha ha2 hthreshold i theta)
      volume
      (platformResidualBlockLeft C k a hk ha ha2 hthreshold i)
      (platformResidualBlockRight C k a hk ha ha2 hthreshold i) := by
  let left := platformResidualBlockLeft C k a hk ha ha2 hthreshold i
  let right := platformResidualBlockRight C k a hk ha ha2 hthreshold i
  let B := platformAngularAdjointDensity
    a xMinus xPlus sigmaMinus sigmaPlus
  let constant := residualBackgroundAt C k i - platformPotentialConstant k a -
    C.weight i
  have hleft := platformResidualBlockLeft_mem_Icc
    C k a hk ha ha2 hthreshold i
  have hright := platformResidualBlockRight_mem_Icc
    C k a hk ha ha2 hthreshold i
  have hlt : left < right :=
    platformResidualBlockLeft_lt_right C k a hk ha ha2 hthreshold i
  have hB : IntervalIntegrable B volume left right :=
    (intervalIntegrable_platformAngularAdjointDensity
      hxMinus hxPlus ha2).mono_set (by
        rw [uIcc_of_le hlt.le, uIcc_of_le Real.pi_pos.le]
        exact Icc_subset_Icc hleft.1 hright.2)
  have hconstant : IntervalIntegrable
      (fun theta ↦ constant * B theta) volume left right :=
    hB.const_mul constant
  have hlog :=
    intervalIntegrable_platformAngularAdjointDensity_mul_blockLogPotentialKernel
      hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        hleft.1 hlt hright.2
  have hlogScaled : IntervalIntegrable
      (fun theta : ℝ ↦ (1 / Real.pi) *
        (B theta *
          ∫ phi : ℝ in left..right,
            platformAngularDensity k a phi *
              Real.log |platformAngularDistance a theta -
                platformAngularDistance a phi|))
      volume left right := hlog.const_mul (1 / Real.pi)
  apply (hconstant.add hlogScaled).congr
  intro theta _htheta
  dsimp only [B, constant, left, right]
  unfold platformResidualBlockLogTangentLower
    platformResidualBlockLogPotential
  ring

end

end Erdos1038
