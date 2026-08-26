import ErdosProblems.Erdos1038.DensityKernelEnergyIntegral
import ErdosProblems.Erdos1038.PlatformDeficitEnergy

/-!
# The platform deficit block as a physical angular integral

This file combines the real-integral form of the circle density deficit with
the angular factorization of the platform logarithmic kernel.  It identifies
the abstract deficit block energy with the physical mixed logarithmic energy
on the corresponding angular interval.
-/

set_option warningAsError false

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1038

noncomputable section

local notation "AngleCircle" => AddCircle (2 * Real.pi)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private lemma intervalIntegral_indicator_Icc_nested
    {f : ℝ → ℝ} {a c d b : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    (∫ x : ℝ in a..b, (Icc c d).indicator f x) =
      ∫ x : ℝ in c..d, f x := by
  have hab : a ≤ b := hac.trans (hcd.trans hdb)
  rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hcd]
  have hμab : (volume : Measure ℝ).restrict (Ioc a b) =
      volume.restrict (Icc a b) :=
    Measure.restrict_congr_set
      (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))
  have hμcd : (volume : Measure ℝ).restrict (Ioc c d) =
      volume.restrict (Icc c d) :=
    Measure.restrict_congr_set
      (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))
  rw [hμab, hμcd, integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc]
  rw [inter_eq_left.mpr (Icc_subset_Icc hac hdb)]

private lemma circleIntervalRadialDensity_neg
    (density : ℝ → ℝ) (left right : ℝ) (z : AngleCircle) :
    circleIntervalRadialDensity density left right (-z) =
      circleIntervalRadialDensity density left right z := by
  unfold circleIntervalRadialDensity
  have hdist : dist (-z) (0 : AngleCircle) = dist z 0 := by
    simpa only [neg_zero] using! (dist_neg_neg z (0 : AngleCircle))
  rw [hdist]

private lemma circleIntervalRadialDensity_coe
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

private lemma circleIntervalRadialDensity_neg_coe
    (density : ℝ → ℝ) (left right : ℝ)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) Real.pi) :
    circleIntervalRadialDensity density left right
        ((-theta : ℝ) : AngleCircle) =
      (Icc left right).indicator density theta := by
  rw [show ((-theta : ℝ) : AngleCircle) =
      -((theta : ℝ) : AngleCircle) by simp only [AddCircle.coe_neg]]
  rw [circleIntervalRadialDensity_neg,
    circleIntervalRadialDensity_coe density left right htheta]

private theorem integrable_positive_square_of_integrable_angleCircle
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

private theorem platformCircleDeficit_toReal_eq_reflectedInterval
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    (circleDensityLogDeficit
        (platformReferenceCircleDensity k a left right)
        (platformAdjointCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right)).toReal =
      2 * ∫ theta : ℝ in left..right,
        platformNormalizedAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          ((∫ phi : ℝ in left..right,
              platformNormalizedReferenceDensity k a phi *
                circleLogDeficitAt (theta : AngleCircle)
                  (phi : AngleCircle)) +
            ∫ phi : ℝ in left..right,
              platformNormalizedReferenceDensity k a phi *
                circleLogDeficitAt ((-theta : ℝ) : AngleCircle)
                  (phi : AngleCircle)) := by
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
      hk ha ha2.le hthreshold hleft hright z).1
  have hfinite : circleDensityLogDeficit g f ≠ ∞ :=
    platformCircleDensity_logDeficit_ne_top hk ha ha2 hthreshold
      hxMinus hxPlus hsigmaMinus hsigmaPlus hleft hle hright
  have hfiniteSwap : circleDensityLogDeficit f g ≠ ∞ := by
    rw [circleDensityLogDeficit_comm hf hg]
    exact hfinite
  have hFint : Integrable F (volume.prod volume) := by
    exact integrable_circleDensityLogDeficit_product_of_ne_top
      hf hg hf0 hg0 hfiniteSwap
  have hfneg (z : AngleCircle) : f (-z) = f z := by
    exact circleIntervalRadialDensity_neg _ _ _ z
  have hgneg (z : AngleCircle) : g (-z) = g z := by
    exact circleIntervalRadialDensity_neg _ _ _ z
  have hsame : ∀ theta phi : ℝ,
      F (((-theta : ℝ) : AngleCircle), ((-phi : ℝ) : AngleCircle)) =
        F ((theta : AngleCircle), (phi : AngleCircle)) := by
    intro theta phi
    dsimp only [F]
    rw [show ((-theta : ℝ) : AngleCircle) =
        -((theta : ℝ) : AngleCircle) by simp only [AddCircle.coe_neg],
      show ((-phi : ℝ) : AngleCircle) =
        -((phi : ℝ) : AngleCircle) by simp only [AddCircle.coe_neg],
      hfneg, hgneg, circleLogDeficitAt_neg_neg]
  have hopposite : ∀ theta phi : ℝ,
      F ((theta : AngleCircle), ((-phi : ℝ) : AngleCircle)) =
        F (((-theta : ℝ) : AngleCircle), (phi : AngleCircle)) := by
    intro theta phi
    dsimp only [F]
    rw [show ((-theta : ℝ) : AngleCircle) =
        -((theta : ℝ) : AngleCircle) by simp only [AddCircle.coe_neg],
      show ((-phi : ℝ) : AngleCircle) =
        -((phi : ℝ) : AngleCircle) by simp only [AddCircle.coe_neg],
      hfneg, hgneg]
    exact congrArg (fun t ↦ f (theta : AngleCircle) *
      g (phi : AngleCircle) * t)
        (by
          simpa only [AddCircle.coe_neg, neg_neg] using!
            (circleLogDeficitAt_neg_neg
              (theta : AngleCircle) ((-phi : ℝ) : AngleCircle)).symm)
  have hreflect := integral_angleCircle_prod_eq_two_mul_positive_reflections
    F hFint hsame hopposite
  have hdeficitReal :
      (circleDensityLogDeficit f g).toReal =
        ∫ p : AngleCircle × AngleCircle, F p ∂(volume.prod volume) := by
    exact circleDensityLogDeficit_toReal_eq_integral_prod
      hf hg hf0 hg0
  rw [circleDensityLogDeficit_comm hg hf, hdeficitReal, hreflect]
  congr 1
  calc
    (∫ theta : ℝ in 0..Real.pi,
        ((∫ phi : ℝ in 0..Real.pi,
            F ((theta : AngleCircle), (phi : AngleCircle))) +
          ∫ phi : ℝ in 0..Real.pi,
            F (((-theta : ℝ) : AngleCircle), (phi : AngleCircle))) =
        ∫ theta : ℝ in 0..Real.pi,
          ((Icc left right).indicator
            (fun theta ↦ B theta *
              ((∫ phi : ℝ in left..right,
                  A phi * circleLogDeficitAt (theta : AngleCircle)
                    (phi : AngleCircle)) +
                ∫ phi : ℝ in left..right,
                  A phi * circleLogDeficitAt
                    ((-theta : ℝ) : AngleCircle)
                    (phi : AngleCircle))) theta)) := by
      apply intervalIntegral.integral_congr
      intro theta htheta
      rw [uIcc_of_le Real.pi_pos.le] at htheta
      have hfpos : f (theta : AngleCircle) =
          (Icc left right).indicator B theta := by
        exact circleIntervalRadialDensity_coe B left right htheta
      have hfnegTheta : f ((-theta : ℝ) : AngleCircle) =
          (Icc left right).indicator B theta := by
        exact circleIntervalRadialDensity_neg_coe B left right htheta
      have hinnerSame :
          (∫ phi : ℝ in 0..Real.pi,
              F ((theta : AngleCircle), (phi : AngleCircle))) =
            (Icc left right).indicator B theta *
              ∫ phi : ℝ in left..right,
                A phi * circleLogDeficitAt (theta : AngleCircle)
                  (phi : AngleCircle) := by
        calc
          (∫ phi : ℝ in 0..Real.pi,
              F ((theta : AngleCircle), (phi : AngleCircle))) =
              ∫ phi : ℝ in 0..Real.pi,
                (Icc left right).indicator B theta *
                  (Icc left right).indicator
                    (fun phi ↦ A phi *
                      circleLogDeficitAt (theta : AngleCircle)
                        (phi : AngleCircle)) phi := by
            apply intervalIntegral.integral_congr
            intro phi hphi
            rw [uIcc_of_le Real.pi_pos.le] at hphi
            have hgpos : g (phi : AngleCircle) =
                (Icc left right).indicator A phi := by
              exact circleIntervalRadialDensity_coe A left right hphi
            dsimp only [F]
            rw [hfpos, hgpos]
            by_cases hmem : phi ∈ Icc left right <;>
              simp [indicator_of_mem, indicator_of_notMem, hmem, mul_assoc]
          _ = (Icc left right).indicator B theta *
              ∫ phi : ℝ in 0..Real.pi,
                (Icc left right).indicator
                  (fun phi ↦ A phi *
                    circleLogDeficitAt (theta : AngleCircle)
                      (phi : AngleCircle)) phi := by
            rw [intervalIntegral.integral_const_mul]
          _ = (Icc left right).indicator B theta *
              ∫ phi : ℝ in left..right,
                A phi * circleLogDeficitAt (theta : AngleCircle)
                  (phi : AngleCircle) := by
            rw [intervalIntegral_indicator_Icc_nested hleft hle hright]
      have hinnerOpposite :
          (∫ phi : ℝ in 0..Real.pi,
              F (((-theta : ℝ) : AngleCircle), (phi : AngleCircle))) =
            (Icc left right).indicator B theta *
              ∫ phi : ℝ in left..right,
                A phi * circleLogDeficitAt
                  ((-theta : ℝ) : AngleCircle) (phi : AngleCircle) := by
        calc
          (∫ phi : ℝ in 0..Real.pi,
              F (((-theta : ℝ) : AngleCircle), (phi : AngleCircle))) =
              ∫ phi : ℝ in 0..Real.pi,
                (Icc left right).indicator B theta *
                  (Icc left right).indicator
                    (fun phi ↦ A phi * circleLogDeficitAt
                      ((-theta : ℝ) : AngleCircle)
                        (phi : AngleCircle)) phi := by
            apply intervalIntegral.integral_congr
            intro phi hphi
            rw [uIcc_of_le Real.pi_pos.le] at hphi
            have hgpos : g (phi : AngleCircle) =
                (Icc left right).indicator A phi := by
              exact circleIntervalRadialDensity_coe A left right hphi
            dsimp only [F]
            rw [hfnegTheta, hgpos]
            by_cases hmem : phi ∈ Icc left right <;>
              simp [indicator_of_mem, indicator_of_notMem, hmem, mul_assoc]
          _ = (Icc left right).indicator B theta *
              ∫ phi : ℝ in 0..Real.pi,
                (Icc left right).indicator
                  (fun phi ↦ A phi * circleLogDeficitAt
                    ((-theta : ℝ) : AngleCircle)
                      (phi : AngleCircle)) phi := by
            rw [intervalIntegral.integral_const_mul]
          _ = (Icc left right).indicator B theta *
              ∫ phi : ℝ in left..right,
                A phi * circleLogDeficitAt
                  ((-theta : ℝ) : AngleCircle) (phi : AngleCircle) := by
            rw [intervalIntegral_indicator_Icc_nested hleft hle hright]
      simp only
      rw [hinnerSame, hinnerOpposite]
      by_cases hmem : theta ∈ Icc left right <;>
        simp [indicator_of_mem, indicator_of_notMem, hmem]
      ring
    _ = ∫ theta : ℝ in left..right,
        B theta *
          ((∫ phi : ℝ in left..right,
              A phi * circleLogDeficitAt (theta : AngleCircle)
                (phi : AngleCircle)) +
            ∫ phi : ℝ in left..right,
              A phi * circleLogDeficitAt
                ((-theta : ℝ) : AngleCircle)
                (phi : AngleCircle)) := by
      exact intervalIntegral_indicator_Icc_nested hleft hle hright

private theorem platformNormalizedAngularLogIntegral_eq
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi) :
    (∫ theta : ℝ in left..right,
        platformNormalizedAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta *
          ∫ phi : ℝ in left..right,
            platformNormalizedReferenceDensity k a phi *
              Real.log |platformAngularDistance a theta -
                platformAngularDistance a phi|) =
      platformReferenceCircleRadius k a left right *
        platformAdjointCircleRadius
          a xMinus xPlus sigmaMinus sigmaPlus left right *
        platformNormalizedCircleLogEnergy
          k a xMinus xPlus sigmaMinus sigmaPlus left right := by
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
  let C : ℝ := Real.log (platformCapacity a) + 2 * Real.log 2
  let DS : ℝ × ℝ → ℝ := fun p ↦
    B p.1 * A p.2 *
      circleLogDeficitAt (p.1 : AngleCircle) (p.2 : AngleCircle)
  let DO : ℝ × ℝ → ℝ := fun p ↦
    B p.1 * A p.2 *
      circleLogDeficitAt ((-p.1 : ℝ) : AngleCircle) (p.2 : AngleCircle)
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
  have hDSpull := integrable_positive_square_of_integrable_angleCircle
    hF hleft hlt.le hright
  have hDOpull := integrable_positive_square_of_integrable_angleCircle
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
      rw [circleIntervalRadialDensity_coe _ _ _ hp1,
        indicator_of_mem hpmem1]
    have hgcoe : g (p.2 : AngleCircle) = A p.2 := by
      dsimp only [g, A, platformReferenceCircleDensity]
      rw [circleIntervalRadialDensity_coe _ _ _ hp2,
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
      rw [circleIntervalRadialDensity_neg_coe _ _ _ hp1,
        indicator_of_mem hpmem1]
    have hgcoe : g (p.2 : AngleCircle) = A p.2 := by
      dsimp only [g, A, platformReferenceCircleDensity]
      rw [circleIntervalRadialDensity_coe _ _ _ hp2,
        indicator_of_mem hpmem2]
    dsimp only [F, DO]
    rw [hfcoe, hgcoe]
    simp only [AddCircle.coe_neg]
  have hsubset : Set.uIcc left right ⊆ Set.uIcc 0 Real.pi := by
    rw [uIcc_of_le hlt.le, uIcc_of_le Real.pi_pos.le]
    exact Icc_subset_Icc hleft hright
  have hA : Integrable A mu := by
    have hAinterval :=
      (intervalIntegrable_platformNormalizedReferenceDensity
        k ha ha2.le).mono_set hsubset
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le] at hAinterval
    simpa only [A, mu] using! hAinterval
  have hB : Integrable B mu := by
    have hBinterval :=
      (intervalIntegrable_platformNormalizedAdjointDensity
        (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
        hxMinus hxPlus ha2).mono_set hsubset
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le] at hBinterval
    simpa only [B, mu] using! hBinterval
  have hAB : Integrable (fun p : ℝ × ℝ ↦ B p.1 * A p.2)
      (mu.prod mu) := hB.mul_prod hA
  have hconstant : Integrable
      (fun p : ℝ × ℝ ↦ C * (B p.1 * A p.2))
      (mu.prod mu) := hAB.const_mul C
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
      fun p ↦ C * (B p.1 * A p.2) - DS p - DO p := by
    change L =ᵐ[
      (volume.restrict (Ioc left right)).prod
        (volume.restrict (Ioc left right))] _
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem
        (measurableSet_Ioc.prod measurableSet_Ioc),
      ae_restrict_of_ae hfstPi, ae_restrict_of_ae hsndPi,
      ae_restrict_of_ae hdiagonal] with p hp hfst h_snd hne
    have hp1 : p.1 ∈ Ioo (0 : ℝ) Real.pi := by
      exact ⟨hleft.trans_lt hp.1.1,
        lt_of_le_of_ne (hp.1.2.trans hright) hfst⟩
    have hp2 : p.2 ∈ Ioo (0 : ℝ) Real.pi := by
      exact ⟨hleft.trans_lt hp.2.1,
        lt_of_le_of_ne (hp.2.2.trans hright) h_snd⟩
    have hkernel :=
      log_abs_platformAngularDistance_sub_eq_circleDeficits
        ha2 hp1 hp2 hne
    dsimp only [L, C, DS, DO]
    rw [hkernel]
    ring
  have hL : Integrable L (mu.prod mu) :=
    ((hconstant.sub hDS).sub hDO).congr hpointwise.symm
  have hDSsection :
      (fun theta ↦ ∫ phi, DS (theta, phi) ∂mu) =ᵐ[mu]
        fun theta ↦ B theta * ∫ phi, A phi *
          circleLogDeficitAt (theta : AngleCircle) (phi : AngleCircle) ∂mu := by
    exact Filter.Eventually.of_forall fun theta ↦ by
      calc
        (∫ phi, DS (theta, phi) ∂mu) =
            ∫ phi, B theta *
              (A phi * circleLogDeficitAt
                (theta : AngleCircle) (phi : AngleCircle)) ∂mu := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun phi ↦ by
            dsimp only [DS]
            ring
        _ = B theta * ∫ phi, A phi *
              circleLogDeficitAt
                (theta : AngleCircle) (phi : AngleCircle) ∂mu := by
          rw [integral_const_mul]
  have hDOsection :
      (fun theta ↦ ∫ phi, DO (theta, phi) ∂mu) =ᵐ[mu]
        fun theta ↦ B theta * ∫ phi, A phi *
          circleLogDeficitAt ((-theta : ℝ) : AngleCircle)
            (phi : AngleCircle) ∂mu := by
    exact Filter.Eventually.of_forall fun theta ↦ by
      calc
        (∫ phi, DO (theta, phi) ∂mu) =
            ∫ phi, B theta *
              (A phi * circleLogDeficitAt
                ((-theta : ℝ) : AngleCircle) (phi : AngleCircle)) ∂mu := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun phi ↦ by
            dsimp only [DO]
            ring
        _ = B theta * ∫ phi, A phi *
              circleLogDeficitAt ((-theta : ℝ) : AngleCircle)
                (phi : AngleCircle) ∂mu := by
          rw [integral_const_mul]
  have hDSouter : Integrable
      (fun theta ↦ B theta * ∫ phi, A phi *
        circleLogDeficitAt (theta : AngleCircle) (phi : AngleCircle) ∂mu)
      mu := hDS.integral_prod_left.congr hDSsection
  have hDOouter : Integrable
      (fun theta ↦ B theta * ∫ phi, A phi *
        circleLogDeficitAt ((-theta : ℝ) : AngleCircle)
          (phi : AngleCircle) ∂mu)
      mu := hDO.integral_prod_left.congr hDOsection
  have hDSouterInterval : IntervalIntegrable
      (fun theta ↦ B theta * ∫ phi : ℝ in left..right,
        A phi * circleLogDeficitAt
          (theta : AngleCircle) (phi : AngleCircle))
      volume left right := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le]
    simpa only [mu, intervalIntegral.integral_of_le hlt.le] using! hDSouter
  have hDOouterInterval : IntervalIntegrable
      (fun theta ↦ B theta * ∫ phi : ℝ in left..right,
        A phi * circleLogDeficitAt
          ((-theta : ℝ) : AngleCircle) (phi : AngleCircle))
      volume left right := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le]
    simpa only [mu, intervalIntegral.integral_of_le hlt.le] using! hDOouter
  have hDSiter :
      (∫ theta : ℝ in left..right, B theta *
          ∫ phi : ℝ in left..right, A phi *
            circleLogDeficitAt
              (theta : AngleCircle) (phi : AngleCircle)) =
        ∫ p, DS p ∂(mu.prod mu) := by
    simp only [intervalIntegral.integral_of_le hlt.le]
    change (∫ theta, B theta * ∫ phi, A phi *
        circleLogDeficitAt
          (theta : AngleCircle) (phi : AngleCircle) ∂mu ∂mu) = _
    calc
      _ = ∫ theta, ∫ phi, DS (theta, phi) ∂mu ∂mu :=
        integral_congr_ae hDSsection.symm
      _ = _ := integral_integral hDS
  have hDOiter :
      (∫ theta : ℝ in left..right, B theta *
          ∫ phi : ℝ in left..right, A phi *
            circleLogDeficitAt ((-theta : ℝ) : AngleCircle)
              (phi : AngleCircle)) =
        ∫ p, DO p ∂(mu.prod mu) := by
    simp only [intervalIntegral.integral_of_le hlt.le]
    change (∫ theta, B theta * ∫ phi, A phi *
        circleLogDeficitAt ((-theta : ℝ) : AngleCircle)
          (phi : AngleCircle) ∂mu ∂mu) = _
    calc
      _ = ∫ theta, ∫ phi, DO (theta, phi) ∂mu ∂mu :=
        integral_congr_ae hDOsection.symm
      _ = _ := integral_integral hDO
  have hdeficit := platformCircleDeficit_toReal_eq_reflectedInterval
    hk0 ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
    hleft hlt.le hright
  have hdeficitProducts :
      (circleDensityLogDeficit
        (platformReferenceCircleDensity k a left right)
        (platformAdjointCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right)).toReal =
        2 * ((∫ p, DS p ∂(mu.prod mu)) +
          ∫ p, DO p ∂(mu.prod mu)) := by
    calc
      _ = 2 * ∫ theta : ℝ in left..right, B theta *
            ((∫ phi : ℝ in left..right, A phi *
                circleLogDeficitAt
                  (theta : AngleCircle) (phi : AngleCircle)) +
              ∫ phi : ℝ in left..right, A phi *
                circleLogDeficitAt ((-theta : ℝ) : AngleCircle)
                  (phi : AngleCircle)) := by
        simpa only [A, B] using! hdeficit
      _ = 2 *
          ((∫ theta : ℝ in left..right, B theta *
              ∫ phi : ℝ in left..right, A phi *
                circleLogDeficitAt
                  (theta : AngleCircle) (phi : AngleCircle)) +
            ∫ theta : ℝ in left..right, B theta *
              ∫ phi : ℝ in left..right, A phi *
                circleLogDeficitAt ((-theta : ℝ) : AngleCircle)
                  (phi : AngleCircle)) := by
        congr 1
        rw [← intervalIntegral.integral_add
          hDSouterInterval hDOouterInterval]
        apply intervalIntegral.integral_congr
        intro theta _htheta
        ring
      _ = _ := by rw [hDSiter, hDOiter]
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
  have hLiterate :
      (∫ theta : ℝ in left..right, B theta *
          ∫ phi : ℝ in left..right, A phi *
            Real.log |platformAngularDistance a theta -
              platformAngularDistance a phi|) =
        ∫ p, L p ∂(mu.prod mu) := by
    simp only [intervalIntegral.integral_of_le hlt.le]
    change (∫ theta, B theta * ∫ phi, A phi *
        Real.log |platformAngularDistance a theta -
          platformAngularDistance a phi| ∂mu ∂mu) = _
    calc
      _ = ∫ theta, ∫ phi, L (theta, phi) ∂mu ∂mu :=
        integral_congr_ae hLsection.symm
      _ = _ := integral_integral hL
  have hLintegral :
      (∫ p, L p ∂(mu.prod mu)) =
        C * ((∫ theta, B theta ∂mu) * ∫ phi, A phi ∂mu) -
          (∫ p, DS p ∂(mu.prod mu)) -
          ∫ p, DO p ∂(mu.prod mu) := by
    calc
      _ = ∫ p, ((fun q : ℝ × ℝ ↦ C * (B q.1 * A q.2)) - DS - DO) p
            ∂(mu.prod mu) := integral_congr_ae hpointwise
      _ = (∫ p, ((fun q : ℝ × ℝ ↦ C * (B q.1 * A q.2)) - DS) p
              ∂(mu.prod mu)) - ∫ p, DO p ∂(mu.prod mu) :=
        integral_sub (hconstant.sub hDS) hDO
      _ = ((∫ p, C * (B p.1 * A p.2) ∂(mu.prod mu)) -
            ∫ p, DS p ∂(mu.prod mu)) -
            ∫ p, DO p ∂(mu.prod mu) := by
        apply congrArg (fun t ↦ t - ∫ p, DO p ∂(mu.prod mu))
        exact integral_sub hconstant hDS
      _ = _ := by rw [integral_const_mul, integral_prod_mul]
  have hAmass : (∫ phi, A phi ∂mu) =
      platformReferenceCircleRadius k a left right := by
    simp only [A, mu, platformReferenceCircleRadius,
      intervalIntegral.integral_of_le hlt.le]
  have hBmass : (∫ theta, B theta ∂mu) =
      platformAdjointCircleRadius
        a xMinus xPlus sigmaMinus sigmaPlus left right := by
    simp only [B, mu, platformAdjointCircleRadius,
      intervalIntegral.integral_of_le hlt.le]
  have hQ : 0 < platformReferenceCircleRadius k a left right :=
    platformReferenceCircleRadius_pos hk ha ha2 hthreshold
      hleft hlt hright
  have hR : 0 < platformAdjointCircleRadius
      a xMinus xPlus sigmaMinus sigmaPlus left right :=
    platformAdjointCircleRadius_pos hxMinus hxPlus
      hsigmaMinus hsigmaPlus ha2 hleft hlt hright
  change (∫ theta : ℝ in left..right, B theta *
      ∫ phi : ℝ in left..right, A phi *
        Real.log |platformAngularDistance a theta -
          platformAngularDistance a phi|) = _
  rw [hLiterate, hLintegral, hBmass, hAmass]
  unfold platformNormalizedCircleLogEnergy normalizedCircleLogEnergy
  dsimp only [C]
  rw [hdeficitProducts]
  field_simp [hQ.ne', hR.ne']
  ring

/-- Exact physical angular-integral form of the platform deficit block. -/
theorem platformDeficitBlockEnergy_eq_angularIntegral
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi) :
    platformDeficitBlockEnergy
        k a xMinus xPlus sigmaMinus sigmaPlus left right =
      (1 / Real.pi ^ 2) *
        ∫ theta : ℝ in left..right,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            ∫ phi : ℝ in left..right,
              platformAngularDensity k a phi *
                Real.log |platformAngularDistance a theta -
                  platformAngularDistance a phi| := by
  let A : ℝ → ℝ := platformNormalizedReferenceDensity k a
  let B : ℝ → ℝ := platformNormalizedAdjointDensity
    a xMinus xPlus sigmaMinus sigmaPlus
  let api : ℝ := platformAPi k a
  let bpi : ℝ := platformBPi
    a xMinus xPlus sigmaMinus sigmaPlus
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  have href (phi : ℝ) :
      platformAngularDensity k a phi = api * A phi := by
    dsimp only [api, A, platformNormalizedReferenceDensity]
    field_simp [(platformAPi_pos hk0 ha ha2.le).ne']
  have hadj (theta : ℝ) :
      platformAngularAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta = bpi * B theta := by
    dsimp only [bpi, B, platformNormalizedAdjointDensity]
    field_simp [(platformBPi_pos hxMinus hxPlus
      hsigmaMinus hsigmaPlus ha2).ne']
  have hraw :
      (∫ theta : ℝ in left..right,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            ∫ phi : ℝ in left..right,
              platformAngularDensity k a phi *
                Real.log |platformAngularDistance a theta -
                  platformAngularDistance a phi|) =
        api * bpi *
          ∫ theta : ℝ in left..right, B theta *
            ∫ phi : ℝ in left..right, A phi *
              Real.log |platformAngularDistance a theta -
                platformAngularDistance a phi| := by
    calc
      _ = ∫ theta : ℝ in left..right, (bpi * B theta) *
            (api * ∫ phi : ℝ in left..right, A phi *
              Real.log |platformAngularDistance a theta -
                platformAngularDistance a phi|) := by
        apply intervalIntegral.integral_congr
        intro theta _htheta
        simp only
        rw [hadj]
        congr 1
        calc
          (∫ phi : ℝ in left..right,
              platformAngularDensity k a phi *
                Real.log |platformAngularDistance a theta -
                  platformAngularDistance a phi|) =
              ∫ phi : ℝ in left..right, api *
                (A phi * Real.log |platformAngularDistance a theta -
                  platformAngularDistance a phi|) := by
            apply intervalIntegral.integral_congr
            intro phi _hphi
            simp only
            rw [href]
            ring
          _ = api * ∫ phi : ℝ in left..right, A phi *
                Real.log |platformAngularDistance a theta -
                  platformAngularDistance a phi| := by
            rw [intervalIntegral.integral_const_mul]
      _ = ∫ theta : ℝ in left..right, (api * bpi) *
            (B theta * ∫ phi : ℝ in left..right, A phi *
              Real.log |platformAngularDistance a theta -
                platformAngularDistance a phi|) := by
        apply intervalIntegral.integral_congr
        intro theta _htheta
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have hnormalized := platformNormalizedAngularLogIntegral_eq
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
    hleft hlt hright
  unfold platformDeficitBlockEnergy
  rw [platformReferenceIntervalMass_eq_endpoint_mul_radius hk0 ha ha2.le,
    platformAdjointIntervalMass_eq_endpoint_mul_radius
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2]
  change (api * platformReferenceCircleRadius k a left right /
        Real.pi) *
      (bpi * platformAdjointCircleRadius
        a xMinus xPlus sigmaMinus sigmaPlus left right / Real.pi) *
      platformNormalizedCircleLogEnergy
        k a xMinus xPlus sigmaMinus sigmaPlus left right = _
  rw [hraw, hnormalized]
  field_simp [Real.pi_ne_zero]

end

end Erdos1038
