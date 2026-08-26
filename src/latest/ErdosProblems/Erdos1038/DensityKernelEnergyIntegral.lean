import ErdosProblems.Erdos1038.CircleDensityLayerCake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Real-integral form of a nonnegative density-kernel energy

The rearrangement layer uses `ℝ≥0∞` lower integrals.  This file records the
exact conversion back to the ordinary product integral when the densities
and kernel are real and nonnegative.  It is the measure-theoretic bridge
needed to identify the platform circle deficit with the mixed logarithmic
block energy in the manuscript.
-/

set_option warningAsError false

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1038

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The `toReal` of a nonnegative density-kernel energy is its ordinary
real product integral.  No separate integrability assumption is needed:
both sides use the standard value zero in the infinite nonintegrable case.
-/
theorem densityKernelEnergy_toReal_eq_integral_prod
    (mu : Measure X) (nu : Measure Y) [SFinite mu] [SFinite nu]
    {f : X → ℝ} {g : Y → ℝ} {kernel : X → Y → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hkernel : Measurable (Function.uncurry kernel))
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y)
    (hkernel0 : ∀ x y, 0 ≤ kernel x y) :
    (densityKernelEnergy mu nu f g
        (fun x y ↦ ENNReal.ofReal (kernel x y))).toReal =
      ∫ p : X × Y,
        f p.1 * g p.2 * kernel p.1 p.2 ∂(mu.prod nu) := by
  let integrand : X × Y → ℝ≥0∞ := fun p ↦
    ENNReal.ofReal (f p.1) * ENNReal.ofReal (g p.2) *
      ENNReal.ofReal (kernel p.1 p.2)
  have hintegrand : Measurable integrand := by
    exact ((hf.comp measurable_fst).ennreal_ofReal.mul
      (hg.comp measurable_snd).ennreal_ofReal).mul hkernel.ennreal_ofReal
  have henergy :
      densityKernelEnergy mu nu f g
          (fun x y ↦ ENNReal.ofReal (kernel x y)) =
        ∫⁻ p : X × Y, integrand p ∂(mu.prod nu) := by
    unfold densityKernelEnergy
    rw [lintegral_prod _ hintegrand.aemeasurable]
  rw [henergy]
  calc
    (∫⁻ p : X × Y, integrand p ∂(mu.prod nu)).toReal =
        ∫ p : X × Y, (integrand p).toReal ∂(mu.prod nu) := by
      symm
      apply integral_toReal hintegrand.aemeasurable
      exact Filter.Eventually.of_forall fun p ↦ by
        simp only [integrand]
        exact ENNReal.mul_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top
    _ = ∫ p : X × Y,
          f p.1 * g p.2 * kernel p.1 p.2 ∂(mu.prod nu) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p ↦ by
        simp only [integrand, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
          hf0 p.1, hg0 p.2, hkernel0 p.1 p.2]

/-- Finiteness of the lower-integral energy gives integrability of the
corresponding real product integrand. -/
theorem integrable_densityKernelProduct_of_ne_top
    (mu : Measure X) (nu : Measure Y) [SFinite mu] [SFinite nu]
    {f : X → ℝ} {g : Y → ℝ} {kernel : X → Y → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hkernel : Measurable (Function.uncurry kernel))
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y)
    (hkernel0 : ∀ x y, 0 ≤ kernel x y)
    (hfinite : densityKernelEnergy mu nu f g
      (fun x y ↦ ENNReal.ofReal (kernel x y)) ≠ ∞) :
    Integrable (fun p : X × Y ↦
      f p.1 * g p.2 * kernel p.1 p.2) (mu.prod nu) := by
  let realIntegrand : X × Y → ℝ := fun p ↦
    f p.1 * g p.2 * kernel p.1 p.2
  have hmeas : Measurable realIntegrand :=
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).mul hkernel
  have hnonneg : ∀ p, 0 ≤ realIntegrand p := fun p ↦
    mul_nonneg (mul_nonneg (hf0 p.1) (hg0 p.2))
      (hkernel0 p.1 p.2)
  apply (lintegral_ofReal_ne_top_iff_integrable
    hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hnonneg)).mp
  have hproduct :
      (∫⁻ p : X × Y, ENNReal.ofReal (realIntegrand p) ∂(mu.prod nu)) =
        densityKernelEnergy mu nu f g
          (fun x y ↦ ENNReal.ofReal (kernel x y)) := by
    unfold densityKernelEnergy
    let ennIntegrand : X × Y → ℝ≥0∞ := fun p ↦
      ENNReal.ofReal (f p.1) * ENNReal.ofReal (g p.2) *
        ENNReal.ofReal (kernel p.1 p.2)
    have hennMeas : Measurable ennIntegrand := by
      exact ((hf.comp measurable_fst).ennreal_ofReal.mul
        (hg.comp measurable_snd).ennreal_ofReal).mul
          hkernel.ennreal_ofReal
    calc
      (∫⁻ p : X × Y,
          ENNReal.ofReal (realIntegrand p) ∂(mu.prod nu)) =
          ∫⁻ p : X × Y, ennIntegrand p ∂(mu.prod nu) := by
        apply lintegral_congr
        intro p
        simp only [realIntegrand, ennIntegrand,
          ENNReal.ofReal_mul (hf0 p.1),
          ENNReal.ofReal_mul (mul_nonneg (hf0 p.1) (hg0 p.2))]
      _ = ∫⁻ x : X, ∫⁻ y : Y,
          ENNReal.ofReal (f x) * ENNReal.ofReal (g y) *
            ENNReal.ofReal (kernel x y) ∂nu ∂mu := by
        rw [lintegral_prod _ hennMeas.aemeasurable]
  rw [hproduct]
  exact hfinite

local notation "AngleCircle" => AddCircle (2 * Real.pi)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Fubini together with the canonical `[-π,π]` representative of
the additive circle. -/
theorem integral_angleCircle_prod_eq_interval
    (F : AngleCircle × AngleCircle → ℝ)
    (hF : Integrable F (volume.prod volume)) :
    (∫ p : AngleCircle × AngleCircle, F p ∂(volume.prod volume)) =
      ∫ theta : ℝ in -Real.pi..Real.pi,
        ∫ phi : ℝ in -Real.pi..Real.pi,
          F ((theta : AngleCircle), (phi : AngleCircle)) := by
  rw [integral_prod F hF]
  rw [← AddCircle.intervalIntegral_preimage
    (2 * Real.pi) (-Real.pi)
      (fun x : AngleCircle ↦ ∫ y : AngleCircle, F (x, y))]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  apply intervalIntegral.integral_congr
  intro theta _htheta
  change (∫ y : AngleCircle, F ((theta : AngleCircle), y)) =
    ∫ phi : ℝ in -Real.pi..Real.pi,
      F ((theta : AngleCircle), (phi : AngleCircle))
  rw [← AddCircle.intervalIntegral_preimage
    (2 * Real.pi) (-Real.pi) (fun y : AngleCircle ↦
      F ((theta : AngleCircle), y))]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]

/-- An integrable circle function is interval integrable on the canonical
real representative. -/
theorem Integrable.angleCircle_intervalIntegrable
    {F : AngleCircle → ℝ} (hF : Integrable F volume) :
    IntervalIntegrable (fun theta : ℝ ↦ F (theta : AngleCircle))
      volume (-Real.pi) Real.pi := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by linarith [Real.pi_pos])]
  have hcomp : Integrable (fun theta : ℝ ↦ F (theta : AngleCircle))
      (volume.restrict
        (Ioc (-Real.pi) (-Real.pi + 2 * Real.pi))) :=
    ((AddCircle.measurePreserving_mk
      (2 * Real.pi) (-Real.pi)).integrable_comp
        hF.aestronglyMeasurable).mpr hF
  simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using! hcomp

/-- Split the canonical circle interval into its positive and negative
halves, reflecting the negative half to `[0,π]`. -/
theorem intervalIntegral_neg_pi_pi_eq_pos_add_reflection
    {F : ℝ → ℝ}
    (hF : IntervalIntegrable F volume (-Real.pi) Real.pi) :
    (∫ theta : ℝ in -Real.pi..Real.pi, F theta) =
      (∫ theta : ℝ in 0..Real.pi, F theta) +
        ∫ theta : ℝ in 0..Real.pi, F (-theta) := by
  have hneg : IntervalIntegrable F volume (-Real.pi) 0 :=
    hF.mono_set (by
      rw [uIcc_of_le (by linarith [Real.pi_pos]),
        uIcc_of_le (by linarith [Real.pi_pos])]
      exact Icc_subset_Icc le_rfl Real.pi_pos.le)
  have hpos : IntervalIntegrable F volume 0 Real.pi :=
    hF.mono_set (by
      rw [uIcc_of_le Real.pi_pos.le,
        uIcc_of_le (by linarith [Real.pi_pos])]
      exact Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hneg hpos]
  rw [intervalIntegral.integral_comp_neg]
  abel

/-- An integrable product on the circle is twice the sum of its same-sign
and opposite-sign contributions on the positive angular quadrant, provided
it has the two reflection symmetries used by the logarithmic deficit. -/
def angleCirclePositiveReflectionIntegral
    (F : AngleCircle × AngleCircle → ℝ) : ℝ :=
  ∫ theta : ℝ in 0..Real.pi,
    ((∫ phi : ℝ in 0..Real.pi,
        F ((theta : AngleCircle), (phi : AngleCircle))) +
      ∫ phi : ℝ in 0..Real.pi,
        F (((-theta : ℝ) : AngleCircle), (phi : AngleCircle)))

theorem integral_angleCircle_prod_eq_two_mul_positive_reflections
    (F : AngleCircle × AngleCircle → ℝ)
    (hF : Integrable F (volume.prod volume))
    (hsame : ∀ theta phi : ℝ,
      F (((-theta : ℝ) : AngleCircle), ((-phi : ℝ) : AngleCircle)) =
        F ((theta : AngleCircle), (phi : AngleCircle)))
    (hopposite : ∀ theta phi : ℝ,
      F ((theta : AngleCircle), ((-phi : ℝ) : AngleCircle)) =
        F (((-theta : ℝ) : AngleCircle), (phi : AngleCircle))) :
    (∫ p : AngleCircle × AngleCircle, F p ∂(volume.prod volume)) =
      2 * angleCirclePositiveReflectionIntegral F := by
  have hsectionsCircle : ∀ᵐ x : AngleCircle ∂(volume : Measure AngleCircle),
      Integrable (fun y : AngleCircle ↦ F (x, y)) volume :=
    hF.prod_right_ae
  have hsectionsPositiveFundamental :
      ∀ᵐ theta : ℝ ∂((volume : Measure ℝ).restrict
        (Ioc (0 : ℝ) (2 * Real.pi))),
        Integrable (fun y : AngleCircle ↦
          F ((theta : AngleCircle), y)) (volume : Measure AngleCircle) := by
    have h := (AddCircle.measurePreserving_mk
      (2 * Real.pi) 0).quasiMeasurePreserving.ae
        hsectionsCircle
    simpa only [zero_add] using! h
  have hsectionsPositive :
      ∀ᵐ theta : ℝ ∂((volume : Measure ℝ).restrict
        (Ioc (0 : ℝ) Real.pi)),
        Integrable (fun y : AngleCircle ↦
          F ((theta : AngleCircle), y)) (volume : Measure AngleCircle) := by
    exact ae_restrict_of_ae_restrict_of_subset (by
      intro theta htheta
      exact ⟨htheta.1, by linarith [htheta.2, Real.pi_pos]⟩)
        hsectionsPositiveFundamental
  have hsectionsNegativeFundamental :
      ∀ᵐ theta : ℝ ∂((volume : Measure ℝ).restrict
        (Ioc (-2 * Real.pi) 0)),
        Integrable (fun y : AngleCircle ↦
          F ((theta : AngleCircle), y)) (volume : Measure AngleCircle) := by
    have h := (AddCircle.measurePreserving_mk
      (2 * Real.pi) (-2 * Real.pi)).quasiMeasurePreserving.ae
        hsectionsCircle
    simpa only [show -2 * Real.pi + 2 * Real.pi = 0 by ring] using! h
  have hnegMaps : MapsTo (fun theta : ℝ ↦ -theta)
      (Ioc (0 : ℝ) Real.pi) (Ioc (-2 * Real.pi) 0) := by
    intro theta htheta
    exact ⟨by linarith [htheta.2, Real.pi_pos], by linarith [htheta.1]⟩
  have hsectionsNegative :
      ∀ᵐ theta : ℝ ∂((volume : Measure ℝ).restrict
        (Ioc (0 : ℝ) Real.pi)),
        Integrable (fun y : AngleCircle ↦
          F (((-theta : ℝ) : AngleCircle), y))
            (volume : Measure AngleCircle) := by
    exact ((Measure.measurePreserving_neg
      (volume : Measure ℝ)).quasiMeasurePreserving.restrict
        hnegMaps).ae hsectionsNegativeFundamental
  have hsplitSection (theta : ℝ)
      (hsection : Integrable (fun y : AngleCircle ↦
        F ((theta : AngleCircle), y)) (volume : Measure AngleCircle)) :
      (∫ y : AngleCircle, F ((theta : AngleCircle), y)) =
        (∫ phi : ℝ in 0..Real.pi,
          F ((theta : AngleCircle), (phi : AngleCircle))) +
        ∫ phi : ℝ in 0..Real.pi,
          F ((theta : AngleCircle), ((-phi : ℝ) : AngleCircle)) := by
    rw [← AddCircle.intervalIntegral_preimage
      (2 * Real.pi) (-Real.pi) (fun y : AngleCircle ↦
        F ((theta : AngleCircle), y))]
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
    exact intervalIntegral_neg_pi_pi_eq_pos_add_reflection
      (Integrable.angleCircle_intervalIntegrable hsection)
  have houter : Integrable
      (fun x : AngleCircle ↦ ∫ y : AngleCircle, F (x, y))
        (volume : Measure AngleCircle) :=
    hF.integral_prod_left
  have hfirst :
      (∫ theta : ℝ in 0..Real.pi,
          ∫ y : AngleCircle, F ((theta : AngleCircle), y)) =
        ∫ theta : ℝ in 0..Real.pi,
          ((∫ phi : ℝ in 0..Real.pi,
              F ((theta : AngleCircle), (phi : AngleCircle))) +
            ∫ phi : ℝ in 0..Real.pi,
              F (((-theta : ℝ) : AngleCircle),
                (phi : AngleCircle))) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have hsectionsPositive' :
        ∀ᵐ theta : ℝ ∂(volume : Measure ℝ).restrict
          (uIoc (0 : ℝ) Real.pi),
          Integrable (fun y : AngleCircle ↦
            F ((theta : AngleCircle), y)) (volume : Measure AngleCircle) := by
      simpa only [uIoc_of_le Real.pi_pos.le] using! hsectionsPositive
    filter_upwards [hsectionsPositive'] with theta htheta
    rw [hsplitSection theta htheta]
    congr 1
    apply intervalIntegral.integral_congr
    intro phi _hphi
    exact hopposite theta phi
  have hsecond :
      (∫ theta : ℝ in 0..Real.pi,
          ∫ y : AngleCircle,
            F (((-theta : ℝ) : AngleCircle), y)) =
        ∫ theta : ℝ in 0..Real.pi,
          ((∫ phi : ℝ in 0..Real.pi,
              F ((theta : AngleCircle), (phi : AngleCircle))) +
            ∫ phi : ℝ in 0..Real.pi,
              F (((-theta : ℝ) : AngleCircle),
                (phi : AngleCircle))) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have hsectionsNegative' :
        ∀ᵐ theta : ℝ ∂(volume : Measure ℝ).restrict
          (uIoc (0 : ℝ) Real.pi),
          Integrable (fun y : AngleCircle ↦
            F (((-theta : ℝ) : AngleCircle), y))
              (volume : Measure AngleCircle) := by
      simpa only [uIoc_of_le Real.pi_pos.le] using! hsectionsNegative
    filter_upwards [hsectionsNegative'] with theta htheta
    have hsplit := hsplitSection (-theta) htheta
    rw [hsplit]
    have hsameIntegral :
        (∫ phi : ℝ in 0..Real.pi,
            F (((-theta : ℝ) : AngleCircle),
              ((-phi : ℝ) : AngleCircle))) =
          ∫ phi : ℝ in 0..Real.pi,
            F ((theta : AngleCircle), (phi : AngleCircle)) := by
      apply intervalIntegral.integral_congr
      intro phi _hphi
      exact hsame theta phi
    rw [hsameIntegral]
    abel
  calc
    (∫ p : AngleCircle × AngleCircle, F p ∂(volume.prod volume)) =
        ∫ x : AngleCircle, ∫ y : AngleCircle, F (x, y) :=
      integral_prod F hF
    _ = ∫ theta : ℝ in -Real.pi..Real.pi,
          ∫ y : AngleCircle, F ((theta : AngleCircle), y) := by
      rw [← AddCircle.intervalIntegral_preimage
        (2 * Real.pi) (-Real.pi)
          (fun x : AngleCircle ↦ ∫ y : AngleCircle, F (x, y))]
      rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
    _ = (∫ theta : ℝ in 0..Real.pi,
          ∫ y : AngleCircle, F ((theta : AngleCircle), y)) +
        ∫ theta : ℝ in 0..Real.pi,
          ∫ y : AngleCircle,
            F (((-theta : ℝ) : AngleCircle), y) := by
      exact intervalIntegral_neg_pi_pi_eq_pos_add_reflection
        (Integrable.angleCircle_intervalIntegrable houter)
    _ = 2 * angleCirclePositiveReflectionIntegral F := by
      unfold angleCirclePositiveReflectionIntegral
      rw [hfirst, hsecond]
      ring

/-- Real product-integral form of the mixed circle logarithmic deficit. -/
theorem circleDensityLogDeficit_toReal_eq_integral_prod
    {f g : AngleCircle → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y) :
    (circleDensityLogDeficit f g).toReal =
      ∫ p : AngleCircle × AngleCircle,
        f p.1 * g p.2 * circleLogDeficitAt p.1 p.2
          ∂(volume.prod volume) := by
  unfold circleDensityLogDeficit
  apply densityKernelEnergy_toReal_eq_integral_prod volume volume
    hf hg
  · unfold circleLogDeficitAt
    fun_prop
  · exact hf0
  · exact hg0
  · exact circleLogDeficitAt_nonneg

/-- Integrability of the real mixed circle deficit follows from finiteness
of its `ℝ≥0∞` energy. -/
theorem integrable_circleDensityLogDeficit_product_of_ne_top
    {f g : AngleCircle → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y)
    (hfinite : circleDensityLogDeficit f g ≠ ∞) :
    Integrable (fun p : AngleCircle × AngleCircle ↦
      f p.1 * g p.2 * circleLogDeficitAt p.1 p.2)
        (volume.prod volume) := by
  unfold circleDensityLogDeficit at hfinite
  apply integrable_densityKernelProduct_of_ne_top volume volume
    hf hg _ hf0 hg0 circleLogDeficitAt_nonneg hfinite
  unfold circleLogDeficitAt
  fun_prop

end

end Erdos1038
