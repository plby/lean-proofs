import ErdosProblems.Erdos906.LogMoment
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ENNReal

namespace CofiniteDerivatives

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The normalized average of `Y` over one angular period. -/
noncomputable def circleLogAverage (Y : Ω → ℝ → ℝ) (ω : Ω) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi, Y ω θ

/-- Joint measurability makes the circle average measurable. -/
theorem measurable_circleLogAverage
    (Y : Ω → ℝ → ℝ) (hY : Measurable (Function.uncurry Y)) :
    Measurable (circleLogAverage Y) := by
  have hsection : StronglyMeasurable
      (fun ω ↦ ∫ θ : ℝ, Y ω θ ∂(volume.restrict (Ioc 0 (2 * Real.pi)))) :=
    hY.stronglyMeasurable.integral_prod_right
  have havg : circleLogAverage Y = fun ω ↦
      (2 * Real.pi)⁻¹ * ∫ θ : ℝ, Y ω θ ∂(volume.restrict (Ioc 0 (2 * Real.pi))) := by
    funext ω
    rw [circleLogAverage, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  rw [havg]
  exact hsection.measurable.const_mul _

/-- A pointwise exponential tail, uniformly in the angular parameter, gives an
exponential tail for the circle average. -/
theorem measure_event_le_two_mul_exp_neg_eighth_of_circleLogAverage
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ → ℝ)
    (E : Set Ω) (t : ℝ)
    (hY : Measurable (Function.uncurry Y))
    (hY_nonneg : ∀ ω θ, 0 ≤ Y ω θ)
    (hY_int : Integrable (Function.uncurry Y)
      (μ.prod (volume.restrict (Ioc 0 (2 * Real.pi)))))
    (hE : MeasurableSet E)
    (ht : 8 ≤ t)
    (hE_large : E ⊆ {ω | t ≤ circleLogAverage Y ω})
    (htail : ∀ θ s : ℝ, 0 ≤ s →
      μ {ω | s < Y ω θ} ≤ ENNReal.ofReal (Real.exp (-s / 2))) :
    μ E ≤ ENNReal.ofReal (2 * Real.exp (-t / 8)) := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  have hY_int_ν : Integrable (Function.uncurry Y) (μ.prod ν) := by
    simpa only [ν] using! hY_int
  let F : Ω → ℝ → ℝ := fun ω θ ↦ E.indicator (fun _ ↦ Y ω θ) ω
  have hF_int : Integrable (Function.uncurry F) (μ.prod ν) := by
    have hpre : MeasurableSet (Prod.fst ⁻¹' E : Set (Ω × ℝ)) :=
      hE.preimage measurable_fst
    have heq : Function.uncurry F =
        (Prod.fst ⁻¹' E).indicator (Function.uncurry Y) := by
      funext z
      by_cases hz : z.1 ∈ E <;> simp [F, Function.uncurry, hz]
    rw [heq]
    exact hY_int_ν.indicator hpre
  have hν_real : ν.real univ = 2 * Real.pi := by
    simp [ν, Real.volume_real_Ioc_of_le Real.two_pi_pos.le]
  have hν_ne : ν ≠ 0 := by
    intro hν
    have : ν.real univ = 0 := by rw [hν]; simp
    rw [hν_real] at this
    exact (ne_of_gt Real.two_pi_pos) this
  let g : ℝ → ℝ := fun θ ↦ ∫ ω : Ω in E, Y ω θ ∂μ
  have hg_int : Integrable g ν := by
    have hinner : Integrable (fun θ ↦ ∫ ω : Ω, F ω θ ∂μ) ν := by
      simpa only [Function.uncurry_apply_pair] using! hF_int.integral_prod_right
    have heq : (fun θ ↦ ∫ ω : Ω, F ω θ ∂μ) = g := by
      funext θ
      change (∫ ω : Ω, E.indicator (fun ω ↦ Y ω θ) ω ∂μ) =
        ∫ ω : Ω in E, Y ω θ ∂μ
      exact integral_indicator hE
    rw [← heq]
    exact hinner
  have hswap :
      (∫ ω : Ω in E, ∫ θ : ℝ, Y ω θ ∂ν ∂μ) = ∫ θ : ℝ, g θ ∂ν := by
    calc
      (∫ ω : Ω in E, ∫ θ : ℝ, Y ω θ ∂ν ∂μ) =
          ∫ ω : Ω, ∫ θ : ℝ, F ω θ ∂ν ∂μ := by
        simpa only [F] using! (integral_integral_indicator Y hE).symm
      _ = ∫ θ : ℝ, ∫ ω : Ω, F ω θ ∂μ ∂ν :=
        integral_integral_swap hF_int
      _ = ∫ θ : ℝ, g θ ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with θ
        change (∫ ω : Ω, E.indicator (fun ω ↦ Y ω θ) ω ∂μ) =
          ∫ ω : Ω in E, Y ω θ ∂μ
        exact integral_indicator hE
  have hset_average :
      (∫ ω : Ω in E, circleLogAverage Y ω ∂μ) = ⨍ θ : ℝ, g θ ∂ν := by
    calc
      (∫ ω : Ω in E, circleLogAverage Y ω ∂μ) =
          (2 * Real.pi)⁻¹ * ∫ ω : Ω in E, ∫ θ : ℝ, Y ω θ ∂ν ∂μ := by
        simp only [circleLogAverage, ν,
          intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_const_mul]
      _ = (2 * Real.pi)⁻¹ * ∫ θ : ℝ, g θ ∂ν := by rw [hswap]
      _ = ⨍ θ : ℝ, g θ ∂ν := by
        rw [average_eq, hν_real, smul_eq_mul]
  have hA_int : Integrable (circleLogAverage Y) μ := by
    have hinner : Integrable (fun ω ↦ ∫ θ : ℝ, Y ω θ ∂ν) μ := by
      simpa only [Function.uncurry_apply_pair] using! hY_int_ν.integral_prod_left
    have heq : circleLogAverage Y = fun ω ↦
        (2 * Real.pi)⁻¹ * ∫ θ : ℝ, Y ω θ ∂ν := by
      funext ω
      rw [circleLogAverage, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    rw [heq]
    exact hinner.const_mul _
  have hE_moment : t * μ.real E ≤ ∫ ω : Ω in E, circleLogAverage Y ω ∂μ :=
    setIntegral_ge_of_const_le_real hE (measure_ne_top μ E)
      (fun ω hω ↦ hE_large hω) hA_int.integrableOn
  have hsections_ae : ∀ᵐ θ ∂ν, Integrable (fun ω ↦ F ω θ) μ := by
    simpa only [Function.uncurry_apply_pair] using! hF_int.prod_left_ae
  have hbad : ν {θ | ¬Integrable (fun ω ↦ F ω θ) μ} = 0 :=
    ae_iff.mp hsections_ae
  obtain ⟨θ, hθ_good, hθ_large⟩ :=
    exists_notMem_null_average_le hν_ne hg_int hbad
  have hFθ_int : Integrable (fun ω ↦ F ω θ) μ := by
    simpa only [mem_ofPred_eq, not_not] using! hθ_good
  have hYθ_int : IntegrableOn (fun ω ↦ Y ω θ) E μ := by
    apply (integrable_indicator_iff hE).mp
    simpa only [F] using! hFθ_int
  have hreal_moment : t * μ.real E ≤ ∫ ω : Ω in E, Y ω θ ∂μ := by
    calc
      t * μ.real E ≤ ∫ ω : Ω in E, circleLogAverage Y ω ∂μ := hE_moment
      _ = ⨍ θ : ℝ, g θ ∂ν := hset_average
      _ ≤ g θ := hθ_large
      _ = ∫ ω : Ω in E, Y ω θ ∂μ := rfl
  have ht_nonneg : 0 ≤ t := by linarith
  have hmoment : ENNReal.ofReal t * μ E ≤
      ∫⁻ ω : Ω in E, ENNReal.ofReal (Y ω θ) ∂μ := by
    calc
      ENNReal.ofReal t * μ E = ENNReal.ofReal (t * μ.real E) := by
        rw [ENNReal.ofReal_mul ht_nonneg, ofReal_measureReal]
      _ ≤ ENNReal.ofReal (∫ ω : Ω in E, Y ω θ ∂μ) :=
        ENNReal.ofReal_le_ofReal hreal_moment
      _ = ∫⁻ ω : Ω in E, ENNReal.ofReal (Y ω θ) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hYθ_int
          (Filter.Eventually.of_forall fun ω ↦ hY_nonneg ω θ)
  have hstrong : μ E ≤ ENNReal.ofReal (2 * Real.exp (-t / 4)) :=
    measure_event_le_two_mul_exp_neg_quarter_of_le_logMoment μ (fun ω ↦ Y ω θ) E t
      (hY.comp measurable_prodMk_right) (fun ω ↦ hY_nonneg ω θ) hE (by linarith)
      (htail θ) hmoment
  calc
    μ E ≤ ENNReal.ofReal (2 * Real.exp (-t / 4)) := hstrong
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t / 8)) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left (Real.exp_monotone (by linarith)) (by norm_num)

end CofiniteDerivatives
