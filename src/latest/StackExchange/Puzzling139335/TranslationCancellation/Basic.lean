import StackExchange.Puzzling139335.WeightedMass.Isometry
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Cancellation of nonzero translations on integrable functions

A finite measure invariant under a nonzero Euclidean translation must vanish:
Poincaré recurrence would force a translated point to return to a ball smaller
than its first displacement. Applying this to the finite measure with density
`‖f‖` proves the actual `L¹` cancellation statement, with no bounded-support
assumption and no pointwise representative chosen for an almost-everywhere
identity.
-/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Puzzling139335

section WithDensity

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {g : X → X}

/-- An almost-everywhere invariant density induces an invariant measure. -/
theorem measurePreserving_withDensity_of_ae_invariant
    (hg : MeasurePreserving g μ μ) (hge : MeasurableEmbedding g)
    (ρ : X → ℝ≥0∞) (hinv : (fun x => ρ (g x)) =ᵐ[μ] ρ) :
    MeasurePreserving g (μ.withDensity ρ) (μ.withDensity ρ) := by
  refine ⟨hg.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hg.measurable hs,
    withDensity_apply _ (hg.measurable hs), withDensity_apply _ hs]
  calc
    ∫⁻ x in g ⁻¹' s, ρ x ∂μ = ∫⁻ x in g ⁻¹' s, ρ (g x) ∂μ :=
      lintegral_congr_ae (ae_restrict_of_ae hinv.symm)
    _ = ∫⁻ x in s, ρ x ∂μ := hg.setLIntegral_comp_preimage_emb hge ρ s

end WithDensity

/-- A nonzero translation cannot preserve a nonzero finite measure on the
Euclidean plane. -/
theorem finite_measure_eq_zero_of_measurePreserving_add
    (μ : Measure Plane) [IsFiniteMeasure μ] {v : Plane} (hv : v ≠ 0)
    (htrans : MeasurePreserving (fun x : Plane => x + v) μ μ) : μ = 0 := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hfalse : ∀ᵐ x ∂μ, False := by
    filter_upwards [htrans.conservative.ae_frequently_mem_of_mem_nhds] with x hx
    have hreturn := hx (Metric.ball x ‖v‖) (Metric.ball_mem_nhds x hvpos)
    obtain ⟨n, hn, hnball⟩ := frequently_atTop.mp hreturn 1
    have hdist := Metric.mem_ball.mp hnball
    rw [add_right_iterate_apply, dist_eq_norm, add_sub_cancel_left,
      RCLike.norm_nsmul (K := ℝ), nsmul_eq_mul] at hdist
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  apply Measure.measure_univ_eq_zero.mp
  simpa only [ae_iff, not_false_eq_true, ofPred_true] using hfalse

/-- An integrable real function invariant almost everywhere under a nonzero
translation is zero almost everywhere. -/
theorem integrable_eq_zero_of_ae_add_invariant {f : Plane → ℝ} {v : Plane}
    (hv : v ≠ 0) (hf : Integrable f volume)
    (hinv : (fun x => f (x + v)) =ᵐ[volume] f) : f =ᵐ[volume] 0 := by
  let ρ : Plane → ℝ≥0∞ := fun x => ‖f x‖ₑ
  let ν : Measure Plane := volume.withDensity ρ
  have hρ : AEMeasurable ρ volume := hf.aestronglyMeasurable.enorm
  have hρinv : (fun x => ρ (x + v)) =ᵐ[volume] ρ := by
    filter_upwards [hinv] with x hx
    simp only [ρ, hx]
  have : IsFiniteMeasure ν :=
    isFiniteMeasure_withDensity (hasFiniteIntegral_iff_enorm.mp hf.hasFiniteIntegral).ne
  have htrans : MeasurePreserving (fun x : Plane => x + v) ν ν :=
    measurePreserving_withDensity_of_ae_invariant (measurePreserving_add_right volume v)
      (Homeomorph.addRight v).toMeasurableEquiv.measurableEmbedding ρ hρinv
  have hν : ν = 0 := finite_measure_eq_zero_of_measurePreserving_add ν hv htrans
  have hρzero : ρ =ᵐ[volume] 0 := (withDensity_eq_zero_iff hρ).mp hν
  filter_upwards [hρzero] with x hx
  simpa only [ρ, Pi.zero_apply, enorm_eq_zero] using hx

end Puzzling139335
