/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCubeMoment

/-!
# Linear lower and constant upper bounds for a cube cutoff integral

These inequalities retain the exact first-moment coefficient. They
apply both to the original energy and to the inner face cutoff.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

theorem cutoffCubeIntegral_upper_constant {G Φ : ℝ → ℝ} {K α : ℝ}
    (hG : Continuous G) (hG0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G t)
    (hΦ : BoundedCutoff Φ K) (hupper : ∀ s : ℝ, 0 ≤ s → Φ s ≤ α) (j : ℕ) :
    cutoffCubeIntegral G Φ j 0 ≤ α * (∫ t in (0 : ℝ)..1, G t) ^ j := by
  have hI := cutoffCubeIntegrand_integrable hG hΦ j 0
  have hGi : Integrable G unitIntervalMeasure := hG.integrableOn_Icc
  have hprod := Integrable.fintype_prod (fun _ : Fin j => hGi)
  unfold cutoffCubeIntegral
  calc
    _ ≤ ∫ t : Fin j → ℝ, α * ∏ i, G (t i)
        ∂Measure.pi (fun _ : Fin j => unitIntervalMeasure) :=
      integral_mono_ae hI (hprod.const_mul α) (by
        filter_upwards [ae_unitCube j] with t ht
        have hp : 0 ≤ ∏ i, G (t i) := Finset.prod_nonneg (fun i _hi => hG0 _ (ht i))
        have hs : 0 ≤ ∑ i, t i := Finset.sum_nonneg (fun i _hi => (ht i).1)
        change (∏ i, G (t i)) * Φ (0 + ∑ i, t i) ≤ α * ∏ i, G (t i)
        rw [zero_add]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hupper _ hs) hp)
    _ = _ := by
      rw [integral_const_mul, integral_fintype_prod_eq_pow]
      simp only [Fintype.card_fin, unitIntervalMeasure_integral]

theorem cutoffCubeIntegral_lower_linear {G Φ : ℝ → ℝ} {K α β : ℝ}
    (hG : Continuous G) (hG0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G t)
    (hΦ : BoundedCutoff Φ K) (hlower : ∀ s : ℝ, 0 ≤ s → α - β * s ≤ Φ s) (j : ℕ) :
    α * (∫ t in (0 : ℝ)..1, G t) ^ j -
      β * (j : ℝ) * (∫ t in (0 : ℝ)..1, t * G t) * (∫ t in (0 : ℝ)..1, G t) ^ (j - 1) ≤
      cutoffCubeIntegral G Φ j 0 := by
  have hI := cutoffCubeIntegrand_integrable hG hΦ j 0
  have hGi : Integrable G unitIntervalMeasure := hG.integrableOn_Icc
  have hprod := Integrable.fintype_prod (fun _ : Fin j => hGi)
  have hmoment := tensorCoordinateSum_integrable hG j
  have h := integral_mono_ae ((hprod.const_mul α).sub (hmoment.const_mul β)) hI (by
    filter_upwards [ae_unitCube j] with t ht
    have hs : 0 ≤ ∑ i, t i := Finset.sum_nonneg (fun i _hi => (ht i).1)
    have hp : 0 ≤ ∏ i, G (t i) := Finset.prod_nonneg (fun i _hi => hG0 _ (ht i))
    change α * (∏ i, G (t i)) - β * ((∑ i, t i) * ∏ i, G (t i)) ≤
      (∏ i, G (t i)) * Φ (0 + ∑ i, t i)
    rw [zero_add]
    calc
      _ = (∏ i, G (t i)) * (α - β * ∑ i, t i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlower _ hs) hp)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hprod.const_mul α) (hmoment.const_mul β), integral_const_mul,
    integral_const_mul, integral_tensorCoordinateSum hG j, integral_fintype_prod_eq_pow,
    unitIntervalMeasure_integral] at h
  simpa only [cutoffCubeIntegral, Fintype.card_fin, mul_assoc] using h

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.cutoffCubeIntegral_lower_linear
