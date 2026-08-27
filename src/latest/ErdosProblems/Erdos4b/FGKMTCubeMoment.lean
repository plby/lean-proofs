/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCutoffIntegral

/-!
# The first moment of a product density on the unit cube

This generalizes the coordinate-product calculation used by the older
fixed-profile proof. Here the one-variable factor is arbitrary, so it
can be the new smoothly truncated rational factor.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

def coordinateProfileFactor {j : ℕ} (G : ℝ → ℝ) (i q : Fin j) (t : ℝ) : ℝ :=
  if q = i then t * G t else G t

theorem coordinateProfileFactor_prod {j : ℕ} (G : ℝ → ℝ) (i : Fin j) (t : Fin j → ℝ) :
    (∏ q, coordinateProfileFactor G i q (t q)) = t i * ∏ q, G (t q) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ
    (fun q => coordinateProfileFactor G i q (t q)) (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase Finset.univ (fun q => G (t q)) (Finset.mem_univ i)]
  have hrest : (∏ q ∈ Finset.univ.erase i, coordinateProfileFactor G i q (t q)) =
      ∏ q ∈ Finset.univ.erase i, G (t q) := by
    apply Finset.prod_congr rfl
    intro q hq
    exact if_neg (Finset.mem_erase.mp hq).1
  rw [hrest]
  simp [coordinateProfileFactor, mul_assoc]

theorem tensorCoordinate_integrable {G : ℝ → ℝ} (hG : Continuous G) {j : ℕ} (i : Fin j) :
    Integrable (fun t : Fin j → ℝ => t i * ∏ q, G (t q))
      (Measure.pi (fun _ : Fin j => unitIntervalMeasure)) := by
  have hf : ∀ q : Fin j, Integrable (coordinateProfileFactor G i q) unitIntervalMeasure := by
    intro q
    change IntegrableOn (coordinateProfileFactor G i q) (Set.Icc (0 : ℝ) 1)
    by_cases hq : q = i
    · have heq : coordinateProfileFactor G i q = fun t => t * G t := by
        funext t
        exact if_pos hq
      rw [heq]
      exact (continuous_id.mul hG).integrableOn_Icc
    · have heq : coordinateProfileFactor G i q = G := by
        funext t
        exact if_neg hq
      rw [heq]
      exact hG.integrableOn_Icc
  simpa only [coordinateProfileFactor_prod] using Integrable.fintype_prod hf

theorem integral_tensorCoordinate {j : ℕ} (G : ℝ → ℝ) (i : Fin j) :
    (∫ t : Fin j → ℝ, t i * ∏ q, G (t q)
      ∂Measure.pi (fun _ : Fin j => unitIntervalMeasure)) =
      (∫ t in (0 : ℝ)..1, t * G t) * (∫ t in (0 : ℝ)..1, G t) ^ (j - 1) := by
  classical
  calc
    _ = ∫ t : Fin j → ℝ, ∏ q, coordinateProfileFactor G i q (t q)
        ∂Measure.pi (fun _ : Fin j => unitIntervalMeasure) :=
      integral_congr_ae (Eventually.of_forall (fun t => (coordinateProfileFactor_prod G i t).symm))
    _ = ∏ q : Fin j, ∫ t, coordinateProfileFactor G i q t ∂unitIntervalMeasure :=
      integral_fintype_prod_eq_prod _
    _ = _ := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun q : Fin j => ∫ t, coordinateProfileFactor G i q t ∂unitIntervalMeasure)
        (Finset.mem_univ i)]
      have hi : (∫ t, coordinateProfileFactor G i i t ∂unitIntervalMeasure) =
          ∫ t in (0 : ℝ)..1, t * G t := by
        simp [coordinateProfileFactor, unitIntervalMeasure_integral]
      rw [hi]
      congr 1
      calc
        _ = ∏ _q ∈ Finset.univ.erase i, (∫ t in (0 : ℝ)..1, G t) := by
          apply Finset.prod_congr rfl
          intro q hq
          simp only [coordinateProfileFactor, if_neg (Finset.mem_erase.mp hq).1,
            unitIntervalMeasure_integral]
        _ = _ := by simp

theorem tensorCoordinateSum_integrable {G : ℝ → ℝ} (hG : Continuous G) (j : ℕ) :
    Integrable (fun t : Fin j → ℝ => (∑ i, t i) * ∏ q, G (t q))
      (Measure.pi (fun _ : Fin j => unitIntervalMeasure)) := by
  simpa only [Finset.sum_mul] using
    integrable_finsetSum Finset.univ (fun i _hi => tensorCoordinate_integrable hG i)

theorem integral_tensorCoordinateSum {G : ℝ → ℝ} (hG : Continuous G) (j : ℕ) :
    (∫ t : Fin j → ℝ, (∑ i, t i) * ∏ q, G (t q)
      ∂Measure.pi (fun _ : Fin j => unitIntervalMeasure)) =
      (j : ℝ) * (∫ t in (0 : ℝ)..1, t * G t) * (∫ t in (0 : ℝ)..1, G t) ^ (j - 1) := by
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _hi => tensorCoordinate_integrable hG i)]
  simp only [integral_tensorCoordinate, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem ae_unitCube (j : ℕ) :
    ∀ᵐ t : Fin j → ℝ ∂Measure.pi (fun _ : Fin j => unitIntervalMeasure),
      ∀ i, t i ∈ Set.Icc (0 : ℝ) 1 := by
  apply eventually_all.mpr
  intro i
  have hi : ∀ᵐ x : ℝ ∂unitIntervalMeasure, x ∈ Set.Icc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  exact (Measure.tendsto_eval_ae_ae
    (μ := fun _ : Fin j => unitIntervalMeasure) (i := i)).eventually hi

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.integral_tensorCoordinateSum
