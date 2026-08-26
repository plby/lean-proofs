/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Product coordinates and real-valued Fubini for Gaussian sign events.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GaussianPair

namespace Erdos521

open MeasureTheory ProbabilityTheory

theorem standardGaussian_pair_coordinates :
    MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 2) ↦ (x 0, x 1))
      (stdGaussian (EuclideanSpace ℝ (Fin 2))) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  exact (measurePreserving_piFinTwo (fun _ : Fin 2 ↦ gaussianReal 0 1)).map_eq

theorem measureReal_prod_sections {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : Set (Ω × Ψ)} (hS : MeasurableSet S) :
    (μ.prod ν).real S = ∫ y, μ.real {x | (x, y) ∈ S} ∂ν := by
  have hi : Integrable (S.indicator (fun _ ↦ (1 : ℝ))) (μ.prod ν) :=
    (integrable_const _).indicator hS
  rw [← integral_indicator_one hS]
  change (∫ z, S.indicator (fun _ ↦ (1 : ℝ)) z ∂μ.prod ν) = _
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [] with y
  have hsection : MeasurableSet {x | (x, y) ∈ S} := hS.preimage (by fun_prop)
  have heq : (fun x ↦ S.indicator (fun _ ↦ (1 : ℝ)) (x, y)) =
      {x | (x, y) ∈ S}.indicator (fun _ ↦ (1 : ℝ)) := by
    funext x
    rfl
  rw [heq]
  change (∫ x, {x | (x, y) ∈ S}.indicator (1 : Ω → ℝ) x ∂μ) = _
  exact integral_indicator_one hsection

end Erdos521
