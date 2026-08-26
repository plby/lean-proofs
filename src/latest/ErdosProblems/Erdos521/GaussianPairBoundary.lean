/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Gaussian sign-change events have null boundaries.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GaussianPair

namespace Erdos521

open MeasureTheory ProbabilityTheory

theorem gaussianPair_eval_measurePreserving {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) (i : Fin 2) :
    MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 2) ↦ x i) (gaussianPair ρ) (gaussianReal 0 1) := by
  have hdiag : pairCovariance ρ i i = 1 := by fin_cases i <;> rfl
  have h := measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 2)))
    (i := i) (pairCovariance_posSemidef hρ)
  simpa only [gaussianPair, PiLp.zero_apply, hdiag, Real.toNNReal_one] using h

theorem gaussianPair_axis_null {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) (i : Fin 2) :
    gaussianPair ρ {x | x i = 0} = 0 := by
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have h := (gaussianPair_eval_measurePreserving hρ i).measure_preimage
    (measurableSet_singleton (0 : ℝ)).nullMeasurableSet
  change gaussianPair ρ {x | x i = 0} = (gaussianReal 0 1) {0} at h
  simpa only [measure_singleton] using h

def pairSignFlip : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 0 * x 1 < 0}

theorem pairSignFlip_measurableSet : MeasurableSet pairSignFlip := by
  exact measurableSet_lt (by fun_prop) measurable_const

theorem gaussianPair_signFlip_frontier_null {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) :
    gaussianPair ρ (frontier pairSignFlip) = 0 := by
  have hf : frontier pairSignFlip ⊆ {x | x 0 * x 1 = 0} :=
    frontier_lt_subset_eq (by fun_prop) continuous_const
  have hsub : frontier pairSignFlip ⊆ {x | x 0 = 0} ∪ {x | x 1 = 0} := by
    intro x hx
    exact mul_eq_zero.mp (hf hx)
  apply measure_mono_null hsub
  simp only [measure_union_null, gaussianPair_axis_null hρ]

end Erdos521
