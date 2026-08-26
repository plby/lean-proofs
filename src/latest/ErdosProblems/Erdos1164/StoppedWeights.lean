import ErdosProblems.Erdos1165.StrongMarkovFullTail

/-! # Nonnegative weighted strong Markov estimates on countable stopped fibers -/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1164

open Erdos1165

/-- Integral form of the full-tail strong Markov property on one stopped event. -/
theorem lintegral_stopped_future {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    {A : Set StepPath} (hA : IsMeasurableAtStopping τ A)
    {f : StepPath → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ w in A, f (postStoppingSteps τ w) ∂fairSteps) =
      fairSteps A * (∫⁻ w, f w ∂fairSteps) := by
  rw [← lintegral_map hf (measurable_postStoppingSteps hτ),
    map_restrict_postStoppingSteps hτ hA, lintegral_smul_measure, smul_eq_mul]

/-- Countable partition of a restricted integral into observable fibers. -/
theorem lintegral_stopped_fibers {State : Type*} [Countable State]
    {τ : StepPath → ℕ} {A : Set StepPath} (location : StepPath → State)
    (hobs : ∀ x, IsMeasurableAtStopping τ (A ∩ {w | location w = x}))
    (f : StepPath → ℝ≥0∞) :
    (∫⁻ w in A, f w ∂fairSteps) =
      ∑' x, ∫⁻ w in A ∩ {v | location v = x}, f w ∂fairSteps := by
  have hu : (⋃ x, A ∩ {w | location w = x}) = A := by ext w; simp
  have hd : Pairwise fun x y : State ↦
      Disjoint (A ∩ {w | location w = x}) (A ∩ {w | location w = y}) := by
    intro x y hxy
    rw [Set.disjoint_left]
    intro w hx hy
    exact hxy (hx.2.symm.trans hy.2)
  nth_rw 1 [← hu]
  exact lintegral_iUnion (fun x ↦ (hobs x).measurableSet) hd f

/-- Exact weighted factorization. The past weight may have infinitely many
values; no boundedness or integrability is needed for nonnegative integrals. -/
theorem strongMarkov_weighted_identity {State : Type*} [Countable State]
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ) {A : Set StepPath}
    (location : StepPath → State)
    (hobs : ∀ x, IsMeasurableAtStopping τ (A ∩ {w | location w = x}))
    (weight : State → ℝ≥0∞) (future : State → StepPath → ℝ≥0∞)
    (hfuture : ∀ x, Measurable (future x)) :
    (∫⁻ w in A, weight (location w) * future (location w) (postStoppingSteps τ w) ∂fairSteps) =
      ∑' x, weight x * fairSteps (A ∩ {w | location w = x}) *
        (∫⁻ v, future x v ∂fairSteps) := by
  rw [lintegral_stopped_fibers location hobs]
  congr 1
  funext x
  calc
    (∫⁻ w in A ∩ {v | location v = x},
        weight (location w) * future (location w) (postStoppingSteps τ w) ∂fairSteps) =
      ∫⁻ w in A ∩ {v | location v = x}, weight x * future x (postStoppingSteps τ w) ∂fairSteps := by
        apply setLIntegral_congr_fun (hobs x).measurableSet
        intro w hw
        dsimp only
        rw [hw.2]
    _ = weight x * (∫⁻ w in A ∩ {v | location v = x},
        future x (postStoppingSteps τ w) ∂fairSteps) :=
      lintegral_const_mul'' _ ((hfuture x).comp (measurable_postStoppingSteps hτ)).aemeasurable
    _ = _ := by rw [lintegral_stopped_future hτ (hobs x) (hfuture x), mul_assoc]

private theorem lintegral_stopped_weight {State : Type*} [Countable State]
    {τ : StepPath → ℕ} {A : Set StepPath} (location : StepPath → State)
    (hobs : ∀ x, IsMeasurableAtStopping τ (A ∩ {w | location w = x}))
    (weight : State → ℝ≥0∞) :
    (∫⁻ w in A, weight (location w) ∂fairSteps) =
      ∑' x, weight x * fairSteps (A ∩ {w | location w = x}) := by
  rw [lintegral_stopped_fibers location hobs]
  congr 1
  funext x
  calc
    (∫⁻ w in A ∩ {v | location v = x}, weight (location w) ∂fairSteps) =
        ∫⁻ _w in A ∩ {v | location v = x}, weight x ∂fairSteps := by
      apply setLIntegral_congr_fun (hobs x).measurableSet
      intro w hw
      dsimp only
      rw [hw.2]
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

/-- Uniform bounds for a fresh future factor remain valid after multiplication
by any nonnegative stopped-past weight. Only nonempty fibers require a bound. -/
theorem strongMarkov_weighted_le {State : Type*} [Countable State]
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ) {A : Set StepPath}
    (location : StepPath → State)
    (hobs : ∀ x, IsMeasurableAtStopping τ (A ∩ {w | location w = x}))
    (weight : State → ℝ≥0∞) (future : State → StepPath → ℝ≥0∞)
    (hfuture : ∀ x, Measurable (future x)) (bound : ℝ≥0∞)
    (hbound : ∀ x, (A ∩ {w | location w = x}).Nonempty →
      (∫⁻ v, future x v ∂fairSteps) ≤ bound) :
    (∫⁻ w in A, weight (location w) * future (location w) (postStoppingSteps τ w) ∂fairSteps) ≤
      (∫⁻ w in A, weight (location w) ∂fairSteps) * bound := by
  rw [strongMarkov_weighted_identity hτ location hobs weight future hfuture,
    lintegral_stopped_weight location hobs weight, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : (A ∩ {w | location w = x}).Nonempty
  · exact mul_le_mul' le_rfl (hbound x hx)
  · have he : A ∩ {w | location w = x} = ∅ := Set.not_nonempty_iff_eq_empty.mp hx
    simp only [he, measure_empty, mul_zero, zero_mul, le_refl]

end Erdos1164
