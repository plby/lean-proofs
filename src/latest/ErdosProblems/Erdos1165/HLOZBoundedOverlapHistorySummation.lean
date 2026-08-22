/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Summing measurable histories with bounded pointwise overlap

This is the bounded-overlap counterpart of the usual disjoint-union measure
identity.  It is useful when a replacement path remembers a source history
up to one of finitely many labels rather than uniquely.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZBoundedOverlapHistorySummation

noncomputable section

/-- A countable family of measurable events whose pointwise membership
fibres have size at most `N` has total mass at most `N` times the ambient
mass. -/
theorem tsum_measure_le_of_overlap
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (A : I → Set Ω) (N : ℕ)
    (hmeas : ∀ i, MeasurableSet (A i))
    (hoverlap : ∀ ω,
      (({i | ω ∈ A i}.encard : ℕ∞) : ℝ≥0∞) ≤ (N : ℝ≥0∞)) :
    (∑' i, μ (A i)) ≤ (N : ℝ≥0∞) * μ Set.univ := by
  calc
    (∑' i, μ (A i)) =
        (∑' i, ∫⁻ ω,
          (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ) := by
      apply tsum_congr
      intro i
      exact (lintegral_indicator_one (hmeas i)).symm
    _ = (∫⁻ ω, ∑' i,
        (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ) := by
      rw [lintegral_tsum]
      intro i
      exact (measurable_const.indicator (hmeas i)).aemeasurable
    _ ≤ ∫⁻ _ω, (N : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro ω
      let fiber : Set I := {i | ω ∈ A i}
      calc
        (∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω) =
            ∑' _i : fiber, (1 : ℝ≥0∞) := by
          rw [tsum_subtype fiber (fun _ : I => (1 : ℝ≥0∞))]
          apply tsum_congr
          intro i
          simp [fiber, Set.indicator]
        _ = ((fiber.encard : ℕ∞) : ℝ≥0∞) :=
          ENNReal.tsum_set_one fiber
        _ ≤ (N : ℝ≥0∞) := hoverlap ω
    _ = (N : ℝ≥0∞) * μ Set.univ := lintegral_const N

/-- Probability-measure specialization. -/
theorem tsum_measure_le_of_overlap_probability
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : I → Set Ω) (N : ℕ)
    (hmeas : ∀ i, MeasurableSet (A i))
    (hoverlap : ∀ ω,
      (({i | ω ∈ A i}.encard : ℕ∞) : ℝ≥0∞) ≤ (N : ℝ≥0∞)) :
    (∑' i, μ (A i)) ≤ (N : ℝ≥0∞) := by
  simpa only [measure_univ, mul_one] using
    tsum_measure_le_of_overlap μ A N hmeas hoverlap

end

end Erdos1165.HLOZBoundedOverlapHistorySummation
