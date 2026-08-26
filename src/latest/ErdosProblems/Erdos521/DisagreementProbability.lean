/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Union bounds for comparisons of statistics and their capped versions.
Formal proof: Codex.
-/
import Mathlib.MeasureTheory.Measure.Real

namespace Erdos521

open MeasureTheory

theorem measureReal_disagreement_triangle {Ω β : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X Y Z : Ω → β) :
    μ.real {ω | X ω ≠ Z ω} ≤ μ.real {ω | X ω ≠ Y ω} + μ.real {ω | Y ω ≠ Z ω} := by
  have hsub : {ω | X ω ≠ Z ω} ⊆ {ω | X ω ≠ Y ω} ∪ {ω | Y ω ≠ Z ω} := by
    intro ω hω
    by_cases hXY : X ω = Y ω
    · exact Or.inr (fun hYZ ↦ hω (hXY.trans hYZ))
    · exact Or.inl hXY
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans (measureReal_union_le _ _)

theorem measureReal_capping_disagreement {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℕ) (T : ℕ) :
    μ.real {ω | X ω ≠ min (X ω) T} ≤ μ.real {ω | (T : ℝ) ≤ X ω} := by
  apply measureReal_mono (h₂ := measure_ne_top μ _)
  intro ω hω
  have hlarge : T < X ω := by
    by_contra h
    exact hω (min_eq_left (Nat.le_of_not_gt h)).symm
  change (T : ℝ) ≤ (X ω : ℝ)
  exact Nat.cast_le.mpr hlarge.le

end Erdos521
