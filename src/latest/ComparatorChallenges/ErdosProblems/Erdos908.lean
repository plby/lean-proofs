/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open MeasureTheory

namespace Erdos908

/-- An additive real-valued function. -/
def IsAdditiveFn (H : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, H (x + y) = H x + H y

/-- Every positive translate difference is Lebesgue measurable. -/
def HasMeasurablePositiveDifferences (f : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → AEMeasurable (fun x => f (x + t) - f x) volume

/-- Every translate difference vanishes almost everywhere. -/
def HasNullIncrements (r : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, ∀ᵐ x ∂volume, r (x + t) - r x = 0

/-- The originally proposed, false continuous decomposition. -/
def HasDecomposition (f : ℝ → ℝ) : Prop :=
  ∃ g H r : ℝ → ℝ,
    Continuous g ∧
      IsAdditiveFn H ∧
        (∀ x : ℝ, f x = g x + H x + r x) ∧
          HasNullIncrements r

/-- The corrected measurable decomposition. -/
def HasMeasurableDecomposition (f : ℝ → ℝ) : Prop :=
  ∃ g H r : ℝ → ℝ,
    AEMeasurable g volume ∧
      IsAdditiveFn H ∧
        (∀ x : ℝ, f x = g x + H x + r x) ∧
          HasNullIncrements r

/-- The continuous version admits a counterexample. -/
theorem not_erdos_908 :
    ¬ (∀ f : ℝ → ℝ, Erdos908.HasMeasurablePositiveDifferences f → Erdos908.HasDecomposition f) := by
  sorry

/-- The measurable version holds. -/
theorem erdos_908_measurable :
    ∀ f : ℝ → ℝ,
      Erdos908.HasMeasurablePositiveDifferences f → Erdos908.HasMeasurableDecomposition f := by
  sorry

end Erdos908
