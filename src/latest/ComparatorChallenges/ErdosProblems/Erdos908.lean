/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos908

open Filter MeasureTheory Set Function
open scoped Pointwise ENNReal

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

/-- The universal assertion with the incorrect continuous conclusion. -/
def Erdos908Claim : Prop :=
  ∀ f : ℝ → ℝ, HasMeasurablePositiveDifferences f → HasDecomposition f

/-- The corrected universal assertion with a measurable summand. -/
def Erdos908MeasurableClaim : Prop :=
  ∀ f : ℝ → ℝ,
    HasMeasurablePositiveDifferences f → HasMeasurableDecomposition f

/-- The continuous version admits a counterexample. -/
theorem erdos908_continuous_counterexample : ¬ Erdos908Claim := by
  sorry

/-- The measurable version holds. -/
theorem erdos908_measurable : Erdos908MeasurableClaim := by
  sorry

end Erdos908
