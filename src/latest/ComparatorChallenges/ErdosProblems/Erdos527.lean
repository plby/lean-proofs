/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter MeasureTheory
open scoped ProbabilityTheory

namespace Erdos527

def SquareSumDiverges (a : ℕ → ℝ) : Prop :=
  Tendsto (fun N ↦ ∑ n ∈ Finset.range N, |a n| ^ 2) atTop atTop

def DecaysFasterThanInvSqrt (a : ℕ → ℝ) : Prop :=
  (fun n : ℕ ↦ |a n|) =o[atTop]
    (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹)

noncomputable def half : unitInterval := ⟨1 / 2, by norm_num⟩

noncomputable def rademacherMeasure : Measure ℝ :=
  Ber((1 : ℝ), (-1 : ℝ), half)

noncomputable def rademacherProductMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ ↦ rademacherMeasure

def seriesTerm (a ε : ℕ → ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ((ε n * a n : ℝ) : ℂ) * z ^ n

def SeriesConvergesAt (a ε : ℕ → ℝ) (z : ℂ) : Prop :=
  Summable (seriesTerm a ε z) (SummationFilter.conditional ℕ)

theorem erdos_527
    (a : ℕ → ℝ) (hsq : SquareSumDiverges a)
    (hsmall : DecaysFasterThanInvSqrt a) :
    ∀ᵐ ε ∂rademacherProductMeasure,
      ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z := by
  sorry

end Erdos527
