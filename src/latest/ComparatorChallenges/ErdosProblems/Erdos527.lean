/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology
open Asymptotics Filter MeasureTheory ProbabilityTheory
open Complex
open Set
open Set Real MeasureTheory
open scoped ENNReal Pointwise Topology
open ProbabilityTheory
open scoped BigOperators Topology
open Set Function
open scoped ENNReal NNReal
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Set
open Filter MeasureTheory Set
open MeasureTheory ProbabilityTheory Set Filter Finset
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
open Finset
open Filter MeasureTheory ProbabilityTheory
open MeasureTheory
open Filter
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Filter Set
open MeasureTheory ProbabilityTheory Filter
open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

namespace Erdos527

open scoped Classical in
def SquareSumDiverges (a : ℕ → ℝ) : Prop :=
  Tendsto (fun N ↦ ∑ n ∈ Finset.range N, |a n| ^ 2) atTop atTop

end Erdos527

namespace Erdos527

open scoped Classical in
def DecaysFasterThanInvSqrt (a : ℕ → ℝ) : Prop :=
  (fun n : ℕ ↦ |a n|) =o[atTop]
    (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹)

/-! ## Exact cyclic grids and refinement -/

end Erdos527

namespace Erdos527

open scoped Classical in
noncomputable def half : unitInterval := ⟨1 / 2, by norm_num⟩

end Erdos527

namespace Erdos527

open scoped Classical in
noncomputable def rademacherMeasure : Measure ℝ :=
  Ber((1 : ℝ), (-1 : ℝ), half)

end Erdos527

namespace Erdos527

open scoped Classical in
noncomputable def rademacherProductMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ ↦ rademacherMeasure

end Erdos527

namespace Erdos527

open scoped Classical in
def seriesTerm (a ε : ℕ → ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ((ε n * a n : ℝ) : ℂ) * z ^ n

end Erdos527

namespace Erdos527

open scoped Classical in
def SeriesConvergesAt (a ε : ℕ → ℝ) (z : ℂ) : Prop :=
  Summable (seriesTerm a ε z) (SummationFilter.conditional ℕ)

end Erdos527

namespace Erdos527

open scoped Classical in
theorem erdos_527
    (a : ℕ → ℝ) (hsq : SquareSumDiverges a)
    (hsmall : DecaysFasterThanInvSqrt a) :
    ∀ᵐ ε ∂rademacherProductMeasure,
      ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z := by
  sorry

end Erdos527

end
