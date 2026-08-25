import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.Closure
import Mathlib.Tactic

/-!
# Weighted density of a closed region

The interior of a region has weight one and its frontier has weight one half.
This density remains additive for a finite dissection even when its common
frontiers have positive measure. The topology and the measure arguments are
kept separate from the Jordan-curve hypotheses.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Puzzling139335

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- Weight one on the interior and one half on the frontier. -/
def weightedDensity (P : Set X) : X → ℝ≥0∞ :=
  (interior P).indicator (fun _ => 1) +
    (frontier P).indicator (fun _ => (2 : ℝ≥0∞)⁻¹)

theorem weightedDensity_of_mem_interior {P : Set X} {x : X}
    (hx : x ∈ interior P) : weightedDensity P x = 1 := by
  have hfront : x ∉ frontier P := fun h => h.2 hx
  simp [weightedDensity, hx, hfront]

theorem weightedDensity_of_mem_frontier {P : Set X} {x : X}
    (hx : x ∈ frontier P) : weightedDensity P x = (2 : ℝ≥0∞)⁻¹ := by
  simp [weightedDensity, hx, hx.2]

theorem weightedDensity_of_not_mem {P : Set X} (hP : IsClosed P) {x : X}
    (hx : x ∉ P) : weightedDensity P x = 0 := by
  have hint : x ∉ interior P := fun h => hx (interior_subset h)
  have hfront : x ∉ frontier P := fun h => hx (hP.frontier_subset h)
  simp [weightedDensity, hint, hfront]

theorem weightedDensity_le_one (P : Set X) (x : X) :
    weightedDensity P x ≤ 1 := by
  by_cases hi : x ∈ interior P
  · rw [weightedDensity_of_mem_interior hi]
  by_cases hf : x ∈ frontier P
  · rw [weightedDensity_of_mem_frontier hf]
    norm_num
  · simp [weightedDensity, hi, hf]

variable [MeasurableSpace X] [BorelSpace X]

theorem measurable_weightedDensity (P : Set X) : Measurable (weightedDensity P) :=
  (measurable_const.indicator isOpen_interior.measurableSet).add
    (measurable_const.indicator isClosed_frontier.measurableSet)

/-- The nonnegative weighted mass, with no integrability hypothesis needed. -/
def weightedMass (μ : Measure X) (P : Set X) : ℝ≥0∞ :=
  ∫⁻ x, weightedDensity P x ∂μ

theorem weightedMass_eq (μ : Measure X) (P : Set X) :
    weightedMass μ P = μ (interior P) + (2 : ℝ≥0∞)⁻¹ * μ (frontier P) := by
  rw [weightedMass, weightedDensity]
  simp only [Pi.add_apply]
  rw [lintegral_add_left (measurable_const.indicator isOpen_interior.measurableSet)]
  rw [lintegral_indicator_const isOpen_interior.measurableSet,
    lintegral_indicator_const isClosed_frontier.measurableSet, one_mul]

end

end Puzzling139335
