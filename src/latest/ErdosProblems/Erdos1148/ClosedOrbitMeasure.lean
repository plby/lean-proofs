import ErdosProblems.Erdos1148.ModularOrbitSpace

/-!
# Measures on closed diagonal-flow orbits

A period gives a continuous map from the circle of that circumference to
the modular quotient. Push forward circle length measure. For the least
positive period the map is injective, and the total mass is that period.
-/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

noncomputable def closedOrbitCurve {g : SL(2, ℝ)} {T : ℝ}
    (hT : T ∈ flowPeriodGroup g) : AddCircle T → ModularOrbitSpace :=
  (modularFlowCurve_periodic hT).lift

lemma closedOrbitCurve_coe {g : SL(2, ℝ)} {T : ℝ} (hT : T ∈ flowPeriodGroup g) (s : ℝ) :
    closedOrbitCurve hT (s : AddCircle T) = modularFlowCurve g s := rfl

lemma continuous_closedOrbitCurve {g : SL(2, ℝ)} {T : ℝ} (hT : T ∈ flowPeriodGroup g) :
    Continuous (closedOrbitCurve hT) :=
  continuous_coinduced_dom.mpr (continuous_modularFlowCurve g)

lemma closedOrbitCurve_injective {g : SL(2, ℝ)} {T : ℝ} (hT : T ∈ flowPeriodGroup g)
    (hgen : flowPeriodGroup g = AddSubgroup.zmultiples T) :
    Function.Injective (closedOrbitCurve hT) := by
  intro x y hxy
  induction x using Quotient.inductionOn' with | h a =>
    induction y using Quotient.inductionOn' with | h b =>
      change modularFlowCurve g a = modularFlowCurve g b at hxy
      have hp := (modularFlowCurve_eq_iff g a b).mp hxy
      rw [hgen] at hp
      apply Quotient.sound
      apply QuotientAddGroup.leftRel_apply.mpr
      simpa only [sub_eq_add_neg, add_comm] using hp

noncomputable def closedOrbitMeasure {g : SL(2, ℝ)} {T : ℝ} [Fact (0 < T)]
    (hT : T ∈ flowPeriodGroup g) : Measure ModularOrbitSpace :=
  Measure.map (closedOrbitCurve hT) volume

lemma closedOrbitMeasure_univ {g : SL(2, ℝ)} {T : ℝ} [Fact (0 < T)]
    (hT : T ∈ flowPeriodGroup g) :
    closedOrbitMeasure hT Set.univ = ENNReal.ofReal T := by
  rw [closedOrbitMeasure, Measure.map_apply (continuous_closedOrbitCurve hT).measurable
    MeasurableSet.univ, Set.preimage_univ, AddCircle.measure_univ]

instance closedOrbitMeasure_isFinite {g : SL(2, ℝ)} {T : ℝ} [Fact (0 < T)]
    (hT : T ∈ flowPeriodGroup g) : IsFiniteMeasure (closedOrbitMeasure hT) where
  measure_univ_lt_top := by rw [closedOrbitMeasure_univ]; exact ENNReal.ofReal_lt_top

end Erdos1148.DukeArithmetic
