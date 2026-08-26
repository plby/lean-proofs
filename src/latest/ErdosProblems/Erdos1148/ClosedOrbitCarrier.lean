import ErdosProblems.Erdos1148.ClosedFlowOrbit

/-! # Compact carriers of closed-orbit measures -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

lemma range_closedOrbitCurve {g : SL(2, ℝ)} {T : ℝ} (hT : T ∈ flowPeriodGroup g) :
    Set.range (closedOrbitCurve hT) = Set.range (modularFlowCurve g) := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    induction s using Quotient.inductionOn' with
    | h a => exact ⟨a, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨(s : AddCircle T), rfl⟩

noncomputable def ClosedFlowOrbit.carrier (o : ClosedFlowOrbit) : Set ModularOrbitSpace :=
  Set.range (modularFlowCurve o.lift)

lemma ClosedFlowOrbit.isCompact_carrier (o : ClosedFlowOrbit) : IsCompact o.carrier := by
  let : Fact (0 < o.period) := ⟨o.period_pos⟩
  rw [ClosedFlowOrbit.carrier, ← range_closedOrbitCurve o.period_mem]
  exact isCompact_range (continuous_closedOrbitCurve o.period_mem)

lemma ClosedFlowOrbit.measurableSet_carrier (o : ClosedFlowOrbit) : MeasurableSet o.carrier :=
  o.isCompact_carrier.measurableSet

lemma ClosedFlowOrbit.measure_compl_carrier (o : ClosedFlowOrbit) : o.measure o.carrierᶜ = 0 := by
  let : Fact (0 < o.period) := ⟨o.period_pos⟩
  rw [ClosedFlowOrbit.measure, closedOrbitMeasure,
    Measure.map_apply (continuous_closedOrbitCurve o.period_mem).measurable
      o.measurableSet_carrier.compl]
  have hempty : (closedOrbitCurve o.period_mem) ⁻¹' o.carrierᶜ = ∅ := by
    rw [ClosedFlowOrbit.carrier, ← range_closedOrbitCurve o.period_mem]
    simp only [Set.preimage_compl, Set.preimage_range, Set.compl_univ]
  rw [hempty, measure_empty]

lemma ClosedFlowOrbit.ae_mem_carrier (o : ClosedFlowOrbit) :
    ∀ᵐ x ∂o.measure, x ∈ o.carrier := by
  rw [ae_iff]
  exact o.measure_compl_carrier

end Erdos1148.DukeArithmetic
