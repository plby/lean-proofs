import ErdosProblems.Erdos1148.ClosedFlowOrbit

/-! # Independence of the intrinsic orbit measure from its lift -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma ClosedFlowOrbit.measure_eq_of_integral_mul (o p : ClosedFlowOrbit) (γ : SL(2, ℤ))
    (h : o.lift = (γ : SL(2, ℝ)) * p.lift) : o.measure = p.measure := by
  let : Fact (0 < o.period) := ⟨o.period_pos⟩
  let : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hgroup : flowPeriodGroup o.lift = flowPeriodGroup p.lift := by
    rw [h, flowPeriodGroup_integral_mul]
  have hper := o.period_eq_of_group_eq p hgroup
  have hp : p.period ∈ flowPeriodGroup o.lift := hgroup.symm ▸ p.period_mem
  calc
    o.measure = closedOrbitMeasure hp := closedOrbitMeasure_congr_period o.period_mem hp hper
    _ = p.measure := by
      simpa only [h, ClosedFlowOrbit.measure] using closedOrbitMeasure_integral_mul γ p.period_mem
        (show p.period ∈ flowPeriodGroup ((γ : SL(2, ℝ)) * p.lift) from h ▸ hp)

lemma ClosedFlowOrbit.measure_eq_of_mul_flow (o p : ClosedFlowOrbit) (s : ℝ)
    (h : o.lift = p.lift * diagonalFlow s) : o.measure = p.measure := by
  let : Fact (0 < o.period) := ⟨o.period_pos⟩
  let : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hgroup : flowPeriodGroup o.lift = flowPeriodGroup p.lift := by
    rw [h, flowPeriodGroup_mul_flow]
  have hper := o.period_eq_of_group_eq p hgroup
  have hp : p.period ∈ flowPeriodGroup o.lift := hgroup.symm ▸ p.period_mem
  calc
    o.measure = closedOrbitMeasure hp := closedOrbitMeasure_congr_period o.period_mem hp hper
    _ = p.measure := by
      simpa only [h, ClosedFlowOrbit.measure] using closedOrbitMeasure_mul_flow s p.period_mem
        (show p.period ∈ flowPeriodGroup (p.lift * diagonalFlow s) from h ▸ hp)

lemma ClosedFlowOrbit.measure_eq_of_formAction_eq (o p : ClosedFlowOrbit)
    (h : formAction o.lift (splitForm ℝ) = formAction p.lift (splitForm ℝ)) :
    o.measure = p.measure := by
  obtain ⟨s, hs | hs⟩ := exists_signed_flow_of_formAction_eq h.symm
  · exact o.measure_eq_of_mul_flow p s hs
  · let q : ClosedFlowOrbit :=
      { lift := p.lift * diagonalFlow s
        period := p.period
        period_pos := p.period_pos
        period_group := (flowPeriodGroup_mul_flow p.lift s).trans p.period_group }
    have hoq : o.measure = q.measure := o.measure_eq_of_integral_mul q (-1) (by simpa [q] using hs)
    exact hoq.trans (q.measure_eq_of_mul_flow p s rfl)

end Erdos1148.DukeArithmetic
