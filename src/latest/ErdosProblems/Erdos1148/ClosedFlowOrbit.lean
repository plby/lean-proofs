import ErdosProblems.Erdos1148.FlowMeasureChange
import ErdosProblems.Erdos1148.RealFormOrbit

/-! # Closed flow orbits with their intrinsic period and length measure -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

structure ClosedFlowOrbit where
  lift : SL(2, ℝ)
  period : ℝ
  period_pos : 0 < period
  period_group : flowPeriodGroup lift = AddSubgroup.zmultiples period

lemma ClosedFlowOrbit.period_mem (o : ClosedFlowOrbit) : o.period ∈ flowPeriodGroup o.lift := by
  rw [o.period_group]
  exact AddSubgroup.mem_zmultiples o.period

lemma ClosedFlowOrbit.period_isLeast (o : ClosedFlowOrbit) :
    IsLeast {s : ℝ | s ∈ flowPeriodGroup o.lift ∧ 0 < s} o.period := by
  rw [o.period_group, AddSubgroup.zmultiples_eq_closure]
  exact AddSubgroup.isLeast_of_closure_iff_eq_abs.mpr
    ⟨(abs_of_pos o.period_pos).symm, o.period_pos⟩

lemma ClosedFlowOrbit.period_eq_of_group_eq (o p : ClosedFlowOrbit)
    (h : flowPeriodGroup o.lift = flowPeriodGroup p.lift) : o.period = p.period := by
  have ho := o.period_isLeast
  rw [h] at ho
  exact ho.unique p.period_isLeast

noncomputable def ClosedFlowOrbit.measure (o : ClosedFlowOrbit) : Measure ModularOrbitSpace :=
  letI : Fact (0 < o.period) := ⟨o.period_pos⟩
  closedOrbitMeasure o.period_mem

lemma ClosedFlowOrbit.measure_univ (o : ClosedFlowOrbit) :
    o.measure Set.univ = ENNReal.ofReal o.period := by
  let : Fact (0 < o.period) := ⟨o.period_pos⟩
  exact closedOrbitMeasure_univ o.period_mem

instance ClosedFlowOrbit.measure_isFinite (o : ClosedFlowOrbit) : IsFiniteMeasure o.measure where
  measure_univ_lt_top := by rw [o.measure_univ]; exact ENNReal.ofReal_lt_top

lemma ClosedFlowOrbit.measure_flow_invariant (o : ClosedFlowOrbit) (s : ℝ) :
    Measure.map (modularRightTranslate (diagonalFlow s)) o.measure = o.measure := by
  let : Fact (0 < o.period) := ⟨o.period_pos⟩
  exact closedOrbitMeasure_flow_invariant o.period_mem s

noncomputable def closedOrbitOfIntegralLift {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) t) : ClosedFlowOrbit where
  lift := g
  period := Classical.choose (exists_least_positive_flow_period hd hns ht g hg)
  period_pos := (Classical.choose_spec (exists_least_positive_flow_period hd hns ht g hg)).1
  period_group := (Classical.choose_spec (exists_least_positive_flow_period hd hns ht g hg)).2.1

theorem exists_closedFlowOrbit_of_integral_form {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    ∃ o : ClosedFlowOrbit, Real.sqrt (d : ℝ) • formAction o.lift (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) t := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have htR : discr (mapCoeffs (Int.castRingHom ℝ) t) = (d : ℝ) := by
    rw [discr_mapCoeffs, ht]
    rfl
  obtain ⟨g, hg⟩ := exists_formAction_sqrt_discr hdR htR
  obtain ⟨T, hT, hgen, _⟩ := exists_least_positive_flow_period hd hns ht g hg
  exact ⟨⟨g, T, hT, hgen⟩, hg⟩

end Erdos1148.DukeArithmetic
