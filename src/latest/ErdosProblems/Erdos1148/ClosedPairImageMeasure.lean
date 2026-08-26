import ErdosProblems.Erdos1148.PeriodRectangle

/-! # Comparing pairs of closed orbits with their parameter areas -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

noncomputable def pairFlowCurve (g h : SL(2, ℝ)) : ℝ × ℝ → ModularOrbitSpace × ModularOrbitSpace :=
  Prod.map (modularFlowCurve g) (modularFlowCurve h)

lemma measurable_pairFlowCurve (g h : SL(2, ℝ)) : Measurable (pairFlowCurve g h) :=
  (continuous_modularFlowCurve g).measurable.prodMap (continuous_modularFlowCurve h).measurable

lemma closedOrbitMeasure_prod_eq_map_rectangle {g h : SL(2, ℝ)} {T U : ℝ}
    [Fact (0 < T)] [Fact (0 < U)] (hT : T ∈ flowPeriodGroup g) (hU : U ∈ flowPeriodGroup h) :
    (closedOrbitMeasure hT).prod (closedOrbitMeasure hU) =
      Measure.map (pairFlowCurve g h) (volume.restrict (Set.Ioc 0 T ×ˢ Set.Ioc 0 U)) := by
  rw [closedOrbitMeasure_eq_map_interval hT 0, closedOrbitMeasure_eq_map_interval hU 0,
    Measure.map_prod_map _ _ (continuous_modularFlowCurve g).measurable
      (continuous_modularFlowCurve h).measurable, Measure.prod_restrict, zero_add, zero_add]
  rfl

theorem closedOrbitMeasure_prod_image_le {g h : SL(2, ℝ)} {T U : ℝ}
    [Fact (0 < T)] [Fact (0 < U)] (hT : T ∈ flowPeriodGroup g) (hU : U ∈ flowPeriodGroup h)
    (hgenT : flowPeriodGroup g = AddSubgroup.zmultiples T)
    (hgenU : flowPeriodGroup h = AddSubgroup.zmultiples U)
    (E : Set (ℝ × ℝ)) (hE : MeasurableSet (pairFlowCurve g h '' E)) :
    (closedOrbitMeasure hT).prod (closedOrbitMeasure hU) (pairFlowCurve g h '' E) ≤ volume E := by
  let H := (AddSubgroup.zmultiples T).prod (AddSubgroup.zmultiples U)
  let : Countable H :=
    ((AddSubgroup.zmultiples T).prodEquiv (AddSubgroup.zmultiples U)).injective.countable
  have hs := isAddFundamentalDomain_period_rectangle (Fact.out : 0 < T) (Fact.out : 0 < U)
  have hsep (x y : ℝ × ℝ) (heq : pairFlowCurve g h x = pairFlowCurve g h y) :
      ∃ n : H, n +ᵥ x = y := by
    have hg := (modularFlowCurve_eq_iff g x.1 y.1).mp (congrArg Prod.fst heq)
    have hh := (modularFlowCurve_eq_iff h x.2 y.2).mp (congrArg Prod.snd heq)
    rw [hgenT] at hg
    rw [hgenU] at hh
    refine ⟨⟨y - x, hg, hh⟩, ?_⟩
    change (y - x) + x = y
    abel
  rw [closedOrbitMeasure_prod_eq_map_rectangle hT hU]
  exact addFundamentalDomain_map_image_le volume hs (measurable_pairFlowCurve g h) hsep E hE

end Erdos1148.DukeArithmetic
