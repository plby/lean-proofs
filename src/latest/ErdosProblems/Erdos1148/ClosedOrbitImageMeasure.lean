import ErdosProblems.Erdos1148.ClosedOrbitMeasure
import ErdosProblems.Erdos1148.QuotientImageMeasure

/-! # Comparing closed-orbit image measure with parameter length -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

lemma closedOrbitMeasure_eq_map_interval {g : SL(2, ℝ)} {T : ℝ} [Fact (0 < T)]
    (hT : T ∈ flowPeriodGroup g) (a : ℝ) :
    closedOrbitMeasure hT =
      Measure.map (modularFlowCurve g) (volume.restrict (Set.Ioc a (a + T))) := by
  have hp := AddCircle.measurePreserving_mk T a
  have hc := (continuous_closedOrbitCurve hT).measurable
  calc
    closedOrbitMeasure hT = Measure.map (closedOrbitCurve hT)
        (Measure.map (fun t : ℝ => (t : AddCircle T)) (volume.restrict (Set.Ioc a (a + T)))) := by
      rw [hp.map_eq]
      rfl
    _ = Measure.map (closedOrbitCurve hT ∘ (fun t : ℝ => (t : AddCircle T)))
        (volume.restrict (Set.Ioc a (a + T))) := Measure.map_map hc hp.measurable
    _ = _ := rfl

theorem closedOrbitMeasure_image_le {g : SL(2, ℝ)} {T : ℝ} [Fact (0 < T)]
    (hT : T ∈ flowPeriodGroup g) (hgen : flowPeriodGroup g = AddSubgroup.zmultiples T)
    (E : Set ℝ) (hE : MeasurableSet (modularFlowCurve g '' E)) :
    closedOrbitMeasure hT (modularFlowCurve g '' E) ≤ volume E := by
  have hs := isAddFundamentalDomain_Ioc (Fact.out : 0 < T) 0
  have hsep (s t : ℝ) (heq : modularFlowCurve g s = modularFlowCurve g t) :
      ∃ n : AddSubgroup.zmultiples T, n +ᵥ s = t := by
    have hp := (modularFlowCurve_eq_iff g s t).mp heq
    rw [hgen] at hp
    refine ⟨⟨t - s, hp⟩, ?_⟩
    change (t - s) + s = t
    ring
  rw [closedOrbitMeasure_eq_map_interval hT 0]
  exact addFundamentalDomain_map_image_le volume hs
    (continuous_modularFlowCurve g).measurable hsep E hE

end Erdos1148.DukeArithmetic
