import ErdosProblems.Erdos1148.ClosedOrbitInvariance

/-! # Changing the lift or the starting point of a closed orbit -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

lemma closedOrbitMeasure_congr_period {g : SL(2, ℝ)} {T U : ℝ}
    [Fact (0 < T)] [Fact (0 < U)] (hT : T ∈ flowPeriodGroup g)
    (hU : U ∈ flowPeriodGroup g) (heq : T = U) : closedOrbitMeasure hT = closedOrbitMeasure hU := by
  subst U
  rfl

lemma mem_flowPeriodGroup_iff_curve (g : SL(2, ℝ)) (T : ℝ) :
    T ∈ flowPeriodGroup g ↔ modularFlowCurve g 0 = modularFlowCurve g T := by
  simpa only [sub_zero] using (modularFlowCurve_eq_iff g 0 T).symm

lemma modularFlowCurve_integral_mul (γ : SL(2, ℤ)) (g : SL(2, ℝ)) (t : ℝ) :
    modularFlowCurve ((γ : SL(2, ℝ)) * g) t = modularFlowCurve g t := by
  change modularMk (((γ : SL(2, ℝ)) * g) * diagonalFlow t) =
    modularMk (g * diagonalFlow t)
  rw [mul_assoc, modularMk_integral_mul]

lemma modularFlowCurve_mul_flow (g : SL(2, ℝ)) (s t : ℝ) :
    modularFlowCurve (g * diagonalFlow s) t = modularFlowCurve g (s + t) := by
  change modularMk ((g * diagonalFlow s) * diagonalFlow t) =
    modularMk (g * diagonalFlow (s + t))
  rw [diagonalFlow_add, mul_assoc]

lemma flowPeriodGroup_integral_mul (γ : SL(2, ℤ)) (g : SL(2, ℝ)) :
    flowPeriodGroup ((γ : SL(2, ℝ)) * g) = flowPeriodGroup g := by
  ext t
  rw [mem_flowPeriodGroup_iff_curve, mem_flowPeriodGroup_iff_curve,
    modularFlowCurve_integral_mul, modularFlowCurve_integral_mul]

lemma flowPeriodGroup_mul_flow (g : SL(2, ℝ)) (s : ℝ) :
    flowPeriodGroup (g * diagonalFlow s) = flowPeriodGroup g := by
  ext t
  rw [mem_flowPeriodGroup_iff_curve, modularFlowCurve_mul_flow, modularFlowCurve_mul_flow,
    modularFlowCurve_eq_iff]
  simp

theorem closedOrbitMeasure_integral_mul {g : SL(2, ℝ)} {T : ℝ} [Fact (0 < T)]
    (γ : SL(2, ℤ)) (hT : T ∈ flowPeriodGroup g)
    (hT' : T ∈ flowPeriodGroup ((γ : SL(2, ℝ)) * g)) :
    closedOrbitMeasure hT' = closedOrbitMeasure hT := by
  have heq : closedOrbitCurve hT' = closedOrbitCurve hT := by
    funext x
    induction x using Quotient.inductionOn' with | h t =>
      exact modularFlowCurve_integral_mul γ g t
  unfold closedOrbitMeasure
  rw [heq]

theorem closedOrbitMeasure_mul_flow {g : SL(2, ℝ)} {T : ℝ} [Fact (0 < T)]
    (s : ℝ) (hT : T ∈ flowPeriodGroup g) (hT' : T ∈ flowPeriodGroup (g * diagonalFlow s)) :
    closedOrbitMeasure hT' = closedOrbitMeasure hT := by
  have heq : closedOrbitCurve hT' =
      modularRightTranslate (diagonalFlow s) ∘ closedOrbitCurve hT := by
    funext x
    induction x using Quotient.inductionOn' with | h t =>
      change modularMk ((g * diagonalFlow s) * diagonalFlow t) =
        modularMk ((g * diagonalFlow t) * diagonalFlow s)
      have hcomm : diagonalFlow s * diagonalFlow t = diagonalFlow t * diagonalFlow s := by
        rw [← diagonalFlow_add, ← diagonalFlow_add, add_comm]
      rw [mul_assoc, mul_assoc, hcomm]
  change Measure.map (closedOrbitCurve hT') volume = closedOrbitMeasure hT
  rw [heq, ← Measure.map_map (continuous_modularRightTranslate _).measurable
    (continuous_closedOrbitCurve hT).measurable]
  exact closedOrbitMeasure_flow_invariant hT s

end Erdos1148.DukeArithmetic
