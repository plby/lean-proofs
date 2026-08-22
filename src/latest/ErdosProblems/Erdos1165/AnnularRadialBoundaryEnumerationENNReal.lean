/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialBoundaryEnumeration

/-! Exact `ℝ≥0∞` form of finite radial-boundary endpoint enumeration. -/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRadialBoundaryEnumeration

open AnnularOffspringKernelRadial AnnularRadialLabelWord
  MarkedBoundaryVisitKernel RealDiscFinite ThickPoint

noncomputable section

theorem sum_radialBoundaryPoint_eq_marked
    (boundary : Set Point) (n : ℕ) (label : Fin (n + 2)) (start : Point) :
    (∑ z : RadialBoundaryPoint n 0 label,
        skeletonExitKernel boundary start z.1) =
      fairSteps (boundaryExitMarkedSteps boundary
        (discBoundary 0 (scaleRadius n label)) start) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.sum_ne_top.mpr fun _ _ ↦ by
      unfold skeletonExitKernel skeletonExitMarkKernel
      exact measure_ne_top fairSteps _)
    (measure_ne_top fairSteps _)).mp
  rw [ENNReal.toReal_sum (fun _ _ ↦ by
    unfold skeletonExitKernel skeletonExitMarkKernel
    exact measure_ne_top fairSteps _)]
  exact sum_radialBoundaryPoint_toReal_eq_marked boundary n label start

end

end Erdos1165.AnnularRadialBoundaryEnumeration
