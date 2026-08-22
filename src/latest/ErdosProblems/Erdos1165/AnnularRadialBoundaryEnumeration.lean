/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialLabelWord
import ErdosProblems.Erdos1165.AnnularOffspringKernelRadial

/-! Exact finite enumeration of one literal radial boundary. -/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRadialBoundaryEnumeration

open AnnularOffspringKernelRadial AnnularRadialLabelWord
  MarkedBoundaryVisitKernel RealDiscFinite ThickPoint

noncomputable section

theorem sum_radialBoundaryPoint_toReal_eq_marked
    (boundary : Set Point) (n : ℕ) (label : Fin (n + 2)) (start : Point) :
    (∑ z : RadialBoundaryPoint n 0 label,
        (skeletonExitKernel boundary start z.1).toReal) =
      (fairSteps (boundaryExitMarkedSteps boundary
        (discBoundary 0 (scaleRadius n label)) start)).toReal := by
  let e : RadialBoundaryPoint n 0 label ≃
      BoundaryFinsetPoint 0 (scaleRadius n label) :=
    { toFun := fun z => ⟨z.1, mem_discBoundaryFinset.mpr z.2⟩
      invFun := fun z => ⟨z.1, mem_discBoundaryFinset.mp z.2⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun z => Subtype.ext rfl }
  rw [Fintype.sum_equiv e
    (fun z : RadialBoundaryPoint n 0 label =>
      (skeletonExitKernel boundary start z.1).toReal)
    (fun z : BoundaryFinsetPoint 0 (scaleRadius n label) =>
      (skeletonExitKernel boundary start z.1).toReal) (fun _ => rfl)]
  exact sum_skeletonExitKernel_boundaryFinsetPoint_eq_marked
    boundary 0 (scaleRadius n label) start

end

end Erdos1165.AnnularRadialBoundaryEnumeration
