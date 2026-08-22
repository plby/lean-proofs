/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularSpatialSpliceInitialExact
import ErdosProblems.Erdos1165.AnnularRadialBoundaryEnumeration
import ErdosProblems.Erdos1165.AnnularSpatialSpliceMembership
import ErdosProblems.Erdos1165.AnnularSpatialSplice

/-! Exact endpoint-summed form of the initial spatial splice. -/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularSpatialSpliceKernel

open AnnularOffspringKernelRadial AnnularRadialBoundaryEnumeration
  AnnularRadialLabelWord AnnularSpatialSplice AnnularSpatialSpliceKernelDefs
  AnnularSpatialSpliceMembership AnnulusHarnack LiteralRealAnnulus
  LiteralRealAnnulusRadialExit MarkedBoundaryVisitKernel PlanarPotential
  RealDiscFinite ThickPoint

noncomputable section

theorem initial_endpoint_sum_toReal_eq_exitMass
    {n : ℕ} (hn : 1 ≤ n) (hlarge : 3 ≤ (n : ℝ))
    {x : Point} (hx : x ∈ candidateBox n) :
    (∑ z : RadialBoundaryPoint n 0 ⟨1, by omega⟩,
        (skeletonExitKernel (initialSpliceBoundary n) (-x) z.1).toReal) =
      (exitMass
        (literalRealAnnulus (scaleRadius n 1) (8 * scaleRadius n 0)
          ⌈8 * scaleRadius n 0⌉₊)
        (literalRealAnnulusInnerExit (scaleRadius n 1)
          (8 * scaleRadius n 0) ⌈8 * scaleRadius n 0⌉₊) (-x)).toReal := by
  have hstart := initial_start_mem_annulus hn hlarge hx
  rw [sum_radialBoundaryPoint_toReal_eq_marked,
    initial_marked_toReal_eq_exitMass_discBoundary hstart,
    exitMass_discBoundaryFinset_eq_literalRealAnnulusInnerExit hstart]

end

end Erdos1165.AnnularSpatialSpliceKernel
