/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularSpatialSpliceBoundaryFacts
import ErdosProblems.Erdos1165.AnnularOffspringKernelRadial

/-! Exact finite-domain interpretation of the initial spatial-splice kernel. -/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AnnularSpatialSpliceKernel

open AnnularOffspringKernelRadial AnnularSpatialSpliceKernelDefs AnnulusHarnack
  AnnularSpatialSpliceBoundaryFacts LiteralRealAnnulus
  MarkedBoundaryVisitKernel PlanarPotential RealDiscFinite ThickPoint

noncomputable section

theorem initial_marked_toReal_eq_exitMass_discBoundary
    {n : ℕ} {x : Point}
    (hstart : -x ∈ literalRealAnnulus (scaleRadius n 1)
      (8 * scaleRadius n 0) ⌈8 * scaleRadius n 0⌉₊) :
    (fairSteps (boundaryExitMarkedSteps (initialSpliceBoundary n)
      (discBoundary 0 (scaleRadius n 1)) (-x))).toReal =
      (exitMass
        (literalRealAnnulus (scaleRadius n 1) (8 * scaleRadius n 0)
          ⌈8 * scaleRadius n 0⌉₊)
        (discBoundaryFinset 0 (scaleRadius n 1)) (-x)).toReal := by
  have heq := fairSteps_boundaryExitMarkedSteps_eq_exitMass
    (literalRealAnnulus (scaleRadius n 1) (8 * scaleRadius n 0)
      ⌈8 * scaleRadius n 0⌉₊)
    ((↑(discBoundaryFinset 0 (scaleRadius n 1)) : Set Point) ∪
      discBoundary 0 (8 * scaleRadius n 0))
    (discBoundaryFinset 0 (scaleRadius n 1)) hstart
    (initial_outerBoundary_subset n)
    (initial_interior_avoids_boundary n)
    (initial_interior_disjoint_mark n)
  have hinner :
      (↑(discBoundaryFinset 0 (scaleRadius n 1)) : Set Point) =
        discBoundary 0 (scaleRadius n 1) := by
    ext y
    simp
  rw [initialSpliceBoundary, ← hinner]
  exact congrArg ENNReal.toReal heq

end

end Erdos1165.AnnularSpatialSpliceKernel
