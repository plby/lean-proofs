/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialSplicedChain

/-! Event definitions for the two spatial pieces around a radial word. -/

open Set

namespace Erdos1165.AnnularSpatialSpliceKernelDefs

open MarkedBoundaryVisitKernel ThickPoint

noncomputable section

def initialSpliceBoundary (n : ℕ) : Set Point :=
  discBoundary 0 (scaleRadius n 1) ∪
    discBoundary 0 (8 * scaleRadius n 0)

def finalSpliceBoundary (n : ℕ) : Set Point :=
  discBoundary 0 (scaleRadius n 1) ∪
    discBoundary 0 (32 * scaleRadius n 0)

def finalSpliceEvent (n : ℕ) (z : Point) : Set StepPath :=
  boundaryExitMarkedSteps (finalSpliceBoundary n)
    (discBoundary 0 (32 * scaleRadius n 0)) z

end


end Erdos1165.AnnularSpatialSpliceKernelDefs
