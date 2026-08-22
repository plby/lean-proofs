/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularSpatialSpliceBoundaryFacts
import ErdosProblems.Erdos1165.AnnularSpatialSpliceMembership
import ErdosProblems.Erdos1165.AnnularOffspringKernelRadial
import ErdosProblems.Erdos1165.TerminalProfileBoundarySeparation

/-! Exact finite-domain interpretations of the final spatial splice. -/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AnnularSpatialSpliceKernel

open AnnularOffspringKernelRadial AnnularRadialLabelWord
  AnnularSpatialSplice AnnularSpatialSpliceBoundaryFacts
  AnnularSpatialSpliceKernelDefs AnnularSpatialSpliceMembership AnnulusHarnack
  LiteralRealAnnulus LiteralRealAnnulusRadialExit MarkedBoundaryVisitKernel
  PlanarPotential RealDiscFinite TerminalSpliceProfileGeometry ThickPoint
  TerminalProfileBoundarySeparation

noncomputable section

theorem finalSpliceEvent_toReal_eq_exitMass_discBoundary
    {n : ℕ} {z : Point}
    (hstart : z ∈ literalRealAnnulus (scaleRadius n 1)
      (32 * scaleRadius n 0) ⌈32 * scaleRadius n 0⌉₊) :
    (fairSteps (finalSpliceEvent n z)).toReal =
      (exitMass
        (literalRealAnnulus (scaleRadius n 1) (32 * scaleRadius n 0)
          ⌈32 * scaleRadius n 0⌉₊)
        (discBoundaryFinset 0 (32 * scaleRadius n 0)) z).toReal := by
  have heq := fairSteps_boundaryExitMarkedSteps_eq_exitMass
    (literalRealAnnulus (scaleRadius n 1) (32 * scaleRadius n 0)
      ⌈32 * scaleRadius n 0⌉₊)
    (discBoundary 0 (scaleRadius n 1) ∪
      (↑(discBoundaryFinset 0 (32 * scaleRadius n 0)) : Set Point))
    (discBoundaryFinset 0 (32 * scaleRadius n 0)) hstart
    (final_outerBoundary_subset n)
    (final_interior_avoids_boundary n)
    (final_interior_disjoint_mark n)
  have houter :
      (↑(discBoundaryFinset 0 (32 * scaleRadius n 0)) : Set Point) =
        discBoundary 0 (32 * scaleRadius n 0) := by
    ext y
    simp
  rw [finalSpliceEvent, finalSpliceBoundary, ← houter]
  exact congrArg ENNReal.toReal heq

theorem finalSpliceEvent_toReal_eq_exitMass
    {n : ℕ} (hn : 2 ≤ n) {z : Point}
    (hz : z ∈ radialBoundary n 0 ⟨0, by omega⟩) :
    (fairSteps (finalSpliceEvent n z)).toReal =
      (exitMass
        (literalRealAnnulus (scaleRadius n 1) (32 * scaleRadius n 0)
          ⌈32 * scaleRadius n 0⌉₊)
        (literalRealAnnulusOuterExit (scaleRadius n 1)
          (32 * scaleRadius n 0) ⌈32 * scaleRadius n 0⌉₊) z).toReal := by
  have hstart := final_start_mem_annulus hn hz
  have hr0pos : 0 < scaleRadius n 0 := by
    simp only [scaleRadius_of_le (Nat.zero_le n), regularRadius,
      Nat.cast_zero, sub_zero]
    positivity
  have hadj : scaleRadius n 1 + 1 ≤ scaleRadius n 0 := by
    simpa using scaleRadius_add_one_le_previous hn (by omega : 0 < 1)
      (by omega : 1 ≤ n + 1)
  rw [finalSpliceEvent_toReal_eq_exitMass_discBoundary hstart,
    exitMass_discBoundaryFinset_eq_literalRealAnnulusOuterExit
      (mul_nonneg (by norm_num) hr0pos.le) (Nat.le_ceil _)
      (hadj.trans (by linarith)) hstart]

end

end Erdos1165.AnnularSpatialSpliceKernel
