/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialSplicedChain
import ErdosProblems.Erdos1165.AnnularSpatialSplice
import ErdosProblems.Erdos1165.AnnularSpatialSpliceMembership
import ErdosProblems.Erdos1165.AnnularSpatialSpliceKernelDefs
import ErdosProblems.Erdos1165.AnnularSpatialSpliceBoundaryFacts
import ErdosProblems.Erdos1165.AnnularSpatialSpliceInitialExact
import ErdosProblems.Erdos1165.AnnularSpatialSpliceInitialEndpoint
import ErdosProblems.Erdos1165.AnnularSpatialSpliceFinalExact
import ErdosProblems.Erdos1165.AnnularOffspringKernelRadial
import ErdosProblems.Erdos1165.AnnularRadialBoundaryEnumeration
import ErdosProblems.Erdos1165.AnnularRadialBoundaryEnumerationENNReal

/-!
# Kernel form of the initial and final Appendix-A.6 spatial splices

The potential estimates in `AnnularSpatialSplice` are stated as finite-domain
exit masses.  The chronological radial word is expressed through stopped
boundary kernels.  This file proves the exact bridge between those two
representations and hence supplies the two uniform `1 / 128` kernel factors.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularSpatialSpliceKernel

open AnnularOffspringKernelRadial AnnularRadialLabelWord
  AnnularRadialSplicedChain AnnularSpatialSplice
  AnnularSpatialSpliceMembership
  AnnularSpatialSpliceKernelDefs
  AnnularSpatialSpliceBoundaryFacts
  AnnularRadialBoundaryEnumeration
  AnnulusHarnack
  LiteralRealAnnulus LiteralRealAnnulusRadialExit
  MarkedBoundaryVisitKernel PlanarPotential RealDiscFinite
  PotentialEuclideanGeometry
  TerminalExcursionBridge TerminalProfileBoundarySeparation
  TerminalSpliceProfileGeometry ThickPoint

noncomputable section

/-- The centered initial endpoint sum has the required uniform kernel lower
bound at every sufficiently large scale. -/
theorem eventually_one_div_128_le_initial_endpoint_sum :
    ∀ᶠ n : ℕ in atTop, ∀ x : Point, x ∈ candidateBox n →
      (1 / 128 : ℝ≥0∞) ≤ fairSteps
        (boundaryExitMarkedSteps (initialSpliceBoundary n)
          (radialBoundary n 0 ⟨1, by omega⟩) (-x)) := by
  filter_upwards [eventually_centered_spatial_splice_bounds,
    eventually_ge_atTop 2,
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (3 : ℝ))]
      with n hspatial hn hlarge x hx
  have hreal := hspatial x hx |>.1
  have hstart := initial_start_mem_annulus (by omega) hlarge hx
  rw [← exitMass_discBoundaryFinset_eq_literalRealAnnulusInnerExit hstart]
    at hreal
  rw [← initial_marked_toReal_eq_exitMass_discBoundary hstart] at hreal
  apply (ENNReal.toReal_le_toReal (by norm_num) (by finiteness)).mp
  simpa only [radialBoundary, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    ENNReal.toReal_div] using hreal

/-- The fresh final escape has the required uniform kernel lower bound at
every sufficiently large scale, uniformly over the random level-zero
endpoint. -/
theorem eventually_one_div_128_le_finalSpliceEvent :
    ∀ᶠ n : ℕ in atTop, ∀ x : Point, x ∈ candidateBox n →
      ∀ z : Point, z ∈ radialBoundary n 0 ⟨0, by omega⟩ →
        (1 / 128 : ℝ≥0∞) ≤ fairSteps (finalSpliceEvent n z) := by
  filter_upwards [eventually_centered_spatial_splice_bounds,
    eventually_ge_atTop 2] with n hspatial hn x hx z hz
  have hreal := hspatial x hx |>.2 z hz
  rw [← finalSpliceEvent_toReal_eq_exitMass hn hz] at hreal
  apply (ENNReal.toReal_le_toReal (by norm_num) (measure_ne_top fairSteps _)).mp
  simpa using hreal

end

end Erdos1165.AnnularSpatialSpliceKernel
