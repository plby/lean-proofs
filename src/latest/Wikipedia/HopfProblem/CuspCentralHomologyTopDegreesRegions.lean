import Wikipedia.HopfProblem.CuspCentralHomologyTopDegreesTori
import Wikipedia.HopfProblem.CuspCentralHomologyDoubleLocusHomeomorph
import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverCollar
import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverOverlap

/-!
# High-degree homology of the actual central-cusp open cover

These are homology computations for the original open subsets, using
their constructed deformation retractions and coordinate homeomorphisms.
The outer set has the homology of the actual boundary suspension, the
inner set that of the two-circle phase torus, and the intersection that
of the three-circle phase-and-boundary torus.
-/

noncomputable section

open Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The actual outer collar retracts onto the actual boundary, whose
suspension identification was constructed from its phase quotient. -/
def outerRegionSuspensionHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    outerRegion C ε hε a ≃ₕ ThreeCircleSuspension :=
  (outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR).trans
    (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).toHomotopyEquiv

def innerRegionHomologyEquiv (n : ℕ) :
    SingularHomology (innerRegion C ε hε) n ≃ₗ[ℤ] binomialModule 2 n :=
  (homotopyEquivHomologyEquiv (innerRegionHomotopyEquiv C ε hε hε1 hC hR) n).trans
    (compactFibreTorusHomologyEquiv n)

def overlapRegionHomologyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    SingularHomology (overlapRegion C ε hε a) n ≃ₗ[ℤ] binomialModule 3 n :=
  (homotopyEquivHomologyEquiv
    (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) n).trans
      (fibreTorusCircleHomologyEquiv n)

def overlapRegionHomologyThreeEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    SingularHomology (overlapRegion C ε hε a) 3 ≃ₗ[ℤ] ℤ :=
  (homotopyEquivHomologyEquiv
    (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) 3).trans
      fibreTorusCircleHomologyThreeEquiv

include hε1 hC hR

theorem outerRegion_homology_subsingleton (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    Subsingleton (SingularHomology (outerRegion C ε hε a) (n + 3)) := by
  let := threeCircleSuspension_homology_subsingleton n
  exact (homotopyEquivHomologyEquiv
    (outerRegionSuspensionHomotopyEquiv C ε hε hε1 hC hR a ha ha1) (n + 3)).injective.subsingleton

theorem innerRegion_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularHomology (innerRegion C ε hε) (n + 3)) := by
  let := compactFibreTorus_homology_subsingleton n
  exact (homotopyEquivHomologyEquiv
    (innerRegionHomotopyEquiv C ε hε hε1 hC hR) (n + 3)).injective.subsingleton

theorem overlapRegion_homology_subsingleton (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    Subsingleton (SingularHomology (overlapRegion C ε hε a) (n + 4)) := by
  let := fibreTorusCircle_homology_subsingleton n
  exact (homotopyEquivHomologyEquiv
    (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) (n + 4)).injective.subsingleton

end Wikipedia.HopfProblem.CuspCentralHomology
