import Wikipedia.SmoothSixDPoincare.Statement
import Wikipedia.HopfProblem.SphereHomologyVanishing
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Actual integral homology vanishing from the original homotopy equivalence

The groups are the objects of the native singular homology functor. The
given homotopy equivalence, not an assumed homeomorphism or homology-sphere
predicate, transports the proved standard-sphere calculation.
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare

open ContinuousMap
open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology
  Wikipedia.HopfProblem.SphereHomology

variable {M : Type} [TopologicalSpace M]

/-- The original homotopy-sphere hypothesis forces integral homology to vanish
away from degree zero and the top degree. -/
theorem homotopySixSphere_homology_subsingleton (h : M ≃ₕ SixSphere)
    (k : ℕ) (hk : k ≠ 0) (hktop : k ≠ 6) : Subsingleton (SingularHomology M k) := by
  let : Subsingleton (SingularHomology SixSphere k) :=
    unitSphere_homology_subsingleton 5 k hk hktop
  exact (homotopyEquivHomologyEquiv h k).injective.subsingleton

end Wikipedia.SmoothSixDPoincare
