import Wikipedia.SmoothSixDPoincare.Statement
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!
# Native simple connectivity from the original homotopy-sphere hypothesis

The sphere simple-connectivity proof is reused with its retained source
provenance. Native homotopy invariance transfers it to the original space;
no homeomorphism or sphere-recognition principle is used here.
-/

open ContinuousMap

namespace Wikipedia.SmoothSixDPoincare

variable {M : Type*} [TopologicalSpace M]

/-- Simple connectivity follows from the original homotopy equivalence with the six-sphere. -/
theorem simplyConnectedSpace_of_homotopySixSphere (e : M ≃ₕ SixSphere) :
    SimplyConnectedSpace M := by
  let : SimplyConnectedSpace SixSphere := EuclideanSphere.simplyConnectedSpace 4
  exact e.simplyConnectedSpace

/-- Every loop in the original homotopy six-sphere is nullhomotopic. -/
theorem loops_nullhomotopic_of_homotopySixSphere (e : M ≃ₕ SixSphere)
    (x : M) (γ : Path x x) : Path.Homotopic γ (Path.refl x) := by
  let : SimplyConnectedSpace M := simplyConnectedSpace_of_homotopySixSphere e
  exact SimplyConnectedSpace.paths_homotopic _ _

/-- The homotopy six-sphere is path connected in its original topology. -/
theorem pathConnectedSpace_of_homotopySixSphere (e : M ≃ₕ SixSphere) : PathConnectedSpace M := by
  let : SimplyConnectedSpace M := simplyConnectedSpace_of_homotopySixSphere e
  infer_instance

end Wikipedia.SmoothSixDPoincare
