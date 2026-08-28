import Wikipedia.HopfProblem.RiemannSphere
import Wikipedia.HopfProblem.SphereHomologySimplyConnectedTopology
import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Connectedness properties of the actual Riemann sphere

The native one-point compactification of `ℂ` is homeomorphic to the literal
Euclidean unit two-sphere.  The previously proved simple connectedness of
that sphere transfers through this homeomorphism.  Local path connectedness
comes from the original complex affine charts, not from an assumed model.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology

/-- The original one-point compactification is the genuine unit two-sphere. -/
def sphereHomeomorphUnitSphere : RiemannSphere ≃ₜ SphereHomology.UnitSphere 2 :=
  onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp)

/-- The actual Riemann sphere is simply connected. -/
theorem sphere_simplyConnectedSpace : SimplyConnectedSpace RiemannSphere := by
  let : SimplyConnectedSpace (SphereHomology.UnitSphere 2) :=
    SphereHomology.unitSphere_simplyConnectedSpace 0
  exact sphereHomeomorphUnitSphere.toHomotopyEquiv.simplyConnectedSpace

/-- The actual complex affine atlas gives local path connectedness. -/
theorem sphere_locallyPathConnectedSpace : LocallyPathConnectedSpace RiemannSphere :=
  ChartedSpace.locallyPathConnectedSpace ℂ RiemannSphere

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology
