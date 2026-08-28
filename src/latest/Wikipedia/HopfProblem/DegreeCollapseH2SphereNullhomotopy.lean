import Wikipedia.HopfProblem.DegreeCollapseIntegralSphereRepresentatives
import Wikipedia.NoExoticSixSphere.SphereCubeHomotopy

/-!
# Actual two-sphere nullhomotopies from simple connectivity and zero H2

The native second Hurewicz equivalence kills the original based cube
class. The genuine cube quotient descends its relative homotopy to the
original sphere map, fixed at its actual marked point.
-/

noncomputable section

open Set ContinuousMap
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse

open NoExoticSixSphere SingularMayerVietoris
open Wikipedia.SmoothSixDPoincare

theorem two_sphere_nullhomotopic_of_homology
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    [Subsingleton (SingularHomology X 2)] (γ : C(Hemisphere.Sphere 2, X)) :
    γ.HomotopicRel (ContinuousMap.const _ (γ (SphereCube.point 2))) {SphereCube.point 2} := by
  let x := γ (SphereCube.point 2)
  let : Subsingleton (π_ 2 X x) :=
    (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).injective.subsingleton
  apply (SphereCubeHomotopy.basedCube_nullhomotopic_iff (by decide : 0 < 2) γ).mp
  exact Quotient.exact (@Subsingleton.elim (π_ 2 X x) inferInstance
    ⟦SphereCube.basedCube γ⟧ ⟦GenLoop.const⟧)

end Wikipedia.HopfProblem.DegreeCollapse
