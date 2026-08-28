import Wikipedia.HopfProblem.DegreeCollapseSphereBasepoint
import Wikipedia.HopfProblem.DegreeCollapseSixSphereDegree

/-!
# Unbased degree-one self-maps of the literal six-sphere

Move the actual value at the distinguished point along a recorded path,
apply the based classification, and concatenate the genuine homotopies.
Homotopy invariance preserves the native top-homology class during the move.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.Sphere

open SixSphereCube SingularMayerVietoris PeriodTorusHigherHomology

/-- No basepoint condition is required for the actual degree-one homotopy classification. -/
theorem homotopic_id_of_topClass (g : C(StandardSphere, StandardSphere))
    (hd : singularHomologyMap g 6 (SixthHurewicz.cubeHomologyClass cubeSphereLoop) =
      SixthHurewicz.cubeHomologyClass cubeSphereLoop) :
    g.Homotopic (ContinuousMap.id StandardSphere) := by
  obtain ⟨v, hv, hgv⟩ := SphereBasepoint.exists_adjustment g
    (PathConnectedSpace.somePath (g sphereBasePoint) sphereBasePoint)
  have hmap := homotopic_homologyMap hgv 6
  have hvd : singularHomologyMap v 6 (SixthHurewicz.cubeHomologyClass cubeSphereLoop) =
      SixthHurewicz.cubeHomologyClass cubeSphereLoop :=
    (LinearMap.congr_fun hmap _).symm.trans hd
  obtain ⟨H⟩ := based_homotopicRel_id_of_topClass v hv hvd
  exact hgv.trans ⟨H.toHomotopy⟩

end Wikipedia.HopfProblem.DegreeCollapse.Sphere
