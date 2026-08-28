import Wikipedia.HopfProblem.DegreeCollapseSphereClassification
import Wikipedia.HopfProblem.DegreeCollapseSixSphereConnectivity
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# A degree-one based self-map of the standard six-sphere is homotopic to the identity

The hypothesis is an equality for the actual induced singular-homology
map and the actual quotient-cube class. The conclusion is an actual native
homotopy fixed at the sphere base point, not an equality of invariants.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.Sphere

open SixSphereCube SingularMayerVietoris PeriodTorusHigherHomology

/-- The finite-dimensional sphere side of the proposed inverse-map argument. -/
theorem based_homotopicRel_id_of_topClass
    (g : C(StandardSphere, StandardSphere)) (hg : g sphereBasePoint = sphereBasePoint)
    (hd : singularHomologyMap g 6 (SixthHurewicz.cubeHomologyClass cubeSphereLoop) =
      SixthHurewicz.cubeHomologyClass cubeSphereLoop) :
    g.HomotopicRel (ContinuousMap.id StandardSphere) {sphereBasePoint} := by
  let := piTwo_subsingleton sphereBasePoint
  let := piThree_subsingleton sphereBasePoint
  let := piFour_subsingleton sphereBasePoint
  let := piFive_subsingleton sphereBasePoint
  apply sphere_homotopicRel_of_topClass_eq g (ContinuousMap.id StandardSphere) hg rfl
  simpa only [singularHomologyMap_id, LinearMap.id_apply] using hd

/-- A based self-map has this actual degree precisely when it is based-homotopic to identity. -/
theorem based_homotopicRel_id_iff_topClass
    (g : C(StandardSphere, StandardSphere)) (hg : g sphereBasePoint = sphereBasePoint) :
    g.HomotopicRel (ContinuousMap.id StandardSphere) {sphereBasePoint} ↔
      singularHomologyMap g 6 (SixthHurewicz.cubeHomologyClass cubeSphereLoop) =
        SixthHurewicz.cubeHomologyClass cubeSphereLoop := by
  constructor
  · rintro ⟨H⟩
    have h := homotopy_homologyMap H.toHomotopy 6
    rw [h, singularHomologyMap_id, LinearMap.id_apply]
  · exact based_homotopicRel_id_of_topClass g hg

end Wikipedia.HopfProblem.DegreeCollapse.Sphere
