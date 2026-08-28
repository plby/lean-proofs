import Wikipedia.HomotopyGroupsOfSpheres.SphereSevenDegree
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicDegree

/-! # The exact sequence's projection degree is the actual sphere-map degree -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

attribute [local irreducible] unitSphereHomologyTopEquiv

@[irreducible] def baseHomologyCoordinate (c : SingularHomology BaseSphere 7) : ℤ :=
  unitSphereHomologyTopEquiv 6 (singularHomologyMap (baseSphereHomeomorph : C(_, _)) 7 c)

theorem baseDegreeEquiv_coordinate (a : π_ 7 BaseSphere north) :
    (baseDegreeEquiv a).toAdd =
      baseHomologyCoordinate (SeventhHurewicz.hurewiczFunction north a) := by
  unfold baseDegreeEquiv baseHomologyCoordinate
  refine (pi7_sphere_seven_coordinate (baseSphereHomeomorph north) _).trans ?_
  exact congrArg (fun c : SingularHomology (Sphere 7) 7 ↦ unitSphereHomologyTopEquiv 6 c)
    (SeventhHurewicz.hurewiczFunction_homeomorph_natural baseSphereHomeomorph north a).symm

theorem projectionDegree_coordinate (a : π_ 7 SpTwo 1) :
    (projectionDegree a).toAdd = baseHomologyCoordinate
      (singularHomologyMap projection 7 (SeventhHurewicz.hurewiczFunction 1 a)) := by
  refine (baseDegreeEquiv_coordinate (projectionMap 6 a)).trans ?_
  exact congrArg baseHomologyCoordinate
    (SeventhHurewicz.hurewiczFunction_map_natural projection 1 a).symm

def projectedSphereMap (f : C(Sphere 7, SpTwo)) : C(Sphere 7, Sphere 7) :=
  (baseSphereHomeomorph : C(_, _)).comp (projection.comp f)

/-- No numerical degree is assumed: this compares the two actual definitions. -/
theorem projectionDegree_pointed_sphereMap (f : C(Sphere 7, SpTwo))
    (x : Sphere 7) (hf : f x = 1) :
    (projectionDegree (pointedMap f x 1 hf (sphereSevenGenerator x))).toAdd =
      sphereSevenDegree (projectedSphereMap f) := by
  refine (projectionDegree_coordinate _).trans ?_
  have hn := SeventhHurewicz.hurewiczFunction_pointed_natural f x 1 hf (sphereSevenGenerator x)
  have hm := congrArg (fun c : SingularHomology SpTwo 7 ↦
    baseHomologyCoordinate (singularHomologyMap projection 7 c)) hn.symm
  refine hm.trans ?_
  have hs := congrArg (fun c : SingularHomology (Sphere 7) 7 ↦
    baseHomologyCoordinate (singularHomologyMap projection 7 (singularHomologyMap f 7 c)))
        (sphereSevenGenerator_hurewicz x)
  refine hs.trans ?_
  simp only [baseHomologyCoordinate, sphereSevenDegree, projectedSphereMap,
    singularHomologyMap_comp, LinearMap.comp_apply]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
