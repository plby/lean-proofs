import Wikipedia.HopfProblem.DegreeCollapseQuaternionicClutchingAction
import Wikipedia.HopfProblem.DegreeCollapseGroupSpherePrecomposition

/-!
# Every generator of pi6(S3) acts injectively on pi8(S6)

Use the actual quaternionic fiber as a topological group. Precomposition
preserves integer powers of sphere classes there. Since the specified
clutching map acts injectively, every generating six-sphere class does
as well. The original fiber homeomorphism then returns the literal S3.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.ThreeSphereGeneratorAction

open NoExoticSixSphere SmoothCube SphereComposition
open Wikipedia.HomotopyGroupsOfSpheres QuaternionicFibration
open QuaternionicClutching

theorem fiberLift_native_map {m n : ℕ} [NeZero m] (f : Based n 3)
    (c : π_ m (NoExoticSixSphere.Sphere n) (spherePole n)) :
    HigherHomotopy.map (N := Fin m) (fiberLift f).val (fiberLift f).property c =
      HigherHomotopy.map (N := Fin m)
        (fiberSphereHomeomorph.symm : C(NoExoticSixSphere.Sphere 3, northSubgroup))
        (fiberSphereHomeomorph.symm_apply_eq.mpr fiberSphereHomeomorph_one.symm)
        (mapHom f m c) :=
  (HigherHomotopy.map_comp f.val f.property
    (fiberSphereHomeomorph.symm : C(NoExoticSixSphere.Sphere 3, northSubgroup))
    (fiberSphereHomeomorph.symm_apply_eq.mpr fiberSphereHomeomorph_one.symm) c).symm

theorem fiberLift_generates {n : ℕ} [NeZero n] (f : Based n 3)
    (hf : Function.Surjective (fun k : ℤ ↦ sphereClass f ^ k)) :
    Function.Surjective (fun k : ℤ ↦ sphereClass (fiberLift f) ^ k) := by
  let F := HigherHomotopy.mapMonoidHom (N := Fin n)
    (fiberSphereHomeomorph.symm : C(NoExoticSixSphere.Sphere 3, northSubgroup))
    (fiberSphereHomeomorph.symm_apply_eq.mpr fiberSphereHomeomorph_one.symm)
  have hF : Function.Surjective F :=
    SphereSelfMapSurjectivity.native_homeomorph_surjective fiberSphereHomeomorph.symm _
  exact (CyclicGenerators.map_generates_iff F (sphereClass f) hf).mpr hF

theorem liftedClutching_eight_injective :
    Function.Injective (HigherHomotopy.map (N := Fin 8)
      (fiberLift sphereClutching).val (fiberLift sphereClutching).property) := by
  intro a b h
  apply sphereClutching_eight_injective
  apply SphereSelfMapSurjectivity.native_homeomorph_injective fiberSphereHomeomorph.symm
    (fiberSphereHomeomorph.symm_apply_eq.mpr fiberSphereHomeomorph_one.symm)
  exact (fiberLift_native_map sphereClutching a).symm.trans
    (h.trans (fiberLift_native_map sphereClutching b))

theorem generator_eight_injective (f : Based 6 3)
    (hf : Function.Surjective (fun k : ℤ ↦ sphereClass f ^ k)) :
    Function.Injective (mapHom f 8) := by
  have hi := GroupSpherePrecomposition.injective_of_generates
    (fiberLift_generates f hf) liftedClutching_eight_injective
  intro a b h
  apply hi
  rw [fiberLift_native_map f a, fiberLift_native_map f b, h]

end Wikipedia.HopfProblem.DegreeCollapse.ThreeSphereGeneratorAction

