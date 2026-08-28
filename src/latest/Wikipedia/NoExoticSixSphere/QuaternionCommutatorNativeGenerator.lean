import Wikipedia.NoExoticSixSphere.QuaternionCommutatorNativeSphere
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps

/-!
# The explicit quaternion cube is primitive and its Samelson square is the original one

The original based sphere/cube correspondence and the proved cyclicity
of pi3(S3) show primitivity of this literal cube. Its undetermined sign
cancels in the Samelson square. This identifies the connecting image of
the explicit native seven-sphere map without assigning that map a degree.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.QuaternionCommutatorNativeSphere

open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres
open QuaternionSamelson QuaternionicFibration QuaternionCommutatorBoundaryLift

def quaternionClass : π_ 3 UnitQuaternions 1 := ⟦quaternionCube⟧

theorem quaternionClass_generates : Function.Surjective (fun k : ℤ ↦ quaternionClass ^ k) := by
  intro a
  obtain ⟨f, hf⟩ := SmoothCube.sphereClass_surjective (by decide : 0 < 3) a
  let fQ : C(UnitQuaternions, UnitQuaternions) :=
    f.val.comp (sphereHomeomorph : C(UnitQuaternions, Sphere 3))
  have hfQ : fQ 1 = 1 := (congrArg f.val sphereHomeomorph_one).trans f.property
  let F : π_ 3 UnitQuaternions 1 →* π_ 3 UnitQuaternions 1 := pointedMap fQ 1 1 hfQ
  have hF : F quaternionClass = a := by
    apply Eq.trans _ hf
    change pointedMap fQ 1 1 hfQ (⟦quaternionCube⟧ : π_ 3 UnitQuaternions 1) = _
    rw [pointedMap_mk]
    apply congrArg (fun p : GenLoop (Fin 3) UnitQuaternions 1 ↦
      (⟦p⟧ : π_ 3 UnitQuaternions 1))
    apply GenLoop.ext
    intro u
    change f.val (sphereHomeomorph (sphereHomeomorph.symm (SmoothCube.quotient 3 u))) =
      f.val (SmoothCube.quotient 3 u)
    rw [Homeomorph.apply_symm_apply]
  let k : ℤ := (degreeEquiv quaternionClass).toAdd
  let j : ℤ := (degreeEquiv (F fundamentalClass)).toAdd
  have hk : fundamentalClass ^ k = quaternionClass := fundamentalClass_zpow_degree _
  have hj : fundamentalClass ^ j = F fundamentalClass := fundamentalClass_zpow_degree _
  refine ⟨j, ?_⟩
  calc
    quaternionClass ^ j = (fundamentalClass ^ k) ^ j := congrArg (fun c ↦ c ^ j) hk.symm
    _ = (fundamentalClass ^ j) ^ k := by rw [← zpow_mul, ← zpow_mul, mul_comm k j]
    _ = (F fundamentalClass) ^ k := congrArg (fun c ↦ c ^ k) hj
    _ = F (fundamentalClass ^ k) := (map_zpow F _ k).symm
    _ = F quaternionClass := congrArg F hk
    _ = a := hF

def quaternionDegree : ℤ := (degreeEquiv quaternionClass).toAdd

theorem quaternionDegree_natAbs : quaternionDegree.natAbs = 1 := by
  obtain ⟨k, hk⟩ := quaternionClass_generates fundamentalClass
  have he := congrArg degreeEquiv hk
  rw [map_zpow, degree_fundamentalClass] at he
  have hm := congrArg Multiplicative.toAdd he
  change k • quaternionDegree = 1 at hm
  rw [Int.zsmul_eq_mul] at hm
  have hn := congrArg Int.natAbs hm
  rw [Int.natAbs_mul] at hn
  exact Nat.eq_one_of_mul_eq_one_left hn

theorem quaternionDegree_square : quaternionDegree * quaternionDegree = 1 := by
  rcases Int.natAbs_eq_iff.mp quaternionDegree_natAbs with h | h <;> rw [h] <;> norm_num

theorem quaternionClass_pairing : pairing quaternionClass quaternionClass = nu := by
  rw [pairing_eq_nu_zpow]
  change nu ^ (quaternionDegree * quaternionDegree) = nu
  rw [quaternionDegree_square, zpow_one]

theorem connecting_sphereClass_nu :
    connecting 6 (SmoothCube.sphereClass basedSphereMap) = fiberEquiv nu :=
  connecting_sphereClass.trans (congrArg fiberEquiv quaternionClass_pairing)

end NoExoticSixSphere.QuaternionCommutatorNativeSphere
