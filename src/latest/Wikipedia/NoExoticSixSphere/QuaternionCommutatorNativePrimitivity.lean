import Wikipedia.NoExoticSixSphere.QuaternionCommutatorNativeHomology
import Wikipedia.NoExoticSixSphere.QuaternionCommutatorNativeGenerator
import Wikipedia.NoExoticSixSphere.JamesSphereAttachingCubeGenerator
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCyclicQuotient

/-!
# Primitivity of the actual seven-loop and generation by its Samelson boundary

The proved degree of the explicit sphere map makes its pointed native
map surjective. The actual smooth cube identity is already a generator,
so this identifies the original descended class as a generator. The
original quaternionic connecting homomorphism is surjective and its
value on this literal class is the quaternionic Samelson square.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.QuaternionCommutatorNativeSphere

open Wikipedia.HomotopyGroupsOfSpheres QuaternionicFibration
open Wikipedia.HopfProblem.UnitQuaternionSphere
open JamesSphere.AttachingSquare QuaternionCommutatorBoundaryLift

theorem map_cubeIdentity_homeomorph {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X}
    (f : SmoothCube.BasedMap 7 X x) (e : X ≃ₜ Y) (g : C(Sphere 7, Y))
    (hp : g (spherePole 7) = e x) (hg : g = (e : C(X, Y)).comp f.val) :
    pointedMap g (spherePole 7) (e x) hp cubeIdentityClass =
      homeomorphMulEquiv (N := Fin 7) e x (SmoothCube.sphereClass f) := by
  subst g
  change pointedMap ((e : C(X, Y)).comp f.val) (spherePole 7) (e x) hp
    (⟦SmoothCube.toGenLoop ⟨ContinuousMap.id _, rfl⟩⟧ : π_ 7 (Sphere 7) (spherePole 7)) = _
  rw [pointedMap_mk]
  rfl

theorem degreeMap_pole : degreeMap (spherePole 7) = baseSphereHomeomorph north :=
  congrArg baseSphereHomeomorph sphereMap_pole

theorem degreeMap_cubeIdentity :
    pointedMap degreeMap (spherePole 7) (baseSphereHomeomorph north) degreeMap_pole
      cubeIdentityClass =
      homeomorphMulEquiv (N := Fin 7) baseSphereHomeomorph north
        (SmoothCube.sphereClass basedSphereMap) :=
  map_cubeIdentity_homeomorph basedSphereMap baseSphereHomeomorph degreeMap degreeMap_pole rfl

theorem degreeMap_pointed_surjective :
    Function.Surjective (pointedMap (N := Fin 7) degreeMap (spherePole 7)
      (baseSphereHomeomorph north) degreeMap_pole) :=
  (sphereSevenMap_generates_iff_surjective degreeMap (spherePole 7)
    (baseSphereHomeomorph north) degreeMap_pole).mp
      (sphereSevenMap_generator_generates degreeMap (spherePole 7)
        (baseSphereHomeomorph north) degreeMap_pole degreeMap_degree_natAbs)

theorem sphereClass_generates :
    Function.Surjective (fun k : ℤ ↦ (SmoothCube.sphereClass basedSphereMap) ^ k) := by
  have h := (CyclicGenerators.map_generates_iff
    (pointedMap (N := Fin 7) degreeMap (spherePole 7) (baseSphereHomeomorph north)
      degreeMap_pole) cubeIdentityClass cubeIdentity_generates).mpr degreeMap_pointed_surjective
  rw [degreeMap_cubeIdentity] at h
  exact (CyclicGenerators.equiv_generates_iff
    (homeomorphMulEquiv (N := Fin 7) baseSphereHomeomorph north) _).mp h

theorem sphereClass_degree_natAbs :
    Int.natAbs (baseDegreeEquiv (SmoothCube.sphereClass basedSphereMap)).toAdd = 1 :=
  generating_integer_coordinate baseDegreeEquiv _ sphereClass_generates

theorem nu_generates : Function.Surjective (fun k : ℤ ↦ QuaternionSamelson.nu ^ k) := by
  have h := (CyclicGenerators.map_generates_iff (connectingHom 6)
    (SmoothCube.sphereClass basedSphereMap) sphereClass_generates).mpr connecting_six_surjective
  change Function.Surjective (fun k : ℤ ↦
    (connecting 6 (SmoothCube.sphereClass basedSphereMap)) ^ k) at h
  rw [connecting_sphereClass_nu] at h
  exact (CyclicGenerators.equiv_generates_iff fiberEquiv QuaternionSamelson.nu).mp h

theorem samelsonSubgroup_eq_top : QuaternionSamelson.samelsonSubgroup = ⊤ := by
  apply le_antisymm le_top
  intro a _
  obtain ⟨k, rfl⟩ := nu_generates a
  exact Subgroup.zpow_mem_zpowers _ _

end NoExoticSixSphere.QuaternionCommutatorNativeSphere
