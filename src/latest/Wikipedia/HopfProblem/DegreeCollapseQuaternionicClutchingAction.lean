import Wikipedia.HopfProblem.DegreeCollapseQuaternionicClutching
import Wikipedia.HopfProblem.DegreeCollapseSphereSelfMapSurjectivity
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCyclicQuotient
import Wikipedia.NoExoticSixSphere.SphereSixCubeGenerator

/-!
# The original two-frame clutching map generates pi6 and is injective on pi8

The original connecting map in degree eight is injective because its
kernel is the image of the already vanishing pi9(Sp(2)). The actual
connecting/suspension formula and the original stable-range suspension
then transfer this injectivity to the specified clutching map S6 -> S3.
In degree six the same formula proves surjectivity; the original
identity cube identifies the clutching class itself as a generator.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicClutching

open NoExoticSixSphere SmoothCube CubicalSphereSuspension SphereComposition
open Wikipedia.HomotopyGroupsOfSpheres QuaternionicFibration

theorem baseMap_native_bijective (k : ℕ) :
    Function.Bijective (HigherHomotopy.map (N := Fin k) baseMap.val baseMap.property) :=
  ⟨SphereSelfMapSurjectivity.native_homeomorph_injective baseSphereHomeomorph.symm
      baseMap.property,
    SphereSelfMapSurjectivity.native_homeomorph_surjective baseSphereHomeomorph.symm
      baseMap.property⟩

theorem sphereClutching_map {k : ℕ} [NeZero k]
    (c : π_ k (NoExoticSixSphere.Sphere 6) (spherePole 6)) :
    mapHom sphereClutching k c =
      HigherHomotopy.map (N := Fin k)
        (fiberSphereHomeomorph : C(northSubgroup, NoExoticSixSphere.Sphere 3))
        fiberSphereHomeomorph_one
        (connecting k (HigherHomotopy.map (N := Fin (k + 1))
          baseMap.val baseMap.property (hom k 6 c))) := by
  have h := QuaternionicConnectingSuspension.connecting_suspension_map
    (by decide : 0 < 6) baseLift c
  change connecting k (HigherHomotopy.map (N := Fin (k + 1))
      baseMap.val baseMap.property (hom k 6 c)) =
    HigherHomotopy.map (N := Fin k) clutching.val clutching.property c at h
  have hcomp := HigherHomotopy.map_comp clutching.val clutching.property
    (fiberSphereHomeomorph : C(northSubgroup, NoExoticSixSphere.Sphere 3))
      fiberSphereHomeomorph_one c
  exact hcomp.symm.trans (congrArg (HigherHomotopy.map (N := Fin k)
    (fiberSphereHomeomorph : C(northSubgroup, NoExoticSixSphere.Sphere 3))
      fiberSphereHomeomorph_one) h.symm)

theorem connecting_eight_injective : Function.Injective (connecting 8) := by
  let := QuaternionicPiNine.piNineSpTwo_subsingleton
  intro a b h
  have hab : connecting 8 (a / b) = 1 := by
    change connectingHom 8 (a / b) = 1
    rw [map_div]
    exact div_eq_one.mpr h
  obtain ⟨c, hc⟩ :=
    (projectionMap_range_eq_connecting_kernel (n := 8) (a / b)).mpr hab
  have hsource : c = 1 := Subsingleton.elim _ _
  have hone : projectionMap 8 (1 : π_ 9 SpTwo 1) = 1 := rfl
  exact div_eq_one.mp
    (hc.symm.trans ((congrArg (projectionMap 8) hsource).trans hone))

theorem sphereClutching_eight_injective :
    Function.Injective (mapHom sphereClutching 8) := by
  intro a b h
  have hf := SphereSelfMapSurjectivity.native_homeomorph_injective
    fiberSphereHomeomorph fiberSphereHomeomorph_one
    ((sphereClutching_map a).symm.trans (h.trans (sphereClutching_map b)))
  have hb := (baseMap_native_bijective 9).injective (connecting_eight_injective hf)
  exact hom_injective (by decide : 8 + 3 < 2 * (6 + 1)) hb

theorem sphereClutching_six_surjective :
    Function.Surjective (mapHom sphereClutching 6) := by
  have hnative : Function.Surjective
      (fun c : π_ 6 (NoExoticSixSphere.Sphere 6) (spherePole 6) ↦
        HigherHomotopy.map (N := Fin 6)
          (fiberSphereHomeomorph : C(northSubgroup, NoExoticSixSphere.Sphere 3))
          fiberSphereHomeomorph_one
          (connecting 6 (HigherHomotopy.map (N := Fin 7)
            baseMap.val baseMap.property (hom 6 6 c)))) :=
    (SphereSelfMapSurjectivity.native_homeomorph_surjective
      fiberSphereHomeomorph fiberSphereHomeomorph_one).comp
        (connecting_six_surjective.comp ((baseMap_native_bijective 7).surjective.comp
          (hom_surjective (by decide : 6 + 2 < 2 * (6 + 1)))))
  intro a
  obtain ⟨c, hc⟩ := hnative a
  exact ⟨c, (sphereClutching_map c).trans hc⟩

theorem sphereClutching_generates :
    Function.Surjective (fun k : ℤ ↦ (sphereClass sphereClutching) ^ k) := by
  intro a
  obtain ⟨c, hc⟩ := sphereClutching_six_surjective a
  obtain ⟨k, hk⟩ := SphereSixCube.identity_generates c
  change SphereSixCube.identityClass ^ k = c at hk
  refine ⟨k, ?_⟩
  calc
    (sphereClass sphereClutching) ^ k =
        (mapHom sphereClutching 6 SphereSixCube.identityClass) ^ k := rfl
    _ = mapHom sphereClutching 6 (SphereSixCube.identityClass ^ k) :=
      (map_zpow (mapHom sphereClutching 6) _ k).symm
    _ = a := by rw [hk, hc]

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicClutching
