import Wikipedia.HopfProblem.DegreeCollapseQuaternionicSeven
import Wikipedia.HopfProblem.DegreeCollapseHopfFirstStemComposition

/-!
# The original S4 attaching action in degrees seven and eight

In degree seven its nonzero integral Hopf coefficient makes the action
injective. In degree eight, the actual quaternionic retraction and
clutching action give injectivity. The first statement, together with
the original EHP sequence, proves that pi8(S4) suspends onto pi9(S5).
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FourSphereLowAttaching

open NoExoticSixSphere SmoothCube SphereComposition SphereLiftFamily CubicalSphereSuspension
open JamesSphere JamesRetractionComposition
open Wikipedia.HomotopyGroupsOfSpheres QuaternionicFibration
open QuaternionicClutching ThreeSphereGeneratorAction FourSphereDesuspension

theorem liftedClutching_seven_injective :
    Function.Injective (HigherHomotopy.map (N := Fin 7)
      (fiberLift sphereClutching).val (fiberLift sphereClutching).property) := by
  intro a b h
  apply QuaternionicSeven.sphereClutching_seven_injective
  apply SphereSelfMapSurjectivity.native_homeomorph_injective fiberSphereHomeomorph.symm
    (fiberSphereHomeomorph.symm_apply_eq.mpr fiberSphereHomeomorph_one.symm)
  exact (fiberLift_native_map sphereClutching a).symm.trans
    (h.trans (fiberLift_native_map sphereClutching b))

theorem generator_seven_injective (f : Based 6 3)
    (hf : Function.Surjective (fun k : ℤ ↦ sphereClass f ^ k)) :
    Function.Injective (mapHom f 7) := by
  have hi := GroupSpherePrecomposition.injective_of_generates
    (fiberLift_generates f hf) liftedClutching_seven_injective
  intro a b h
  apply hi
  rw [fiberLift_native_map f a, fiberLift_native_map f b, h]

theorem attaching_eight_injective :
    Function.Injective (EHPCell.attachingHom 4 (by decide) 8) := by
  intro a b hab
  obtain ⟨c, rfl⟩ := hom_surjective (by decide : 7 + 2 < 2 * (6 + 1)) a
  obtain ⟨d, rfl⟩ := hom_surjective (by decide : 7 + 2 < 2 * (6 + 1)) b
  obtain ⟨g, rfl⟩ := sphereClass_surjective (by decide : 0 < 7) c
  obtain ⟨h, rfl⟩ := sphereClass_surjective (by decide : 0 < 7) d
  rw [hom_sphereClass, hom_sphereClass] at hab
  change sphereClass (compose attachingMap (productBasedMap g)) =
    sphereClass (compose attachingMap (productBasedMap h)) at hab
  have hr := congrArg (ThreeRetraction.sectionHom 7) hab
  rw [retraction_precomposition, retraction_precomposition] at hr
  have hclass : sphereClass g = sphereClass h :=
    generator_seven_injective (retractionRepresentative attachingMap)
      retractionRepresentative_generates hr
  exact congrArg (hom 7 6) hclass

theorem attaching_seven_injective :
    Function.Injective (EHPCell.attachingHom 4 (by decide) 7) := by
  let D : ℤ := (pi7_sphere_seven_mulEquiv (spherePole 7)
    (SphereFourSeventh.hopf (sphereClass attachingMap))).toAdd
  have hD : D.natAbs = 2 := by
    dsimp only [D, SphereFourSeventh.hopf]
    simpa only [JamesHopfComposition.hopfRepresentative_class] using
      HopfFirstStemComposition.attachingHopf_coordinate_natAbs
  have hz : D ≠ 0 := by
    intro h
    rw [h] at hD
    norm_num at hD
  intro a b h
  obtain ⟨k, rfl⟩ := AttachingSquare.cubeIdentity_generates a
  obtain ⟨l, rfl⟩ := AttachingSquare.cubeIdentity_generates b
  rw [map_zpow, map_zpow] at h
  change sphereClass attachingMap ^ k = sphereClass attachingMap ^ l at h
  have hh := congrArg SphereFourSeventh.hopf h
  rw [map_zpow, map_zpow] at hh
  have hc := congrArg (pi7_sphere_seven_mulEquiv (spherePole 7)) hh
  rw [map_zpow, map_zpow] at hc
  have hd := congrArg Multiplicative.toAdd hc
  change k • D = l • D at hd
  rw [Int.zsmul_eq_mul, Int.zsmul_eq_mul] at hd
  have hkl : k = l := mul_right_cancel₀ hz hd
  rw [hkl]

theorem connecting_seven_injective :
    Function.Injective (EHP.connectingHomMetastable 4 7 (by decide) (by decide)) := by
  intro a b hab
  obtain ⟨c, rfl⟩ := (EHPCell.comparisonHom_bijective 4 7
    (by decide) (by decide)).surjective a
  obtain ⟨d, rfl⟩ := (EHPCell.comparisonHom_bijective 4 7
    (by decide) (by decide)).surjective b
  rw [EHPCell.connecting_comparisonHom, EHPCell.connecting_comparisonHom] at hab
  exact congrArg (EHPCell.comparisonHom 4 (by decide) 7) (attaching_seven_injective hab)

theorem hopf_nine_eq_one (x : π_ 9 (NoExoticSixSphere.Sphere 5) (spherePole 5)) :
    SuspensionComparison.orderedHopfHom 4 (by decide) 8 x = 1 := by
  apply connecting_seven_injective
  exact ((EHP.connecting_eq_one_iff_metastable 4 7 (by decide) (by decide) _).mpr
    ⟨x, rfl⟩).trans
      (map_one (EHP.connectingHomMetastable 4 7 (by decide) (by decide))).symm

theorem suspension_eight_surjective : Function.Surjective (hom 8 4) := by
  intro x
  exact (EHP.hopf_eq_one_iff_metastable 4 7 (by decide) (by decide) x).mp
    (hopf_nine_eq_one x)

end Wikipedia.HopfProblem.DegreeCollapse.FourSphereLowAttaching
