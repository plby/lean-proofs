import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfPrecomposition
import Wikipedia.HopfProblem.DegreeCollapseHopfFirstStemComposition
import Wikipedia.NoExoticSixSphere.QuaternionicHopfUnitCoordinate
import Wikipedia.NoExoticSixSphere.StableSixFiniteDetection

/-!
# The actual quaternionic first-stem composite dies after two suspensions

The original polynomial Hopf map has Hopf coordinate of absolute value one.
Its composite with the joined nonzero S4-to-S3 map has nonzero first
suspension. Its twelvefold ordinary nullhomotopy, proved through the
orthogonal family, reflects down to two suspensions in the stable range.
All maps and suspensions retain their existing coordinates.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFirstStem

open NoExoticSixSphere SmoothCube CubicalSphereSuspension
open QuaternionicHopfPrecomposition JamesHopfComposition JamesSphere

def firstMap : SphereComposition.Based 4 3 :=
  (sphereClass_surjective (by decide : 0 < 4) (FirstStemGroup.generator 0)).choose

theorem firstMap_class : sphereClass firstMap = FirstStemGroup.generator 0 :=
  (sphereClass_surjective (by decide : 0 < 4) (FirstStemGroup.generator 0)).choose_spec

theorem joined_class_ne_one : sphereClass (joinedBasedMap firstMap) ≠ 1 := by
  intro h
  have hn := (sphereClass_eq_one_iff_nullhomotopic (by decide)
    (joinedBasedMap firstMap)).mp h
  have hi := (joinedMap_nullhomotopic_iff firstMap.val).mp hn
  have hf := (SphereMapSuspension.iterate_nullhomotopic_iff
    (by decide : 4 + 3 < 2 * (3 + 1)) firstMap.val 4).mp hi
  have hc := (sphereClass_eq_one_iff_nullhomotopic (by decide) firstMap).mpr hf
  rw [firstMap_class] at hc
  exact FirstStemGroup.generator_ne_one 0 hc

theorem joined_class : sphereClass (joinedBasedMap firstMap) = FirstStemGroup.generator 4 :=
  (FirstStemGroup.eq_one_or_generator 4 _).resolve_left joined_class_ne_one

def firstComposite : SphereComposition.Based 8 4 := composite firstMap

theorem firstComposite_class :
    sphereClass firstComposite = sphereClass (SphereLiftFamily.compose QuaternionicHopf.basedMap
      (productBasedMap HopfFirstStemComposition.firstStemMap)) := by
  have h := joined_class.trans HopfFirstStemComposition.suspendedFirstStem_class.symm
  exact congrArg (SphereComposition.mapHom QuaternionicHopf.basedMap 8) h

theorem hopf_coordinate_natAbs :
    Int.natAbs (Wikipedia.HomotopyGroupsOfSpheres.pi7_sphere_seven_mulEquiv (spherePole 7)
      (sphereClass (hopfRepresentative QuaternionicHopf.basedMap))).toAdd = 1 := by
  rw [hopfRepresentative_class]
  exact QuaternionicHopf.hopfNumber_natAbs

theorem hopf_power : ∃ k : ℤ,
    sphereClass (hopfRepresentative QuaternionicHopf.basedMap) =
      sphereClass (⟨ContinuousMap.id _, rfl⟩ : SphereComposition.Based 7 7) ^ k ∧
        Int.natAbs k = 1 := by
  obtain ⟨k, hk⟩ := AttachingSquare.cubeIdentity_generates
    (sphereClass (hopfRepresentative QuaternionicHopf.basedMap))
  refine ⟨k, hk.symm, ?_⟩
  have h := hopf_coordinate_natAbs
  rw [← hk, map_zpow] at h
  change Int.natAbs (k • AttachingSquare.cubeIdentitySign) = 1 at h
  rwa [Int.zsmul_eq_mul, Int.natAbs_mul, AttachingSquare.cubeIdentitySign_natAbs, mul_one] at h

theorem firstComposite_hopf_ne_one :
    SuspensionComparison.orderedHopfHom 3 (by decide) 7 (sphereClass firstComposite) ≠ 1 := by
  rw [firstComposite_class, hopf_precomposition]
  obtain ⟨k, hk, habs⟩ := hopf_power
  rw [SuspendedPrecomposition.compose_power HopfFirstStemComposition.firstStemMap k hk]
  change sphereClass (productBasedMap HopfFirstStemComposition.firstStemMap) ^ k ≠ 1
  rw [HopfFirstStemComposition.suspendedFirstStem_class]
  have hc : k = 1 ∨ k = -1 := Int.natAbs_eq_natAbs_iff.mp habs
  rcases hc with rfl | rfl
  · simpa only [zpow_one] using FirstStemGroup.generator_ne_one 4
  · intro h
    apply FirstStemGroup.generator_ne_one 4
    have hi := congrArg (fun c : π_ 8 (Sphere 7) (spherePole 7) ↦ c⁻¹) h
    simpa only [zpow_neg_one, inv_inv, inv_one] using hi

theorem firstComposite_suspension_ne_one :
    hom 8 4 (sphereClass firstComposite) ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := (EHPCell.suspension_eq_one_iff_attaching 4 8
    (by decide) (by decide) (sphereClass firstComposite)).mp h
  have hh := congrArg (SuspensionComparison.orderedHopfHom 3 (by decide) 7) hc
  rw [HopfFirstStemComposition.hopf_attaching_eight] at hh
  exact firstComposite_hopf_ne_one hh.symm

theorem composite_two_suspensions_nullhomotopic (g : SphereComposition.Based 4 3) :
    (SphereMapSuspension.iterate (composite g).val 2).Nullhomotopic := by
  have h := composite_twelve_suspensions_nullhomotopic g
  change (SphereMapSuspension.iterate
    (SphereMapSuspension.iterate (composite g).val 2) 10).Nullhomotopic at h
  exact (SphereMapSuspension.iterate_nullhomotopic_iff
    (by decide : 10 + 3 < 2 * (6 + 1)) _ 10).mp h

theorem composite_double_suspension (g : SphereComposition.Based 4 3) :
    hom 9 5 (hom 8 4 (sphereClass (composite g))) = 1 := by
  rw [hom_sphereClass]
  apply (hom_sphereClass_eq_one_iff (productBasedMap (composite g))).mpr
  apply (iterate_product_nullhomotopic_iff (composite g) 1).mpr
  exact composite_two_suspensions_nullhomotopic g

theorem firstComposite_double_suspension :
    hom 9 5 (hom 8 4 (sphereClass firstComposite)) = 1 :=
  composite_double_suspension firstMap

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFirstStem
