import Wikipedia.HopfProblem.DegreeCollapseJamesHopfComposition
import Wikipedia.HopfProblem.DegreeCollapseSuspendedPrecomposition
import Wikipedia.HopfProblem.DegreeCollapseFirstStemGroup
import Wikipedia.HopfProblem.DegreeCollapseFourSphereDesuspension
import Wikipedia.NoExoticSixSphere.JamesSphereAttachingHopfCoefficient

/-!
# A detected first-stem composition and its nonzero suspension into S5

Choose an actual S7-to-S4 representative whose original James--Hopf
image is the identity class. Composing with the suspended nonzero
first-stem class has nonzero Hopf image. The original S4 attaching
image has zero Hopf image in this degree: its top Hopf coefficient
has absolute value two, and suspended precomposition preserves powers.
EHP exactness therefore shows that the specified composition remains
nonzero after the original suspension to S5.
This does not identify it with the original S5 attaching class.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.HopfFirstStemComposition

open NoExoticSixSphere SmoothCube SphereLiftFamily CubicalSphereSuspension
open JamesSphere JamesHopfComposition

def unitHopfMap : SphereComposition.Based 7 4 :=
  (sphereClass_surjective (by decide : 0 < 7)
    (SphereFourSeventh.hopf_surjective AttachingSquare.cubeIdentityClass).choose).choose

theorem unitHopfMap_projection :
    SphereFourSeventh.hopf (sphereClass unitHopfMap) = AttachingSquare.cubeIdentityClass :=
  (congrArg SphereFourSeventh.hopf
    (sphereClass_surjective (by decide : 0 < 7)
      (SphereFourSeventh.hopf_surjective
        AttachingSquare.cubeIdentityClass).choose).choose_spec).trans
    (SphereFourSeventh.hopf_surjective AttachingSquare.cubeIdentityClass).choose_spec

def firstStemMap : SphereComposition.Based 7 6 :=
  (sphereClass_surjective (by decide : 0 < 7) (FirstStemGroup.generator 3)).choose

theorem firstStemMap_class : sphereClass firstStemMap = FirstStemGroup.generator 3 :=
  (sphereClass_surjective (by decide : 0 < 7) (FirstStemGroup.generator 3)).choose_spec

theorem suspendedFirstStem_class :
    sphereClass (productBasedMap firstStemMap) = FirstStemGroup.generator 4 := by
  rw [← hom_sphereClass, firstStemMap_class]
  exact FirstStemGroup.generator_suspension 3

def firstComposite : SphereComposition.Based 8 4 :=
  compose unitHopfMap (productBasedMap firstStemMap)

theorem firstComposite_hopf :
    SuspensionComparison.orderedHopfHom 3 (by decide) 7 (sphereClass firstComposite) =
      FirstStemGroup.generator 4 := by
  rw [firstComposite, hopf_precomposition]
  have h : sphereClass (hopfRepresentative unitHopfMap) =
      sphereClass (⟨ContinuousMap.id _, rfl⟩ : SphereComposition.Based 7 7) :=
    (hopfRepresentative_class unitHopfMap).trans unitHopfMap_projection
  exact (GroupSpherePrecomposition.compose_class_congr h
    (productBasedMap firstStemMap)).trans suspendedFirstStem_class

theorem firstComposite_ne_one : sphereClass firstComposite ≠ 1 := by
  intro h
  exact FirstStemGroup.generator_ne_one 4
    (firstComposite_hopf.symm.trans
      ((congrArg (SuspensionComparison.orderedHopfHom 3 (by decide) 7) h).trans (map_one _)))

theorem attachingHopf_coordinate_natAbs :
    Int.natAbs (Wikipedia.HomotopyGroupsOfSpheres.pi7_sphere_seven_mulEquiv (spherePole 7)
      (sphereClass (hopfRepresentative FourSphereDesuspension.attachingMap))).toAdd = 2 := by
  rw [hopfRepresentative_class]
  change Int.natAbs (Wikipedia.HomotopyGroupsOfSpheres.pi7_sphere_seven_mulEquiv (spherePole 7)
    (SphereFourSeventh.hopf (sphereClass FourSphereDesuspension.attachingMap))).toAdd = 2
  rw [← SphereFourSeventh.groupEquiv_hopf, FourSphereDesuspension.attachingMap_class, map_zpow]
  change Int.natAbs (AttachingSquare.cubeIdentitySign • SphereFiveEighth.relation.1.toAdd) = 2
  rw [Int.zsmul_eq_mul, Int.natAbs_mul, AttachingSquare.cubeIdentitySign_natAbs,
    AttachingSquare.originalAttachingClass_hopf_natAbs_two, one_mul]

theorem attachingHopf_power : ∃ k : ℤ,
    sphereClass (hopfRepresentative FourSphereDesuspension.attachingMap) =
      sphereClass (⟨ContinuousMap.id _, rfl⟩ : SphereComposition.Based 7 7) ^ k ∧
        Int.natAbs k = 2 := by
  obtain ⟨k, hk⟩ := AttachingSquare.cubeIdentity_generates
    (sphereClass (hopfRepresentative FourSphereDesuspension.attachingMap))
  refine ⟨k, hk.symm, ?_⟩
  have h := attachingHopf_coordinate_natAbs
  rw [← hk, map_zpow] at h
  change Int.natAbs (k • AttachingSquare.cubeIdentitySign) = 2 at h
  rwa [Int.zsmul_eq_mul, Int.natAbs_mul, AttachingSquare.cubeIdentitySign_natAbs, mul_one] at h

theorem hopf_attaching_eight (c : π_ 8 (Sphere 7) (spherePole 7)) :
    SuspensionComparison.orderedHopfHom 3 (by decide) 7
      (EHPCell.attachingHom 4 (by decide) 8 c) = 1 := by
  obtain ⟨a, rfl⟩ := hom_surjective (by decide : 7 + 2 < 2 * (6 + 1)) c
  obtain ⟨g, rfl⟩ := sphereClass_surjective (by decide : 0 < 7) a
  rw [hom_sphereClass]
  change SuspensionComparison.orderedHopfHom 3 (by decide) 7
    (sphereClass (compose FourSphereDesuspension.attachingMap (productBasedMap g))) = 1
  rw [hopf_precomposition]
  obtain ⟨k, hk, habs⟩ := attachingHopf_power
  rw [SuspendedPrecomposition.compose_power g k hk]
  have hp := FirstStemGroup.pow_two 4
    (sphereClass (compose (⟨ContinuousMap.id _, rfl⟩ : SphereComposition.Based 7 7)
      (productBasedMap g)))
  have hc : k = 2 ∨ k = -2 := Int.natAbs_eq_natAbs_iff.mp habs
  rcases hc with rfl | rfl
  · exact hp
  · rw [zpow_neg]
    change (sphereClass (compose
      (⟨ContinuousMap.id _, rfl⟩ : SphereComposition.Based 7 7)
      (productBasedMap g)) ^ (2 : ℕ))⁻¹ = 1
    rw [hp, inv_one]

theorem firstComposite_suspension_ne_one :
    hom 8 4 (sphereClass firstComposite) ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := (EHPCell.suspension_eq_one_iff_attaching 4 8
    (by decide) (by decide) (sphereClass firstComposite)).mp h
  have hh := congrArg (SuspensionComparison.orderedHopfHom 3 (by decide) 7) hc
  rw [hopf_attaching_eight, firstComposite_hopf] at hh
  exact FirstStemGroup.generator_ne_one 4 hh.symm

def suspendedComposite : SphereComposition.Based 9 5 := productBasedMap firstComposite

theorem suspendedComposite_ne_one : sphereClass suspendedComposite ≠ 1 := by
  rw [suspendedComposite, ← hom_sphereClass]
  exact firstComposite_suspension_ne_one

end Wikipedia.HopfProblem.DegreeCollapse.HopfFirstStemComposition
