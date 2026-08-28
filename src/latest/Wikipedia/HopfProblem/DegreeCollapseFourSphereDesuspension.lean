import Wikipedia.HopfProblem.DegreeCollapseJamesRetractionComposition
import Wikipedia.HopfProblem.DegreeCollapseThreeSphereGeneratorAction
import Wikipedia.HopfProblem.DegreeCollapseSixthSphereFourImage
import Wikipedia.NoExoticSixSphere.JamesAttachingQuaternionClass
import Wikipedia.NoExoticSixSphere.QuaternionCommutatorNativePrimitivity

/-!
# The original suspension pi10(S4) -> pi11(S5) is surjective

The original second James-cell attaching map acts injectively on pi9(S7).
After one actual desuspension, its quaternionic James retraction acts by
a generator of pi6(S3). The original two-frame fibration proves that
this action is injective on pi8(S6). Metastable EHP exactness then forces
the James--Hopf map to vanish and proves the claimed suspension
surjectivity. No unstable sphere-group table is used.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FourSphereDesuspension

open NoExoticSixSphere SmoothCube SphereLiftFamily CubicalSphereSuspension
open JamesSphere JamesRetractionComposition
open Wikipedia.HomotopyGroupsOfSpheres

def attachingMap : SphereComposition.Based 7 4 :=
  ⟨EHPCell.attachingMap 4 (by decide), EHPCell.attachingMap_pole 4 (by decide)⟩

theorem attachingMap_class :
    sphereClass attachingMap =
      SphereFourAttaching.attachingClass ^ AttachingSquare.cubeIdentitySign := by
  change EHPCell.attachingHom 4 (by decide) 7 AttachingSquare.cubeIdentityClass = _
  rw [AttachingSquare.cubeIdentity_eq_generator_power, map_zpow]
  rfl

theorem inverse_generates {G : Type*} [Group G] (a : G)
    (ha : Function.Surjective (fun k : ℤ ↦ a ^ k)) :
    Function.Surjective (fun k : ℤ ↦ a⁻¹ ^ k) := by
  intro b
  obtain ⟨k, hk⟩ := ha b
  refine ⟨-k, ?_⟩
  change (a⁻¹) ^ (-k) = b
  rw [zpow_neg, inv_zpow, inv_inv]
  exact hk

theorem original_retraction_generates :
    Function.Surjective (fun k : ℤ ↦
      (ThreeRetraction.sectionHom 6 SphereFourAttaching.attachingClass) ^ k) := by
  have hnu : Function.Surjective (fun k : ℤ ↦
      (ThreeRetraction.quaternionSphereEquiv QuaternionSamelson.nu) ^ k) :=
    (CyclicGenerators.equiv_generates_iff ThreeRetraction.quaternionSphereEquiv
      QuaternionSamelson.nu).mpr QuaternionCommutatorNativeSphere.nu_generates
  rcases ThreeRetraction.originalAttaching_retraction_eq_nu_or_inv with h | h
  · rw [h]
    exact hnu
  · rw [h]
    exact inverse_generates _ hnu

theorem retractionRepresentative_generates :
    Function.Surjective (fun k : ℤ ↦
      sphereClass (retractionRepresentative attachingMap) ^ k) := by
  rw [retractionRepresentative_class, attachingMap_class, map_zpow]
  rcases AttachingSquare.cubeIdentitySign_eq_one_or_neg_one with h | h
  · rw [h, zpow_one]
    exact original_retraction_generates
  · rw [h, zpow_neg_one]
    exact inverse_generates _ original_retraction_generates

theorem attaching_suspended_class (g : SphereComposition.Based 8 6) :
    sphereClass (compose attachingMap (productBasedMap g)) =
      EHPCell.attachingHom 4 (by decide) 9 (hom 8 6 (sphereClass g)) := by
  rw [hom_sphereClass]
  rfl

theorem attaching_nine_injective :
    Function.Injective (EHPCell.attachingHom 4 (by decide) 9) := by
  intro a b hab
  obtain ⟨c, rfl⟩ := hom_surjective (by decide : 8 + 2 < 2 * (6 + 1)) a
  obtain ⟨d, rfl⟩ := hom_surjective (by decide : 8 + 2 < 2 * (6 + 1)) b
  obtain ⟨g, rfl⟩ := sphereClass_surjective (by decide : 0 < 8) c
  obtain ⟨h, rfl⟩ := sphereClass_surjective (by decide : 0 < 8) d
  have hcomp : sphereClass (compose attachingMap (productBasedMap g)) =
      sphereClass (compose attachingMap (productBasedMap h)) := by
    rw [attaching_suspended_class, attaching_suspended_class]
    exact hab
  have hr := congrArg (ThreeRetraction.sectionHom 8) hcomp
  rw [retraction_precomposition, retraction_precomposition] at hr
  have hclass : sphereClass g = sphereClass h :=
    ThreeSphereGeneratorAction.generator_eight_injective
      (retractionRepresentative attachingMap) retractionRepresentative_generates hr
  exact congrArg (hom 8 6) hclass

theorem connecting_nine_injective :
    Function.Injective (EHP.connectingHomMetastable 4 9 (by decide) (by decide)) := by
  intro a b hab
  obtain ⟨c, rfl⟩ := (EHPCell.comparisonHom_bijective 4 9
    (by decide) (by decide)).surjective a
  obtain ⟨d, rfl⟩ := (EHPCell.comparisonHom_bijective 4 9
    (by decide) (by decide)).surjective b
  rw [EHPCell.connecting_comparisonHom, EHPCell.connecting_comparisonHom] at hab
  exact congrArg (EHPCell.comparisonHom 4 (by decide) 9) (attaching_nine_injective hab)

theorem hopf_eq_one (x : π_ 11 (NoExoticSixSphere.Sphere 5) (spherePole 5)) :
    SuspensionComparison.orderedHopfHom 4 (by decide) 10 x = 1 := by
  apply connecting_nine_injective
  exact ((EHP.connecting_eq_one_iff_metastable 4 9 (by decide) (by decide) _).mpr
    ⟨x, rfl⟩).trans
      (map_one (EHP.connectingHomMetastable 4 9 (by decide) (by decide))).symm

theorem suspension_surjective : Function.Surjective (hom 10 4) := by
  intro x
  exact (EHP.hopf_eq_one_iff_metastable 4 9 (by decide) (by decide) x).mp (hopf_eq_one x)

theorem stable_eq_one_or_square (x : π_ 11 (NoExoticSixSphere.Sphere 5) (spherePole 5)) :
    CubicalStableSix.ofNative (k := 3) x = 1 ∨
      CubicalStableSix.ofNative (k := 3) x = StableThirdComposition.stableSquare := by
  obtain ⟨a, rfl⟩ := suspension_surjective x
  have he := CubicalStableSix.ofNative_stepHom 2 a
  rcases SixthSphereFourImage.stable_eq_one_or_square a with h | h
  · exact Or.inl (he.trans h)
  · exact Or.inr (he.trans h)

end Wikipedia.HopfProblem.DegreeCollapse.FourSphereDesuspension
