import Wikipedia.HopfProblem.DegreeCollapseSecondStemGroup
import Wikipedia.HopfProblem.DegreeCollapseFiveSphereNinth
import Wikipedia.HopfProblem.DegreeCollapseFiveSphereAttachingGenerator

/-!
# The further first-stem action on the actual pi9(S5) generator

The proved nonzero first-stem square detects a second composition under
the original James--Hopf map. The original S4 attaching image has zero
Hopf image here because its Hopf coefficient is twice a unit and the
second stem has exponent two. EHP therefore preserves this composition
under suspension to S5. Every nonzero pi9(S5) class acts nontrivially on
the first-stem generator. Only nonvanishing of the actual S5 attaching
class itself remains for the middle suspension argument.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.HopfSecondStemComposition

open NoExoticSixSphere SmoothCube SphereLiftFamily CubicalSphereSuspension JamesSphere
open JamesHopfComposition HopfFirstStemComposition

def nextFirstStemMap : SphereComposition.Based 8 7 :=
  (sphereClass_surjective (by decide : 0 < 8) (FirstStemGroup.generator 4)).choose

theorem nextFirstStemMap_class : sphereClass nextFirstStemMap = FirstStemGroup.generator 4 :=
  (sphereClass_surjective (by decide : 0 < 8) (FirstStemGroup.generator 4)).choose_spec

theorem nextFirstStemMap_suspension_class :
    sphereClass (productBasedMap nextFirstStemMap) = FirstStemGroup.generator 5 := by
  rw [← hom_sphereClass, nextFirstStemMap_class, FirstStemGroup.generator_suspension]

theorem nextFirstStemMap_double_suspension_class :
    sphereClass (productBasedMap (productBasedMap nextFirstStemMap)) =
      FirstStemGroup.generator 6 := by
  rw [← hom_sphereClass, nextFirstStemMap_suspension_class, FirstStemGroup.generator_suspension]

def secondComposite : SphereComposition.Based 9 4 :=
  compose firstComposite (productBasedMap nextFirstStemMap)

theorem secondComposite_hopf_ne_one :
    SuspensionComparison.orderedHopfHom 3 (by decide) 8 (sphereClass secondComposite) ≠ 1 := by
  rw [secondComposite, hopf_precomposition]
  exact SecondStemGroup.firstStem_composite_ne_one 4 (hopfRepresentative firstComposite)
    (productBasedMap nextFirstStemMap)
    ((hopfRepresentative_class firstComposite).trans firstComposite_hopf)
    nextFirstStemMap_suspension_class

theorem hopf_attaching_nine (c : π_ 9 (Sphere 7) (spherePole 7)) :
    SuspensionComparison.orderedHopfHom 3 (by decide) 8
      (EHPCell.attachingHom 4 (by decide) 9 c) = 1 := by
  obtain ⟨a, rfl⟩ := hom_surjective (by decide : 8 + 2 < 2 * (6 + 1)) c
  obtain ⟨g, rfl⟩ := sphereClass_surjective (by decide : 0 < 8) a
  rw [hom_sphereClass]
  change SuspensionComparison.orderedHopfHom 3 (by decide) 8
    (sphereClass (compose FourSphereDesuspension.attachingMap (productBasedMap g))) = 1
  rw [hopf_precomposition]
  obtain ⟨k, hk, habs⟩ := attachingHopf_power
  rw [SuspendedPrecomposition.compose_power g k hk]
  have hp := SecondStemGroup.pow_two 4
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

theorem secondComposite_suspension_ne_one : hom 9 4 (sphereClass secondComposite) ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := (EHPCell.suspension_eq_one_iff_attaching 4 9
    (by decide) (by decide) (sphereClass secondComposite)).mp h
  have hh := congrArg (SuspensionComparison.orderedHopfHom 3 (by decide) 8) hc
  rw [hopf_attaching_nine] at hh
  exact secondComposite_hopf_ne_one hh.symm

def suspendedSecondComposite : SphereComposition.Based 10 5 := productBasedMap secondComposite

theorem suspendedSecondComposite_ne_one : sphereClass suspendedSecondComposite ≠ 1 := by
  rw [suspendedSecondComposite, ← hom_sphereClass]
  exact secondComposite_suspension_ne_one

theorem candidate_composite_ne_one :
    sphereClass (compose suspendedComposite
      (productBasedMap (productBasedMap nextFirstStemMap))) ≠ 1 := by
  have h : suspendedSecondComposite = compose suspendedComposite
      (productBasedMap (productBasedMap nextFirstStemMap)) :=
    SecondStemSuspension.product_compose firstComposite (productBasedMap nextFirstStemMap)
  exact fun he ↦ suspendedSecondComposite_ne_one ((congrArg sphereClass h).trans he)

theorem nonzero_ninth_firstStem_action (f : SphereComposition.Based 9 5)
    (hf : sphereClass f ≠ 1) :
    HigherHomotopy.map f.val f.property (FirstStemGroup.generator 6) ≠ 1 := by
  have hclass : sphereClass f = sphereClass suspendedComposite :=
    (FiveSphereNinth.eq_one_or_generator (sphereClass f)).resolve_left hf
  have h : HigherHomotopy.map f.val f.property (FirstStemGroup.generator 6) =
      sphereClass (compose suspendedComposite
        (productBasedMap (productBasedMap nextFirstStemMap))) :=
    (congrArg (HigherHomotopy.map f.val f.property)
      nextFirstStemMap_double_suspension_class.symm).trans
        (GroupSpherePrecomposition.compose_class_congr hclass
          (productBasedMap (productBasedMap nextFirstStemMap)))
  exact fun he ↦ candidate_composite_ne_one (h.symm.trans he)

theorem firstStem_action_eq (f : SphereComposition.Based 9 5) :
    HigherHomotopy.map f.val f.property (FirstStemGroup.generator 6) =
      SuspendedPrecomposition.hom (productBasedMap nextFirstStemMap) (sphereClass f) :=
  (congrArg (HigherHomotopy.map f.val f.property)
    nextFirstStemMap_double_suspension_class.symm).trans
      (SuspendedPrecomposition.hom_class (productBasedMap nextFirstStemMap) f).symm

theorem firstStem_action_ne_one_iff (f : SphereComposition.Based 9 5) :
    HigherHomotopy.map f.val f.property (FirstStemGroup.generator 6) ≠ 1 ↔ sphereClass f ≠ 1 := by
  constructor
  · intro h hf
    apply h
    rw [firstStem_action_eq, hf, map_one]
  · exact nonzero_ninth_firstStem_action f

theorem meridianImage_ne_one_iff : FiveSphereAttachingGenerator.meridianImage ≠ 1 ↔
    sphereClass AttachingSmashHomotopy.meridianFiveMap ≠ 1 :=
  firstStem_action_ne_one_iff AttachingSmashHomotopy.meridianFiveMap

theorem middle_suspension_surjective_of_meridianClass_ne_one
    (h : sphereClass AttachingSmashHomotopy.meridianFiveMap ≠ 1) :
    Function.Surjective (hom 11 5) :=
  FiveSphereAttachingGenerator.suspension_surjective_of_meridian_ne_one
    (meridianImage_ne_one_iff.mpr h)

end Wikipedia.HopfProblem.DegreeCollapse.HopfSecondStemComposition
