import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFirstStem
import Wikipedia.HopfProblem.DegreeCollapseHopfSecondStemComposition

/-!
# The original middle sixth-stem suspension is surjective

The nonzero ninth class of S5 is the first suspension of the actual
quaternionic composite. Its next suspension vanishes. EHP therefore
places this nonzero class in the image of the original S5 attaching map.
The exact boundary-coordinate comparison forces the actual meridian
representative to be nonzero. Its already detected first-stem action
then proves the required middle suspension is surjective.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MiddleSuspensionSurjective

open NoExoticSixSphere SmoothCube CubicalSphereSuspension JamesSphere

theorem quaternionic_suspension_generator :
    hom 8 4 (sphereClass QuaternionicHopfFirstStem.firstComposite) =
      FiveSphereNinth.generator :=
  (FiveSphereNinth.eq_one_or_generator _).resolve_left
    QuaternionicHopfFirstStem.firstComposite_suspension_ne_one

theorem generator_suspension : hom 9 5 FiveSphereNinth.generator = 1 := by
  rw [← quaternionic_suspension_generator]
  exact QuaternionicHopfFirstStem.firstComposite_double_suspension

theorem ninth_suspension_eq_one (c : π_ 9 (Sphere 5) (spherePole 5)) :
    hom 9 5 c = 1 := by
  rcases FiveSphereNinth.eq_one_or_generator c with rfl | rfl
  · exact map_one _
  · exact generator_suspension

theorem sixth_sphere_tenth_eq_one (c : π_ 10 (Sphere 6) (spherePole 6)) : c = 1 := by
  obtain ⟨b, rfl⟩ := hom_surjective (by decide : 9 + 2 < 2 * (5 + 1)) c
  exact ninth_suspension_eq_one b

theorem attaching_nine_surjective :
    Function.Surjective (EHPCell.attachingHom 5 (by decide) 9) := by
  intro c
  exact (EHPCell.suspension_eq_one_iff_attaching 5 9
    (by decide) (by decide) c).mp (ninth_suspension_eq_one c)

theorem meridian_class_ne_one :
    sphereClass AttachingSmashHomotopy.meridianFiveMap ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := attaching_nine_surjective FiveSphereNinth.generator
  rw [FiveSphereAttachingGenerator.attaching_comparison,
    AttachingSmashHomotopy.sourceFiveHom_comparison] at hc
  obtain ⟨g, hg⟩ := sphereClass_surjective (by decide : 0 < 9)
    (FiveSphereAttachingGenerator.sourceChange 9 c)
  rw [← hg] at hc
  change sphereClass (SphereComposition.comp AttachingSmashHomotopy.meridianFiveMap g) =
    FiveSphereNinth.generator at hc
  have hn := (sphereClass_eq_one_iff_nullhomotopic (by decide)
    AttachingSmashHomotopy.meridianFiveMap).mp h
  have hz : sphereClass (SphereComposition.comp AttachingSmashHomotopy.meridianFiveMap g) = 1 :=
    (sphereClass_eq_one_iff_nullhomotopic (by decide) _).mpr (hn.comp_left g.val)
  exact FiveSphereNinth.generator_ne_one (hc.symm.trans hz)

theorem meridian_class_eq_generator :
    sphereClass AttachingSmashHomotopy.meridianFiveMap = FiveSphereNinth.generator :=
  (FiveSphereNinth.eq_one_or_generator _).resolve_left meridian_class_ne_one

theorem attaching_ten_injective :
    Function.Injective (EHPCell.attachingHom 5 (by decide) 10) :=
  FiveSphereAttachingGenerator.attaching_ten_injective_iff.mpr
    (HopfSecondStemComposition.meridianImage_ne_one_iff.mpr meridian_class_ne_one)

theorem middle_suspension_surjective : Function.Surjective (hom 11 5) :=
  HopfSecondStemComposition.middle_suspension_surjective_of_meridianClass_ne_one
    meridian_class_ne_one

end Wikipedia.HopfProblem.DegreeCollapse.MiddleSuspensionSurjective
