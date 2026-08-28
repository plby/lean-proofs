import Wikipedia.NoExoticSixSphere.CollapsedSubspaceCylinderPair

/-!
# The original cofibration quotient induces relative-homology isomorphisms

The actual upper-cylinder retraction, open-cover excision, and genuine
collapse map of pairs are all homology isomorphisms. Their literal
commuting square identifies the remaining map with the original quotient
`(X,A) -> (X/A,*)`. No compactness or homotopy-excision assertion is used.
-/

noncomputable section

open CategoryTheory Set
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.CollapsedSubspace

open CollapsedSubspaceCylinder

variable {X : Type} [TopologicalSpace X] (A : Set X) (a : A)

theorem quotient_relative_square (d : ℕ) :
    (RelativeSingularHomology.map (quotientMap A) (quotientMap_mapsTo A a) d).comp
      (RelativeSingularHomology.map (upperMap A) (upperMap_mapsTo A) d) =
    (RelativeSingularHomology.map (collapseMap A a) (collapseMap_mapsTo A a) d).comp
      (RelativeSingularHomology.excisionMap (upperSet A) (lowerSet A) d) := by
  change _ = (RelativeSingularHomology.map (collapseMap A a) (collapseMap_mapsTo A a) d).comp
    (RelativeSingularHomology.map (subtypeInclusion (upperSet A))
      (show Set.MapsTo (subtypeInclusion (upperSet A)) (overlapSet A) (lowerSet A)
        from fun _ hp ↦ hp) d)
  rw [← RelativeSingularHomology.map_comp, ← RelativeSingularHomology.map_comp]
  exact RelativeSingularHomology.map_congr _ _ (collapse_upper_factor A a).symm d

theorem relativeHomology_bijective
    (hA : HomotopyExtension.HasHomotopyExtension (CollapsedSubspacePushout.inclusion A))
    (d : ℕ) : Function.Bijective
      (RelativeSingularHomology.map (quotientMap A) (quotientMap_mapsTo A a) d) := by
  have hc : upperSet A ∪ lowerSet A = Set.univ := by
    rw [Set.union_comm]
    exact DoubleMappingCylinder.cover
      (CollapsedSubspacePushout.inclusion A) (CollapsedSubspacePushout.toPoint A)
  have he := RelativeSingularHomology.excisionMap_bijective (upperSet A) (lowerSet A)
    (DoubleMappingCylinder.upper_isOpen _ _) (DoubleMappingCylinder.lower_isOpen _ _) hc d
  have hb : Function.Bijective
      ((RelativeSingularHomology.map (quotientMap A) (quotientMap_mapsTo A a) d).comp
        (RelativeSingularHomology.map (upperMap A) (upperMap_mapsTo A) d)) := by
    rw [quotient_relative_square]
    exact (collapseMap_relative_bijective A a hA d).comp he
  exact (Function.Bijective.of_comp_iff _ (upperMap_relative_bijective A d)).mp hb

end NoExoticSixSphere.CollapsedSubspace
