import Wikipedia.HopfProblem.TriangleUniformizationGluingFold

/-!
# Compact preimages for the folded Ford map

Properness of the supplied map on the single closed half-triangle
implies compact preimages on the full Ford polygon. The full preimage
is exactly the union of a compact left-half preimage and the reflection
of the compact preimage of the conjugate target set.
-/

noncomputable section

open Set UpperHalfPlane Complex
open scoped Topology MatrixGroups ComplexConjugate

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods SpecialPeriods.Triangle

namespace BoundaryMap

/-- Only properness of the given half-triangle map is assumed. -/
theorem foldedFordMap_compact_preimage (D : BoundaryMap)
    (hlocal : IsProperMap (fun z : halfFordRegion => D.toFun z))
    (K : Set ℂ) (hK : IsCompact K) :
    IsCompact (fordRegion ∩ D.foldedFordMap ⁻¹' K) := by
  have hhalf (L : Set ℂ) (hL : IsCompact L) :
      IsCompact (halfFordRegion ∩ D.toFun ⁻¹' L) := by
    have hs := (hlocal.isCompact_preimage hL).image continuous_subtype_val
    change IsCompact ((Subtype.val : halfFordRegion → ℍ) ''
      ((Subtype.val : halfFordRegion → ℍ) ⁻¹' (D.toFun ⁻¹' L))) at hs
    simpa only [Subtype.image_preimage_val] using hs
  have hconj : IsCompact ((conj : ℂ → ℂ) ⁻¹' K) :=
    Complex.conjCLE.toHomeomorph.isCompact_preimage.mpr hK
  have heq : fordRegion ∩ D.foldedFordMap ⁻¹' K =
      (halfFordRegion ∩ D.toFun ⁻¹' K) ∪
        rightReflection '' (halfFordRegion ∩ D.toFun ⁻¹' ((conj : ℂ → ℂ) ⁻¹' K)) := by
    ext z
    constructor
    · rintro ⟨hz, hKz⟩
      change D.foldedFordMap z ∈ K at hKz
      rw [← halfFordRegion_union_reflection] at hz
      rcases hz with hz | ⟨w, hw, rfl⟩
      · left
        refine ⟨hz, ?_⟩
        change D z ∈ K
        rwa [D.foldedFordMap_of_left hz.2] at hKz
      · right
        refine ⟨w, ⟨hw, ?_⟩, rfl⟩
        change conj (D w) ∈ K
        rwa [D.foldedFordMap_reflected w hw] at hKz
    · rintro (⟨hz, hKz⟩ | ⟨w, ⟨hw, hKw⟩, rfl⟩)
      · refine ⟨hz.1, ?_⟩
        change D.foldedFordMap z ∈ K
        rwa [D.foldedFordMap_of_left hz.2]
      · refine ⟨rightReflection_mapsTo_fordRegion hw.1, ?_⟩
        change D.foldedFordMap (rightReflection w) ∈ K
        rw [D.foldedFordMap_reflected w hw]
        exact hKw
  rw [heq]
  exact (hhalf K hK).union ((hhalf _ hconj).image rightReflection.continuous)

end BoundaryMap
end Wikipedia.HopfProblem.TriangleUniformizationGluing
