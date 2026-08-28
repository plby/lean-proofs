import Wikipedia.HopfProblem.TriangleUniformizationGluingQuotient
import Wikipedia.HopfProblem.TriangleUniformizationGluingEdges
import Wikipedia.HopfProblem.TriangleUniformizationGluingReflectionAnalytic

/-!
# Holomorphicity of the actual invariant reflected function

Holomorphicity is supplied only on the original open half-Ford triangle.
The literal conjugate-reflection formula is holomorphic on its reflected
half.  The actual triangle transformations transport these two formulas
to every open tile.  The proved removable-edge theorem then gives
holomorphicity everywhere on the original upper half-plane.
-/

noncomputable section

open Set UpperHalfPlane Complex
open scoped Topology ContDiff Manifold ComplexConjugate

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods SpecialPeriods.Triangle

namespace BoundaryMap

variable (D : BoundaryMap)

theorem upstairsMap_holomorphicOn_half
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) halfFordInterior) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap halfFordInterior := by
  apply hd.congr
  intro z hz
  have hclosed := halfFordInterior_subset_halfFordRegion hz
  rw [D.upstairsMap_of_mem hclosed.1, D.foldedFordMap_of_left hclosed.2]

theorem upstairsMap_holomorphicOn_reflected_half
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) halfFordInterior) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap (rightReflection '' halfFordInterior) := by
  have href := contMDiffOn_conj_rightReflection halfFordInterior_isOpen hd
  apply href.congr
  rintro z ⟨w, hw, rfl⟩
  have hclosed := halfFordInterior_subset_halfFordRegion hw
  rw [D.upstairsMap_of_mem (rightReflection_mapsTo_fordRegion hclosed.1)]
  exact D.foldedFordMap_eqOn_right ⟨w, hclosed, rfl⟩

theorem upstairsMap_holomorphicOn_fold (b : Bool)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) halfFordInterior) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap (halfFold b '' halfFordInterior) := by
  cases b
  · change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap (id '' halfFordInterior)
    rw [image_id]
    exact D.upstairsMap_holomorphicOn_half hd
  · exact D.upstairsMap_holomorphicOn_reflected_half hd

theorem upstairsMap_holomorphicOn_tile (i : TriangleGroup × Bool)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) halfFordInterior) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap (halfTriangleOpenTile i) := by
  rw [halfTriangleOpenTile_eq]
  have hm : MapsTo (triangleGeometricRepresentation i.1⁻¹)
      (triangleGeometricRepresentation i.1 '' (halfFold i.2 '' halfFordInterior))
      (halfFold i.2 '' halfFordInterior) := by
    rintro z ⟨w, hw, rfl⟩
    rw [map_inv]
    change (triangleGeometricRepresentation i.1).symm
      (triangleGeometricRepresentation i.1 w) ∈ _
    rw [(triangleGeometricRepresentation i.1).symm_apply_apply w]
    exact hw
  have hc := (D.upstairsMap_holomorphicOn_fold i.2 hd).comp
    (triangleGeometricRepresentation_holomorphic i.1⁻¹).contMDiffOn hm
  apply hc.congr
  intro z _
  exact (D.upstairsMap_smul i.1⁻¹ z).symm

/-- The actual descended representative function is holomorphic upstairs
everywhere.  No analytic behavior along the tile edges is assumed. -/
theorem upstairsMap_holomorphic
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) halfFordInterior) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap :=
  contMDiff_of_continuous_of_halfTriangleOpenTiles D.upstairsMap_continuous
    (fun i => D.upstairsMap_holomorphicOn_tile i hd)

end BoundaryMap

namespace SignedHalfPlaneMap

variable (D : SignedHalfPlaneMap)

theorem upstairsMap_holomorphic
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.toFun : ℍ → ℂ) halfFordInterior) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap :=
  D.toBoundaryMap.upstairsMap_holomorphic hd

end SignedHalfPlaneMap
end Wikipedia.HopfProblem.TriangleUniformizationGluing
