import Wikipedia.HopfProblem.SpecialPeriodsTriangleFundamentalRegion
import Wikipedia.HopfProblem.SpecialPeriodsTriangleDiscrete

/-!
# Orbit representatives in the actual triangle polygon

The proved discreteness of the explicit matrix group supplies the proper
discontinuity needed for the finite maximal-height argument.  Consequently
every actual triangle orbit meets the explicit Ford polygon.

This is a covering by translates, not yet a claim that interiors are
disjoint or that the complex quotient is the affine line.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

theorem matrixGroup_exists_fordRegion_representative (z : ℍ) :
    ∃ g : matrixGroup, g • z ∈ fordRegion :=
  subgroup_exists_fordRegion_representative matrixGroup
    generatorOneSL_mem_matrixGroup cuspSL_mem_matrixGroup z

end Wikipedia.HopfProblem.SpecialPeriods.Triangle

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- Every orbit of the actual faithful triangle action meets the concrete
polygon.  No quotient-uniformization hypothesis occurs here. -/
theorem triangle_exists_fordRegion_representative (z : ℍ) :
    ∃ g : TriangleGroup, triangleGeometricRepresentation g z ∈ Triangle.fordRegion := by
  obtain ⟨A, hA⟩ := Triangle.matrixGroup_exists_fordRegion_representative z
  obtain ⟨g, hg⟩ := Triangle.matrixGroup_permutation_lift A A.property
  refine ⟨g, ?_⟩
  rw [hg]
  exact hA

theorem triangle_exists_fordRegion_preimage (z : ℍ) :
    ∃ w ∈ Triangle.fordRegion, ∃ g : TriangleGroup, triangleGeometricRepresentation g w = z := by
  obtain ⟨g, hg⟩ := triangle_exists_fordRegion_representative z
  refine ⟨triangleGeometricRepresentation g z, hg, g⁻¹, ?_⟩
  rw [map_inv]
  exact (triangleGeometricRepresentation g).symm_apply_apply z

/-- The translates of the explicit polygon cover the whole upper
half-plane for the constructed group, not just an abstract presentation. -/
theorem triangle_translates_fordRegion_cover :
    (⋃ g : TriangleGroup, (triangleGeometricRepresentation g) '' Triangle.fordRegion) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨w, hw, g, hg⟩ := triangle_exists_fordRegion_preimage z
  exact mem_iUnion.mpr ⟨g, w, hw, hg⟩

end Wikipedia.HopfProblem.SpecialPeriods
