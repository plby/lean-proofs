import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexBoundaryFacets
import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexBoundaryInternal
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronBasic

/-!
# Boundary-compatible interpolation of the two literal fillings

Both maps send the original cube boundary to the actual two-skeleton.
After reflection the zero-coordinate pair is common, so the entire
affine interpolation remains in that two-skeleton on the boundary.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open SecondHurewicz.SimplyConnected

theorem fourSimplexFillA_boundary (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  obtain ⟨i, j, hij, hi, hj, _, _⟩ := fourSimplexFill_boundary_common_zeros u hu
  exact ⟨i, j, hij, hi, hj⟩

theorem fourSimplexFillB_boundary (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  obtain ⟨i, j, hij, _, _, hi, hj⟩ :=
    fourSimplexFill_boundary_common_zeros (fourSimplexReflectFirst u)
      (fourSimplexReflectFirst_boundary u hu)
  exact ⟨i, j, hij, by simpa only [fourSimplexReflectFirst_involutive] using hi,
    by simpa only [fourSimplexReflectFirst_involutive] using hj⟩

/-- The whole affine homotopy stays in the actual two-skeleton on the
entire original native cube boundary. -/
theorem fourSimplexFill_blend_boundary (t : I) (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    tetrahedronSimplexBlend t (fourSimplexFillA u)
      (fourSimplexFillB (fourSimplexReflectFirst u)) ∈ fourSimplexTwoSkeleton := by
  obtain ⟨i, j, hij, hai, haj, hbi, hbj⟩ :=
    fourSimplexFill_boundary_common_zeros u hu
  exact ⟨i, j, hij, tetrahedronSimplexBlend_zero_coordinate t _ _ i hai hbi,
    tetrahedronSimplexBlend_zero_coordinate t _ _ j haj hbj⟩

end Wikipedia.HopfProblem.ThirdHurewicz
