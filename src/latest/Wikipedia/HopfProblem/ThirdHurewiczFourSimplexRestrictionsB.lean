import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexRestrictionsBasic
import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexTetrahedra
import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexFaces
import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexOrientation

/-!
# The second filling contains the other three faces, with their actual vertex orders
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz Geometry

variable {X : Type} [TopologicalSpace X] {x : X}

theorem fourSimplexTetrahedronB_zero (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (cubePermutation 0) =
      basedThreeSimplexSwapFirst (basedFourSimplexFace τ 4) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillB (cubeTetrahedron (cubePermutation 0) s)) =
    τ.val (simplexFace 3 4 (threeSimplexSwapFirst s))
  apply congrArg τ.val
  apply Subtype.ext
  exact (fourSimplexFillB_tetrahedron_zero s).trans
    (simplexFace_three_four (threeSimplexSwapFirst s)).symm

theorem fourSimplexTetrahedronB_one (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (cubePermutation 1) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillB (cubeTetrahedron (cubePermutation 1) s)) = x
  apply τ.property
  exact ⟨2, 4, by decide,
    (congrFun (fourSimplexFillB_tetrahedron_one s) 2).trans rfl,
    (congrFun (fourSimplexFillB_tetrahedron_one s) 4).trans rfl⟩

theorem fourSimplexTetrahedronB_two (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (cubePermutation 2) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillB (cubeTetrahedron (cubePermutation 2) s)) = x
  apply τ.property
  exact ⟨0, 4, by decide,
    (congrFun (fourSimplexFillB_tetrahedron_two s) 0).trans rfl,
    (congrFun (fourSimplexFillB_tetrahedron_two s) 4).trans rfl⟩

theorem fourSimplexTetrahedronB_three (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (cubePermutation 3) =
      basedThreeSimplexVertexOrder1302 (basedFourSimplexFace τ 2) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillB (cubeTetrahedron (cubePermutation 3) s)) =
    τ.val (simplexFace 3 2 (threeSimplexVertexOrder1302 s))
  apply congrArg τ.val
  apply Subtype.ext
  exact (fourSimplexFillB_tetrahedron_three s).trans
    (simplexFace_three_two (threeSimplexVertexOrder1302 s)).symm

theorem fourSimplexTetrahedronB_four (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (cubePermutation 4) =
      basedThreeSimplexSwapLast (basedFourSimplexFace τ 0) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillB (cubeTetrahedron (cubePermutation 4) s)) =
    τ.val (simplexFace 3 0 (threeSimplexSwapLast s))
  apply congrArg τ.val
  apply Subtype.ext
  exact (fourSimplexFillB_tetrahedron_four s).trans
    (simplexFace_three_zero (threeSimplexSwapLast s)).symm

theorem fourSimplexTetrahedronB_five (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (cubePermutation 5) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillB (cubeTetrahedron (cubePermutation 5) s)) = x
  apply τ.property
  exact ⟨0, 2, by decide,
    (congrFun (fourSimplexFillB_tetrahedron_five s) 0).trans rfl,
    (congrFun (fourSimplexFillB_tetrahedron_five s) 2).trans rfl⟩

end Wikipedia.HopfProblem.ThirdHurewicz
