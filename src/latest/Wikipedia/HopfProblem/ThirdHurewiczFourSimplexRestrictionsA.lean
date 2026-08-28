import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexRestrictionsBasic
import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexTetrahedra
import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexFaces

/-!
# The first filling contains exactly two nonconstant based faces
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz Geometry

variable {X : Type} [TopologicalSpace X] {x : X}

theorem fourSimplexTetrahedronA_zero (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (cubePermutation 0) = basedFourSimplexFace τ 3 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (cubeTetrahedron (cubePermutation 0) s)) =
    τ.val (simplexFace 3 3 s)
  apply congrArg τ.val
  apply Subtype.ext
  exact (fourSimplexFillA_tetrahedron_zero s).trans (simplexFace_three_three s).symm

theorem fourSimplexTetrahedronA_one (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (cubePermutation 1) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (cubeTetrahedron (cubePermutation 1) s)) = x
  apply τ.property
  exact ⟨2, 3, by decide,
    (congrFun (fourSimplexFillA_tetrahedron_one s) 2).trans rfl,
    (congrFun (fourSimplexFillA_tetrahedron_one s) 3).trans rfl⟩

theorem fourSimplexTetrahedronA_two (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (cubePermutation 2) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (cubeTetrahedron (cubePermutation 2) s)) = x
  apply τ.property
  exact ⟨1, 3, by decide,
    (congrFun (fourSimplexFillA_tetrahedron_two s) 1).trans rfl,
    (congrFun (fourSimplexFillA_tetrahedron_two s) 3).trans rfl⟩

theorem fourSimplexTetrahedronA_three (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (cubePermutation 3) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (cubeTetrahedron (cubePermutation 3) s)) = x
  apply τ.property
  exact ⟨1, 2, by decide,
    (congrFun (fourSimplexFillA_tetrahedron_three s) 1).trans rfl,
    (congrFun (fourSimplexFillA_tetrahedron_three s) 2).trans rfl⟩

theorem fourSimplexTetrahedronA_four (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (cubePermutation 4) = basedFourSimplexFace τ 1 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (cubeTetrahedron (cubePermutation 4) s)) =
    τ.val (simplexFace 3 1 s)
  apply congrArg τ.val
  apply Subtype.ext
  exact (fourSimplexFillA_tetrahedron_four s).trans (simplexFace_three_one s).symm

theorem fourSimplexTetrahedronA_five (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (cubePermutation 5) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (cubeTetrahedron (cubePermutation 5) s)) = x
  apply τ.property
  exact ⟨1, 2, by decide,
    (congrFun (fourSimplexFillA_tetrahedron_five s) 1).trans rfl,
    (congrFun (fourSimplexFillA_tetrahedron_five s) 2).trans rfl⟩

end Wikipedia.HopfProblem.ThirdHurewicz
