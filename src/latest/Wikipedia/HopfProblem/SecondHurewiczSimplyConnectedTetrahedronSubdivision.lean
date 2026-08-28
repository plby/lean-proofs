import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronFill
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronCyclic
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSubdivision

/-!
# The four actual faces occurring in the two tetrahedral fillings

These are equalities of singular parametrizations and generalized loops,
before taking either a homotopy group or singular homology.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

theorem tetrahedronQuadrilateralA_lower (u : Fin 2 → I) :
    tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u) =
      simplexFace 2 3 (triangleCubeQuotient u) := by
  apply Subtype.ext
  funext j
  change tetrahedronQuadrilateralA ![u 0, min (u 0) (u 1)] j =
    (simplexFace 2 3 (triangleCubeQuotient u) : Fin 4 → ℝ) j
  rw [simplexFace_two_three]
  fin_cases j <;> simp

theorem tetrahedronQuadrilateralA_upper (u : Fin 2 → I) :
    tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u) =
      simplexFace 2 1 (triangleCubeQuotient u) := by
  have hm : (u 0 : ℝ) - min (u 0 : ℝ) (u 1 : ℝ) ≤ (u 0 : ℝ) :=
    sub_le_self _ (le_min (u 0).property.1 (u 1).property.1)
  apply Subtype.ext
  funext j
  change tetrahedronQuadrilateralA ![subdivisionSubMin (u 0) (u 1), u 0] j =
    (simplexFace 2 1 (triangleCubeQuotient u) : Fin 4 → ℝ) j
  rw [simplexFace_two_one]
  fin_cases j <;> simp [min_eq_left hm, max_eq_right hm]

theorem tetrahedronQuarterShift_face_three (s : Simplex 2) :
    tetrahedronQuarterShift (simplexFace 2 3 s) = simplexFace 2 0 s := by
  apply Subtype.ext
  funext j
  change tetrahedronQuarterShift (simplexFace 2 3 s) j =
    (simplexFace 2 0 s : Fin 4 → ℝ) j
  rw [simplexFace_two_zero]
  fin_cases j
  · exact simplexFace_apply_self 2 3 s
  · exact simplexFace_apply_succAbove 2 3 s 0
  · exact simplexFace_apply_succAbove 2 3 s 1
  · exact simplexFace_apply_succAbove 2 3 s 2

theorem tetrahedronQuarterShift_face_one (s : Simplex 2) :
    tetrahedronQuarterShift (simplexFace 2 1 s) =
      simplexFace 2 2 (triangleCyclicPermutation (triangleCyclicPermutation s)) := by
  apply Subtype.ext
  funext j
  change tetrahedronQuarterShift (simplexFace 2 1 s) j =
    (simplexFace 2 2 (triangleCyclicPermutation (triangleCyclicPermutation s)) : Fin 4 → ℝ) j
  rw [simplexFace_two_two]
  fin_cases j
  · exact simplexFace_apply_succAbove 2 1 s 2
  · exact simplexFace_apply_succAbove 2 1 s 0
  · exact simplexFace_apply_self 2 1 s
  · exact simplexFace_apply_succAbove 2 1 s 1

variable {X : Type} [TopologicalSpace X] {x : X}

theorem tetrahedronLowerLoop_eq_face (τ : BasedTetrahedron x) :
    subdivisionLowerTriangleLoop (tetrahedronQuadrilateralLoop τ)
      (tetrahedronQuadrilateralLoop_diagonal τ) =
        basedTriangleLoop (basedTetrahedronFace τ 3) := by
  apply GenLoop.ext
  intro u
  change τ.val (tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u)) =
    τ.val (simplexFace 2 3 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_lower]

theorem tetrahedronUpperLoop_eq_face (τ : BasedTetrahedron x) :
    subdivisionUpperTriangleLoop (tetrahedronQuadrilateralLoop τ)
      (tetrahedronQuadrilateralLoop_diagonal τ) =
        basedTriangleLoop (basedTetrahedronFace τ 1) := by
  apply GenLoop.ext
  intro u
  change τ.val (tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u)) =
    τ.val (simplexFace 2 1 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_upper]

theorem tetrahedronShiftedLowerLoop_eq_face (τ : BasedTetrahedron x) :
    subdivisionLowerTriangleLoop (tetrahedronShiftedQuadrilateralLoop τ)
      (tetrahedronShiftedQuadrilateralLoop_diagonal τ) =
        basedTriangleLoop (basedTetrahedronFace τ 0) := by
  apply GenLoop.ext
  intro u
  change τ.val
      (tetrahedronQuarterShift (tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u))) =
    τ.val (simplexFace 2 0 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_lower, tetrahedronQuarterShift_face_three]

theorem tetrahedronShiftedUpperLoop_eq_face (τ : BasedTetrahedron x) :
    subdivisionUpperTriangleLoop (tetrahedronShiftedQuadrilateralLoop τ)
      (tetrahedronShiftedQuadrilateralLoop_diagonal τ) =
        basedTriangleLoop (cyclicBasedTriangle
          (cyclicBasedTriangle (basedTetrahedronFace τ 2))) := by
  apply GenLoop.ext
  intro u
  change τ.val
      (tetrahedronQuarterShift (tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u))) =
    τ.val (simplexFace 2 2
      (triangleCyclicPermutation (triangleCyclicPermutation (triangleCubeQuotient u))))
  rw [tetrahedronQuadrilateralA_upper, tetrahedronQuarterShift_face_one]

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
