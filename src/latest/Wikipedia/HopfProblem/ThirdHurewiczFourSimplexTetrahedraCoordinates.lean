import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexMaps
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionGeometryPermutations

/-!
# Barycentric coordinates on the six actual cube tetrahedra

These pointwise formulas follow from the original affine simplex map,
not merely from the images of its vertices.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz Geometry

theorem fourSimplexTetrahedron_coordinate_perm (e : Equiv.Perm (Fin 3))
    (s : Simplex 3) (i : Fin 3) :
    (cubeTetrahedron e s i : ℝ) = ![s 1 + s 2 + s 3, s 2 + s 3, s 3] (e.symm i) := by
  obtain ⟨j, rfl⟩ := e.surjective i
  fin_cases j <;> simp

theorem fourSimplexTetrahedron_zero_coordinate (s : Simplex 3) (i : Fin 3) :
    (cubeTetrahedron (cubePermutation 0) s i : ℝ) =
      ![s 1 + s 2 + s 3, s 2 + s 3, s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  rfl

theorem fourSimplexTetrahedron_one_coordinate (s : Simplex 3) (i : Fin 3) :
    (cubeTetrahedron (cubePermutation 1) s i : ℝ) =
      ![s 1 + s 2 + s 3, s 3, s 2 + s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [cubePermutation, Equiv.swap_apply_def]

theorem fourSimplexTetrahedron_two_coordinate (s : Simplex 3) (i : Fin 3) :
    (cubeTetrahedron (cubePermutation 2) s i : ℝ) =
      ![s 2 + s 3, s 1 + s 2 + s 3, s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [cubePermutation, Equiv.swap_apply_def]

theorem fourSimplexTetrahedron_three_coordinate (s : Simplex 3) (i : Fin 3) :
    (cubeTetrahedron (cubePermutation 3) s i : ℝ) =
      ![s 2 + s 3, s 3, s 1 + s 2 + s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [cubePermutation, Equiv.swap_apply_def]

theorem fourSimplexTetrahedron_four_coordinate (s : Simplex 3) (i : Fin 3) :
    (cubeTetrahedron (cubePermutation 4) s i : ℝ) =
      ![s 3, s 1 + s 2 + s 3, s 2 + s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [cubePermutation, Equiv.swap_apply_def]

theorem fourSimplexTetrahedron_five_coordinate (s : Simplex 3) (i : Fin 3) :
    (cubeTetrahedron (cubePermutation 5) s i : ℝ) =
      ![s 3, s 2 + s 3, s 1 + s 2 + s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [cubePermutation, Equiv.swap_apply_def]

theorem fourSimplexTetrahedron_tail_le_middle (s : Simplex 3) :
    s 3 ≤ s 2 + s 3 := le_add_of_nonneg_left (stdSimplex.zero_le s 2)

theorem fourSimplexTetrahedron_middle_le_first (s : Simplex 3) :
    s 2 + s 3 ≤ s 1 + s 2 + s 3 := by
  linarith [stdSimplex.zero_le s 1]

theorem fourSimplexTetrahedron_tail_le_first (s : Simplex 3) :
    s 3 ≤ s 1 + s 2 + s 3 :=
  (fourSimplexTetrahedron_tail_le_middle s).trans (fourSimplexTetrahedron_middle_le_first s)

theorem fourSimplexTetrahedron_sum (s : Simplex 3) :
    s 0 + s 1 + s 2 + s 3 = 1 := by
  have h := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  change s 0 + (s 1 + (s 2 + s 3)) = 1 at h
  linarith

end Wikipedia.HopfProblem.ThirdHurewicz
