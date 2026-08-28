import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexTetrahedraCoordinates

/-!
# The twelve literal filling formulas on the ordered tetrahedra

Each identity holds on the entire original singular tetrahedron. The
coordinate vectors also display which restrictions are degenerate.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz Geometry

theorem fourSimplexFillA_tetrahedron_zero (s : Simplex 3) :
    (fourSimplexFillA (cubeTetrahedron (cubePermutation 0) s) : Fin 5 → ℝ) =
      ![s 0, s 1, s 2, 0, s 3] := by
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;> simp [fourSimplexTetrahedron_zero_coordinate, min_eq_right hca]
  all_goals linarith

theorem fourSimplexFillB_tetrahedron_zero (s : Simplex 3) :
    (fourSimplexFillB (cubeTetrahedron (cubePermutation 0) s) : Fin 5 → ℝ) =
      ![s 1, s 0, s 2, s 3, 0] := by
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;> simp [fourSimplexTetrahedron_zero_coordinate, min_eq_right hca]
  all_goals linarith

theorem fourSimplexFillA_tetrahedron_one (s : Simplex 3) :
    (fourSimplexFillA (cubeTetrahedron (cubePermutation 1) s) : Fin 5 → ℝ) =
      ![s 0, s 1, 0, 0, s 2 + s 3] := by
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexTetrahedron_one_coordinate, max_eq_left hca, min_eq_right hca]
  all_goals linarith

theorem fourSimplexFillB_tetrahedron_one (s : Simplex 3) :
    (fourSimplexFillB (cubeTetrahedron (cubePermutation 1) s) : Fin 5 → ℝ) =
      ![s 1 + s 2, s 0, 0, s 3, 0] := by
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;> simp [fourSimplexTetrahedron_one_coordinate, min_eq_right hca]
  all_goals linarith

theorem fourSimplexFillA_tetrahedron_two (s : Simplex 3) :
    (fourSimplexFillA (cubeTetrahedron (cubePermutation 2) s) : Fin 5 → ℝ) =
      ![s 0, 0, s 1 + s 2, 0, s 3] := by
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexTetrahedron_two_coordinate, max_eq_left hca, min_eq_right hca]
  all_goals linarith

theorem fourSimplexFillB_tetrahedron_two (s : Simplex 3) :
    (fourSimplexFillB (cubeTetrahedron (cubePermutation 2) s) : Fin 5 → ℝ) =
      ![0, s 0, s 1 + s 2, s 3, 0] := by
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexTetrahedron_two_coordinate, max_eq_left hca, min_eq_right hca]
  all_goals linarith

theorem fourSimplexFillA_tetrahedron_three (s : Simplex 3) :
    (fourSimplexFillA (cubeTetrahedron (cubePermutation 3) s) : Fin 5 → ℝ) =
      ![s 0 + s 1, 0, 0, 0, s 2 + s 3] := by
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexTetrahedron_three_coordinate, max_eq_right hca, min_eq_left hca]
  all_goals linarith

theorem fourSimplexFillB_tetrahedron_three (s : Simplex 3) :
    (fourSimplexFillB (cubeTetrahedron (cubePermutation 3) s) : Fin 5 → ℝ) =
      ![s 2, s 0, 0, s 3, s 1] := by
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexTetrahedron_three_coordinate, max_eq_right hca, min_eq_left hca]
  all_goals linarith

theorem fourSimplexFillA_tetrahedron_four (s : Simplex 3) :
    (fourSimplexFillA (cubeTetrahedron (cubePermutation 4) s) : Fin 5 → ℝ) =
      ![s 0, 0, s 1, s 2, s 3] := by
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexTetrahedron_four_coordinate, max_eq_right hca, min_eq_left hca]
  all_goals linarith

theorem fourSimplexFillB_tetrahedron_four (s : Simplex 3) :
    (fourSimplexFillB (cubeTetrahedron (cubePermutation 4) s) : Fin 5 → ℝ) =
      ![0, s 0, s 1, s 3, s 2] := by
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexTetrahedron_four_coordinate, min_eq_left hca, max_eq_right hca]
  all_goals linarith

theorem fourSimplexFillA_tetrahedron_five (s : Simplex 3) :
    (fourSimplexFillA (cubeTetrahedron (cubePermutation 5) s) : Fin 5 → ℝ) =
      ![s 0 + s 1, 0, 0, s 2, s 3] := by
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;> simp [fourSimplexTetrahedron_five_coordinate, min_eq_left hca]
  all_goals linarith

theorem fourSimplexFillB_tetrahedron_five (s : Simplex 3) :
    (fourSimplexFillB (cubeTetrahedron (cubePermutation 5) s) : Fin 5 → ℝ) =
      ![0, s 0, 0, s 3, s 1 + s 2] := by
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexTetrahedron_five_coordinate, max_eq_right hca, min_eq_left hca]
  all_goals linarith

end Wikipedia.HopfProblem.ThirdHurewicz
