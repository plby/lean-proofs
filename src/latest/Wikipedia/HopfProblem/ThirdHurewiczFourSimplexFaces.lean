import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexBasic

/-!
# Literal barycentric coordinates of all five four-simplex faces
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz

theorem simplexFace_three_zero (s : Simplex 3) :
    (simplexFace 3 0 s : Fin 5 → ℝ) = ![0, s 0, s 1, s 2, s 3] := by
  funext i
  fin_cases i
  · exact simplexFace_apply_self 3 0 s
  · exact simplexFace_apply_succAbove 3 0 s 0
  · exact simplexFace_apply_succAbove 3 0 s 1
  · exact simplexFace_apply_succAbove 3 0 s 2
  · exact simplexFace_apply_succAbove 3 0 s 3

theorem simplexFace_three_one (s : Simplex 3) :
    (simplexFace 3 1 s : Fin 5 → ℝ) = ![s 0, 0, s 1, s 2, s 3] := by
  funext i
  fin_cases i
  · exact simplexFace_apply_succAbove 3 1 s 0
  · exact simplexFace_apply_self 3 1 s
  · exact simplexFace_apply_succAbove 3 1 s 1
  · exact simplexFace_apply_succAbove 3 1 s 2
  · exact simplexFace_apply_succAbove 3 1 s 3

theorem simplexFace_three_two (s : Simplex 3) :
    (simplexFace 3 2 s : Fin 5 → ℝ) = ![s 0, s 1, 0, s 2, s 3] := by
  funext i
  fin_cases i
  · exact simplexFace_apply_succAbove 3 2 s 0
  · exact simplexFace_apply_succAbove 3 2 s 1
  · exact simplexFace_apply_self 3 2 s
  · exact simplexFace_apply_succAbove 3 2 s 2
  · exact simplexFace_apply_succAbove 3 2 s 3

theorem simplexFace_three_three (s : Simplex 3) :
    (simplexFace 3 3 s : Fin 5 → ℝ) = ![s 0, s 1, s 2, 0, s 3] := by
  funext i
  fin_cases i
  · exact simplexFace_apply_succAbove 3 3 s 0
  · exact simplexFace_apply_succAbove 3 3 s 1
  · exact simplexFace_apply_succAbove 3 3 s 2
  · exact simplexFace_apply_self 3 3 s
  · exact simplexFace_apply_succAbove 3 3 s 3

theorem simplexFace_three_four (s : Simplex 3) :
    (simplexFace 3 4 s : Fin 5 → ℝ) = ![s 0, s 1, s 2, s 3, 0] := by
  funext i
  fin_cases i
  · exact simplexFace_apply_succAbove 3 4 s 0
  · exact simplexFace_apply_succAbove 3 4 s 1
  · exact simplexFace_apply_succAbove 3 4 s 2
  · exact simplexFace_apply_succAbove 3 4 s 3
  · exact simplexFace_apply_self 3 4 s

end Wikipedia.HopfProblem.ThirdHurewicz
