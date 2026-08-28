import ErdosProblems.Erdos577.FirstPawOutsideModel

/-! Explicit factors for each pair of outside contacts in patterns (3) and (8). -/

namespace Erdos577.FirstPawOutside

open Finset

theorem finite_factor (patternEight : Bool) (i j : Fin 4) (hne : i ≠ j) :
    LocalFactor (graph patternEight i j) univ := by
  cases patternEight
  · fin_cases i <;> fin_cases j
    · exact False.elim (hne rfl)
    · refine ⟨{0, 4, 3, 5}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 4, 2, 7}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 4, 3, 5}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · exact False.elim (hne rfl)
    · refine ⟨{0, 5, 1, 6}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 5, 1, 6}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · exact False.elim (hne rfl)
    · refine ⟨{0, 6, 1, 7}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 4, 2, 7}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 6, 1, 7}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · exact False.elim (hne rfl)
  · fin_cases i <;> fin_cases j
    · exact False.elim (hne rfl)
    · refine ⟨{0, 4, 6, 5}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 4, 6, 7}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 4, 6, 5}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · exact False.elim (hne rfl)
    · refine ⟨{0, 5, 4, 6}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 5, 4, 6}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · exact False.elim (hne rfl)
    · refine ⟨{0, 6, 4, 7}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 4, 6, 7}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · refine ⟨{0, 6, 4, 7}, subset_univ _, ?_, ?_⟩
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
      · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · exact False.elim (hne rfl)

end Erdos577.FirstPawOutside
