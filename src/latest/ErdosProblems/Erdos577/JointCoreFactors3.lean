import ErdosProblems.Erdos577.JointCoreModel

/-! Explicit outside factors for source pattern 30. -/

namespace Erdos577.JointCore

open Finset

private theorem factor_0_1 : LocalFactor (outsideGraph 3 0 1) univ := by
  refine ⟨{0, 1, 2, 3}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_0_2 : LocalFactor (outsideGraph 3 0 2) univ := by
  refine ⟨{0, 1, 2, 3}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_0_3 : LocalFactor (outsideGraph 3 0 3) univ := by
  refine ⟨{0, 1, 2, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_0_4 : LocalFactor (outsideGraph 3 0 4) univ := by
  refine ⟨{0, 1, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_0_5 : LocalFactor (outsideGraph 3 0 5) univ := by
  refine ⟨{0, 1, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_0_6 : LocalFactor (outsideGraph 3 0 6) univ := by
  refine ⟨{0, 1, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_1_2 : LocalFactor (outsideGraph 3 1 2) univ := by
  refine ⟨{0, 1, 2, 3}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_1_3 : LocalFactor (outsideGraph 3 1 3) univ := by
  refine ⟨{0, 1, 2, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_1_4 : LocalFactor (outsideGraph 3 1 4) univ := by
  refine ⟨{0, 2, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_1_5 : LocalFactor (outsideGraph 3 1 5) univ := by
  refine ⟨{0, 1, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_1_6 : LocalFactor (outsideGraph 3 1 6) univ := by
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_2_3 : LocalFactor (outsideGraph 3 2 3) univ := by
  refine ⟨{0, 3, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_2_4 : LocalFactor (outsideGraph 3 2 4) univ := by
  refine ⟨{0, 3, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_2_5 : LocalFactor (outsideGraph 3 2 5) univ := by
  refine ⟨{0, 3, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_2_6 : LocalFactor (outsideGraph 3 2 6) univ := by
  refine ⟨{0, 1, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_3_4 : LocalFactor (outsideGraph 3 3 4) univ := by
  refine ⟨{0, 3, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_3_5 : LocalFactor (outsideGraph 3 3 5) univ := by
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_3_6 : LocalFactor (outsideGraph 3 3 6) univ := by
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_4_5 : LocalFactor (outsideGraph 3 4 5) univ := by
  refine ⟨{0, 3, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_4_6 : LocalFactor (outsideGraph 3 4 6) univ := by
  refine ⟨{0, 3, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem factor_5_6 : LocalFactor (outsideGraph 3 5 6) univ := by
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem row_0 (j : Fin 7) (h : (0 : Fin 7) < j) :
    LocalFactor (outsideGraph 3 0 j) univ := by
  fin_cases j
  · exact False.elim ((by decide : ¬ (0 : Fin 7) < 0) h)
  · exact factor_0_1
  · exact factor_0_2
  · exact factor_0_3
  · exact factor_0_4
  · exact factor_0_5
  · exact factor_0_6

private theorem row_1 (j : Fin 7) (h : (1 : Fin 7) < j) :
    LocalFactor (outsideGraph 3 1 j) univ := by
  fin_cases j
  · exact False.elim ((by decide : ¬ (1 : Fin 7) < 0) h)
  · exact False.elim ((by decide : ¬ (1 : Fin 7) < 1) h)
  · exact factor_1_2
  · exact factor_1_3
  · exact factor_1_4
  · exact factor_1_5
  · exact factor_1_6

private theorem row_2 (j : Fin 7) (h : (2 : Fin 7) < j) :
    LocalFactor (outsideGraph 3 2 j) univ := by
  fin_cases j
  · exact False.elim ((by decide : ¬ (2 : Fin 7) < 0) h)
  · exact False.elim ((by decide : ¬ (2 : Fin 7) < 1) h)
  · exact False.elim ((by decide : ¬ (2 : Fin 7) < 2) h)
  · exact factor_2_3
  · exact factor_2_4
  · exact factor_2_5
  · exact factor_2_6

private theorem row_3 (j : Fin 7) (h : (3 : Fin 7) < j) :
    LocalFactor (outsideGraph 3 3 j) univ := by
  fin_cases j
  · exact False.elim ((by decide : ¬ (3 : Fin 7) < 0) h)
  · exact False.elim ((by decide : ¬ (3 : Fin 7) < 1) h)
  · exact False.elim ((by decide : ¬ (3 : Fin 7) < 2) h)
  · exact False.elim ((by decide : ¬ (3 : Fin 7) < 3) h)
  · exact factor_3_4
  · exact factor_3_5
  · exact factor_3_6

private theorem row_4 (j : Fin 7) (h : (4 : Fin 7) < j) :
    LocalFactor (outsideGraph 3 4 j) univ := by
  fin_cases j
  · exact False.elim ((by decide : ¬ (4 : Fin 7) < 0) h)
  · exact False.elim ((by decide : ¬ (4 : Fin 7) < 1) h)
  · exact False.elim ((by decide : ¬ (4 : Fin 7) < 2) h)
  · exact False.elim ((by decide : ¬ (4 : Fin 7) < 3) h)
  · exact False.elim ((by decide : ¬ (4 : Fin 7) < 4) h)
  · exact factor_4_5
  · exact factor_4_6

private theorem row_5 (j : Fin 7) (h : (5 : Fin 7) < j) :
    LocalFactor (outsideGraph 3 5 j) univ := by
  fin_cases j
  · exact False.elim ((by decide : ¬ (5 : Fin 7) < 0) h)
  · exact False.elim ((by decide : ¬ (5 : Fin 7) < 1) h)
  · exact False.elim ((by decide : ¬ (5 : Fin 7) < 2) h)
  · exact False.elim ((by decide : ¬ (5 : Fin 7) < 3) h)
  · exact False.elim ((by decide : ¬ (5 : Fin 7) < 4) h)
  · exact False.elim ((by decide : ¬ (5 : Fin 7) < 5) h)
  · exact factor_5_6

private theorem row_6 (j : Fin 7) (h : (6 : Fin 7) < j) :
    LocalFactor (outsideGraph 3 6 j) univ := by
  fin_cases j
  · exact False.elim ((by decide : ¬ (6 : Fin 7) < 0) h)
  · exact False.elim ((by decide : ¬ (6 : Fin 7) < 1) h)
  · exact False.elim ((by decide : ¬ (6 : Fin 7) < 2) h)
  · exact False.elim ((by decide : ¬ (6 : Fin 7) < 3) h)
  · exact False.elim ((by decide : ¬ (6 : Fin 7) < 4) h)
  · exact False.elim ((by decide : ¬ (6 : Fin 7) < 5) h)
  · exact False.elim ((by decide : ¬ (6 : Fin 7) < 6) h)

theorem outside_factor_3 (i j : Fin 7) (h : i < j) :
    LocalFactor (outsideGraph 3 i j) univ := by
  fin_cases i
  · exact row_0 j h
  · exact row_1 j h
  · exact row_2 j h
  · exact row_3 j h
  · exact row_4 j h
  · exact row_5 j h
  · exact row_6 j h

end Erdos577.JointCore
