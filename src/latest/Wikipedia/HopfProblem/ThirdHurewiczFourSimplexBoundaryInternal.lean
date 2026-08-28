import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexMaps

/-!
# Internal equality planes of the two explicit cube fillings

Every equality between distinct cube coordinates gives two missing
barycentric coordinates. Thus all the internal faces of the six ordered
tetrahedra lie in the actual two-skeleton of the four-simplex.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

theorem fourSimplexFillA_first_eq_second (u : Fin 3 → I) (hu : u 0 = u 1) :
    fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  refine ⟨1, 3, by decide, ?_, ?_⟩
  · simp [hu]
  · simp [hu]

theorem fourSimplexFillA_first_eq_third (u : Fin 3 → I) (hu : u 0 = u 2) :
    fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  refine ⟨1, 3, by decide, ?_, ?_⟩
  · simp [hu]
  · simp [hu]

theorem fourSimplexFillA_second_eq_third (u : Fin 3 → I) (hu : u 1 = u 2) :
    fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  rcases le_total (u 0 : ℝ) (u 2 : ℝ) with h | h
  · refine ⟨1, 2, by decide, ?_, ?_⟩
    · simp [hu, min_eq_left h]
    · simp [hu]
  · refine ⟨2, 3, by decide, ?_, ?_⟩
    · simp [hu]
    · simp [hu, min_eq_right h]

theorem fourSimplexFillB_first_eq_second (u : Fin 3 → I) (hu : u 0 = u 1) :
    fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  rcases le_total (u 1 : ℝ) (u 2 : ℝ) with h | h
  · refine ⟨0, 2, by decide, ?_, ?_⟩
    · simp [hu]
    · simp [min_eq_left h]
  · refine ⟨0, 4, by decide, ?_, ?_⟩
    · simp [hu]
    · simp [hu, min_eq_right h]

theorem fourSimplexFillB_first_eq_third (u : Fin 3 → I) (hu : u 0 = u 2) :
    fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  rcases le_total (u 2 : ℝ) (u 1 : ℝ) with h | h
  · refine ⟨0, 4, by decide, ?_, ?_⟩
    · simp [hu, min_eq_left h]
    · simp [hu]
  · refine ⟨2, 4, by decide, ?_, ?_⟩
    · simp [min_eq_left h]
    · simp [hu]

theorem fourSimplexFillB_second_eq_third (u : Fin 3 → I) (hu : u 1 = u 2) :
    fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  rcases le_total (u 0 : ℝ) (u 2 : ℝ) with h | h
  · refine ⟨0, 2, by decide, ?_, ?_⟩
    · simp [hu, min_eq_left h]
    · simp [hu]
  · refine ⟨2, 4, by decide, ?_, ?_⟩
    · simp [hu]
    · simp [min_eq_right h]

/-- All native internal coordinate-equality faces for the first filling. -/
theorem fourSimplexFillA_internal (u : Fin 3 → I) (i j : Fin 3)
    (hij : i ≠ j) (hu : u i = u j) :
    fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact fourSimplexFillA_first_eq_second u hu
  · exact fourSimplexFillA_first_eq_third u hu
  · exact fourSimplexFillA_first_eq_second u hu.symm
  · exact (hij rfl).elim
  · exact fourSimplexFillA_second_eq_third u hu
  · exact fourSimplexFillA_first_eq_third u hu.symm
  · exact fourSimplexFillA_second_eq_third u hu.symm
  · exact (hij rfl).elim

/-- All native internal coordinate-equality faces for the second filling. -/
theorem fourSimplexFillB_internal (u : Fin 3 → I) (i j : Fin 3)
    (hij : i ≠ j) (hu : u i = u j) :
    fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact fourSimplexFillB_first_eq_second u hu
  · exact fourSimplexFillB_first_eq_third u hu
  · exact fourSimplexFillB_first_eq_second u hu.symm
  · exact (hij rfl).elim
  · exact fourSimplexFillB_second_eq_third u hu
  · exact fourSimplexFillB_first_eq_third u hu.symm
  · exact fourSimplexFillB_second_eq_third u hu.symm
  · exact (hij rfl).elim

end Wikipedia.HopfProblem.ThirdHurewicz
