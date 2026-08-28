import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexMaps

/-!
# Common missing coordinates on the six cube facets

The two literal fillings, with the second reflected in the first cube
coordinate, lie in the same two-dimensional simplex face at every
boundary point. The missing coordinate pairs are exhibited separately
on each of the six original cube facets.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

theorem fourSimplexFill_first_zero (u : Fin 3 → I) (hu : u 0 = 0) :
    fourSimplexFillA u 1 = 0 ∧ fourSimplexFillA u 4 = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) 1 = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) 4 = 0 := by
  simp [hu,
    min_eq_left ((u 1).property.1.trans (le_max_left _ (u 2 : ℝ))),
    min_eq_left (u 2).property.1,
    max_eq_left (max_le (u 1).property.2 (u 2).property.2),
    min_eq_right (u 2).property.2]

theorem fourSimplexFill_first_one (u : Fin 3 → I) (hu : u 0 = 1) :
    fourSimplexFillA u 0 = 0 ∧ fourSimplexFillA u 3 = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) 0 = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) 3 = 0 := by
  simp [hu, max_eq_left (u 1).property.2,
    min_eq_right ((min_le_left (u 1 : ℝ) (u 2 : ℝ)).trans (u 1).property.2),
    min_eq_left (u 1).property.1,
    min_eq_left (le_min (u 1).property.1 (u 2).property.1)]

theorem fourSimplexFill_second_zero (u : Fin 3 → I) (hu : u 1 = 0) :
    fourSimplexFillA u 2 = 0 ∧ fourSimplexFillA u 3 = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) 2 = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) 3 = 0 := by
  simp [hu, min_eq_left (u 2).property.1, min_eq_right (u 0).property.1,
    (u 0).property.2]

theorem fourSimplexFill_second_one (u : Fin 3 → I) (hu : u 1 = 1) :
    fourSimplexFillA u 0 = 0 ∧ fourSimplexFillA u 1 = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) 0 = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) 1 = 0 := by
  simp [hu, max_eq_right (u 0).property.2, max_eq_left (u 2).property.2,
    min_eq_left (u 0).property.2, min_eq_left (sub_le_self 1 (u 0).property.1),
    max_eq_right (sub_le_self 1 (u 0).property.1)]

theorem fourSimplexFill_third_zero (u : Fin 3 → I) (hu : u 2 = 0) :
    fourSimplexFillA u 3 = 0 ∧ fourSimplexFillA u 4 = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) 3 = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) 4 = 0 := by
  simp [hu, min_eq_right (u 1).property.1, min_eq_right (u 0).property.1,
    (u 0).property.2]

theorem fourSimplexFill_third_one (u : Fin 3 → I) (hu : u 2 = 1) :
    fourSimplexFillA u 1 = 0 ∧ fourSimplexFillA u 2 = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) 1 = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) 2 = 0 := by
  simp [hu, max_eq_right (u 1).property.2, min_eq_left (u 0).property.2,
    min_eq_left (u 1).property.2, max_eq_right (sub_le_self 1 (u 0).property.1)]

/-- Every original cube boundary point has two common missing barycentric
coordinates in the two reflected fillings. -/
theorem fourSimplexFill_boundary_common_zeros (u : Fin 3 → I)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    ∃ i j : Fin 5, i ≠ j ∧
      fourSimplexFillA u i = 0 ∧ fourSimplexFillA u j = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) i = 0 ∧
      fourSimplexFillB (fourSimplexReflectFirst u) j = 0 := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · exact ⟨1, 4, by decide, fourSimplexFill_first_zero u hi⟩
    · exact ⟨2, 3, by decide, fourSimplexFill_second_zero u hi⟩
    · exact ⟨3, 4, by decide, fourSimplexFill_third_zero u hi⟩
  · fin_cases i
    · exact ⟨0, 3, by decide, fourSimplexFill_first_one u hi⟩
    · exact ⟨0, 1, by decide, fourSimplexFill_second_one u hi⟩
    · exact ⟨1, 2, by decide, fourSimplexFill_third_one u hi⟩

end Wikipedia.HopfProblem.ThirdHurewicz
