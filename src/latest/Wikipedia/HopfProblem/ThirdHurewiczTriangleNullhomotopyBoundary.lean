import Wikipedia.HopfProblem.ThirdHurewiczTriangleNullhomotopyCoordinates

/-!
# Boundary control of the triangle-square return map

The return map takes every triangle face into the square perimeter.
After composing with the original square-to-triangle quotient, every
zero barycentric coordinate remains zero.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

theorem triangleCubicalReturn_face_zero (s : Simplex 2) (hs : s 0 = 0) :
    triangleCubicalReturn s 0 = 1 := by
  apply Subtype.ext
  change s 1 + max (s 2 - s 0) 0 = 1
  rw [hs, sub_zero, max_eq_left (stdSimplex.zero_le s 2)]
  have hsum := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change s 0 + (s 1 + s 2) = 1 at hsum
  simpa only [hs, zero_add] using hsum

theorem triangleCubicalReturn_face_two (s : Simplex 2) (hs : s 2 = 0) :
    triangleCubicalReturn s 1 = 0 := by
  apply Subtype.ext
  change s 2 + min (s 0) (s 2) = 0
  rw [hs, min_eq_right (stdSimplex.zero_le s 0), zero_add]

theorem triangleCubicalReturn_face_one (s : Simplex 2) (hs : s 1 = 0) :
    triangleCubicalReturn s 0 = 0 ∨ triangleCubicalReturn s 1 = 1 := by
  rcases le_total (s 2) (s 0) with h | h
  · left
    apply Subtype.ext
    change s 1 + max (s 2 - s 0) 0 = 0
    rw [hs, max_eq_right (sub_nonpos.mpr h), zero_add]
  · right
    apply Subtype.ext
    change s 2 + min (s 0) (s 2) = 1
    rw [min_eq_left h]
    have hsum := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
    change s 0 + (s 1 + s 2) = 1 at hsum
    linarith

/-- Every original boundary point maps to the actual cube boundary. -/
theorem triangleCubicalReturn_boundary (s : Simplex 2) (hs : s ∈ triangleBoundary) :
    triangleCubicalReturn s ∈ Cube.boundary (Fin 2) := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨0, Or.inr (triangleCubicalReturn_face_zero s hi)⟩
  · rcases triangleCubicalReturn_face_one s hi with h | h
    · exact ⟨0, Or.inl h⟩
    · exact ⟨1, Or.inr h⟩
  · exact ⟨1, Or.inl (triangleCubicalReturn_face_two s hi)⟩

/-- The return followed by the existing quotient preserves each zero
coordinate separately, not just the union of the faces. -/
theorem triangleCubicalReturn_quotient_zero (s : Simplex 2) (i : Fin 3)
    (hi : s i = 0) : triangleCubeQuotient (triangleCubicalReturn s) i = 0 := by
  fin_cases i
  · change 1 - (triangleCubicalReturn s 0 : ℝ) = 0
    rw [triangleCubicalReturn_face_zero s hi]
    norm_num
  · change (triangleCubicalReturn s 0 : ℝ) -
      min (triangleCubicalReturn s 0 : ℝ) (triangleCubicalReturn s 1 : ℝ) = 0
    rcases triangleCubicalReturn_face_one s hi with h | h
    · rw [h]
      change 0 - min 0 (triangleCubicalReturn s 1 : ℝ) = 0
      rw [min_eq_left (triangleCubicalReturn s 1).property.1, sub_self]
    · rw [h]
      change (triangleCubicalReturn s 0 : ℝ) - min (triangleCubicalReturn s 0 : ℝ) 1 = 0
      rw [min_eq_left (triangleCubicalReturn s 0).property.2, sub_self]
  · change min (triangleCubicalReturn s 0 : ℝ) (triangleCubicalReturn s 1 : ℝ) = 0
    rw [triangleCubicalReturn_face_two s hi]
    change min (triangleCubicalReturn s 0 : ℝ) 0 = 0
    exact min_eq_right (triangleCubicalReturn s 0).property.1

end Wikipedia.HopfProblem.ThirdHurewicz
