import StackExchange.Puzzling139335.N7.CornerGap

/-!
# Actual ownership of the strict gap

Source support and the inverse third-placement coordinate exclude the
first three pieces. The actual square cover then forces the fourth owner.
-/

open Set

namespace Puzzling139335.N7

open ReflectionSeparation

/-- The source support inequality excludes the horizontal image from one
strict side of the gap. -/
theorem not_mem_horizontal_of_strict_gap {P : Set Plane} {c s : ℝ} {p : Plane}
    (hsupport : ∀ q ∈ P, c * q 1 ≤ s * (1 - q 0))
    (hgap : s * (1 - p 0) < c * (1 - p 1)) :
    p ∉ horizontal '' P := by
  rintro ⟨q, hq, rfl⟩
  simp only [horizontal_apply_zero, horizontal_apply_one, sub_sub_cancel] at hgap
  exact (not_lt_of_ge (hsupport q hq)) hgap

/-- Nonnegative source height excludes the third image from the other
strict side of the gap. -/
theorem not_mem_thirdMap_of_strict_gap {P : Set Plane} {c s : ℝ} {p : Plane}
    (hP : P ⊆ unitSquare) (hunit : c ^ 2 + s ^ 2 = 1)
    (hgap : s * (1 - p 1) < c * (1 - p 0)) :
    p ∉ thirdMap c s '' P := by
  rintro ⟨q, hq, heq⟩
  have hinverse := thirdMap_inverse_second hunit q
  rw [heq] at hinverse
  have hheight := (hP hq).2.1
  nlinarith only [hinverse, hheight, hgap]

/-- A point of the square above the source and strictly between the two
known images belongs to the fourth actual piece. -/
theorem strict_gap_mem_fourth (d : SquareDissection) {c s : ℝ} {p : Plane}
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hhalf : ∀ q ∈ d.piece 0, q 1 ≤ (1 / 2 : ℝ))
    (hH : horizontal '' d.piece 0 = d.piece 1)
    (hT : thirdMap c s '' d.piece 0 = d.piece 2)
    (hsupport : ∀ q ∈ d.piece 0, c * q 1 ≤ s * (1 - q 0))
    (hp : p ∈ unitSquare) (hheight : (1 / 2 : ℝ) < p 1)
    (hgapH : s * (1 - p 0) < c * (1 - p 1))
    (hgapT : s * (1 - p 1) < c * (1 - p 0)) : p ∈ d.piece 3 := by
  have hzero : p ∉ d.piece 0 := fun hmem => (not_lt_of_ge (hhalf p hmem)) hheight
  have hone : p ∉ d.piece 1 := by
    rw [← hH]
    exact not_mem_horizontal_of_strict_gap hsupport hgapH
  have htwo : p ∉ d.piece 2 := by
    rw [← hT]
    exact not_mem_thirdMap_of_strict_gap (d.piece_subset 0) hunit hgapT
  obtain ⟨i, hi⟩ := d.exists_piece_mem hp
  fin_cases i
  · exact (hzero hi).elim
  · exact (hone hi).elim
  · exact (htwo hi).elim
  · exact hi

end Puzzling139335.N7
