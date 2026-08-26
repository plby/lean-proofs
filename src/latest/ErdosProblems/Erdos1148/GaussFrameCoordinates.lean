import ErdosProblems.Erdos1148.HorocycleFrames

/-! # Gauss coordinates near the identity -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem gauss_frame_decomposition (g : SL(2, ℝ)) (ha : g 0 0 ≠ 0) :
    g = unstableHorocycle (g 1 0 / g 0 0) *
      upperTriangularFrame (g 0 0 * g 0 1) (g 0 0) ha := by
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet
  apply Subtype.ext
  change g.1 = (unstableHorocycle (g 1 0 / g 0 0)).1 *
    (upperTriangularFrame (g 0 0 * g 0 1) (g 0 0) ha).1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unstableHorocycle, upperTriangularFrame, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> nlinarith [hdet]

theorem entryCloseOne_gauss_coordinates {η : ℝ} (hη : η ≤ 1 / 2) {g : SL(2, ℝ)}
    (hg : EntryCloseOne η g) :
    ∃ (r x h : ℝ) (hh : 0 < h), |r| ≤ 2 * η ∧ |x| ≤ 2 * η ∧ |h - 1| ≤ η ∧
      g = unstableHorocycle r * upperTriangularFrame x h hh.ne' := by
  have ha := abs_le.mp hg.1
  have ha0 : 0 < g 0 0 := by linarith [ha.1]
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hg.1
  refine ⟨g 1 0 / g 0 0, g 0 0 * g 0 1, g 0 0, ha0, ?_, ?_, hg.1,
    gauss_frame_decomposition g ha0.ne'⟩
  · rw [abs_div, abs_of_pos ha0]
    apply (div_le_iff₀ ha0).mpr
    nlinarith [hg.2.2.1]
  · rw [abs_mul, abs_of_pos ha0]
    have hb : |g 0 1| ≤ η := hg.2.1
    calc
      _ ≤ (3 / 2) * η := mul_le_mul (by linarith [ha.2]) hb (abs_nonneg _) (by norm_num)
      _ ≤ 2 * η := by linarith

end Erdos1148.DukeArithmetic
