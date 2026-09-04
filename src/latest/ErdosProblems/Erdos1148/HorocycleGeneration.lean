import ErdosProblems.Erdos1148.HorocycleContraction
import ErdosProblems.Erdos1148.GaussFrameCoordinates

/-! # The two horocycle subgroups generate SL(2,R) -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma diagonal_frame_horocycle_product (h : ℝ) (hh : h ≠ 0) :
    upperTriangularFrame 0 h hh = stableHorocycle (h - 1) * unstableHorocycle 1 *
      stableHorocycle (h⁻¹ - 1) * unstableHorocycle (-h) := by
  apply Subtype.ext
  change (upperTriangularFrame 0 h hh).1 =
    (stableHorocycle (h - 1)).1 * (unstableHorocycle 1).1 *
      (stableHorocycle (h⁻¹ - 1)).1 * (unstableHorocycle (-h)).1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperTriangularFrame, stableHorocycle, unstableHorocycle,
      Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp [hh] <;> ring_nf <;> simp

lemma upperTriangularFrame_diagonal_stable (x h : ℝ) (hh : h ≠ 0) :
    upperTriangularFrame x h hh = upperTriangularFrame 0 h hh * stableHorocycle (x / h ^ 2) := by
  apply Subtype.ext
  change (upperTriangularFrame x h hh).1 =
    (upperTriangularFrame 0 h hh).1 * (stableHorocycle (x / h ^ 2)).1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperTriangularFrame, stableHorocycle, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hh] <;> ring

theorem specialLinear_fixed_of_horocycles {X : Type*} [MulAction SL(2, ℝ) X] {x : X}
    (hs : ∀ r : ℝ, stableHorocycle r • x = x)
    (hu : ∀ r : ℝ, unstableHorocycle r • x = x) (g : SL(2, ℝ)) : g • x = x := by
  have hupper (a h : ℝ) (hh : h ≠ 0) : upperTriangularFrame a h hh • x = x := by
    rw [upperTriangularFrame_diagonal_stable, diagonal_frame_horocycle_product]
    simp only [mul_smul, hs, hu]
  have hregular (g : SL(2, ℝ)) (hg : g 0 0 ≠ 0) : g • x = x := by
    rw [gauss_frame_decomposition g hg, mul_smul, hupper, hu]
  by_cases hg : g 0 0 ≠ 0
  · exact hregular g hg
  · have hg00 : g 0 0 = 0 := not_ne_iff.mp hg
    have hg10 : g 1 0 ≠ 0 := by
      intro h
      have hdet := Matrix.SpecialLinearGroup.det_coe g
      rw [Matrix.det_fin_two, hg00, h] at hdet
      norm_num at hdet
    have hentry : (stableHorocycle 1 * g) 0 0 ≠ 0 := by
      change ((stableHorocycle 1 * g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ≠ 0
      rw [Matrix.SpecialLinearGroup.coe_mul]
      simpa [stableHorocycle, Matrix.mul_apply, Fin.sum_univ_two, hg00] using hg10
    have hfixed := hregular (stableHorocycle 1 * g) hentry
    calc
      g • x = (stableHorocycle 1)⁻¹ • ((stableHorocycle 1 * g) • x) := by
        simp only [mul_smul, inv_smul_smul]
      _ = (stableHorocycle 1)⁻¹ • x := by rw [hfixed]
      _ = x := by
        have h := hs 1
        calc
          (stableHorocycle 1)⁻¹ • x = (stableHorocycle 1)⁻¹ • (stableHorocycle 1 • x) := by rw [h]
          _ = x := inv_smul_smul _ _

end Erdos1148.DukeArithmetic
