import ErdosProblems.Erdos1148.GaussFrameCoordinates
import ErdosProblems.Erdos1148.BowenTube

/-! # Relative matrices in the Gauss chart -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma unstableHorocycle_zero : unstableHorocycle 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unstableHorocycle]

lemma unstableHorocycle_neg (r : ℝ) : unstableHorocycle (-r) = (unstableHorocycle r)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← unstableHorocycle_add, neg_add_cancel, unstableHorocycle_zero]

lemma gaussFrame_relative (g : SL(2, ℝ)) (r s x y h k : ℝ) (hh : h ≠ 0) (hk : k ≠ 0) :
    (g * unstableHorocycle r * upperTriangularFrame x h hh)⁻¹ *
        (g * unstableHorocycle s * upperTriangularFrame y k hk) =
      (upperTriangularFrame x h hh)⁻¹ * unstableHorocycle (s - r) *
        upperTriangularFrame y k hk := by
  calc
    _ = (upperTriangularFrame x h hh)⁻¹ *
        ((unstableHorocycle r)⁻¹ * unstableHorocycle s) * upperTriangularFrame y k hk := by group
    _ = _ := by
      rw [← unstableHorocycle_neg, ← unstableHorocycle_add]
      congr 3
      ring

theorem upperHorocycleUpper_matrix (x y h k q : ℝ) (hh : h ≠ 0) (hk : k ≠ 0) :
    (((upperTriangularFrame x h hh)⁻¹ * unstableHorocycle q * upperTriangularFrame y k hk :
        SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![k / h - x * k * q / h, (y - x) / (h * k) - x * y * q / (h * k);
        h * k * q, h / k + h * y * q / k] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperTriangularFrame, unstableHorocycle, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

end Erdos1148.DukeArithmetic
