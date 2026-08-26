import ErdosProblems.Erdos1148.GaussRelativeFrames

/-! # Quantitative relative-entry bounds in a bounded Gauss chart -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma abs_ratio_sub_one_le {h k δ : ℝ} (hh : 1 / 2 ≤ h) (hδ : 0 ≤ δ)
    (hdiff : |k - h| ≤ δ) : |k / h - 1| ≤ 2 * δ := by
  have hpos : 0 < h := by linarith
  rw [show k / h - 1 = (k - h) / h by field_simp, abs_div, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  nlinarith

lemma abs_gauss_diagonal_perturbation_le {x k q h ε : ℝ} (hx : |x| ≤ 1)
    (hk0 : 0 ≤ k) (hk2 : k ≤ 2) (hh : 1 / 2 ≤ h) (hε : 0 ≤ ε) (hq : |q| ≤ ε) :
    |x * k * q / h| ≤ 4 * ε := by
  have hpos : 0 < h := by linarith
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hk0, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  have hxk : |x| * k ≤ 2 := by
    calc
      _ ≤ 1 * 2 := mul_le_mul hx hk2 hk0 zero_le_one
      _ = 2 := one_mul _
  have hnum : |x| * k * |q| ≤ 2 * ε := mul_le_mul hxk hq (abs_nonneg _) (by norm_num)
  nlinarith

lemma abs_gauss_upper_perturbation_le {x y q h k ε : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hh : 1 / 2 ≤ h) (hk : 1 / 2 ≤ k) (hε : 0 ≤ ε) (hq : |q| ≤ ε) :
    |x * y * q / (h * k)| ≤ 4 * ε := by
  have hpos : 0 < h := by linarith
  have hkpos : 0 < k := by linarith
  have hhklow : 1 / 4 ≤ h * k := by nlinarith [mul_le_mul hh hk (by norm_num) hpos.le]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (mul_pos hpos hkpos)]
  apply (div_le_iff₀ (mul_pos hpos hkpos)).mpr
  have hxy : |x| * |y| ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hx hy (abs_nonneg _) zero_le_one
  have hnum : |x| * |y| * |q| ≤ ε := by
    simpa only [one_mul] using mul_le_mul hxy hq (abs_nonneg _) zero_le_one
  nlinarith

theorem upperHorocycleUpper_entry_bounds {x y h k q δ ε : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hh : 1 / 2 ≤ h) (hk : 1 / 2 ≤ k)
    (hh2 : h ≤ 2) (hk2 : k ≤ 2) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hheight : |k - h| ≤ δ) (hstable : |y - x| ≤ δ) (hunstable : |q| ≤ ε) :
    let M := (upperTriangularFrame x h (by linarith : h ≠ 0))⁻¹ * unstableHorocycle q *
      upperTriangularFrame y k (by linarith : k ≠ 0)
    EntryCloseOne (8 * δ) M ∧ |M 1 0| ≤ 4 * ε := by
  have hpos : 0 < h := by linarith
  have hkpos : 0 < k := by linarith
  have hbaseA := abs_ratio_sub_one_le hh hδ hheight
  have hbaseD := abs_ratio_sub_one_le (h := k) (k := h) hk hδ
    (by simpa only [abs_sub_comm] using hheight)
  have hpertA := abs_gauss_diagonal_perturbation_le hx hkpos.le hk2 hh hε hunstable
  have hpertD : |h * y * q / k| ≤ 4 * ε := by
    simpa only [mul_comm] using abs_gauss_diagonal_perturbation_le hy hpos.le hh2 hk hε hunstable
  have hpertB := abs_gauss_upper_perturbation_le hx hy hh hk hε hunstable
  have hbaseB : |(y - x) / (h * k)| ≤ 4 * δ := by
    rw [abs_div, abs_of_pos (mul_pos hpos hkpos)]
    apply (div_le_iff₀ (mul_pos hpos hkpos)).mpr
    have hhklow : 1 / 4 ≤ h * k := by nlinarith [mul_le_mul hh hk (by norm_num) hpos.le]
    nlinarith
  have hA : |k / h - x * k * q / h - 1| ≤ 8 * δ := by
    rw [show k / h - x * k * q / h - 1 = (k / h - 1) - x * k * q / h by ring]
    exact (abs_sub _ _).trans (by linarith)
  have hB : |(y - x) / (h * k) - x * y * q / (h * k)| ≤ 8 * δ :=
    (abs_sub _ _).trans (by linarith)
  have hC : |h * k * q| ≤ 4 * ε := by
    rw [abs_mul, abs_mul, abs_of_pos hpos, abs_of_pos hkpos]
    have hhk : h * k ≤ 4 := by nlinarith [mul_le_mul hh2 hk2 hkpos.le (by norm_num)]
    exact mul_le_mul hhk hunstable (abs_nonneg _) (by norm_num)
  have hD : |h / k + h * y * q / k - 1| ≤ 8 * δ := by
    rw [show h / k + h * y * q / k - 1 = (h / k - 1) + h * y * q / k by ring]
    exact (abs_add_le _ _).trans (by linarith)
  dsimp only
  constructor
  · unfold EntryCloseOne
    change |(((upperTriangularFrame x h hpos.ne')⁻¹ * unstableHorocycle q *
      upperTriangularFrame y k hkpos.ne' : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - 1| ≤ _ ∧ _
    rw [upperHorocycleUpper_matrix]
    simpa only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using And.intro hA ⟨hB, by linarith [hC], hD⟩
  · have hm := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ => m 1 0)
      (upperHorocycleUpper_matrix x y h k q hpos.ne' hkpos.ne')
    change |(((upperTriangularFrame x h hpos.ne')⁻¹ * unstableHorocycle q *
      upperTriangularFrame y k hkpos.ne' : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0| ≤ _
    rw [hm]
    exact hC

end Erdos1148.DukeArithmetic
