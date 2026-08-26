import ErdosProblems.Erdos1148.IwasawaFrames

/-! # The upper triangular frame chart and its relative matrix -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

noncomputable def upperTriangularFrame (x h : ℝ) (hh : h ≠ 0) : SL(2, ℝ) :=
  ⟨!![h, x / h; 0, h⁻¹], by simp [hh]⟩

lemma upperHalfPlane_toSL2R_eq_frame (z : UpperHalfPlane) :
    z.toSL2R = upperTriangularFrame z.re (Real.sqrt z.im) (Real.sqrt_ne_zero'.mpr z.im_pos) := by
  apply Subtype.ext
  simp [UpperHalfPlane.coe_toSL2R, upperTriangularFrame, one_div]

theorem upperTriangularFrame_relative (x y h k : ℝ) (hh : h ≠ 0) (hk : k ≠ 0) :
    (((upperTriangularFrame x h hh)⁻¹ * upperTriangularFrame y k hk : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![k / h, (y - x) / (h * k); 0, h / k] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperTriangularFrame, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

theorem upperTriangularFrame_relative_close {x y h k H δ : ℝ}
    (hH : 0 < H) (hh : H ≤ h) (hk : H ≤ k) (hδ : 0 ≤ δ)
    (hheight : |k - h| ≤ δ * H) (hhor : |y - x| ≤ δ * H ^ 2) :
    EntryCloseOne δ ((upperTriangularFrame x h (hH.trans_le hh).ne')⁻¹ *
      upperTriangularFrame y k (hH.trans_le hk).ne') := by
  have hh0 := hH.trans_le hh
  have hk0 := hH.trans_le hk
  have hdiag1 : |k / h - 1| ≤ δ := by
    rw [show k / h - 1 = (k - h) / h by field_simp, abs_div, abs_of_pos hh0]
    exact (div_le_iff₀ hh0).mpr (hheight.trans (mul_le_mul_of_nonneg_left hh hδ))
  have hdiag2 : |h / k - 1| ≤ δ := by
    rw [show h / k - 1 = (h - k) / k by field_simp, abs_div, abs_of_pos hk0, abs_sub_comm h k]
    exact (div_le_iff₀ hk0).mpr (hheight.trans (mul_le_mul_of_nonneg_left hk hδ))
  have hhor' : |(y - x) / (h * k)| ≤ δ := by
    rw [abs_div, abs_of_pos (mul_pos hh0 hk0)]
    apply (div_le_iff₀ (mul_pos hh0 hk0)).mpr
    exact hhor.trans (mul_le_mul_of_nonneg_left
      (by simpa only [pow_two] using mul_le_mul hh hk hH.le hh0.le) hδ)
  change |(((upperTriangularFrame x h hh0.ne')⁻¹ * upperTriangularFrame y k hk0.ne' : SL(2, ℝ)) :
    Matrix (Fin 2) (Fin 2) ℝ) 0 0 - 1| ≤ δ ∧ _
  rw [upperTriangularFrame_relative]
  simpa only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, abs_zero] using
    And.intro hdiag1 ⟨hhor', hδ, hdiag2⟩

end Erdos1148.DukeArithmetic
