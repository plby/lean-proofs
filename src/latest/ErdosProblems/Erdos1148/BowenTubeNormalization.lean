import ErdosProblems.Erdos1148.BowenTube

/-! # Removing the flow direction from an entrywise Bowen tube -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma mul_diagonalFlow_neg_two_log_matrix (g : SL(2, ℝ)) {k : ℝ} (hk : 0 < k) :
    ((g * diagonalFlow (-(2 * Real.log k)) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![g 0 0 / k, g 0 1 * k; g 1 0 / k, g 1 1 * k] := by
  change g.1 * (diagonalFlow (-(2 * Real.log k))).1 = _
  have hdiv : -(2 * Real.log k) / 2 = -Real.log k := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalFlow, Matrix.mul_apply, Fin.sum_univ_two, hdiv, Real.exp_neg,
      Real.exp_log hk, div_eq_mul_inv]

theorem entryCloseOne_of_bowenTube_grid {η δ k : ℝ} {g : SL(2, ℝ)}
    (hη : η ≤ 1 / 2) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hg : EntryBowenTube η δ g)
    (hk : 1 - η ≤ k) (hak : g 0 0 ∈ Set.Icc k (k + δ)) :
    EntryCloseOne (3 * δ) (g * diagonalFlow (-(2 * Real.log k))) := by
  have hkhalf : 1 / 2 ≤ k := by linarith
  have hkpos : 0 < k := by linarith
  have hkupper : k ≤ 3 / 2 := by linarith [(abs_le.mp hg.1).2, hak.1]
  have hakabs : |g 0 0 - k| ≤ δ := abs_le.mpr ⟨by linarith [hak.1], by linarith [hak.2]⟩
  have hdabs : |g 1 1| ≤ 3 / 2 := by
    have hd := abs_le.mp hg.2.2.2
    exact abs_le.mpr ⟨by linarith [hd.1], by linarith [hd.2]⟩
  have hdet := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet
  have hdk : g 1 1 * k - 1 = g 1 1 * (k - g 0 0) + g 0 1 * g 1 0 := by
    nlinarith [hdet]
  unfold EntryCloseOne
  change |((g * diagonalFlow (-(2 * Real.log k)) : SL(2, ℝ)) :
    Matrix (Fin 2) (Fin 2) ℝ) 0 0 - 1| ≤ 3 * δ ∧ _
  rw [mul_diagonalFlow_neg_two_log_matrix g hkpos]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show g 0 0 / k - 1 = (g 0 0 - k) / k by field_simp,
      abs_div, abs_of_pos hkpos]
    apply (div_le_iff₀ hkpos).mpr
    nlinarith
  · rw [abs_mul, abs_of_pos hkpos]
    calc
      _ ≤ δ * (3 / 2) := mul_le_mul hg.2.1 hkupper hkpos.le hδ
      _ ≤ 3 * δ := by linarith
  · rw [abs_div, abs_of_pos hkpos]
    apply (div_le_iff₀ hkpos).mpr
    nlinarith [hg.2.2.1]
  · rw [hdk]
    calc
      _ ≤ |g 1 1 * (k - g 0 0)| + |g 0 1 * g 1 0| := abs_add_le _ _
      _ = |g 1 1| * |g 0 0 - k| + |g 0 1| * |g 1 0| := by
        rw [abs_mul, abs_mul, abs_sub_comm k]
      _ ≤ (3 / 2) * δ + δ * δ := add_le_add
        (mul_le_mul hdabs hakabs (abs_nonneg _) (by norm_num))
        (mul_le_mul hg.2.1 hg.2.2.1 (abs_nonneg _) hδ)
      _ ≤ 3 * δ := by nlinarith

end Erdos1148.DukeArithmetic
