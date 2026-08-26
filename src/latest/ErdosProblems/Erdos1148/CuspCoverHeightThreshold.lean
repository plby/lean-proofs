import ErdosProblems.Erdos1148.BufferedExcursionScale

/-! # A common height threshold for pattern counting and excursion refinement -/

namespace Erdos1148.DukeArithmetic

theorem exists_cusp_cover_height_threshold (K Hp : ℝ) {ε : ℝ} (hε : 0 < ε) (hHp : 0 < Hp) :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      Hp ≤ H ∧ Real.exp 1 ≤ H ^ 4 ∧ 96 / cuspEndpointLengthSqLower ≤ H ∧
      (2 * Real.log K + 1 / 2) / (4 * Real.log H) ≤ ε := by
  let R := (2 * Real.log K + 1 / 2) / (4 * ε)
  let H₀ := 2 + Hp + Real.exp 1 + 96 / cuspEndpointLengthSqLower + Real.exp R
  have hquot : 0 < 96 / cuspEndpointLengthSqLower :=
    div_pos (by norm_num) cuspEndpointLengthSqLower_pos
  have hH₀ : 1 < H₀ := by dsimp only [H₀]; linarith [Real.exp_pos 1, Real.exp_pos R]
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  have hH1 : 1 < H := hH₀.trans_le hH
  have hHpH : Hp ≤ H := by dsimp only [H₀] at hH; linarith [Real.exp_pos 1, Real.exp_pos R]
  have hlarge : 96 / cuspEndpointLengthSqLower ≤ H := by
    dsimp only [H₀] at hH
    linarith [Real.exp_pos 1, Real.exp_pos R]
  have hwindow : Real.exp 1 ≤ H ^ 4 := by
    have hExp : Real.exp 1 ≤ H := by dsimp only [H₀] at hH; linarith [Real.exp_pos R]
    exact hExp.trans (by nlinarith [sq_nonneg (H ^ 2 - 1)])
  have hR : R ≤ Real.log H := by
    have hExp : Real.exp R ≤ H := by dsimp only [H₀] at hH; linarith [Real.exp_pos 1]
    have h := Real.log_le_log (Real.exp_pos R) hExp
    simpa only [Real.log_exp] using h
  refine ⟨hHpH, hwindow, hlarge, ?_⟩
  apply (div_le_iff₀ (mul_pos (by norm_num) (Real.log_pos hH1))).mpr
  have h := (div_le_iff₀ (show 0 < 4 * ε by positivity)).mp hR
  nlinarith

end Erdos1148.DukeArithmetic
