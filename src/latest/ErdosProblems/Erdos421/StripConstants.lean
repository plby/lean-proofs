import ErdosProblems.Erdos421.DifferenceConstants
import ErdosProblems.Erdos421.ZetaGrowth

/-! # Constants in the zeta strip estimate, uniformly in the difference order -/

namespace Erdos421

theorem one_sub_two_rpow_neg_half_lower {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    d / 8 ≤ 1 - (2 : ℝ) ^ (-d / 2) := by
  have hlog : 1 / 2 ≤ Real.log 2 := by
    have h := log_difference_lower (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  let x : ℝ := d * Real.log 2 / 2
  have hx : 0 < x := by dsimp only [x]; positivity
  have hx1 : x ≤ 1 := by dsimp only [x]; nlinarith
  have hdx : d / 8 ≤ x / 2 := by dsimp only [x]; nlinarith
  have he : (2 : ℝ) ^ (-d / 2) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    dsimp only [x]
    ring
  have hexp : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hq : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by linarith) hexp
  have hfrac : x / 2 ≤ x / (1 + x) :=
    div_le_div_of_nonneg_left hx.le (by linarith) (by linarith)
  have hid : x / (1 + x) = 1 - 1 / (1 + x) := by field_simp; ring
  rw [he]
  rw [hid] at hfrac
  linarith

theorem zetaStripConstant_le (R : ℕ) {K : ℕ} (hK : 2 ≤ K) :
    zetaStripConstant R K ≤ 131072 * K * ((2 ^ R : ℕ) : ℝ) := by
  have hd := logarithmicSavingExponent_pos R (by omega : 0 < K)
  have hd1 : logarithmicSavingExponent R K ≤ 1 :=
    (logarithmicSavingExponent_le_half R hK).trans (by norm_num)
  have hden := one_sub_two_rpow_neg_half_lower hd hd1
  have hc := logarithmicSavingConstant_pos R
  have hcupper := logarithmicSavingConstant_le R
  unfold zetaStripConstant
  calc
    _ ≤ 4 * logarithmicSavingConstant R / (logarithmicSavingExponent R K / 8) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ 4 * 4096 / (logarithmicSavingExponent R K / 8) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by
      unfold logarithmicSavingExponent
      field_simp
      ring

theorem riemannZeta_near_one_explicit_bound (R K : ℕ)
    (hK : 2 * R + 4 ≤ K) (hK8 : 8 ≤ K) (s : ℂ) (hs1 : s.re ≤ 1)
    (hstrip : 1 - s.re ≤ logarithmicSavingExponent R K / 2)
    (ht : (2 : ℝ) ^ (R + 1) ≤ |s.im|) :
    ‖riemannZeta s‖ ≤
      (1 + Real.log |s.im| / (((R : ℝ) + 1) * Real.log 2)) *
        (2 : ℝ) ^ (1 - s.re) * |s.im| ^ ((1 - s.re) / ((R : ℝ) + 1)) +
      131072 * K * ((2 ^ R : ℕ) : ℝ) + 9 := by
  have hb := riemannZeta_near_one_growth_bound R K hK hK8 s hs1 hstrip ht
  have hc := zetaStripConstant_le R (by omega : 2 ≤ K)
  linarith

end Erdos421
