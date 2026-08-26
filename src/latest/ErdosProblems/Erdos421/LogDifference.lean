import ErdosProblems.Erdos421.LogarithmicSpacing

/-! # Increment bounds for a difference of logarithmic phases -/

namespace Erdos421

noncomputable def logDifferenceIncrement (x h : ℝ) : ℝ :=
  (Real.log (x + 1) - Real.log x) - (Real.log (x + h + 1) - Real.log (x + h))

theorem logDifferenceIncrement_eq {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    logDifferenceIncrement x h = Real.log (1 + h / (x * (x + h + 1))) := by
  have hx1 : x + 1 ≠ 0 := by positivity
  have hxh : x + h ≠ 0 := by positivity
  have hxh1 : x + h + 1 ≠ 0 := by positivity
  have heq : 1 + h / (x * (x + h + 1)) =
      (x + 1) * (x + h) / (x * (x + h + 1)) := by
    field_simp
    ring
  rw [heq, Real.log_div (mul_ne_zero hx1 hxh) (mul_ne_zero hx.ne' hxh1),
    Real.log_mul hx1 hxh, Real.log_mul hx.ne' hxh1]
  unfold logDifferenceIncrement
  ring

theorem logDifferenceIncrement_nonneg {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    0 ≤ logDifferenceIncrement x h := by
  rw [logDifferenceIncrement_eq hx hh]
  apply Real.log_nonneg
  have hq : 0 ≤ h / (x * (x + h + 1)) := by positivity
  linarith

theorem logDifferenceIncrement_upper {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    logDifferenceIncrement x h ≤ h / x ^ 2 := by
  rw [logDifferenceIncrement_eq hx hh]
  have hlog := Real.log_le_sub_one_of_pos
    (by positivity : 0 < 1 + h / (x * (x + h + 1)))
  have hden : x ^ 2 ≤ x * (x + h + 1) := by nlinarith
  have hdiv := div_le_div_of_nonneg_left hh (sq_pos_of_pos hx) hden
  linarith

theorem logDifferenceIncrement_antitone {x y h : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hh : 0 ≤ h) :
    logDifferenceIncrement y h ≤ logDifferenceIncrement x h := by
  have hy := hx.trans_le hxy
  rw [logDifferenceIncrement_eq hx hh, logDifferenceIncrement_eq hy hh]
  have hden : x * (x + h + 1) ≤ y * (y + h + 1) := by
    exact mul_le_mul hxy (by linarith) (by positivity) hy.le
  have hdiv := div_le_div_of_nonneg_left hh (by positivity : 0 < x * (x + h + 1)) hden
  exact Real.log_le_log (by positivity) (by linarith)

theorem logDifferenceIncrement_drop_lower {x y h : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hh : 0 < h) :
    h * (y - x) / (y * (x + 1) * (x + h)) ≤
      logDifferenceIncrement x h - logDifferenceIncrement y h := by
  rcases eq_or_lt_of_le hxy with rfl | hxy
  · simp
  have hy := hx.trans hxy
  have hx1 : 0 < x + 1 := by positivity
  have hxh : 0 < x + h := by positivity
  have hxh1 : 0 < x + h + 1 := by positivity
  have hyh1 : 0 < y + h + 1 := by positivity
  have hden : x * (x + h + 1) < y * (y + h + 1) :=
    mul_lt_mul hxy (by linarith) (by positivity) hy.le
  have hfrac : h / (y * (y + h + 1)) < h / (x * (x + h + 1)) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    exact mul_lt_mul_of_pos_left hden hh
  have hlog := log_difference_lower
    (by positivity : 0 < 1 + h / (y * (y + h + 1)))
    (show 1 + h / (y * (y + h + 1)) < 1 + h / (x * (x + h + 1)) by linarith)
  have hpos : 1 + h / (x * (x + h + 1)) ≠ 0 := by positivity
  have heq : ((1 + h / (x * (x + h + 1))) - (1 + h / (y * (y + h + 1)))) /
      (1 + h / (x * (x + h + 1))) =
        (h * (y - x) / (y * (x + 1) * (x + h))) * ((x + y + h + 1) / (y + h + 1)) := by
    field_simp
    ring
  rw [heq] at hlog
  have hratio : 1 ≤ (x + y + h + 1) / (y + h + 1) :=
    (one_le_div hyh1).mpr (by linarith)
  have hnum : 0 ≤ h * (y - x) / (y * (x + 1) * (x + h)) := by positivity
  calc
    _ ≤ (h * (y - x) / (y * (x + 1) * (x + h))) *
        ((x + y + h + 1) / (y + h + 1)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio hnum
    _ ≤ Real.log (1 + h / (x * (x + h + 1))) -
        Real.log (1 + h / (y * (y + h + 1))) := hlog
    _ = _ := by rw [logDifferenceIncrement_eq hx hh.le, logDifferenceIncrement_eq hy hh.le]

theorem logDifferenceIncrement_drop_lower_bounded {x y h B : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hh : 0 < h) (hyB : y + h + 1 ≤ B) :
    h * (y - x) / B ^ 3 ≤ logDifferenceIncrement x h - logDifferenceIncrement y h := by
  have hy := hx.trans_le hxy
  have hB : 0 < B := by linarith
  have hden : y * (x + 1) * (x + h) ≤ B ^ 3 := by
    calc
      _ ≤ B * B * B := by gcongr <;> linarith
      _ = _ := by ring
  exact (div_le_div_of_nonneg_left (by positivity)
    (by positivity : 0 < y * (x + 1) * (x + h)) hden).trans
      (logDifferenceIncrement_drop_lower hx hxy hh)

end Erdos421
