import ErdosProblems.Erdos1148.RealSeriesCutoff

/-! # Real-power identities used in quantitative hyperbola estimates -/

namespace Erdos1148.DukeArithmetic

lemma rpow_hyperbola_error_weight {x m : ℝ} (hx : 0 ≤ x) (hm : 0 < m) (s : ℝ) :
    m ^ (-s) * (x / m) ^ (-s) = x ^ (-s) := by
  rw [Real.div_rpow hx hm.le]
  exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos hm _).ne'

lemma rpow_hyperbola_main_weight {x m : ℝ} (hx : 0 ≤ x) (hm : 0 < m) (s : ℝ) :
    m ^ (-s) * (x / m) ^ (1 - s) = x ^ (1 - s) * m ^ (-1 : ℝ) := by
  calc
    _ = x ^ (1 - s) * (m ^ (-s) / m ^ (1 - s)) := by
      rw [Real.div_rpow hx hm.le]
      ring
    _ = _ := by rw [← Real.rpow_sub hm, show -s - (1 - s) = -1 by ring]

lemma rpow_hyperbola_square_error {x : ℝ} (hx : 0 < x) (s : ℝ) :
    x * (x * x) ^ (-s) = x ^ (1 - 2 * s) := by
  rw [Real.mul_rpow hx.le hx.le]
  calc
    _ = x ^ (1 : ℝ) * x ^ (-s) * x ^ (-s) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hx, ← Real.rpow_add hx]; congr 1; ring

lemma rpow_hyperbola_square_main_tail {x : ℝ} (hx : 0 < x) (s : ℝ) :
    (x * x) ^ (1 - s) * x ^ (-1 : ℝ) = x ^ (1 - 2 * s) := by
  rw [Real.mul_rpow hx.le hx.le, ← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  ring

lemma rpow_hyperbola_cross_term {x : ℝ} (hx : 0 < x) (s : ℝ) :
    x ^ (1 - s) * x ^ (-s) = x ^ (1 - 2 * s) := by
  rw [← Real.rpow_add hx]
  congr 1
  ring

end Erdos1148.DukeArithmetic
