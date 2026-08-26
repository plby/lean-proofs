import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Exponent comparisons for a one-tenth interval threshold -/

namespace Erdos421

theorem twoFactor_exponent_b {r e d : ℝ} (hr : 5 ≤ r) (he : 0 ≤ e) (hd : d ≤ e / 2) :
    (2 * r) * (9 / 10 - e) + 1 ≤ (1 - d) * (2 * r) := by
  have hrd := mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ 2 * r)
  have hre := mul_nonneg (by linarith : 0 ≤ r) he
  nlinarith

theorem twoFactor_exponent_d {r e d : ℝ} (hr : 5 ≤ r) (he : 0 ≤ e) (hd : d ≤ e / 2) :
    (9 / 10 - e) * (2 * r - 2) ≤
      (-d) * (2 * r) + (1 - 1 / r) * (2 * r - 1) := by
  have hrp : 0 < r := by linarith
  have hbase : 0 ≤ (r - 1) * (r - 5) / (5 * r) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  have hrd := mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ 2 * r)
  have heterm := mul_nonneg he (by linarith : 0 ≤ r - 2)
  have hid : ((-d) * (2 * r) + (1 - 1 / r) * (2 * r - 1)) -
      ((9 / 10 - e) * (2 * r - 2)) =
      (r - 1) * (r - 5) / (5 * r) + 2 * (r - 1) * e - 2 * r * d := by
    field_simp
    ring
  nlinarith

theorem twoFactor_exponent_c {r e d : ℝ} (hr : 1 ≤ r) (he : 0 ≤ e)
    (hd : d ≤ 1 / (60 * r)) : 9 / 10 - e ≤ (-d) * (3 * r) + 1 := by
  have hrp : 0 < r := by linarith
  have hm := (le_div_iff₀ (by positivity : 0 < 60 * r)).mp hd
  nlinarith

theorem twoFactor_lower_length_exponent {r : ℝ} (hr : 1 ≤ r) :
    1 ≤ (1 / (r + 1)) * (2 * r) := by
  have hp : 0 < r + 1 := by linarith
  calc
    1 ≤ (2 * r) / (r + 1) := (one_le_div hp).mpr (by linarith)
    _ = _ := by ring

end Erdos421
