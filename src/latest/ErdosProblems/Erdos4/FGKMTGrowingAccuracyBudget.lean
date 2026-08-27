import ErdosProblems.Erdos4.FGKMTJointAccuracyBudget

/-! Explicit logarithmic powers absorb the errors from a growing family of tuple sites. -/

namespace Erdos4.FGKMT

theorem growing_joint_exponent_budget {L K r v : ℝ}
    (hL : 12 ≤ L) (hK : L ^ 100 / 2 ≤ K)
    (hr0 : 0 ≤ r) (hr : r ≤ 3 * L) (hv0 : 0 ≤ v) (hv : v ≤ 3 * L)
    (hlarge : 2 * (36 + 324 / Real.log 2) ≤ L ^ 16) :
    2 * r ^ 2 / K + 2 * r ^ 3 * v / (K * Real.log 2) ≤ (1 / L ^ 80) / 2 := by
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hKpos : 0 < K := (by positivity : 0 < L ^ 100 / 2).trans_le hK
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hr2 : r ^ 2 ≤ (3 * L) ^ 2 := pow_le_pow_left₀ hr0 hr 2
  have hr3 : r ^ 3 ≤ (3 * L) ^ 3 := pow_le_pow_left₀ hr0 hr 3
  have hfirst : 2 * r ^ 2 / K ≤ 36 * L ^ 2 / L ^ 100 := by
    calc
      _ ≤ (2 * (3 * L) ^ 2) / K :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr2 (by norm_num)) hKpos.le
      _ ≤ (2 * (3 * L) ^ 2) / (L ^ 100 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hK
      _ = _ := by field_simp; ring
  have hnum : 2 * r ^ 3 * v ≤ 162 * L ^ 4 := by
    calc
      _ ≤ 2 * (3 * L) ^ 3 * (3 * L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr3 (by norm_num)) hv hv0 (by positivity)
      _ = _ := by ring
  have hsecond : 2 * r ^ 3 * v / (K * Real.log 2) ≤
      324 * L ^ 4 / (L ^ 100 * Real.log 2) := by
    calc
      _ ≤ (162 * L ^ 4) / (K * Real.log 2) := div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (162 * L ^ 4) / ((L ^ 100 / 2) * Real.log 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right hK hlog2.le)
      _ = _ := by field_simp; ring
  have hL24 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hcoeff : 36 + 324 / Real.log 2 ≤ L ^ 16 / 2 := by linarith
  calc
    _ ≤ 36 * L ^ 2 / L ^ 100 + 324 * L ^ 4 / (L ^ 100 * Real.log 2) :=
      add_le_add hfirst hsecond
    _ = (36 * L ^ 2 + (324 / Real.log 2) * L ^ 4) / L ^ 100 := by field_simp
    _ ≤ ((36 + 324 / Real.log 2) * L ^ 4) / L ^ 100 :=
      div_le_div_of_nonneg_right (by nlinarith) (pow_nonneg hLpos.le _)
    _ ≤ ((L ^ 16 / 2) * L ^ 4) / L ^ 100 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hLpos.le _))
        (pow_nonneg hLpos.le _)
    _ = _ := by field_simp

end Erdos4.FGKMT
