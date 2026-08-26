import ErdosProblems.Erdos421.LongIntervalScale

/-! # Parameters for the square-root boundary in the Buchstab induction -/

namespace Erdos421

theorem inverse_rpow_of_lower_scale {K L R A : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hR : 0 < R) (hA : 0 ≤ A) (hLR : L / K ≤ R) :
    1 / R ^ A ≤ K ^ A / L ^ A := by
  have hp := Real.rpow_le_rpow (div_nonneg hL.le hK.le) hLR hA
  rw [Real.div_rpow hL.le hK.le] at hp
  have hm := (div_le_iff₀ (Real.rpow_pos_of_pos hK A)).mp hp
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hR A) (Real.rpow_pos_of_pos hL A)).mpr
  simpa only [one_mul, mul_one, mul_comm] using hm

theorem sqrt_boundary_bounds {a b : ℝ} (hb : 4 ≤ b) (ha : b / 2 ≤ a) (hab : a ≤ b) :
    1 < Real.sqrt a ∧ Real.sqrt a ≤ Real.sqrt b ∧ Real.sqrt b ≤ 2 * Real.sqrt a ∧
      Real.log b / 4 ≤ Real.log (Real.sqrt a) := by
  obtain ⟨ha1, hla, hhalf, _⟩ := half_interval_log_bounds hb ha hab
  have hap : 0 < a := by linarith
  have hbp : 0 < b := by linarith
  have hsa : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt hap.le
  have hsb : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hbp.le
  have hsa0 := Real.sqrt_nonneg a
  have hsb0 := Real.sqrt_nonneg b
  refine ⟨?_, Real.sqrt_le_sqrt hab, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · rw [Real.log_sqrt hap.le]
    linarith

theorem sqrt_boundary_main_error {a b : ℝ} (hb : 4 ≤ b) (ha : b / 2 ≤ a) (hab : a ≤ b) :
    (b - a) * (Real.sqrt b - Real.sqrt a) /
      (Real.sqrt a * (Real.log (Real.sqrt a)) ^ 2) ≤
        16 * (b - a) ^ 2 / (b * (Real.log b) ^ 2) := by
  obtain ⟨hsa1, hsab, _, hlog⟩ := sqrt_boundary_bounds hb ha hab
  have hap : 0 < a := by linarith
  have hbp : 0 < b := by linarith
  have hsap : 0 < Real.sqrt a := by linarith
  have hla := Real.log_pos hsa1
  have hlb : 0 < Real.log b := Real.log_pos (by linarith)
  have hsqa := Real.sq_sqrt hap.le
  have hsqb := Real.sq_sqrt hbp.le
  have hdiff : Real.sqrt b - Real.sqrt a ≤ (b - a) / (2 * Real.sqrt a) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt a)).mpr
    nlinarith [sq_nonneg (Real.sqrt b - Real.sqrt a)]
  have hden : b * (Real.log b) ^ 2 / 16 ≤ 2 * a * (Real.log (Real.sqrt a)) ^ 2 := by
    have hm := mul_le_mul ha (pow_le_pow_left₀ (by positivity : 0 ≤ Real.log b / 4) hlog 2)
      (sq_nonneg (Real.log b / 4)) hap.le
    nlinarith
  calc
    _ ≤ (b - a) * ((b - a) / (2 * Real.sqrt a)) /
        (Real.sqrt a * (Real.log (Real.sqrt a)) ^ 2) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdiff (sub_nonneg.mpr hab)) (by positivity)
    _ = (b - a) ^ 2 / (2 * (Real.sqrt a) ^ 2 * (Real.log (Real.sqrt a)) ^ 2) := by
      field_simp
    _ = (b - a) ^ 2 / (2 * a * (Real.log (Real.sqrt a)) ^ 2) := by rw [hsqa]
    _ ≤ (b - a) ^ 2 / (b * (Real.log b) ^ 2 / 16) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
    _ = _ := by field_simp

theorem sqrt_boundary_log_error {a b A η : ℝ} (hb : 4 ≤ b) (ha : b / 2 ≤ a) (hab : a ≤ b)
    (hlogb : 4 ≤ Real.log b) (hA : 0 ≤ A) (hη : 0 ≤ η) :
    η * (b - a) * Real.sqrt b /
      ((Real.log (Real.sqrt a)) ^ A * (Real.sqrt a * Real.log (Real.sqrt a))) ≤
        2 * η * (4 : ℝ) ^ A * b / (Real.log b) ^ A := by
  obtain ⟨hsa1, _, hsratio, hlog⟩ := sqrt_boundary_bounds hb ha hab
  have hsap : 0 < Real.sqrt a := by linarith
  have hla := Real.log_pos hsa1
  have hlb : 0 < Real.log b := by linarith
  have hbp : 0 < b := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hY : 0 ≤ b - a := sub_nonneg.mpr hab
  have hYb : b - a ≤ b := by linarith
  have hr : Real.sqrt b / Real.sqrt a ≤ 2 := (div_le_iff₀ hsap).mpr hsratio
  have hinv : 1 / Real.log (Real.sqrt a) ≤ 1 := (div_le_one hla).mpr (by linarith)
  have hp := inverse_rpow_of_lower_scale (by norm_num : (0 : ℝ) < 4) hlb hla hA hlog
  have hfirst : (η * (b - a)) * (Real.sqrt b / Real.sqrt a) ≤ 2 * η * b := by
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hYb hη) hr
      (by positivity) (mul_nonneg hη hbp.le)).trans_eq (by ring)
  have hsecond : (η * (b - a)) * (Real.sqrt b / Real.sqrt a) *
      (1 / Real.log (Real.sqrt a)) ≤ 2 * η * b := by
    simpa only [mul_one] using mul_le_mul hfirst hinv (by positivity)
      (show 0 ≤ 2 * η * b by positivity)
  calc
    _ = (η * (b - a)) * (Real.sqrt b / Real.sqrt a) *
        (1 / Real.log (Real.sqrt a)) * (1 / (Real.log (Real.sqrt a)) ^ A) := by ring
    _ ≤ (2 * η * b) * ((4 : ℝ) ^ A / (Real.log b) ^ A) :=
      mul_le_mul hsecond hp (by positivity) (by positivity)
    _ = _ := by ring

end Erdos421
