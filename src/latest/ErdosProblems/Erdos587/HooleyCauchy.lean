import ErdosProblems.Erdos587.HooleySmoothQuadratic

/-! # Taking square roots of the log-log mean estimates -/

open scoped BigOperators

namespace Erdos587

lemma delta_sum_norm_le_of_sq_bound {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    {C R K F : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hK : 0 ≤ K) (hF : 0 ≤ F)
    (hcard : (I.card : ℝ) ≤ 2 * R)
    (hmean : (∑ m ∈ I, ‖z m‖ ^ 2) ≤ C * R * K * F ^ 2) :
    (∑ m ∈ I, ‖z m‖) ≤ (C + 1) * R * Real.sqrt K * F := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) (fun m => ‖z m‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
  have hconst : 2 * C ≤ (C + 1) ^ 2 := by nlinarith [sq_nonneg C]
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)).mp
  calc
    _ ≤ (I.card : ℝ) * ∑ m ∈ I, ‖z m‖ ^ 2 := hCS
    _ ≤ (2 * R) * (C * R * K * F ^ 2) :=
      mul_le_mul hcard hmean (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
    _ = (2 * C) * (R ^ 2 * K * F ^ 2) := by ring
    _ ≤ (C + 1) ^ 2 * (R ^ 2 * K * F ^ 2) :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = _ := by rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hK]; ring

lemma delta_sum_norm_le_of_seventh_power {ι : Type*} (I : Finset ι) (z : ι → ℂ)
    {C R K F : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hK : 0 ≤ K) (hF : 0 ≤ F)
    (hcard : (I.card : ℝ) ≤ 2 * R)
    (hmean : (∑ m ∈ I, ‖z m‖ ^ 2) ≤ C * R * K * F ^ 7) :
    (∑ m ∈ I, ‖z m‖) ≤ (C + 1) * R * Real.sqrt K * F ^ (7 / 2 : ℝ) := by
  have hpow : (F ^ (7 / 2 : ℝ)) ^ 2 = F ^ 7 := by
    rw [← Real.rpow_mul_natCast hF]
    norm_num
  exact delta_sum_norm_le_of_sq_bound I z hC hR hK (Real.rpow_nonneg hF _)
    hcard (by simpa only [hpow] using hmean)

end Erdos587
