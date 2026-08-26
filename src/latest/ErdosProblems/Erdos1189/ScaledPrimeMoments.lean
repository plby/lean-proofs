/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Fixed positive rescalings of the real prime-moment asymptotics.
Informal argument: log(cx)/log x tends to one for fixed c > 0.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountingFibres

namespace Erdos1189

open Filter Asymptotics
open scoped Asymptotics

lemma tendsto_log_div_log_mul {u : ℝ} (hu : 0 < u) :
    Tendsto (fun x : ℝ => Real.log x / Real.log (x * u)) atTop (nhds 1) := by
  have hnorm : Tendsto (fun x : ℝ => ‖Real.log x‖) atTop atTop :=
    tendsto_norm_atTop_atTop.comp Real.tendsto_log_atTop
  have heq : (fun x : ℝ => Real.log x + Real.log u) ~[atTop] Real.log :=
    IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm
  have hlog : (fun x : ℝ => Real.log (x * u)) ~[atTop] Real.log := by
    apply heq.congr_left
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Real.log_mul hx.ne' hu.ne').symm
  apply (isEquivalent_iff_tendsto_one ?_).mp hlog.symm
  have ht : Tendsto (fun x : ℝ => x * u) atTop atTop :=
    tendsto_id.atTop_mul_const hu
  filter_upwards [ht.eventually (eventually_gt_atTop (1 : ℝ))] with x hx
  exact (Real.log_pos hx).ne'

lemma tendsto_realLogPower_scaling (r : ℕ) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun x : ℝ => realLogPower r (x * u) / realLogPower r x)
      atTop (nhds (u ^ r)) := by
  have ht := (tendsto_const_nhds (x := u ^ r)).mul (tendsto_log_div_log_mul hu)
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  dsimp [realLogPower]
  rw [mul_pow]
  field_simp

lemma tendsto_moment_scaling {f : ℝ → ℝ} {r : ℕ} {a u : ℝ} (hu : 0 < u)
    (hf : Tendsto (fun x => f x / realLogPower r x) atTop (nhds a)) :
    Tendsto (fun x : ℝ => f (x * u) / realLogPower r x)
      atTop (nhds (a * u ^ r)) := by
  have hxt : Tendsto (fun x : ℝ => x * u) atTop atTop := tendsto_id.atTop_mul_const hu
  have ht := (hf.comp hxt).mul (tendsto_realLogPower_scaling r hu)
  apply ht.congr'
  filter_upwards [hxt.eventually (realLogPower_eventually_ne_zero r)] with x hx
  dsimp only [Function.comp_apply]
  field_simp

theorem scaled_prime_weight_sum_ratio {u : ℝ} (hu : 0 < u) :
    Tendsto (fun x : ℝ => realPrimeWeightSum (x * u) / realLogPower 2 x)
      atTop (nhds (u ^ 2 / 2)) := by
  simpa only [realPrimeWeightSum, one_div, mul_comm (2 : ℝ)⁻¹, ← div_eq_mul_inv] using
    tendsto_moment_scaling hu real_prime_weight_sum_ratio

end Erdos1189
