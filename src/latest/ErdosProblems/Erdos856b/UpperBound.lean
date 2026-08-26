import ErdosProblems.Erdos856b.UpperCapacity
import ErdosProblems.Erdos856b.LowerBound

/-! # The unconditional weighted upper bound -/

namespace Erdos856b

open Real Filter
open scoped BigOperators Topology

theorem logScale_square {N : ℕ} (hN : 1 < N) :
    logScale (N ^ 2) = logScale N + log 2 := by
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  simp only [logScale, Nat.cast_pow, log_pow, Nat.cast_ofNat]
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hlog.ne', add_comm]

theorem tendsto_logScale_square_div :
    Tendsto (fun N : ℕ => logScale (N ^ 2) / logScale N) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add
    ((tendsto_const_nhds (x := log 2)).div_atTop tendsto_logScale)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ),
    tendsto_logScale.eventually_gt_atTop 0] with N hN hL
  rw [logScale_square hN, add_div, div_self hL.ne']

theorem tendsto_nat_square : Tendsto (fun N : ℕ => N ^ 2) atTop atTop := by
  apply tendsto_atTop_mono (f := fun N : ℕ => N) _ tendsto_id
  intro N
  nlinarith

theorem tendsto_primeHarmonic_square_div :
    Tendsto (fun N : ℕ => primeHarmonic (N ^ 2 : ℕ) / logScale N) atTop (𝓝 1) := by
  have h := (tendsto_primeHarmonic_nat_div.comp tendsto_nat_square).mul
    tendsto_logScale_square_div
  simp only [one_mul] at h
  apply h.congr'
  have hscale := tendsto_logScale.comp tendsto_nat_square
  filter_upwards [hscale.eventually_gt_atTop 0] with N hN
  have hN0 : logScale (N ^ 2) ≠ 0 := ne_of_gt hN
  dsimp [Function.comp_def]
  field_simp [hN0]

theorem tendsto_upper_envelope {z : ℝ} (hz : 0 < z) (u K : ℝ) :
    Tendsto (fun N : ℕ =>
      (log K + u * (primeHarmonic (N ^ 2 : ℕ) + 1)) / logScale N -
        log (squarefreeKernel z N) / logScale N) atTop (𝓝 (u - z)) := by
  have h := (((tendsto_const_nhds (x := log K)).div_atTop tendsto_logScale).add
    ((tendsto_primeHarmonic_square_div.add
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_logScale)).const_mul u)).sub
        (tendsto_log_squarefreeKernel_div hz)
  simp only [add_zero, mul_one, zero_add] at h
  convert h using 1
  ext N
  ring

/-- Theorem 3.1: the upper exponent is the sunflower pressure minus the kernel weight. -/
theorem weighted_upper_bound {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) {b : ℝ}
    (hb : sunflowerPressure k z - z < b) :
    ∀ᶠ N : ℕ in atTop, exponentRatio k N < b := by
  obtain ⟨u, hu, hub⟩ := exists_between (show sunflowerPressure k z < b + z by linarith)
  obtain ⟨K, hK, hbound⟩ := f_mul_kernel_le_exp hk hz hu
  have hlarge := (tendsto_upper_envelope hz u K).eventually
    (gt_mem_nhds (show u - z < b by linarith))
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ),
    tendsto_logScale.eventually_gt_atTop 0] with N hN hN1 hL
  have hfpos : 0 < f k N := zero_lt_one.trans_le (one_le_f hk hN1)
  have hkerpos : 0 < squarefreeKernel z N :=
    zero_lt_one.trans_le (one_le_squarefreeKernel hz.le hN1)
  have hlog := log_le_log (mul_pos hfpos hkerpos) (hbound N)
  rw [log_mul hfpos.ne' hkerpos.ne', log_mul hK.ne' (exp_ne_zero _), log_exp] at hlog
  have hdiv := div_le_div_of_nonneg_right hlog hL.le
  rw [add_div] at hdiv
  change log (f k N) / logScale N < b
  linarith

end Erdos856b
